/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdges
public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative

/-!
# Russo formula in `p` for the active random-cluster measure

For the active random-cluster measure with a common edge parameter `p`, the `p`-derivative of an
event probability is `(p(1 - p))⁻¹ ∑_e Cov(𝟙_A, ω_e)`.

## i. Overview

The active weight of `ω` on `E(G)` is the random-cluster weight of its extension, so its
`p`-derivative is the weight times the centered score `∑_e (ω_e - p) / (p(1 - p))`. Differentiating
the numerator and partition function term by term and applying the quotient rule expresses the
derivative of any expectation as a covariance with the score, which splits into a sum of covariances
with the edge indicators. This is Russo's formula for the finite-volume random-cluster model.

All results are proved unconditionally, under only `0 < p < 1` and `0 < q`.

## ii. Key results

- `hasDerivAt_activeMean_p` : the `p`-derivative of an active expectation is a sum of edge
  covariances.
- `hasDerivAt_activeProbOf_p` : Russo's formula for the `p`-derivative of an event probability.

## iii. Table of contents

- A. The centered score
- B. Derivatives of weights, expectations, and event probabilities

## iv. References

- L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.12.
-/

@[expose] public section

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The centered score -/

/-- The centered score `∑_{e ∈ E(G)} (ω_e - p)` of an active configuration. -/
noncomputable def activePScore (p : ℝ) (ω : ConfigSpace G.edgeSet) : ℝ :=
  ∑ e : G.edgeSet, (OSSS.Lindeberg.coord e ω - p)

lemma centeredScore_extendActive (p : ℝ) (ω : ConfigSpace G.edgeSet) :
    (∑ e ∈ G.edgeFinset, (coord e (extendActive G ω) - p)) =
      activePScore G p ω := by
  unfold activePScore
  rw [Finset.sum_subtype G.edgeFinset]
  · apply Finset.sum_congr rfl
    intro e _
    change (if extendActive G ω e.1 then (1 : ℝ) else 0) - p =
      (if ω e then (1 : ℝ) else 0) - p
    rw [extendActive_apply]
  · intro e
    rw [SimpleGraph.mem_edgeFinset]

/-! ## B. Derivatives of weights, expectations, and event probabilities -/

lemma hasDerivAt_activeWeight_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (q : ℝ) (ω : ConfigSpace G.edgeSet) :
    HasDerivAt (fun x => activeWeight G (fun _ => x) q ω)
      (activeWeight G (fun _ => p) q ω * activePScore G p ω / (p * (1 - p))) p := by
  have h := hasDerivAt_fkWeight G hp hp1 q (extendActive G ω)
  have hw : ∀ x : ℝ, activeWeight G (fun _ => x) q ω =
      fkWeight G x q (extendActive G ω) := by
    intro x
    rfl
  rw [show (fun x => activeWeight G (fun _ => x) q ω) =
      (fun x => fkWeight G x q (extendActive G ω)) by funext x; exact hw x]
  refine h.congr_deriv ?_
  rw [← hw p, centeredScore_extendActive]
  ring

lemma hasDerivAt_activeNumer_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (q : ℝ) (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun x => activeNumer G (fun _ => x) q f)
      (activeNumer G (fun _ => p) q (fun ω => f ω * activePScore G p ω)
        / (p * (1 - p))) p := by
  unfold activeNumer
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (hasDerivAt_activeWeight_p G hp hp1 q ω).const_mul (f ω))
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- The `p`-derivative of the active expectation of `f` is `(p(1 - p))⁻¹ ∑_e Cov(f, ω_e)`. -/
theorem hasDerivAt_activeMean_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 0 < q) (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun x => activeMean G (fun _ => x) q f)
      ((∑ e : G.edgeSet,
        activeCov G (fun _ => p) q f (OSSS.Lindeberg.coord e)) / (p * (1 - p))) p := by
  have hN := hasDerivAt_activeNumer_p G hp hp1 q f
  have hZraw := hasDerivAt_activeNumer_p G hp hp1 q (fun _ => 1)
  have hZ : HasDerivAt (fun x => activeZ G (fun _ => x) q)
      (activeNumer G (fun _ => p) q (activePScore G p) / (p * (1 - p))) p := by
    simpa only [activeNumer_one, one_mul] using hZraw
  have hZne : activeZ G (fun _ => p) q ≠ 0 :=
    (activeZ_pos G (fun _ => hp) (fun _ => hp1) hq).ne'
  rw [show (fun x => activeMean G (fun _ => x) q f) =
      (fun x => activeNumer G (fun _ => x) q f / activeZ G (fun _ => x) q) by
    funext x
    exact activeMean_eq_div G _ _ _]
  refine (hN.div hZ hZne).congr_deriv ?_
  have hscore : activeCov G (fun _ => p) q f (activePScore G p) =
      ∑ e : G.edgeSet,
        activeCov G (fun _ => p) q f (OSSS.Lindeberg.coord e) := by
    unfold activePScore
    change activeCov G (fun _ => p) q f
      (fun ω => ∑ e : G.edgeSet,
        (fun e ω => OSSS.Lindeberg.coord e ω - p) e ω) = _
    rw [activeCov_sum_right]
    exact Finset.sum_congr rfl fun e _ =>
      activeCov_sub_const G (fun _ => hp) (fun _ => hp1) hq f
        (OSSS.Lindeberg.coord e) p
  rw [← hscore]
  unfold activeCov
  rw [activeMean_eq_div, activeMean_eq_div, activeMean_eq_div]
  field_simp

/-- Russo's formula: the `p`-derivative of `P(A)` is `(p(1 - p))⁻¹ ∑_e Cov(𝟙_A, ω_e)`. -/
theorem hasDerivAt_activeProbOf_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 0 < q) (A : Set (ConfigSpace G.edgeSet)) :
    HasDerivAt (fun x => activeProbOf G (fun _ => x) q A)
      ((∑ e : G.edgeSet, activeCov G (fun _ => p) q
        (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) /
          (p * (1 - p))) p := by
  exact hasDerivAt_activeMean_p G hp hp1 hq _

end StatMech.FK

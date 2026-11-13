/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib
import Code.FK.ActiveEdges
import Code.FK.RussoDerivative

open scoped BigOperators
open Finset

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

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

theorem hasDerivAt_activeWeight_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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

theorem hasDerivAt_activeNumer_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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


theorem hasDerivAt_activeProbOf_p {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 0 < q) (A : Set (ConfigSpace G.edgeSet)) :
    HasDerivAt (fun x => activeProbOf G (fun _ => x) q A)
      ((∑ e : G.edgeSet, activeCov G (fun _ => p) q
        (A.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) /
          (p * (1 - p))) p := by
  exact hasDerivAt_activeMean_p G hp hp1 hq _

end StatMech.FK

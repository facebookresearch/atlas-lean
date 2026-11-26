/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Defs.Basic

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Negative answer to Scottish Book Problem 65

The cone of nondecreasing real continuous functions on the unit interval refutes Mazur's
symmetric hull claim.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65Wanted

/-- **Mazur's symmetric hull claim (Scottish Book Problem 65).** The claim that for every real
Banach space $E$ and every convex set $W \subseteq E$ with $0 \in W$, if the closure of $W$ has
empty interior (that is, $W$ is nowhere dense), then the closure of the convex hull of
$W \cup (-W)$ also has empty interior. The convex hull of $W \cup (-W)$ is the smallest convex
set containing $W$ that is symmetric about the origin.

The typescript's parenthetical identifies this set with the difference set $W - W$, which is
larger in general; the smallest-set reading is adopted here. For the Ad 65 counterexample $W$
(non-decreasing functions, a cone) the two constructions coincide, so the counterexample still
applies. -/
def ScottishBookProblem65Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Set E),
    Convex ℝ W → 0 ∈ W → interior (closure W) = ∅ →
    interior (closure (convexHull ℝ
      (W ∪ {z | ∃ w ∈ W, z = -w}))) = ∅

open Set
open scoped unitInterval

private def monotoneCone : Set C(I, ℝ) := {f | Monotone f}

private theorem convex_monotoneCone : Convex ℝ monotoneCone := by
  intro f hf g hg a b ha hb _ x y hxy
  change a * f x + b * g x ≤ a * f y + b * g y
  exact add_le_add (mul_le_mul_of_nonneg_left (hf hxy) ha)
    (mul_le_mul_of_nonneg_left (hg hxy) hb)

private theorem interior_closure_monotoneCone : interior (closure monotoneCone) = ∅ := by
  have hclosed : IsClosed monotoneCone := isClosed_monotone.preimage continuous_coeFun
  rw [hclosed.closure_eq]
  refine eq_empty_iff_forall_notMem.mpr fun f hf => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hf)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (f.continuous.continuousAt (x := (0 : I))) (ε / 2) (by positivity)
  let t : I := ⟨min (δ / 2) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have ht : 0 < (t : ℝ) := lt_min (by positivity) zero_lt_one
  have htδ : dist t 0 < δ := by
    change dist (t : ℝ) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hdiff : f t - f 0 < ε / 2 := by
    have h := hclose htδ
    rw [Real.dist_eq] at h
    exact (le_abs_self _).trans_lt h
  -- Raise the value at zero by ε/2 with a bump that vanishes at t.
  let bump : C(I, ℝ) := ⟨fun x => max 0 (1 - (x : ℝ) / (t : ℝ)),
    continuous_const.max (continuous_const.sub (continuous_subtype_val.div_const _))⟩
  have hnorm : ‖bump‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x => by
    change ‖max (0 : ℝ) (1 - (x : ℝ) / (t : ℝ))‖ ≤ 1
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (sub_le_self _ (div_nonneg (unitInterval.nonneg x) ht.le))
  have hbump_zero : bump 0 = 1 := by
    change max (0 : ℝ) (1 - 0 / (t : ℝ)) = 1
    simp
  have hbump_t : bump t = 0 := by
    change max (0 : ℝ) (1 - (t : ℝ) / (t : ℝ)) = 0
    simp [ht.ne']
  let g := f + (ε / 2) • bump
  have hg : g ∈ Metric.ball f ε := by
    rw [Metric.mem_ball, dist_eq_norm, show g - f = (ε / 2) • bump by
      dsimp [g]
      abel, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      ε / 2 * ‖bump‖ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ < ε := by linarith
  have hmono : Monotone g := hball hg
  have hle : g 0 ≤ g t := hmono (show (0 : I) ≤ t from ht.le)
  change f 0 + ε / 2 * bump 0 ≤ f t + ε / 2 * bump t at hle
  rw [hbump_zero, hbump_t, mul_one, mul_zero, add_zero] at hle
  linarith

private theorem polynomial_mem_convexHull (p : Polynomial ℝ) :
    p.toContinuousMapOn I ∈ convexHull ℝ
      (monotoneCone ∪ {z | ∃ w ∈ monotoneCone, z = -w}) := by
  -- Adding a line whose slope dominates the derivative makes the polynomial nondecreasing.
  let slope := ‖p.derivative.toContinuousMapOn I‖
  let line : C(I, ℝ) := ⟨fun x => slope * (x : ℝ), continuous_const.mul continuous_subtype_val⟩
  have hline : Monotone line := fun _ _ hxy =>
    mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
  have hpoly : Monotone (p.toContinuousMapOn I + line) := by
    have hmono : MonotoneOn (fun x : ℝ => p.eval x + slope * x) I := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => p.derivative.eval x + slope)
        (convex_Icc 0 1) (p.continuous.add (continuous_const.mul continuous_id)).continuousOn
        (fun x _ => ?_) (fun x hx => ?_)
      · simpa only [Pi.add_def, mul_one] using
          ((p.hasDerivAt x).add ((hasDerivAt_id' x).const_mul slope)).hasDerivWithinAt
      · apply neg_le_iff_add_nonneg.mp
        exact (p.derivative.toContinuousMapOn I).neg_norm_le_apply ⟨x, interior_subset hx⟩
    exact fun x y hxy => hmono x.2 y.2 hxy
  have double_mem {f : C(I, ℝ)} (hf : Monotone f) : (2 : ℝ) • f ∈ monotoneCone :=
    fun _ _ hxy => mul_le_mul_of_nonneg_left (hf hxy) (by norm_num)
  -- Take the midpoint of twice the shifted polynomial and the negative of twice the line.
  have h := (convex_convexHull ℝ
      (monotoneCone ∪ {z | ∃ w ∈ monotoneCone, z = -w}))
    (subset_convexHull ℝ _ (Or.inl (double_mem hpoly)))
    (subset_convexHull ℝ _ (Or.inr ⟨_, double_mem hline, rfl⟩))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [smul_neg, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
    ← sub_eq_add_neg, add_sub_cancel_right] using h

/--
**Mazur's Problem 65 has a negative answer.** The symmetric hull claim of Scottish Book
Problem 65 is false: there are a real Banach space $E$ and a convex set $W \subseteq E$ with
$0 \in W$ whose closure has empty interior, such that the closure of the convex hull of
$W \cup (-W)$ has nonempty interior.

Source: S. Mazur, Problem 65 of the
Scottish Book; typescript Ad 65 records the negative answer, with the
counterexample of the set `W` of non-decreasing functions in the space
`(C)` of continuous functions: `W` is convex, nowhere dense, and
contains `0`, while the symmetric convex set containing `W` contains
all functions of bounded variation and is not nowhere dense (indeed,
it is dense, since it contains the polynomials). For this `W` (a cone)
the `W ∪ -W` hull and the difference-set construction coincide, so the
counterexample refutes the corrected claim too.
-/
theorem mazur65_refuted : ¬ ScottishBookProblem65Claim := by
  intro claim
  have hzero : (0 : C(I, ℝ)) ∈ monotoneCone := fun _ _ _ => le_rfl
  have hinterior := claim C(I, ℝ) monotoneCone convex_monotoneCone hzero
    interior_closure_monotoneCone
  let hull := convexHull ℝ (monotoneCone ∪ {z | ∃ w ∈ monotoneCone, z = -w})
  have hsubset : (polynomialFunctions I : Set C(I, ℝ)) ⊆ hull := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p, rfl⟩
    exact polynomial_mem_convexHull p
  have hdense : closure hull = univ := by
    apply eq_univ_of_univ_subset
    have hclosure := closure_mono hsubset
    rwa [← Subalgebra.topologicalClosure_coe, polynomialFunctions_closure_eq_top',
      Algebra.coe_top] at hclosure
  change interior (closure hull) = ∅ at hinterior
  rw [hdense, interior_univ] at hinterior
  exact Set.univ_nonempty.ne_empty hinterior

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook65Wanted

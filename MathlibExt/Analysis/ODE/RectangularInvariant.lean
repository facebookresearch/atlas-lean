/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/forseti-lean, commit
0a81edc7fe82748af7c9b1139229c4d898f50c28,
`Gimle/Forseti/RectangularODE.lean` and the scalar comparison in
`Gimle/Forseti/Examples/AIFNonnegative.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.ODE.Basic
public import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Forward solutions in closed coordinate boxes

An autonomous field that is Lipschitz on a finite closed box and points inward
on its faces has a forward solution in that box. Coordinate projection extends
it to a globally Lipschitz field, to which Atlas's global existence theorem
applies. Degenerate coordinate intervals and empty coordinate types are allowed.

Only the field on the box is constrained. This gives a trapped solution, not
invariance for every solution of a field that may fail uniqueness outside the
box. No regularity outside the box is assumed in the existence theorem.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MathlibExt.Analysis.ODE

private lemma nonneg_of_derivative_nonneg_below_zero
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (ha : 0 ≤ u a) (hin : ∀ t ∈ Ico a b, u t ≤ 0 → 0 ≤ u' t) :
    ∀ t ∈ Icc a b, 0 ≤ u t := by
  intro t ht
  by_contra h
  have hu : u t < 0 := lt_of_not_ge h
  have hab : 0 < b - a + 1 := by linarith [ht.1, ht.2]
  let δ := -u t / (b - a + 1)
  have hδ : 0 < δ := div_pos (neg_pos.mpr hu) hab
  have hmul : δ * (b - a + 1) = -u t := div_mul_cancel₀ _ (ne_of_gt hab)
  have hdδ (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun r => -u r - δ * (r - a)) (-u' s - δ) s := by
    simpa only [Pi.neg_apply, Pi.sub_apply, id_eq, mul_one] using!
      (hd s hs).neg.sub (((hasDerivAt_id s).sub_const a).const_mul δ)
  have hf := image_le_of_deriv_right_lt_deriv_boundary'
    (fun s hs => (hdδ s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hdδ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (B := fun _ => 0) (B' := fun _ => 0)
    (by simpa using neg_nonpos.mpr ha)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) (by
      intro s hs hc
      have hs0 : u s ≤ 0 := by
        nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hs.1)]
      have := hin s hs hs0
      linarith)
  have := hf ht
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr ht.2)]

/-- A field Lipschitz on a closed coordinate box, with nonnegative rates on its
lower faces and nonpositive rates on its upper faces, has a forward solution
that stays in the box. No regularity of the field outside the box is needed. -/
theorem exists_forward_solution_in_Icc
    {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ}
    {K : ℝ≥0} (hlohi : lo ≤ hi) (hF : LipschitzOnWith K F (Icc lo hi))
    (hin : ∀ y ∈ Icc lo hi, ∀ i,
      (y i = lo i → 0 ≤ F y i) ∧ (y i = hi i → F y i ≤ 0))
    (a : ℝ) {x₀ : ι → ℝ} (hx₀ : x₀ ∈ Icc lo hi) :
    ∃ x : ℝ → ι → ℝ, x a = x₀ ∧
      (∀ t ∈ Ici a, x t ∈ Icc lo hi) ∧
      ∀ t ∈ Ici a, HasDerivAt x (F (x t)) t := by
  let p : (ι → ℝ) → ι → ℝ := fun x i => projIcc (lo i) (hi i) (hlohi i) (x i)
  have hp (x : ι → ℝ) : p x ∈ Icc lo hi :=
    ⟨fun i => (projIcc (lo i) (hi i) (hlohi i) (x i)).property.1,
      fun i => (projIcc (lo i) (hi i) (hlohi i) (x i)).property.2⟩
  have hpeq {x : ι → ℝ} (hx : x ∈ Icc lo hi) : p x = x := by
    funext i
    simp [p, projIcc_of_mem _ ⟨hx.1 i, hx.2 i⟩]
  have hplip : LipschitzWith 1 p := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro i
    calc dist (p x i) (p y i) ≤ dist (x i) (y i) := by
          simpa [p, Subtype.dist_eq] using
            (LipschitzWith.projIcc (hlohi i)).dist_le_mul (x i) (y i)
      _ ≤ dist x y := dist_le_pi_dist x y i
  have hFp : LipschitzWith K (F ∘ p) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hd : dist (p x) (p y) ≤ dist x y := by
      simpa using hplip.dist_le_mul x y
    exact (hF.dist_le_mul _ (hp x) _ (hp y)).trans
      (mul_le_mul_of_nonneg_left hd K.coe_nonneg)
  obtain ⟨x, hx, -⟩ := MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    (fun _ => F ∘ p) a x₀ K (hFp.continuous.comp continuous_snd) (fun _ => hFp)
  have hbox : ∀ t ∈ Ici a, x t ∈ Icc lo hi := by
    intro t ht
    have hlower (i : ι) : lo i ≤ x t i := by
      have h := nonneg_of_derivative_nonneg_below_zero
        (u := fun s => x s i - lo i) (u' := fun s => F (p (x s)) i)
        (a := a) (b := t)
        (fun s _ => (hasDerivAt_pi.mp (hx.2 s) i).sub_const _)
        (by rw [hx.1]; exact sub_nonneg.mpr (hx₀.1 i)) (by
          intro s _ hs
          apply (hin _ (hp (x s)) i).1
          change max (lo i) (min (hi i) (x s i)) = lo i
          exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mp hs)))
      exact sub_nonneg.mp (h t ⟨ht, le_rfl⟩)
    have hupper (i : ι) : x t i ≤ hi i := by
      have h := nonneg_of_derivative_nonneg_below_zero
        (u := fun s => hi i - x s i) (u' := fun s => -F (p (x s)) i)
        (a := a) (b := t)
        (fun s _ => (hasDerivAt_pi.mp (hx.2 s) i).const_sub _)
        (by rw [hx.1]; exact sub_nonneg.mpr (hx₀.2 i)) (by
          intro s _ hs
          apply neg_nonneg.mpr
          apply (hin _ (hp (x s)) i).2
          change max (lo i) (min (hi i) (x s i)) = hi i
          rw [min_eq_left (sub_nonpos.mp hs), max_eq_right (hlohi i)])
      exact sub_nonneg.mp (h t ⟨ht, le_rfl⟩)
    exact ⟨hlower, hupper⟩
  refine ⟨x, hx.1, hbox, fun t ht => ?_⟩
  simpa only [Function.comp_apply, hpeq (hbox t ht)] using hx.2 t

/-- If the field is locally Lipschitz on the whole state space, every solution
starting in an inward-pointing box stays in it on its forward interval.
Local Lipschitz continuity supplies uniqueness, unlike the box-only hypothesis
of `exists_forward_solution_in_Icc`. -/
theorem mapsTo_Icc_of_inward
    {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ}
    (hlohi : lo ≤ hi) (hF : LocallyLipschitz F)
    (hin : ∀ y ∈ Icc lo hi, ∀ i,
      (y i = lo i → 0 ≤ F y i) ∧ (y i = hi i → F y i ≤ 0))
    {a b : ℝ} {x : ℝ → ι → ℝ}
    (hx : IsIntegralCurveOn x (fun _ => F) (Icc a b)) (hx₀ : x a ∈ Icc lo hi) :
    MapsTo x (Icc a b) (Icc lo hi) := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Icc lo hi)) hF.locallyLipschitzOn
  obtain ⟨z, hz₀, hzbox, hz⟩ := exists_forward_solution_in_Icc hlohi hK hin a hx₀
  have hxcont : ContinuousOn x (Icc a b) :=
    fun t ht => (hx t ht).continuousWithinAt
  have hzcont : ContinuousOn z (Icc a b) :=
    fun t ht => (hz t ht.1).continuousAt.continuousWithinAt
  let S := x '' Icc a b ∪ z '' Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hxcont).union
      (isCompact_Icc.image_of_continuousOn hzcont)
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hS hF.locallyLipschitzOn
  have heq : EqOn x z (Icc a b) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => S)
      (fun _ _ => hL) hxcont
      (fun t ht => (hx t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
      (fun t ht => Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
      hzcont (fun t ht => (hz t ht.1).hasDerivWithinAt)
      (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) hz₀.symm
  intro t ht
  rw [heq ht]
  exact hzbox t ht.1

end MathlibExt.Analysis.ODE

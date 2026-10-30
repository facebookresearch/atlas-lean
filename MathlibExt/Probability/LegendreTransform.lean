/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.FenchelMoreau
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Convex.Function

/-!
# Extended-real Legendre transform

The Euclidean Legendre transform is the canonical Fenchel conjugate at the
continuous linear inner-product functional `innerSL ℝ x`. Its values are
`EReal`, so an unbounded supremum is `⊤`.

This corrects the Real-valued conditional supremum in
`v1/Atlas/TheoryOfProbability/code/LegendreTransform.lean`, motivated by the
Lecture 13 target "Definition (Legendre transform)". Real source functions
are embedded pointwise into `EReal`; allowing extended-real input also makes
composition of conjugates well typed. The quadratic's finite value and the
zero function's value at and away from the origin are proved here.

General convexity is expressed by the real-threshold epigraph. The real
`ConvexOn` corollary explicitly requires finite conjugate values. Cramer's
theorem and its probabilistic large-deviation conclusions are not proved by
this development.
-/

@[expose] public section

open scoped InnerProductSpace
open MathlibExt.Analysis.Convex.FenchelMoreau

namespace MathlibExt.Probability.LegendreTransform

/-- The Euclidean specialization of the canonical extended-real Fenchel conjugate. -/
noncomputable def legendreTransform {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → EReal) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  fenchelConj Λ (innerSL ℝ x)

/-- The canonical specialization has the source's inner-product supremum formula. -/
theorem legendreTransform_eq_iSup {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → EReal) (x : EuclideanSpace ℝ (Fin d)) :
    legendreTransform Λ x = ⨆ l, ((⟪l, x⟫_ℝ : ℝ) : EReal) - Λ l := by
  unfold legendreTransform fenchelConj
  congr 1
  funext l
  rw [innerSL_apply_apply, real_inner_comm]

/-- Difference form of Fenchel–Young: every term is at most the conjugate. -/
theorem le_legendreTransform {d : ℕ}
    {Λ : EuclideanSpace ℝ (Fin d) → EReal}
    {x l : EuclideanSpace ℝ (Fin d)} :
    ((⟪l, x⟫_ℝ : ℝ) : EReal) - Λ l ≤ legendreTransform Λ x := by
  rw [legendreTransform_eq_iSup]
  exact le_iSup (fun y => ((⟪y, x⟫_ℝ : ℝ) : EReal) - Λ y) l

/-- A larger input function has a smaller conjugate. -/
theorem legendreTransform_antitone {d : ℕ}
    {Λ₁ Λ₂ : EuclideanSpace ℝ (Fin d) → EReal} (h : ∀ x, Λ₁ x ≤ Λ₂ x)
    {x : EuclideanSpace ℝ (Fin d)} :
    legendreTransform Λ₂ x ≤ legendreTransform Λ₁ x := by
  rw [legendreTransform_eq_iSup, legendreTransform_eq_iSup]
  exact iSup_mono (fun l => EReal.sub_le_sub le_rfl (h l))

/-- The real-threshold epigraph of the extended-real conjugate is convex. -/
theorem convex_epi_legendreTransform {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → EReal) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin d) × ℝ |
      legendreTransform Λ p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq a b ha hb hab
  change legendreTransform Λ (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [legendreTransform_eq_iSup]
  apply iSup_le
  intro l
  have hlp := (le_legendreTransform (Λ := Λ) (x := p.1) (l := l)).trans hp
  have hlq := (le_legendreTransform (Λ := Λ) (x := q.1) (l := l)).trans hq
  by_cases hbot : Λ l = ⊥
  · rw [hbot, EReal.sub_bot (EReal.coe_ne_bot _)] at hlp
    exact False.elim ((EReal.coe_lt_top p.2).not_ge hlp)
  by_cases htop : Λ l = ⊤
  · rw [htop, EReal.sub_top]
    exact bot_le
  lift Λ l to ℝ using ⟨htop, hbot⟩ with r hr
  rw [← EReal.coe_sub] at hlp hlq ⊢
  have hp' := EReal.coe_le_coe_iff.mp hlp
  have hq' := EReal.coe_le_coe_iff.mp hlq
  apply EReal.coe_le_coe_iff.mpr
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hrone : (a + b) * r = r := by rw [hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp' ha, mul_le_mul_of_nonneg_left hq' hb]

/-- The real projection is convex when every conjugate value is finite. -/
theorem convexOn_legendreTransform {d : ℕ}
    {Λ : EuclideanSpace ℝ (Fin d) → EReal}
    (hfinite : ∀ x, legendreTransform Λ x ≠ ⊤ ∧ legendreTransform Λ x ≠ ⊥) :
    ConvexOn ℝ Set.univ (fun x => (legendreTransform Λ x).toReal) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hx := EReal.coe_toReal (hfinite x).1 (hfinite x).2
  have hy := EReal.coe_toReal (hfinite y).1 (hfinite y).2
  have hmx : (x, (legendreTransform Λ x).toReal) ∈
      {p : EuclideanSpace ℝ (Fin d) × ℝ | legendreTransform Λ p.1 ≤ (p.2 : EReal)} :=
    hx.symm.le
  have hmy : (y, (legendreTransform Λ y).toReal) ∈
      {p : EuclideanSpace ℝ (Fin d) × ℝ | legendreTransform Λ p.1 ≤ (p.2 : EReal)} :=
    hy.symm.le
  have hc := convex_epi_legendreTransform Λ hmx hmy ha hb hab
  change legendreTransform Λ (a • x + b • y) ≤
    ((a * (legendreTransform Λ x).toReal + b * (legendreTransform Λ y).toReal : ℝ) : EReal) at hc
  rw [← EReal.coe_toReal (hfinite (a • x + b • y)).1 (hfinite (a • x + b • y)).2] at hc
  exact EReal.coe_le_coe_iff.mp hc

/-- The double Euclidean transform is bounded by the canonical biconjugate and the input. -/
theorem legendreTransform_legendreTransform_le {d : ℕ}
    {Λ : EuclideanSpace ℝ (Fin d) → EReal}
    (hnotbot : ∀ x, Λ x ≠ ⊥) {x : EuclideanSpace ℝ (Fin d)} :
    legendreTransform (legendreTransform Λ) x ≤ Λ x := by
  apply le_trans ?_ (biconj_le Λ hnotbot x)
  rw [legendreTransform_eq_iSup]
  apply iSup_le
  intro y
  have h := le_iSup (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
    ((L x : ℝ) : EReal) - fenchelConj Λ L) (innerSL ℝ y)
  simpa only [legendreTransform, fenchelBiconj, innerSL_apply_apply, real_inner_comm] using h

/-- Inner product is bounded by the average of the squared norms. -/
private theorem inner_le_avg_norm_sq {d : ℕ} (l x : EuclideanSpace ℝ (Fin d)) :
    ⟪l, x⟫_ℝ ≤ (‖l‖ ^ 2 + ‖x‖ ^ 2) / 2 := by
  have h0 : 0 ≤ ‖l - x‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at h0
  linarith

/-- The quadratic is its own conjugate, with an explicitly finite extended-real value. -/
theorem legendreTransform_norm_sq_div_two {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    legendreTransform (fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) x
      = ((‖x‖ ^ 2 / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · rw [legendreTransform_eq_iSup]
    apply iSup_le
    intro l
    rw [← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have h := inner_le_avg_norm_sq l x
    linarith
  · calc ((‖x‖ ^ 2 / 2 : ℝ) : EReal)
        = ((⟪x, x⟫_ℝ : ℝ) : EReal) - ((‖x‖ ^ 2 / 2 : ℝ) : EReal) := by
          rw [← EReal.coe_sub]
          congr 1
          rw [real_inner_self_eq_norm_sq]
          ring
      _ ≤ legendreTransform (fun y : EuclideanSpace ℝ (Fin d) =>
            ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) x :=
          le_legendreTransform
            (Λ := fun y : EuclideanSpace ℝ (Fin d) => ((‖y‖ ^ 2 / 2 : ℝ) : EReal))
            (x := x) (l := x)

/-- The conjugate of the zero function is zero at the origin. -/
theorem legendreTransform_zero {d : ℕ} :
    legendreTransform (fun _ : EuclideanSpace ℝ (Fin d) => (0 : EReal)) 0 = 0 := by
  rw [legendreTransform_eq_iSup]
  simp

/-- The conjugate of the zero function is `⊤` at every nonzero vector. -/
theorem legendreTransform_zero_of_ne {d : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    legendreTransform (fun _ : EuclideanSpace ℝ (Fin d) => (0 : EReal)) x = ⊤ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos hxpos 2
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro R
  let l : EuclideanSpace ℝ (Fin d) := ((R + 1) / ‖x‖ ^ 2) • x
  have hval : ⟪l, x⟫_ℝ = R + 1 := by
    dsimp [l]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ (ne_of_gt hx2)]
  have hFY := le_legendreTransform
    (Λ := fun _ : EuclideanSpace ℝ (Fin d) => (0 : EReal)) (x := x) (l := l)
  have hR : (R : EReal) < ((R + 1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by linarith)
  exact hR.trans_le (by simpa only [hval, sub_zero] using hFY)

end MathlibExt.Probability.LegendreTransform

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse, @toskua

Inner-tail cutoff quotient short complex for first-quadrant complexes.

This builds on the source-neutral adjacent-tail primitive.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantTail
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
@[expose] public section

open CategoryTheory Category Limits ZeroObject

namespace FirstQuadrantTail

variable {C : Type*} [Category C] [Abelian C]

/-- Cutoff-layer complex supported only in absolute degree `r`,
identified there with `K.X r`. -/
noncomputable abbrev cutoffLayer (r : ℕ)
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) :
    HomologicalComplex C (ComplexShape.up' (1 : ℕ)) :=
  (HomologicalComplex.single C (ComplexShape.up' (1 : ℕ)) r).obj (K.X r)

/-- `(innerTail r).obj K` is `K.stupidTrunc (tailEmbedding r)` by definition. -/
lemma innerTail_obj_eq
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (innerTail (C := C) r).obj K = K.stupidTrunc (tailEmbedding r) := rfl

/-- On-degree identification of the tail with the cutoff layer. -/
noncomputable def quotientIso
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (K.stupidTrunc (tailEmbedding r)).X r ≅ (cutoffLayer (C := C) r K).X r :=
  (K.stupidTruncXIso _ (show (tailEmbedding r).f 0 = r by
    rw [tailEmbedding_f]; omega)) ≪≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up' (1 : ℕ)) r (K.X r)).symm

open Classical in
/-- Components of the quotient map onto the cutoff layer:
identity through `stupidTruncXIso` and `singleObjXSelf` at `q = r`,
zero otherwise. -/
noncomputable def quotientF
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r q : ℕ) :
    (K.stupidTrunc (tailEmbedding r)).X q ⟶ (cutoffLayer (C := C) r K).X q :=
  if hq : r = q then hq ▸ (quotientIso (C := C) K r).hom else 0

/-- Off-degree components of the quotient vanish. -/
lemma quotientF_eq_zero
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))} {r q : ℕ} (hq : q ≠ r) :
    quotientF (C := C) K r q = 0 := by
  unfold quotientF
  rw [dite_eq_right (Ne.symm hq)]

/-- On-degree component of the quotient is the canonical identification. -/
lemma quotientF_self
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))} {r : ℕ} :
    quotientF (C := C) K r r = (quotientIso (C := C) K r).hom := by
  unfold quotientF
  simp

/-- The quotient chain map from the tail onto the cutoff layer. -/
noncomputable def tailQuotient
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    K.stupidTrunc (tailEmbedding r) ⟶ cutoffLayer (C := C) r K where
  f := quotientF K r
  comm' q q' h := by
    have hB : (cutoffLayer (C := C) r K).d q q' = 0 := by
      unfold cutoffLayer
      rfl
    rw [hB, comp_zero]
    by_cases hq' : r = q'
    · subst hq'
      have hqr : q + 1 = r := h
      have hz : IsZero ((K.stupidTrunc (tailEmbedding r)).X q) :=
        K.isZero_stupidTrunc_X _ q (by intro i; rw [tailEmbedding_f]; omega)
      have h0 : (K.stupidTrunc (tailEmbedding r)).d q r = 0 := hz.eq_of_src _ _
      rw [h0, zero_comp]
    · rw [quotientF_eq_zero (Ne.symm hq'), comp_zero]

/-- Naturality of the quotient map in `K`, componentwise. -/
lemma tailQuotient_naturality
    {K L : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    (φ : K ⟶ L) (r q : ℕ) :
    (HomologicalComplex.stupidTruncMap φ (tailEmbedding r)).f q ≫
        (tailQuotient (C := C) L r).f q =
      (tailQuotient (C := C) K r).f q ≫
        ((HomologicalComplex.single C (ComplexShape.up' (1 : ℕ)) r).map
          (φ.f r)).f q := by
  change (HomologicalComplex.stupidTruncMap φ (tailEmbedding r)).f q ≫
      quotientF L r q =
    quotientF K r q ≫
      ((HomologicalComplex.single C (ComplexShape.up' (1 : ℕ)) r).map
        (φ.f r)).f q
  by_cases hq : r = q
  · subst hq
    rw [HomologicalComplex.stupidTruncMap_f_eq φ
      (show (tailEmbedding r).f 0 = r by rw [tailEmbedding_f]; omega),
      quotientF_self, quotientF_self,
      HomologicalComplex.single_map_f_self]
    unfold quotientIso
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
  · have hL : quotientF (C := C) L r q = 0 := quotientF_eq_zero (Ne.symm hq)
    have hK : quotientF (C := C) K r q = 0 := quotientF_eq_zero (Ne.symm hq)
    rw [hL, hK]
    exact comp_zero.trans zero_comp.symm

/-- The adjacent-tail comparison followed by the quotient is zero. -/
lemma tailCut_zero
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    tailCompare K r ≫ tailQuotient (C := C) K r = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun q => ?_
  change (tailCompare K r).f q ≫ quotientF K r q = 0
  by_cases hq : r = q
  · subst hq
    have hz : (tailCompare K r).f r = 0 :=
      tailCompare_f_eq_zero (by intro i; rw [tailEmbedding_f]; omega)
    rw [hz, zero_comp]
  · rw [quotientF_eq_zero (Ne.symm hq), comp_zero]

/-- The short complex `tail (r+1) ⟶ tail r ⟶ cutoff r`. -/
noncomputable def tailCutShort
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    ShortComplex (HomologicalComplex C (ComplexShape.up' (1 : ℕ))) :=
  ShortComplex.mk (tailCompare K r) (tailQuotient (C := C) K r)
    (tailCut_zero K r)

/-- The tail-cutoff short complex is short exact, by degreewise splitting. -/
theorem tailCut_shortExact
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    (tailCutShort (C := C) K r).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro q
  rcases lt_trichotomy q r with hlt | heq | hgt
  · -- Below `r`: all three objects vanish.
    refine (ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_).shortExact
    · exact K.isZero_stupidTrunc_X _ q (by intro i; rw [tailEmbedding_f]; omega)
    · have h2 : IsZero ((K.stupidTrunc (tailEmbedding r)).X q) :=
        K.isZero_stupidTrunc_X _ q (by intro i; rw [tailEmbedding_f]; omega)
      have h3 : IsZero ((cutoffLayer (C := C) r K).X q) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up' (1 : ℕ)) r
          (K.X r) q (by omega)
      exact IsZero.isIso h2 h3 _
  · -- At `r`: the source vanishes and the quotient map is an iso.
    subst q
    refine (ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_).shortExact
    · exact K.isZero_stupidTrunc_X _ r (by intro i; rw [tailEmbedding_f]; omega)
    · have h : IsIso (quotientF (C := C) K r r) := by
        rw [quotientF_self]; infer_instance
      exact h
  · -- Above `r`: the target vanishes and the comparison map is an iso.
    refine (ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_).shortExact
    · have hi : (tailEmbedding (r + 1)).f (q - (r + 1)) = q := by
        rw [tailEmbedding_f]; omega
      have hi2 : (tailEmbedding r).f ((q - (r + 1)) + 1) = q := by
        rw [tailEmbedding_f]; omega
      have h : IsIso ((tailCompare K r).f q) := by
        rw [tailCompare_f_eq hi hi2]; infer_instance
      exact h
    · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up' (1 : ℕ)) r
        (K.X r) q (by omega)

end FirstQuadrantTail

end

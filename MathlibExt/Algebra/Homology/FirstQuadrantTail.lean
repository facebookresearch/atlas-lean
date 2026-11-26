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

Adjacent-tail natural inclusion for first-quadrant complexes.

Built on MathlibExt's stupid-truncation map and inclusion APIs.
-/

module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncMap
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Additive
@[expose] public section

open CategoryTheory Category Limits ZeroObject

namespace FirstQuadrantTail

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- For r∈ℕ, the cochain-shape embedding e_r : ℕ → ℕ is
i ↦ i+r. It preserves the relation q′=q+1 and has image
the degrees q≥r. -/
noncomputable def tailEmbedding (r : ℕ) :
    (ComplexShape.up' (1 : ℕ)).Embedding (ComplexShape.up' (1 : ℕ)) :=
  ComplexShape.embeddingUp'Add 1 r

lemma tailEmbedding_f (r i : ℕ) : (tailEmbedding r).f i = i + r := rfl

instance tailEmbedding_isRelIff (r : ℕ) : (tailEmbedding r).IsRelIff :=
  inferInstanceAs (ComplexShape.embeddingUp'Add 1 r).IsRelIff

/-- For r∈ℕ, the embedding e_r(i)=i+r identifies the
nonnegative cochain shape with the full tail of degrees q≥r.
Thus it is an embedding defining truncation at and above r. -/
instance tailEmbedding_isTruncGE (r : ℕ) : (tailEmbedding r).IsTruncGE :=
  inferInstanceAs (ComplexShape.embeddingUp'Add 1 r).IsTruncGE

/-- For r,i,q∈ℕ, if e_(r+1)(i)=q, then e_r(i+1)=q.
Both expressions equal i+r+1, so the adjacent tail comparison
preserves the absolute cochain degree. -/
lemma tailEmbedding_shift (r i q : ℕ)
    (hi : (tailEmbedding (r + 1)).f i = q) :
    (tailEmbedding r).f (i + 1) = q := by
  have h1 : (tailEmbedding (r + 1)).f i = i + (r + 1) := rfl
  have h2 : (tailEmbedding r).f (i + 1) = (i + 1) + r := rfl
  omega

/-- In a category C with zero morphisms and a zero object,
the tail functor T_r sends a nonnegative cochain complex K to
its stupid truncation supported in absolute degrees q≥r.
It retains K_q and its differential within the tail and is zero
below r; it does not shift the retained degrees. -/
noncomputable def innerTail (r : ℕ) :
    HomologicalComplex C (ComplexShape.up' (1 : ℕ)) ⥤
      HomologicalComplex C (ComplexShape.up' (1 : ℕ)) :=
  (tailEmbedding r).stupidTruncFunctor C

instance innerTail_preservesZeroMorphisms (r : ℕ) :
    (innerTail (C := C) r).PreservesZeroMorphisms where
  map_zero := by
    intros K L
    refine HomologicalComplex.hom_ext _ _ fun q => ?_
    change (HomologicalComplex.stupidTruncMap (0 : K ⟶ L)
      (tailEmbedding r)).f q = 0
    by_cases hq : ∃ i, (tailEmbedding r).f i = q
    · obtain ⟨i, hi⟩ := hq
      rw [HomologicalComplex.stupidTruncMap_f_eq (0 : K ⟶ L) hi]
      simp
    · rw [HomologicalComplex.stupidTruncMap_f_eq_zero (0 : K ⟶ L)
        (fun i hi => hq ⟨i, hi⟩)]

open Classical in
/-- For a nonnegative cochain complex K in a category with
zero morphisms and a zero object, the component
(T_(r+1)K)_q → (T_r K)_q is the identity through their
identifications with K_q when q≥r+1, and zero otherwise.
The target tail uses the same absolute degree q. -/
noncomputable def tailCompareF
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r q : ℕ) :
    (K.stupidTrunc (tailEmbedding (r + 1))).X q ⟶
      (K.stupidTrunc (tailEmbedding r)).X q :=
  if hq : ∃ i, (tailEmbedding (r + 1)).f i = q then
    (K.stupidTruncXIso _ hq.choose_spec).hom ≫
      (K.stupidTruncXIso _ (tailEmbedding_shift r _ _ hq.choose_spec)).inv
  else 0

lemma tailCompareF_eq
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    {r i q : ℕ} (hi : (tailEmbedding (r + 1)).f i = q)
    (hi2 : (tailEmbedding r).f (i + 1) = q) :
    tailCompareF K r q =
      (K.stupidTruncXIso _ hi).hom ≫ (K.stupidTruncXIso _ hi2).inv := by
  have hi' : ∃ k, (tailEmbedding (r + 1)).f k = q := ⟨i, hi⟩
  have hch : hi'.choose = i :=
    (tailEmbedding (r + 1)).injective_f (by rw [hi'.choose_spec, hi])
  subst i
  unfold tailCompareF
  simp only [dite_eq_left hi']

lemma tailCompareF_eq_zero
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    {r q : ℕ} (hq : ∀ i, (tailEmbedding (r + 1)).f i ≠ q) :
    tailCompareF K r q = 0 := by
  unfold tailCompareF
  rw [dite_eq_right (by simpa using hq)]

/-- For a nonnegative cochain complex K in a category with
zero morphisms and a zero object, the adjacent-tail inclusion
T_(r+1)K → T_r K retains every degree q≥r+1 and is zero on
the remaining source degrees. These components commute with
the degree-raising differentials. -/
noncomputable def tailCompare
    (K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    K.stupidTrunc (tailEmbedding (r + 1)) ⟶
      K.stupidTrunc (tailEmbedding r) where
  f := tailCompareF K r
  comm' q q' hqq' := by
    by_cases hq : ∃ i, (tailEmbedding (r + 1)).f i = q
    · obtain ⟨i, rfl⟩ := hq
      by_cases hq' : ∃ j, (tailEmbedding (r + 1)).f j = q'
      · obtain ⟨j, rfl⟩ := hq'
        have hi : (tailEmbedding (r + 1)).f i = (tailEmbedding (r + 1)).f i :=
          rfl
        have hj : (tailEmbedding (r + 1)).f j = (tailEmbedding (r + 1)).f j :=
          rfl
        have hi2 := tailEmbedding_shift r i _ hi
        have hj2 := tailEmbedding_shift r j _ hj
        rw [tailCompareF_eq (K := K) (r := r) hi hi2,
          tailCompareF_eq (K := K) (r := r) hj hj2,
          HomologicalComplex.stupidTrunc_d_eq K
            (tailEmbedding (r + 1)) hi hj,
          HomologicalComplex.stupidTrunc_d_eq K
            (tailEmbedding r) hi2 hj2]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      · exfalso
        apply hq'
        refine ⟨i + 1, ?_⟩
        have h1 : (tailEmbedding (r + 1)).f (i + 1) = (i + 1) + (r + 1) := rfl
        have h2 : (tailEmbedding (r + 1)).f i + 1 = q' := hqq'
        have h3 : (tailEmbedding (r + 1)).f i = i + (r + 1) := rfl
        omega
    · rw [tailCompareF_eq_zero (K := K) (fun i hi => hq ⟨i, hi⟩)]
      have hz : (K.stupidTrunc (tailEmbedding (r + 1))).d q q' = 0 :=
        (K.isZero_stupidTrunc_X _ q (fun i hi => hq ⟨i, hi⟩)).eq_of_src _ _
      simp [hz]

@[simp]
lemma tailCompare_f_eq
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    {r i q : ℕ} (hi : (tailEmbedding (r + 1)).f i = q)
    (hi2 : (tailEmbedding r).f (i + 1) = q) :
    (tailCompare K r).f q =
      (K.stupidTruncXIso _ hi).hom ≫ (K.stupidTruncXIso _ hi2).inv :=
  tailCompareF_eq hi hi2

@[simp]
lemma tailCompare_f_eq_zero
    {K : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    {r q : ℕ} (hq : ∀ i, (tailEmbedding (r + 1)).f i ≠ q) :
    (tailCompare K r).f q = 0 :=
  tailCompareF_eq_zero hq

/-- For a nonnegative cochain map φ : K → L in a category
with zero morphisms and a zero object, the tail inclusions η
satisfy η_L ∘ T_(r+1)(φ) = T_r(φ) ∘ η_K in every degree q.
They compare the same absolute degrees of K and L. -/
lemma tailCompare_naturality
    {K L : HomologicalComplex C (ComplexShape.up' (1 : ℕ))}
    (φ : K ⟶ L) (r q : ℕ) :
    (HomologicalComplex.stupidTruncMap φ (tailEmbedding (r + 1))).f q ≫
        (tailCompare L r).f q =
      (tailCompare K r).f q ≫
        (HomologicalComplex.stupidTruncMap φ (tailEmbedding r)).f q := by
  by_cases hq : ∃ i, (tailEmbedding (r + 1)).f i = q
  · obtain ⟨i, rfl⟩ := hq
    have hi : (tailEmbedding (r + 1)).f i = (tailEmbedding (r + 1)).f i := rfl
    have hi2 := tailEmbedding_shift r i _ hi
    rw [HomologicalComplex.stupidTruncMap_f_eq φ
      (emb := tailEmbedding (r + 1)) hi,
      HomologicalComplex.stupidTruncMap_f_eq φ
      (emb := tailEmbedding r) hi2,
      tailCompare_f_eq (K := L) (r := r) hi hi2,
      tailCompare_f_eq (K := K) (r := r) hi hi2]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [HomologicalComplex.stupidTruncMap_f_eq_zero φ (fun i hi => hq ⟨i, hi⟩),
      tailCompare_f_eq_zero (K := K) (fun i hi => hq ⟨i, hi⟩)]
    simp

/-- In a category with zero morphisms and a zero object,
the inclusions T_(r+1)K → T_r K form a natural transformation
between the corresponding nonnegative cochain tail functors,
for every r∈ℕ. -/
noncomputable def tailNatTrans (r : ℕ) :
    innerTail (C := C) (r + 1) ⟶ innerTail (C := C) r where
  app K := tailCompare K r
  naturality := fun _ _ φ =>
    HomologicalComplex.hom_ext _ _ fun q => tailCompare_naturality φ r q

/-- In a category with zero morphisms and a zero object,
applying the tail inclusions to each inner complex gives the
natural transformation between inner-tail functors on bicomplexes
whose two differentials raise nonnegative degrees.
It changes the inner cutoff from r+1 to r. -/
noncomputable def bicomplexTail (r : ℕ) :
    (innerTail (C := C) (r + 1)).mapHomologicalComplex
        (ComplexShape.up' (1 : ℕ)) ⟶
      (innerTail (C := C) r).mapHomologicalComplex
        (ComplexShape.up' (1 : ℕ)) :=
  NatTrans.mapHomologicalComplex (tailNatTrans (C := C) r) _

/-- For a bicomplex K with both differentials raising
nonnegative degrees in a category with zero morphisms and
a zero object, the inner-tail inclusion T_(r+1)K → T_r K
has component η_(K_p) on each outer degree p.
It is the identity on the retained inner degrees q≥r+1. -/
noncomputable def tailInclusion
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r : ℕ) :
    ((innerTail (C := C) (r + 1)).mapHomologicalComplex _).obj K ⟶
      ((innerTail (C := C) r).mapHomologicalComplex _).obj K :=
  (bicomplexTail (C := C) r).app K

@[simp]
lemma tailInclusion_f
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p : ℕ) :
    (tailInclusion K r).f p = tailCompare (K.X p) r := rfl

@[simp]
lemma tailInclusion_f_f_eq
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) {r i q : ℕ} (p : ℕ)
    (hi : (tailEmbedding (r + 1)).f i = q) :
    ((tailInclusion K r).f p).f q =
      ((K.X p).stupidTruncXIso _ hi).hom ≫
        ((K.X p).stupidTruncXIso _ (tailEmbedding_shift r i q hi)).inv := by
  rw [tailInclusion_f]
  exact tailCompare_f_eq hi (tailEmbedding_shift r i q hi)

@[simp]
lemma tailInclusion_f_f_eq_zero
    (K : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) (r p q : ℕ)
    (hq : ∀ i, (tailEmbedding (r + 1)).f i ≠ q) :
    ((tailInclusion K r).f p).f q = 0 := by
  rw [tailInclusion_f]
  exact tailCompare_f_eq_zero hq

end FirstQuadrantTail

end

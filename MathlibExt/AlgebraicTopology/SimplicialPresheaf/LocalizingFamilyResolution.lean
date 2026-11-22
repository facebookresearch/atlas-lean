/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrationFamilyResolution
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveDerivedMappingComparison

/-!
# Small resolutions of original localizing families

Every original small Arrow family is resolved on its original index. Both
comparison components are actual trivial fibrations. One produced regular
cardinal controls all original/resolved endpoints, the original site and
operator profiles, local presentability and the literal resolved-family small
object argument. Raw and chosen-derived locality agree with the original
family at every actual injectively fibrant target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open Cardinal HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The original whole Arrow square induces the exact contravariant end square. -/
theorem rawFamilyComparison_square {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre S.hom Z ≫ innerHomPre r.left Z =
      innerHomPre r.right Z ≫ innerHomPre T.hom Z := by
  rw [innerHomPre_comp, innerHomPre_comp, r.w]

/-- The same original whole Arrow square induces the exact chosen-derived square. -/
theorem derivedFamilyComparison_square {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (Z : SimplicialPresheaf.{u} D) :
    originalDerivedPrecomp D S.hom Z ≫ originalDerivedPrecomp D r.left Z =
      originalDerivedPrecomp D r.right Z ≫ originalDerivedPrecomp D T.hom Z := by
  calc
    _ = originalDerivedPrecomp D (r.left ≫ S.hom) Z :=
      ((originalDerivedMapping_laws D).2.1 r.left S.hom Z).symm
    _ = originalDerivedPrecomp D (T.hom ≫ r.right) Z :=
      congrArg (fun f => originalDerivedPrecomp D f Z) r.w
    _ = _ := (originalDerivedMapping_laws D).2.1 T.hom r.right Z

/-- Both raw vertical maps of an actual trivial-fibration Arrow comparison are weak. -/
theorem rawFamilyComparison_vertical_weak {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (hleft : trivialFibrations (SimplicialPresheaf.{u} D) r.left)
    (hright : trivialFibrations (SimplicialPresheaf.{u} D) r.right)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (innerHomPre r.left Z) ∧
      SSet.realizationWeakEquivalences (innerHomPre r.right Z) :=
  ⟨innerHomPre_weak_of_weakEquivalence r.left Z hleft.2 hZ,
    innerHomPre_weak_of_weakEquivalence r.right Z hright.2 hZ⟩

/-- Both actual chosen-derived vertical comparisons are weak at every original target. -/
theorem derivedFamilyComparison_vertical_weak {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (hleft : trivialFibrations (SimplicialPresheaf.{u} D) r.left)
    (hright : trivialFibrations (SimplicialPresheaf.{u} D) r.right)
    (Z : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (originalDerivedPrecomp D r.left Z) ∧
      SSet.realizationWeakEquivalences (originalDerivedPrecomp D r.right Z) :=
  ⟨originalDerivedPrecomp_weak_of_weak r.left Z hleft.2,
    originalDerivedPrecomp_weak_of_weak r.right Z hright.2⟩

/-- Raw horizontal weak tests agree across both actual weak comparison legs. -/
theorem rawFamilyComparison_weak_iff {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (hleft : trivialFibrations (SimplicialPresheaf.{u} D) r.left)
    (hright : trivialFibrations (SimplicialPresheaf.{u} D) r.right)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (innerHomPre T.hom Z) ↔
      SSet.realizationWeakEquivalences (innerHomPre S.hom Z) := by
  have h := rawFamilyComparison_vertical_weak r hleft hright Z hZ
  have hL := SSet.realizationWeakEquivalences.postcomp_iff
    (innerHomPre S.hom Z) (innerHomPre r.left Z) h.1
  have hR := SSet.realizationWeakEquivalences.precomp_iff
    (innerHomPre r.right Z) (innerHomPre T.hom Z) h.2
  rw [rawFamilyComparison_square r Z] at hL
  exact hR.symm.trans hL

/-- The same chosen Q/R tests agree with the original arbitrary-arrow tests at a fibrant target. -/
theorem derivedFamilyComparison_weak_iff {T S : Arrow (SimplicialPresheaf.{u} D)}
    (r : T ⟶ S) (hleft : trivialFibrations (SimplicialPresheaf.{u} D) r.left)
    (hright : trivialFibrations (SimplicialPresheaf.{u} D) r.right)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (originalDerivedPrecomp D T.hom Z) ↔
      SSet.realizationWeakEquivalences (originalDerivedPrecomp D S.hom Z) :=
  (originalDerivedPrecomp_weak_iff T.hom Z hZ).trans
    ((rawFamilyComparison_weak_iff r hleft hright Z hZ).trans
      (originalDerivedPrecomp_weak_iff S.hom Z hZ).symm)

/-- Every original small family has a same-index cofibration resolution and both locality iff's.
All four endpoint ranks, both original trivial-fibration legs and the literal-family small-object
argument use one internally produced cardinal. No model, resolution or weak-test outcome is
input. -/
theorem exists_original_small_family_resolution {I : Type i} [Small.{u} I]
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    ∃ (T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
      (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      ℵ₀ < κ ∧ HasCardinalLT I κ ∧ HasCardinalLT D κ ∧
        HasCardinalLT (Arrow D) κ ∧ HasCardinalLT (Arrow SimplexCategory) κ ∧
        (data D).κ < κ ∧ IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ ∧
        (∀ j, IsCofibrant (T j).left ∧ cofibrations (SimplicialPresheaf.{u} D) (T j).hom ∧
          trivialFibrations (SimplicialPresheaf.{u} D) (r j).left ∧
          trivialFibrations (SimplicialPresheaf.{u} D) (r j).right ∧
          (r j).left ≫ (S j).hom = (T j).hom ≫ (r j).right) ∧
        (∀ j, IsCardinalPresentable (S j).left κ ∧ IsCardinalPresentable (S j).right κ ∧
          IsCardinalPresentable (T j).left κ ∧ IsCardinalPresentable (T j).right κ) ∧
        (ofHoms (fun j => (T j).hom)).IsSmall.{u} ∧
        (ofHoms (fun j => (T j).hom)).IsCardinalForSmallObjectArgument κ ∧
        (ofHoms (fun j => (T j).hom)).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (ofHoms (fun j => (T j).hom)).rlp.llp (ofHoms (fun j => (T j).hom)).rlp) ∧
        (∀ Z : SimplicialPresheaf.{u} D, IsFibrant Z →
          ((∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z)) ↔
            ∀ j, SSet.realizationWeakEquivalences (innerHomPre (T j).hom Z))) ∧
        (∀ Z : SimplicialPresheaf.{u} D, IsFibrant Z →
          ((∀ j, SSet.realizationWeakEquivalences (originalDerivedPrecomp D (S j).hom Z)) ↔
            ∀ j, SSet.realizationWeakEquivalences (originalDerivedPrecomp D (T j).hom Z))) := by
  let : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) :=
    SimplicialPresheaf.isLocallyPresentable
  let profile : Type u := (data D).κ.ord.ToType ⊕ (Shrink.{u} D ⊕
    (Shrink.{u} (Arrow D) ⊕ Shrink.{u} (Arrow SimplexCategory)))
  obtain ⟨T, r, κ, hκ, hbot, hω, hIndex, hProfile, hResolution, hRanks,
    hSmall, hEligible, hSOA, hFF⟩ :=
      exists_small_cofibration_family_resolution S profile
  let : Fact κ.IsRegular := hκ
  let : OrderBot κ.ord.ToType := hbot
  have hI : HasCardinalLT I κ :=
    hIndex.of_injective (equivShrink.{u} I) (equivShrink.{u} I).injective
  have hD : HasCardinalLT D κ := hProfile.of_injective
    (fun d => (Sum.inr (Sum.inl (equivShrink.{u} D d)) : profile))
    (Sum.inr_injective.comp (Sum.inl_injective.comp (equivShrink.{u} D).injective))
  have hArrowD : HasCardinalLT (Arrow D) κ := hProfile.of_injective
    (fun a => (Sum.inr (Sum.inr (Sum.inl (equivShrink.{u} (Arrow D) a))) : profile))
    (Sum.inr_injective.comp (Sum.inr_injective.comp
      (Sum.inl_injective.comp (equivShrink.{u} (Arrow D)).injective)))
  have hSimplex : HasCardinalLT (Arrow SimplexCategory) κ := hProfile.of_injective
    (fun a => (Sum.inr (Sum.inr (Sum.inr (equivShrink.{u} (Arrow SimplexCategory) a))) : profile))
    (Sum.inr_injective.comp (Sum.inr_injective.comp
      (Sum.inr_injective.comp (equivShrink.{u} (Arrow SimplexCategory)).injective)))
  have hBase : (data D).κ < κ := by
    have h := hProfile.of_injective (Sum.inl : (data D).κ.ord.ToType → profile)
      Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  let : Fact (data D).κ.IsRegular := (data D).regular
  let : IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) (data D).κ :=
    (data D).locallyPresentable
  have hLP : IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ :=
    IsCardinalLocallyPresentable.of_le (SimplicialPresheaf.{u} D) hBase.le
  refine ⟨T, r, κ, hκ, hbot, hω, hI, hD, hArrowD, hSimplex, hBase, hLP,
    ?_, hRanks, hSmall, hEligible, hSOA, hFF, ?_, ?_⟩
  · intro j
    exact ⟨(hResolution j).1, (hResolution j).2.1,
      (hResolution j).2.2.1, (hResolution j).2.2.2, (r j).w⟩
  · intro Z hZ
    exact forall_congr' fun j =>
      (rawFamilyComparison_weak_iff (r j) (hResolution j).2.2.1
        (hResolution j).2.2.2 Z hZ).symm
  · intro Z hZ
    exact forall_congr' fun j =>
      (derivedFamilyComparison_weak_iff (r j) (hResolution j).2.2.1
        (hResolution j).2.2.2 Z hZ).symm

end SimplicialPresheaf.InjectiveKan

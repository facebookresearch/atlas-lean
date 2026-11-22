/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalizingFamilyResolution
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Original local boundary generators and terminal lifting
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Cardinal Opposite
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The original chosen scalar pushout corner for every actual boundary. -/
def localBoundaryCorner (a : Arrow (SimplicialPresheaf.{u} D)) (n : ℕ) :
    scalarTensor.PushoutObjObj a.hom (SSet.boundary.{u} n).ι :=
  Functor.PushoutObjObj.ofHasPushout scalarTensor a.hom (SSet.boundary.{u} n).ι

/-- The literal scalar boundary cells on the original index. -/
def localBoundaryGenerators {I : Type i} (T : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  ofHoms (fun k : I × ℕ => (localBoundaryCorner (T k.1) k.2).ι)

/-- The original base generators together with the literal local boundary cells. -/
def originalLocalGenerators {I : Type i} (T : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  (data D).smith.J ⊔ localBoundaryGenerators T

/-- Both original boundary and end square lifts correspond through the whole terminal corner. -/
theorem localBoundary_hasLiftingProperty_iff (a : Arrow (SimplicialPresheaf.{u} D))
    (n : ℕ) (Z : SimplicialPresheaf.{u} D) :
    HasLiftingProperty (localBoundaryCorner a n).ι (terminal.from Z) ↔
      HasLiftingProperty (SSet.boundary.{u} n).ι (innerHomPre a.hom Z) := by
  let q := Functor.PullbackObjObj.ofHasPullback innerHomFunctor a.hom (terminal.from Z)
  have h := (scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff
    (localBoundaryCorner a n) q
  exact h.trans (HasLiftingProperty.iff_of_arrow_iso_right (SSet.boundary.{u} n).ι
    (precompCornerIso a.hom Z q))

/-- The literal local generator RLP is exactly all original scalar boundary lifts. -/
theorem localBoundaryGenerators_terminal_iff {I : Type i}
    (T : I → Arrow (SimplicialPresheaf.{u} D)) (Z : SimplicialPresheaf.{u} D) :
    (localBoundaryGenerators T).rlp (terminal.from Z) ↔
      ∀ j, SSet.modelCategoryQuillen.I.rlp (innerHomPre (T j).hom Z) := by
  constructor
  · intro h j A B b hb
    cases hb with
    | mk n =>
      exact (localBoundary_hasLiftingProperty_iff (T j) n Z).mp
        (h _ (ofHoms.mk (j, n)))
  · intro h A B a ha
    cases ha with
    | mk k =>
      exact (localBoundary_hasLiftingProperty_iff (T k.1) k.2 Z).mpr
        (h k.1 _ (SSet.modelCategoryQuillen.boundary_ι_mem_I k.2))

/-- Terminal RLP for the actual base/local generators is original injective fibrancy and
locality. -/
theorem originalLocalGenerators_terminal_iff {I : Type i}
    (T : I → Arrow (SimplicialPresheaf.{u} D))
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom)
    (Z : SimplicialPresheaf.{u} D) :
    (originalLocalGenerators T).rlp (terminal.from Z) ↔
      IsFibrant Z ∧ ∀ j, SSet.realizationWeakEquivalences (innerHomPre (T j).hom Z) := by
  have hsplit : (originalLocalGenerators T).rlp (terminal.from Z) ↔
      (data D).smith.J.rlp (terminal.from Z) ∧
        (localBoundaryGenerators T).rlp (terminal.from Z) := by
    constructor
    · intro h
      exact ⟨fun {A B} a ha => h a (Or.inl ha), fun {A B} a ha => h a (Or.inr ha)⟩
    · rintro ⟨hbase, hlocal⟩ A B a (ha | ha)
      · exact hbase a ha
      · exact hlocal a ha
  have hbase : (data D).smith.J.rlp (terminal.from Z) ↔ IsFibrant Z := by
    rw [(data D).J_rlp_eq, ← (data D).fibrations_eq]
    change fibrations (SimplicialPresheaf.{u} D) (terminal.from Z) ↔ IsFibrant Z
    exact ((fibration_iff _).symm.trans (isFibrant_iff Z).symm)
  rw [hsplit, hbase, localBoundaryGenerators_terminal_iff]
  constructor
  · rintro ⟨hZ, hlocal⟩
    refine ⟨hZ, fun j => ?_⟩
    let : Fibration (innerHomPre (T j).hom Z) :=
      (fibration_iff _).mpr (rawPrecomp_fibration_of_cofibration (T j).hom Z (hT j) hZ)
    exact (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mp
      (hlocal j)
  · rintro ⟨hZ, hlocal⟩
    refine ⟨hZ, fun j => ?_⟩
    let : Fibration (innerHomPre (T j).hom Z) :=
      (fibration_iff _).mpr (rawPrecomp_fibration_of_cofibration (T j).hom Z (hT j) hZ)
    exact (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr
      (hlocal j)

/-- Every literal local boundary generator is an original monomorphism. -/
theorem localBoundaryGenerators_le_monomorphisms {I : Type i}
    (T : I → Arrow (SimplicialPresheaf.{u} D))
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom) :
    localBoundaryGenerators T ≤ monomorphisms (SimplicialPresheaf.{u} D) := by
  intro A B a ha
  cases ha with
  | mk k =>
    have hm := scalar_pushoutObjObj_cofibration (T k.1).hom (SSet.boundary.{u} k.2).ι
      (localBoundaryCorner (T k.1) k.2) (hT k.1)
        ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono _))
    change (data D).model.categoryWithCofibrations.cofibrations _ at hm
    rwa [(data D).cofibrations_eq] at hm

/-- Both the literal base and local generators are original monomorphisms. -/
theorem originalLocalGenerators_le_monomorphisms {I : Type i}
    (T : I → Arrow (SimplicialPresheaf.{u} D))
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom) :
    originalLocalGenerators T ≤ monomorphisms (SimplicialPresheaf.{u} D) := by
  intro A B a ha
  rcases ha with ha | ha
  · have h := (le_llp_rlp (data D).smith.J) a ha
    rw [(data D).J_left_eq] at h
    exact h.1
  · exact localBoundaryGenerators_le_monomorphisms T hT a ha

/-- The original base-J and local-cell labels, shrunk only as a counting type. -/
def localGeneratorFamily {I : Type i} (T : I → Arrow (SimplicialPresheaf.{u} D)) :
    ((data D).smith.J.toSet) ⊕ (I × ℕ) → Arrow (SimplicialPresheaf.{u} D) :=
  Sum.elim (fun a => a.val) (fun k => Arrow.mk (localBoundaryCorner (T k.1) k.2).ι)

/-- The combined label family represents the literal generator class, with no isomorphic
replacement. -/
theorem localGeneratorFamily_ofHoms {I : Type i}
    (T : I → Arrow (SimplicialPresheaf.{u} D)) :
    ofHoms (fun k => (localGeneratorFamily T k).hom) = originalLocalGenerators T := by
  ext A B a
  constructor
  · intro h
    cases h with
    | mk k =>
      cases k with
      | inl a => exact Or.inl a.property
      | inr k => exact Or.inr (ofHoms.mk k)
  · intro h
    rcases h with h | h
    · exact ofHoms.mk (Sum.inl (⟨Arrow.mk a, h⟩ : (data D).smith.J.toSet))
    · cases h with
      | mk k => exact ofHoms.mk (Sum.inr k)

/-- The actual combined generator class is small at the original value universe. -/
theorem originalLocalGenerators_isSmall {I : Type i} [Small.{u} I]
    (T : I → Arrow (SimplicialPresheaf.{u} D)) :
    (originalLocalGenerators T).IsSmall.{u} := by
  let : (data D).smith.J.IsSmall.{u} := (data D).J_eligible.isSmall
  rw [← localGeneratorFamily_ofHoms T]
  infer_instance

private theorem eligibleOfDomainRanks {ι : Type*} [Small.{u} ι]
    (F : ι → Arrow (SimplicialPresheaf.{u} D)) (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hRanks : ∀ j, IsCardinalPresentable (F j).left κ) :
    (ofHoms (fun j => (F j).hom)).IsCardinalForSmallObjectArgument κ := by
  let : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) :=
    SimplicialPresheaf.isLocallyPresentable
  exact
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := (data D).J_eligible.hasCoproducts
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y f hf p c
        cases hf with
        | mk j =>
          let : IsCardinalPresentable (F j).left κ := hRanks j
          let : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op (F j).left)) :=
            preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
              (F j).left κ κ.ord.ToType
          infer_instance }

/-- After forming the literal local generators, one larger cardinal bounds all their endpoints. -/
theorem exists_localGenerator_cardinal {I : Type i} [Small.{u} I]
    (T : I → Arrow (SimplicialPresheaf.{u} D)) (lower : Cardinal.{u}) :
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      lower < κ ∧ ℵ₀ < κ ∧
        HasCardinalLT I κ ∧ HasCardinalLT D κ ∧ HasCardinalLT (Arrow D) κ ∧
        HasCardinalLT (Arrow SimplexCategory) κ ∧
        IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ ∧
        (∀ j, IsCardinalPresentable (localGeneratorFamily T j).left κ ∧
          IsCardinalPresentable (localGeneratorFamily T j).right κ) ∧
        (originalLocalGenerators T).IsSmall.{u} ∧
        (originalLocalGenerators T).IsCardinalForSmallObjectArgument κ ∧
        (originalLocalGenerators T).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (originalLocalGenerators T).rlp.llp (originalLocalGenerators T).rlp) := by
  let : (data D).smith.J.IsSmall.{u} := (data D).J_eligible.isSmall
  let profile : Type u := Shrink.{u} I ⊕ (Shrink.{u} D ⊕
    (Shrink.{u} (Arrow D) ⊕ Shrink.{u} (Arrow SimplexCategory)))
  obtain ⟨κ, hκ, hLower, hω, hLabels, hProfile, hLP, hRanks⟩ :=
    SimplicialPresheaf.exists_regular_cardinal_for_family (localGeneratorFamily T) lower profile
  let : Fact κ.IsRegular := hκ
  have : Nonempty κ.ord.ToType := by simpa using hκ.out.ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  have hI : HasCardinalLT I κ := hProfile.of_injective
    (fun j => (Sum.inl (equivShrink.{u} I j) : profile))
    (Sum.inl_injective.comp (equivShrink.{u} I).injective)
  have hD : HasCardinalLT D κ := hProfile.of_injective
    (fun d => (Sum.inr (Sum.inl (equivShrink.{u} D d)) : profile))
    (Sum.inr_injective.comp (Sum.inl_injective.comp (equivShrink.{u} D).injective))
  have hAD : HasCardinalLT (Arrow D) κ := hProfile.of_injective
    (fun a => (Sum.inr (Sum.inr (Sum.inl (equivShrink.{u} (Arrow D) a))) : profile))
    (Sum.inr_injective.comp (Sum.inr_injective.comp
      (Sum.inl_injective.comp (equivShrink.{u} (Arrow D)).injective)))
  have hAS : HasCardinalLT (Arrow SimplexCategory) κ := hProfile.of_injective
    (fun a => (Sum.inr (Sum.inr (Sum.inr (equivShrink.{u} (Arrow SimplexCategory) a))) : profile))
    (Sum.inr_injective.comp (Sum.inr_injective.comp
      (Sum.inr_injective.comp (equivShrink.{u} (Arrow SimplexCategory)).injective)))
  have hEligible : (originalLocalGenerators T).IsCardinalForSmallObjectArgument κ := by
    rw [← localGeneratorFamily_ofHoms T]
    exact eligibleOfDomainRanks (localGeneratorFamily T) κ (fun j => (hRanks j).1)
  let := hEligible
  exact ⟨κ, hκ, inferInstance, hLower, hω, hI, hD, hAD, hAS, hLP,
    hRanks, originalLocalGenerators_isSmall T, hEligible,
    ⟨κ, inferInstance, inferInstance, hEligible⟩,
    ⟨SmallObject.functorialFactorizationData (originalLocalGenerators T) κ⟩⟩

/-- A same-index original family comparison gives the exact original S terminal condition. -/
theorem originalLocalGenerators_terminal_iff_of_resolution {I : Type i}
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hT : ∀ j, cofibrations (SimplicialPresheaf.{u} D) (T j).hom)
    (hleft : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).left)
    (hright : ∀ j, trivialFibrations (SimplicialPresheaf.{u} D) (r j).right)
    (Z : SimplicialPresheaf.{u} D) :
    (originalLocalGenerators T).rlp (terminal.from Z) ↔
      IsFibrant Z ∧ ∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z) := by
  rw [originalLocalGenerators_terminal_iff T hT]
  constructor
  · rintro ⟨hZ, hLocal⟩
    exact ⟨hZ, fun j => (rawFamilyComparison_weak_iff (r j)
      (hleft j) (hright j) Z hZ).mp (hLocal j)⟩
  · rintro ⟨hZ, hLocal⟩
    exact ⟨hZ, fun j => (rawFamilyComparison_weak_iff (r j)
      (hleft j) (hright j) Z hZ).mpr (hLocal j)⟩

/-- Every original small localizer has its actual boundary generators, exact terminal criterion,
and full same-cardinal source/iteration data, constructed on the original index. -/
theorem exists_original_local_generator_system {I : Type i} [Small.{u} I]
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
        originalLocalGenerators T ≤ monomorphisms (SimplicialPresheaf.{u} D) ∧
        (originalLocalGenerators T).IsSmall.{u} ∧
        (∀ j, IsCardinalPresentable (localGeneratorFamily T j).left κ ∧
          IsCardinalPresentable (localGeneratorFamily T j).right κ) ∧
        (originalLocalGenerators T).IsCardinalForSmallObjectArgument κ ∧
        (originalLocalGenerators T).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (originalLocalGenerators T).rlp.llp (originalLocalGenerators T).rlp) ∧
        (ofHoms (fun j => (T j).hom)).IsSmall.{u} ∧
        (ofHoms (fun j => (T j).hom)).IsCardinalForSmallObjectArgument κ ∧
        (ofHoms (fun j => (T j).hom)).HasSmallObjectArgument.{u} ∧
        Nonempty (FunctorialFactorizationData
          (ofHoms (fun j => (T j).hom)).rlp.llp (ofHoms (fun j => (T j).hom)).rlp) ∧
        (∀ Z : SimplicialPresheaf.{u} D,
          (originalLocalGenerators T).rlp (terminal.from Z) ↔
            IsFibrant Z ∧ ∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z)) ∧
        (∀ Z : SimplicialPresheaf.{u} D,
          (originalLocalGenerators T).rlp (terminal.from Z) ↔
            IsFibrant Z ∧ ∀ j,
              SSet.realizationWeakEquivalences (originalDerivedPrecomp D (S j).hom Z)) := by
  obtain ⟨T, r, κ₀, hκ₀, hbot₀, hω₀, hI₀, hD₀, hAD₀, hAS₀, hBase₀, hLP₀,
    hRes, hRanks₀, hSmall₀, hEligible₀, hSOA₀, hFF₀, hRaw₀, hDerived₀⟩ :=
    exists_original_small_family_resolution S
  obtain ⟨κ, hκ, hbot, hLower, hω, hI, hD, hAD, hAS, hLP,
    hGenRanks, hGenSmall, hGenEligible, hGenSOA, hGenFF⟩ :=
    exists_localGenerator_cardinal T κ₀
  let : Fact κ₀.IsRegular := hκ₀
  let : OrderBot κ₀.ord.ToType := hbot₀
  let : Fact κ.IsRegular := hκ
  let : OrderBot κ.ord.ToType := hbot
  have hRanks (j : I) : IsCardinalPresentable (S j).left κ ∧
      IsCardinalPresentable (S j).right κ ∧ IsCardinalPresentable (T j).left κ ∧
        IsCardinalPresentable (T j).right κ := by
    have old := hRanks₀ j
    let : IsCardinalPresentable (S j).left κ₀ := old.1
    let : IsCardinalPresentable (S j).right κ₀ := old.2.1
    let : IsCardinalPresentable (T j).left κ₀ := old.2.2.1
    let : IsCardinalPresentable (T j).right κ₀ := old.2.2.2
    exact ⟨isCardinalPresentable_of_le _ hLower.le,
      isCardinalPresentable_of_le _ hLower.le,
      isCardinalPresentable_of_le _ hLower.le,
      isCardinalPresentable_of_le _ hLower.le⟩
  let M := ofHoms (fun j => (T j).hom)
  have hMEligible : M.IsCardinalForSmallObjectArgument κ :=
    eligibleOfDomainRanks T κ (fun j => (hRanks j).2.2.1)
  let := hMEligible
  have hT (j : I) := (hRes j).2.1
  have hLeft (j : I) := (hRes j).2.2.1
  have hRight (j : I) := (hRes j).2.2.2.1
  have hTerminal (Z : SimplicialPresheaf.{u} D) :
      (originalLocalGenerators T).rlp (terminal.from Z) ↔
        IsFibrant Z ∧ ∀ j, SSet.realizationWeakEquivalences (innerHomPre (S j).hom Z) :=
    originalLocalGenerators_terminal_iff_of_resolution S T r hT hLeft hRight Z
  refine ⟨T, r, κ, hκ, hbot, hω, hI, hD, hAD, hAS, hBase₀.trans hLower,
    hLP, hRes, hRanks, originalLocalGenerators_le_monomorphisms T hT,
    hGenSmall, hGenRanks, hGenEligible, hGenSOA, hGenFF, inferInstance, hMEligible,
    ⟨κ, inferInstance, inferInstance, hMEligible⟩,
    ⟨SmallObject.functorialFactorizationData M κ⟩, hTerminal, ?_⟩
  intro Z
  rw [hTerminal]
  constructor
  · rintro ⟨hZ, hLocal⟩
    exact ⟨hZ, fun j => (originalDerivedPrecomp_weak_iff (S j).hom Z hZ).mpr (hLocal j)⟩
  · rintro ⟨hZ, hLocal⟩
    exact ⟨hZ, fun j => (originalDerivedPrecomp_weak_iff (S j).hom Z hZ).mp (hLocal j)⟩

end SimplicialPresheaf.InjectiveKan

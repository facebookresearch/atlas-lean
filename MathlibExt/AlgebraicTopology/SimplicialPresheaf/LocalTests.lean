/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RawLocality
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalizingFamilyResolution
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Local

/-!
# Original local objects and weak tests

Raw local tests use the actual fixed-u mapping end on original presheaves.
The same native lower-Hom model and Q/R choices give the genuine derived
formulation. Both local-fibrant predicates and all-original-arrow weak
classes agree, without a supplied localized model or calculus outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite Cardinal
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.scalarEnrichment
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory
attribute [local instance] SimplicialPresheaf.InjectiveKan.mappingCarrierModel
  SimplicialPresheaf.enrichedCarrierSimplicialCategory
attribute [local instance] SimplicialPresheaf.InjectiveKan.mappingCarrierHasCofibrationFactorization
  SimplicialPresheaf.InjectiveKan.mappingCarrierHasTrivialCofibrationFactorization

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i}

/-- The original family is moved by the actual whole-Arrow enriched carrier functor. -/
def enrichedLocalizingFamily (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    I → Arrow (MappingCarrier.{u} D) :=
  fun j => (enrichedCarrierEquivalence (D := D)).functor.mapArrow.obj (S j)

/-- Genuine native derived locality uses the same lower-Hom model and replacement choices. -/
def isOriginalDerivedLocal (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) : Prop :=
  HomotopicalAlgebra.isDerivedLocal (enrichedLocalizingFamily S)
    ((enrichedCarrierEquivalence (D := D)).functor.obj Z)

/-- The native lower-Hom local-fibrant predicate is pulled to the original objects. -/
def isOriginalDerivedLocalFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) : Prop :=
  HomotopicalAlgebra.isLocalFibrant (enrichedLocalizingFamily S)
    ((enrichedCarrierEquivalence (D := D)).functor.obj Z)

/-- The actual native local-equivalence class quantifies over all lower-carrier targets. -/
def originalDerivedLocalEquivalences (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty (SimplicialPresheaf.{u} D) :=
  (HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).inverseImage
    (enrichedCarrierEquivalence (D := D)).functor

/-- Native derived-local tests are exactly the original same-Q/R precomposition maps. -/
theorem isOriginalDerivedLocal_iff (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) :
    isOriginalDerivedLocal S Z ↔
      ∀ j, SSet.realizationWeakEquivalences (originalDerivedPrecomp D (S j).hom Z) := Iff.rfl

/-- At any actual fibrant target, every arbitrary original raw test agrees with its derived test. -/
theorem isRawLocal_iff_derived (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    isRawLocal S Z ↔ isOriginalDerivedLocal S Z := by
  rw [isOriginalDerivedLocal_iff]
  exact forall_congr' fun j => (originalDerivedPrecomp_weak_iff (S j).hom Z hZ).symm

/-- The actual lower-carrier fibrancy condition is exactly original injective fibrancy. -/
theorem originalCarrier_fibrant_iff (Z : SimplicialPresheaf.{u} D) :
    IsFibrant ((enrichedCarrierEquivalence (D := D)).functor.obj Z) ↔ IsFibrant Z :=
  mappingCarrier_fibrant_iff _

/-- Both local-fibrant formulations use the same actual fibrancy and original family. -/
theorem isOriginalLocalFibrant_iff_derived (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) :
    isOriginalLocalFibrant S Z ↔ isOriginalDerivedLocalFibrant S Z := by
  change (IsFibrant Z ∧ isRawLocal S Z) ↔
    (IsFibrant ((enrichedCarrierEquivalence (D := D)).functor.obj Z) ∧
      isOriginalDerivedLocal S Z)
  rw [originalCarrier_fibrant_iff]
  exact and_congr_right fun hZ => isRawLocal_iff_derived S Z hZ

/-- The native all-target quantifier gives exactly the original raw local-equivalence class. -/
theorem originalLocalEquivalences_eq_derived (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    originalLocalEquivalences S = originalDerivedLocalEquivalences S := by
  ext A B f
  constructor
  · intro h Y hY
    let Z := (enrichedCarrierEquivalence (D := D)).inverse.obj Y
    have hZ : IsFibrant Z := (mappingCarrier_fibrant_iff Y).mp hY.1
    have hLocal : isOriginalDerivedLocal S Z := hY.2
    have hRaw : isOriginalLocalFibrant S Z :=
      ⟨hZ, (isRawLocal_iff_derived S Z hZ).mpr hLocal⟩
    exact (originalDerivedPrecomp_weak_iff f Z hZ).mpr (h Z hRaw)
  · intro h Z hZ
    have hn : isOriginalDerivedLocalFibrant S Z :=
      (isOriginalLocalFibrant_iff_derived S Z).mp hZ
    exact (originalDerivedPrecomp_weak_iff f Z hZ.1).mp
      (h ((enrichedCarrierEquivalence (D := D)).functor.obj Z) hn)

/-- Literal raw local equivalences contain identities by native derived-class reuse. -/
theorem originalLocalEquivalences_containsIdentities
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (originalLocalEquivalences S).ContainsIdentities := by
  rw [originalLocalEquivalences_eq_derived]
  change ((HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).inverseImage
    (enrichedCarrierEquivalence (D := D)).functor).ContainsIdentities
  let : (HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).ContainsIdentities :=
    HomotopicalAlgebra.localEquivalences_containsIdentities _
  infer_instance

/-- All three two-out-of-three directions hold for the actual original weak-test class. -/
theorem originalLocalEquivalences_hasTwoOutOfThreeProperty
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (originalLocalEquivalences S).HasTwoOutOfThreeProperty := by
  rw [originalLocalEquivalences_eq_derived]
  change ((HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).inverseImage
    (enrichedCarrierEquivalence (D := D)).functor).HasTwoOutOfThreeProperty
  let :
      (HomotopicalAlgebra.localEquivalences
        (enrichedLocalizingFamily S)).HasTwoOutOfThreeProperty :=
    HomotopicalAlgebra.localEquivalences_hasTwoOutOfThreeProperty _
  infer_instance

/-- Original whole-Arrow retracts preserve the actual weak tests. -/
theorem originalLocalEquivalences_isStableUnderRetracts
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (originalLocalEquivalences S).IsStableUnderRetracts := by
  rw [originalLocalEquivalences_eq_derived]
  change ((HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).inverseImage
    (enrichedCarrierEquivalence (D := D)).functor).IsStableUnderRetracts
  let : (HomotopicalAlgebra.localEquivalences (enrichedLocalizingFamily S)).IsStableUnderRetracts :=
    HomotopicalAlgebra.localEquivalences_isStableUnderRetracts _
  infer_instance

/-- Every actual original base weak equivalence passes all local-fibrant raw tests. -/
theorem weakEquivalences_le_originalLocalEquivalences
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    weakEquivalences (SimplicialPresheaf.{u} D) ≤ originalLocalEquivalences S := by
  intro A B f hf Z hZ
  exact innerHomPre_weak_of_weakEquivalence f Z hf hZ.1

/-- Every original isomorphism belongs to the literal local weak class. -/
theorem isomorphisms_le_originalLocalEquivalences
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    isomorphisms (SimplicialPresheaf.{u} D) ≤ originalLocalEquivalences S := by
  intro A B f hf
  let : IsIso f := hf
  exact weakEquivalences_le_originalLocalEquivalences S f
    ((weakEquivalences (SimplicialPresheaf.{u} D)).of_isIso f)

/-- The two original target comparison maps preserve every arbitrary source-arrow weak test. -/
theorem rawPrecomp_weak_iff_of_targetWeak {A B X Y : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (g : X ⟶ Y) (hg : weakEquivalences (SimplicialPresheaf.{u} D) g)
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    SSet.realizationWeakEquivalences (innerHomPre f X) ↔
      SSet.realizationWeakEquivalences (innerHomPre f Y) := by
  have hA := innerHomPost_weak_of_weakEquivalence A g hg hX hY
  have hB := innerHomPost_weak_of_weakEquivalence B g hg hX hY
  have hL := SSet.realizationWeakEquivalences.postcomp_iff
    (innerHomPre f X) (innerHomPost A g) hA
  have hR := SSet.realizationWeakEquivalences.precomp_iff
    (innerHomPost B g) (innerHomPre f Y) hB
  rw [innerHom_exchange f g] at hL
  exact hL.symm.trans hR

/-- Original raw locality is invariant under actual weak maps between base-fibrant targets. -/
theorem isRawLocal_iff_of_targetWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
    (hg : weakEquivalences (SimplicialPresheaf.{u} D) g)
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    isRawLocal S X ↔ isRawLocal S Y :=
  forall_congr' fun j => rawPrecomp_weak_iff_of_targetWeak (S j).hom g hg hX hY

/-- Both original local-fibrant predicates are preserved along that actual target weak map. -/
theorem isOriginalLocalFibrant_iff_of_targetWeak
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
    (hg : weakEquivalences (SimplicialPresheaf.{u} D) g)
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    isOriginalLocalFibrant S X ↔ isOriginalLocalFibrant S Y := by
  constructor
  · intro h
    exact ⟨hY, (isRawLocal_iff_of_targetWeak S g hg hX hY).mp h.2⟩
  · intro h
    exact ⟨hX, (isRawLocal_iff_of_targetWeak S g hg hX hY).mpr h.2⟩

/-- Both original weak endpoint comparisons preserve an arbitrary horizontal raw test. -/
theorem rawPrecomp_weak_iff_of_sourceComparison
    {T S : Arrow (SimplicialPresheaf.{u} D)} (r : T ⟶ S)
    (hleft : weakEquivalences (SimplicialPresheaf.{u} D) r.left)
    (hright : weakEquivalences (SimplicialPresheaf.{u} D) r.right)
    (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (innerHomPre T.hom Z) ↔
      SSet.realizationWeakEquivalences (innerHomPre S.hom Z) := by
  have hLw := innerHomPre_weak_of_weakEquivalence r.left Z hleft hZ
  have hRw := innerHomPre_weak_of_weakEquivalence r.right Z hright hZ
  have hL := SSet.realizationWeakEquivalences.postcomp_iff
    (innerHomPre S.hom Z) (innerHomPre r.left Z) hLw
  have hR := SSet.realizationWeakEquivalences.precomp_iff
    (innerHomPre r.right Z) (innerHomPre T.hom Z) hRw
  rw [rawFamilyComparison_square r Z] at hL
  exact hR.symm.trans hL

/-- Weak original family endpoint comparisons give equality of actual local-fibrant predicates. -/
theorem isOriginalLocalFibrant_eq_of_familyComparison
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hleft : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).left)
    (hright : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).right) :
    isOriginalLocalFibrant S = isOriginalLocalFibrant T := by
  funext Z
  apply propext
  apply and_congr_right
  intro hZ
  exact forall_congr' fun j =>
    (rawPrecomp_weak_iff_of_sourceComparison (r j) (hleft j) (hright j) Z hZ).symm

/-- Those same original comparisons give equality of all-original-arrow weak-test classes. -/
theorem originalLocalEquivalences_eq_of_familyComparison
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hleft : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).left)
    (hright : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).right) :
    originalLocalEquivalences S = originalLocalEquivalences T := by
  ext A B f
  change (∀ Z, isOriginalLocalFibrant S Z →
      SSet.realizationWeakEquivalences (innerHomPre f Z)) ↔
    ∀ Z, isOriginalLocalFibrant T Z →
      SSet.realizationWeakEquivalences (innerHomPre f Z)
  rw [isOriginalLocalFibrant_eq_of_familyComparison S T r hleft hright]

/-- Native lower-carrier local-fibrant predicates agree for the same weak family comparisons. -/
theorem isOriginalDerivedLocalFibrant_eq_of_familyComparison
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hleft : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).left)
    (hright : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).right) :
    isOriginalDerivedLocalFibrant S = isOriginalDerivedLocalFibrant T := by
  calc
    _ = isOriginalLocalFibrant S :=
      funext fun Z => propext (isOriginalLocalFibrant_iff_derived S Z).symm
    _ = isOriginalLocalFibrant T :=
      isOriginalLocalFibrant_eq_of_familyComparison S T r hleft hright
    _ = _ := funext fun Z => propext (isOriginalLocalFibrant_iff_derived T Z)

/-- Both all-target native derived weak classes agree for those same original comparisons. -/
theorem originalDerivedLocalEquivalences_eq_of_familyComparison
    (S T : I → Arrow (SimplicialPresheaf.{u} D)) (r : ∀ j, T j ⟶ S j)
    (hleft : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).left)
    (hright : ∀ j, weakEquivalences (SimplicialPresheaf.{u} D) (r j).right) :
    originalDerivedLocalEquivalences S = originalDerivedLocalEquivalences T :=
  (originalLocalEquivalences_eq_derived S).symm.trans
    ((originalLocalEquivalences_eq_of_familyComparison S T r hleft hright).trans
      (originalLocalEquivalences_eq_derived T))

/-- Empty original families impose no raw-locality condition at any target. -/
theorem isRawLocal_of_isEmpty [IsEmpty I] (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Z : SimplicialPresheaf.{u} D) : isRawLocal S Z := fun j => isEmptyElim j

/-- For an empty original family, local-fibrant means exactly actual base-fibrant. -/
theorem isOriginalLocalFibrant_iff_of_isEmpty [IsEmpty I]
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (Z : SimplicialPresheaf.{u} D) :
    isOriginalLocalFibrant S Z ↔ IsFibrant Z :=
  ⟨fun h => h.1, fun h => ⟨h, isRawLocal_of_isEmpty S Z⟩⟩

/-- The empty-family weak class is its literal all-fibrant-target raw test, with no converse
assumed. -/
theorem originalLocalEquivalences_iff_of_isEmpty [IsEmpty I]
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) :
    originalLocalEquivalences S f ↔
      ∀ Z, IsFibrant Z → SSet.realizationWeakEquivalences (innerHomPre f Z) := by
  simp only [originalLocalEquivalences, isOriginalLocalFibrant_iff_of_isEmpty]

/-- The actual same-index resolution retains all same-κ bounds and both local/weak class
equalities. -/
theorem exists_original_locality_family_resolution [Small.{u} I]
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
        isOriginalLocalFibrant S = isOriginalLocalFibrant T ∧
        originalLocalEquivalences S = originalLocalEquivalences T ∧
        isOriginalDerivedLocalFibrant S = isOriginalDerivedLocalFibrant T ∧
        originalDerivedLocalEquivalences S = originalDerivedLocalEquivalences T := by
  obtain ⟨T, r, κ, hκ, hbot, hω, hI, hD, hArD, hSimp, hBase, hLP,
    hRes, hRanks, hSmall, hEligible, hSOA, hFF, _hRaw, _hDerived⟩ :=
      exists_original_small_family_resolution S
  let : Fact κ.IsRegular := hκ
  let : OrderBot κ.ord.ToType := hbot
  have hl (j : I) : weakEquivalences (SimplicialPresheaf.{u} D) (r j).left :=
    (hRes j).2.2.1.2
  have hr (j : I) : weakEquivalences (SimplicialPresheaf.{u} D) (r j).right :=
    (hRes j).2.2.2.1.2
  exact ⟨T, r, κ, hκ, hbot, hω, hI, hD, hArD, hSimp, hBase, hLP,
    hRes, hRanks, hSmall, hEligible, hSOA, hFF,
    isOriginalLocalFibrant_eq_of_familyComparison S T r hl hr,
    originalLocalEquivalences_eq_of_familyComparison S T r hl hr,
    isOriginalDerivedLocalFibrant_eq_of_familyComparison S T r hl hr,
    originalDerivedLocalEquivalences_eq_of_familyComparison S T r hl hr⟩

end SimplicialPresheaf.InjectiveKan

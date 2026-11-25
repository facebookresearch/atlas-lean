/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalReplacement

/-!
# Exact trivial-fibration comparison for original generated locality

The weak class is the actual original generated homotopy-function-complex
test. Its formal weak-class laws are proved from the same original mapping
functor. A local-weak map lifting against local trivial cofibrations is a
retract of its original I projection. Thus the exact trivial-fibration
comparison follows before construction of the localized factorization
system. No localized factorization system is a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CellularLocalizationFactorizations

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} (S : K → Arrow C)

open GeneratedRightMappingEnrichment HomotopyMappingSpaceCategory

/-- Original cofibrations which satisfy the same actual derived local weak test. -/
def localTrivialCofibrations : MorphismProperty C :=
  cofibrations C ⊓ generatedLocalEquivalences d S

/-- The right lifting class of the actual original local trivial cofibrations. -/
def localFibrations : MorphismProperty C := (localTrivialCofibrations d S).rlp

/-- Each original localizing arrow belongs to its original derived local weak class. -/
theorem localizingMaps (k : K) : generatedLocalEquivalences d S (S k).hom :=
  fun _ hZ => hZ.2 k

/-- Original base weakness gives the same original weak mapping tests at arbitrary endpoints. -/
theorem baseWeak_le : weakEquivalences C ≤ generatedLocalEquivalences d S := by
  intro X Y f hf Z _
  exact GeneratedLocalReplacement.nativePrecomp_isIso_of_weak d f hf Z

/-- Every original weak target map acts invertibly on the same complete native derived Hom. -/
theorem nativePostcomp_isIso_of_weak (A : C) {X Y : C} (g : X ⟶ Y)
    (hg : weakEquivalences C g) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A g) := by
  rw [GeneratedRightMappingEnrichment.postcomp_eq]
  exact localize_isIso _ ((weakEquivalence_iff _).mp
    (GeneratedFrameEnrichmentComparison.right_target_weak d A g hg))

/-- Original source tests retain both actual target maps and their complete natural square. -/
theorem nativePrecomp_target_iff {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    (hg : weakEquivalences C g) :
    IsIso (GeneratedRightMappingEnrichment.precomp d f X) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d f Y) := by
  let _ : IsIso (GeneratedRightMappingEnrichment.postcomp d A g) :=
    nativePostcomp_isIso_of_weak d A g hg
  let _ : IsIso (GeneratedRightMappingEnrichment.postcomp d B g) :=
    nativePostcomp_isIso_of_weak d B g hg
  have h : GeneratedRightMappingEnrichment.precomp d f X ≫
      GeneratedRightMappingEnrichment.postcomp d A g =
    GeneratedRightMappingEnrichment.postcomp d B g ≫
      GeneratedRightMappingEnrichment.precomp d f Y :=
    (((bifunctor d).map f.op).naturality g).symm
  constructor
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_left h.symm
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_right h

/-- The entire original derived locality predicate is invariant under each original base weak
target map. -/
theorem derivedLocal_target_iff {X Y : C} (g : X ⟶ Y) (hg : weakEquivalences C g) :
    generatedIsDerivedLocal d S X ↔ generatedIsDerivedLocal d S Y :=
  forall_congr' (fun k => nativePrecomp_target_iff d (S k).hom g hg)

/-- Actual fibrancy and original weak target comparison preserve the same full local-fibrant test.
-/
theorem localFibrant_of_weak {X Y : C} (g : X ⟶ Y) (hg : weakEquivalences C g)
    (hX : generatedLocalFibrant d S X) [IsFibrant Y] : generatedLocalFibrant d S Y :=
  ⟨inferInstance, (derivedLocal_target_iff d S g hg).mp hX.2⟩

/-- The original local weak class contains the actual original identities. -/
theorem weak_containsIdentities : (generatedLocalEquivalences d S).ContainsIdentities where
  id_mem X := baseWeak_le d S _ ((weakEquivalences C).id_mem X)

/-- All directions of two-out-of-three retain the original reversed source composition. -/
theorem weak_twoOutOfThree : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg Z hZ := by
    change (isomorphisms SpaceHo.{v}) (precomp d (f ≫ g) Z)
    rw [GeneratedLocalReplacement.nativePrecomp_comp]
    exact (isomorphisms SpaceHo.{v}).comp_mem _ _ (hg Z hZ) (hf Z hZ)
  of_postcomp f g hg hfg Z hZ := by
    apply (isomorphisms SpaceHo.{v}).of_precomp (precomp d g Z) (precomp d f Z) (hg Z hZ)
    simpa only [← GeneratedLocalReplacement.nativePrecomp_comp] using hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    apply (isomorphisms SpaceHo.{v}).of_postcomp (precomp d g Z) (precomp d f Z) (hf Z hZ)
    simpa only [← GeneratedLocalReplacement.nativePrecomp_comp] using hfg Z hZ

/-- The entire original Arrow retract is mapped by the same original fixed-target functor. -/
theorem weak_retracts : (generatedLocalEquivalences d S).IsStableUnderRetracts where
  of_retract r hg Z hZ := by
    let F := bifunctor d ⋙ (evaluation C SpaceHo.{v}).obj Z
    exact (isomorphisms SpaceHo.{v}).of_retract (r.op.map F) (hg Z hZ)

/-- Every original base trivial cofibration is an actual local trivial cofibration. -/
theorem baseTrivialCofibrations_le :
    trivialCofibrations C ≤ localTrivialCofibrations d S := by
  intro X Y f hf
  exact ⟨hf.1, baseWeak_le d S f hf.2⟩

/-- Original base trivial fibrations lift against all the actual local trivial cofibrations. -/
theorem baseTrivialFibrations_le : trivialFibrations C ≤ localFibrations d S := by
  intro X Y p hp A B i hi
  exact hasLiftingProperty_of_wfs i p hi.1 hp

/-- Every local fibration is a fibration in the same original base model. -/
theorem localFibrations_le_base : localFibrations d S ≤ fibrations C := by
  rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
  exact MorphismProperty.antitone_rlp (baseTrivialCofibrations_le d S)

/-- The actual original I factor constructs the full retract of each local-weak local fibration. -/
def trivialFibrationRetract {X Y : C} (f : X ⟶ Y)
    (hf : (localFibrations d S ⊓ generatedLocalEquivalences d S) f) :
    RetractArrow f (d.cofibrantFactorizationData.factorizationData f).p := by
  let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
  let a := d.cofibrantFactorizationData.factorizationData f
  have hp : generatedLocalEquivalences d S a.p := baseWeak_le d S a.p a.hp.2
  have hi : generatedLocalEquivalences d S a.i := by
    apply (generatedLocalEquivalences d S).of_postcomp a.i a.p hp
    rw [a.fac]
    exact hf.2
  let _ : HasLiftingProperty a.i f := hf.1 a.i ⟨a.hi, hi⟩
  exact RetractArrow.ofRightLiftingProperty a.fac

/-- The complete class comparison is proved for every original arrow and endpoint. -/
theorem trivialFibrations_eq :
    localFibrations d S ⊓ generatedLocalEquivalences d S = trivialFibrations C := by
  apply le_antisymm
  · intro X Y f hf
    exact (trivialFibrations C).of_retract (trivialFibrationRetract d S f hf)
      (d.cofibrantFactorizationData.factorizationData f).hp
  · intro X Y f hf
    exact ⟨baseTrivialFibrations_le d S f hf, baseWeak_le d S f hf.2⟩

/-- Local Whitehead is for the same entire original derived weak class. -/
theorem weak_iff_of_local {X Y : C} (f : X ⟶ Y)
    (hX : generatedLocalFibrant d S X) (hY : generatedLocalFibrant d S Y) :
    generatedLocalEquivalences d S f ↔ weakEquivalences C f :=
  GeneratedLocalReplacement.generatedLocalEquivalences_weak_iff_of_local d S f hX hY

end HomotopicalAlgebra.CellularLocalizationFactorizations

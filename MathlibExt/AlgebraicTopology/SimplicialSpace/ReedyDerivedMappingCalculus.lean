/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerLeibnizHom
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplexCalculus
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.StrictComparison
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# The actual Reedy derived inner mapping calculus

The literal one-fold I and J families supply the chosen functorial
factorizations at one common cardinal. The existing inner enrichment and
SM7 construct the simplicial-model and homotopy-function-complex packets.
Components of the actual mapping object `H(QX,RY)` are identified with
Mathlib's fibrant-object homotopy category, naturally in both original maps.

The replacements are the actual chosen Q and R, with their original counit
and unit. No model, mapping calculus, weak detector, localizing family or
desired component equivalence is a caller-supplied input.

Source: Rezk, Sections 2 and 9, together with the model-category fundamental
lemma. The native fibrant-resolution bridge keeps the original resolution
maps and both inverse triangles.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty MonoidalCategory
open scoped SimplicialSpace.Inner Simplicial MonoidalCategory

namespace SimplicialSpace.ReedyModel

attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
attribute [local instance] SSet.modelCategoryQuillen.modelCategory

private structure CommonGenerationWitness where
  κ : Cardinal.{u}
  regular : Fact κ.IsRegular
  orderBot : OrderBot κ.ord.ToType
  smallI :
    letI : Fact κ.IsRegular := regular
    letI : OrderBot κ.ord.ToType := orderBot
    ReedyGeneratingFamilies.I.{u}.IsCardinalForSmallObjectArgument κ
  smallJ :
    letI : Fact κ.IsRegular := regular
    letI : OrderBot κ.ord.ToType := orderBot
    ReedyGeneratingFamilies.J.{u}.IsCardinalForSmallObjectArgument κ

private theorem exists_commonGenerationWitness : Nonempty CommonGenerationWitness.{u} := by
  obtain ⟨κ, hκ, hbot, h⟩ :=
    ReedyGeneratingFamilies.exists_cofibrantGenerationData.{u}
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  rcases h with ⟨_hC, hI, hJ, _cg, _hcgI, _hcgJ, _dI, _dJ, _hdI, _hdJ⟩
  exact ⟨⟨κ, hκ, hbot, hI, hJ⟩⟩

private noncomputable def commonGenerationWitness : CommonGenerationWitness.{u} :=
  Classical.choice exists_commonGenerationWitness

private noncomputable def factorizationPair :
    FunctorialFactorizationData (cofibrations SimplicialSpace.{u})
        (trivialFibrations SimplicialSpace.{u}) ×
      FunctorialFactorizationData (trivialCofibrations SimplicialSpace.{u})
        (fibrations SimplicialSpace.{u}) := by
  let w := commonGenerationWitness.{u}
  letI : Fact w.κ.IsRegular := w.regular
  letI : OrderBot w.κ.ord.ToType := w.orderBot
  letI : ReedyGeneratingFamilies.I.{u}.IsCardinalForSmallObjectArgument w.κ := w.smallI
  letI : ReedyGeneratingFamilies.J.{u}.IsCardinalForSmallObjectArgument w.κ := w.smallJ
  let dI := SmallObject.functorialFactorizationData ReedyGeneratingFamilies.I.{u} w.κ
  let dJ := SmallObject.functorialFactorizationData ReedyGeneratingFamilies.J.{u} w.κ
  rw [ReedyGeneratingFamilies.I_rlp_eq_trivialFibrations,
    trivialFibrations_llp] at dI
  rw [ReedyGeneratingFamilies.J_rlp_eq_fibrations, fibrations_llp] at dJ
  exact ⟨dI, dJ⟩

/-- The actual common-cardinal I small-object factorization in the named Reedy classes. -/
noncomputable def cofibrationTrivialFibrationFactorization :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    FunctorialFactorizationData (cofibrations SimplicialSpace.{u})
      (trivialFibrations SimplicialSpace.{u}) :=
  factorizationPair.1

/-- The actual common-cardinal J small-object factorization in the named Reedy classes. -/
noncomputable def trivialCofibrationFibrationFactorization :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    FunctorialFactorizationData (trivialCofibrations SimplicialSpace.{u})
      (fibrations SimplicialSpace.{u}) :=
  factorizationPair.2

/-- The actual Reedy I data supplies factorization existence in the designated scope. -/
noncomputable scoped instance instHasFunctorialFactorizationCofibrationsTrivialFibrations :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HasFunctorialFactorization (cofibrations SimplicialSpace.{u})
      (trivialFibrations SimplicialSpace.{u}) :=
  ⟨⟨cofibrationTrivialFibrationFactorization⟩⟩

/-- The actual Reedy J data supplies factorization existence in the designated scope. -/
noncomputable scoped instance instHasFunctorialFactorizationTrivialCofibrationsFibrations :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HasFunctorialFactorization (trivialCofibrations SimplicialSpace.{u})
      (fibrations SimplicialSpace.{u}) :=
  ⟨⟨trivialCofibrationFibrationFactorization⟩⟩

open scoped SimplicialSpace.ReedyModel

/-- Actual two-variable weak invariance of the native inner mapping bifunctor. -/
theorem invarianceData :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopyFunctionComplexInvarianceData (C := SimplicialSpace.{u}) where
  precompWeakOfWeakEquivalence f hX hY hf Z hZ :=
    inner_precomp_weak_of_weak f Z hX hY hf hZ
  postcompWeakOfWeakEquivalence := fun X hX {_Y _Z} g hY hZ hg =>
    inner_postcomp_weak_of_weak X g hX hY hZ hg

/-- The source-variable packet supplied by the same actual two-variable proof. -/
theorem precompData :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopyFunctionComplexPrecompData (C := SimplicialSpace.{u}) :=
  invarianceData.toHomotopyFunctionComplexPrecompData

/-- The literal inner pushout-product with the original simplicial boundary inclusion. -/
noncomputable def boundaryTensor (n : ℕ) {A B : SimplicialSpace.{u}} (i : A ⟶ B) :
    Arrow SimplicialSpace.{u} :=
  Arrow.mk (Functor.PushoutObjObj.ofHasPushout
    innerTensorBifunctor i (SSet.boundary n).ι).ι

private theorem boundaryTensor_cofibration (n : ℕ) {A B : SimplicialSpace.{u}}
    (i : A ⟶ B) (hi : cofibrations SimplicialSpace.{u} i) :
    cofibrations SimplicialSpace.{u} (boundaryTensor n i).hom := by
  let pp := Functor.PushoutObjObj.ofHasPushout
    innerTensorBifunctor i (SSet.boundary n).ι
  have hj : cofibrations SSet.{u} (SSet.boundary n).ι :=
    (HomotopicalAlgebra.cofibration_iff _).1
      (SSet.modelCategoryQuillen.cofibration_of_mono _)
  exact inner_pushoutObjObj_cofibration i (SSet.boundary n).ι pp hi hj

private theorem boundaryTensor_lifting_iff (n : ℕ) {A B : SimplicialSpace.{u}}
    (i : A ⟶ B) (Z : SimplicialSpace.{u})
    (_hi : cofibrations SimplicialSpace.{u} i) (_hZ : IsFibrant Z) :
    HasLiftingProperty (SSet.boundary n).ι ((innerHomFunctor.map i.op).app Z) ↔
      HasLiftingProperty (boundaryTensor n i).hom (terminal.from Z) := by
  let _ : (innerHomFunctor.obj (op A)).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj A).isRightAdjoint
  let _ : (innerHomFunctor.obj (op B)).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj B).isRightAdjoint
  let pp := Functor.PushoutObjObj.ofHasPushout
    innerTensorBifunctor i (SSet.boundary n).ι
  let q := Functor.PullbackObjObj.ofIsTerminal innerHomFunctor i
    (terminal.from Z) terminalIsTerminal
  exact (innerTensorHomAdjunction₂.hasLiftingProperty_iff pp q).symm

private theorem rawPrecomp_zero_surjective_of_weak {A B : SimplicialSpace.{u}}
    (i : A ⟶ B) (Z : SimplicialSpace.{u})
    (hi : cofibrations SimplicialSpace.{u} i) (hZ : IsFibrant Z)
    (hw : SSet.realizationWeakEquivalences ((innerHomFunctor.map i.op).app Z)) :
    Function.Surjective (((innerHomFunctor.map i.op).app Z).app (op ⦋0⦌)) := by
  let p := (innerHomFunctor.map i.op).app Z
  have hpTriv : trivialFibrations SSet.{u} p :=
    ⟨inner_precomp_fibration i Z hi hZ, hw⟩
  intro b
  let hinit : IsInitial
      ((SSet.boundary 0 : (SSet.stdSimplex.obj ⦋0⦌ : SSet.{u}).Subcomplex) :
        SSet.{u}) :=
    (SSet.Subcomplex.isInitialBot
      (X := (SSet.stdSimplex.obj ⦋0⦌ : SSet.{u}))).ofIso
        (SSet.Subcomplex.eqToIso SSet.boundary_zero).symm
  let top : (SSet.boundary 0 : SSet.{u}) ⟶ (innerHomFunctor.obj (op B)).obj Z :=
    hinit.to _
  let sq : CommSq top (SSet.boundary 0).ι p (SSet.yonedaEquiv.symm b) :=
    ⟨SSet.boundary.hom_ext₀⟩
  have hl : HasLiftingProperty (SSet.boundary 0).ι p :=
    hasLiftingProperty_of_wfs (SSet.boundary 0).ι p
      ((HomotopicalAlgebra.cofibration_iff _).1
        (SSet.modelCategoryQuillen.cofibration_of_mono _)) hpTriv
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply, sq.fac_right]

private theorem rawPrecomp_weak_of_boundary_lifts {A B : SimplicialSpace.{u}}
    (i : A ⟶ B) (Z : SimplicialSpace.{u})
    (_hi : cofibrations SimplicialSpace.{u} i) (_hZ : IsFibrant Z)
    (hlift : ∀ n, HasLiftingProperty (SSet.boundary n).ι
      ((innerHomFunctor.map i.op).app Z)) :
    SSet.realizationWeakEquivalences ((innerHomFunctor.map i.op).app Z) := by
  have hp : SSet.modelCategoryQuillen.I.{u}.rlp
      ((innerHomFunctor.map i.op).app Z) := by
    intro K L j hj
    rcases hj with ⟨n⟩
    exact hlift n
  exact SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ hp

private theorem boundaryTensor_rawPrecomp_weak {A B : SimplicialSpace.{u}}
    (i : A ⟶ B) (Z : SimplicialSpace.{u})
    (hi : cofibrations SimplicialSpace.{u} i) (hZ : IsFibrant Z)
    (hw : SSet.realizationWeakEquivalences ((innerHomFunctor.map i.op).app Z))
    (n : ℕ) :
    SSet.realizationWeakEquivalences
      ((innerHomFunctor.map (boundaryTensor n i).hom.op).app Z) := by
  let p := (innerHomFunctor.map i.op).app Z
  let _ : Fibration p :=
    (HomotopicalAlgebra.fibration_iff _).2 (inner_precomp_fibration i Z hi hZ)
  let _ : WeakEquivalence p := (HomotopicalAlgebra.weakEquivalence_iff _).2 hw
  let _ : Cofibration (SSet.boundary n).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  have hscalar : SSet.realizationWeakEquivalences
      (SSet.ihomToPullback (SSet.boundary n).ι p) :=
    (SSet.ihomToPullback_mem_trivialFibrations_of_right (SSet.boundary n).ι p).2
  let pp := Functor.PushoutObjObj.ofHasPushout
    innerTensorBifunctor i (SSet.boundary n).ι
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (innerLeibnizHomIso i (SSet.boundary n).ι pp Z)).2 hscalar

/-- All actual tensor–Hom and Kan mapping fields for the native Reedy model. -/
noncomputable def simplicialModelData :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    SimplicialModelCategoryData (C := SimplicialSpace.{u}) where
  boundaryTensor := boundaryTensor
  boundaryTensor_cofibration := boundaryTensor_cofibration
  boundaryTensor_lifting_iff := boundaryTensor_lifting_iff
  rawPrecomp_app_zero := inner_precomp_app_zero
  rawPrecomp_zero_surjective_of_weak := rawPrecomp_zero_surjective_of_weak
  rawPrecomp_weak_of_boundary_lifts := rawPrecomp_weak_of_boundary_lifts
  boundaryTensor_rawPrecomp_weak := boundaryTensor_rawPrecomp_weak
  realizationWeak_bijective_piZero _ hf :=
    SSet.realizationWeakEquivalences.bijective_mapπ₀ hf

private theorem realizationWeak_iff_of_square
    {A B C D : SSet.{u}} (top : A ⟶ B) (bottom : C ⟶ D)
    (left : A ⟶ C) (right : B ⟶ D)
    (hsq : top ≫ right = left ≫ bottom)
    (hleft : SSet.realizationWeakEquivalences left)
    (hright : SSet.realizationWeakEquivalences right) :
    SSet.realizationWeakEquivalences top ↔
      SSet.realizationWeakEquivalences bottom := by
  constructor
  · intro htop
    have hcomp := SSet.realizationWeakEquivalences.comp_mem top right htop hright
    rw [hsq] at hcomp
    exact SSet.realizationWeakEquivalences.of_precomp left bottom hleft hcomp
  · intro hbottom
    have hcomp := SSet.realizationWeakEquivalences.comp_mem left bottom hleft hbottom
    rw [← hsq] at hcomp
    exact SSet.realizationWeakEquivalences.of_postcomp top right hright hcomp

/-- For every original arrow and fibrant target, raw and chosen derived
precomposition have exactly the same realization weakness. No arrow cofibration
is assumed; both source objects are cofibrant in the actual named Reedy model. -/
theorem derived_weak_iff_raw_of_isFibrant {A B : SimplicialSpace.{u}} (i : A ⟶ B)
    (Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant Z →
      (SSet.realizationWeakEquivalences
          (derivedMappingPrecomp (C := SimplicialSpace.{u}) i Z) ↔
        SSet.realizationWeakEquivalences ((innerHomFunctor.map i.op).app Z)) := by
  intro hZ
  let _ : IsFibrant Z := hZ
  let _ : IsCofibrant A := isCofibrant A
  let _ : IsCofibrant B := isCofibrant B
  let η := strictToDerivedMappingObject (C := SimplicialSpace.{u})
  have hA : SSet.realizationWeakEquivalences ((η.app (op A)).app Z) :=
    strictToDerivedMappingObject_app_mem_realizationWeakEquivalences
      invarianceData A Z
  have hB : SSet.realizationWeakEquivalences ((η.app (op B)).app Z) :=
    strictToDerivedMappingObject_app_mem_realizationWeakEquivalences
      invarianceData B Z
  have hnat : (innerHomFunctor.map i.op).app Z ≫ (η.app (op A)).app Z =
      (η.app (op B)).app Z ≫ derivedMappingPrecomp (C := SimplicialSpace.{u}) i Z :=
    congr_fun (congr_arg NatTrans.app (η.naturality i.op)) Z
  exact (realizationWeak_iff_of_square _ _ _ _ hnat hB hA).symm

/-- The cofibrant-arrow form required by the generic lifting calculus is a
specialization of the all-original-arrow weak comparison. -/
theorem derived_weak_iff_raw {A B : SimplicialSpace.{u}} (i : A ⟶ B)
    (Z : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} i → IsFibrant Z →
      (SSet.realizationWeakEquivalences
          (derivedMappingPrecomp (C := SimplicialSpace.{u}) i Z) ↔
        SSet.realizationWeakEquivalences ((innerHomFunctor.map i.op).app Z)) :=
  fun _hi hZ => derived_weak_iff_raw_of_isFibrant i Z hZ

private noncomputable def fibrantHomEquiv {X Y : SimplicialSpace.{u}}
    [IsCofibrant X] [IsFibrant X] [IsFibrant Y] :
    LeftHomotopyClass X Y ≃
      (FibrantObject.toHoCat.obj (FibrantObject.mk X) ⟶
        FibrantObject.toHoCat.obj (FibrantObject.mk Y)) := by
  let toHom : LeftHomotopyClass X Y →
      (FibrantObject.toHoCat.obj (FibrantObject.mk X) ⟶
        FibrantObject.toHoCat.obj (FibrantObject.mk Y)) :=
    Quot.lift
      (fun f ↦ FibrantObject.toHoCat.map (FibrantObject.homMk f))
      (fun _ _ h ↦ by
        apply FibrantObject.toHoCat_map_eq
        rw [FibrantObject.homRel_iff_leftHomotopyRel]
        exact h)
  refine Equiv.ofBijective toHom ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨f, rfl⟩ := a.mk_surjective
    obtain ⟨g, rfl⟩ := b.mk_surjective
    apply LeftHomotopyClass.sound
    exact (FibrantObject.toHoCat_map_eq_iff
      (FibrantObject.homMk f) (FibrantObject.homMk g)).mp hab
  · intro k
    obtain ⟨f, rfl⟩ := FibrantObject.toHoCat.map_surjective k
    exact ⟨LeftHomotopyClass.mk f.hom, rfl⟩

private noncomputable def leftPrecompEquiv {X Y T : SimplicialSpace.{u}}
    (i : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence i] [IsFibrant T] :
    LeftHomotopyClass Y T ≃ LeftHomotopyClass X T := by
  let pre := (innerHomFunctor.map i.op).app T
  have hw : SSet.realizationWeakEquivalences pre :=
    inner_precomp_weak_of_weak i T inferInstance inferInstance
      WeakEquivalence.mem inferInstance
  let componentEquiv : SSet.π₀ ((innerHomFunctor.obj (op Y)).obj T) ≃
      SSet.π₀ ((innerHomFunctor.obj (op X)).obj T) :=
    Equiv.ofBijective (SSet.mapπ₀ pre)
      (SSet.realizationWeakEquivalences.bijective_mapπ₀ hw)
  exact (mappingComponentEquiv Y T).symm.trans
    (componentEquiv.trans (mappingComponentEquiv X T))

private theorem leftPrecompEquiv_mk {X Y T : SimplicialSpace.{u}} (i : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence i] [IsFibrant T] (f : Y ⟶ T) :
    leftPrecompEquiv i (LeftHomotopyClass.mk f) =
      LeftHomotopyClass.mk (i ≫ f) := by
  change mappingComponentEquiv X T
      (SSet.mapπ₀ ((innerHomFunctor.map i.op).app T)
        ((mappingComponentEquiv Y T).symm (LeftHomotopyClass.mk f))) = _
  rw [mappingComponentEquiv_precompose, Equiv.apply_symm_apply,
    leftHomotopyClassPrecomp_mk]

private noncomputable def leftPostcompEquiv {X Y Z : SimplicialSpace.{u}}
    (g : Y ⟶ Z) [IsCofibrant X] [IsFibrant Y] [IsFibrant Z] [WeakEquivalence g] :
    LeftHomotopyClass X Y ≃ LeftHomotopyClass X Z :=
  Equiv.ofBijective (fun f ↦ f.postcomp g)
    (LeftHomotopyClass.postcomp_bijective_of_weakEquivalence X g)

private theorem fibrantHomEquiv_mk {X Y : SimplicialSpace.{u}}
    [IsCofibrant X] [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    fibrantHomEquiv (LeftHomotopyClass.mk f) =
      FibrantObject.toHoCat.map (FibrantObject.homMk f) := rfl

/-- Components between the actual chosen Q/R replacements, before the endpoint transport. -/
noncomputable def replacedPiZeroEquiv (X Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    SSet.π₀ ((innerHomFunctor.obj
      (op ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X))).obj
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y)) ≃
      (FibrantObject.HoCat.resolution.obj
          ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X) ⟶
        FibrantObject.HoCat.resolution.obj
          ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y)) := by
  let QX := (cofibrantReplacement (C := SimplicialSpace.{u})).obj X
  let RY := (fibrantReplacement (C := SimplicialSpace.{u})).obj Y
  let RX := FibrantObject.HoCat.resolutionObj QX
  let RRY := FibrantObject.HoCat.resolutionObj RY
  let iX := FibrantObject.HoCat.iResolutionObj QX
  let iY := FibrantObject.HoCat.iResolutionObj RY
  letI : IsCofibrant QX := isCofibrant QX
  letI : IsCofibrant RX := isCofibrant RX
  letI : IsCofibrant RY := isCofibrant RY
  letI : IsCofibrant RRY := isCofibrant RRY
  letI : WeakEquivalence iX := by infer_instance
  letI : WeakEquivalence iY := by infer_instance
  exact (mappingComponentEquiv QX RY).trans
    ((leftPostcompEquiv iY).trans
      ((leftPrecompEquiv iX).symm.trans fibrantHomEquiv))

/-- The original map between QX and RY represents its actual Ho-resolution image. -/
theorem replacedPiZeroEquiv_mk (X Y : SimplicialSpace.{u})
    (g : (cofibrantReplacement (C := SimplicialSpace.{u})).obj X ⟶
      (fibrantReplacement (C := SimplicialSpace.{u})).obj Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    replacedPiZeroEquiv X Y
        (SSet.π₀.mk (innerHomEquiv
          ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X)
          ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y) g)) =
      FibrantObject.HoCat.resolution.map g := by
  let QX := (cofibrantReplacement (C := SimplicialSpace.{u})).obj X
  let RY := (fibrantReplacement (C := SimplicialSpace.{u})).obj Y
  let RX := FibrantObject.HoCat.resolutionObj QX
  let RRY := FibrantObject.HoCat.resolutionObj RY
  let iX := FibrantObject.HoCat.iResolutionObj QX
  let iY := FibrantObject.HoCat.iResolutionObj RY
  let rg := FibrantObject.HoCat.resolutionMap g
  let _ : IsCofibrant QX := isCofibrant QX
  let _ : IsCofibrant RX := isCofibrant RX
  let _ : IsCofibrant RY := isCofibrant RY
  let _ : IsCofibrant RRY := isCofibrant RRY
  let _ : WeakEquivalence iX := by infer_instance
  let _ : WeakEquivalence iY := by infer_instance
  have hpre : leftPrecompEquiv iX (LeftHomotopyClass.mk rg) =
      LeftHomotopyClass.mk (g ≫ iY) := by
    rw [leftPrecompEquiv_mk]
    congr 1
    exact FibrantObject.HoCat.resolutionMap_fac g
  have hinv : (leftPrecompEquiv iX).symm
      (LeftHomotopyClass.mk (g ≫ iY)) = LeftHomotopyClass.mk rg := by
    apply (leftPrecompEquiv iX).injective
    rw [Equiv.apply_symm_apply, hpre]
  change fibrantHomEquiv
      ((leftPrecompEquiv iX).symm
        ((leftPostcompEquiv iY)
          (mappingComponentEquiv QX RY
            (SSet.π₀.mk (innerHomEquiv QX RY g))))) = _
  have hcomp : mappingComponentEquiv QX RY
      (SSet.π₀.mk (innerHomEquiv QX RY g)) = LeftHomotopyClass.mk g :=
    (mappingComponentEquiv_mk QX RY (innerHomEquiv QX RY g)).trans
      (congrArg LeftHomotopyClass.mk ((innerHomEquiv QX RY).symm_apply_apply g))
  have hm := congrArg
    (fun q : LeftHomotopyClass QX RY => fibrantHomEquiv
      ((leftPrecompEquiv iX).symm ((leftPostcompEquiv iY) q))) hcomp
  have hp : fibrantHomEquiv
      ((leftPrecompEquiv iX).symm ((leftPostcompEquiv iY) (LeftHomotopyClass.mk g))) =
    fibrantHomEquiv ((leftPrecompEquiv iX).symm
      (LeftHomotopyClass.mk (g ≫ iY))) := rfl
  have hi : fibrantHomEquiv ((leftPrecompEquiv iX).symm
      (LeftHomotopyClass.mk (g ≫ iY))) =
    fibrantHomEquiv (X := RX) (Y := RRY) (LeftHomotopyClass.mk rg) :=
    congrArg (fibrantHomEquiv (X := RX) (Y := RRY)) hinv
  have hf : fibrantHomEquiv (X := RX) (Y := RRY) (LeftHomotopyClass.mk rg) =
      FibrantObject.HoCat.resolution.map g :=
    fibrantHomEquiv_mk rg
  exact hm.trans (hp.trans (hi.trans hf))

private theorem resolution_map_isIso_of_weak {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hf : weakEquivalences SimplicialSpace.{u} f) :
    IsIso (FibrantObject.HoCat.resolution.map f) := by
  let rf := FibrantObject.HoCat.resolutionMap f
  let RX := FibrantObject.HoCat.resolutionObj X
  let RY := FibrantObject.HoCat.resolutionObj Y
  let _ : IsCofibrant RX := isCofibrant RX
  let _ : IsCofibrant RY := isCofibrant RY
  let _ : WeakEquivalence rf :=
    (FibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).2
      ((HomotopicalAlgebra.weakEquivalence_iff f).2 hf)
  obtain ⟨g, hfg, hgf⟩ := LeftHomotopyClass.whitehead rf
  let rg : FibrantObject.mk RY ⟶ FibrantObject.mk RX := FibrantObject.homMk g
  have hfg' : FibrantObject.toHoCat.map (FibrantObject.homMk rf) ≫
      FibrantObject.toHoCat.map rg = 𝟙 _ := by
    rw [← FibrantObject.toHoCat.map_comp, ← FibrantObject.toHoCat.map_id]
    apply FibrantObject.toHoCat_map_eq
    exact hfg
  have hgf' : FibrantObject.toHoCat.map rg ≫
      FibrantObject.toHoCat.map (FibrantObject.homMk rf) = 𝟙 _ := by
    rw [← FibrantObject.toHoCat.map_comp, ← FibrantObject.toHoCat.map_id]
    apply FibrantObject.toHoCat_map_eq
    exact hgf
  change IsIso (FibrantObject.toHoCat.map (FibrantObject.homMk rf))
  exact ⟨⟨FibrantObject.toHoCat.map rg, hfg', hgf'⟩⟩

/-- The actual Q-counit becomes the original endpoint isomorphism in Ho-resolution. -/
noncomputable def cofibrantReplacementResolutionIso (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    FibrantObject.HoCat.resolution.obj
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X) ≅
      FibrantObject.HoCat.resolution.obj X := by
  let f := (cofibrantReplacementCounit (C := SimplicialSpace.{u})).app X
  letI : IsIso (FibrantObject.HoCat.resolution.map f) :=
    resolution_map_isIso_of_weak f WeakEquivalence.mem
  exact asIso (FibrantObject.HoCat.resolution.map f)

/-- The actual R-unit becomes the original endpoint isomorphism in Ho-resolution. -/
noncomputable def fibrantReplacementResolutionIso (Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    FibrantObject.HoCat.resolution.obj Y ≅
      FibrantObject.HoCat.resolution.obj
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y) := by
  let f := (fibrantReplacementUnit (C := SimplicialSpace.{u})).app Y
  letI : IsIso (FibrantObject.HoCat.resolution.map f) :=
    resolution_map_isIso_of_weak f WeakEquivalence.mem
  exact asIso (FibrantObject.HoCat.resolution.map f)

/-- The source endpoint transport has the literal Q-counit image as its hom. -/
@[simp] theorem cofibrantReplacementResolutionIso_hom (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (cofibrantReplacementResolutionIso X).hom =
      FibrantObject.HoCat.resolution.map
        ((cofibrantReplacementCounit (C := SimplicialSpace.{u})).app X) := rfl

/-- The target endpoint transport has the literal R-unit image as its hom. -/
@[simp] theorem fibrantReplacementResolutionIso_hom (Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (fibrantReplacementResolutionIso Y).hom =
      FibrantObject.HoCat.resolution.map
        ((fibrantReplacementUnit (C := SimplicialSpace.{u})).app Y) := rfl

/-- Transport original morphisms between QX and RY back to the original Ho endpoints. -/
noncomputable def replacementHomEquiv (X Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (FibrantObject.HoCat.resolution.obj
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X) ⟶
      FibrantObject.HoCat.resolution.obj
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y)) ≃
      (FibrantObject.HoCat.resolution.obj X ⟶ FibrantObject.HoCat.resolution.obj Y) :=
  (cofibrantReplacementResolutionIso X).homCongr
    (fibrantReplacementResolutionIso Y).symm

/-- Components of the actual chosen derived inner mapping object are native Ho morphisms. -/
noncomputable def piZeroEquiv (X Y : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    SSet.π₀ (((derivedMappingObject (C := SimplicialSpace.{u})).obj (op X)).obj Y) ≃
      (FibrantObject.HoCat.resolution.obj X ⟶ FibrantObject.HoCat.resolution.obj Y) :=
  (replacedPiZeroEquiv X Y).trans (replacementHomEquiv X Y)

/-- The literal zero-simplex represented by a map between the chosen replacements. -/
noncomputable def derivedZero (X Y : SimplicialSpace.{u})
    (g : (cofibrantReplacement (C := SimplicialSpace.{u})).obj X ⟶
      (fibrantReplacement (C := SimplicialSpace.{u})).obj Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (((derivedMappingObject (C := SimplicialSpace.{u})).obj (op X)).obj Y).obj (op ⦋0⦌) :=
  innerHomEquiv
    ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X)
    ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y) g

/-- The represented component keeps both original Q/R endpoint transports. -/
theorem piZeroEquiv_mk (X Y : SimplicialSpace.{u})
    (g : (cofibrantReplacement (C := SimplicialSpace.{u})).obj X ⟶
      (fibrantReplacement (C := SimplicialSpace.{u})).obj Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    piZeroEquiv X Y (SSet.π₀.mk (derivedZero X Y g)) =
      (cofibrantReplacementResolutionIso X).inv ≫
        FibrantObject.HoCat.resolution.map g ≫
          (fibrantReplacementResolutionIso Y).inv := by
  change replacementHomEquiv X Y
      (replacedPiZeroEquiv X Y (SSet.π₀.mk (innerHomEquiv
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X)
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y) g))) = _
  rw [replacedPiZeroEquiv_mk]
  rfl

private theorem derivedMappingPrecomp_piZero_mk {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (Z : SimplicialSpace.{u})
    (g : (cofibrantReplacement (C := SimplicialSpace.{u})).obj Y ⟶
      (fibrantReplacement (C := SimplicialSpace.{u})).obj Z) :
    SSet.mapπ₀ (derivedMappingPrecomp (C := SimplicialSpace.{u}) f Z)
        (SSet.π₀.mk (derivedZero Y Z g)) =
      SSet.π₀.mk (derivedZero X Z
        ((cofibrantReplacement (C := SimplicialSpace.{u})).map f ≫ g)) := by
  rw [SSet.mapπ₀_mk]
  congr 1
  change ((innerHomFunctor.map
      ((cofibrantReplacement (C := SimplicialSpace.{u})).map f).op).app
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Z)).app (op ⦋0⦌)
      (innerHomEquiv
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj Y)
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Z) g) = _
  exact inner_precomp_app_zero
    ((cofibrantReplacement (C := SimplicialSpace.{u})).map f)
    ((fibrantReplacement (C := SimplicialSpace.{u})).obj Z) g

private theorem derivedMappingPostcomp_piZero_mk (X : SimplicialSpace.{u})
    {Y Z : SimplicialSpace.{u}} (g : Y ⟶ Z)
    (f : (cofibrantReplacement (C := SimplicialSpace.{u})).obj X ⟶
      (fibrantReplacement (C := SimplicialSpace.{u})).obj Y) :
    SSet.mapπ₀ (derivedMappingPostcomp (C := SimplicialSpace.{u}) X g)
        (SSet.π₀.mk (derivedZero X Y f)) =
      SSet.π₀.mk (derivedZero X Z
        (f ≫ (fibrantReplacement (C := SimplicialSpace.{u})).map g)) := by
  let QX := (cofibrantReplacement (C := SimplicialSpace.{u})).obj X
  let RY := (fibrantReplacement (C := SimplicialSpace.{u})).obj Y
  let RZ := (fibrantReplacement (C := SimplicialSpace.{u})).obj Z
  let _ : IsCofibrant QX := isCofibrant QX
  let _ : IsFibrant RY := by infer_instance
  let _ : IsFibrant RZ := by infer_instance
  apply (mappingComponentEquiv QX RZ).injective
  change mappingComponentEquiv QX RZ
      (SSet.mapπ₀ ((innerHomFunctor.obj (op QX)).map
        ((fibrantReplacement (C := SimplicialSpace.{u})).map g))
        (SSet.π₀.mk (innerHomEquiv QX RY f))) =
    mappingComponentEquiv QX RZ (SSet.π₀.mk (innerHomEquiv QX RZ
      (f ≫ (fibrantReplacement (C := SimplicialSpace.{u})).map g)))
  have hsrc : mappingComponentEquiv QX RY
      (SSet.π₀.mk (innerHomEquiv QX RY f)) = LeftHomotopyClass.mk f :=
    (mappingComponentEquiv_mk QX RY (innerHomEquiv QX RY f)).trans
      (congrArg LeftHomotopyClass.mk ((innerHomEquiv QX RY).symm_apply_apply f))
  let Rg := (fibrantReplacement (C := SimplicialSpace.{u})).map g
  have htgt : mappingComponentEquiv QX RZ
      (SSet.π₀.mk (innerHomEquiv QX RZ (f ≫ Rg))) = LeftHomotopyClass.mk (f ≫ Rg) :=
    (mappingComponentEquiv_mk QX RZ (innerHomEquiv QX RZ (f ≫ Rg))).trans
      (congrArg LeftHomotopyClass.mk
        ((innerHomEquiv QX RZ).symm_apply_apply (f ≫ Rg)))
  have hpost : (LeftHomotopyClass.mk f).postcomp Rg = LeftHomotopyClass.mk (f ≫ Rg) := rfl
  exact (mappingComponentEquiv_postcompose Rg
    (SSet.π₀.mk (innerHomEquiv QX RY f))).trans
      ((congrArg (fun q => q.postcomp Rg) hsrc).trans (hpost.trans htgt.symm))

/-- Inverse Q-endpoint transport retains the original source naturality equation. -/
theorem cofibrantReplacementResolutionIso_naturality
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    (cofibrantReplacementResolutionIso X).inv ≫
        FibrantObject.HoCat.resolution.map
          ((cofibrantReplacement (C := SimplicialSpace.{u})).map f) =
      FibrantObject.HoCat.resolution.map f ≫
        (cofibrantReplacementResolutionIso Y).inv := by
  let q := cofibrantReplacementCounit (C := SimplicialSpace.{u})
  have hnat :
      FibrantObject.HoCat.resolution.map
          ((cofibrantReplacement (C := SimplicialSpace.{u})).map f) ≫
        FibrantObject.HoCat.resolution.map (q.app Y) =
      FibrantObject.HoCat.resolution.map (q.app X) ≫
        FibrantObject.HoCat.resolution.map f := by
    simpa only [← FibrantObject.HoCat.resolution.map_comp, Functor.id_map] using
      congrArg FibrantObject.HoCat.resolution.map (q.naturality f)
  apply (cancel_mono (cofibrantReplacementResolutionIso Y).hom).1
  have hX : (cofibrantReplacementResolutionIso X).hom =
      FibrantObject.HoCat.resolution.map (q.app X) := rfl
  have hY : (cofibrantReplacementResolutionIso Y).hom =
      FibrantObject.HoCat.resolution.map (q.app Y) := rfl
  rw [hY, Category.assoc, hnat, ← Category.assoc, ← hX, ← hY]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Inverse R-endpoint transport retains the original target naturality equation. -/
theorem fibrantReplacementResolutionIso_naturality
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    FibrantObject.HoCat.resolution.map
        ((fibrantReplacement (C := SimplicialSpace.{u})).map f) ≫
        (fibrantReplacementResolutionIso Y).inv =
      (fibrantReplacementResolutionIso X).inv ≫
        FibrantObject.HoCat.resolution.map f := by
  let r := fibrantReplacementUnit (C := SimplicialSpace.{u})
  have hnat :
      FibrantObject.HoCat.resolution.map f ≫
          (fibrantReplacementResolutionIso Y).hom =
        (fibrantReplacementResolutionIso X).hom ≫
          FibrantObject.HoCat.resolution.map
            ((fibrantReplacement (C := SimplicialSpace.{u})).map f) := by
    simpa only [fibrantReplacementResolutionIso_hom,
      ← FibrantObject.HoCat.resolution.map_comp, Functor.id_map] using
      congrArg FibrantObject.HoCat.resolution.map (r.naturality f)
  apply (cancel_epi (fibrantReplacementResolutionIso X).hom).1
  calc
    (fibrantReplacementResolutionIso X).hom ≫
          (FibrantObject.HoCat.resolution.map
              ((fibrantReplacement (C := SimplicialSpace.{u})).map f) ≫
            (fibrantReplacementResolutionIso Y).inv) =
        (FibrantObject.HoCat.resolution.map f ≫
          (fibrantReplacementResolutionIso Y).hom) ≫
            (fibrantReplacementResolutionIso Y).inv := by
      rw [← Category.assoc, ← hnat]
    _ = FibrantObject.HoCat.resolution.map f := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (fibrantReplacementResolutionIso X).hom ≫
        ((fibrantReplacementResolutionIso X).inv ≫
          FibrantObject.HoCat.resolution.map f) := by
      simp only [Iso.hom_inv_id_assoc]

/-- Every original source map acts by native left composition on derived components. -/
theorem piZero_precomp {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (Z : SimplicialSpace.{u})
    (q : SSet.π₀ (((derivedMappingObject (C := SimplicialSpace.{u})).obj (op Y)).obj Z)) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    piZeroEquiv X Z
        (SSet.mapπ₀ (derivedMappingPrecomp (C := SimplicialSpace.{u}) f Z) q) =
      FibrantObject.HoCat.resolution.map f ≫ piZeroEquiv Y Z q := by
  induction q using SSet.π₀.rec with
  | mk z =>
      let g := (innerHomEquiv
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj Y)
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Z)).symm z
      have hz : derivedZero Y Z g = z :=
        (innerHomEquiv
          ((cofibrantReplacement (C := SimplicialSpace.{u})).obj Y)
          ((fibrantReplacement (C := SimplicialSpace.{u})).obj Z)).apply_symm_apply z
      rw [← hz, derivedMappingPrecomp_piZero_mk, piZeroEquiv_mk, piZeroEquiv_mk]
      rw [FibrantObject.HoCat.resolution.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ FibrantObject.HoCat.resolution.map g ≫
          (fibrantReplacementResolutionIso Z).inv)
        (cofibrantReplacementResolutionIso_naturality f)

/-- Every original target map acts by native right composition on derived components. -/
theorem piZero_postcomp (X : SimplicialSpace.{u}) {Y Z : SimplicialSpace.{u}}
    (g : Y ⟶ Z)
    (q : SSet.π₀ (((derivedMappingObject (C := SimplicialSpace.{u})).obj (op X)).obj Y)) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    piZeroEquiv X Z
        (SSet.mapπ₀ (derivedMappingPostcomp (C := SimplicialSpace.{u}) X g) q) =
      piZeroEquiv X Y q ≫ FibrantObject.HoCat.resolution.map g := by
  induction q using SSet.π₀.rec with
  | mk z =>
      let f := (innerHomEquiv
        ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X)
        ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y)).symm z
      have hz : derivedZero X Y f = z :=
        (innerHomEquiv
          ((cofibrantReplacement (C := SimplicialSpace.{u})).obj X)
          ((fibrantReplacement (C := SimplicialSpace.{u})).obj Y)).apply_symm_apply z
      rw [← hz, derivedMappingPostcomp_piZero_mk, piZeroEquiv_mk, piZeroEquiv_mk]
      rw [FibrantObject.HoCat.resolution.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (cofibrantReplacementResolutionIso X).inv ≫
          FibrantObject.HoCat.resolution.map f ≫ k)
        (fibrantReplacementResolutionIso_naturality g)

/-- The actual fibrant-object homotopy category detects exactly the native Reedy weak class. -/
theorem weakEquivalence_iff_isIso_resolution {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    weakEquivalences SimplicialSpace.{u} f ↔
      IsIso (FibrantObject.HoCat.resolution.map f) := by
  constructor
  · exact resolution_map_isIso_of_weak f
  · intro hf
    let _ : IsIso (FibrantObject.HoCat.resolution.map f) := hf
    let L := toHomotopyCategory SimplicialSpace.{u}
    let T := FibrantObject.HoCat.toLocalization L
    let η := FibrantObject.HoCat.resolutionCompToLocalizationNatTrans L
    let _ : IsIso (η.app X) := by infer_instance
    let _ : IsIso (η.app Y) := by infer_instance
    let _ : IsIso (T.map (FibrantObject.HoCat.resolution.map f)) := by infer_instance
    have hη : L.map f ≫ η.app Y =
        η.app X ≫ T.map (FibrantObject.HoCat.resolution.map f) := by
      simpa only [Functor.comp_map] using η.naturality f
    let _ : IsIso (η.app X ≫ T.map (FibrantObject.HoCat.resolution.map f)) := by
      infer_instance
    let _ : IsIso (L.map f) := IsIso.of_isIso_fac_right hη
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map f).2 inferInstance

/-- The fully constructed, family-independent native Reedy derived mapping calculus. -/
noncomputable def calculusData :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopyFunctionComplexCalculusData (C := SimplicialSpace.{u}) where
  derived_weak_iff_raw := derived_weak_iff_raw
  piZeroEquiv := piZeroEquiv
  piZero_precomp := piZero_precomp
  weakEquivalence_iff_isIso_resolution := weakEquivalence_iff_isIso_resolution

end SimplicialSpace.ReedyModel

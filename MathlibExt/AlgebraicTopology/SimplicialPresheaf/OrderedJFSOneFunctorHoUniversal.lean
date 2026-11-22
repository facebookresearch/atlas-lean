/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorNativeCore
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorOperations
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalScalarQuillen
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanCartesian
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# The original one-fold Cartesian universal function on homotopy categories

The original scalar Quillen adjunction and the actual baseline groupoidal
unit classify all homotopy-category maps out of the full Cartesian source.
The checked new zero/end Iso and the actual first-JT core comparison give
the native core and original Q/R-derived end. The entire Hom functions are
natural, and the full Cartesian transpose has its original strict image.
No Cartesian-model certificate or additional replacement choice is assumed.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The actual original-local homotopy-category functor for the normalized one-fold family. -/
abbrev originalHo := SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}

/-- Tensor the unchanged baseline groupoidal unit with the original source. -/
def parameterUnit (A : Original.{u} 1) (K : SSet.{u}) :
    (scalarTensor.obj A).obj K ⟶ A ⊗ groupoidal.obj K :=
  A ◁ ((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K)

/-- The parameter comparison is weak in the genuine original local model. -/
theorem parameterUnit_weak (A : Original.{u} 1) (K : SSet.{u}) :
    originalLocalEquivalences family.{u} (parameterUnit A K) := by
  let _ : ModelCategory (Original.{u} 1) :=
    SimplicialPresheaf.InjectiveKan.modelCategory.{u} (FinitePowerSite.Source 1)
  let _ : IsClosedSymmetricMonoidalModelCategory (Original.{u} 1) :=
    cartesian_isClosedSymmetricMonoidalModelCategory.{u} (D := FinitePowerSite.Source 1)
  let _ : IsCofibrant A := (data.{u} (FinitePowerSite.Source 1)).all_cofibrant A
  let _ : IsCofibrant ((SimplicialPresheaf.ConstantEvaluation.constant.{u}
    (D := FinitePowerSite.Source 1)).obj K) :=
    (data.{u} (FinitePowerSite.Source 1)).all_cofibrant _
  let _ : IsCofibrant (groupoidal.obj K) := (data.{u} (FinitePowerSite.Source 1)).all_cofibrant _
  let _ : (ihom.adjunction A).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant A
  let p := (BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K
  let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr
    (BaselineConstantCoreComparison.unit_baselineWeak K)
  have hw : weakEquivalences (Original.{u} 1) (parameterUnit A K) :=
    (weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := ihom.adjunction A) p)
  exact weakEquivalences_le_originalLocalEquivalences family.{u} _ hw

private theorem parameterUnit_modelWeak (A : Original.{u} 1) (K : SSet.{u}) :
    SimplicialPresheaf.CoreDerivedAdjunction.localWeakClass family.{u} (parameterUnit A K) := by
  change (originalLocalSmithData family.{u}).model.categoryWithWeakEquivalences.weakEquivalences _
  rw [(originalLocalSmithData family.{u}).weakEquivalences_eq]
  exact parameterUnit_weak A K

private theorem parameterUnit_isIso (A : Original.{u} 1) (K : SSet.{u}) :
    IsIso (originalHo.{u}.map (parameterUnit A K)) :=
  Localization.inverts originalHo.{u} (SimplicialPresheaf.CoreDerivedAdjunction.localWeakClass family.{u}) _
    (parameterUnit_modelWeak A K)

private def scalarHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (originalHo.{u}.obj ((scalarTensor.obj A).obj K) ⟶ originalHo.{u}.obj Z) ≃
      (scalarHo.{u}.obj K ⟶ scalarHo.{u}.obj (innerHom A Z)) := by
  let _ : ModelCategory (Original.{u} 1) := (originalLocalSmithData family.{u}).model
  let _ : IsFibrant Z := ((originalLocalSmithData family.{u}).isFibrant_iff Z).mpr hZ
  let _ : (scalarTensorHomAdjunction A).IsQuillenAdjunction :=
    originalLocalScalarTensorHom_isQuillenAdjunction family.{u} A
  exact QuillenOrdinaryHoHom.homEquiv (scalarTensorHomAdjunction A) K Z

private theorem scalarHomEquiv_map (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : (scalarTensor.obj A).obj K ⟶ Z) :
    scalarHomEquiv A K Z hZ (originalHo.{u}.map f) = scalarHo.{u}.map (scalarTensorHomEquiv A K Z f) := by
  let _ : ModelCategory (Original.{u} 1) := (originalLocalSmithData family.{u}).model
  let _ : IsFibrant Z := ((originalLocalSmithData family.{u}).isFibrant_iff Z).mpr hZ
  let _ : (scalarTensorHomAdjunction A).IsQuillenAdjunction :=
    originalLocalScalarTensorHom_isQuillenAdjunction family.{u} A
  let H := (weakEquivalences (Original.{u} 1)).Q
  let V := (weakEquivalences SSet.{u}).Q
  change QuillenOrdinaryHoHom.homEquiv (scalarTensorHomAdjunction A) K Z (H.map f) =
    V.map (scalarTensorHomEquiv A K Z f)
  exact (QuillenOrdinaryHoHom.homEquiv_map (scalarTensorHomAdjunction A) K Z f).trans
    (congrArg V.map (congrArg (fun e => e K Z f) (scalarTensorHomAdjunction_homEquiv A)))

private theorem originalHo_representative {X Z : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (h : originalHo.{u}.obj X ⟶ originalHo.{u}.obj Z) :
    ∃ f : X ⟶ Z, originalHo.{u}.map f = h := by
  let d := originalLocalSmithData family.{u}
  let _ : ModelCategory (Original.{u} 1) := d.model
  let _ : IsCofibrant X := d.all_cofibrant X
  let _ : IsFibrant Z := (d.isFibrant_iff Z).mpr hZ
  let H := (weakEquivalences (Original.{u} 1)).Q
  let h' : H.obj X ⟶ H.obj Z := h
  exact map_surjective_of_isLocalization H X Z h'

private def scalarNativeIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.{u}.obj (innerHom A Z) ≅ scalarHo.{u}.obj ((nativeCoreFunctor A).obj Z) :=
  (scalarHo.{u}.mapIso ((rawEndNatIso A).app Z)).symm ≪≫ nativeZeroIso A Z hZ

/-- Every Ho map out of the original Cartesian source is classified by the actual native functor core. -/
def tensorNativeHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) ≃
      (scalarHo.{u}.obj K ⟶ scalarHo.{u}.obj ((nativeCoreFunctor A).obj Z)) := by
  let _ : IsIso (originalHo.{u}.map (parameterUnit A K)) := parameterUnit_isIso A K
  exact (Iso.homCongr (asIso (originalHo.{u}.map (parameterUnit A K))).symm (Iso.refl _)).trans
    ((scalarHomEquiv A K Z hZ).trans
      (Iso.homCongr (Iso.refl _) (scalarNativeIso A Z hZ)))

/-- The forward Ho function retains the original parameter unit and original scalar adjunct. -/
theorem tensorNativeHomEquiv_map (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : A ⊗ groupoidal.obj K ⟶ Z) :
    tensorNativeHomEquiv A K Z hZ (originalHo.{u}.map f) =
      scalarHo.{u}.map (scalarTensorHomEquiv A K Z (parameterUnit A K ≫ f)) ≫
        (scalarNativeIso A Z hZ).hom := by
  let _ : IsIso (originalHo.{u}.map (parameterUnit A K)) := parameterUnit_isIso A K
  change (𝟙 (scalarHo.{u}.obj K)) ≫
    scalarHomEquiv A K Z hZ
      (originalHo.{u}.map (parameterUnit A K) ≫ originalHo.{u}.map f ≫ 𝟙 (originalHo.{u}.obj Z)) ≫
        (scalarNativeIso A Z hZ).hom = _
  rw [Category.comp_id, Category.id_comp, ← originalHo.{u}.map_comp,
    scalarHomEquiv_map]

private theorem parameter_curry (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (f : A ⊗ groupoidal.obj K ⟶ Z) :
    ((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
        (op (ConstantEvaluation.zeroTuple 1)) ≫
      (curry f).app (op (ConstantEvaluation.zeroTuple 1)) ≫ (rawEndNatIso A).hom.app Z =
        scalarTensorHomEquiv A K Z (parameterUnit A K ≫ f) := by
  have hc : scalarCurry A K Z (parameterUnit A K ≫ f) =
      (BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K ≫ curry f := by
    change curry (𝟙 _ ≫ (A ◁ _ ≫ f)) = _
    rw [Category.id_comp]
    exact (adjunction A).homEquiv_naturality_left _ f
  have ht : zeroTranspose A K Z (parameterUnit A K ≫ f) =
      zero.map ((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K ≫ curry f) := by
    unfold zeroTranspose
    rw [hc]
    ext n x
    change (zero.map ((BaselineConstantCoreComparison.unit.{u}
      (D := FinitePowerSite.Source 1)).app K ≫ curry f)).app n
        ((scalarConstAdjunction.unit.app K).app n x) = _
    rw [scalarConstAdjunction_unit_app]
    rfl
  have hz :
      (((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
          (op (ConstantEvaluation.zeroTuple 1)) ≫
        (curry f).app (op (ConstantEvaluation.zeroTuple 1))) ≫
          zeroEvaluationIso.hom.app (object A Z) =
        zero.map ((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K ≫ curry f) := rfl
  change (((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
      (op (ConstantEvaluation.zeroTuple 1)) ≫
    (curry f).app (op (ConstantEvaluation.zeroTuple 1)) ≫
      zeroEvaluationIso.hom.app (object A Z)) ≫ (zeroScalarIso A Z).hom = _
  exact (congrArg (fun t => t ≫ (zeroScalarIso A Z).hom) hz).trans
    ((congrArg (fun t => t ≫ (zeroScalarIso A Z).hom) ht.symm).trans
      (zeroScalarIso_characteristic A K Z _))

/-- The entire native Ho universal function agrees with the original full Cartesian transpose. -/
theorem tensorNativeHomEquiv_currying (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : A ⊗ groupoidal.obj K ⟶ Z) :
    tensorNativeHomEquiv A K Z hZ (originalHo.{u}.map f) =
      nativeUniversalHomEquiv A K Z hZ (originalHo.{u}.map (curry f)) := by
  rw [tensorNativeHomEquiv_map, nativeUniversalHomEquiv_map, ← parameter_curry]
  let p := ((BaselineConstantCoreComparison.unit.{u} (D := FinitePowerSite.Source 1)).app K).app
    (op (ConstantEvaluation.zeroTuple 1)) ≫ (curry f).app (op (ConstantEvaluation.zeroTuple 1))
  let e := (rawEndNatIso A).app Z
  change scalarHo.{u}.map (p ≫ e.hom) ≫ (scalarHo.{u}.map e.inv ≫ (nativeZeroIso A Z hZ).hom) =
    scalarHo.{u}.map p ≫ (nativeZeroIso A Z hZ).hom
  have he : scalarHo.{u}.map e.hom ≫ scalarHo.{u}.map e.inv = 𝟙 _ :=
    (scalarHo.{u}.map_comp e.hom e.inv).symm.trans
      ((scalarHo.{u}.congr_map e.hom_inv_id).trans (scalarHo.{u}.map_id _))
  rw [scalarHo.{u}.map_comp, Category.assoc, ← Category.assoc (scalarHo.{u}.map e.hom),
    he, Category.id_comp]

/-- The original Cartesian Ho adjunction on every baseline groupoidal scalar source. -/
def cartesianHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) ≃
      (originalHo.{u}.obj (groupoidal.obj K) ⟶ originalHo.{u}.obj (object A Z)) :=
  (tensorNativeHomEquiv A K Z hZ).trans (nativeUniversalHomEquiv A K Z hZ).symm

/-- The full Cartesian Ho function keeps every original strict representative's transpose. -/
theorem cartesianHomEquiv_map (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : A ⊗ groupoidal.obj K ⟶ Z) :
    cartesianHomEquiv A K Z hZ (originalHo.{u}.map f) = originalHo.{u}.map (curry f) := by
  apply (nativeUniversalHomEquiv A K Z hZ).injective
  change nativeUniversalHomEquiv A K Z hZ
      ((nativeUniversalHomEquiv A K Z hZ).symm (tensorNativeHomEquiv A K Z hZ (originalHo.{u}.map f))) = _
  rw [Equiv.apply_symm_apply, tensorNativeHomEquiv_currying]

/-- This is the same full original Cartesian Ho Hom function with the original Q/R-derived end target. -/
def tensorDerivedHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) ≃
      (scalarHo.{u}.obj K ⟶ scalarHo.{u}.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z)) :=
  (tensorNativeHomEquiv A K Z hZ).trans (nativeHomEquiv A K Z hZ)

/-- The derived full Hom function is the actual native Hom function followed by the original Q/R leg. -/
theorem tensorDerivedHomEquiv_apply (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) :
    tensorDerivedHomEquiv A K Z hZ h =
      tensorNativeHomEquiv A K Z hZ h ≫ (nativeMappingIso A Z hZ).hom := by
  change (𝟙 (scalarHo.{u}.obj K)) ≫ _ ≫ _ = _
  rw [Category.id_comp]

/-- The Cartesian Ho comparison and the original Q/R universal core Hom comparison have the same image. -/
theorem tensorDerivedHomEquiv_triangle (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) :
    homEquiv A K Z hZ (cartesianHomEquiv A K Z hZ h) = tensorDerivedHomEquiv A K Z hZ h := by
  rw [← nativeUniversalHomEquiv_derived]
  change nativeUniversalHomEquiv A K Z hZ
      ((nativeUniversalHomEquiv A K Z hZ).symm (tensorNativeHomEquiv A K Z hZ h)) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  change _ = (𝟙 (scalarHo.{u}.obj K)) ≫ _ ≫ _
  rw [Category.id_comp]

/-- The native full Ho function is natural in the original target and first-JT core map. -/
theorem tensorNativeHomEquiv_target (A : Original.{u} 1) (K : SSet.{u}) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) (g : Z ⟶ V) :
    tensorNativeHomEquiv A K V hV (h ≫ originalHo.{u}.map g) =
      tensorNativeHomEquiv A K Z hZ h ≫ scalarHo.{u}.map ((nativeCoreFunctor A).map g) := by
  obtain ⟨f, rfl⟩ := originalHo_representative hZ h
  rw [← originalHo.{u}.map_comp, tensorNativeHomEquiv_currying, tensorNativeHomEquiv_currying]
  have hc : curry (f ≫ g) = curry f ≫ targetMap A g := (adjunction A).homEquiv_naturality_right f g
  rw [hc, originalHo.{u}.map_comp, nativeUniversalHomEquiv_target]

/-- Every scalar map keeps its actual baseline R action in the full Cartesian Ho function. -/
theorem tensorNativeHomEquiv_scalar (A : Original.{u} 1) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj L) ⟶ originalHo.{u}.obj Z) :
    tensorNativeHomEquiv A K Z hZ (originalHo.{u}.map (A ◁ groupoidal.map k) ≫ h) =
      scalarHo.{u}.map k ≫ tensorNativeHomEquiv A L Z hZ h := by
  obtain ⟨f, rfl⟩ := originalHo_representative hZ h
  rw [← originalHo.{u}.map_comp, tensorNativeHomEquiv_currying, tensorNativeHomEquiv_currying]
  have hc : curry (A ◁ groupoidal.map k ≫ f) = groupoidal.map k ≫ curry f :=
    (adjunction A).homEquiv_naturality_left _ f
  rw [hc, originalHo.{u}.map_comp, nativeUniversalHomEquiv_scalar]

/-- Original source contravariance keeps both the original Cartesian map and native functor-core map. -/
theorem tensorNativeHomEquiv_source {A B : Original.{u} 1} (a : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (B ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) :
    tensorNativeHomEquiv A K Z hZ (originalHo.{u}.map (a ▷ groupoidal.obj K) ≫ h) =
      tensorNativeHomEquiv B K Z hZ h ≫
        scalarHo.{u}.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
          (oneDesignatedEquivalence.functor.map (sourceMap a Z))) := by
  obtain ⟨f, rfl⟩ := originalHo_representative hZ h
  rw [← originalHo.{u}.map_comp, tensorNativeHomEquiv_currying, tensorNativeHomEquiv_currying,
    curry_source, originalHo.{u}.map_comp, nativeUniversalHomEquiv_source]

/-- The full Cartesian Ho transpose is natural in every genuine local target map. -/
theorem cartesianHomEquiv_target (A : Original.{u} 1) (K : SSet.{u}) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) (g : Z ⟶ V) :
    cartesianHomEquiv A K V hV (h ≫ originalHo.{u}.map g) =
      cartesianHomEquiv A K Z hZ h ≫ originalHo.{u}.map (targetMap A g) := by
  apply (nativeUniversalHomEquiv A K V hV).injective
  change nativeUniversalHomEquiv A K V hV
      ((nativeUniversalHomEquiv A K V hV).symm (tensorNativeHomEquiv A K V hV _)) = _
  rw [Equiv.apply_symm_apply, nativeUniversalHomEquiv_target]
  change tensorNativeHomEquiv A K V hV _ =
    nativeUniversalHomEquiv A K Z hZ
      ((nativeUniversalHomEquiv A K Z hZ).symm (tensorNativeHomEquiv A K Z hZ h)) ≫ _
  rw [Equiv.apply_symm_apply, tensorNativeHomEquiv_target]

/-- Scalar-source maps retain the same original groupoidal R action in the entire Ho transpose. -/
theorem cartesianHomEquiv_scalar (A : Original.{u} 1) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj L) ⟶ originalHo.{u}.obj Z) :
    cartesianHomEquiv A K Z hZ (originalHo.{u}.map (A ◁ groupoidal.map k) ≫ h) =
      originalHo.{u}.map (groupoidal.map k) ≫ cartesianHomEquiv A L Z hZ h := by
  apply (nativeUniversalHomEquiv A K Z hZ).injective
  change nativeUniversalHomEquiv A K Z hZ
      ((nativeUniversalHomEquiv A K Z hZ).symm (tensorNativeHomEquiv A K Z hZ _)) = _
  rw [Equiv.apply_symm_apply, nativeUniversalHomEquiv_scalar]
  change tensorNativeHomEquiv A K Z hZ _ = _ ≫
    nativeUniversalHomEquiv A L Z hZ
      ((nativeUniversalHomEquiv A L Z hZ).symm (tensorNativeHomEquiv A L Z hZ h))
  rw [Equiv.apply_symm_apply, tensorNativeHomEquiv_scalar]

/-- The full Cartesian Ho transpose retains the original source contravariance. -/
theorem cartesianHomEquiv_source {A B : Original.{u} 1} (a : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (B ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) :
    cartesianHomEquiv A K Z hZ (originalHo.{u}.map (a ▷ groupoidal.obj K) ≫ h) =
      cartesianHomEquiv B K Z hZ h ≫ originalHo.{u}.map (sourceMap a Z) := by
  apply (nativeUniversalHomEquiv A K Z hZ).injective
  change nativeUniversalHomEquiv A K Z hZ
      ((nativeUniversalHomEquiv A K Z hZ).symm (tensorNativeHomEquiv A K Z hZ _)) = _
  rw [Equiv.apply_symm_apply, nativeUniversalHomEquiv_source]
  change tensorNativeHomEquiv A K Z hZ _ =
    nativeUniversalHomEquiv B K Z hZ
      ((nativeUniversalHomEquiv B K Z hZ).symm (tensorNativeHomEquiv B K Z hZ h)) ≫ _
  rw [Equiv.apply_symm_apply, tensorNativeHomEquiv_source]

/-- Every actual target map acts through the original derived R action on the full Hom function. -/
theorem tensorDerivedHomEquiv_target (A : Original.{u} 1) (K : SSet.{u}) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) (g : Z ⟶ V) :
    tensorDerivedHomEquiv A K V hV (h ≫ originalHo.{u}.map g) =
      tensorDerivedHomEquiv A K Z hZ h ≫ scalarHo.{u}.map (localDerivedPostcomp family.{u} A g) := by
  rw [tensorDerivedHomEquiv_apply, tensorNativeHomEquiv_target,
    tensorDerivedHomEquiv_apply, Category.assoc, nativeMappingIso_target, ← Category.assoc]

/-- The derived Hom function retains every scalar-source map. -/
theorem tensorDerivedHomEquiv_scalar (A : Original.{u} 1) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (A ⊗ groupoidal.obj L) ⟶ originalHo.{u}.obj Z) :
    tensorDerivedHomEquiv A K Z hZ (originalHo.{u}.map (A ◁ groupoidal.map k) ≫ h) =
      scalarHo.{u}.map k ≫ tensorDerivedHomEquiv A L Z hZ h := by
  rw [tensorDerivedHomEquiv_apply, tensorNativeHomEquiv_scalar,
    tensorDerivedHomEquiv_apply, Category.assoc]

/-- Original source maps act through the actual derived Q action on the full Hom function. -/
theorem tensorDerivedHomEquiv_source {A B : Original.{u} 1} (a : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : originalHo.{u}.obj (B ⊗ groupoidal.obj K) ⟶ originalHo.{u}.obj Z) :
    tensorDerivedHomEquiv A K Z hZ (originalHo.{u}.map (a ▷ groupoidal.obj K) ≫ h) =
      tensorDerivedHomEquiv B K Z hZ h ≫ scalarHo.{u}.map (localDerivedPrecomp family.{u} a Z) := by
  rw [tensorDerivedHomEquiv_apply, tensorNativeHomEquiv_source, tensorDerivedHomEquiv_apply,
    Category.assoc, nativeMappingIso_source, ← Category.assoc]

/-- The Cartesian Ho function retains actual pointwise composition of original full functors. -/
theorem cartesianHomEquiv_composition (A B C : Original.{u} 1) (K : SSet.{u})
    (hC : isOriginalLocalFibrant family.{u} C)
    (b : groupoidal.obj K ⟶ object B C ⊗ object A B) :
    cartesianHomEquiv A K C hC
        (originalHo.{u}.map (uncurry (b ≫ OneFunctor.composition A B C))) =
      originalHo.{u}.map (b ≫ OneFunctor.composition A B C) := by
  rw [cartesianHomEquiv_map, curry_uncurry]

/-- Actual original composition has the same original Q/R-derived scalar Hom image. -/
theorem tensorDerivedHomEquiv_composition (A B C : Original.{u} 1) (K : SSet.{u})
    (hC : isOriginalLocalFibrant family.{u} C)
    (b : groupoidal.obj K ⟶ object B C ⊗ object A B) :
    tensorDerivedHomEquiv A K C hC
        (originalHo.{u}.map (uncurry (b ≫ OneFunctor.composition A B C))) =
      homEquiv A K C hC (originalHo.{u}.map (b ≫ OneFunctor.composition A B C)) := by
  rw [← tensorDerivedHomEquiv_triangle, cartesianHomEquiv_composition]

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core

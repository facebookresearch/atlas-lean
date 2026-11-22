/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Data.Fintype.Option
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.HomotopyExtensionClosure
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKMonoidal
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarTestPreservation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableCellularClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CGWHRealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.StableHomotopy.IntegerGroups
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationLifting
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHBasedHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHMonoidAxiom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalOmegaCoproductClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalRawPiHEPPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalRawPiHomotopyPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaDetectionClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialStableModelProperties
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableHEPOrdinalWeakComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionIntegerPiDetection
import MathlibExt.CategoryTheory.Enriched.PointwiseColimitReflection
import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHBasedCW
import MathlibExt.Topology.Category.PointedCGWH.TensorMappingAdjunction

/-!
# Original stable ScalarCWClosure

The complete original sequential, symmetric and orthogonal carriers, maps,
caller cardinal/bottom and all permitted universes are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

private theorem scalarNativeHasCoproduct {I : Type} [CategoryTheory.EnrichedCategory
  PointedCGWH.{u, v} I]
    {J : Type v} (X : J → CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v} I) : HasCoproduct
      X := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let h : HasColimitsOfSize.{v, v} (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v} I) := by
    infer_instance
  let _ : HasColimitsOfShape (Discrete J) (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u, v}
    I) :=
    @HasColimitsOfSize.has_colimits_of_shape (CategoryTheory.EnrichedFunctorCat PointedCGWH.{u,
      v} I) _ h (Discrete J) _
  exact HasColimitsOfShape.has_colimit (Discrete.functor X)

private theorem scalarPointedHasCoproduct {J : Type v} (X : J → PointedCGWH.{u, v}) :
  HasCoproduct X := by
  let h : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let _ : HasColimitsOfShape (Discrete J) PointedCGWH.{u, v} :=
    @HasColimitsOfSize.has_colimits_of_shape PointedCGWH.{u, v} _ h (Discrete J) _
  exact HasColimitsOfShape.has_colimit (Discrete.functor X)

attribute [local instance] scalarNativeHasCoproduct scalarPointedHasCoproduct

private theorem scalarPointedHasBinaryCoproduct (K L : PointedCGWH.{u, v}) : HasBinaryCoproduct K
  L := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let _ : HasColimits PointedCGWH.{u, v} := by infer_instance
  exact HasColimitsOfShape.has_colimit (pair K L)

attribute [local instance] scalarPointedHasBinaryCoproduct

section OriginalScalarCoefficientGeometry01

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalScalarCoefficientGeometry

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The actual coefficient functor keeps the full original enriched spectrum and scalar maps. -/
abbrev coefficientFunctor (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I :=
  WeightedEndVariance.tensorBifunctor.flip.obj X

/-- The whole original scalar coefficient functor preserves the caller's colimits by its
actual full mapping-end adjunction. -/
theorem coefficientFunctor_preservesColimits (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesColimits (coefficientFunctor X) :=
  (EnrichedFunctorMapping.tensorMappingAdjunction X).leftAdjoint_preservesColimits

/-- Every actual based coefficient pushout becomes the same full scalar pushout, retaining
both input legs, both output legs and the caller's chosen spectrum. -/
private theorem scalarTensorMap_isPushout {K L M P : PointedCGWH.{u, v}}
    (i : K ⟶ L) (z : K ⟶ M) (kL : L ⟶ P) (kM : M ⟶ P)
    (sq : IsPushout i z kL kM) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPushout (scalarTensorMap i X) (scalarTensorMap z X)
      (scalarTensorMap kL X) (scalarTensorMap kM X) := by
  let _ : PreservesColimits (coefficientFunctor X) := coefficientFunctor_preservesColimits X
  exact sq.map (coefficientFunctor X)


end PointedCGWH.Spectra.OriginalScalarCoefficientGeometry

end OriginalScalarCoefficientGeometry01

section OriginalSequentialFiniteCoefficientRaw02

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

open OriginalScalarCoefficientGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev C1 := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Wpi := integerPiStarEquivalences.{u, v}

private instance raw_respectsIso : Wpi.{u, v}.RespectsIso := by
  dsimp only [Wpi, integerPiStarEquivalences]
  infer_instance

/-- Scalar preservation retains every signed original integer map on arbitrary original
prespectrum endpoints. This property has no cofibrancy condition on the spectrum arrow. -/
private structure PreservesRaw (K : PointedCGWH.{u, v}) : Prop where
  preserves : ∀ {X Y : C1.{u, v}} (f : X ⟶ Y),
    Wpi f → Wpi ((EnrichedFunctorCat.tensorLeft K).map f)

/-- A coefficient isomorphism transports the literal scalar arrow at both original endpoints. -/
private theorem preservesRaw_of_iso {K L : PointedCGWH.{u, v}} (e : K ≅ L)
    (hK : PreservesRaw K) : PreservesRaw L := by
  constructor
  intro X Y f hf
  let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft K).map f) ≅
      Arrow.mk ((EnrichedFunctorCat.tensorLeft L).map f) :=
    Arrow.isoMk ((coefficientFunctor X).mapIso e) ((coefficientFunctor Y).mapIso e)
      (scalarTensorMap_diagram_naturality e.hom f).symm
  exact (Wpi.arrow_mk_iso_iff a).mp (hK.preserves f hf)

/-- The original unit coefficient acts through the actual full scalar unit isomorphism. -/
private theorem preservesRaw_unit : PreservesRaw (𝟙_ PointedCGWH.{u, v}) := by
  constructor
  intro X Y f hf
  let a : Arrow.mk ((EnrichedFunctorCat.tensorLeft (𝟙_ PointedCGWH.{u, v})).map f) ≅
      Arrow.mk f :=
    Arrow.isoMk (scalarUnitIso X) (scalarUnitIso Y) (scalarUnitIso_naturality f).symm
  exact (Wpi.arrow_mk_iso_iff a).mpr hf

/-- Scalar tensor of the actual initial coefficient is the actual initial spectrum at every
input, so its full original arrow is an isomorphism. -/
private theorem preservesRaw_initial : PreservesRaw (⊥_ PointedCGWH.{u, v}) := by
  constructor
  intro X Y f _
  let _ : PreservesColimits (coefficientFunctor X) := coefficientFunctor_preservesColimits X
  let _ : PreservesColimits (coefficientFunctor Y) := coefficientFunctor_preservesColimits Y
  have hX := initialIsInitial.isInitialObj (G := coefficientFunctor X)
  have hY := initialIsInitial.isInitialObj (G := coefficientFunctor Y)
  let e := hX.uniqueUpToIso hY
  have he : (EnrichedFunctorCat.tensorLeft (⊥_ PointedCGWH.{u, v})).map f = e.hom :=
    hX.hom_ext _ _
  let _ : IsIso ((EnrichedFunctorCat.tensorLeft (⊥_ PointedCGWH.{u, v})).map f) := by
    exact he.symm ▸ e.isIso_hom
  exact (integerPiStarEquivalences_iff _).mpr (fun q => by infer_instance)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual finite coefficient attachment preserves raw signed integer maps. Both original
coefficient pushout squares and all four scalar comparison maps are the caller's literal maps. -/
private theorem preservesRaw_pushout {K L M P : PointedCGWH.{u, v}}
    (i : K ⟶ L) (z : K ⟶ M) (kL : L ⟶ P) (kM : M ⟶ P)
    (sq : IsPushout i z kL kM) (hi : BasedTimeHomotopyExtension.property i)
    (hK : PreservesRaw K) (hL : PreservesRaw L) (hM : PreservesRaw M) :
    PreservesRaw P := by
  constructor
  intro X Y f hf
  exact OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    (B := B)
    (scalarTensorMap i X) (scalarTensorMap z X)
    (scalarTensorMap kL X) (scalarTensorMap kM X)
    (scalarTensorMap i Y) (scalarTensorMap z Y)
    (scalarTensorMap kL Y) (scalarTensorMap kM Y)
    (scalarTensorMap_isPushout i z kL kM sq X)
    (scalarTensorMap_isPushout i z kL kM sq Y)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi X)
      (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi Y)
    ((EnrichedFunctorCat.tensorLeft K).map f)
    ((EnrichedFunctorCat.tensorLeft L).map f)
    ((EnrichedFunctorCat.tensorLeft M).map f)
    ((EnrichedFunctorCat.tensorLeft P).map f)
    (scalarTensorMap_diagram_naturality i f)
    (scalarTensorMap_diagram_naturality z f)
    (scalarTensorMap_diagram_naturality kL f)
    (scalarTensorMap_diagram_naturality kM f)
    (hK.preserves f hf) (hL.preserves f hf) (hM.preserves f hf)

/-- A binary coefficient coproduct is its actual pushout over the based initial object.
Cofibrancy is imposed on the coefficient, with arbitrary original spectrum endpoints. -/
private theorem preservesRaw_binaryCoproduct (K L : PointedCGWH.{u, v}) [IsCofibrant K]
    (hK : PreservesRaw K) (hL : PreservesRaw L) : PreservesRaw (K ⨿ L) := by
  have hi : BasedTimeHomotopyExtension.property (initial.to K) :=
    BasedTimeHomotopyExtension.modelCofibration_mem _
      ((HomotopicalAlgebra.cofibration_iff _).mp inferInstance)
  exact preservesRaw_pushout (B := B) (initial.to K) (initial.to L)
    coprod.inl coprod.inr (IsPushout.of_hasBinaryCoproduct' K L) hi
    preservesRaw_initial hK hL

/-- The original finite caller cofan is transported only through its complete colimit
isomorphism, retaining all based coefficients. -/
private theorem preservesRaw_finiteCopower (K : PointedCGWH.{u, v}) [IsCofibrant K]
    (hK : PreservesRaw K) (J : Type v) [Finite J] :
    PreservesRaw (∐ fun (_ : J) => K) := by
  classical
  refine Finite.induction_empty_option (P := fun J : Type v =>
    PreservesRaw (∐ fun (_ : J) => K)) ?_ ?_ ?_ J
  · intro A D e hA
    exact preservesRaw_of_iso (Sigma.whiskerEquiv e (fun _ => Iso.refl K)) hA
  · let c : Cofan (fun (_ : PEmpty.{v + 1}) => K) :=
      Cofan.mk (⊥_ PointedCGWH.{u, v}) (fun j => j.elim)
    let hc : IsColimit c := Cofan.IsColimit.mk _ (fun s => initial.to s.pt)
      (fun _ j => j.elim) (fun _ _ _ => initialIsInitial.hom_ext _ _)
    exact preservesRaw_of_iso
      ((coproductIsCoproduct (fun (_ : PEmpty.{v + 1}) => K)).coconePointUniqueUpToIso hc).symm
      preservesRaw_initial
  · intro A _ hA
    let c : Cofan (fun (_ : Option A) => K) :=
      Cofan.mk (K ⨿ ∐ fun (_ : A) => K)
        (fun j => match j with
          | none => coprod.inl
          | some a => Sigma.ι (fun (_ : A) => K) a ≫ coprod.inr)
    let hc : IsColimit c := Cofan.IsColimit.mk _
      (fun s => coprod.desc (s.inj none) (Sigma.desc (fun a => s.inj (some a))))
      (by
        intro s j
        cases j with
        | none =>
            change coprod.inl ≫ coprod.desc _ _ = _
            exact coprod.inl_desc _ _
        | some a =>
            change (Sigma.ι (fun (_ : A) => K) a ≫ coprod.inr) ≫
              coprod.desc _ _ = _
            rw [Category.assoc, coprod.inr_desc, Sigma.ι_comp_desc])
      (by
        intro s m hm
        apply coprod.hom_ext
        · have hn := hm none
          change coprod.inl ≫ m = s.inj none at hn
          exact hn.trans (coprod.inl_desc _ _).symm
        · apply Sigma.hom_ext
          intro a
          have ha := hm (some a)
          change (Sigma.ι (fun (_ : A) => K) a ≫ coprod.inr) ≫ m =
            s.inj (some a) at ha
          calc
            _ = (Sigma.ι (fun (_ : A) => K) a ≫ coprod.inr) ≫ m :=
              (Category.assoc _ _ _).symm
            _ = s.inj (some a) := ha
            _ = _ := by rw [coprod.inr_desc, Sigma.ι_comp_desc])
    exact preservesRaw_of_iso
      ((coproductIsCoproduct (fun (_ : Option A) => K)).coconePointUniqueUpToIso hc).symm
      (preservesRaw_binaryCoproduct (B := B) K _ hK hA)


end PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

end OriginalSequentialFiniteCoefficientRaw02

section OriginalAugmentedCoefficientGeometry03

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory SSet.modelCategoryQuillen MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalAugmentedCoefficientGeometry

/-- The original simplicial realization followed by disjoint based augmentation. -/
private def augmentedRealization : SSet.{v} ⥤ PointedCGWH.{u, v} :=
  SSet.toCGWH.{u, v} ⋙ Under.costar CGWH.point.{u, v}

/-- The actual realization and disjoint-basepoint functors preserve all original colimits. -/
private theorem augmentedRealization_preservesColimits :
    PreservesColimits augmentedRealization.{u, v} :=
  (SSet.sSetCGWHAdj.comp (Under.costarAdjForget CGWH.point.{u, v})).leftAdjoint_preservesColimits

attribute [local instance] augmentedRealization_preservesColimits

/-- Every original simplicial monomorphism gives the actual based realization cofibration.
The proof uses the existing whole realization adjunction lifting class and the original costar. -/
private theorem augmentedMap_cofibration {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f] :
    cofibrations PointedCGWH.{u, v} (augmentedRealization.map f) := by
  have hf : cofibrations SSet.{v} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp
      ((SSet.modelCategoryQuillen.cofibration_iff f).mpr inferInstance)
  have hm := (cofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} f hf
  have h := ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp _ hm
  rw [CGWH.modelCategory.cgwhFreeCofibration_rlp_eq, trivialFibrations_llp] at h
  exact (Under.costarAdjForget_isQuillenAdjunction CGWH.point.{u, v}).preservesCofibrations
    (SSet.toCGWH.map f) h

/-- All original augmented simplicial realization coefficients are cofibrant in the original
based CGWH model; no spectrum endpoint is restricted. -/
private theorem augmentedObject_cofibrant (X : SSet.{v}) :
    IsCofibrant (augmentedRealization.{u, v}.obj X) := by
  let _ : Cofibration (augmentedRealization.{u, v}.map (initial.to X)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (augmentedMap_cofibration (initial.to X))
  have hInitial : IsInitial (augmentedRealization.{u, v}.obj (⊥_ SSet.{v})) :=
    initialIsInitial.isInitialObj (G := augmentedRealization.{u, v})
  exact (isCofibrant_iff_of_isInitial (augmentedRealization.map (initial.to X)) hInitial).mpr
    inferInstance

/-- Original simplicial monomorphisms retain genuine based HEP after disjoint augmentation. -/
private theorem augmentedMap_HEP {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f] :
    BasedTimeHomotopyExtension.property (augmentedRealization.{u, v}.map f) :=
  BasedTimeHomotopyExtension.modelCofibration_mem _ (augmentedMap_cofibration f)

/-- The full finite/general realization isomorphism keeps the original augmented coefficient. -/
private def originalFiniteCoefficientIso (X : SSet.{v}) [X.Finite] :
    augmentedRealization.{u, v}.obj X ≅
      (Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite X) :=
  (Under.costar CGWH.point.{u, v}).mapIso (CGWH.finiteRealizationIso X)

/-- The original augmented zero-simplex is the actual based smash unit through the original
finite realization, original point and costar monoidal unit isomorphisms. -/
private def augmentedZeroIsoUnit : augmentedRealization.{u, v}.obj (Δ[0] : SSet.{v}) ≅
    𝟙_ PointedCGWH.{u, v} := by
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} :=
    CGWH.finiteRealizationIso (Δ[0] : SSet.{v}) ≪≫
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  let eP : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
    CGWH.point_isTerminal.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let hF : (Under.costar CGWH.point.{u, v}).CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  exact (Under.costar CGWH.point).mapIso (e₀ ≪≫ eP) ≪≫ hF.εIso.symm

/-- The original selected finite boundary inclusion is retained literally with its full
augmented domain, target, native index-independent label and both coefficient maps. -/
private abbrev originalBoundary (n : ℕ) := NativeK.boundaryMap.{u, v} n

/-- Every literal selected boundary arrow has the original based HEP. -/
private theorem originalBoundary_HEP (n : ℕ) : BasedTimeHomotopyExtension.property
    (OriginalAugmentedCoefficientGeometry.originalBoundary.{u, v} n) :=
  BasedTimeHomotopyExtension.modelCofibration_mem _
    (Orthogonal.OriginalIClosedHomotopyExtension.boundaryMap_modelCofibration
      _ (.map (CGWH.boundary_mem_realizedBoundaryInclusions n)))

/-- The complete caller coproduct of original simplicial coefficients realizes to its actual
based coefficient cofan, using both maps of the genuine preservation isomorphism. -/
private def augmentedCopowerIso (X : SSet.{v}) (J : Type v) :
    augmentedRealization.{u, v}.obj (∐ fun (_ : J) => X) ≅
      ∐ fun (_ : J) => augmentedRealization.{u, v}.obj X :=
  PreservesCoproduct.iso augmentedRealization (fun (_ : J) => X)


end PointedCGWH.Spectra.OriginalAugmentedCoefficientGeometry

end OriginalAugmentedCoefficientGeometry03

section OriginalAugmentedSimplexVertex04

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory SSet.modelCategoryQuillen MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalAugmentedCoefficientGeometry

/-- The literal last vertex of the original standard simplex. -/
private def simplexLastVertex (n : ℕ) : (Δ[0] : SSet.{v}) ⟶ Δ[n] :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))

/-- The original standard-simplex augmentation is the unique map to the original zero-simplex. -/
private def simplexCollapse (n : ℕ) : (Δ[n] : SSet.{v}) ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- The whole original collapse/vertex composite is the literal last-vertex constant map. -/
private theorem simplexCollapse_vertex (n : ℕ) :
    simplexCollapse.{v} n ≫ simplexLastVertex n =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
  SSet.comp_const _ _

/-- The whole original vertex/collapse composite is the original coefficient identity. -/
private theorem simplexVertex_collapse (n : ℕ) :
    simplexLastVertex.{v} n ≫ simplexCollapse n = 𝟙 (Δ[0] : SSet.{v}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The actual original simplex contraction realizes to the complete collapse/vertex
homotopy equivalence, with both original maps and both inverse equations. -/
private def simplexCollapseHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj (Δ[n] : SSet.{v}))
      (SSet.toTop.obj (Δ[0] : SSet.{v})) where
  toFun := (SSet.toTop.map (simplexCollapse n)).hom
  invFun := (SSet.toTop.map (simplexLastVertex n)).hom
  left_inv := by
    let H := SSet.realizeHomotopy (Δ[n] : SSet.{v}) (Δ[n] : SSet.{v})
      (𝟙 _) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)))
      (SSet.stdSimplex.homotopyIdConstLast n)
    refine ⟨ContinuousMap.Homotopy.cast H.symm ?_ ?_⟩
    · rw [← TopCat.hom_comp, ← CategoryTheory.Functor.map_comp, simplexCollapse_vertex]
    · rw [CategoryTheory.Functor.map_id]
      rfl
  right_inv := by
    have he : (SSet.toTop.map (simplexCollapse n)).hom.comp
        (SSet.toTop.map (simplexLastVertex n)).hom = ContinuousMap.id _ := by
      rw [← TopCat.hom_comp, ← CategoryTheory.Functor.map_comp, simplexVertex_collapse,
        CategoryTheory.Functor.map_id]
      rfl
    rw [he]

/-- The same original last vertex realizes to a weak equivalence. -/
private theorem simplexVertex_realizationWeak (n : ℕ) :
    SSet.realizationWeakEquivalences (simplexLastVertex.{v} n) :=
  TopCat.mem_of_eq_invFun (simplexCollapseHomotopyEquiv n) rfl

/-- The same original last vertex, after the actual disjoint augmentation, is an original
based coefficient trivial cofibration. No spectrum arrow or its endpoints enters this proof. -/
private theorem augmentedSimplexVertex_trivialCofibration (n : ℕ) :
    trivialCofibrations PointedCGWH.{u, v}
      (augmentedRealization.map (simplexLastVertex.{v} n)) := by
  let _ : Mono (simplexLastVertex.{v} n) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  have hv : trivialCofibrations SSet.{v} (simplexLastVertex n) :=
    ⟨(HomotopicalAlgebra.cofibration_iff _).mp
        ((SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance),
      simplexVertex_realizationWeak n⟩
  have hm := (trivialCofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v}
    (simplexLastVertex n) hv
  have h := ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp _ hm
  rw [CGWH.modelCategory.cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp] at h
  exact (Under.costarAdjForget_isQuillenAdjunction CGWH.point.{u, v}).preservesTrivialCofibrations
    (SSet.toCGWH.map (simplexLastVertex n)) h

/-- The actual selected finite augmented simplex receives its original last vertex through
only the genuine zero-unit and finite/general realization maps. -/
private def originalFiniteSimplexVertex (n : ℕ) : 𝟙_ PointedCGWH.{u, v} ⟶
    (Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite (Δ[n] : SSet.{v})) :=
  augmentedZeroIsoUnit.inv ≫ augmentedRealization.map (simplexLastVertex n) ≫
    (originalFiniteCoefficientIso (Δ[n] : SSet.{v})).hom

/-- Both original isomorphism legs and the original last-vertex map give the genuine
selected finite coefficient trivial cofibration. -/
private theorem originalFiniteSimplexVertex_trivialCofibration (n : ℕ) :
    trivialCofibrations PointedCGWH.{u, v} (originalFiniteSimplexVertex n) := by
  have h₀ : trivialCofibrations PointedCGWH.{u, v} augmentedZeroIsoUnit.{u, v}.inv :=
    ⟨(HomotopicalAlgebra.cofibration_iff _).mp inferInstance,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance⟩
  have h₁ : trivialCofibrations PointedCGWH.{u, v}
      (originalFiniteCoefficientIso.{u, v} (Δ[n] : SSet.{v})).hom :=
    ⟨(HomotopicalAlgebra.cofibration_iff _).mp inferInstance,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance⟩
  exact (trivialCofibrations PointedCGWH.{u, v}).comp_mem _ _ h₀
    ((trivialCofibrations PointedCGWH.{u, v}).comp_mem _ _
      (augmentedSimplexVertex_trivialCofibration n) h₁)


end PointedCGWH.Spectra.OriginalAugmentedCoefficientGeometry

end OriginalAugmentedSimplexVertex04

section OriginalScalarSimplexRaw05

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty MonoidalCategory
  HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

open OriginalAugmentedCoefficientGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The earned original based-space monoid axiom gives weak right tensor of each actual
coefficient trivial cofibration, for every arbitrary original based-space endpoint. -/
private theorem coefficientTrivial_tensor_weak {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : trivialCofibrations PointedCGWH.{u, v} i) (X : PointedCGWH.{u, v}) :
    weakEquivalences PointedCGWH.{u, v} (i ▷ X) := by
  let P := tensorTrivialCofibrationsRight PointedCGWH.{u, v}
  have h₁ : P ≤ P.coproducts.{v} := P.le_coproducts
  have h₂ : P.coproducts.{v} ≤ P.coproducts.{v}.pushouts :=
    P.coproducts.le_pushouts
  have h₃ : P.coproducts.{v}.pushouts ≤
      transfiniteCompositions.{v} P.coproducts.{v}.pushouts :=
    CategoryTheory.MorphismProperty.le_transfiniteCompositions _
  have h₄ : transfiniteCompositions.{v} P.coproducts.{v}.pushouts ≤
      weakEquivalences PointedCGWH.{u, v} :=
    MonoidAxiom.cellularClosure_le_weakEquivalences
  exact (h₁.trans (h₂.trans (h₃.trans h₄))) _
    (whiskerRight_mem_tensorTrivialCofibrationsRight _ i hi X)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The full native scalar coefficient map is level weak at EVERY original spectrum input.
The only hypothesis is that its actual coefficient arrow is a based trivial cofibration. -/
private theorem scalarTensorMap_trivialCoefficient_levelWeak
    {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : trivialCofibrations PointedCGWH.{u, v} i)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (scalarTensorMap i X) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq,
    EvaluationTransfer.evaluationProperty_iff]
  intro a
  change weakEquivalences PointedCGWH.{u, v} (component (scalarTensorMap i X) a)
  exact (scalarTensorMap_component i X a).symm ▸
    coefficientTrivial_tensor_weak i hi (X.toEnrichedFunctor.obj a)

/-- An actual coefficient trivial cofibration out of the literal scalar unit gives raw
integer preservation at arbitrary original prespectrum endpoints via its real naturality square. -/
private theorem preservesRaw_of_trivialUnitCoefficient {K : PointedCGWH.{u, v}}
    (i : 𝟙_ PointedCGWH.{u, v} ⟶ K)
    (hi : trivialCofibrations PointedCGWH.{u, v} i) : PreservesRaw K := by
  constructor
  intro X Y f hf
  have hu := preservesRaw_unit.preserves f hf
  apply (integerPiStarEquivalences_iff _).mpr
  intro q
  let P := integerStablePiFunctor.{u, v} q
  let u := (EnrichedFunctorCat.tensorLeft (𝟙_ PointedCGWH.{u, v})).map f
  let g := (EnrichedFunctorCat.tensorLeft K).map f
  let a := scalarTensorMap i X
  let b := scalarTensorMap i Y
  have huP : IsIso (P.map u) := (integerPiStarEquivalences_iff _).mp hu q
  have haP : IsIso (P.map a) :=
    integerStablePiLevelWeak_isIso
      q a (scalarTensorMap_trivialCoefficient_levelWeak (B := B) i hi X)
  have hbP : IsIso (P.map b) :=
    integerStablePiLevelWeak_isIso
      q b (scalarTensorMap_trivialCoefficient_levelWeak (B := B) i hi Y)
  have hs : u ≫ b = a ≫ g := scalarTensorMap_diagram_naturality i f
  have hp : P.map u ≫ P.map b = P.map a ≫ P.map g :=
    (P.map_comp _ _).symm.trans ((P.congr_map hs).trans (P.map_comp _ _))
  have hcP : IsIso (P.map u ≫ P.map b) := IsIso.comp_isIso' huP hbP
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (P.map a) (P.map g) haP (hp ▸ hcP)

/-- Every actual original selected augmented finite simplex coefficient preserves all
original signed integer maps on arbitrary original spectrum arrow endpoints. -/
private theorem preservesRaw_originalFiniteSimplex (n : ℕ) :
    PreservesRaw ((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n] : SSet.{v}))) :=
  preservesRaw_of_trivialUnitCoefficient (B := B) (originalFiniteSimplexVertex n)
    (originalFiniteSimplexVertex_trivialCofibration n)

/-- The same original standard simplex under the full augmentation functor has raw
integer preservation through both maps of its genuine finite/general coefficient isomorphism. -/
private theorem preservesRaw_augmentedSimplex (n : ℕ) :
    PreservesRaw (augmentedRealization.{u, v}.obj (Δ[n] : SSet.{v})) :=
  preservesRaw_of_iso (originalFiniteCoefficientIso (Δ[n] : SSet.{v})).symm
    (preservesRaw_originalFiniteSimplex (B := B) n)


end PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

end OriginalScalarSimplexRaw05

section OriginalFiniteRealizationInduction06

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

open OriginalAugmentedCoefficientGeometry

attribute [local instance] augmentedRealization_preservesColimits

/-- The original simplicial skeleton has the dimension bound of its actual cell filtration. -/
private theorem originalSkeleton_hasDimensionLT (X : SSet.{v}) (n : ℕ) :
    SSet.HasDimensionLT (X.skeleton n) n := by
  constructor
  intro d hd
  apply ((X.skeleton n).degenerate_eq_top_iff d).mpr
  apply le_antisymm inf_le_right
  intro x hx
  refine ⟨?_, hx⟩
  rw [X.mem_degenerate_iff_notMem_nonDegenerate]
  intro hNon
  have hlt : d < n := (X.mem_skeleton_obj_iff_of_nonDegenerate ⟨x, hNon⟩ n).mp hx
  exact (not_lt_of_ge hd) hlt

/-- A bounded-dimensional original simplicial set equals its actual final skeleton. -/
private theorem originalSkeleton_eq_top (X : SSet.{v}) (n : ℕ) [X.HasDimensionLT n] :
    X.skeleton n = ⊤ := by
  apply (X.skeleton n).eq_top_iff_contains_nonDegenerate.mpr
  intro d x hx
  exact X.mem_skeleton x (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ n)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every actual finite simplicial coefficient preserves raw signed integer maps. The
induction uses the original full skeletal cell pushout, its literal finite caller cofans and
all boundary/disk attachment maps, with arbitrary original spectrum endpoints throughout. -/
private theorem augmentedFiniteDimension_preservesRaw (n : ℕ) (X : SSet.{v}) [X.Finite]
    [X.HasDimensionLT n] : PreservesRaw (augmentedRealization.{u, v}.obj X) := by
  induction n generalizing X with
  | zero =>
      have hBT : (⊥ : X.Subcomplex) = ⊤ :=
        X.skeleton_zero.symm.trans (originalSkeleton_eq_top X 0)
      let eX : ((⊥ : X.Subcomplex) : SSet.{v}) ≅ X :=
        SSet.Subcomplex.eqToIso hBT ≪≫ SSet.Subcomplex.topIso X
      have hI : IsInitial (augmentedRealization.{u, v}.obj
          ((⊥ : X.Subcomplex) : SSet.{v})) :=
        (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj
          (G := augmentedRealization.{u, v})
      let e : (⊥_ PointedCGWH.{u, v}) ≅ augmentedRealization.obj X :=
        initialIsInitial.uniqueUpToIso hI ≪≫ augmentedRealization.mapIso eX
      exact preservesRaw_of_iso e preservesRaw_initial
  | succ n ih =>
      let i : ((⊥ : X.Subcomplex) : SSet.{v}) ⟶ X := SSet.Subcomplex.ι ⊥
      let J := SSet.relativeCellComplexOfMono.Cell i n
      let eJ : J ↪ X.nonDegenerate n :=
        { toFun := fun c => ⟨c.simplex, c.nonDegenerate⟩
          inj' := by
            intro a b h
            apply SSet.relativeCellComplexOfMono.Cell.ext
            exact congrArg Subtype.val h }
      let _ : Finite J := Finite.of_injective _ eJ.injective
      let _ : SSet.Finite (X.skeleton n) := SSet.finite_of_mono (X.skeleton n).ι
      let _ : SSet.HasDimensionLT (X.skeleton n) n := originalSkeleton_hasDimensionLT X n
      have hSk : PreservesRaw (augmentedRealization.{u, v}.obj (X.skeleton n)) := ih _
      have hStage (d : ℕ) : SSet.skeletonOfMono i d = X.skeleton d := by
        simp only [SSet.skeletonOfMono, i, OrderHom.coe_mk, Subfunctor.range_ι]
        exact le_antisymm (sup_le bot_le le_rfl) le_sup_right
      have hStageRaw : PreservesRaw (augmentedRealization.{u, v}.obj
          (SSet.skeletonOfMono i n)) :=
        preservesRaw_of_iso
          (augmentedRealization.mapIso (SSet.Subcomplex.eqToIso (hStage n))).symm hSk
      let _ : IsCofibrant (augmentedRealization.{u, v}.obj (SSet.boundary n)) :=
        augmentedObject_cofibrant (SSet.boundary n)
      let _ : IsCofibrant (augmentedRealization.{u, v}.obj (Δ[n] : SSet.{v})) :=
        augmentedObject_cofibrant (Δ[n] : SSet.{v})
      have hBoundary : PreservesRaw (augmentedRealization.{u, v}.obj (SSet.boundary n)) :=
        ih (SSet.boundary n)
      have hBoundaryCofan : PreservesRaw (augmentedRealization.{u, v}.obj
          (SSet.relativeCellComplexOfMono.sigmaBoundary i n)) :=
        preservesRaw_of_iso (augmentedCopowerIso (SSet.boundary n) J).symm
          (preservesRaw_finiteCopower (B := B) _ hBoundary J)
      have hDiskCofan : PreservesRaw (augmentedRealization.{u, v}.obj
          (SSet.relativeCellComplexOfMono.sigmaStdSimplex i n)) :=
        preservesRaw_of_iso (augmentedCopowerIso (Δ[n] : SSet.{v}) J).symm
          (preservesRaw_finiteCopower (B := B) _ (preservesRaw_augmentedSimplex (B := B) n) J)
      let _ : Mono (SSet.relativeCellComplexOfMono.l i n) := inferInstance
      have hLastRaw : PreservesRaw (augmentedRealization.{u, v}.obj
          (SSet.skeletonOfMono i (n + 1))) :=
        preservesRaw_pushout (B := B)
          (augmentedRealization.map (SSet.relativeCellComplexOfMono.l i n))
          (augmentedRealization.map (SSet.relativeCellComplexOfMono.t i n))
          (augmentedRealization.map (SSet.relativeCellComplexOfMono.b i n))
          (augmentedRealization.map (SSet.relativeCellComplexOfMono.r i n))
          ((SSet.relativeCellComplexOfMono.isPushout i n).flip.map augmentedRealization)
          (augmentedMap_HEP (SSet.relativeCellComplexOfMono.l i n))
          hBoundaryCofan hDiskCofan hStageRaw
      let eLast : (SSet.skeletonOfMono i (n + 1) : SSet.{v}) ≅ X :=
        SSet.Subcomplex.eqToIso ((hStage (n + 1)).trans (originalSkeleton_eq_top X (n + 1))) ≪≫
          SSet.Subcomplex.topIso X
      exact preservesRaw_of_iso (augmentedRealization.mapIso eLast) hLastRaw

/-- Every actual finite simplicial realization has the finite-stage preservation theorem,
with the dimension cutoff obtained from its real finite nondegenerate cells. -/
private theorem preservesRaw_finiteAugmented (X : SSet.{v}) [X.Finite] :
    PreservesRaw (augmentedRealization.{u, v}.obj X) := by
  obtain ⟨n, hn⟩ := X.hasDimensionLT_of_finite
  let _ : X.HasDimensionLT n := hn
  exact augmentedFiniteDimension_preservesRaw (B := B) n X

/-- Both genuine finite/general maps transfer raw preservation to the actual selected
finite augmented coefficient without replacing its original carrier. -/
private theorem preservesRaw_originalFiniteCoefficient (X : SSet.{v}) [X.Finite] :
    PreservesRaw ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite X)) :=
  preservesRaw_of_iso (originalFiniteCoefficientIso X)
    (preservesRaw_finiteAugmented (B := B) X)

/-- Both original augmented endpoints of every selected realized boundary inclusion preserve
all signed integer maps at arbitrary original spectrum arrow endpoints. -/
private theorem originalBoundary_endpoints_preservesRaw (n : ℕ) :
    PreservesRaw ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite (SSet.boundary n))) ∧
      PreservesRaw ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite (Δ[n] : SSet.{v}))) :=
  ⟨preservesRaw_originalFiniteCoefficient (B := B) (SSet.boundary n),
    preservesRaw_originalFiniteSimplex (B := B) n⟩

/-- The whole original strict boundary family retains its actual augmented domain and target
coefficients, including dimension zero and the caller's exact original inclusion. -/
private theorem originalBoundaryFamily_endpoints_preservesRaw {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i) :
    PreservesRaw K ∧ PreservesRaw L := by
  change (CGWH.realizedBoundaryInclusions.strictMap (Under.costar CGWH.point)) i at hi
  cases hi with
  | map h =>
      obtain ⟨n⟩ := h
      exact originalBoundary_endpoints_preservesRaw (B := B) n


end PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

end OriginalFiniteRealizationInduction06

section OriginalFiniteBasedCWHistory07

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

open OriginalAugmentedCoefficientGeometry

/-- The domain of the original selected based cell, including its disjoint basepoint. -/
private abbrev originalCellSource (n : ℕ) : PointedCGWH.{u, v} :=
  (Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite (SSet.boundary n))

/-- The target of the original selected based cell is the actual augmented finite simplex. -/
private abbrev originalCellTarget (n : ℕ) : PointedCGWH.{u, v} :=
  (Under.costar CGWH.point.{u, v}).obj (SSet.toCGWHOfFinite (Δ[n] : SSet.{v}))

/-- A finite based CW presentation records a finite sequence of actual selected cell
attachments. Every cell uses the ORIGINAL augmented boundary inclusion, with its original
label, attaching map, characteristic map, stage inclusion and complete pushout square.
The first and final coefficient identifications are genuine isomorphisms. No homotopy-group
preservation, cofibrancy or stable-equivalence outcome is a field of this presentation. -/
private structure FiniteBasedCWPresentation (M : PointedCGWH.{u, v}) where
  length : ℕ
  stage : Fin (length + 1) → PointedCGWH.{u, v}
  initialIso : (⊥_ PointedCGWH.{u, v}) ≅ stage 0
  cellDimension : Fin length → ℕ
  attaching : ∀ i : Fin length, originalCellSource (cellDimension i) ⟶ stage i.castSucc
  characteristic : ∀ i : Fin length, originalCellTarget (cellDimension i) ⟶ stage i.succ
  inclusion : ∀ i : Fin length, stage i.castSucc ⟶ stage i.succ
  square : ∀ i : Fin length, IsPushout (OriginalAugmentedCoefficientGeometry.originalBoundary
    (cellDimension i))
    (attaching i) (characteristic i) (inclusion i)
  finalIso : stage (Fin.last length) ≅ M

/-- Finite based CW coefficients have an actual finite original cell history. -/
private def FiniteBasedCW (M : PointedCGWH.{u, v}) : Prop := Nonempty (FiniteBasedCWPresentation M)

/-- Every coefficient in the complete original finite cell history is cofibrant, by genuine
cobase change of each actual original boundary inclusion. -/
private theorem finiteCWPresentation_cofibrant {M : PointedCGWH.{u, v}}
    (p : FiniteBasedCWPresentation M) : IsCofibrant M := by
  have hStage : ∀ (k : ℕ) (hk : k < p.length + 1), IsCofibrant (p.stage ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        change IsCofibrant (p.stage 0)
        let _ : IsIso p.initialIso.hom := p.initialIso.isIso_hom
        have hi : cofibrations PointedCGWH.{u, v} p.initialIso.hom :=
          (cofibrations PointedCGWH.{u, v}).of_isIso _
        let _ : Cofibration p.initialIso.hom := (HomotopicalAlgebra.cofibration_iff _).mpr hi
        exact (isCofibrant_iff_of_isInitial p.initialIso.hom initialIsInitial).mpr inferInstance
    | succ k ih =>
        intro hk
        let i : Fin p.length := ⟨k, by omega⟩
        let _ : IsCofibrant (p.stage i.castSucc) := ih (by omega)
        have hCell : cofibrations PointedCGWH.{u, v}
          (OriginalAugmentedCoefficientGeometry.originalBoundary (p.cellDimension i)) :=
          Orthogonal.OriginalIClosedHomotopyExtension.boundaryMap_modelCofibration
            _ (.map (CGWH.boundary_mem_realizedBoundaryInclusions (p.cellDimension i)))
        have hInc : cofibrations PointedCGWH.{u, v} (p.inclusion i) :=
          CategoryTheory.MorphismProperty.of_isPushout (p.square i).flip hCell
        let _ : Cofibration (p.inclusion i) := (HomotopicalAlgebra.cofibration_iff _).mpr hInc
        exact isCofibrant_of_cofibration (p.inclusion i)
  let _ : IsCofibrant (p.stage (Fin.last p.length)) := hStage p.length (by omega)
  exact isCofibrant_of_cofibration p.finalIso.hom

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Scalar tensor with every actual finite based CW coefficient preserves the original raw
signed integer maps at arbitrary original spectrum arrow endpoints. The complete finite
history is proved stage by stage through its actual original boundary/disk pushouts. -/
private theorem finiteCWPresentation_preservesRaw {M : PointedCGWH.{u, v}}
    (p : FiniteBasedCWPresentation M) : PreservesRaw M := by
  have hStage : ∀ (k : ℕ) (hk : k < p.length + 1), PreservesRaw (p.stage ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact preservesRaw_of_iso p.initialIso preservesRaw_initial
    | succ k ih =>
        intro hk
        let i : Fin p.length := ⟨k, by omega⟩
        have hPrev : PreservesRaw (p.stage i.castSucc) := ih (by omega)
        have hEnds := originalBoundary_endpoints_preservesRaw (B := B) (p.cellDimension i)
        exact preservesRaw_pushout (B := B)
          (OriginalAugmentedCoefficientGeometry.originalBoundary (p.cellDimension i))
          (p.attaching i) (p.characteristic i) (p.inclusion i) (p.square i)
          (originalBoundary_HEP (p.cellDimension i)) hEnds.1 hEnds.2 hPrev
  exact preservesRaw_of_iso p.finalIso (hStage p.length (by omega))

/-- The finite based CW condition supplies raw scalar preservation through its actual
finite cell presentation, with no outcome premise and no condition on either spectrum endpoint. -/
private theorem finiteBasedCW_preservesRaw {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M) :
    PreservesRaw M := by
  obtain ⟨p⟩ := hM
  exact finiteCWPresentation_preservesRaw (B := B) p

omit B in
/-- Cofibrancy of a finite based CW coefficient follows from the actual geometric cell
history, rather than being an added hypothesis of scalar stable preservation. -/
private theorem finiteBasedCW_cofibrant {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M) :
    IsCofibrant M := by
  obtain ⟨p⟩ := hM
  exact finiteCWPresentation_cofibrant p


end PointedCGWH.Spectra.OriginalFiniteCoefficientRaw

end OriginalFiniteBasedCWHistory07

section OriginalNativeFiniteScalarInteger08

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.Spectra.OriginalNativeFiniteScalar

open OriginalFiniteCoefficientRaw OriginalAugmentedCoefficientGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)

/-- The whole actual restriction/scalar natural isomorphism transfers the earned finite
coefficient raw theorem to EVERY original native spectrum arrow, retaining its original j
embedding and all integer functor maps. -/
private theorem nativeScalar_integerMaps (M : PointedCGWH.{u, v}) (hM : PreservesRaw M)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map f)) :
    ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      ((EnrichedFunctorCat.tensorLeft M).map f)) := by
  have hSource : integerPiStarEquivalences ((restriction j).map f) :=
    (integerPiStarEquivalences_iff _).mpr hf
  have hTensor := hM.preserves ((restriction j).map f) hSource
  intro q
  let e := CategoryTheory.Functor.isoWhiskerRight (originalRestrictionScalarNatIso j M)
    (integerStablePiFunctor.{u, v} q)
  have hFirst : IsIso (((restriction j ⋙ EnrichedFunctorCat.tensorLeft M) ⋙
      integerStablePiFunctor.{u, v} q).map f) :=
    (integerPiStarEquivalences_iff _).mp hTensor q
  exact (NatIso.isIso_map_iff e f).mp hFirst

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every finite based CW history gives scalar raw preservation at every original native
index, without a spectrum endpoint cofibrancy, Omega, semistability or basepoint hypothesis. -/
private theorem nativeFiniteCW_integerMaps {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map f)) :
    ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      ((EnrichedFunctorCat.tensorLeft M).map f)) :=
  nativeScalar_integerMaps j M (finiteBasedCW_preservesRaw (B := B) hM) f hf

/-- The original selected finite augmented coefficient, its functor and all original integer
maps are retained on every native spectrum arrow. -/
private theorem nativeFiniteCoefficient_integerMaps (T : SSet.{v}) [T.Finite]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map f)) :
    ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      ((EnrichedFunctorCat.tensorLeft ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite T))).map f)) :=
  nativeScalar_integerMaps j _ (preservesRaw_originalFiniteCoefficient (B := B) T) f hf

/-- Every original selected boundary inclusion has the same actual domain and target scalar
integer tests, keeping its original label, maps and disjoint based augmentation. -/
private theorem nativeBoundaryFamily_integerMaps {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map f)) :
    (∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      ((EnrichedFunctorCat.tensorLeft K).map f))) ∧
      ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
        ((EnrichedFunctorCat.tensorLeft L).map f)) := by
  have hEnds := originalBoundaryFamily_endpoints_preservesRaw (B := B) i hi
  exact ⟨nativeScalar_integerMaps j K hEnds.1 f hf,
    nativeScalar_integerMaps j L hEnds.2 f hf⟩

/-- The actual original symmetric signed integer functors have the finite based CW theorem
on every arbitrary original symmetric arrow. -/
private theorem symmetricFiniteCW_integerMaps {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map
      ((EnrichedFunctorCat.tensorLeft M).map f)) :=
  nativeFiniteCW_integerMaps (B := B) sequentialSymmetricOperatorIndexFunctor hM f hf

/-- The actual original orthogonal signed integer functors have the same finite based CW
scalar theorem, with arbitrary original arrow endpoints and the original index embedding. -/
private theorem orthogonalFiniteCW_integerMaps {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map f)) :
    ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map
      ((EnrichedFunctorCat.tensorLeft M).map f)) :=
  nativeFiniteCW_integerMaps (B := B) sequentialOrthogonalOperatorIndexFunctor hM f hf

/-- Both literal original realized-boundary coefficient functors have their actual symmetric
integer endpoint tests for every arbitrary original input arrow. -/
private theorem symmetricBoundaryFamily_integerMaps {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    (∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map
      ((EnrichedFunctorCat.tensorLeft K).map f))) ∧
      ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map
        ((EnrichedFunctorCat.tensorLeft L).map f)) :=
  nativeBoundaryFamily_integerMaps (B := B) sequentialSymmetricOperatorIndexFunctor i hi f hf

/-- Both literal original realized-boundary coefficient functors have their actual orthogonal
integer endpoint tests, including the original degree-zero boundary and every arbitrary arrow. -/
private theorem orthogonalBoundaryFamily_integerMaps {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map f)) :
    (∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map
      ((EnrichedFunctorCat.tensorLeft K).map f))) ∧
      ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map
        ((EnrichedFunctorCat.tensorLeft L).map f)) :=
  nativeBoundaryFamily_integerMaps (B := B) sequentialOrthogonalOperatorIndexFunctor i hi f hf


end PointedCGWH.Spectra.OriginalNativeFiniteScalar

end OriginalNativeFiniteScalarInteger08

section OriginalNativeScalarOmegaBridge09

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalNativeFiniteScalar

open OriginalFiniteCoefficientRaw

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev C8 := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev Q8 := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε8 := Replacement.cofibrantReplacementCounit (B := B) (A := I)

variable (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)

/-- Both actual native replacement counits remain original raw integer isomorphisms after
an earned finite scalar coefficient. Their original targets remain completely arbitrary. -/
private theorem scalarCounit_integerMaps (M : PointedCGWH.{u, v}) (hM : PreservesRaw M) (X :
  C8.{u, v}) :
    ∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      ((EnrichedFunctorCat.tensorLeft M).map (ε8.app X))) :=
  nativeScalar_integerMaps j M hM (ε8.app X)
    (fun q => NativeStableCofiberIntegerMaps.integerPiFunctor_invertsLevelWeak (j := j) q _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X))

variable (s : NativeStabilizationFamily.{u, v} I L)
  (hDetector : ∀ {X Y : C8.{u, v}} (f : X ⟶ Y),
    (∀ q : ℤ, IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map f)) →
      NativeK.omegaTests (B := B) s f)

include j hDetector in
/-- The closed forward detector is applied to the SAME full original scalar replacement
counit. This uses only raw integer-to-Omega detection, with no converse assumption. -/
private theorem scalarCounit_omegaTests (M : PointedCGWH.{u, v}) (hM : PreservesRaw M) (X :
  C8.{u, v}) :
    NativeK.omegaTests (B := B) s ((EnrichedFunctorCat.tensorLeft M).map (ε8.app X)) :=
  hDetector _ (scalarCounit_integerMaps (B := B) j M hM X)

/-- The complete original Q8/counit naturality square retains both caller endpoints and all
four literal scalar spectrum maps. -/
private theorem scalarQCounit_naturality (M : PointedCGWH.{u, v}) {X Y : C8.{u, v}} (f : X ⟶ Y) :
    (EnrichedFunctorCat.tensorLeft (A := I) M).map ((Q8 (I := I)).map f) ≫
        (EnrichedFunctorCat.tensorLeft (A := I) M).map ((ε8 (I := I)).app Y) =
      (EnrichedFunctorCat.tensorLeft (A := I) M).map ((ε8 (I := I)).app X) ≫
        (EnrichedFunctorCat.tensorLeft (A := I) M).map f := by
  let T := EnrichedFunctorCat.tensorLeft (A := I) M
  exact (T.map_comp _ _).symm.trans ((T.congr_map (ε8.naturality f)).trans (T.map_comp _ _))

include j hDetector in
/-- The actual scalar Q8 arrow and both SAME original counit images transfer Omega tests to
the original arbitrary-endpoint scalar arrow. Cofibrancy is solely a coefficient condition,
and every finite based CW client below derives it from its actual original cell history. -/
private theorem nativeScalar_omegaTests (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (hM : PreservesRaw M) {X Y : C8.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) s f) :
    NativeK.omegaTests (B := B) s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let T := EnrichedFunctorCat.tensorLeft (A := I) M
  let W := NativeK.omegaTests (B := B) s
  have hX := scalarCounit_omegaTests (B := B) j s hDetector M hM X
  have hY := scalarCounit_omegaTests (B := B) j s hDetector M hM Y
  have hQ := NativeK.tensorQMap_omegaTests (B := B) s M f hf
  have hComp : W (T.map (Q8.map f) ≫ T.map (ε8.app Y)) :=
    W.comp_mem _ _ hQ hY
  have hNat := scalarQCounit_naturality (B := B) M f
  exact W.of_precomp (T.map (ε8.app X)) (T.map f) hX (hNat ▸ hComp)

include j hDetector in
/-- The full native scalar finite based CW theorem has no coefficient preservation outcome
as an input: both raw preservation and coefficient cofibrancy are proved from the original
finite cell history before the genuine native Q8/counit transfer. -/
private theorem nativeFiniteCW_omegaTests {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : C8.{u, v}} (f : X ⟶ Y) (hf : NativeK.omegaTests (B := B) s f) :
    NativeK.omegaTests (B := B) s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let _ : IsCofibrant M := finiteBasedCW_cofibrant hM
  exact nativeScalar_omegaTests (B := B) j s hDetector M
    (finiteBasedCW_preservesRaw (B := B) hM) f hf

include j hDetector in
/-- Every actual original boundary inclusion retains both original endpoint scalar functors
and their true arbitrary-spectrum Omega tests, using the SAME original Q8/counit maps. -/
private theorem nativeBoundaryFamily_omegaTests {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : C8.{u, v}} (f : X ⟶ Y) (hf : NativeK.omegaTests (B := B) s f) :
    NativeK.omegaTests (B := B) s ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      NativeK.omegaTests (B := B) s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  have hCof := NativeK.pointedBoundary_endpoints i hi
  let _ : IsCofibrant K := hCof.1
  let _ : IsCofibrant M := hCof.2
  have hRaw := originalBoundaryFamily_endpoints_preservesRaw (B := B) i hi
  exact ⟨nativeScalar_omegaTests (B := B) j s hDetector K hRaw.1 f hf,
    nativeScalar_omegaTests (B := B) j s hDetector M hRaw.2 f hf⟩


end PointedCGWH.Spectra.OriginalNativeFiniteScalar

end OriginalNativeScalarOmegaBridge09

section OriginalFiniteScalarOmegaClients10

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalNativeFiniteScalar

open OriginalFiniteCoefficientRaw OriginalAugmentedCoefficientGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every actual finite based CW coefficient preserves the original symmetric Omega tests
on every arbitrary original spectrum arrow, through its genuine cell history and original
Q/counit square. Only the earned CLOSED forward raw-integer detector is used. -/
private theorem symmetricFiniteCW_omegaTests {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft M).map f) :=
  nativeFiniteCW_omegaTests (B := B) sequentialSymmetricOperatorIndexFunctor Actual.symmetricFamily
    (fun f h => PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests.integerIsos_imply_omegaTests
      (B := B) f h) hM f hf

/-- The same actual finite based CW coefficient preserves original orthogonal Omega tests
at arbitrary endpoints, using the original orthogonal forward detector and both original
scalar replacement counits. -/
private theorem orthogonalFiniteCW_omegaTests {M : PointedCGWH.{u, v}} (hM : FiniteBasedCW M)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft M).map f) :=
  nativeFiniteCW_omegaTests (B := B) sequentialOrthogonalOperatorIndexFunctor
    Actual.orthogonalFamily
    (fun f h =>
      Orthogonal.MMSSStabilization.OriginalFunctionRawIteration.integerIsos_imply_omegaTests
      (B := B) f h) hM f hf

/-- Both original augmented endpoints of EVERY literal selected realized boundary inclusion
preserve the true original symmetric Omega tests at arbitrary spectrum endpoints. -/
theorem symmetricBoundaryFamily_omegaTests {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft M).map
        f) :=
  nativeBoundaryFamily_omegaTests (B := B) sequentialSymmetricOperatorIndexFunctor
    Actual.symmetricFamily
    (fun f h => PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests.integerIsos_imply_omegaTests
      (B := B) f h) i hi f hf

/-- Both original augmented endpoints of EVERY literal selected realized boundary inclusion
preserve the true original orthogonal Omega tests without changing either spectrum endpoint. -/
theorem orthogonalBoundaryFamily_omegaTests {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft M).map
        f) :=
  nativeBoundaryFamily_omegaTests (B := B) sequentialOrthogonalOperatorIndexFunctor
    Actual.orthogonalFamily
    (fun f h =>
      Orthogonal.MMSSStabilization.OriginalFunctionRawIteration.integerIsos_imply_omegaTests
      (B := B) f h) i hi f hf

/-- Every original dimension label, augmented boundary and augmented simplex is retained
in the actual symmetric endpoint tests, including the original empty zero-boundary. -/
private theorem symmetricRealizedBoundary_omegaTests (n : ℕ)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily
      ((EnrichedFunctorCat.tensorLeft (originalCellSource.{u, v} n)).map f) ∧
      NativeK.omegaTests (B := B) Actual.symmetricFamily
        ((EnrichedFunctorCat.tensorLeft (originalCellTarget.{u, v} n)).map f) :=
  symmetricBoundaryFamily_omegaTests (B := B)
    (OriginalAugmentedCoefficientGeometry.originalBoundary n)
    (.map (CGWH.boundary_mem_realizedBoundaryInclusions n)) f hf

/-- Every original realized boundary dimension label and both actual augmented coefficients
have the actual orthogonal Omega tests on arbitrary original spectrum arrows. -/
private theorem orthogonalRealizedBoundary_omegaTests (n : ℕ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily
      ((EnrichedFunctorCat.tensorLeft (originalCellSource.{u, v} n)).map f) ∧
      NativeK.omegaTests (B := B) Actual.orthogonalFamily
        ((EnrichedFunctorCat.tensorLeft (originalCellTarget.{u, v} n)).map f) :=
  orthogonalBoundaryFamily_omegaTests (B := B)
    (OriginalAugmentedCoefficientGeometry.originalBoundary n)
    (.map (CGWH.boundary_mem_realizedBoundaryInclusions n)) f hf

/-- The SAME literal symmetric coefficient boundary map and full scalar arrow naturality
square accompany both original endpoint tests. -/
private theorem symmetricBoundaryFamily_scalar_testSquare {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    (NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft M).map
        f)) ∧
      (EnrichedFunctorCat.tensorLeft K).map f ≫ scalarTensorMap i Y =
        scalarTensorMap i X ≫ (EnrichedFunctorCat.tensorLeft M).map f :=
  ⟨symmetricBoundaryFamily_omegaTests (B := B) i hi f hf,
    scalarTensorMap_diagram_naturality i f⟩

/-- The SAME literal orthogonal augmented boundary map and its whole scalar naturality
square retain both endpoint tests at arbitrary original spectrum arrows. -/
private theorem orthogonalBoundaryFamily_scalar_testSquare {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    (NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft M).map
        f)) ∧
      (EnrichedFunctorCat.tensorLeft K).map f ≫ scalarTensorMap i Y =
        scalarTensorMap i X ≫ (EnrichedFunctorCat.tensorLeft M).map f :=
  ⟨orthogonalBoundaryFamily_omegaTests (B := B) i hi f hf,
    scalarTensorMap_diagram_naturality i f⟩


end PointedCGWH.Spectra.OriginalNativeFiniteScalar

end OriginalFiniteScalarOmegaClients10

section CoefficientCellFrames01

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]


/-- The actual scalar transformation of the whole original spectrum arrow. -/
def coefficientTransformation {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) : OriginalScalarCoefficientGeometry.coefficientFunctor X ⟶
      OriginalScalarCoefficientGeometry.coefficientFunctor Y :=
  WeightedEndVariance.tensorBifunctor.flip.map f

private theorem coefficientTransformation_app
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (K : PointedCGWH.{u, v}) :
    (coefficientTransformation f).app K = (EnrichedFunctorCat.tensorLeft K).map f := rfl

private theorem coefficientFunctor_map
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {K M : PointedCGWH.{u, v}} (i : K ⟶ M) :
    (OriginalScalarCoefficientGeometry.coefficientFunctor X).map i = scalarTensorMap i X := rfl



end PointedCGWH.Spectra.OriginalCoefficientCells

end CoefficientCellFrames01

section CoefficientColimitClosure02

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (s : NativeStabilizationFamily.{u, v} I L)

private abbrev C11 := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Both scalar images of the caller's full coefficient cofan retain the original
comparison arrow and all injections. The summand shape need not be finite. -/
theorem scalarMap_cofan_omegaTests
    [(NativeK.omegaTests s).IsStableUnderCoproducts.{v}]
    {X Y : C11.{u, v}} (f : X ⟶ Y) {J : Type v}
    (K : J → PointedCGWH.{u, v}) (c : Cofan K) (hc : IsColimit c)
    (hf : ∀ j, NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft (K j)).map f)) :
    NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft c.pt).map f) := by
  let P := OriginalScalarCoefficientGeometry.coefficientFunctor X
  let Q := OriginalScalarCoefficientGeometry.coefficientFunctor Y
  let α := coefficientTransformation f
  let _ : PreservesColimits P := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits X
  let _ : PreservesColimits Q := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits Y
  apply MorphismProperty.colimitsOfShape_le (W := NativeK.omegaTests s) (J := Discrete J)
  exact MorphismProperty.colimitsOfShape.mk' _ _ (P.mapCocone c) (Q.mapCocone c)
    (isColimitOfPreserves P hc) (isColimitOfPreserves Q hc)
    (Functor.whiskerLeft (Discrete.functor K) α) (fun j => hf j.as) (α.app c.pt)
    (fun j => α.naturality (c.ι.app j))

/-- Every actual continuous coefficient HEP history transfers its stage scalar
tests to the same original chosen colimit coefficient, at arbitrary spectrum endpoints. -/
theorem scalarMap_ordinal_omegaTests
    {X Y : C11.{u, v}} (f : X ⟶ Y)
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ PointedCGWH.{u, v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → BasedTimeHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c)
    (hf : ∀ j, NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft (F.obj j)).map f)) :
    NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft c.pt).map f) := by
  let P := OriginalScalarCoefficientGeometry.coefficientFunctor X
  let Q := OriginalScalarCoefficientGeometry.coefficientFunctor Y
  let α := coefficientTransformation f
  let _ : PreservesColimits P := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits X
  let _ : PreservesColimits Q := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits Y
  let _ : PreservesColimitsOfSize.{w, w} P :=
    (EnrichedFunctorMapping.tensorMappingAdjunction X).leftAdjoint_preservesColimits
  let _ : PreservesColimitsOfSize.{w, w} Q :=
    (EnrichedFunctorMapping.tensorMappingAdjunction Y).leftAdjoint_preservesColimits
  let _ : PreservesWellOrderContinuousOfShape J P :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  let _ : PreservesWellOrderContinuousOfShape J Q :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  exact StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests s
    (F ⋙ P) (F ⋙ Q) (Functor.whiskerLeft F α)
    (fun j hj => PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem _ (hF j hj) X)
    (fun j hj => PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem _ (hF j hj) Y)
    hf (P.mapCocone c) (Q.mapCocone c)
    (isColimitOfPreserves P hc) (isColimitOfPreserves Q hc)
    (α.app c.pt) (fun j => α.naturality (c.ι.app j))


end PointedCGWH.Spectra.OriginalCoefficientCells

end CoefficientColimitClosure02

section CoefficientRelativeCells03

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C12 := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Arbitrary based coefficient cell families and all limit stages are retained.
The concrete carrier specializations derive both cell tests and pushout gluing below. -/
theorem scalarMap_relativeCells_omegaTests
    (s : NativeStabilizationFamily.{u, v} I L)
    [(NativeK.omegaTests s).IsStableUnderCoproducts.{v}]
    {X Y : C12.{u, v}} (f : X ⟶ Y)
    (hCells : ∀ {A Z : PointedCGWH.{u, v}} (i : A ⟶ Z),
      PointedCGWH.realizedBoundaryInclusions i →
      NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft A).map f) ∧
        NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft Z).map f))
    (hPush : ∀ {A Z K P : PointedCGWH.{u, v}} (i : A ⟶ Z) (a : A ⟶ K)
      (z : Z ⟶ P) (k : K ⟶ P), IsPushout i a z k →
      BasedTimeHomotopyExtension.property i →
      NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft A).map f) →
      NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft Z).map f) →
      NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft K).map f) →
      NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft P).map f))
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    {K M : PointedCGWH.{u, v}} {i : K ⟶ M}
    (c : RelativeCellComplex.{v}
      (fun (_ : J) => PointedCGWH.realizedBoundaryInclusions.homFamily) i)
    (hK : NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft K).map f)) :
    NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let W := NativeK.omegaTests (B := B) s
  let T := cofibrations PointedCGWH.{u, v}
  let P := OriginalScalarCoefficientGeometry.coefficientFunctor X
  let Q := OriginalScalarCoefficientGeometry.coefficientFunctor Y
  let α := coefficientTransformation f
  let _ : PreservesColimits P := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits X
  let _ : PreservesColimits Q := OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits Y
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.nativeColimits
  let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  have hBasic : PointedCGWH.realizedBoundaryInclusions ≤ T := by
    intro A Z i hi
    exact Orthogonal.OriginalIClosedHomotopyExtension.boundaryMap_modelCofibration i hi
  let tr := c.transfiniteCompositionOfShape' (I := T) (fun cell => hBasic _ cell.i.2)
  let _ : T.IsStableUnderCoproducts.{v} := by
    dsimp only [T]
    rw [← trivialFibrations_llp]
    infer_instance
  have hClosure : (MorphismProperty.coproducts.{v} T).pushouts ≤ T :=
    (MorphismProperty.pushouts_monotone (MorphismProperty.coproducts_le T)).trans
      MorphismProperty.pushouts_le
  let th := tr.ofLE hClosure
  let _ : T.IsStableUnderTransfiniteComposition.{w} := by
    dsimp only [T]
    rw [← trivialFibrations_llp]
    infer_instance
  have hAllMaps : ∀ {a b : J} (g : a ⟶ b), T (c.F.map g) := fun g => th.mem_map g
  have hStages : ∀ k, W ((EnrichedFunctorCat.tensorLeft (c.F.obj k)).map f) := by
    intro k
    induction k using SuccOrder.limitRecOn with
    | isMin k hk =>
      obtain rfl := hk.eq_bot
      let e : Arrow.mk (α.app (c.F.obj ⊥)) ≅ Arrow.mk (α.app K) :=
        Arrow.isoMk (P.mapIso c.isoBot) (Q.mapIso c.isoBot)
          (α.naturality c.isoBot.hom)
      exact (W.arrow_mk_iso_iff e).mpr hK
    | succ k hk ih =>
      let a := c.attachCells k hk
      let sources : a.ι → PointedCGWH.{u, v} := fun t => (a.π t).1.left
      let targets : a.ι → PointedCGWH.{u, v} := fun t => (a.π t).1.right
      have hSources : W ((EnrichedFunctorCat.tensorLeft a.cofan₁.pt).map f) :=
        scalarMap_cofan_omegaTests s f sources a.cofan₁ a.isColimit₁
          (fun t => (hCells (a.π t).1.hom (a.π t).2).1)
      have hTargets : W ((EnrichedFunctorCat.tensorLeft a.cofan₂.pt).map f) :=
        scalarMap_cofan_omegaTests s f targets a.cofan₂ a.isColimit₂
          (fun t => (hCells (a.π t).1.hom (a.π t).2).2)
      have hm : MorphismProperty.coproducts.{v} T a.m :=
        MorphismProperty.colimitsOfShape_le_coproducts T a.ι a.m
          (MorphismProperty.colimitsOfShape.mk' (W := T) _ _ a.cofan₁ a.cofan₂
            a.isColimit₁ a.isColimit₂ (Discrete.natTrans (fun t => (a.π t.as).1.hom))
            (fun t => hBasic _ (a.π t.as).2) a.m (fun t => a.hm t.as))
      exact hPush a.m a.g₁ a.g₂ (c.F.map (homOfLE (Order.le_succ k))) a.isPushout.flip
        (BasedTimeHomotopyExtension.modelCofibration_mem a.m
          (MorphismProperty.coproducts_le T a.m hm)) hSources hTargets ih
    | isSuccLimit k hk ih =>
      let _ : OrderBot (Set.Iio k) := { bot := ⟨⊥, hk.bot_lt⟩, bot_le t := bot_le }
      let _ : SuccOrder (Set.Iio k) := SuccOrder.ofLinearWellFoundedLT (Set.Iio k)
      let F := (Set.principalSegIio k).monotone.functor ⋙ c.F
      let _ : F.IsWellOrderContinuous :=
        inferInstanceAs
          (((Set.principalSegIio k : Set.Iio k ≤i J)).monotone.functor ⋙ c.F).IsWellOrderContinuous
      exact scalarMap_ordinal_omegaTests s f F
        (fun t _ => BasedTimeHomotopyExtension.modelCofibration_mem _
          (hAllMaps ((Set.principalSegIio k).monotone.functor.map
            (homOfLE (Order.le_succ t)))))
        ((Set.principalSegIio k).cocone c.F) (c.F.isColimitOfIsWellOrderContinuous k hk)
        (fun t => ih t.1 t.2)
  exact scalarMap_ordinal_omegaTests s f c.F
    (fun k hk => BasedTimeHomotopyExtension.modelCofibration_mem _ (th.map_mem k hk))
    (⟨M, c.incl⟩ : Cocone c.F) c.isColimit hStages


end PointedCGWH.Spectra.OriginalCoefficientCells

end CoefficientRelativeCells03

section ActualCoefficientCells04

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
/-- The actual initial coefficient comparison is an isomorphism at every spectrum arrow. -/
private theorem scalarMap_initial_isIso {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) : IsIso ((EnrichedFunctorCat.tensorLeft (⊥_ PointedCGWH.{u, v})).map f) := by
  let _ : PreservesColimits (OriginalScalarCoefficientGeometry.coefficientFunctor X) :=
    OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits X
  let _ : PreservesColimits (OriginalScalarCoefficientGeometry.coefficientFunctor Y) :=
    OriginalScalarCoefficientGeometry.coefficientFunctor_preservesColimits Y
  exact isIso_of_isInitial (initialIsInitial.isInitialObj (OriginalScalarCoefficientGeometry.coefficientFunctor X))
    (initialIsInitial.isInitialObj (OriginalScalarCoefficientGeometry.coefficientFunctor Y))
    ((coefficientTransformation f).app (⊥_ PointedCGWH.{u, v}))

/-- The original zero coefficient starts every actual based cell history. -/
theorem scalarMap_initial_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    NativeK.omegaTests s ((EnrichedFunctorCat.tensorLeft (⊥_ PointedCGWH.{u, v})).map f) := by
  let _ := scalarMap_initial_isIso f
  exact (NativeK.omegaTests s).of_isIso _

private instance symmetricOmegaCoproducts :
    (NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}).IsStableUnderCoproducts.{v} :=
  { isStableUnderCoproductsOfShape := fun J =>
      MorphismProperty.IsStableUnderCoproductsOfShape.mk _ J
        (fun _ _ _ _ f hf =>
          PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalCoproductMap_omegaTests f
          hf) }

private instance orthogonalOmegaCoproducts :
    (NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}).IsStableUnderCoproducts.{v} :=
  { isStableUnderCoproductsOfShape := fun J =>
      MorphismProperty.IsStableUnderCoproductsOfShape.mk _ J
        (fun _ _ _ _ f hf => Orthogonal.OriginalHEPOmegaClosure.originalCoproductMap_omegaTests f
          hf) }

private theorem symmetricScalarPushout
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    {A Z K P : PointedCGWH.{u, v}} (i : A ⟶ Z) (a : A ⟶ K)
    (z : Z ⟶ P) (k : K ⟶ P) (sq : IsPushout i a z k)
    (hi : BasedTimeHomotopyExtension.property i)
    (hA : NativeK.omegaTests Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft A).map f))
    (hZ : NativeK.omegaTests Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft Z).map f))
    (hK : NativeK.omegaTests Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft K).map f)) :
    NativeK.omegaTests Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft P).map f) :=
  PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
    (scalarTensorMap i X) (scalarTensorMap a X) (scalarTensorMap z X) (scalarTensorMap k X)
    (scalarTensorMap i Y) (scalarTensorMap a Y) (scalarTensorMap z Y) (scalarTensorMap k Y)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq X)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq Y)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi X)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi Y)
    ((EnrichedFunctorCat.tensorLeft A).map f) ((EnrichedFunctorCat.tensorLeft Z).map f)
    ((EnrichedFunctorCat.tensorLeft K).map f) ((EnrichedFunctorCat.tensorLeft P).map f)
    (scalarTensorMap_diagram_naturality i f) (scalarTensorMap_diagram_naturality a f)
    (scalarTensorMap_diagram_naturality z f) (scalarTensorMap_diagram_naturality k f) hA hZ hK

private theorem orthogonalScalarPushout
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    {A Z K P : PointedCGWH.{u, v}} (i : A ⟶ Z) (a : A ⟶ K)
    (z : Z ⟶ P) (k : K ⟶ P) (sq : IsPushout i a z k)
    (hi : BasedTimeHomotopyExtension.property i)
    (hA : NativeK.omegaTests Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft A).map f))
    (hZ : NativeK.omegaTests Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft Z).map f))
    (hK : NativeK.omegaTests Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft K).map f)) :
    NativeK.omegaTests Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft P).map f) :=
  Orthogonal.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
    (scalarTensorMap i X) (scalarTensorMap a X) (scalarTensorMap z X) (scalarTensorMap k X)
    (scalarTensorMap i Y) (scalarTensorMap a Y) (scalarTensorMap z Y) (scalarTensorMap k Y)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq X)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq Y)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi X)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi Y)
    ((EnrichedFunctorCat.tensorLeft A).map f) ((EnrichedFunctorCat.tensorLeft Z).map f)
    ((EnrichedFunctorCat.tensorLeft K).map f) ((EnrichedFunctorCat.tensorLeft P).map f)
    (scalarTensorMap_diagram_naturality i f) (scalarTensorMap_diagram_naturality a f)
    (scalarTensorMap_diagram_naturality z f) (scalarTensorMap_diagram_naturality k f) hA hZ hK

/-- Every genuine possibly nonfinite based CW history has the actual symmetric
scalar theorem, with arbitrary cell multiplicities and all original ordinal maps. -/
theorem symmetricScalarCellHistory_omegaTests
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] {M : PointedCGWH.{u, v}}
    (c : RelativeCellComplex.{v}
      (fun (_ : J) => PointedCGWH.realizedBoundaryInclusions.homFamily) (initial.to M))
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft M).map f) :=
  scalarMap_relativeCells_omegaTests Actual.symmetricFamily f
    (fun i hi => OriginalNativeFiniteScalar.symmetricBoundaryFamily_omegaTests i hi f hf)
    (symmetricScalarPushout f) c (scalarMap_initial_omegaTests Actual.symmetricFamily f)

/-- The same unrestricted scalar statement holds on every actual nonfinite
orthogonal coefficient cell history, retaining the original CW cell labels and maps. -/
theorem orthogonalScalarCellHistory_omegaTests
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] {M : PointedCGWH.{u, v}}
    (c : RelativeCellComplex.{v}
      (fun (_ : J) => PointedCGWH.realizedBoundaryInclusions.homFamily) (initial.to M))
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft M).map f) :=
  scalarMap_relativeCells_omegaTests Actual.orthogonalFamily f
    (fun i hi => OriginalNativeFiniteScalar.orthogonalBoundaryFamily_omegaTests i hi f hf)
    (orthogonalScalarPushout f) c (scalarMap_initial_omegaTests Actual.orthogonalFamily f)


end PointedCGWH.Spectra.OriginalCoefficientCells

end ActualCoefficientCells04

section CofibrantCoefficientFrames05

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]





private abbrev coefficientBoundaryFamily := PointedCGWH.realizedBoundaryInclusions.{u, v}
private abbrev κ14 := realizedGeneratorCardinal.{v}

private instance pointedBoundarySOA : coefficientBoundaryFamily.{u,
  v}.IsCardinalForSmallObjectArgument κ14 :=
  by
    have hB : B = instOrderBotToTypeOrdRealizedGeneratorCardinal.{v} := Subsingleton.elim _ _
    cases hB
    exact PointedCGWH.cofibrantGenerationData.I_smallObject

/-- The same realized-cardinal boundary factor of the actual coefficient zero inclusion. -/
private def coefficientCellObject (M : PointedCGWH.{u, v}) : PointedCGWH.{u, v} :=
  SmallObject.obj coefficientBoundaryFamily κ14 (initial.to M)

/-- The full original cellular source arrow retains all ordinal stages and characteristic maps. -/
private def coefficientCellComplex (M : PointedCGWH.{u, v}) :
    RelativeCellComplex.{v} (fun (_ : κ14.ord.ToType) => coefficientBoundaryFamily.homFamily)
      (SmallObject.ιObj coefficientBoundaryFamily κ14 (initial.to M)) :=
  SmallObject.relativeCellComplexιObj coefficientBoundaryFamily κ14 (initial.to M)

/-- The actual model lifting square constructs both original coefficient splitting maps. -/
private def coefficientCellRetract (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Retract M (coefficientCellObject M) := by
  let i := SmallObject.ιObj coefficientBoundaryFamily κ14 (initial.to M)
  let p := SmallObject.πObj coefficientBoundaryFamily κ14 (initial.to M)
  have hR : coefficientBoundaryFamily.rlp = trivialFibrations PointedCGWH.{u, v} := by
    have hB : B = instOrderBotToTypeOrdRealizedGeneratorCardinal.{v} := Subsingleton.elim _ _
    cases hB
    exact PointedCGWH.cofibrantGenerationData.I_rlp
  have hp : trivialFibrations PointedCGWH.{u, v} p :=
    hR ▸ SmallObject.rlp_πObj coefficientBoundaryFamily κ14 (initial.to M)
  let _ : Fibration p := (HomotopicalAlgebra.fibration_iff _).mpr hp.1
  let _ : WeakEquivalence p := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hp.2
  let _ : HasLiftingProperty (initial.to M) p := inferInstance
  let sq : CommSq i (initial.to M) p (𝟙 M) :=
    ⟨(SmallObject.ιObj_πObj coefficientBoundaryFamily κ14 (initial.to M)).trans (Category.comp_id
      _).symm⟩
  exact { i := sq.lift, r := p, retract := sq.fac_right }


end PointedCGWH.Spectra.OriginalCoefficientCells

end CofibrantCoefficientFrames05

section CofibrantCoefficientClosure06

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
/-- Both original coefficient splitting maps induce the full scalar comparison Arrow retract. -/
def coefficientScalarArrowRetract
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    {K M : PointedCGWH.{u, v}} (r : Retract K M) :
    RetractArrow ((EnrichedFunctorCat.tensorLeft K).map f)
      ((EnrichedFunctorCat.tensorLeft M).map f) where
  i := Arrow.homMk ((OriginalScalarCoefficientGeometry.coefficientFunctor X).map r.i)
    ((OriginalScalarCoefficientGeometry.coefficientFunctor Y).map r.i)
    ((coefficientTransformation f).naturality r.i)
  r := Arrow.homMk ((OriginalScalarCoefficientGeometry.coefficientFunctor X).map r.r)
    ((OriginalScalarCoefficientGeometry.coefficientFunctor Y).map r.r)
    ((coefficientTransformation f).naturality r.r)
  retract := by
    apply Arrow.hom_ext
    · change (OriginalScalarCoefficientGeometry.coefficientFunctor X).map r.i ≫
      (OriginalScalarCoefficientGeometry.coefficientFunctor X).map r.r = 𝟙 _
      rw [← (OriginalScalarCoefficientGeometry.coefficientFunctor X).map_comp, r.retract,
        (OriginalScalarCoefficientGeometry.coefficientFunctor X).map_id]
    · change (OriginalScalarCoefficientGeometry.coefficientFunctor Y).map r.i ≫
      (OriginalScalarCoefficientGeometry.coefficientFunctor Y).map r.r = 𝟙 _
      rw [← (OriginalScalarCoefficientGeometry.coefficientFunctor Y).map_comp, r.retract,
        (OriginalScalarCoefficientGeometry.coefficientFunctor Y).map_id]

/-- Every cofibrant pointed coefficient has the full unrestricted symmetric scalar
private theorem through its original same-cardinal cell source and whole coefficient retract. -/
theorem symmetricCofibrantScalar_omegaTests
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily ((EnrichedFunctorCat.tensorLeft M).map f)
      := by
  let Z := coefficientCellObject (B := B) M
  let j := SmallObject.ιObj PointedCGWH.realizedBoundaryInclusions
    realizedGeneratorCardinal.{v} (initial.to M)
  have hj : j = initial.to Z := initialIsInitial.hom_ext _ _
  have c := coefficientCellComplex (B := B) M
  change RelativeCellComplex.{v}
    (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
      PointedCGWH.realizedBoundaryInclusions.homFamily) j at c
  rw [hj] at c
  have hZ := symmetricScalarCellHistory_omegaTests (B := B) c f hf
  exact MorphismProperty.of_retract
    (coefficientScalarArrowRetract f (coefficientCellRetract (B := B) M)) hZ

/-- The same actual cardinal source, every coefficient cell map and both retract
equations give the unrestricted orthogonal theorem, with arbitrary spectrum endpoints. -/
theorem orthogonalCofibrantScalar_omegaTests
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily ((EnrichedFunctorCat.tensorLeft M).map f)
      := by
  let Z := coefficientCellObject (B := B) M
  let j := SmallObject.ιObj PointedCGWH.realizedBoundaryInclusions
    realizedGeneratorCardinal.{v} (initial.to M)
  have hj : j = initial.to Z := initialIsInitial.hom_ext _ _
  have c := coefficientCellComplex (B := B) M
  change RelativeCellComplex.{v}
    (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
      PointedCGWH.realizedBoundaryInclusions.homFamily) j at c
  rw [hj] at c
  have hZ := orthogonalScalarCellHistory_omegaTests (B := B) c f hf
  exact MorphismProperty.of_retract
    (coefficientScalarArrowRetract f (coefficientCellRetract (B := B) M)) hZ


end PointedCGWH.Spectra.OriginalCoefficientCells

end CofibrantCoefficientClosure06

section SequentialCoefficientClosure09

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C16 := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev W16 := NativeK.omegaTests (B := B) Sequential.originalFamily.{u, v}

private instance sequentialOmegaCoproducts : W16.{u, v}.IsStableUnderCoproducts.{v} :=
  PointedCGWH.Spectra.OriginalCoefficientCells.Sequential.originalOmegaCoproducts

/-- Both endpoints of every literal realized coefficient boundary preserve the
original sequential weak class at arbitrary original spectrum endpoints. -/
private theorem sequentialBoundaryFamily_omegaTests {K M : PointedCGWH.{u, v}}
    (i : K ⟶ M) (hi : PointedCGWH.realizedBoundaryInclusions i)
    {X Y : C16.{u, v}} (f : X ⟶ Y) (hf : W16 f) :
    W16 ((EnrichedFunctorCat.tensorLeft K).map f) ∧
      W16 ((EnrichedFunctorCat.tensorLeft M).map f) := by
  have hW : W16.{u, v} =
      integerPiStarEquivalences :=
    PointedCGWH.Spectra.OriginalCoefficientCells.Sequential.omegaTests_eq_integerPiStar (B := B)
  rw [hW] at hf ⊢
  have hRaw := OriginalFiniteCoefficientRaw.originalBoundaryFamily_endpoints_preservesRaw (B :=
    B) i hi
  exact ⟨hRaw.1.preserves f hf, hRaw.2.preserves f hf⟩

private theorem sequentialScalarPushout
    {X Y : C16.{u, v}} (f : X ⟶ Y)
    {A Z K P : PointedCGWH.{u, v}} (i : A ⟶ Z) (a : A ⟶ K)
    (z : Z ⟶ P) (k : K ⟶ P) (sq : IsPushout i a z k)
    (hi : BasedTimeHomotopyExtension.property i)
    (hA : W16 ((EnrichedFunctorCat.tensorLeft A).map f))
    (hZ : W16 ((EnrichedFunctorCat.tensorLeft Z).map f))
    (hK : W16 ((EnrichedFunctorCat.tensorLeft K).map f)) :
    W16 ((EnrichedFunctorCat.tensorLeft P).map f) :=
  PointedCGWH.Spectra.OriginalCoefficientCells.Sequential.originalHEPPushoutComparison_omegaTests
    (scalarTensorMap i X) (scalarTensorMap a X) (scalarTensorMap z X) (scalarTensorMap k X)
    (scalarTensorMap i Y) (scalarTensorMap a Y) (scalarTensorMap z Y) (scalarTensorMap k Y)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq X)
    (OriginalScalarCoefficientGeometry.scalarTensorMap_isPushout i a z k sq Y)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi X)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i hi Y)
    ((EnrichedFunctorCat.tensorLeft A).map f) ((EnrichedFunctorCat.tensorLeft Z).map f)
    ((EnrichedFunctorCat.tensorLeft K).map f) ((EnrichedFunctorCat.tensorLeft P).map f)
    (scalarTensorMap_diagram_naturality i f) (scalarTensorMap_diagram_naturality a f)
    (scalarTensorMap_diagram_naturality z f) (scalarTensorMap_diagram_naturality k f) hA hZ hK

/-- Every actual possibly nonfinite coefficient cell history retains the scalar
weak theorem on the original sequential carrier and every signed homotopy degree. -/
theorem sequentialScalarCellHistory_omegaTests
    {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] {M : PointedCGWH.{u, v}}
    (c : RelativeCellComplex.{v}
      (fun (_ : J) => PointedCGWH.realizedBoundaryInclusions.homFamily) (initial.to M))
    {X Y : C16.{u, v}} (f : X ⟶ Y) (hf : W16 f) :
    W16 ((EnrichedFunctorCat.tensorLeft M).map f) :=
  scalarMap_relativeCells_omegaTests Sequential.originalFamily f
    (fun i hi => sequentialBoundaryFamily_omegaTests i hi f hf)
    (sequentialScalarPushout f) c (scalarMap_initial_omegaTests Sequential.originalFamily f)

/-- Every cofibrant based coefficient has the original sequential scalar weak theorem
on arbitrary original spectrum endpoints, through the same-cardinal coefficient retract. -/
theorem sequentialCofibrantScalar_omegaTests
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : C16.{u, v}} (f : X ⟶ Y) (hf : W16 f) :
    W16 ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let Z := coefficientCellObject (B := B) M
  let j := SmallObject.ιObj PointedCGWH.realizedBoundaryInclusions
    realizedGeneratorCardinal.{v} (initial.to M)
  have hj : j = initial.to Z := initialIsInitial.hom_ext _ _
  have c := coefficientCellComplex (B := B) M
  change RelativeCellComplex.{v}
    (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
      PointedCGWH.realizedBoundaryInclusions.homFamily) j at c
  rw [hj] at c
  have hZ := sequentialScalarCellHistory_omegaTests (B := B) c f hf
  exact MorphismProperty.of_retract
    (coefficientScalarArrowRetract f (coefficientCellRetract (B := B) M)) hZ


end PointedCGWH.Spectra.OriginalCoefficientCells

end SequentialCoefficientClosure09



section AllNativeScalarWeakClasses11

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every cofibrant coefficient preserves every weak arrow of the actual original
sequential stable model, without a cofibrancy condition on either spectrum endpoint. -/
theorem sequentialCofibrantScalar_weak (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      StableModelConstruction.sequentialModelCategory (B := B)
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f →
      weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    StableModelConstruction.sequentialModelCategory (B := B)
  change weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f →
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.sequential_five_classes (B := B)).1] at hf ⊢
  exact sequentialCofibrantScalar_omegaTests (B := B) M f hf

/-- The same actual scalar arrow is weak in the original symmetric stable model. -/
theorem symmetricCofibrantScalar_weak (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} :=
      StableModelConstruction.symmetricModelCategory (B := B)
    weakEquivalences Actual.SymmetricCarrier.{u, v} f →
      weakEquivalences Actual.SymmetricCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory Actual.SymmetricCarrier.{u, v} :=
    StableModelConstruction.symmetricModelCategory (B := B)
  change weakEquivalences Actual.SymmetricCarrier.{u, v} f →
    weakEquivalences Actual.SymmetricCarrier.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.symmetric_five_classes (B := B)).1] at hf ⊢
  exact symmetricCofibrantScalar_omegaTests (B := B) M f hf

/-- The full orthogonal model uses the same arbitrary coefficient scalar map and weak class. -/
theorem orthogonalCofibrantScalar_weak (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
      StableModelConstruction.orthogonalModelCategory (B := B)
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f →
      weakEquivalences Actual.OrthogonalCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
    StableModelConstruction.orthogonalModelCategory (B := B)
  change weakEquivalences Actual.OrthogonalCarrier.{u, v} f →
    weakEquivalences Actual.OrthogonalCarrier.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.orthogonal_five_classes (B := B)).1] at hf ⊢
  exact orthogonalCofibrantScalar_omegaTests (B := B) M f hf

section CoefficientHistory

variable {J : Type w} [Small.{v} J] [LinearOrder J] [OrderBot J]
  [SuccOrder J] [WellFoundedLT J] {M : PointedCGWH.{u, v}}
  (c : RelativeCellComplex.{v}
    (fun (_ : J) => PointedCGWH.realizedBoundaryInclusions.homFamily) (initial.to M))

include c

/-- All original nonfinite coefficient cell maps act on the same sequential stable model. -/
theorem sequentialScalarCellHistory_weak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      StableModelConstruction.sequentialModelCategory (B := B)
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f →
      weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    StableModelConstruction.sequentialModelCategory (B := B)
  change weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f →
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.sequential_five_classes (B := B)).1] at hf ⊢
  exact sequentialScalarCellHistory_omegaTests (B := B) c f hf

/-- Every original arbitrary-dimensional symmetric coefficient cell history is retained. -/
theorem symmetricScalarCellHistory_weak
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} :=
      StableModelConstruction.symmetricModelCategory (B := B)
    weakEquivalences Actual.SymmetricCarrier.{u, v} f →
      weakEquivalences Actual.SymmetricCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory Actual.SymmetricCarrier.{u, v} :=
    StableModelConstruction.symmetricModelCategory (B := B)
  change weakEquivalences Actual.SymmetricCarrier.{u, v} f →
    weakEquivalences Actual.SymmetricCarrier.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.symmetric_five_classes (B := B)).1] at hf ⊢
  exact symmetricScalarCellHistory_omegaTests (B := B) c f hf

/-- The full orthogonal statement keeps the same caller ordinal and original coefficient. -/
theorem orthogonalScalarCellHistory_weak
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
      StableModelConstruction.orthogonalModelCategory (B := B)
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f →
      weakEquivalences Actual.OrthogonalCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
    StableModelConstruction.orthogonalModelCategory (B := B)
  change weakEquivalences Actual.OrthogonalCarrier.{u, v} f →
    weakEquivalences Actual.OrthogonalCarrier.{u, v} ((tensorLeft M).map f)
  intro hf
  rw [(StableModelConstruction.orthogonal_five_classes (B := B)).1] at hf ⊢
  exact orthogonalScalarCellHistory_omegaTests (B := B) c f hf

end CoefficientHistory


end PointedCGWH.Spectra.OriginalCoefficientCells

end AllNativeScalarWeakClasses11



section AllClassicalBasedCWScalar13

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.OriginalCoefficientCells

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (M : PointedCGWH.{u, v}) [T2Space (CGWH.cgwhToTop.obj M.right)]
  [Topology.CWComplex (Set.univ : Set (CGWH.cgwhToTop.obj M.right))]
  (j : Topology.CWComplex.cell (Set.univ : Set (CGWH.cgwhToTop.obj M.right)) 0)
  (hj : ∀ x : CGWH.point.{u, v}, M.hom x = Topology.CWComplex.map (C := Set.univ) 0 j ![])

include j hj

/-- Every classical based CW coefficient, with any number and dimension of cells,
preserves the original sequential Omega tests on arbitrary spectrum arrows. -/
theorem sequentialClassicalBasedCW_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Sequential.originalFamily f) :
    NativeK.omegaTests (B := B) Sequential.originalFamily ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact sequentialCofibrantScalar_omegaTests (B := B) M f hf

/-- The same nonfinite classical based CW condition preserves all original
symmetric Omega tests, retaining the actual coefficient and both spectrum endpoints. -/
theorem symmetricClassicalBasedCW_omegaTests
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.symmetricFamily f) :
    NativeK.omegaTests (B := B) Actual.symmetricFamily ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact symmetricCofibrantScalar_omegaTests (B := B) M f hf

/-- Every original nonfinite classical based CW coefficient has the actual
orthogonal Omega theorem, without a cofibrancy premise on either spectrum endpoint. -/
theorem orthogonalClassicalBasedCW_omegaTests
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : NativeK.omegaTests (B := B) Actual.orthogonalFamily f) :
    NativeK.omegaTests (B := B) Actual.orthogonalFamily ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact orthogonalCofibrantScalar_omegaTests (B := B) M f hf

/-- The complete original sequential stable model has the classical based CW
scalar theorem at every arbitrary original spectrum arrow. -/
theorem sequentialClassicalBasedCW_weak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      StableModelConstruction.sequentialModelCategory (B := B)
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f →
      weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact sequentialCofibrantScalar_weak (B := B) M f

/-- The full original symmetric weak class is preserved by every based CW scalar. -/
theorem symmetricClassicalBasedCW_weak
    {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} :=
      StableModelConstruction.symmetricModelCategory (B := B)
    weakEquivalences Actual.SymmetricCarrier.{u, v} f →
      weakEquivalences Actual.SymmetricCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact symmetricCofibrantScalar_weak (B := B) M f

/-- The canonical orthogonal model keeps the same original based CW scalar map. -/
theorem orthogonalClassicalBasedCW_weak
    {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
      StableModelConstruction.orthogonalModelCategory (B := B)
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f →
      weakEquivalences Actual.OrthogonalCarrier.{u, v} ((tensorLeft M).map f) := by
  let _ : IsCofibrant M := PointedCGWH.ClassicalCW.classicalBasedCW_isCofibrant M j hj
  exact orthogonalCofibrantScalar_weak (B := B) M f


end PointedCGWH.Spectra.OriginalCoefficientCells

end AllClassicalBasedCWScalar13

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeModel
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OmegaUnit

/-!
# Omega targets retain their original Omega structure after the native telescope

The coefficients of a native stabilization family are genuinely cofibrant.
Internal Hom from each original coefficient preserves level weak maps between
the native fibrant targets. The complete original adjoint square consequently
makes the Omega condition invariant under level weak equivalences.

The actual stage-zero telescope unit is level weak at an Omega input. Its
same original target therefore remains Omega. No Omega property is imposed
on the telescope of an arbitrary input.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalOmegaTargetPreservation

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The carrier is the same original complete native enriched functor category. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Both original Omega conditions are preserved by every original level weak map. -/
theorem isOmega_iff_of_levelWeak (s : NativeStabilizationFamily.{u, v} I L)
    {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) f) :
    NativeK.IsOmega s X ↔ NativeK.IsOmega s Y := by
  have hEval : ∀ a : I, weakEquivalences PointedCGWH.{u, v} (component f a) := by
    rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hf
    exact (EvaluationTransfer.evaluationProperty_iff
      (fun a : I => evaluation (V := PointedCGWH.{u, v}) a)
      (weakEquivalences PointedCGWH.{u, v}) f).mp hf
  have hInternal (l : L) : weakEquivalences PointedCGWH.{u, v}
      ((ihom (s.coefficient l)).map (component f (s.target l))) := by
    let _ : IsCofibrant (s.coefficient l) := s.coefficient_cofibrant l
    let A := X.toEnrichedFunctor.obj (s.target l)
    let D := Y.toEnrichedFunctor.obj (s.target l)
    let _ : IsFibrant A := (PointedCGWH.isFibrant_iff A).mpr
      (CGWH.modelCategory.allObjectsFibrant A.right)
    let _ : IsFibrant D := (PointedCGWH.isFibrant_iff D).mpr
      (CGWH.modelCategory.allObjectsFibrant D.right)
    let _ : WeakEquivalence (component f (s.target l)) :=
      (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hEval (s.target l))
    let _ : (ihom.adjunction (s.coefficient l)).IsQuillenAdjunction :=
      ihomAdjunction_isQuillenAdjunction_of_isCofibrant (s.coefficient l)
    exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
      (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
        (adj := ihom.adjunction (s.coefficient l)) (component f (s.target l)))
  constructor
  · intro hX l
    have hw := (weakEquivalences PointedCGWH.{u, v}).comp_mem
      (NativeK.adjoint s l X) ((ihom (s.coefficient l)).map (component f (s.target l)))
      (hX l) (hInternal l)
    rw [← CurrentFree.adjoint_naturality
      (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) f] at hw
    exact (weakEquivalences PointedCGWH.{u, v}).of_precomp
      (component f (s.source l)) (NativeK.adjoint s l Y) (hEval (s.source l)) hw
  · intro hY l
    have hw := (weakEquivalences PointedCGWH.{u, v}).comp_mem
      (component f (s.source l)) (NativeK.adjoint s l Y) (hEval (s.source l)) (hY l)
    rw [CurrentFree.adjoint_naturality
      (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) f] at hw
    exact (weakEquivalences PointedCGWH.{u, v}).of_postcomp
      (NativeK.adjoint s l X) ((ihom (s.coefficient l)).map (component f (s.target l)))
      (hInternal l) hw

/-- The original weak target unit retains the full original Omega condition on its telescope. -/
theorem telescope_isOmega (s : NativeStabilizationFamily.{u, v} I L)
    {F : Carrier (I := I) ⥤ Carrier (I := I)} (η : 𝟭 (Carrier (I := I)) ⟶ F)
    (hF : ∀ {A D : Carrier (I := I)} (f : A ⟶ D),
      weakEquivalences (Carrier (I := I)) f → weakEquivalences (Carrier (I := I)) (F.map f))
    (E : Carrier (I := I)) (hE : NativeK.IsOmega s E)
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    NativeK.IsOmega s ((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj E) :=
  (isOmega_iff_of_levelWeak s ((EnrichedCoaugmentationTelescope.unit η).app E)
    (EnrichedCoaugmentationTelescope.unit_mem_weak_of_preserves η hF E hηE)).mp hE

end PointedCGWH.Spectra.OriginalOmegaTargetPreservation

namespace PointedCGWH.Spectra.OriginalOmegaTargetPreservation

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.FunctionSpectrum
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- At every actual original orthogonal Omega input its original telescope remains Omega. -/
theorem orthogonalTelescope_isOmega (E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E) :
    NativeK.IsOmega orthogonalFamily (OmegaUnit.telescopeFunctor.obj E) :=
  telescope_isOmega orthogonalFamily Delooping.delta
    (fun {A D} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := A) (Y := D) f hf)
    E hE (Delooping.delta_weak E hE)

end PointedCGWH.Spectra.OriginalOmegaTargetPreservation

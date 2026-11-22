/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKAdjointCorner
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FiberArrowEvaluation
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen

/-!
# One-sphere recognition from the original chosen K-right fiber

Every original index object is the source of an actual stabilization label
whose coefficient is isomorphic to the native one-sphere. If the chosen
fiber collapse of a K-right arrow passes the original Omega-target tests,
the arrow is a level trivial fibration at every index object.

The coefficient isomorphism transports the entire internal-Hom arrow. The
original normalized pullback corner then supplies weakness of the source
component, including the full path-component condition. This is the
fiber criterion in the proof of MMSS Corollary 9.8, with the original
native freely pointed realized-generator K family retained.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original test-null chosen fiber makes every component a level
trivial fibration, using actual one-sphere labels covering the full index. -/
theorem chosenFiber_omegaTests_levelTrivialFibration
    (oneStep : I → L) (source_oneStep : ∀ a, s.source (oneStep a) = a)
    (coefficientIso : ∀ a, s.coefficient (oneStep a) ≅ PointedCGWH.sphereOne.{u, v})
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y)
    (hp : (generators s).rlp p)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hTests : omegaTests s c.snd) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) p ∧
      ∀ a : I, trivialFibrations PointedCGWH.{u, v} (component p a) := by
  have hFiber := chosenFiber_right_local_omega s p hp c hc
  let Z : EnrichedFunctorCat PointedCGWH.{u, v} I := zeroDiagram
  let _ : IsIso (toZero Z) := zeroDiagram_isZero.isIso zeroDiagram_isZero (toZero Z)
  have hZeroOmega : IsOmega s Z := (lifting_toZero_iff_isOmega s Z).mp
    (MorphismProperty.rlp_of_isIso _ _)
  have hCollapse : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) c.snd :=
    (omegaTests_iff_levelWeak_of_isOmega s c.snd hFiber.2.2 hZeroOmega).mp hTests
  have hCollapseEval : ∀ a : I,
      weakEquivalences PointedCGWH.{u, v} ((evaluation a).map c.snd) := by
    rw [Native.weakEquivalences_eq] at hCollapse
    exact (EvaluationTransfer.evaluationProperty_iff _ _ c.snd).mp hCollapse
  have hLevel := ((lifting_iff s p).mp hp).1
  have hLevelEval : ∀ a : I,
      fibrations PointedCGWH.{u, v} ((evaluation a).map p) := by
    rw [Native.fibrations_eq] at hLevel
    exact (EvaluationTransfer.evaluationProperty_iff _ _ p).mp hLevel
  have hComponents (a : I) : trivialFibrations PointedCGWH.{u, v} (component p a) := by
    let l := oneStep a
    let q := (ihom (s.coefficient l)).map (component p (s.target l))
    let _ : Fibration ((evaluation (s.target l)).map p) :=
      (HomotopicalAlgebra.fibration_iff _).mpr (hLevelEval (s.target l))
    have hOneWeak : weakEquivalences PointedCGWH.{u, v}
        ((ihom PointedCGWH.sphereOne).map (component p (s.target l))) :=
      FiberGeometry.chosenFiber_component_ihomSphereOne_weak
        (s.target l) p c hc (hCollapseEval (s.target l))
    let e : ihom (s.coefficient l) ≅ ihom PointedCGWH.sphereOne :=
      (MonoidalClosed.internalHom (C := PointedCGWH.{u, v})).mapIso (coefficientIso a).symm.op
    have hqWeak : weakEquivalences PointedCGWH.{u, v} q :=
      ((weakEquivalences PointedCGWH.{u, v}).arrow_mk_iso_iff
        (CategoryTheory.Arrow.isoMk (e.app (X.toEnrichedFunctor.obj (s.target l)))
          (e.app (Y.toEnrichedFunctor.obj (s.target l)))
          (e.hom.naturality (component p (s.target l))).symm)).mpr hOneWeak
    let _ : IsCofibrant (s.coefficient l) := s.coefficient_cofibrant l
    let _ : (ihom.adjunction (s.coefficient l)).IsQuillenAdjunction :=
      ihomAdjunction_isQuillenAdjunction_of_isCofibrant (s.coefficient l)
    have hqFibration : fibrations PointedCGWH.{u, v} q :=
      Adjunction.IsQuillenAdjunction.preservesFibrations
        (adj := ihom.adjunction (s.coefficient l))
        (component p (s.target l)) (hLevelEval (s.target l))
    let _ : Fibration q := (HomotopicalAlgebra.fibration_iff _).mpr hqFibration
    let _ : WeakEquivalence q := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hqWeak
    let aX := adjoint s l X
    let aY := adjoint s l Y
    have hSquare : component p (s.source l) ≫ aY = aX ≫ q :=
      CurrentFree.adjoint_naturality
        (s.source l) (s.target l) (s.coefficient l) (s.inclusion l) p
    let φ := pullback.lift aX (component p (s.source l)) hSquare.symm
    have hφ : weakEquivalences PointedCGWH.{u, v} φ :=
      adjointPullbackCorner_weak s p hp l
    have hProjection : weakEquivalences PointedCGWH.{u, v} (pullback.snd q aY) :=
      mem_weakEquivalences _
    have hComp := (weakEquivalences PointedCGWH.{u, v}).comp_mem φ
      (pullback.snd q aY) hφ hProjection
    have hFactor : φ ≫ pullback.snd q aY = component p (s.source l) :=
      pullback.lift_snd aX (component p (s.source l)) hSquare.symm
    rw [hFactor] at hComp
    have hWeak : weakEquivalences PointedCGWH.{u, v} (component p a) := by
      change weakEquivalences PointedCGWH.{u, v}
        (component p (s.source (oneStep a))) at hComp
      rw [source_oneStep a] at hComp
      exact hComp
    exact ⟨hLevelEval a, hWeak⟩
  refine ⟨?_, hComponents⟩
  rw [Native.trivialFibrations_eq]
  exact (EvaluationTransfer.evaluationProperty_iff
    (fun a : I => evaluation a) (trivialFibrations PointedCGWH.{u, v}) p).mpr hComponents

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

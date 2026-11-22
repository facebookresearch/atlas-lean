/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NegativeHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalSuspensionPreservation

/-!
# Original symmetric suspension tests

The actual first-free-zero-sphere delooping retains the full original
symmetric Omega family. Its level-weak comparison to the native scalar
loop supplies the negative Hom equivalence. Source naturality of that
equivalence proves that the original I suspension of the same Q arrow
preserves and reflects the original Omega-target tests.

The weak class consists of those Hom tests throughout. No converse from
symmetric stable equivalences to naive integer homotopy is used.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.SuspensionTestDetection

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open NativeOmegaRecovery.NativeSymmetricDelooping

private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev C := SymmetricCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := J.{u, v})

/-- The original suspended Q arrow has exactly the original symmetric Omega tests. -/
theorem suspensionQ_omegaTests_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    NativeK.omegaTests symmetricFamily (S.map (Q.map f)) ↔
      NativeK.omegaTests symmetricFamily f := by
  constructor
  · intro hS E hE
    let D := firstDelooping.obj E
    let eY := negativeHomEquiv (B := B) Y E hE
    let eX := negativeHomEquiv (B := B) X E hE
    let l : (H.obj (S.obj (Q.obj Y)) ⟶ H.obj D) →
        (H.obj (S.obj (Q.obj X)) ⟶ H.obj D) :=
      fun g => H.map (S.map (Q.map f)) ≫ g
    have hl : Function.Bijective l := hS D (firstDelooping_isOmega E hE)
    let e : (H.obj Y ⟶ H.obj E) ≃ (H.obj X ⟶ H.obj E) :=
      eY.symm.trans ((Equiv.ofBijective l hl).trans eX)
    have he : (fun g : H.obj Y ⟶ H.obj E => e g) = (fun g => H.map f ≫ g) := by
      funext g
      change eX (l (eY.symm g)) = H.map f ≫ g
      have h := negativeHomEquiv_naturality_left (B := B) f E hE (eY.symm g)
      change eX (l (eY.symm g)) = H.map f ≫ eY (eY.symm g) at h
      exact h.trans (congrArg (fun a => H.map f ≫ a) (eY.apply_symm_apply g))
    exact he ▸ e.bijective
  · intro hf
    exact NativeK.originalISuspensionQMap_omegaTests (B := B) symmetricFamily f hf

end PointedCGWH.Spectra.Symmetric.SuspensionTestDetection

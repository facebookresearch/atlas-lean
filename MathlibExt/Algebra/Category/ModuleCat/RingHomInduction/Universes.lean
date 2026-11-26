/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Module.ULift
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Adjunction

/-!
# ULift comparisons for induced modules

ULift module equivalences induce isomorphisms between induction of a lifted input and the lift of
its induced carrier. Their pure-tensor formulas give the comparison in the joint scalar and module
universe.
-/

@[expose] public section

open CategoryTheory

universe u v w t

namespace ModuleCat.RingHomInduction

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)
variable (M : Type w) [AddCommGroup M] [Module k M]

/-- Induction of the lifted module lowers by the ULift equivalence. -/
def liftedInputEquiv : Carrier φ (ULift.{t} M) ≃ₗ[R] Carrier φ M := by
  let e : ULift.{t} M ≃ₗ[k] M := ULift.moduleEquiv
  refine LinearEquiv.ofLinearMap (map φ e.toLinearMap) (map φ e.symm.toLinearMap) ?_ ?_
  · apply hom_ext φ M
    intro r m
    simp only [LinearMap.comp_apply, map_tensor]
    change tensor φ M r (e (e.symm m)) = tensor φ M r m
    exact congrArg (tensor φ M r) (e.apply_symm_apply m)
  · apply hom_ext φ (ULift.{t} M)
    intro r m
    simp only [LinearMap.comp_apply, map_tensor]
    change tensor φ (ULift.{t} M) r (e.symm (e m)) = tensor φ (ULift.{t} M) r m
    exact congrArg (tensor φ (ULift.{t} M) r) (e.symm_apply_apply m)

theorem liftedInputEquiv_tensor (r : R) (m : ULift.{t} M) :
    liftedInputEquiv φ M (tensor φ (ULift.{t} M) r m) = tensor φ M r m.down := by
  change map φ (ULift.moduleEquiv : ULift.{t} M ≃ₗ[k] M).toLinearMap
    (tensor φ (ULift.{t} M) r m) = _
  rw [map_tensor]
  rfl

theorem liftedInputEquiv_symm_tensor (r : R) (m : M) :
    (liftedInputEquiv φ M).symm (tensor φ M r m) =
      tensor φ (ULift.{t} M) r (ULift.up m) := by
  change map φ (ULift.moduleEquiv : ULift.{t} M ≃ₗ[k] M).symm.toLinearMap
    (tensor φ M r m) = _
  rw [map_tensor]
  rfl

/-- Input and output are both transported into the constructed joint maximum universe. -/
def jointCarrierEquiv :
    Carrier φ (ULift.{max u v} M) ≃ₗ[R] ULift.{max u v} (Carrier φ M) :=
  let e : Carrier φ (ULift.{max u v} M) ≃ₗ[R] Carrier φ M := liftedInputEquiv φ M
  e.trans (ULift.moduleEquiv : ULift.{max u v} (Carrier φ M) ≃ₗ[R] Carrier φ M).symm

theorem jointCarrierEquiv_tensor (r : R) (m : M) :
    jointCarrierEquiv φ M (tensor φ (ULift.{max u v} M) r (ULift.up m)) =
      ULift.up (tensor φ M r m) := by
  change ULift.up (liftedInputEquiv φ M
    (tensor φ (ULift.{max u v} M) r (ULift.up m))) = _
  rw [liftedInputEquiv_tensor]

/-- ULift includes the induced carrier in the common adjunction universe. -/
def originalInductionLiftIso (M : ModuleCat.{w} k) :
    (ModuleCat.induceScalars.{u, v, w} φ).obj (ModuleCat.of k (ULift.{max u v} M)) ≅
      ModuleCat.of R (ULift.{max u v} (Carrier φ M)) :=
  (jointCarrierEquiv φ M).toModuleIso

theorem originalInductionLiftIso_hom_tensor (M : ModuleCat.{w} k) (r : R) (m : M) :
    (originalInductionLiftIso φ M).hom
        (tensor φ (ULift.{max u v} M) r (ULift.up m)) = ULift.up (tensor φ M r m) :=
  jointCarrierEquiv_tensor φ M r m

theorem originalInductionLiftIso_inv_tensor (M : ModuleCat.{w} k) (r : R) (m : M) :
    (originalInductionLiftIso φ M).inv (ULift.up (tensor φ M r m)) =
      tensor φ (ULift.{max u v} M) r (ULift.up m) := by
  change (jointCarrierEquiv φ M).symm (ULift.up (tensor φ M r m)) = _
  change (liftedInputEquiv φ M).symm (tensor φ M r m) = _
  exact liftedInputEquiv_symm_tensor φ M r m

end ModuleCat.RingHomInduction

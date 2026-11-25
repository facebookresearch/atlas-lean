/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoStableExtension
public import MathlibExt.KTheory.Ring.K2.StableSteinbergLift
public import MathlibExt.KTheory.Ring.K2.Basic
public import MathlibExt.KTheory.Ring.K2.KernelBridge
public import MathlibExt.KTheory.Milnor.ClassicalDegree

/-!
# The reverse map from algebraic K2 to Milnor K2

For a field, the stable Steinberg group lifts to the stable Matsumoto central
extension compatibly with its elementary-group projection. Restricting this
lift to K2 gives a coefficient homomorphism to Milnor K-theory in degree two,
presented in multiplicative and additive forms with their conversion and
central-image equations.
-/

@[expose] public section

open MatsumotoStableExtensionDiagram
open AlgebraicKTheory

universe u

noncomputable section

namespace AlgebraicKTheory.K2

variable (F : Type u) [Field F]

/-- Canonical stable lift from `StableSteinberg F` to the stable
Matsumoto extension, obtained from `StableSteinberg.liftToCentralExtension`
applied to `stableMatsumotoExtension` and its centrality. -/
noncomputable def matsumotoStableLift :
    StableSteinberg F →* StableExtensionGroup F :=
  StableSteinberg.liftToCentralExtension
    (stableMatsumotoExtension (F := F))
    (stableMatsumotoExtension_isCentral (F := F))

/-- Projection square for the Matsumoto stable lift:
the stable projection after the lift recovers `toStableE`. -/
theorem stableProjection_comp_matsumotoStableLift :
    (stableProjection (F := F)).hom.comp (matsumotoStableLift (F := F)) =
      StableSteinberg.toStableE := by
  have h :=
    StableSteinberg.rightHom_comp_liftToCentralExtension
      (S := stableMatsumotoExtension (F := F))
      (hS := stableMatsumotoExtension_isCentral (F := F))
  have h_eq :
      (stableMatsumotoExtension (F := F)).rightHom =
        (stableProjection (F := F)).hom :=
    rfl
  rw [h_eq] at h
  exact h

/-- Composite from `K₂ F` through `K₂.inclusion` to the stable extension. -/
noncomputable def matsumotoK2Lift : K2 F →* StableExtensionGroup F :=
  (matsumotoStableLift (F := F)).comp (K2.inclusion.app (RingCat.of F)).hom

theorem matsumotoK2Lift_apply (x : K2 F) :
    matsumotoK2Lift (F := F) x =
      matsumotoStableLift (F := F)
        (K2.inclusion.app (RingCat.of F) x) :=
  rfl

/-- Every value of the composite lands in the central range.
Uses the projection square, `K₂`-kernel vanishing, and
`stableProjection_ker_eq_central_range`. -/
theorem matsumotoStableLift_inclusion_mem_range (x : K2 F) :
    matsumotoK2Lift (F := F) x ∈ (stableCentralHom (F := F)).range := by
  have h_proj :
      (stableProjection (F := F)).hom (matsumotoK2Lift (F := F) x) = 1 := by
    have h_comp := stableProjection_comp_matsumotoStableLift (F := F)
    have h_eq :
        (stableProjection (F := F)).hom
            (matsumotoStableLift (F := F)
              (K2.inclusion.app (RingCat.of F) x)) =
          StableSteinberg.toStableE (K2.inclusion.app (RingCat.of F) x) :=
      DFunLike.congr_fun h_comp (K2.inclusion.app (RingCat.of F) x)
    have h_to : StableSteinberg.toStableE
        (K2.inclusion.app (RingCat.of F) x) = 1 :=
      K2.toStableE_inclusion_apply (R := F) x
    calc (stableProjection (F := F)).hom (matsumotoK2Lift (F := F) x)
        = (stableProjection (F := F)).hom
            (matsumotoStableLift (F := F)
              (K2.inclusion.app (RingCat.of F) x)) := rfl
      _ = StableSteinberg.toStableE
            (K2.inclusion.app (RingCat.of F) x) := h_eq
      _ = 1 := h_to
  have h_mem_ker :
      matsumotoK2Lift (F := F) x ∈ (stableProjection (F := F)).hom.ker := by
    rw [MonoidHom.mem_ker]
    exact h_proj
  rw [stableProjection_ker_eq_central_range (F := F)] at h_mem_ker
  exact h_mem_ker

/-- Bundled homomorphism from `K₂ F` into the central range,
obtained via `MonoidHom.codRestrict`. -/
noncomputable def matsumotoRangeHom :
    K2 F →* (stableCentralHom (F := F)).range :=
  (matsumotoK2Lift (F := F)).codRestrict
    (stableCentralHom (F := F)).range
    (matsumotoStableLift_inclusion_mem_range (F := F))

theorem matsumotoRangeHom_coe (x : K2 F) :
    (matsumotoRangeHom (F := F) x : StableExtensionGroup F) =
      matsumotoK2Lift (F := F) x :=
  rfl

/-- Multiplicative reverse comparison `K₂ F →* Multiplicative (MilnorK F 2)`,
obtained by composing the range lift with the inverse of
`MonoidHom.ofInjective (stableCentralHom_injective ...)`. -/
noncomputable def matsumotoReverseMul :
    K2 F →* Multiplicative (MilnorK F 2) :=
  ((MonoidHom.ofInjective (stableCentralHom_injective (F := F))).symm.toMonoidHom).comp
    (matsumotoRangeHom (F := F))

/-- Key characterization: `stableCentralHom` after the multiplicative reverse
recovers the stable lift of the `K₂` inclusion. -/
theorem stableCentralHom_matsumotoReverseMul (x : K2 F) :
    stableCentralHom (F := F) (matsumotoReverseMul (F := F) x) =
      matsumotoStableLift (F := F)
        (K2.inclusion.app (RingCat.of F) x) := by
  have h_range :
      (matsumotoRangeHom (F := F) x : StableExtensionGroup F) =
        matsumotoK2Lift (F := F) x :=
    rfl
  have h_ofInjective :
      stableCentralHom (F := F)
          ((MonoidHom.ofInjective (stableCentralHom_injective (F := F))).symm
            (matsumotoRangeHom (F := F) x)) =
        (matsumotoRangeHom (F := F) x : StableExtensionGroup F) :=
    MonoidHom.apply_ofInjective_symm
      (stableCentralHom_injective (F := F))
      (matsumotoRangeHom (F := F) x)
  calc stableCentralHom (F := F) (matsumotoReverseMul (F := F) x)
      = stableCentralHom (F := F)
          ((MonoidHom.ofInjective (stableCentralHom_injective (F := F))).symm
            (matsumotoRangeHom (F := F) x)) := rfl
    _ = (matsumotoRangeHom (F := F) x : StableExtensionGroup F) :=
        h_ofInjective
    _ = matsumotoK2Lift (F := F) x := h_range
    _ = matsumotoStableLift (F := F)
          (K2.inclusion.app (RingCat.of F) x) := rfl

theorem stableCentralHom_matsumotoReverseMul_bundled :
    (stableCentralHom (F := F)).comp (matsumotoReverseMul (F := F)) =
      matsumotoK2Lift (F := F) := by
  ext x
  exact stableCentralHom_matsumotoReverseMul (F := F) x

/-- Additive reverse map `Additive (K₂ F) →+ MilnorK F 2`,
obtained via `MonoidHom.toAdditiveLeft`. -/
noncomputable def matsumotoReverse :
    Additive (K2 F) →+ MilnorK F 2 :=
  (matsumotoReverseMul (F := F)).toAdditiveLeft

theorem matsumotoReverse_ofMul (x : K2 F) :
    matsumotoReverse (F := F) (Additive.ofMul x) =
      Multiplicative.toAdd (matsumotoReverseMul (F := F) x) :=
  rfl

theorem matsumotoReverse_toMul (x : Additive (K2 F)) :
    matsumotoReverseMul (F := F) (Additive.toMul x) =
      Multiplicative.ofAdd (matsumotoReverse (F := F) x) := by
  cases x with
  | ofMul x => rfl

end AlgebraicKTheory.K2

end

end

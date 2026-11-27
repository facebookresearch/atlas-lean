/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual balanced scalar-extension maps from restriction-of-scalars data

For same-universe associative rings, the original balanced quotient has its
actual universal maps to an S-module. Restriction sends a map to its value on
1 tensor p, and the inverse sends s tensor p to s times the given R-linear
value. The full S-linearity is earned from the original pure and action laws.
No adjunction or functor-comparison outcome is supplied.
-/

public section
noncomputable section

open CategoryTheory MulOpposite

universe u

namespace ModuleCat.RingHomScalarExtension

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- Restrict the actual balanced map by evaluating its original unit pure class. -/
def toRestrictHom {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : (functor f).obj M ⟶ N) : M ⟶ (ModuleCat.restrictScalars f).obj N := by
  let NR := (ModuleCat.restrictScalars f).obj N
  let T := (functor f).obj M
  let gActual : T →ₗ[S] N := g.hom
  let l : M →ₗ[R] NR :=
    { toFun := fun p => (show NR from gActual (pure f M 1 p))
      map_add' := by
        intro p q
        let vp : T := pure f M 1 p
        let vq : T := pure f M 1 q
        have hPure : (show T from pure f M 1 (p + q)) = vp + vq :=
          (pure f M 1).map_add p q
        exact (congrArg gActual hPure).trans (gActual.map_add vp vq)
      map_smul' := by
        intro r p
        let vp : T := pure f M 1 p
        have hBalance : pure f M 1 (r • p) = f r • pure f M 1 p := by
          rw [← pure_balance f M r 1 p, one_mul]
          have h := smul_pure f M (f r) 1 p
          rw [mul_one] at h
          exact h.symm
        have hPure : (show T from pure f M 1 (r • p)) = f r • vp := hBalance
        have hLinear := gActual.map_smul (f r) vp
        change gActual (pure f M 1 (r • p)) = f r • gActual (pure f M 1 p)
        exact (congrArg gActual hPure).trans hLinear }
  exact ModuleCat.ofHom (Y := NR) l

private def actionPairingAdd {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) : S →+ (M →ₗ[ℤ] N) where
  toFun s := by
    let a : M →+ N :=
      { toFun := fun p => s • (g p : N)
        map_zero' := by rw [map_zero, smul_zero]; rfl
        map_add' := by intro p q; rw [map_add, smul_add]; rfl }
    exact a.toIntLinearMap
  map_zero' := by
    apply LinearMap.ext
    intro p
    exact zero_smul S (g p : N)
  map_add' := by
    intro s t
    apply LinearMap.ext
    intro p
    exact add_smul s t (g p : N)

private theorem actionPairingBalance {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) :
    letI := rightModule f
    ∀ (r : R) (s : S) (p : M),
      (actionPairingAdd f g).toIntLinearMap ((op r) • s) p =
        (actionPairingAdd f g).toIntLinearMap s (r • p) := by
  let := rightModule f
  intro r s p
  change ((op r) • s) • (g p : N) = s • (g (r • p) : N)
  rw [rightModule_smul f r s, g.hom.map_smul]
  change (s * f r) • (g p : N) = s • (f r • (g p : N))
  exact mul_smul s (f r) (g p : N)

private def balancedLiftInt {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) : tensor f M →ₗ[ℤ] N := by
  letI := rightModule f
  exact TensorProduct.Balanced.lift (actionPairingAdd f g).toIntLinearMap
    (actionPairingBalance f g)

private theorem balancedLiftIntPure {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (p : M) :
    balancedLiftInt f g (pure f M s p) = s • (g p : N) := by
  let := rightModule f
  exact TensorProduct.Balanced.lift_mk (actionPairingAdd f g).toIntLinearMap
    (actionPairingBalance f g) s p

private def scalarAddHom (s : S) (X : Type u) [AddCommGroup X] [Module S X] : X →+ X where
  toFun x := s • x
  map_zero' := smul_zero s
  map_add' := smul_add s

private theorem balancedLiftIntSmul {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (x : tensor f M) :
    balancedLiftInt f g (s • x) = s • balancedLiftInt f g x := by
  let := rightModule f
  have h : (balancedLiftInt f g).toAddMonoidHom.comp (scalarAddHom s (tensor f M)) =
      (scalarAddHom s N).comp (balancedLiftInt f g).toAddMonoidHom := by
    apply TensorProduct.Balanced.addHom_ext ℤ R S M
    intro a p
    change balancedLiftInt f g (s • pure f M a p) = s • balancedLiftInt f g (pure f M a p)
    rw [smul_pure, balancedLiftIntPure, balancedLiftIntPure]
    exact mul_smul s a (g p : N)
  exact DFunLike.congr_fun h x

/-- The actual universal S-linear map from the original balanced scalar extension. -/
def fromRestrictHom {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) : (functor f).obj M ⟶ N :=
  ModuleCat.ofHom
    { toFun := balancedLiftInt f g
      map_add' := (balancedLiftInt f g).map_add
      map_smul' := balancedLiftIntSmul f g }

private theorem fromRestrictHomPureComputed {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (p : M) :
    fromRestrictHom f g (pure f M s p) = s • (g p : N) :=
  balancedLiftIntPure f g s p

/-- Every original pure class has its actual given restriction-map value. -/
theorem fromRestrictHom_pure {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (p : M) :
    fromRestrictHom f g (pure f M s p) = s • (g p : N) :=
  fromRestrictHomPureComputed f g s p

private theorem toRestrictHomValueComputed {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : (functor f).obj M ⟶ N) (p : M) :
    toRestrictHom f g p = g (pure f M 1 p) := by
  unfold toRestrictHom
  rfl

/-- The actual restriction map evaluates the same original unit pure class. -/
theorem toRestrictHom_value {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : (functor f).obj M ⟶ N) (p : M) :
    toRestrictHom f g p = g (pure f M 1 p) :=
  toRestrictHomValueComputed f g p

/-- The original balanced unit map into restriction of its actual scalar extension. -/
def unitHom (M : ModuleCat.{u} R) : M ⟶ (ModuleCat.restrictScalars f).obj ((functor f).obj M) :=
  toRestrictHom f (𝟙 ((functor f).obj M))

/-- The whole unit uses precisely the original class 1 tensor p. -/
theorem unitHom_value (M : ModuleCat.{u} R) (p : M) :
    unitHom f M p = pure f M 1 p :=
  toRestrictHom_value f (𝟙 ((functor f).obj M)) p

end ModuleCat.RingHomScalarExtension

end

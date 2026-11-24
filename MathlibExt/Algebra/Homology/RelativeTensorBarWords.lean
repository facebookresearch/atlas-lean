/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.RelativeTensorBarComparison
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tensor coordinates for relative Bar complexes

Monad-power transport and finite tensor-product decompositions identify Bar terms with word
coordinates. Their pure-tensor formulas preserve the order of noncommutative factors. The
categorical specialization uses the universe conditions of the monoidal module category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct

universe r u

namespace ModuleCat.RelativeTensorBar

/-- Multiplying the two adjacent middle positions retains their original order. -/
def mergeTuple {R : Type r} [Mul R] {d : ℕ}
    (a : Fin (d + 1) → R) (j : Fin d) (i : Fin d) : R :=
  if i < j then a i.castSucc
  else if i = j then a j.castSucc * a j.succ
  else a i.succ

variable (k R : Type u) [CommRing k] [Ring R] [Algebra k R]

/-- The word coordinates use the original internal monoid of the algebra. -/
local instance : MonObj (ringUnderlying k R) := ringMonObj k R

/-- The first-position/remainder index equivalence for a nonempty word. -/
def splitIndex (d : ℕ) : Fin (d + 1) ≃ PUnit.{1} ⊕ Fin d where
  toFun i := Fin.cases (Sum.inl PUnit.unit) Sum.inr i
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by
    intro i
    cases i with
    | inl a => cases a; rfl
    | inr j => rfl

/-- The first summand is precisely the original first coordinate. -/
theorem splitIndex_symm_inl (d : ℕ) (a : PUnit.{1}) :
    (splitIndex d).symm (Sum.inl a) = 0 := rfl

/-- The second summand retains the original successor coordinate. -/
theorem splitIndex_symm_inr (d : ℕ) (i : Fin d) :
    (splitIndex d).symm (Sum.inr i) = i.succ := rfl

/-- Splitting of the first tensor factor from the remaining word. -/
def splitPower (d : ℕ) :
    (⨂[k] (_ : Fin (d + 1)), R) ≃ₗ[k] R ⊗[k] (⨂[k] (_ : Fin d), R) :=
  ((PiTensorProduct.reindex k (fun _ : Fin (d + 1) => R) (splitIndex d)).trans
    (PiTensorProduct.tmulEquiv k R).symm).trans
      (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : PUnit.{1} => R) PUnit.unit)
        (LinearEquiv.refl k (⨂[k] (_ : Fin d), R)))

private theorem splitPower_tprod (d : ℕ) (a : Fin (d + 1) → R) :
    splitPower k R d (PiTensorProduct.tprod k a) =
      a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a) := by
  simp only [splitPower, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquiv_symm_apply, TensorProduct.congr_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod, LinearEquiv.refl_apply,
    splitIndex_symm_inl, splitIndex_symm_inr]
  rfl

/-- Ordinary tensor coordinates of the monad-power object. -/
def powerCoordinates (d : ℕ) : (X : ModuleCat.{u} k) →
    ModuleCat.of k ((⨂[k] (_ : Fin d), R) ⊗[k] X) ≅
      (Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X :=
  fun X => match d with
    | 0 =>
      let e : ((⨂[k] (_ : Fin 0), R) ⊗[k] X) ≃ₗ[k] k ⊗[k] X :=
        TensorProduct.congr
          (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => R) (Fin 0))
          (LinearEquiv.refl k X)
      e.toModuleIso ≪≫ (λ_ X)
    | d + 1 =>
      let P : ModuleCat.{u} k := ModuleCat.of k (⨂[k] (_ : Fin d), R)
      let e : ((⨂[k] (_ : Fin (d + 1)), R) ⊗[k] X) ≃ₗ[k]
          (R ⊗[k] (⨂[k] (_ : Fin d), R)) ⊗[k] X :=
        TensorProduct.congr (splitPower k R d) (LinearEquiv.refl k X)
      let e₁ : ModuleCat.of k ((⨂[k] (_ : Fin (d + 1)), R) ⊗[k] X) ≅
          ((ringUnderlying k R) ⊗ P) ⊗ X := e.toModuleIso
      let e₂ : (ringUnderlying k R) ⊗ (P ⊗ X) ≅
          (Monad.tensorMonad (ringUnderlying k R)).obj
            ((Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X) :=
        tensorIso (Iso.refl (ringUnderlying k R)) (powerCoordinates d X)
      e₁ ≪≫ (α_ (ringUnderlying k R) P X) ≪≫ e₂ ≪≫
        (eqToIso (Monad.monadPow_succ_obj_eq
          (Monad.tensorMonad (ringUnderlying k R)) d X)).symm

/-- The zero-degree coordinates retain the empty tensor's scalar coefficient. -/
theorem powerCoordinates_zero (X : ModuleCat.{u} k) :
    powerCoordinates k R 0 X =
      (TensorProduct.congr
        (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => R) (Fin 0))
        (LinearEquiv.refl k X)).toModuleIso ≪≫ (λ_ X) := rfl

/-- The next coordinate map splits, associates, and transports the previous map. -/
theorem powerCoordinates_succ (d : ℕ) (X : ModuleCat.{u} k) :
    powerCoordinates k R (d + 1) X =
      (TensorProduct.congr (splitPower k R d) (LinearEquiv.refl k X)).toModuleIso ≪≫
        (α_ (ringUnderlying k R) (ModuleCat.of k (⨂[k] (_ : Fin d), R)) X) ≪≫
        tensorIso (Iso.refl (ringUnderlying k R)) (powerCoordinates k R d X) ≪≫
        (eqToIso (Monad.monadPow_succ_obj_eq
          (Monad.tensorMonad (ringUnderlying k R)) d X)).symm := rfl


/-- A pure word in the monad-power object. -/
def powerPure (d : ℕ) (X : ModuleCat.{u} k) (a : Fin d → R) (x : X) :
    (Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X :=
  (powerCoordinates k R d X).hom.hom (PiTensorProduct.tprod k a ⊗ₜ[k] x)

theorem powerPure_zero (X : ModuleCat.{u} k) (a : Fin 0 → R) (x : X) :
    powerPure k R 0 X a x = x := by
  rw [powerPure, powerCoordinates_zero]
  change (λ_ X).hom.hom
    ((TensorProduct.congr
      (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => R) (Fin 0))
      (LinearEquiv.refl k X)) (PiTensorProduct.tprod k a ⊗ₜ[k] x)) = x
  rw [TensorProduct.congr_tmul, PiTensorProduct.isEmptyEquiv_apply_tprod,
    LinearEquiv.refl_apply]
  exact (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (1 : k) x).trans (one_smul k x)


/-- Peeling the first factor keeps the monad-power transport. -/
theorem powerPure_succ (d : ℕ) (X : ModuleCat.{u} k)
    (a : Fin (d + 1) → R) (x : X) :
    (eqToHom (Monad.monadPow_succ_obj_eq
      (Monad.tensorMonad (ringUnderlying k R)) d X)).hom
      (powerPure k R (d + 1) X a x) =
      a 0 ⊗ₜ[k] powerPure k R d X (Fin.tail a) x := by
  let P : ModuleCat.{u} k := ModuleCat.of k (⨂[k] (_ : Fin d), R)
  let e₁ : ModuleCat.of k ((⨂[k] (_ : Fin (d + 1)), R) ⊗[k] X) ≅
      ((ringUnderlying k R) ⊗ P) ⊗ X :=
    (TensorProduct.congr (splitPower k R d) (LinearEquiv.refl k X)).toModuleIso
  let e₂ : (ringUnderlying k R) ⊗ (P ⊗ X) ≅
      (Monad.tensorMonad (ringUnderlying k R)).obj
        ((Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X) :=
    tensorIso (Iso.refl (ringUnderlying k R)) (powerCoordinates k R d X)
  let e₃ := eqToIso (Monad.monadPow_succ_obj_eq
    (Monad.tensorMonad (ringUnderlying k R)) d X)
  rw [powerPure, powerCoordinates_succ]
  change e₃.hom.hom
    ((e₁ ≪≫ (α_ (ringUnderlying k R) P X) ≪≫ e₂ ≪≫ e₃.symm).hom.hom
      (PiTensorProduct.tprod k a ⊗ₜ[k] x)) =
    a 0 ⊗ₜ[k] (powerCoordinates k R d X).hom.hom
      (PiTensorProduct.tprod k (Fin.tail a) ⊗ₜ[k] x)
  have cancel (z : (Monad.tensorMonad (ringUnderlying k R)).obj
      ((Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X)) :
      e₃.hom.hom (e₃.inv.hom z) = z := ModuleCat.hom_inv_apply e₃ z
  simp only [Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cancel]
  have hs : e₁.hom.hom (PiTensorProduct.tprod k a ⊗ₜ[k] x) =
      (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)) ⊗ₜ[k] x := by
    change (TensorProduct.congr (splitPower k R d) (LinearEquiv.refl k X))
      (PiTensorProduct.tprod k a ⊗ₜ[k] x) = _
    rw [TensorProduct.congr_tmul, splitPower_tprod, LinearEquiv.refl_apply]
  rw [hs]
  have ha : (α_ (ringUnderlying k R) P X).hom.hom
      ((a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)) ⊗ₜ[k] x) =
      a 0 ⊗ₜ[k] (PiTensorProduct.tprod k (Fin.tail a) ⊗ₜ[k] x) :=
    ModuleCat.MonoidalCategory.associator_hom_apply _ _ _
  rw [ha]
  change ((Iso.refl (ringUnderlying k R)).hom ⊗ₘ (powerCoordinates k R d X).hom).hom
    (a 0 ⊗ₜ[k] (PiTensorProduct.tprod k (Fin.tail a) ⊗ₜ[k] x)) = _
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rfl


/-- Pure coordinate values determine a map out of the power. -/
theorem powerPure_ext (d : ℕ) (X Z : ModuleCat.{u} k)
    (f g : (Monad.monadPow (Monad.tensorMonad (ringUnderlying k R)) d).obj X ⟶ Z)
    (h : ∀ (a : Fin d → R) (x : X), f.hom (powerPure k R d X a x) =
      g.hom (powerPure k R d X a x)) : f = g := by
  apply (cancel_epi (powerCoordinates k R d X).hom).1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro q x
  have hh : f.hom.comp ((powerCoordinates k R d X).hom.hom.comp
      ((TensorProduct.mk k (⨂[k] (_ : Fin d), R) X).flip x)) =
    g.hom.comp ((powerCoordinates k R d X).hom.hom.comp
      ((TensorProduct.mk k (⨂[k] (_ : Fin d), R) X).flip x)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    exact h a x
  exact LinearMap.congr_fun hh q

/-- Ordinary word coordinates of the literal coefficient Bar level. -/
def barCoordinates (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) (d : ℕ) :
    ModuleCat.of k ((rightUnderlying k R M).carrier ⊗[k]
      ((⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier)) ≅
      (literalBar k R M N).obj (Opposite.op (SimplexCategory.mk d)) :=
  tensorIso (Iso.refl (rightUnderlying k R M))
    (powerCoordinates k R d (leftUnderlying k R N))

/-- A tensor morphism evaluates on its two pure components. -/
private theorem native_tensorHom_value {A B C D : ModuleCat.{u} k}
    (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
    (f ⊗ₘ g).hom (x ⊗ₜ[k] y) = f.hom x ⊗ₜ[k] g.hom y := rfl

/-- Pure values use the original right and left coefficient carriers. -/
def barPure (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) (d : ℕ)
    (x : M) (a : Fin d → R) (y : N) :
    (literalBar k R M N).obj (Opposite.op (SimplexCategory.mk d)) :=
  (barCoordinates k R M N d).hom.hom
    ((show (rightUnderlying k R M).carrier from x) ⊗ₜ[k]
      (PiTensorProduct.tprod k a ⊗ₜ[k] (show (leftUnderlying k R N).carrier from y)))

theorem barPure_val (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) (d : ℕ)
    (x : M) (a : Fin d → R) (y : N) :
    barPure k R M N d x a y =
      (show (rightUnderlying k R M).carrier from x) ⊗ₜ[k]
        powerPure k R d (leftUnderlying k R N) a
          (show (leftUnderlying k R N).carrier from y) := by
  let X : (rightUnderlying k R M).carrier := x
  let Y : ((⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier) :=
    PiTensorProduct.tprod k a ⊗ₜ[k] (show (leftUnderlying k R N).carrier from y)
  have h := native_tensorHom_value (k := k)
    (𝟙 (rightUnderlying k R M)) (powerCoordinates k R d (leftUnderlying k R N)).hom X Y
  change (barCoordinates k R M N d).hom.hom (X ⊗ₜ[k] Y) =
    X ⊗ₜ[k] (powerCoordinates k R d (leftUnderlying k R N)).hom.hom Y
  change ((𝟙 (rightUnderlying k R M)) ⊗ₘ
    (powerCoordinates k R d (leftUnderlying k R N)).hom).hom (X ⊗ₜ[k] Y) = _
  simpa only [ModuleCat.hom_id, LinearMap.id_apply] using h


/-- Pure values determine every literal Bar level map. -/
theorem barPure_ext (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) (d : ℕ)
    (Z : ModuleCat.{u} k)
    (f g : (literalBar k R M N).obj (Opposite.op (SimplexCategory.mk d)) ⟶ Z)
    (h : ∀ (x : M) (a : Fin d → R) (y : N),
      f.hom (barPure k R M N d x a y) = g.hom (barPure k R M N d x a y)) : f = g := by
  apply (cancel_epi (barCoordinates k R M N d).hom).1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x z
  induction z using TensorProduct.inductionOn with
  | tmul q y =>
      let c : (⨂[k] (_ : Fin d), R) →ₗ[k]
          (⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier :=
        (TensorProduct.mk k (⨂[k] (_ : Fin d), R)
          (leftUnderlying k R N).carrier).flip y
      let b : ((⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier) →ₗ[k]
          (literalBar k R M N).obj (Opposite.op (SimplexCategory.mk d)) :=
        (barCoordinates k R M N d).hom.hom.comp
          ((TensorProduct.mk k (rightUnderlying k R M).carrier
            ((⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier)) x)
      have hh : f.hom.comp (b.comp c) = g.hom.comp (b.comp c) := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro a
        exact h x a y
      exact LinearMap.congr_fun hh q
  | add z₁ z₂ h₁ h₂ =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        TensorProduct.tmul_add, map_add] at h₁ h₂ ⊢
      rw [h₁, h₂]

end ModuleCat.RelativeTensorBar

end

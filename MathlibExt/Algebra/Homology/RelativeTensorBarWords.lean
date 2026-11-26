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
# Ordered tensor coordinates for relative bar complexes

For a commutative ring k, a possibly noncommutative k-algebra R and a k-module X, the iterated
tensor-monad object T^d(X), T=R ⊗_k −, is canonically isomorphic to R^{⊗d} ⊗_k X. Splitting off
the first factor gives its recursive coordinates. For a right R-module M and left R-module N in
the same module-category universe, this identifies degree d of the relative bar construction
with M ⊗_k (R^{⊗d} ⊗_k N). Pure ordered tensors determine maps from these objects; adjacent
multiplication retains the order of the algebra factors.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct

universe r u

namespace ModuleCat.RelativeTensorBar

/-- Let R be a type with multiplication, d ∈ ℕ, a : Fin(d+1) → R a word and j ∈ Fin(d). The
shortened word mergeTuple a j has entry a_i for i<j, entry a_j a_{j+1} for i=j, and entry
a_{i+1} for i>j, using the canonical finite-index inclusions. No associativity or commutativity
of multiplication is required. -/
def mergeTuple {R : Type r} [Mul R] {d : ℕ}
    (a : Fin (d + 1) → R) (j : Fin d) (i : Fin d) : R :=
  if i < j then a i.castSucc
  else if i = j then a j.castSucc * a j.succ
  else a i.succ

variable (k R : Type u) [CommRing k] [Ring R] [Algebra k R]

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. The
monoid structure on the k-module R used in these tensor coordinates has multiplication r⊗s ↦ rs
and unit the algebra map k → R. -/
local instance : MonObj (ringUnderlying k R) := ringMonObj k R

/-- For d ∈ ℕ, splitIndex is the equivalence Fin(d+1) ≅ {∗} ⊔ Fin(d) sending position zero to the
singleton summand and a successor position i+1 to i in the remainder. -/
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

/-- For d ∈ ℕ and the unique a in the singleton summand of {∗} ⊔ Fin(d), the inverse of splitIndex
sends a to position zero in Fin(d+1). -/
theorem splitIndex_symm_inl (d : ℕ) (a : PUnit.{1}) :
    (splitIndex d).symm (Sum.inl a) = 0 := rfl

/-- For d ∈ ℕ and i ∈ Fin(d), the inverse of splitIndex sends i in the remainder summand to i+1 in
Fin(d+1). -/
theorem splitIndex_symm_inr (d : ℕ) (i : Fin d) :
    (splitIndex d).symm (Sum.inr i) = i.succ := rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ there is a k-linear equivalence R^{⊗(d+1)} ≅ R ⊗_k R^{⊗d}, indexed by Fin(d+1) and Fin(d).
It sends the pure tensor of a word a to a₀ ⊗ the pure tensor of its tail. -/
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

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ and X ∈ ModuleCat k, powerCoordinates is the canonical isomorphism R^{⊗d} ⊗_k X ≅ T^d(X),
where T=R ⊗_k − and the tensor power is indexed by Fin(d). It preserves the order of the R
factors. -/
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

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For X
∈ ModuleCat k, powerCoordinates in degree zero is the composite R^{⊗0} ⊗_k X ≅ k ⊗_k X ≅ X. The
first map identifies the empty tensor product with k and the second is the left unitor. -/
theorem powerCoordinates_zero (X : ModuleCat.{u} k) :
    powerCoordinates k R 0 X =
      (TensorProduct.congr
        (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => R) (Fin 0))
        (LinearEquiv.refl k X)).toModuleIso ≪≫ (λ_ X) := rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ and X ∈ ModuleCat k, powerCoordinates at d+1 first splits R^{⊗(d+1)} into R ⊗_k R^{⊗d},
associates the tensor factors, applies id_R ⊗ powerCoordinates_d, and finally identifies R ⊗_k
T^d(X) with T^{d+1}(X). -/
theorem powerCoordinates_succ (d : ℕ) (X : ModuleCat.{u} k) :
    powerCoordinates k R (d + 1) X =
      (TensorProduct.congr (splitPower k R d) (LinearEquiv.refl k X)).toModuleIso ≪≫
        (α_ (ringUnderlying k R) (ModuleCat.of k (⨂[k] (_ : Fin d), R)) X) ≪≫
        tensorIso (Iso.refl (ringUnderlying k R)) (powerCoordinates k R d X) ≪≫
        (eqToIso (Monad.monadPow_succ_obj_eq
          (Monad.tensorMonad (ringUnderlying k R)) d X)).symm := rfl


/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ, a word a : Fin(d) → R, X ∈ ModuleCat k and x ∈ X, powerPure is the image of
(⊗_{i∈Fin(d)}a_i) ⊗ x under powerCoordinates : R^{⊗d} ⊗_k X ≅ T^d(X). -/
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


/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ, X ∈ ModuleCat k, a : Fin(d+1) → R and x ∈ X, the canonical identification T^{d+1}(X) ≅ R
⊗_k T^d(X) sends powerPure(a,x) to a₀ ⊗ powerPure(tail(a),x). -/
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


/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For d
∈ ℕ and k-modules X,Z, maps f,g : T^d(X) → Z are equal if f(powerPure(a,x)) = g(powerPure(a,x))
for every word a : Fin(d) → R and every x ∈ X. -/
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

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, left R-module N and d ∈ ℕ, barCoordinates is the k-module isomorphism M ⊗_k
(R^{⊗d} ⊗_k N) ≅ literalBar(M,N)_d, obtained by tensoring the power-coordinate map of N with
id_M. -/
def barCoordinates (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) (d : ℕ) :
    ModuleCat.of k ((rightUnderlying k R M).carrier ⊗[k]
      ((⨂[k] (_ : Fin d), R) ⊗[k] (leftUnderlying k R N).carrier)) ≅
      (literalBar k R M N).obj (Opposite.op (SimplexCategory.mk d)) :=
  tensorIso (Iso.refl (rightUnderlying k R M))
    (powerCoordinates k R d (leftUnderlying k R N))

/-- Let k be a commutative ring, A,B,C,D k-modules, f : A → B and g : C → D k-linear maps, and x ∈
A,y ∈ C. The tensor map satisfies (f⊗g)(x⊗y) = f(x)⊗g(y). -/
private theorem native_tensorHom_value {A B C D : ModuleCat.{u} k}
    (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
    (f ⊗ₘ g).hom (x ⊗ₜ[k] y) = f.hom x ⊗ₜ[k] g.hom y := rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, left R-module N, d ∈ ℕ, x ∈ M, y ∈ N and a : Fin(d) → R, barPure is the image
of x ⊗ ((⊗_i a_i) ⊗ y) under the degree-d coordinate isomorphism M ⊗_k (R^{⊗d} ⊗_k N) ≅
literalBar(M,N)_d. -/
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


/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, left R-module N, d ∈ ℕ and k-module Z, maps f,g : literalBar(M,N)_d → Z are
equal if they agree on barPure(x,a,y) for every x ∈ M, a : Fin(d) → R and y ∈ N. -/
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Generic monoidal finite tensor powers

For `X : C` in an arbitrary monoidal category define the left-associated
finite power `tensorPowObj X n` (`0 ↦ 𝟙`, `n+1 ↦ pow n ⊗ X`), functorial
`tensorPowMap`, and the finite add/coherence isomorphism
`pow (m + n) ≅ pow m ⊗ pow n`.  For a lax monoidal functor `G`, it also
constructs the ordered multiplication and unit on the objects
`G.obj (tensorPowObj X n)`, with naturality, unit, and associativity laws.

This supplies reusable category-level finite tensor powers. It uses only ambient `tensorObj` /
`tensorHom` (notation `⊗` / `⊗ₘ`), `associator`, unitors, and generic
coherence lemmas. No `ModuleCat`, `GradedObject`, `HomologicalComplex`,
preadditive, zero-morphism, dg/sign, coproduct, free/cofree, completion, or
operad content is provided here.

## Declaration inventory

* `tensorPowObj`: left-associated `n`-fold power.
* `tensorPowObj_zero` / `tensorPowObj_succ`: computation rules.
* `tensorPowMap`: functorial map by recursion via `⊗ₘ`.
* `tensorPowMap_zero` / `tensorPowMap_succ`: computation rules.
* `tensorPowMap_id` / `tensorPowMap_comp`: functoriality laws.
* `tensorPowFunctor`: the bundled power functor for each `n`.
* `tensorPowObj_add`: finite add/coherence iso by induction on `n`
  (base via `rightUnitor`, step via `tensorIso` + `associator`).
* `tensorPowAddNatIso`: the add/coherence isomorphism bundled naturally in `X`.
* `tensorPowObj_add_zero_right` / `tensorPowObj_add_zero_left`: unit coherence.
* `tensorPowObj_eqToHom_whiskerRight`: generic right-whisker transport for
  `tensorPowObj` equalities, derived from `MonoidalCategory.eqToHom_whiskerRight`.
* `tensorPowObj_add_naturality`: the add iso commutes with `tensorPowMap`.
* `tensorPowObj_add_assoc`: the two `(m+n)+k` reassociation routes agree
  (by induction on `k` via `pentagon` + associator naturality).
* `laxTensorPowerPairing` / `laxTensorPowerUnit`: the ordered multiplication
  and unit on tensor powers after applying a lax monoidal functor.
* `laxTensorPowerPairing_naturality`: naturality in the base object.
* `laxTensorPowerPairing_zero_left` / `laxTensorPowerPairing_zero_right`:
  the lax unit laws.
* `laxTensorPowerPairing_assoc`: ordered associativity.

## Finite-support note

For fixed `n`, `tensorPowObj X n` is an `n`-fold binary iteration. No
infinite sum, tensor coalgebra carrier, or colimit beyond binary `⊗`
is constructed here. This is explicitly *not* a graded direct sum.

## Nonclaims

* No infinite sums, (co)free objects, filtrations, completeness, or
  adjunction data.
* No derived, Koszul, operadic, or model-category claim.
* No new global instances are declared.

## Import justification

`CoherenceLemmas` (which transitively imports `Monoidal.Category`) supplies
`Category` / `MonoidalCategory`, `tensorObj` / `tensorHom` (`⊗` / `⊗ₘ`),
`tensorIso`, `associator`, `leftUnitor` / `rightUnitor`, and the
`tensorHom_comp`, `associator_naturality`, `leftUnitor_naturality`,
`rightUnitor_naturality`, `pentagon`, and `triangle` coherence fields.
`Monoidal.Category` supplies `leftUnitor_tensor_hom` for the `0+n` step and
`rightUnitor_tensor_inv` for the associativity base case; `CoherenceLemmas`
contributes `unitors_equal` for the `0+n` base case.
-/

@[expose] public section

set_option autoImplicit false

universe v u vD uD

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.TensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Left-associated finite tensor power: `0 ↦ 𝟙`, `n+1 ↦ pow n ⊗ X`. -/
noncomputable def tensorPowObj (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => tensorPowObj X n ⊗ X

/-- Computation rule: `tensorPowObj X 0` is the tensor unit. -/
@[simp]
theorem tensorPowObj_zero (X : C) : tensorPowObj X 0 = 𝟙_ C :=
  rfl

/-- Computation rule: `tensorPowObj X (n + 1)` is `tensorPowObj X n ⊗ X`. -/
@[simp]
theorem tensorPowObj_succ (X : C) (n : ℕ) :
    tensorPowObj X (n + 1) = tensorPowObj X n ⊗ X :=
  rfl

/-- Functorial map on finite powers by recursion via `⊗ₘ`. -/
noncomputable def tensorPowMap {X Y : C} (f : X ⟶ Y) : ∀ (n : ℕ),
    tensorPowObj X n ⟶ tensorPowObj Y n
  | 0 => 𝟙 _
  | n + 1 => tensorPowMap f n ⊗ₘ f

/-- Computation rule: `tensorPowMap f 0` is the identity on the unit. -/
@[simp]
theorem tensorPowMap_zero {X Y : C} (f : X ⟶ Y) :
    tensorPowMap f 0 = 𝟙 _ :=
  rfl

/-- Computation rule: `tensorPowMap f (n + 1)` is `tensorPowMap f n ⊗ₘ f`. -/
@[simp]
theorem tensorPowMap_succ {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) = tensorPowMap f n ⊗ₘ f :=
  rfl

/-- Identity law: mapping the identity yields the identity on each tensor power. -/
@[simp]
theorem tensorPowMap_id (X : C) (n : ℕ) :
    tensorPowMap (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tensorPowMap (𝟙 X) n ⊗ₘ 𝟙 X = 𝟙 _
    rw [ih]
    exact id_tensorHom_id _ _

/-- Composition law: `tensorPowMap` preserves composition degreewise. -/
theorem tensorPowMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    tensorPowMap (f ≫ g) n = tensorPowMap f n ≫ tensorPowMap g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change tensorPowMap (f ≫ g) n ⊗ₘ (f ≫ g) =
      (tensorPowMap f n ⊗ₘ f) ≫ (tensorPowMap g n ⊗ₘ g)
    rw [ih]
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- The `n`-fold tensor power as a functor of its base object. -/
noncomputable def tensorPowFunctor (n : ℕ) : C ⥤ C where
  obj X := tensorPowObj X n
  map f := tensorPowMap f n
  map_id X := tensorPowMap_id X n
  map_comp f g := tensorPowMap_comp f g n

@[simp]
theorem tensorPowFunctor_obj (n : ℕ) (X : C) :
    (tensorPowFunctor n).obj X = tensorPowObj X n :=
  rfl

@[simp]
theorem tensorPowFunctor_map (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (tensorPowFunctor n).map f = tensorPowMap f n :=
  rfl

/-- Finite add/coherence iso: `pow (m + n) ≅ pow m ⊗ pow n` by induction on
`n` (base via `rightUnitor`, step via `tensorIso` + `associator`). -/
noncomputable def tensorPowObj_add (X : C) (m : ℕ) : ∀ (n : ℕ),
    tensorPowObj X (m + n) ≅ tensorPowObj X m ⊗ tensorPowObj X n
  | 0 => (rightUnitor _).symm
  | n + 1 =>
      (tensorIso (tensorPowObj_add X m n) (Iso.refl X)) ≪≫
        associator _ _ _

/-- Right-unit coherence: `tensorPowObj_add X m 0` is the inverse right unitor. -/
theorem tensorPowObj_add_zero_right (X : C) (m : ℕ) :
    (tensorPowObj_add X m 0).hom = (rightUnitor _).symm.hom :=
  rfl

/-- Generic right-whisker transport for `tensorPowObj` equalities, derived
from `MonoidalCategory.eqToHom_whiskerRight`. -/
theorem tensorPowObj_eqToHom_whiskerRight (X : C) {a b : ℕ} (h : a = b) :
    ((eqToIso (congrArg (tensorPowObj X) h)).hom ⊗ₘ 𝟙 X) =
      (eqToIso (congrArg (fun k => tensorPowObj X k ⊗ X) h)).hom := by
  rw [eqToIso.hom, tensorHom_id, MonoidalCategory.eqToHom_whiskerRight]
  cases h
  rfl

/-- Left-unit coherence: unfolding `tensorPowObj_add X 0 n` then the left unitor
is transport along `0 + n = n`. -/
theorem tensorPowObj_add_zero_left (X : C) (n : ℕ) :
    (tensorPowObj_add X 0 n).hom ≫
        (leftUnitor (tensorPowObj X n)).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := by
  induction n with
  | zero =>
    rw [tensorPowObj_add_zero_right] at ⊢
    change (rightUnitor (𝟙_ C)).inv ≫ (leftUnitor (𝟙_ C)).hom =
      𝟙 (𝟙_ C)
    have hUE : (leftUnitor (𝟙_ C)).hom = (rightUnitor (𝟙_ C)).hom :=
      unitors_equal
    rw [hUE, Iso.inv_hom_id]
  | succ n ih =>
    have hAdd : (tensorPowObj_add X 0 (n + 1)).hom =
          (tensorIso (tensorPowObj_add X 0 n) (Iso.refl X)).hom ≫
          (associator (tensorPowObj X 0)
            (tensorPowObj X n) X).hom := rfl
    have hIso : (tensorIso (tensorPowObj_add X 0 n) (Iso.refl X)).hom =
        (tensorPowObj_add X 0 n).hom ⊗ₘ 𝟙 X := rfl
    rw [hAdd, hIso] at ⊢
    let a2 : tensorPowObj X (0 + n) ⟶ 𝟙_ C ⊗ tensorPowObj X n :=
      Eq.mpr
        (congrArg (fun U => tensorPowObj X (0 + n) ⟶ U ⊗ tensorPowObj X n)
          (rfl : tensorPowObj X 0 = 𝟙_ C)) (tensorPowObj_add X 0 n).hom
    have hTri := leftUnitor_tensor_hom (tensorPowObj X n) X
    have hTriW : (leftUnitor (tensorPowObj X n ⊗ X)).hom =
        (associator (𝟙_ C) (tensorPowObj X n) X).inv ≫
        ((leftUnitor (tensorPowObj X n)).hom ⊗ₘ 𝟙 X) := by
      rw [hTri, ← tensorHom_id]
    have ih_t : a2 ≫ (leftUnitor (tensorPowObj X n)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := ih
    change ((a2 ⊗ₘ 𝟙 X) ≫ (associator (𝟙_ C) (tensorPowObj X n) X).hom) ≫
        (leftUnitor (tensorPowObj X n ⊗ X)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add (n + 1)))).hom
    rw [hTriW, Category.assoc, ← Category.assoc
      (associator (𝟙_ C) (tensorPowObj X n) X).hom
      (associator (𝟙_ C) (tensorPowObj X n) X).inv _,
      Iso.hom_inv_id, Category.id_comp, tensorHom_comp_tensorHom,
      Category.comp_id, ih_t]
    rw [tensorPowObj_eqToHom_whiskerRight X (Nat.zero_add n)]
    have hD : Nat.zero_add (n + 1) = congrArg Nat.succ (Nat.zero_add n) :=
      rfl
    rw [hD]
    rfl

/-- Naturality of `tensorPowObj_add` in the base morphism: mapping commutes with splitting. -/
theorem tensorPowObj_add_naturality {X Y : C} (f : X ⟶ Y) (m n : ℕ) :
    tensorPowMap f (m + n) ≫ (tensorPowObj_add Y m n).hom =
      (tensorPowObj_add X m n).hom ≫
        ((tensorPowMap f m) ⊗ₘ (tensorPowMap f n)) := by
  induction n generalizing m with
  | zero =>
    rw [tensorPowObj_add_zero_right, tensorPowObj_add_zero_right]
    change tensorPowMap f m ≫ (rightUnitor _).inv =
      (rightUnitor _).inv ≫ (tensorPowMap f m ⊗ₘ 𝟙 _)
    have h := rightUnitor_naturality (tensorPowMap f m)
    have h' : (tensorPowMap f m ⊗ₘ 𝟙 _) ≫ (rightUnitor _).hom =
        (rightUnitor _).hom ≫ tensorPowMap f m := by
      rw [tensorHom_id]
      exact h
    rw [Iso.comp_inv_eq, Category.assoc, h',
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  | succ n ih =>
    have hMap : tensorPowMap f (m + (n + 1)) =
        tensorPowMap f (m + n) ⊗ₘ f := rfl
    have hMapN : tensorPowMap f (n + 1) =
        tensorPowMap f n ⊗ₘ f := rfl
    have hAddY : (tensorPowObj_add Y m (n + 1)).hom =
          (tensorIso (tensorPowObj_add Y m n) (Iso.refl Y)).hom ≫
          (associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom := rfl
    have hAddX : (tensorPowObj_add X m (n + 1)).hom =
          (tensorIso (tensorPowObj_add X m n) (Iso.refl X)).hom ≫
          (associator (tensorPowObj X m)
            (tensorPowObj X n) X).hom := rfl
    have hIsoY : (tensorIso (tensorPowObj_add Y m n) (Iso.refl Y)).hom =
        (tensorPowObj_add Y m n).hom ⊗ₘ 𝟙 Y := rfl
    have hIsoX : (tensorIso (tensorPowObj_add X m n) (Iso.refl X)).hom =
        (tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X := rfl
    rw [hMap, hAddY, hAddX, hIsoY, hIsoX, hMapN]
    change (tensorPowMap f (m + n) ⊗ₘ f) ≫
        (((tensorPowObj_add Y m n).hom ⊗ₘ 𝟙 Y) ≫
          (associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom) =
      (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 X) ≫
        (associator (tensorPowObj X m)
          (tensorPowObj X n) X).hom) ≫
        (tensorPowMap f m ⊗ₘ (tensorPowMap f n ⊗ₘ f))
    have hNat := associator_naturality
      (tensorPowMap f m) (tensorPowMap f n) f
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id, ih] at ⊢
    nth_rewrite 3 [← Category.id_comp f] at ⊢
    rw [← tensorHom_comp_tensorHom, Category.assoc, hNat,
      ← Category.assoc] at ⊢

/-- Tensor powers turn addition of exponents into tensor product, naturally in the base object. -/
noncomputable def tensorPowAddNatIso (m n : ℕ) :
    tensorPowFunctor (C := C) (m + n) ≅
      (tensorPowFunctor (C := C) m).prod' (tensorPowFunctor (C := C) n) ⋙
        MonoidalCategory.tensor C :=
  NatIso.ofComponents (fun X ↦ tensorPowObj_add X m n)
    (fun f ↦ tensorPowObj_add_naturality f m n)

/-- Associativity coherence: the two `((m + n) + k)`-reassociation routes via
`tensorPowObj_add` agree up to the associator. -/
theorem tensorPowObj_add_assoc (X : C) (m n k : ℕ) :
    (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
        (tensorPowObj_add X m (n + k)).hom ≫
        (𝟙 _ ⊗ₘ (tensorPowObj_add X n k).hom) =
      (tensorPowObj_add X (m + n) k).hom ≫
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _) ≫
        (associator _ _ _).hom := by
  induction k with
  | zero =>
    have hr : (m + n) + 0 = m + (n + 0) := rfl
    have hAeq : Nat.add_assoc m n 0 = hr := rfl
    rw [hAeq] at ⊢
    have hA1 : (eqToIso (congrArg (tensorPowObj X) hr)).hom = 𝟙 _ := rfl
    rw [hA1, Category.id_comp] at ⊢
    have hN0 : (tensorPowObj_add X m (n + 0)).hom =
        (tensorPowObj_add X m n).hom := rfl
    rw [hN0] at ⊢
    have hR1 : (tensorPowObj_add X n 0).hom =
        (rightUnitor (tensorPowObj X n)).symm.hom :=
      tensorPowObj_add_zero_right X n
    have hR2 : (tensorPowObj_add X (m + n) 0).hom =
        (rightUnitor (tensorPowObj X (m + n))).symm.hom :=
      tensorPowObj_add_zero_right X (m + n)
    rw [hR1, hR2] at ⊢
    change (tensorPowObj_add X m n).hom ≫
        (𝟙 _ ⊗ₘ (rightUnitor (tensorPowObj X n)).inv) =
      (rightUnitor (tensorPowObj X (m + n))).inv ≫
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _) ≫
        (associator (tensorPowObj X m)
          (tensorPowObj X n) (𝟙_ C)).hom
    have hTinv : (rightUnitor
          (tensorPowObj X m ⊗ tensorPowObj X n)).inv =
        (𝟙 (tensorPowObj X m) ⊗ₘ (rightUnitor (tensorPowObj X n)).inv) ≫
        (associator (tensorPowObj X m)
          (tensorPowObj X n) (𝟙_ C)).inv := by
      have h := rightUnitor_tensor_inv
        (tensorPowObj X m) (tensorPowObj X n)
      rwa [← id_tensorHom] at h
    have hNat := rightUnitor_naturality (tensorPowObj_add X m n).hom
    have hNat' : ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _) ≫
        (rightUnitor (tensorPowObj X m ⊗ tensorPowObj X n)).hom =
        (rightUnitor (tensorPowObj X (m + n))).hom ≫
          (tensorPowObj_add X m n).hom := by
      rw [tensorHom_id]
      exact hNat
    have hVW : (rightUnitor (tensorPowObj X (m + n))).inv ≫
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _) =
        (tensorPowObj_add X m n).hom ≫
        (rightUnitor (tensorPowObj X m ⊗ tensorPowObj X n)).inv := by
      have h1 : (rightUnitor (tensorPowObj X (m + n))).hom ≫
          ((rightUnitor (tensorPowObj X (m + n))).inv ≫
          ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _)) =
          (rightUnitor (tensorPowObj X (m + n))).hom ≫
          ((tensorPowObj_add X m n).hom ≫
          (rightUnitor (tensorPowObj X m ⊗ tensorPowObj X n)).inv) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          ← Category.assoc, ← hNat', Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      exact (Iso.cancel_iso_hom_left (rightUnitor (tensorPowObj X (m + n))) _ _).mp h1
    rw [← Category.assoc, hVW, Category.assoc, hTinv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id] at ⊢
  | succ k ih =>
    have hAddR : (tensorPowObj_add X (m + n) (k + 1)).hom =
          (tensorIso (tensorPowObj_add X (m + n) k) (Iso.refl X)).hom ≫
          (associator (tensorPowObj X (m + n))
            (tensorPowObj X k) X).hom := rfl
    have hAddM : (tensorPowObj_add X m (n + (k + 1))).hom =
          (tensorIso (tensorPowObj_add X m (n + k)) (Iso.refl X)).hom ≫
          (associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom := rfl
    have hAddN : (tensorPowObj_add X n (k + 1)).hom =
          (tensorIso (tensorPowObj_add X n k) (Iso.refl X)).hom ≫
          (associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom := rfl
    have hIsoR : (tensorIso
        (tensorPowObj_add X (m + n) k) (Iso.refl X)).hom =
        (tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X := rfl
    have hIsoM : (tensorIso
        (tensorPowObj_add X m (n + k)) (Iso.refl X)).hom =
        (tensorPowObj_add X m (n + k)).hom ⊗ₘ 𝟙 X := rfl
    have hIsoN : (tensorIso (tensorPowObj_add X n k) (Iso.refl X)).hom =
        (tensorPowObj_add X n k).hom ⊗ₘ 𝟙 X := rfl
    have hD : Nat.add_assoc m n (k + 1) =
        congrArg Nat.succ (Nat.add_assoc m n k) := rfl
    rw [hD] at ⊢
    rw [hAddR, hAddM, hAddN, hIsoR, hIsoM, hIsoN] at ⊢
    change (eqToIso (congrArg (fun j => tensorPowObj X j ⊗ X)
            (Nat.add_assoc m n k))).hom ≫
          (((tensorPowObj_add X m (n + k)).hom ⊗ₘ 𝟙 X) ≫
          (associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom) ≫
          (𝟙 _ ⊗ₘ (((tensorPowObj_add X n k).hom ⊗ₘ 𝟙 X) ≫
            (associator (tensorPowObj X n)
              (tensorPowObj X k) X).hom)) =
        (((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X) ≫
        (associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom) ≫
        (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 _) ≫
        (associator (tensorPowObj X m)
          (tensorPowObj X n)
          (tensorPowObj X k ⊗ X)).hom)
    rw [← tensorPowObj_eqToHom_whiskerRight X (Nat.add_assoc m n k)] at ⊢
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id] at ⊢
    have e1 : (𝟙 (tensorPowObj X m)) =
        𝟙 (tensorPowObj X m) ≫ 𝟙 (tensorPowObj X m) :=
      (Category.id_comp _).symm
    rw [e1] at ⊢
    rw [← tensorHom_comp_tensorHom] at ⊢
    have hNat3 := associator_naturality
      (𝟙 (tensorPowObj X m)) (tensorPowObj_add X n k).hom (𝟙 X)
    rw [Category.assoc _ _
      ((𝟙 (tensorPowObj X m) ⊗ₘ
        ((tensorPowObj_add X n k).hom ⊗ₘ 𝟙 X)) ≫
      (𝟙 (tensorPowObj X m) ⊗ₘ
        (associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom))] at ⊢
    rw [← Category.assoc
      (associator (tensorPowObj X m)
        (tensorPowObj X (n + k)) X).hom
      (𝟙 (tensorPowObj X m) ⊗ₘ
        ((tensorPowObj_add X n k).hom ⊗ₘ 𝟙 X))
      (𝟙 (tensorPowObj X m) ⊗ₘ
        (associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← hNat3] at ⊢
    rw [Category.assoc
      (((𝟙 (tensorPowObj X m) ⊗ₘ (tensorPowObj_add X n k).hom) ⊗ₘ 𝟙 X))
      (associator (tensorPowObj X m)
        (tensorPowObj X n ⊗ tensorPowObj X k) X).hom
      (𝟙 (tensorPowObj X m) ⊗ₘ
        (associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← Category.assoc
      (((eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
          (tensorPowObj_add X m (n + k)).hom) ⊗ₘ 𝟙 X)
      ((𝟙 (tensorPowObj X m) ⊗ₘ (tensorPowObj_add X n k).hom) ⊗ₘ 𝟙 X)
      ((associator (tensorPowObj X m)
        (tensorPowObj X n ⊗ tensorPowObj X k) X).hom ≫
      (𝟙 (tensorPowObj X m) ⊗ₘ
        (associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom))] at ⊢
    rw [tensorHom_comp_tensorHom, Category.comp_id] at ⊢
    rw [Category.assoc
      (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom
      (tensorPowObj_add X m (n + k)).hom
      (𝟙 (tensorPowObj X m) ⊗ₘ (tensorPowObj_add X n k).hom)] at ⊢
    rw [ih] at ⊢
    have e2 : (𝟙 X) = 𝟙 X ≫ 𝟙 X :=
      (Category.id_comp _).symm
    conv_lhs =>
      rw [e2, ← tensorHom_comp_tensorHom]
    conv_lhs =>
      rw [e2, ← tensorHom_comp_tensorHom, Category.comp_id]
    rw [Category.assoc] at ⊢
    rw [Category.assoc] at ⊢
    have hPent : (((associator (tensorPowObj X m)
            (tensorPowObj X n) (tensorPowObj X k)).hom ⊗ₘ 𝟙 X) ≫
        ((associator (tensorPowObj X m)
          (tensorPowObj X n ⊗ tensorPowObj X k) X).hom ≫
        (𝟙 (tensorPowObj X m) ⊗ₘ
          (associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom))) =
        (associator (tensorPowObj X m ⊗ tensorPowObj X n)
          (tensorPowObj X k) X).hom ≫
        (associator (tensorPowObj X m)
          (tensorPowObj X n)
          (tensorPowObj X k ⊗ X)).hom := by
      have h := pentagon
        (tensorPowObj X m) (tensorPowObj X n) (tensorPowObj X k) X
      simp only [← tensorHom_id, ← id_tensorHom] at h ⊢
      exact h
    rw [hPent] at ⊢
    rw [← Category.assoc
      (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k)) ⊗ₘ 𝟙 X)
      (associator (tensorPowObj X m ⊗ tensorPowObj X n)
        (tensorPowObj X k) X).hom
      (associator (tensorPowObj X m)
        (tensorPowObj X n)
        (tensorPowObj X k ⊗ X)).hom] at ⊢
    have hNat9 : (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k))
          ⊗ₘ 𝟙 X) ≫
        (associator (tensorPowObj X m ⊗ tensorPowObj X n)
          (tensorPowObj X k) X).hom =
        (associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom ≫
        ((tensorPowObj_add X m n).hom ⊗ₘ
          (𝟙 (tensorPowObj X k) ⊗ₘ 𝟙 X)) :=
      associator_naturality
        (tensorPowObj_add X m n).hom (𝟙 (tensorPowObj X k)) (𝟙 X)
    rw [hNat9] at ⊢
    simp only [id_tensorHom] at ⊢
    rw [← Category.assoc
      ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
      ((associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom ≫
      ((tensorPowObj_add X m n).hom ⊗ₘ
        (tensorPowObj X k ◁ 𝟙 X)))
      (associator (tensorPowObj X m)
        (tensorPowObj X n)
        (tensorPowObj X k ⊗ X)).hom] at ⊢
    rw [← Category.assoc
      ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
      (associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom
      ((tensorPowObj_add X m n).hom ⊗ₘ
        (tensorPowObj X k ◁ 𝟙 X))] at ⊢
    rw [Category.assoc
      ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
      (associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom
      ((tensorPowObj_add X m n).hom ⊗ₘ
        (tensorPowObj X k ◁ 𝟙 X))] at ⊢
    have hLast : (associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom ≫
        ((tensorPowObj_add X m n).hom ⊗ₘ (tensorPowObj X k ◁ 𝟙 X)) =
        (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k)) ⊗ₘ 𝟙 X) ≫
        (associator (tensorPowObj X m ⊗ tensorPowObj X n)
          (tensorPowObj X k) X).hom := by
      have h := (associator_naturality (tensorPowObj_add X m n).hom
        (𝟙 (tensorPowObj X k)) (𝟙 X)).symm
      have hBridge : (tensorPowObj X k ◁ 𝟙 X) =
          (𝟙 (tensorPowObj X k) ⊗ₘ 𝟙 X) := by simp
      rw [hBridge]
      exact h
    rw [hLast] at ⊢
    have hBridge2 : (𝟙 (tensorPowObj X k ⊗ X)) =
        (tensorPowObj X k ◁ 𝟙 X) := by simp
    conv_rhs =>
      rw [Category.assoc ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
        (associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom
        ((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k ⊗ X))]
      rw [hBridge2]
      rw [hLast]
      rw [← Category.assoc ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
        (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k)) ⊗ₘ 𝟙 X)
        (associator (tensorPowObj X m ⊗ tensorPowObj X n)
          (tensorPowObj X k) X).hom]
    rw [Category.assoc ((tensorPowObj_add X (m + n) k).hom ⊗ₘ 𝟙 X)
      (((tensorPowObj_add X m n).hom ⊗ₘ 𝟙 (tensorPowObj X k)) ⊗ₘ 𝟙 X)
      (associator (tensorPowObj X m ⊗ tensorPowObj X n)
        (tensorPowObj X k) X).hom] at ⊢

section LaxMonoidalImage

variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- The ordered multiplication on the lax-monoidal image of finite tensor
powers. -/
noncomputable def laxTensorPowerPairing (G : C ⥤ D) [G.LaxMonoidal]
    (X : C) (p q : ℕ) :
    G.obj (TensorPower.tensorPowObj X p) ⊗
        G.obj (TensorPower.tensorPowObj X q) ⟶
      G.obj (TensorPower.tensorPowObj X (p + q)) :=
  Functor.LaxMonoidal.μ G _ _ ≫
    G.map (TensorPower.tensorPowObj_add X p q).inv

/-- The lax unit into the image of the weight-zero tensor power. -/
noncomputable def laxTensorPowerUnit (G : C ⥤ D) [G.LaxMonoidal] (X : C) :
    𝟙_ D ⟶ G.obj (TensorPower.tensorPowObj X 0) :=
  Functor.LaxMonoidal.ε G

/-- Ordered tensor-power multiplication is natural in the base object. -/
theorem laxTensorPowerPairing_naturality (G : C ⥤ D) [G.LaxMonoidal]
    {X Y : C} (f : X ⟶ Y) (p q : ℕ) :
    (G.map (TensorPower.tensorPowMap f p) ⊗ₘ
        G.map (TensorPower.tensorPowMap f q)) ≫
        laxTensorPowerPairing G Y p q =
      laxTensorPowerPairing G X p q ≫
        G.map (TensorPower.tensorPowMap f (p + q)) := by
  unfold laxTensorPowerPairing
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Category.assoc, ← G.map_comp]
  congr 1
  apply congrArg G.map
  apply (cancel_mono (TensorPower.tensorPowObj_add Y p q).hom).mp
  simp [TensorPower.tensorPowObj_add_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The left unit law uses the lax unit map; no strong-monoidal unit
identification is assumed. -/
theorem laxTensorPowerPairing_zero_left (G : C ⥤ D) [G.LaxMonoidal]
    (X : C) (p : ℕ) :
    (laxTensorPowerUnit G X ▷ G.obj (TensorPower.tensorPowObj X p)) ≫
        laxTensorPowerPairing G X 0 p =
      (λ_ (G.obj (TensorPower.tensorPowObj X p))).hom ≫
        eqToHom (congrArg
          (fun n ↦ G.obj (TensorPower.tensorPowObj X n))
          (Nat.zero_add p).symm) := by
  have hAdd : (TensorPower.tensorPowObj_add X 0 p).inv =
      (λ_ (TensorPower.tensorPowObj X p)).hom ≫
        eqToHom (congrArg (TensorPower.tensorPowObj X)
          (Nat.zero_add p).symm) := by
    let e := eqToIso
      (congrArg (TensorPower.tensorPowObj X) (Nat.zero_add p))
    have h₁ : (λ_ (TensorPower.tensorPowObj X p)).hom =
        (TensorPower.tensorPowObj_add X 0 p).inv ≫ e.hom :=
      (Iso.eq_inv_comp (TensorPower.tensorPowObj_add X 0 p)).2
        (TensorPower.tensorPowObj_add_zero_left X p)
    exact ((Iso.comp_inv_eq e).2 h₁).symm
  change (Functor.LaxMonoidal.ε G ▷
      G.obj (TensorPower.tensorPowObj X p)) ≫
      Functor.LaxMonoidal.μ G (𝟙_ C) (TensorPower.tensorPowObj X p) ≫
      G.map (TensorPower.tensorPowObj_add X 0 p).inv = _
  rw [hAdd, G.map_comp]
  rw [← Functor.LaxMonoidal.left_unitality_assoc, eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
/-- The right unit law uses the lax unit map; weight `p + 0` reduces
definitionally to `p`. -/
theorem laxTensorPowerPairing_zero_right (G : C ⥤ D) [G.LaxMonoidal]
    (X : C) (p : ℕ) :
    (G.obj (TensorPower.tensorPowObj X p) ◁ laxTensorPowerUnit G X) ≫
        laxTensorPowerPairing G X p 0 =
      (ρ_ (G.obj (TensorPower.tensorPowObj X p))).hom := by
  change (G.obj (TensorPower.tensorPowObj X p) ◁
      Functor.LaxMonoidal.ε G) ≫
      Functor.LaxMonoidal.μ G (TensorPower.tensorPowObj X p) (𝟙_ C) ≫
      G.map (TensorPower.tensorPowObj_add X p 0).inv = _
  have hAdd : (TensorPower.tensorPowObj_add X p 0).inv =
      (ρ_ (TensorPower.tensorPowObj X p)).hom :=
    (Iso.inv_eq_inv (TensorPower.tensorPowObj_add X p 0)
      (ρ_ (TensorPower.tensorPowObj X p)).symm).2
        (TensorPower.tensorPowObj_add_zero_right X p)
  rw [hAdd]
  simpa only [← Category.assoc] using
      (Functor.LaxMonoidal.right_unitality G
        (TensorPower.tensorPowObj X p)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Ordered associativity of lax-monoidal tensor-power multiplication. -/
theorem laxTensorPowerPairing_assoc (G : C ⥤ D) [G.LaxMonoidal]
    (X : C) (p q r : ℕ) :
    (laxTensorPowerPairing G X p q ⊗ₘ
        𝟙 (G.obj (TensorPower.tensorPowObj X r))) ≫
        laxTensorPowerPairing G X (p + q) r ≫
        eqToHom (congrArg
          (fun n ↦ G.obj (TensorPower.tensorPowObj X n))
          (Nat.add_assoc p q r)) =
      (α_ (G.obj (TensorPower.tensorPowObj X p))
        (G.obj (TensorPower.tensorPowObj X q))
        (G.obj (TensorPower.tensorPowObj X r))).hom ≫
        (𝟙 (G.obj (TensorPower.tensorPowObj X p)) ⊗ₘ
          laxTensorPowerPairing G X q r) ≫
        laxTensorPowerPairing G X p (q + r) := by
  have hSourceIso :
      ((TensorPower.tensorPowObj_add X p q).inv ▷
          TensorPower.tensorPowObj X r) ≫
          (TensorPower.tensorPowObj_add X (p + q) r).inv ≫
          (eqToIso (congrArg (TensorPower.tensorPowObj X)
            (Nat.add_assoc p q r))).hom =
        (α_ (TensorPower.tensorPowObj X p)
          (TensorPower.tensorPowObj X q)
          (TensorPower.tensorPowObj X r)).hom ≫
          (TensorPower.tensorPowObj X p ◁
            (TensorPower.tensorPowObj_add X q r).inv) ≫
          (TensorPower.tensorPowObj_add X p (q + r)).inv := by
    apply (cancel_mono
      ((TensorPower.tensorPowObj_add X p (q + r)).hom ≫
        (𝟙 (TensorPower.tensorPowObj X p) ⊗ₘ
          (TensorPower.tensorPowObj_add X q r).hom))).mp
    simp only [Category.assoc]
    slice_lhs 3 5 =>
      rw [TensorPower.tensorPowObj_add_assoc X p q r]
    simp [id_tensorHom, tensorHom_id]
  have hSource :
      ((TensorPower.tensorPowObj_add X p q).inv ▷
          TensorPower.tensorPowObj X r) ≫
          (TensorPower.tensorPowObj_add X (p + q) r).inv ≫
          eqToHom (congrArg (TensorPower.tensorPowObj X)
            (Nat.add_assoc p q r)) =
        (α_ (TensorPower.tensorPowObj X p)
          (TensorPower.tensorPowObj X q)
          (TensorPower.tensorPowObj X r)).hom ≫
          (TensorPower.tensorPowObj X p ◁
            (TensorPower.tensorPowObj_add X q r).inv) ≫
          (TensorPower.tensorPowObj_add X p (q + r)).inv :=
    hSourceIso
  unfold laxTensorPowerPairing
  simp only [tensorHom_id, comp_whiskerRight, id_tensorHom,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← Functor.LaxMonoidal.associativity_assoc]
  rw [← eqToHom_map G
    (congrArg (TensorPower.tensorPowObj X) (Nat.add_assoc p q r))]
  simp only [← G.map_comp]
  rw [hSource]

end LaxMonoidalImage

end CategoryTheory.MonoidalCategory.TensorPower

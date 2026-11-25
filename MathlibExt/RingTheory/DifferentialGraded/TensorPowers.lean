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

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Finite tensor powers of cochain complexes

For `X : CochainComplex (ModuleCat R) ℤ` define the left-associated finite
power `tensorPowObj X n` (`0 ↦ unit`, `n+1 ↦ pow n ⊗ X`), functorial
`tensorPowMap`, and the finite add/coherence isomorphism
`pow (m + n) ≅ pow m ⊗ pow n`.

This is the finite prerequisite for coradical/augmentation-ideal filtrations.
It uses only binary `tensorObj`/`tensorHom`/`associator` plus the existing
`TensorHomFunctoriality` composition/identity/zero laws (binary `associator` only).
No infinite direct sum `⨁ₙ X^⊗n`, no tensor-coalgebra
carrier, no `ComonObj` deconcatenation, no cofree/free object or universal
property, no `IsConilpotent`/`IsComplete` predicate, no convolution
summability, no twisting bijection/adjunction, no totalization/EZ-AW, and no
derived/Koszul/operadic/model-category claim is provided here.

## Declaration inventory

* `tensorPowObj`: left-associated `n`-fold power.
* `tensorPowObj_zero` / `tensorPowObj_succ`: computation rules.
* `tensorPowMap`: functorial map by recursion via `tensorHom`.
* `tensorPowMap_zero` / `tensorPowMap_succ`: computation rules.
* `tensorPowMap_id` / `tensorPowMap_comp`: functoriality laws.
* `tensorPowFunctor`: the bundled weak-assumption DG power functor for each `n`.
* `tensorHom_zero` / `zero_tensorHom`: `CochainComplex` compatibility names
  delegating to the generic homological-complex tensor-zero laws.
* `tensorIsoRight`: lift an iso through `tensorObj - C` (helper, not a global
  instance).
* `tensorPowObj_add`: finite add/coherence iso by induction on `n`
  (base via `rightUnitor`, step via `tensorIsoRight` + `associator`).
* `tensorPowObj_add_zero_right` / `tensorPowObj_add_zero_left`: unit coherence
  (`rightUnitor` definitionally; `leftUnitor` by induction).
* `tensorPowObj_add_naturality`: the add iso commutes with `tensorPowMap`.
* `tensorPowObj_add_assoc`: the two `(m+n)+k` reassociation routes agree
  (by induction on `k` via `pentagon` + associator naturality).
* `tensorPowObj_eq_tensorPower`: under `AddCoherence`, the DG carrier agrees
  with generic `TensorPower.tensorPowObj` (by induction from the two recursion
  equations).
* `tensorPowObj_whisker_right` / `tensorPowObj_bridge_succ`: right-whiskered
  `eqToIso` transport and the `n + 1` bridge factorization.
* `tensorPowObj_add_bridge_hom` / `tensorPowObj_add_bridge_inv`: native and generic
  add isomorphisms commute with the original finite-power comparisons.
* `tensorPowObj_powMap_bridge` / `tensorPowObj_powMap_bridge_inv`: generic and
  DG power maps agree across the bridges (both orientations).

## Finite-support note

For fixed `n`, `tensorPowObj X n` is an `n`-fold binary iteration. The only
colimits are the binary `tensorObj` degree coproducts already assumed. This
is explicitly *not* `⨁ₙ X^⊗n`.

## Nonclaims

* No `down ℤ` API; everything is cohomological (`up ℤ` via `CochainComplex`).
* No new global instances are declared; every `HasTensor`/`HasGoodTensor`
  need is discharged by the six hypothesis families below.
* No infinite sums, (co)free objects, filtrations, completeness, or
  adjunction data.

## Specialization note

This file parallels the generic
`CategoryTheory.MonoidalCategory.TensorPower` API with the same left-associated
recursion convention and matching declaration names. The carrier/map layer
(`tensorPowObj`, `tensorPowMap`) and `tensorIsoRight` keep small direct
recursions using only the top-level binary `HasTensor` family; the generic
foundation instead needs the full `MonoidalCategory` instance, so heterogeneous
transport would add lines without removing duplication. The compatibility names
`tensorHom_zero` and `zero_tensorHom` delegate to the generic
`HomologicalComplex` laws. The add/naturality/associativity proofs likewise
retain their direct form for stable `rfl` computation behavior. Under the full
`AddCoherence` hypotheses, `tensorPowObj_eq_tensorPower` identifies the DG
carrier with the generic power by induction from the two public recursion
equations.

## Import justification

`Monoidal`/`Bifunctor`/`BifunctorAssociator`/`Preadditive` supply
`tensorUnit`/`tensorObj`/`tensorHom`/`associator`/`leftUnitor`/`rightUnitor`
and the graded hypotheses. `CoherenceLemmas` supplies `unitors_equal` for
the `0+n` base case, `leftUnitor_tensor_hom` for its step, and
`rightUnitor_tensor_inv` for the associativity base case.
`TensorHomFunctoriality` supplies `tensorHom_comp_tensorHom`,
`tensorHom_id_id`, and the generic `tensorHom_zero`/`zero_tensorHom` laws used
by the compatibility wrappers. `tensorPowObj_add` uses only the binary
`HomologicalComplex.associator`; `TripleTensor` tridegree lemmas are not
referenced here.
`ModuleCat.Basic` supplies `ModuleCat`/`CommRing`.
`TensorPowers` (generic) supplies `TensorPower.tensorPowObj` and its recursion
equations for the `tensorPowObj_eq_tensorPower` bridge.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]

/-- Left-associated finite tensor power: `0 ↦ unit`, `n+1 ↦ pow n ⊗ X`.
Matches the left-accumulating orientation of `reducedConvPow`. -/
noncomputable def tensorPowObj (X : CochainComplex (ModuleCat R) ℤ) :
    ℕ → CochainComplex (ModuleCat R) ℤ
  | 0 => HomologicalComplex.tensorUnit _ _
  | n + 1 => HomologicalComplex.tensorObj (tensorPowObj X n) X

/-- `tensorPowObj` at `0` is the tensor unit; left-associated base computation (`rfl`). -/
@[simp]
theorem tensorPowObj_zero (X : CochainComplex (ModuleCat R) ℤ) :
    tensorPowObj X 0 = HomologicalComplex.tensorUnit _ _ :=
  rfl

/-- `tensorPowObj` at `n+1` is `tensorObj (pow n) X`; left-associated step computation (`rfl`). -/
@[simp]
theorem tensorPowObj_succ (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    tensorPowObj X (n + 1) =
      HomologicalComplex.tensorObj (tensorPowObj X n) X :=
  rfl

/-- Functorial map on finite powers by recursion via `tensorHom`. -/
noncomputable def tensorPowMap {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : ∀ (n : ℕ), tensorPowObj X n ⟶ tensorPowObj Y n
  | 0 => 𝟙 _
  | n + 1 => HomologicalComplex.tensorHom (tensorPowMap f n) f

/-- Functorial map at `0` is the identity on the tensor unit (`rfl`). -/
@[simp]
theorem tensorPowMap_zero {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : tensorPowMap f 0 = 𝟙 _ :=
  rfl

/-- Functorial map at `n+1` is `tensorHom` of the `n`-th map and `f` (`rfl`). -/
@[simp]
theorem tensorPowMap_succ {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) =
      HomologicalComplex.tensorHom (tensorPowMap f n) f :=
  rfl

/-- Identity law for the functorial power map, by induction using `tensorHom_id_id`. -/
@[simp]
theorem tensorPowMap_id (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    tensorPowMap (𝟙 X) n = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change HomologicalComplex.tensorHom (tensorPowMap (𝟙 X) n) (𝟙 X) = 𝟙 _
    rw [ih]
    exact HomologicalComplex.tensorHom_id_id _ _

/-- Composition law for the functorial power map, by induction using `tensorHom_comp_tensorHom`. -/
theorem tensorPowMap_comp {X Y Z : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    tensorPowMap (f ≫ g) n = tensorPowMap f n ≫ tensorPowMap g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change HomologicalComplex.tensorHom (tensorPowMap (f ≫ g) n) (f ≫ g) =
      HomologicalComplex.tensorHom (tensorPowMap f n) f ≫
        HomologicalComplex.tensorHom (tensorPowMap g n) g
    rw [ih]
    exact (HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _).symm

/-- The `n`-fold DG tensor power as a functor of its base complex. -/
noncomputable def tensorPowFunctor (n : ℕ) :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R) ℤ where
  obj X := tensorPowObj X n
  map f := tensorPowMap f n
  map_id X := tensorPowMap_id X n
  map_comp f g := tensorPowMap_comp f g n

@[simp]
theorem tensorPowFunctor_obj (n : ℕ) (X : CochainComplex (ModuleCat R) ℤ) :
    (tensorPowFunctor n).obj X = tensorPowObj X n :=
  rfl

@[simp]
theorem tensorPowFunctor_map (n : ℕ) {X Y : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Y) : (tensorPowFunctor n).map f = tensorPowMap f n :=
  rfl

/-- Lift an iso through `tensorObj - C` on the right. Helper only; not a
global instance. -/
noncomputable def tensorIsoRight
    {A B C : CochainComplex (ModuleCat R) ℤ} (e : A ≅ B) :
    HomologicalComplex.tensorObj A C ≅ HomologicalComplex.tensorObj B C where
  hom := HomologicalComplex.tensorHom e.hom (𝟙 C)
  inv := HomologicalComplex.tensorHom e.inv (𝟙 C)
  hom_inv_id := by
    rw [HomologicalComplex.tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Iso.hom_inv_id,
      CategoryTheory.Category.id_comp, HomologicalComplex.tensorHom_id_id]
  inv_hom_id := by
    rw [HomologicalComplex.tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.id_comp, HomologicalComplex.tensorHom_id_id]

/-- `tensorHom` with zero on the right vanishes, specialized from the generic
homological-complex tensor-zero law. -/
theorem tensorHom_zero {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat R) ℤ}
    (f : K₁ ⟶ L₁) :
    HomologicalComplex.tensorHom f (0 : K₂ ⟶ L₂) = 0 := by
  exact HomologicalComplex.tensorHom_zero f

/-- `tensorHom` with zero on the left vanishes, specialized from the generic
homological-complex tensor-zero law. -/
theorem zero_tensorHom {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat R) ℤ}
    (g : K₂ ⟶ L₂) :
    HomologicalComplex.tensorHom (0 : K₁ ⟶ L₁) g = 0 := by
  exact HomologicalComplex.zero_tensorHom g

section AddCoherence

variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Finite add/coherence iso: `pow (m + n) ≅ pow m ⊗ pow n` by induction on
`n` (base via `rightUnitor`, step via `tensorIsoRight` + `associator`). -/
@[nolint defsWithUnderscore]
noncomputable def tensorPowObj_add (X : CochainComplex (ModuleCat R) ℤ)
    (m : ℕ) : ∀ (n : ℕ),
    tensorPowObj X (m + n) ≅
      HomologicalComplex.tensorObj (tensorPowObj X m) (tensorPowObj X n)
  | 0 =>
    eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m)) ≪≫
      (HomologicalComplex.rightUnitor _).symm
  | n + 1 =>
    eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n)) ≪≫
      (tensorIsoRight (tensorPowObj_add X m n)) ≪≫
        HomologicalComplex.associator _ _ _

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- Right-unit coherence for the add iso at `n = 0`: the hom is `eqToIso`
then `rightUnitor.symm` (`rfl`). -/
theorem tensorPowObj_add_zero_right
    (X : CochainComplex (ModuleCat R) ℤ) (m : ℕ) :
    (tensorPowObj_add X m 0).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m))).hom ≫
        (HomologicalComplex.rightUnitor _).symm.hom :=
  rfl

/-- Left-unit coherence for the add iso at `m = 0`, by induction using `unitors_equal`
and `leftUnitor_tensor_hom`. -/
theorem tensorPowObj_add_zero_left
    (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    (tensorPowObj_add X 0 n).hom ≫
        (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := by
  induction n with
  | zero =>
    have hR : (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero 0))).hom
        = 𝟙 _ := rfl
    rw [tensorPowObj_add_zero_right, hR,
      CategoryTheory.Category.id_comp] at ⊢
    change (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).inv ≫
        (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom =
      𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
    have hLU : HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
        CategoryTheory.MonoidalCategory.leftUnitor _ := rfl
    have hRU : HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
        CategoryTheory.MonoidalCategory.rightUnitor _ := rfl
    have hUE : (CategoryTheory.MonoidalCategory.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom =
        (CategoryTheory.MonoidalCategory.rightUnitor
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))).hom :=
      CategoryTheory.MonoidalCategory.unitors_equal
    rw [hLU, hRU, hUE, CategoryTheory.Iso.inv_hom_id]
  | succ n ih =>
    have hY0 : (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ 0 n))).hom
        = 𝟙 _ := rfl
    have hAdd : (tensorPowObj_add X 0 (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ 0 n))).hom ≫
          (tensorIsoRight (tensorPowObj_add X 0 n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X 0)
            (tensorPowObj X n) X).hom := rfl
    have hIso : (tensorIsoRight (tensorPowObj_add X 0 n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add X 0 n).hom (𝟙 X) := rfl
    rw [hAdd, hIso, hY0, CategoryTheory.Category.id_comp] at ⊢
    have hP0 : tensorPowObj X 0 =
        HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ) := rfl
    have hObj : HomologicalComplex.tensorObj (tensorPowObj X 0)
          (tensorPowObj X n) =
        HomologicalComplex.tensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) :=
      congrArg
        (fun U => HomologicalComplex.tensorObj U (tensorPowObj X n)) hP0
    let a2 : tensorPowObj X (0 + n) ⟶
        HomologicalComplex.tensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) := Eq.mpr
      (congrArg (fun U => tensorPowObj X (0 + n) ⟶
        HomologicalComplex.tensorObj U (tensorPowObj X n)) hP0)
      (tensorPowObj_add X 0 n).hom
    change HomologicalComplex.tensorHom a2 (𝟙 X) ≫
        (HomologicalComplex.associator
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) X).hom ≫
        (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X n) X)).hom =
      (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add (n + 1)))).hom
    have hTri := CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom
      (tensorPowObj X n) X
    have hTri' : (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X n) X)).hom =
        (HomologicalComplex.associator
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          (tensorPowObj X n) X).inv ≫
        HomologicalComplex.tensorHom
          (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom (𝟙 X) := hTri
    have ih_t : a2 ≫
          (HomologicalComplex.leftUnitor (tensorPowObj X n)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add n))).hom := ih
    rw [hTri', CategoryTheory.Iso.hom_inv_id_assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id, ih_t] at ⊢
    have gen : ∀ {a b : ℕ} (h : a = b),
        HomologicalComplex.tensorHom
          (eqToIso (congrArg (tensorPowObj X) h)).hom (𝟙 X) =
        (eqToIso (congrArg
          (fun k => HomologicalComplex.tensorObj (tensorPowObj X k) X) h)).hom := by
      intro a b h
      cases h
      simp [HomologicalComplex.tensorHom_id_id]
    rw [gen (Nat.zero_add n)] at ⊢
    have hD : Nat.zero_add (n + 1) = congrArg Nat.succ (Nat.zero_add n) :=
      rfl
    rw [hD] at ⊢
    rfl

/-- Naturality of the add iso in the base map, by induction using `rightUnitor_naturality`
and `associator_naturality`. -/
theorem tensorPowObj_add_naturality
    {X Y : CochainComplex (ModuleCat R) ℤ} (f : X ⟶ Y) (m n : ℕ) :
    tensorPowMap f (m + n) ≫ (tensorPowObj_add Y m n).hom =
      (tensorPowObj_add X m n).hom ≫
        HomologicalComplex.tensorHom (tensorPowMap f m) (tensorPowMap f n) := by
  induction n generalizing m with
  | zero =>
    have hY : (eqToIso (congrArg (tensorPowObj Y) (Nat.add_zero m))).hom
        = 𝟙 _ := rfl
    have hX : (eqToIso (congrArg (tensorPowObj X) (Nat.add_zero m))).hom
        = 𝟙 _ := rfl
    rw [tensorPowObj_add_zero_right, tensorPowObj_add_zero_right,
      hY, hX, CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]
    change tensorPowMap f m ≫ (HomologicalComplex.rightUnitor _).inv =
      (HomologicalComplex.rightUnitor _).inv ≫
        HomologicalComplex.tensorHom (tensorPowMap f m) (𝟙 _)
    have h := CategoryTheory.MonoidalCategory.rightUnitor_naturality
      (tensorPowMap f m)
    have h' : HomologicalComplex.tensorHom (tensorPowMap f m) (𝟙 _) ≫
        (HomologicalComplex.rightUnitor _).hom =
        (HomologicalComplex.rightUnitor _).hom ≫ tensorPowMap f m := h
    rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, h',
      ← CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.id_comp]
  | succ n ih =>
    have hMap : tensorPowMap f (m + (n + 1)) =
        HomologicalComplex.tensorHom (tensorPowMap f (m + n)) f := rfl
    have hMapN : tensorPowMap f (n + 1) =
        HomologicalComplex.tensorHom (tensorPowMap f n) f := rfl
    have hY0 : (eqToIso (congrArg (tensorPowObj Y) (Nat.add_succ m n))).hom
        = 𝟙 _ := rfl
    have hX0 : (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n))).hom
        = 𝟙 _ := rfl
    have hAddY : (tensorPowObj_add Y m (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj Y) (Nat.add_succ m n))).hom ≫
          (tensorIsoRight (tensorPowObj_add Y m n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom := rfl
    have hAddX : (tensorPowObj_add X m (n + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X) (Nat.add_succ m n))).hom ≫
          (tensorIsoRight (tensorPowObj_add X m n)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) X).hom := rfl
    have hIsoY : (tensorIsoRight (tensorPowObj_add Y m n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add Y m n).hom (𝟙 Y) := rfl
    have hIsoX : (tensorIsoRight (tensorPowObj_add X m n)).hom =
        HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom (𝟙 X) := rfl
    rw [hMap, hAddY, hAddX, hIsoY, hIsoX, hY0, hX0,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp, hMapN]
    change HomologicalComplex.tensorHom (tensorPowMap f (m + n)) f ≫
        (HomologicalComplex.tensorHom (tensorPowObj_add Y m n).hom (𝟙 Y) ≫
          (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom) =
      (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n) X).hom) ≫
        HomologicalComplex.tensorHom (tensorPowMap f m)
          (HomologicalComplex.tensorHom (tensorPowMap f n) f)
    have hNat := CategoryTheory.MonoidalCategory.associator_naturality
      (tensorPowMap f m) (tensorPowMap f n) f
    have hNat' : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (tensorPowMap f m) (tensorPowMap f n))
          f ≫ (HomologicalComplex.associator (tensorPowObj Y m)
            (tensorPowObj Y n) Y).hom =
        (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) X).hom ≫
          HomologicalComplex.tensorHom (tensorPowMap f m)
            (HomologicalComplex.tensorHom (tensorPowMap f n) f) := hNat
    simp only [← CategoryTheory.Category.assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id, ih] at ⊢
    nth_rewrite 3 [← CategoryTheory.Category.id_comp f] at ⊢
    rw [← HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.assoc, hNat',
      ← CategoryTheory.Category.assoc] at ⊢

/-- Associativity coherence of the add iso, by induction on `k` via `pentagon`,
associator naturality, and `rightUnitor_tensor_inv`. -/
theorem tensorPowObj_add_assoc
    (X : CochainComplex (ModuleCat R) ℤ) (m n k : ℕ) :
    (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
        (tensorPowObj_add X m (n + k)).hom ≫
        HomologicalComplex.tensorHom (𝟙 _)
          ((tensorPowObj_add X n k).hom) =
      (tensorPowObj_add X (m + n) k).hom ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator _ _ _).hom := by
  induction k with
  | zero =>
    have hr : (m + n) + 0 = m + (n + 0) := rfl
    have hAeq : Nat.add_assoc m n 0 = hr := rfl
    rw [hAeq] at ⊢
    have hA1 : (eqToIso (congrArg (tensorPowObj X) hr)).hom = 𝟙 _ := rfl
    rw [hA1, CategoryTheory.Category.id_comp] at ⊢
    have hN0 : (tensorPowObj_add X m (n + 0)).hom =
        (tensorPowObj_add X m n).hom := rfl
    rw [hN0] at ⊢
    have hR1 : (tensorPowObj_add X n 0).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj X n)).symm.hom := by
      rw [tensorPowObj_add_zero_right]
      have h1 : (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_zero n))).hom = 𝟙 _ := rfl
      rw [h1, CategoryTheory.Category.id_comp]
    have hR2 : (tensorPowObj_add X (m + n) 0).hom =
        (HomologicalComplex.rightUnitor
          (tensorPowObj X (m + n))).symm.hom := by
      rw [tensorPowObj_add_zero_right]
      have h2 : (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_zero (m + n)))).hom = 𝟙 _ := rfl
      rw [h2, CategoryTheory.Category.id_comp]
    rw [hR1, hR2] at ⊢
    change (tensorPowObj_add X m n).hom ≫
        HomologicalComplex.tensorHom (𝟙 _)
          (HomologicalComplex.rightUnitor (tensorPowObj X n)).inv =
      (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))).inv ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorUnit (ModuleCat R)
            (ComplexShape.up ℤ))).hom
    have hTinv0 := CategoryTheory.MonoidalCategory.rightUnitor_tensor_inv
      (tensorPowObj X m) (tensorPowObj X n)
    have hTinv : (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).inv =
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.rightUnitor (tensorPowObj X n)).inv ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorUnit (ModuleCat R)
            (ComplexShape.up ℤ))).inv := hTinv0
    have hNat := CategoryTheory.MonoidalCategory.rightUnitor_naturality
      (tensorPowObj_add X m n).hom
    have hNat' : HomologicalComplex.tensorHom
          ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).hom =
        (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))).hom ≫
          (tensorPowObj_add X m n).hom := hNat
    have hVW : (HomologicalComplex.rightUnitor
          (tensorPowObj X (m + n))).inv ≫
        HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom) (𝟙 _) =
        (tensorPowObj_add X m n).hom ≫
        (HomologicalComplex.rightUnitor
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n))).inv := by
      have h1 : (HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).hom ≫
          ((HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).inv ≫
          HomologicalComplex.tensorHom ((tensorPowObj_add X m n).hom)
            (𝟙 _)) =
          (HomologicalComplex.rightUnitor
            (tensorPowObj X (m + n))).hom ≫
          ((tensorPowObj_add X m n).hom ≫
          (HomologicalComplex.rightUnitor
            (HomologicalComplex.tensorObj (tensorPowObj X m)
              (tensorPowObj X n))).inv) := by
        rw [← CategoryTheory.Category.assoc,
          CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.id_comp,
          ← CategoryTheory.Category.assoc, ← hNat',
          CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id,
          CategoryTheory.Category.comp_id]
      exact (CategoryTheory.Iso.cancel_iso_hom_left
        (HomologicalComplex.rightUnitor (tensorPowObj X (m + n))) _ _).mp h1
    rw [← CategoryTheory.Category.assoc, hVW,
      CategoryTheory.Category.assoc, hTinv,
      CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
      CategoryTheory.Category.comp_id] at ⊢
  | succ k ih =>
    have hS1 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ m (n + k)))).hom = 𝟙 _ := rfl
    have hS2 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ n k))).hom = 𝟙 _ := rfl
    have hS3 : (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_succ (m + n) k))).hom = 𝟙 _ := rfl
    have hAddR : (tensorPowObj_add X (m + n) (k + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ (m + n) k))).hom ≫
          (tensorIsoRight (tensorPowObj_add X (m + n) k)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X (m + n))
            (tensorPowObj X k) X).hom := rfl
    have hAddM : (tensorPowObj_add X m (n + (k + 1))).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ m (n + k)))).hom ≫
          (tensorIsoRight (tensorPowObj_add X m (n + k))).hom ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom := rfl
    have hAddN : (tensorPowObj_add X n (k + 1)).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_succ n k))).hom ≫
          (tensorIsoRight (tensorPowObj_add X n k)).hom ≫
          (HomologicalComplex.associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom := rfl
    have hIsoR : (tensorIsoRight
        (tensorPowObj_add X (m + n) k)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X (m + n) k).hom (𝟙 X) := rfl
    have hIsoM : (tensorIsoRight
        (tensorPowObj_add X m (n + k))).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X m (n + k)).hom (𝟙 X) := rfl
    have hIsoN : (tensorIsoRight (tensorPowObj_add X n k)).hom =
        HomologicalComplex.tensorHom
          (tensorPowObj_add X n k).hom (𝟙 X) := rfl
    have hD : Nat.add_assoc m n (k + 1) =
        congrArg Nat.succ (Nat.add_assoc m n k) := rfl
    rw [hD] at ⊢
    rw [hAddR, hAddM, hAddN, hIsoR, hIsoM, hIsoN,
      hS1, hS2, hS3, CategoryTheory.Category.id_comp,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp] at ⊢
    change (eqToIso (congrArg (fun j => HomologicalComplex.tensorObj
            (tensorPowObj X j) X) (Nat.add_assoc m n k))).hom ≫
          (HomologicalComplex.tensorHom
            (tensorPowObj_add X m (n + k)).hom (𝟙 X) ≫
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X (n + k)) X).hom) ≫
          HomologicalComplex.tensorHom (𝟙 _)
            (HomologicalComplex.tensorHom
              (tensorPowObj_add X n k).hom (𝟙 X) ≫
            (HomologicalComplex.associator (tensorPowObj X n)
              (tensorPowObj X k) X).hom) =
        (HomologicalComplex.tensorHom
          (tensorPowObj_add X (m + n) k).hom (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom) ≫
        HomologicalComplex.tensorHom
          ((tensorPowObj_add X m n).hom) (𝟙 _) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom
    have genX : ∀ {a b : ℕ} (h : a = b),
        HomologicalComplex.tensorHom
          (eqToIso (congrArg (tensorPowObj X) h)).hom (𝟙 X) =
        (eqToIso (congrArg
          (fun k => HomologicalComplex.tensorObj (tensorPowObj X k) X) h)).hom := by
      intro a b h
      cases h
      simp [HomologicalComplex.tensorHom_id_id]
    rw [← genX (Nat.add_assoc m n k)] at ⊢
    simp only [← CategoryTheory.Category.assoc,
      HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id] at ⊢
    have e1 : (𝟙 (tensorPowObj X m)) =
        𝟙 (tensorPowObj X m) ≫ 𝟙 (tensorPowObj X m) :=
      (CategoryTheory.Category.id_comp _).symm
    rw [e1] at ⊢
    rw [← HomologicalComplex.tensorHom_comp_tensorHom] at ⊢
    have hNat3MC := CategoryTheory.MonoidalCategory.associator_naturality
      (𝟙 (tensorPowObj X m)) (tensorPowObj_add X n k).hom (𝟙 X)
    have hNat3 : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
            (tensorPowObj_add X n k).hom) (𝟙 X) ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (HomologicalComplex.tensorObj (tensorPowObj X n)
            (tensorPowObj X k)) X).hom =
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X (n + k)) X).hom ≫
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom
            (𝟙 X)) := hNat3MC
    rw [CategoryTheory.Category.assoc _ _
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom (𝟙 X)) ≫
      HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X (n + k)) X).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.tensorHom (tensorPowObj_add X n k).hom (𝟙 X)))
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← hNat3] at ⊢
    rw [CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (tensorPowObj_add X n k).hom) (𝟙 X))
      (HomologicalComplex.associator (tensorPowObj X m)
        (HomologicalComplex.tensorObj (tensorPowObj X n)
          (tensorPowObj X k)) X).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        ((eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom ≫
          (tensorPowObj_add X m (n + k)).hom) (𝟙 X))
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (tensorPowObj_add X n k).hom) (𝟙 X))
      ((HomologicalComplex.associator (tensorPowObj X m)
        (HomologicalComplex.tensorObj (tensorPowObj X n)
          (tensorPowObj X k)) X).hom ≫
      HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (HomologicalComplex.associator (tensorPowObj X n)
          (tensorPowObj X k) X).hom)] at ⊢
    rw [HomologicalComplex.tensorHom_comp_tensorHom,
      CategoryTheory.Category.comp_id] at ⊢
    rw [CategoryTheory.Category.assoc
      (eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc m n k))).hom
      (tensorPowObj_add X m (n + k)).hom
      (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
        (tensorPowObj_add X n k).hom)] at ⊢
    rw [ih] at ⊢
    have e2 : (𝟙 X) = 𝟙 X ≫ 𝟙 X :=
      (CategoryTheory.Category.id_comp _).symm
    conv_lhs =>
      rw [e2, ← HomologicalComplex.tensorHom_comp_tensorHom]
    conv_lhs =>
      rw [e2, ← HomologicalComplex.tensorHom_comp_tensorHom,
        CategoryTheory.Category.comp_id]
    rw [CategoryTheory.Category.assoc] at ⊢
    rw [CategoryTheory.Category.assoc] at ⊢
    have hPentMC := CategoryTheory.MonoidalCategory.pentagon
      (tensorPowObj X m) (tensorPowObj X n) (tensorPowObj X k) X
    have hPent : HomologicalComplex.tensorHom
          (HomologicalComplex.associator (tensorPowObj X m)
            (tensorPowObj X n) (tensorPowObj X k)).hom (𝟙 X) ≫
        ((HomologicalComplex.associator (tensorPowObj X m)
          (HomologicalComplex.tensorObj (tensorPowObj X n)
            (tensorPowObj X k)) X).hom ≫
        HomologicalComplex.tensorHom (𝟙 (tensorPowObj X m))
          (HomologicalComplex.associator (tensorPowObj X n)
            (tensorPowObj X k) X).hom) =
        (HomologicalComplex.associator
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n)) (tensorPowObj X k) X).hom ≫
        (HomologicalComplex.associator (tensorPowObj X m)
          (tensorPowObj X n)
          (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom := hPentMC
    rw [hPent] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
          (𝟙 (tensorPowObj X k))) (𝟙 X))
      (HomologicalComplex.associator
        (HomologicalComplex.tensorObj (tensorPowObj X m)
          (tensorPowObj X n)) (tensorPowObj X k) X).hom
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X n)
        (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom] at ⊢
    have hNat9MC := CategoryTheory.MonoidalCategory.associator_naturality
      (tensorPowObj_add X m n).hom (𝟙 (tensorPowObj X k)) (𝟙 X)
    have hNat9 : HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
            (𝟙 (tensorPowObj X k))) (𝟙 X) ≫
        (HomologicalComplex.associator
          (HomologicalComplex.tensorObj (tensorPowObj X m)
            (tensorPowObj X n)) (tensorPowObj X k) X).hom =
        (HomologicalComplex.associator (tensorPowObj X (m + n))
          (tensorPowObj X k) X).hom ≫
        HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
          (HomologicalComplex.tensorHom (𝟙 (tensorPowObj X k))
            (𝟙 X)) := hNat9MC
    rw [hNat9] at ⊢
    rw [HomologicalComplex.tensorHom_id_id] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom (tensorPowObj_add X (m + n) k).hom
        (𝟙 X))
      ((HomologicalComplex.associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom ≫
      HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
        (𝟙 (HomologicalComplex.tensorObj (tensorPowObj X k) X)))
      (HomologicalComplex.associator (tensorPowObj X m)
        (tensorPowObj X n)
        (HomologicalComplex.tensorObj (tensorPowObj X k) X)).hom] at ⊢
    rw [← CategoryTheory.Category.assoc
      (HomologicalComplex.tensorHom (tensorPowObj_add X (m + n) k).hom
        (𝟙 X))
      (HomologicalComplex.associator (tensorPowObj X (m + n))
        (tensorPowObj X k) X).hom
      (HomologicalComplex.tensorHom (tensorPowObj_add X m n).hom
        (𝟙 (HomologicalComplex.tensorObj (tensorPowObj X k) X)))] at ⊢

-- Instance propagation: each recursion step finds its binary/ternary needs
-- from the six hypothesis families above. A missing pinned instance surfaces
-- here as a named blocker rather than a synthesized substitute.

/-- Under the full coherence hypotheses, the DG carrier agrees with the generic
`TensorPower` power, by induction from the two public recursion equations.
This is the DG-to-generic orientation: the weak direct carrier/map layer above
is retained, and only the carrier identification is transported. -/
theorem tensorPowObj_eq_tensorPower (X : CochainComplex (ModuleCat R) ℤ)
    (n : ℕ) :
    tensorPowObj X n =
      CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tensorPowObj_succ,
      CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_succ, ih]
    rfl

omit [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)]
  [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] in
/-- Right whiskering commutes with `eqToIso` transport, generalized over a
free equation so `cases` applies. Shared by the insertion-lane bridge
arguments (carrier Leibniz and insertion naturality). -/
theorem tensorPowObj_whisker_right
    {X : CochainComplex (ModuleCat R) ℤ}
    {A B : CochainComplex (ModuleCat R) ℤ} (e : A = B) :
    (eqToIso (congrArg (fun Y => HomologicalComplex.tensorObj Y X) e)).hom =
      HomologicalComplex.tensorHom (eqToIso e).hom (𝟙 X) := by
  cases e
  simp [HomologicalComplex.tensorHom_id_id]

/-- The DG-to-generic power bridge at `n + 1` is the bridge at `n`
right-whiskered. The two index equations agree by proof irrelevance
(definitionally equal ends). -/
theorem tensorPowObj_bridge_succ
    (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    (eqToIso (tensorPowObj_eq_tensorPower X (n + 1))).hom =
      HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) := by
  have hEq : tensorPowObj_eq_tensorPower X (n + 1) =
      congrArg (fun Y => HomologicalComplex.tensorObj Y X)
        (tensorPowObj_eq_tensorPower X n) := proof_irrel _ _
  rw [hEq]
  exact tensorPowObj_whisker_right (tensorPowObj_eq_tensorPower X n)

/-- Generic and DG power maps agree across the bridges: bridge, then generic
map, equals DG map, then bridge. By induction from the whiskered bridge. -/
theorem tensorPowObj_powMap_bridge
    {X Y : CochainComplex (ModuleCat R) ℤ} (g : X ⟶ Y) (n : ℕ) :
    (eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
        CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n =
      tensorPowMap g n ≫
        (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom := by
  induction n with
  | zero =>
      have hbX : (eqToIso (tensorPowObj_eq_tensorPower X 0)).hom =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have hbY : (eqToIso (tensorPowObj_eq_tensorPower Y 0)).hom =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have zG : CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g 0 =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have zD : tensorPowMap g 0 =
          𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) :=
        rfl
      have cL : (eqToIso (tensorPowObj_eq_tensorPower X 0)).hom ≫
              CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g 0 =
            𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) := by
        rw [hbX, zG]
        exact Category.comp_id _
      have cR : 𝟙 (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) =
            tensorPowMap g 0 ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y 0)).hom := by
        rw [zD, hbY]
        exact (Category.id_comp _).symm
      exact cL.trans cR
  | succ n ih =>
      have hGen : CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g
            (n + 1) =
          HomologicalComplex.tensorHom
            (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
            g := rfl
      have hDG : tensorPowMap g (n + 1) =
          HomologicalComplex.tensorHom (tensorPowMap g n) g :=
        tensorPowMap_succ g n
      have cL : (eqToIso (tensorPowObj_eq_tensorPower X (n + 1))).hom ≫
              CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g (n + 1) =
            HomologicalComplex.tensorHom
              ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
              (𝟙 X ≫ g) := by
        have e1 := congrArg (fun b => b ≫
          CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g (n + 1))
          (tensorPowObj_bridge_succ X n)
        have e2 := congrArg (fun m => HomologicalComplex.tensorHom
          (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) ≫ m) hGen
        have e3 : HomologicalComplex.tensorHom
                (eqToIso (tensorPowObj_eq_tensorPower X n)).hom (𝟙 X) ≫
                HomologicalComplex.tensorHom
                  (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
                  g =
              HomologicalComplex.tensorHom
                ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                  CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
                (𝟙 X ≫ g) :=
          HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _
        exact e1.trans (e2.trans e3)
      have cM : HomologicalComplex.tensorHom
              ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
                CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n)
              (𝟙 X ≫ g) =
            HomologicalComplex.tensorHom
              (tensorPowMap g n ≫
                (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g := by
        rw [ih, Category.id_comp]
      have cR : HomologicalComplex.tensorHom
              (tensorPowMap g n ≫
                (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g =
            tensorPowMap g (n + 1) ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y (n + 1))).hom := by
        have e0 : HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) g =
              HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom)
                (g ≫ 𝟙 Y) := by
          rw [Category.comp_id]
        have e1 : HomologicalComplex.tensorHom
                (tensorPowMap g n ≫
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom)
                (g ≫ 𝟙 Y) =
              HomologicalComplex.tensorHom (tensorPowMap g n) g ≫
                HomologicalComplex.tensorHom
                  (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom (𝟙 Y) :=
          (HomologicalComplex.tensorHom_comp_tensorHom _ _ _ _).symm
        have e2 := congrArg (fun m => m ≫
          HomologicalComplex.tensorHom
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom (𝟙 Y)) hDG
        have e3 := congrArg (fun b => tensorPowMap g (n + 1) ≫ b)
          (tensorPowObj_bridge_succ Y n)
        exact e0.trans (e1.trans (e2.symm.trans e3.symm))
      exact cL.trans (cM.trans cR)

/-- Inverse form of the bridge/map agreement, by iso cancellation. -/
theorem tensorPowObj_powMap_bridge_inv
    {X Y : CochainComplex (ModuleCat R) ℤ} (g : X ⟶ Y) (n : ℕ) :
    CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
        (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv =
      (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
        tensorPowMap g n := by
  have h := tensorPowObj_powMap_bridge g n
  calc CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
          (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv
      = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
            (CategoryTheory.MonoidalCategory.TensorPower.tensorPowMap g n ≫
              (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv)) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          ((tensorPowMap g n ≫
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).hom) ≫
            (eqToIso (tensorPowObj_eq_tensorPower Y n)).inv) := by
        rw [← Category.assoc ((eqToIso (tensorPowObj_eq_tensorPower X n)).hom),
          h]
    _ = (eqToIso (tensorPowObj_eq_tensorPower X n)).inv ≫
          tensorPowMap g n := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

example (X : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    HomologicalComplex.HasTensor (tensorPowObj X n) X :=
  inferInstance

example (X : CochainComplex (ModuleCat R) ℤ) (m n : ℕ) :
    HomologicalComplex.HasGoodTensor₁₂
      (tensorPowObj X m) (tensorPowObj X n) X :=
  inferInstance

example (X : CochainComplex (ModuleCat R) ℤ) (m n : ℕ) :
    HomologicalComplex.HasGoodTensor₂₃
      (tensorPowObj X m) (tensorPowObj X n) X :=
  inferInstance

end AddCoherence

end CochainComplex

namespace CochainComplex

universe u
variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- Splitting a native word commutes with its original generic tensor-power comparisons. -/
theorem tensorPowObj_add_bridge_hom
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℕ) :
    (tensorPowObj_add X m n).hom ≫
      HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom =
    (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom ≫
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_add X m n).hom := by
  induction n with
  | zero =>
    change (ρ_ (tensorPowObj X m)).inv ≫
        ((eqToIso (tensorPowObj_eq_tensorPower X m)).hom ⊗ₘ 𝟙 _) =
      (eqToIso (tensorPowObj_eq_tensorPower X m)).hom ≫
        (ρ_ (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X m)).inv
    exact (rightUnitor_inv_naturality (eqToIso (tensorPowObj_eq_tensorPower X m)).hom).symm
  | succ n ih =>
    let N := tensorPowObj_add X m n
    let A := CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_add X m n
    let Bm := eqToIso (tensorPowObj_eq_tensorPower X m)
    let Bn := eqToIso (tensorPowObj_eq_tensorPower X n)
    let Bsum := eqToIso (tensorPowObj_eq_tensorPower X (m + n))
    let αN := HomologicalComplex.associator (tensorPowObj X m) (tensorPowObj X n) X
    let αA := HomologicalComplex.associator
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X m)
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj X n) X
    have hN : (tensorPowObj_add X m (n + 1)).hom =
        HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom := by rfl
    have hA : (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_add X m (n + 1)).hom =
        HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom := by rfl
    rw [hN, hA]
    simp only [tensorPowObj_bridge_succ]
    change (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom) ≫
        HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
      HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
        (HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom)
    have hNat : αN.hom ≫
        HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
      HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫ αA.hom :=
      (associator_naturality Bm.hom Bn.hom (𝟙 X)).symm
    have hCompN : HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
        HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) =
      HomologicalComplex.tensorHom (N.hom ≫ HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id]
    have hCompA : HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
        HomologicalComplex.tensorHom A.hom (𝟙 X) =
      HomologicalComplex.tensorHom (Bsum.hom ≫ A.hom) (𝟙 X) := by
      rw [HomologicalComplex.tensorHom_comp_tensorHom, Category.comp_id]
    calc
      (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ αN.hom) ≫
          HomologicalComplex.tensorHom Bm.hom (HomologicalComplex.tensorHom Bn.hom (𝟙 X)) =
        HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          (αN.hom ≫ HomologicalComplex.tensorHom Bm.hom
            (HomologicalComplex.tensorHom Bn.hom (𝟙 X))) := Category.assoc _ _ _
      _ = HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          (HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫ αA.hom) :=
        congrArg (fun f => HomologicalComplex.tensorHom N.hom (𝟙 X) ≫ f) hNat
      _ = (HomologicalComplex.tensorHom N.hom (𝟙 X) ≫
          HomologicalComplex.tensorHom (HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X)) ≫ αA.hom :=
        (Category.assoc _ _ _).symm
      _ = HomologicalComplex.tensorHom
          (N.hom ≫ HomologicalComplex.tensorHom Bm.hom Bn.hom) (𝟙 X) ≫ αA.hom :=
        congrArg (fun f => f ≫ αA.hom) hCompN
      _ = HomologicalComplex.tensorHom (Bsum.hom ≫ A.hom) (𝟙 X) ≫ αA.hom :=
        congrArg (fun f => HomologicalComplex.tensorHom f (𝟙 X) ≫ αA.hom) ih
      _ = (HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
          HomologicalComplex.tensorHom A.hom (𝟙 X)) ≫ αA.hom :=
        congrArg (fun f => f ≫ αA.hom) hCompA.symm
      _ = HomologicalComplex.tensorHom Bsum.hom (𝟙 X) ≫
          (HomologicalComplex.tensorHom A.hom (𝟙 X) ≫ αA.hom) := Category.assoc _ _ _

/-- Concatenating native powers commutes with the original generic tensor-power comparisons. -/
theorem tensorPowObj_add_bridge_inv
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℕ) :
    HomologicalComplex.tensorHom
        (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
        (eqToIso (tensorPowObj_eq_tensorPower X n)).hom ≫
      (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_add X m n).inv =
    (tensorPowObj_add X m n).inv ≫
      (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom := by
  let e := tensorPowObj_add X m n
  let f := CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj_add X m n
  let a := HomologicalComplex.tensorHom
    (eqToIso (tensorPowObj_eq_tensorPower X m)).hom
    (eqToIso (tensorPowObj_eq_tensorPower X n)).hom
  let b := (eqToIso (tensorPowObj_eq_tensorPower X (m + n))).hom
  have h : e.hom ≫ a = b ≫ f.hom := tensorPowObj_add_bridge_hom X m n
  change a ≫ f.inv = e.inv ≫ b
  calc
    a ≫ f.inv = e.inv ≫ ((e.hom ≫ a) ≫ f.inv) := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ ((b ≫ f.hom) ≫ f.inv) := congrArg (fun k => e.inv ≫ (k ≫ f.inv)) h
    _ = e.inv ≫ b := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CochainComplex

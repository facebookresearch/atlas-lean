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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

/-!
# Finite weighted Weyl words

This file packages the repeated finite-word data used by the matrix and
Stable-Steinberg developments.  A letter consists of two distinct indices
and a unit.  A word is a head-left `List` product, with simultaneous
evaluations in permutations, weight tuples, monomial bases, monomial special
linear matrices, and special linear matrices.

The tuple evaluator is the left coordinate of the monomial-base evaluator;
in particular its cons and append laws use the existing semidirect-product
permutation action.  Coefficient maps use the landed tuple and monomial map
APIs.  No second tuple action, monomial group, Bruhat decomposition, or word
quotient is introduced.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

universe u v w

/-- A weighted Weyl letter with two distinct indices. -/
structure WeylLetter (R : Type u) [CommRing R] (ι : Type v) where
  /-- The first index of the weighted Weyl generator. -/
  left : ι
  /-- The second index of the weighted Weyl generator. -/
  right : ι
  /-- The two indices of the Weyl generator are distinct. -/
  ne : left ≠ right
  /-- The invertible coefficient of the weighted Weyl generator. -/
  unit : Rˣ

/-- A finite head-left word of weighted Weyl letters. -/
abbrev FiniteWeylWord (R : Type u) [CommRing R] (ι : Type v) :=
  List (WeylLetter R ι)

namespace WeylLetter

variable {R : Type u} [CommRing R]
variable {S : Type w} [CommRing S]
variable {ι : Type v} [DecidableEq ι] [Fintype ι]

/-- Permutation carried by a Weyl letter. -/
def perm (a : WeylLetter R ι) : Equiv.Perm ι :=
  Equiv.swap a.left a.right

/-- Weight tuple carried by a Weyl letter. -/
def weight (a : WeylLetter R ι) : ι → Rˣ :=
  weylWeightUnit a.left a.right a.ne a.unit

/-- Monomial-base realization of a Weyl letter. -/
def monomialBase (a : WeylLetter R ι) : MonomialBase Rˣ ι :=
  weylMonomialBaseUnit a.left a.right a.ne a.unit

/-- Determinant-one monomial realization of a Weyl letter. -/
noncomputable def monomialSL (a : WeylLetter R ι) : MonomialSL R ι :=
  weylMonomialSLUnit a.left a.right a.ne a.unit

/-- Special-linear realization of a Weyl letter. -/
noncomputable def specialLinear (a : WeylLetter R ι) :
    Matrix.SpecialLinearGroup ι R :=
  weylSLUnit a.left a.right a.ne a.unit

/-- Map the coefficient of a Weyl letter along a ring homomorphism. -/
def mapRingHom (f : R →+* S) (a : WeylLetter R ι) : WeylLetter S ι where
  left := a.left
  right := a.right
  ne := a.ne
  unit := Units.map f.toMonoidHom a.unit

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_left (f : R →+* S) (a : WeylLetter R ι) :
    (mapRingHom f a).left = a.left :=
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_right (f : R →+* S) (a : WeylLetter R ι) :
    (mapRingHom f a).right = a.right :=
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_unit (f : R →+* S) (a : WeylLetter R ι) :
    (mapRingHom f a).unit = Units.map f.toMonoidHom a.unit :=
  rfl

omit [Fintype ι] in
@[simp]
theorem perm_mapRingHom (f : R →+* S) (a : WeylLetter R ι) :
    (mapRingHom f a).perm = a.perm :=
  rfl

omit [Fintype ι] in
@[simp]
theorem monomialBase_right (a : WeylLetter R ι) :
    a.monomialBase.right = a.perm :=
  rfl

omit [Fintype ι] in
@[simp]
theorem monomialBase_left (a : WeylLetter R ι) :
    a.monomialBase.left = a.weight :=
  rfl

@[simp]
theorem monomialSL_coe (a : WeylLetter R ι) :
    (a.monomialSL : MonomialBase Rˣ ι) = a.monomialBase :=
  rfl

theorem specialLinear_eq_monomialSLHom (a : WeylLetter R ι) :
    a.specialLinear = monomialSLHom R ι a.monomialSL := by
  exact weylSLUnit_eq_monomialSLHom a.left a.right a.ne a.unit

omit [Fintype ι] in
@[simp]
theorem monomialBase_mapRingHom (f : R →+* S) (a : WeylLetter R ι) :
    monomialBaseHom (ι := ι) (Units.map f.toMonoidHom) a.monomialBase =
      (mapRingHom f a).monomialBase := by
  exact weylMonomialBaseUnit_map f a.left a.right a.ne a.unit

@[simp]
theorem monomialSL_mapRingHom (f : R →+* S) (a : WeylLetter R ι) :
    monomialSLMap R S ι f a.monomialSL =
      (mapRingHom f a).monomialSL := by
  exact weylMonomialSLUnit_map f a.left a.right a.ne a.unit

@[simp]
theorem specialLinear_mapRingHom (f : R →+* S) (a : WeylLetter R ι) :
    Matrix.SpecialLinearGroup.map f a.specialLinear =
      (mapRingHom f a).specialLinear := by
  exact weylSLUnit_map f a.left a.right a.ne a.unit

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_id (a : WeylLetter R ι) :
    mapRingHom (RingHom.id R) a = a := by
  cases a with
  | mk left right ne unit =>
      congr 1

omit [DecidableEq ι] [Fintype ι] in
theorem mapRingHom_comp
    {T : Type*} [CommRing T]
    (f : R →+* S) (g : S →+* T) (a : WeylLetter R ι) :
    mapRingHom (g.comp f) a = mapRingHom g (mapRingHom f a) := by
  cases a with
  | mk left right ne unit =>
      congr 1

end WeylLetter

namespace FiniteWeylWord

variable {R : Type u} [CommRing R]
variable {S : Type w} [CommRing S]
variable {ι : Type v} [DecidableEq ι] [Fintype ι]

/-- Turn a finite indexed family of letters into its ordered word. -/
def ofFn {m : ℕ} (a : Fin m → WeylLetter R ι) : FiniteWeylWord R ι :=
  List.ofFn a

/-- The standard bounded-natural-number presentation of a finite Weyl word. -/
def ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    FiniteWeylWord R (Fin n) :=
  List.ofFn fun k =>
    { left := ⟨a k, ha k⟩
      right := ⟨b k, hb k⟩
      ne := fun h => hab k (congrArg Fin.val h)
      unit := unit k }

/-- Head-left permutation evaluation. -/
def permEval (word : FiniteWeylWord R ι) : Equiv.Perm ι :=
  (word.map WeylLetter.perm).prod

/-- Head-left monomial-base evaluation. -/
def monomialBaseEval (word : FiniteWeylWord R ι) : MonomialBase Rˣ ι :=
  (word.map WeylLetter.monomialBase).prod

/-- Weight tuple of the monomial-base evaluation. -/
def tupleEval (word : FiniteWeylWord R ι) : ι → Rˣ :=
  (monomialBaseEval word).left

/-- Head-left determinant-one monomial evaluation. -/
noncomputable def monomialSLEval (word : FiniteWeylWord R ι) : MonomialSL R ι :=
  (word.map WeylLetter.monomialSL).prod

/-- Head-left special-linear evaluation. -/
noncomputable def specialLinearEval (word : FiniteWeylWord R ι) :
    Matrix.SpecialLinearGroup ι R :=
  (word.map WeylLetter.specialLinear).prod

/-- Map every coefficient of a finite Weyl word along a ring homomorphism. -/
def mapRingHom (f : R →+* S) (word : FiniteWeylWord R ι) :
    FiniteWeylWord S ι :=
  word.map (WeylLetter.mapRingHom f)

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem ofFn_length {m : ℕ} (a : Fin m → WeylLetter R ι) :
    (ofFn a).length = m := by
  simp [ofFn]

@[simp]
theorem ofBoundedNat_length {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    (ofBoundedNat a b ha hb hab unit).length = m := by
  simp [ofBoundedNat]

omit [Fintype ι] in
@[simp] theorem permEval_nil :
    permEval ([] : FiniteWeylWord R ι) = 1 :=
  rfl

omit [Fintype ι] in
@[simp] theorem monomialBaseEval_nil :
    monomialBaseEval ([] : FiniteWeylWord R ι) = 1 :=
  rfl

omit [Fintype ι] in
@[simp] theorem tupleEval_nil :
    tupleEval ([] : FiniteWeylWord R ι) = 1 :=
  rfl

@[simp] theorem monomialSLEval_nil :
    monomialSLEval ([] : FiniteWeylWord R ι) = 1 :=
  rfl

@[simp] theorem specialLinearEval_nil :
    specialLinearEval ([] : FiniteWeylWord R ι) = 1 :=
  rfl

omit [Fintype ι] in
@[simp]
theorem permEval_cons (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    permEval (letter :: word) = letter.perm * permEval word :=
  rfl

omit [Fintype ι] in
@[simp]
theorem monomialBaseEval_cons
    (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    monomialBaseEval (letter :: word) =
      letter.monomialBase * monomialBaseEval word :=
  rfl

omit [Fintype ι] in
@[simp]
theorem tupleEval_cons (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    tupleEval (letter :: word) =
      letter.weight *
        PermutationBilinearCocycle.permute letter.perm (tupleEval word) :=
  rfl

@[simp]
theorem monomialSLEval_cons
    (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    monomialSLEval (letter :: word) =
      letter.monomialSL * monomialSLEval word :=
  rfl

@[simp]
theorem specialLinearEval_cons
    (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    specialLinearEval (letter :: word) =
      letter.specialLinear * specialLinearEval word :=
  rfl

omit [Fintype ι] in
@[simp]
theorem permEval_singleton (letter : WeylLetter R ι) :
    permEval [letter] = letter.perm := by
  simp

omit [Fintype ι] in
@[simp]
theorem monomialBaseEval_singleton (letter : WeylLetter R ι) :
    monomialBaseEval [letter] = letter.monomialBase := by
  simp

omit [Fintype ι] in
@[simp]
theorem tupleEval_singleton (letter : WeylLetter R ι) :
    tupleEval [letter] = letter.weight := by
  simp

@[simp]
theorem monomialSLEval_singleton (letter : WeylLetter R ι) :
    monomialSLEval [letter] = letter.monomialSL := by
  simp

@[simp]
theorem specialLinearEval_singleton (letter : WeylLetter R ι) :
    specialLinearEval [letter] = letter.specialLinear := by
  simp

omit [Fintype ι] in
theorem permEval_append (word₁ word₂ : FiniteWeylWord R ι) :
    permEval (word₁ ++ word₂) = permEval word₁ * permEval word₂ := by
  simp [permEval, List.map_append, List.prod_append]

omit [Fintype ι] in
theorem monomialBaseEval_append (word₁ word₂ : FiniteWeylWord R ι) :
    monomialBaseEval (word₁ ++ word₂) =
      monomialBaseEval word₁ * monomialBaseEval word₂ := by
  simp [monomialBaseEval, List.map_append, List.prod_append]

omit [Fintype ι] in
theorem tupleEval_append (word₁ word₂ : FiniteWeylWord R ι) :
    tupleEval (word₁ ++ word₂) =
      tupleEval word₁ *
        PermutationBilinearCocycle.permute (permEval word₁) (tupleEval word₂) := by
  induction word₁ with
  | nil =>
      rw [List.nil_append, tupleEval_nil, permEval_nil, one_mul,
        PermutationBilinearCocycle.permute_one]
  | cons letter word ih =>
      rw [List.cons_append, tupleEval_cons, ih, tupleEval_cons,
        permEval_cons, PermutationBilinearCocycle.permute_mul_tuple,
        PermutationBilinearCocycle.permute_mul, mul_assoc]

theorem monomialSLEval_append (word₁ word₂ : FiniteWeylWord R ι) :
    monomialSLEval (word₁ ++ word₂) =
      monomialSLEval word₁ * monomialSLEval word₂ := by
  simp [monomialSLEval, List.map_append, List.prod_append]

theorem specialLinearEval_append (word₁ word₂ : FiniteWeylWord R ι) :
    specialLinearEval (word₁ ++ word₂) =
      specialLinearEval word₁ * specialLinearEval word₂ := by
  simp [specialLinearEval, List.map_append, List.prod_append]

omit [Fintype ι] in
@[simp]
theorem monomialBaseEval_left (word : FiniteWeylWord R ι) :
    (monomialBaseEval word).left = tupleEval word :=
  rfl

omit [Fintype ι] in
@[simp]
theorem monomialBaseEval_right (word : FiniteWeylWord R ι) :
    (monomialBaseEval word).right = permEval word := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      change letter.monomialBase.right * (monomialBaseEval word).right =
        letter.perm * permEval word
      rw [ih]
      rfl

@[simp]
theorem monomialSLEval_coe (word : FiniteWeylWord R ι) :
    (monomialSLEval word : MonomialBase Rˣ ι) = monomialBaseEval word := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      change (letter.monomialSL : MonomialBase Rˣ ι) *
          (monomialSLEval word : MonomialBase Rˣ ι) =
        letter.monomialBase * monomialBaseEval word
      rw [WeylLetter.monomialSL_coe, ih]

/-- A determinant-one monomial word that evaluates to the identity has
trivial permutation evaluation. -/
theorem permEval_eq_one_of_monomialSLEval_eq_one
    (word : FiniteWeylWord R ι) (hmono : monomialSLEval word = 1) :
    permEval word = 1 := by
  have hbase : monomialBaseEval word = 1 := by
    rw [← monomialSLEval_coe]
    exact congrArg
      (fun x : MonomialSL R ι => (x : MonomialBase Rˣ ι)) hmono
  have hright := congrArg SemidirectProduct.right hbase
  simpa only [monomialBaseEval_right, SemidirectProduct.one_right] using hright

theorem specialLinearEval_eq_monomialSLHom
    (word : FiniteWeylWord R ι) :
    specialLinearEval word = monomialSLHom R ι (monomialSLEval word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [specialLinearEval_cons, monomialSLEval_cons,
        WeylLetter.specialLinear_eq_monomialSLHom, map_mul, ih]

theorem bruhatMiddle_specialLinearEval
    {F : Type u} [Field F] [LinearOrder ι]
    (word : FiniteWeylWord F ι) :
    bruhatMiddle (specialLinearEval word) = monomialSLEval word := by
  rw [specialLinearEval_eq_monomialSLHom,
    bruhatMiddle_monomialSLHom]

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_nil (f : R →+* S) :
    mapRingHom f ([] : FiniteWeylWord R ι) = [] :=
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_cons (f : R →+* S)
    (letter : WeylLetter R ι) (word : FiniteWeylWord R ι) :
    mapRingHom f (letter :: word) =
      WeylLetter.mapRingHom f letter :: mapRingHom f word :=
  rfl

omit [DecidableEq ι] [Fintype ι] in
theorem mapRingHom_append (f : R →+* S)
    (word₁ word₂ : FiniteWeylWord R ι) :
    mapRingHom f (word₁ ++ word₂) =
      mapRingHom f word₁ ++ mapRingHom f word₂ := by
  simp [mapRingHom, List.map_append]

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mapRingHom_id (word : FiniteWeylWord R ι) :
    mapRingHom (RingHom.id R) word = word := by
  induction word with
  | nil => rfl
  | cons letter word ih => simp [ih]

omit [DecidableEq ι] [Fintype ι] in
theorem mapRingHom_comp
    {T : Type*} [CommRing T]
    (f : R →+* S) (g : S →+* T) (word : FiniteWeylWord R ι) :
    mapRingHom (g.comp f) word = mapRingHom g (mapRingHom f word) := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      simp only [mapRingHom_cons, ih]
      rw [WeylLetter.mapRingHom_comp]

omit [Fintype ι] in
@[simp]
theorem permEval_mapRingHom (f : R →+* S) (word : FiniteWeylWord R ι) :
    permEval (mapRingHom f word) = permEval word := by
  induction word with
  | nil => rfl
  | cons letter word ih => simp [ih]

omit [Fintype ι] in
@[simp]
theorem monomialBaseEval_mapRingHom
    (f : R →+* S) (word : FiniteWeylWord R ι) :
    monomialBaseHom (ι := ι) (Units.map f.toMonoidHom)
        (monomialBaseEval word) =
      monomialBaseEval (mapRingHom f word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [monomialBaseEval_cons, map_mul,
        WeylLetter.monomialBase_mapRingHom, ih,
        mapRingHom_cons, monomialBaseEval_cons]

omit [Fintype ι] in
@[simp]
theorem tupleEval_mapRingHom (f : R →+* S) (word : FiniteWeylWord R ι) :
    PermutationBilinearCocycle.mapTuple (Units.map f.toMonoidHom)
        (tupleEval word) =
      tupleEval (mapRingHom f word) := by
  have h := congrArg SemidirectProduct.left
    (monomialBaseEval_mapRingHom f word)
  simpa only [monomialBaseHom_left, mapTupleHom_apply,
    monomialBaseEval_left] using h

@[simp]
theorem monomialSLEval_mapRingHom
    (f : R →+* S) (word : FiniteWeylWord R ι) :
    monomialSLMap R S ι f (monomialSLEval word) =
      monomialSLEval (mapRingHom f word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [monomialSLEval_cons, map_mul,
        WeylLetter.monomialSL_mapRingHom, ih,
        mapRingHom_cons, monomialSLEval_cons]

@[simp]
theorem specialLinearEval_mapRingHom
    (f : R →+* S) (word : FiniteWeylWord R ι) :
    Matrix.SpecialLinearGroup.map f (specialLinearEval word) =
      specialLinearEval (mapRingHom f word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [specialLinearEval_cons, map_mul,
        WeylLetter.specialLinear_mapRingHom, ih,
        mapRingHom_cons, specialLinearEval_cons]

theorem permEval_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    permEval (ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k =>
        Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)).prod :=
  by
    simp only [ofBoundedNat, permEval, List.map_ofFn]
    congr 1

theorem monomialBaseEval_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    monomialBaseEval (ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k =>
        weylMonomialBaseUnit
          (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (unit k)).prod :=
  by
    simp only [ofBoundedNat, monomialBaseEval, List.map_ofFn]
    congr 1

theorem monomialSLEval_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    monomialSLEval (ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k =>
        weylMonomialSLUnit
          (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (unit k)).prod :=
  by
    simp only [ofBoundedNat, monomialSLEval, List.map_ofFn]
    congr 1

theorem specialLinearEval_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    specialLinearEval (ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k =>
        weylSLUnit
          (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)
          (fun h => hab k (congrArg Fin.val h)) (unit k)).prod :=
  by
    simp only [ofBoundedNat, specialLinearEval, List.map_ofFn]
    congr 1

end FiniteWeylWord

end Matrix.GeneralLinearGroup

end

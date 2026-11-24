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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylRealization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.FiniteWeylWord

/-!
# Stable-Steinberg evaluation of finite Weyl words

This file adapts the generic matrix `FiniteWeylWord` carrier to the two
Stable-Steinberg evaluations: the product of stable Weyl generators and the
product of their three-factor finite `StableE` realizations.  The comparison
is a list induction whose only mathematical step is the landed one-letter
finite realization theorem.

Word order is head-left throughout.  No matrix calculation, word quotient,
representation-independence statement, torus landing, or Matsumoto claim is
introduced here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Matrix.GeneralLinearGroup

namespace AlgebraicKTheory.StableSteinberg

universe u

variable {R : Type u} [CommRing R]

theorem letterNatNe {n : ℕ} (letter : WeylLetter R (Fin n)) :
    letter.left.val ≠ letter.right.val :=
  fun h => letter.ne (Fin.ext h)

/-- Evaluate a finite weighted Weyl letter as its Weyl element in the stable
Steinberg group. -/
def evalLetter {n : ℕ} (letter : WeylLetter R (Fin n)) :
    AlgebraicKTheory.StableSteinberg R :=
  weyl letter.left.val letter.right.val (letterNatNe letter) letter.unit

/-- Evaluate a finite Weyl letter in the stable elementary group as the three
elementary factors with coefficients `u`, `-u⁻¹` and `u`. -/
def evalLetterInStableE {n : ℕ} (letter : WeylLetter R (Fin n)) :
    StableE R :=
    StableE.elementary n letter.left letter.right letter.ne
      (letter.unit : R) *
    StableE.elementary n letter.right letter.left letter.ne.symm
      (-(letter.unit⁻¹ : Rˣ) : R) *
    StableE.elementary n letter.left letter.right letter.ne
      (letter.unit : R)

/-- Evaluate a finite Weyl word as a head-left product in the stable
Steinberg group. -/
def evalFiniteWeylWord {n : ℕ}
    (word : FiniteWeylWord R (Fin n)) :
    AlgebraicKTheory.StableSteinberg R :=
  (word.map evalLetter).prod

/-- Evaluate a finite Weyl word as the head-left product of the corresponding
three-factor finite elementary realizations. -/
def evalFiniteWeylWordInStableE {n : ℕ}
    (word : FiniteWeylWord R (Fin n)) : StableE R :=
  (word.map evalLetterInStableE).prod

@[simp]
theorem evalFiniteWeylWord_nil (n : ℕ) :
    evalFiniteWeylWord ([] : FiniteWeylWord R (Fin n)) = 1 :=
  rfl

@[simp]
theorem evalFiniteWeylWordInStableE_nil (n : ℕ) :
    evalFiniteWeylWordInStableE ([] : FiniteWeylWord R (Fin n)) = 1 :=
  rfl

@[simp]
theorem evalFiniteWeylWord_cons {n : ℕ}
    (letter : WeylLetter R (Fin n)) (word : FiniteWeylWord R (Fin n)) :
    evalFiniteWeylWord (letter :: word) =
      evalLetter letter * evalFiniteWeylWord word :=
  rfl

@[simp]
theorem evalFiniteWeylWordInStableE_cons {n : ℕ}
    (letter : WeylLetter R (Fin n)) (word : FiniteWeylWord R (Fin n)) :
    evalFiniteWeylWordInStableE (letter :: word) =
      evalLetterInStableE letter * evalFiniteWeylWordInStableE word :=
  rfl

@[simp]
theorem evalFiniteWeylWord_singleton {n : ℕ}
    (letter : WeylLetter R (Fin n)) :
    evalFiniteWeylWord [letter] = evalLetter letter := by
  simp

@[simp]
theorem evalFiniteWeylWordInStableE_singleton {n : ℕ}
    (letter : WeylLetter R (Fin n)) :
    evalFiniteWeylWordInStableE [letter] = evalLetterInStableE letter := by
  simp

theorem evalFiniteWeylWord_append {n : ℕ}
    (word₁ word₂ : FiniteWeylWord R (Fin n)) :
    evalFiniteWeylWord (word₁ ++ word₂) =
      evalFiniteWeylWord word₁ * evalFiniteWeylWord word₂ := by
  simp [evalFiniteWeylWord, List.map_append, List.prod_append]

theorem evalFiniteWeylWordInStableE_append {n : ℕ}
    (word₁ word₂ : FiniteWeylWord R (Fin n)) :
    evalFiniteWeylWordInStableE (word₁ ++ word₂) =
      evalFiniteWeylWordInStableE word₁ *
        evalFiniteWeylWordInStableE word₂ := by
  simp [evalFiniteWeylWordInStableE, List.map_append, List.prod_append]

theorem toStableE_evalLetter {n : ℕ}
    (letter : WeylLetter R (Fin n)) :
    toStableE (evalLetter letter) = evalLetterInStableE letter := by
  simpa only [evalLetter, evalLetterInStableE] using
    finiteWeyl_toStableE_eq_finiteElementary n
      letter.left.val letter.right.val letter.left.isLt letter.right.isLt
      (letterNatNe letter) letter.unit

/-- Stable elementary realization of a finite Weyl word, obtained by applying
the accepted one-letter realization at every list entry. -/
theorem toStableE_evalFiniteWeylWord {n : ℕ}
    (word : FiniteWeylWord R (Fin n)) :
    toStableE (evalFiniteWeylWord word) =
      evalFiniteWeylWordInStableE word := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [evalFiniteWeylWord_cons, map_mul,
        evalFiniteWeylWordInStableE_cons, toStableE_evalLetter, ih]

theorem evalLetter_mapRingHom
    {S : Type u} [CommRing S] (f : R →+* S) {n : ℕ}
    (letter : WeylLetter R (Fin n)) :
    AlgebraicKTheory.StableSteinberg.mapRingHom f (evalLetter letter) =
      evalLetter (WeylLetter.mapRingHom f letter) := by
  simpa only [evalLetter, WeylLetter.mapRingHom] using
    AlgebraicKTheory.StableSteinberg.mapRingHom_weyl f
      letter.left.val letter.right.val (letterNatNe letter) letter.unit

theorem evalLetterInStableE_mapRingHom
    {S : Type u} [CommRing S] (f : R →+* S) {n : ℕ}
    (letter : WeylLetter R (Fin n)) :
    StableE.mapRingHom f (evalLetterInStableE letter) =
      evalLetterInStableE (WeylLetter.mapRingHom f letter) := by
  simp only [evalLetterInStableE, map_mul,
    StableE.mapRingHom_elementary, WeylLetter.mapRingHom_left,
    WeylLetter.mapRingHom_right, WeylLetter.mapRingHom_unit]
  congr 2
  all_goals simp

/-- Naturality of stable-Steinberg word evaluation under a same-universe ring
homomorphism. -/
@[simp]
theorem evalFiniteWeylWord_mapRingHom
    {S : Type u} [CommRing S] (f : R →+* S) {n : ℕ}
    (word : FiniteWeylWord R (Fin n)) :
    AlgebraicKTheory.StableSteinberg.mapRingHom f
        (evalFiniteWeylWord word) =
      evalFiniteWeylWord (FiniteWeylWord.mapRingHom f word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [evalFiniteWeylWord_cons, map_mul, evalLetter_mapRingHom, ih,
        FiniteWeylWord.mapRingHom_cons, evalFiniteWeylWord_cons]

/-- Naturality of the finite `StableE` word realization under a same-universe
ring homomorphism. -/
@[simp]
theorem evalFiniteWeylWordInStableE_mapRingHom
    {S : Type u} [CommRing S] (f : R →+* S) {n : ℕ}
    (word : FiniteWeylWord R (Fin n)) :
    StableE.mapRingHom f (evalFiniteWeylWordInStableE word) =
      evalFiniteWeylWordInStableE
        (FiniteWeylWord.mapRingHom f word) := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [evalFiniteWeylWordInStableE_cons, map_mul,
        evalLetterInStableE_mapRingHom, ih,
        FiniteWeylWord.mapRingHom_cons,
        evalFiniteWeylWordInStableE_cons]

theorem evalFiniteWeylWord_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    evalFiniteWeylWord
        (FiniteWeylWord.ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k => weyl (a k) (b k) (hab k) (unit k)).prod := by
  simp only [FiniteWeylWord.ofBoundedNat, evalFiniteWeylWord,
    List.map_ofFn]
  congr 1

theorem evalFiniteWeylWordInStableE_ofBoundedNat {m n : ℕ}
    (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
    (hab : ∀ k, a k ≠ b k) (unit : Fin m → Rˣ) :
    evalFiniteWeylWordInStableE
        (FiniteWeylWord.ofBoundedNat a b ha hb hab unit) =
      (List.ofFn fun k =>
        StableE.elementary n ⟨a k, ha k⟩ ⟨b k, hb k⟩
            (fun h => hab k (congrArg Fin.val h)) (unit k : R) *
          StableE.elementary n ⟨b k, hb k⟩ ⟨a k, ha k⟩
            (fun h => (hab k).symm (congrArg Fin.val h))
              (-(↑((unit k)⁻¹) : R)) *
          StableE.elementary n ⟨a k, ha k⟩ ⟨b k, hb k⟩
            (fun h => hab k (congrArg Fin.val h)) (unit k : R)).prod := by
  simp only [FiniteWeylWord.ofBoundedNat,
    evalFiniteWeylWordInStableE, List.map_ofFn]
  congr 1

end AlgebraicKTheory.StableSteinberg

end

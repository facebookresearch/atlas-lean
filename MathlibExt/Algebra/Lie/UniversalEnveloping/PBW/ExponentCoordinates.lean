/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Multiset.Sort
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Exponent-function PBW coordinates

An ordered word is equivalent to its finite multiset of letters, hence to a
finitely supported exponent function. Reindexing the actual ordered-word
PBW basis gives the exponent basis. Its coefficient equivalence identifies
the original UEA with polynomials as a module over the ground ring.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {I : Type w} [LinearOrder I]

/-- Weakly increasing finite words are the finite multisets of their letters. -/
def orderedWordMultisetEquiv : OrderedWord I ≃ Multiset I where
  toFun xs := (xs.val : Multiset I)
  invFun s := ⟨s.sort (· ≤ ·), Multiset.pairwise_sort s (· ≤ ·)⟩
  left_inv xs := by
    apply Subtype.ext
    change (xs.val : Multiset I).sort (· ≤ ·) = xs.val
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) xs.property
  right_inv s := Multiset.sort_eq s (· ≤ ·)

/-- The literal finite exponent function of a word. -/
def wordExponent (xs : List I) : I →₀ ℕ := Multiset.toFinsupp (xs : Multiset I)

/-- The ordered-word/exponent-function bijection uses native multiset multiplicities. -/
def orderedWordExponentEquiv : OrderedWord I ≃ (I →₀ ℕ) :=
  orderedWordMultisetEquiv.trans Multiset.toFinsupp.toEquiv

@[simp]
theorem orderedWordExponentEquiv_apply (xs : OrderedWord I) :
    orderedWordExponentEquiv xs = wordExponent xs.val := rfl

@[simp]
theorem wordExponent_nil : wordExponent ([] : List I) = 0 := by
  simp only [wordExponent, Multiset.coe_nil, map_zero]

theorem wordExponent_append (xs ys : List I) :
    wordExponent (xs ++ ys) = wordExponent xs + wordExponent ys := by
  change Multiset.toFinsupp ((xs : Multiset I) + (ys : Multiset I)) = _
  exact map_add Multiset.toFinsupp _ _

@[simp]
theorem wordExponent_singleton (i : I) : wordExponent [i] = Finsupp.single i 1 := by
  simpa only [wordExponent, Multiset.coe_singleton] using Multiset.toFinsupp_singleton i

theorem wordExponent_cons (i : I) (xs : List I) :
    wordExponent (i :: xs) = Finsupp.single i 1 + wordExponent xs := by
  change wordExponent ([i] ++ xs) = _
  rw [wordExponent_append, wordExponent_singleton]

theorem wordExponent_adjacent_swap (p s : List I) (i j : I) :
    wordExponent (p ++ i :: j :: s) = wordExponent (p ++ j :: i :: s) := by
  simp only [wordExponent_append, wordExponent_cons]
  abel

theorem wordExponent_degree (xs : List I) : (wordExponent xs).degree = xs.length := by
  induction xs with
  | nil => simp only [wordExponent_nil, map_zero, List.length_nil]
  | cons i xs ih =>
      rw [wordExponent_cons, map_add, Finsupp.degree_single, ih, List.length_cons]
      omega

/-- The canonical ordered word with the original finite multiplicities. -/
def canonicalOrderedWord (xs : List I) : OrderedWord I :=
  orderedWordExponentEquiv.symm (wordExponent xs)

@[simp]
theorem canonicalOrderedWord_ordered (xs : OrderedWord I) :
    canonicalOrderedWord xs.val = xs :=
  orderedWordExponentEquiv.symm_apply_apply xs

theorem canonicalOrderedWord_exponent (xs : List I) :
    wordExponent (canonicalOrderedWord xs).val = wordExponent xs :=
  orderedWordExponentEquiv.apply_symm_apply (wordExponent xs)

theorem canonicalOrderedWord_length (xs : List I) :
    (canonicalOrderedWord xs).val.length = xs.length := by
  have h := wordExponent_degree (canonicalOrderedWord xs).val
  rw [canonicalOrderedWord_exponent, wordExponent_degree] at h
  exact h.symm

theorem orderedWordExponentEquiv_symm_length (e : I →₀ ℕ) :
    (orderedWordExponentEquiv.symm e).val.length = e.degree := by
  have h := wordExponent_degree (orderedWordExponentEquiv.symm e).val
  change (orderedWordExponentEquiv (orderedWordExponentEquiv.symm e)).degree = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem canonicalOrderedWord_adjacent_swap (p s : List I) (i j : I) :
    canonicalOrderedWord (p ++ i :: j :: s) = canonicalOrderedWord (p ++ j :: i :: s) := by
  rw [canonicalOrderedWord, canonicalOrderedWord, wordExponent_adjacent_swap]

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- The actual PBW basis indexed by finite exponent functions. -/
def exponentBasis (b : Module.Basis I R L) : Module.Basis (I →₀ ℕ) R U :=
  (orderedBasis b).reindex orderedWordExponentEquiv

theorem exponentBasis_apply (b : Module.Basis I R L) (e : I →₀ ℕ) :
    exponentBasis b e = basisWord b (orderedWordExponentEquiv.symm e).val := by
  rw [exponentBasis, Module.Basis.reindex_apply, orderedBasis_apply]
  rfl

/-- Polynomial PBW coordinates are a ground-module equivalence of the
original UEA; no algebra equivalence to the commutative polynomial ring is claimed. -/
def polynomialCoordinates (b : Module.Basis I R L) : U ≃ₗ[R] P :=
  (exponentBasis b).repr.trans (MvPolynomial.basisMonomials I R).repr.symm

@[simp]
theorem polynomialCoordinates_exponentBasis (b : Module.Basis I R L) (e : I →₀ ℕ) :
    polynomialCoordinates b (exponentBasis b e) = MvPolynomial.monomial e 1 := by
  change (MvPolynomial.basisMonomials I R).repr.symm
    ((exponentBasis b).repr (exponentBasis b e)) = _
  rw [Module.Basis.repr_self]
  change (MvPolynomial.basisMonomials I R : (I →₀ ℕ) → P) e = _
  rw [MvPolynomial.coe_basisMonomials]

theorem polynomialCoordinates_orderedWord (b : Module.Basis I R L) (xs : OrderedWord I) :
    polynomialCoordinates b (orderedWordValue b xs) =
      MvPolynomial.monomial (wordExponent xs.val) 1 := by
  have h : exponentBasis b (orderedWordExponentEquiv xs) = orderedWordValue b xs := by
    rw [exponentBasis_apply, Equiv.symm_apply_apply]
    rfl
  rw [← h, polynomialCoordinates_exponentBasis, orderedWordExponentEquiv_apply]

/-- Polynomial coordinates compute the actual recursive word normalizer,
including its finite lower-length bracket terms. -/
theorem polynomialCoordinates_basisWord (b : Module.Basis I R L) (xs : List I) :
    polynomialCoordinates b (basisWord b xs) =
      (normalize b xs).sum (fun ys r =>
        r • MvPolynomial.monomial (wordExponent ys.val) 1) := by
  rw [← orderedWordLinear_normalize b xs, orderedWordLinear,
    Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, polynomialCoordinates_orderedWord]

end UniversalEnvelopingAlgebra.PBW

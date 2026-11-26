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
# PBW coordinates indexed by finite exponent functions

Let `I` be a linearly ordered alphabet. A weakly increasing finite word is determined by its
multiset of letters, equivalently by the finitely supported exponent function `e : I →₀ ℕ`.
Its total exponent degree is the word length.

For an ordered `R`-basis `b` of an `R`-Lie algebra over a commutative ring, reindexing the
ordered-word PBW basis gives a basis of `U_R(L)` indexed by exponent functions. Its
coefficient coordinates give an `R`-linear equivalence to `MvPolynomial I R`. Ordered basis
words map to their monomials; arbitrary words map to the finite sum of monomials specified by
their bracket normalization.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {I : Type w} [LinearOrder I]

/-- The equivalence of ordered words and finite multisets.

A weakly increasing word maps to its multiset of letters; the inverse sorts a multiset in the
given linear order. -/
def orderedWordMultisetEquiv : OrderedWord I ≃ Multiset I where
  toFun xs := (xs.val : Multiset I)
  invFun s := ⟨s.sort (· ≤ ·), Multiset.pairwise_sort s (· ≤ ·)⟩
  left_inv xs := by
    apply Subtype.ext
    change (xs.val : Multiset I).sort (· ≤ ·) = xs.val
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self (· ≤ ·) xs.property
  right_inv s := Multiset.sort_eq s (· ≤ ·)

/-- The finite multiplicity function of a word.

For a finite word `xs`, this finitely supported function records the multiplicity of each
letter. -/
def wordExponent (xs : List I) : I →₀ ℕ := Multiset.toFinsupp (xs : Multiset I)

/-- The equivalence of ordered words and finite exponent functions.

Multiset multiplicities identify weakly increasing words with finitely supported functions `I
→₀ ℕ`. -/
def orderedWordExponentEquiv : OrderedWord I ≃ (I →₀ ℕ) :=
  orderedWordMultisetEquiv.trans Multiset.toFinsupp.toEquiv

/-- The exponent function of an ordered word.

The ordered-word exponent equivalence sends `xs` to the multiplicity function of `xs.val`. -/
@[simp]
theorem orderedWordExponentEquiv_apply (xs : OrderedWord I) :
    orderedWordExponentEquiv xs = wordExponent xs.val := rfl

/-- The exponent function of the empty word.

The empty word has the zero multiplicity function. -/
@[simp]
theorem wordExponent_nil : wordExponent ([] : List I) = 0 := by
  simp only [wordExponent, Multiset.coe_nil, map_zero]

/-- The exponent function of a concatenated word.

The multiplicity function of `xs ++ ys` is the sum of the two word exponent functions. -/
theorem wordExponent_append (xs ys : List I) :
    wordExponent (xs ++ ys) = wordExponent xs + wordExponent ys := by
  change Multiset.toFinsupp ((xs : Multiset I) + (ys : Multiset I)) = _
  exact map_add Multiset.toFinsupp _ _

/-- The exponent function of a one-letter word.

The word `[i]` has multiplicity one at `i` and zero at every other letter. -/
@[simp]
theorem wordExponent_singleton (i : I) : wordExponent [i] = Finsupp.single i 1 := by
  simpa only [wordExponent, Multiset.coe_singleton] using Multiset.toFinsupp_singleton i

/-- The exponent function after adjoining a first letter.

The word `i :: xs` has exponent function `single(i,1) + wordExponent(xs)`. -/
theorem wordExponent_cons (i : I) (xs : List I) :
    wordExponent (i :: xs) = Finsupp.single i 1 + wordExponent xs := by
  change wordExponent ([i] ++ xs) = _
  rw [wordExponent_append, wordExponent_singleton]

/-- Invariance of word exponents under an adjacent exchange.

Exchanging two adjacent letters within fixed prefix and suffix words retains the multiplicity
function. -/
theorem wordExponent_adjacent_swap (p s : List I) (i j : I) :
    wordExponent (p ++ i :: j :: s) = wordExponent (p ++ j :: i :: s) := by
  simp only [wordExponent_append, wordExponent_cons]
  abel

/-- The total exponent degree of a word.

The sum of the multiplicities in a word exponent function equals the word length. -/
theorem wordExponent_degree (xs : List I) : (wordExponent xs).degree = xs.length := by
  induction xs with
  | nil => simp only [wordExponent_nil, map_zero, List.length_nil]
  | cons i xs ih =>
      rw [wordExponent_cons, map_add, Finsupp.degree_single, ih, List.length_cons]
      omega

/-- The ordered word with prescribed word multiplicities.

Sort the letters of a word through the ordered-word exponent equivalence, retaining their
multiplicities. -/
def canonicalOrderedWord (xs : List I) : OrderedWord I :=
  orderedWordExponentEquiv.symm (wordExponent xs)

/-- The canonical ordering of an already ordered word.

A weakly increasing word is fixed by the canonical ordered-word map. -/
@[simp]
theorem canonicalOrderedWord_ordered (xs : OrderedWord I) :
    canonicalOrderedWord xs.val = xs :=
  orderedWordExponentEquiv.symm_apply_apply xs

/-- The exponent function of the canonical ordered word.

Canonical ordering retains the multiplicity of every letter. -/
theorem canonicalOrderedWord_exponent (xs : List I) :
    wordExponent (canonicalOrderedWord xs).val = wordExponent xs :=
  orderedWordExponentEquiv.apply_symm_apply (wordExponent xs)

/-- The length of the canonical ordered word.

Canonical ordering retains the finite word length. -/
theorem canonicalOrderedWord_length (xs : List I) :
    (canonicalOrderedWord xs).val.length = xs.length := by
  have h := wordExponent_degree (canonicalOrderedWord xs).val
  rw [canonicalOrderedWord_exponent, wordExponent_degree] at h
  exact h.symm

/-- The word length of an exponent-function index.

The ordered word corresponding to `e : I →₀ ℕ` has length `e.degree`. -/
theorem orderedWordExponentEquiv_symm_length (e : I →₀ ℕ) :
    (orderedWordExponentEquiv.symm e).val.length = e.degree := by
  have h := wordExponent_degree (orderedWordExponentEquiv.symm e).val
  change (orderedWordExponentEquiv (orderedWordExponentEquiv.symm e)).degree = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Invariance of canonical ordering under an adjacent exchange.

Two words differing by an adjacent exchange within the same prefix and suffix have the same
canonical ordered word. -/
theorem canonicalOrderedWord_adjacent_swap (p s : List I) (i j : I) :
    canonicalOrderedWord (p ++ i :: j :: s) = canonicalOrderedWord (p ++ j :: i :: s) := by
  rw [canonicalOrderedWord, canonicalOrderedWord, wordExponent_adjacent_swap]

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- The PBW basis indexed by exponent functions.

For an ordered basis `b` of `L`, reindex the ordered-word basis of `U_R(L)` by finite letter
multiplicities. -/
def exponentBasis (b : Module.Basis I R L) : Module.Basis (I →₀ ℕ) R U :=
  (orderedBasis b).reindex orderedWordExponentEquiv

/-- The ordered-word value of a PBW exponent basis element.

The basis element indexed by `e` is the enveloping product of the canonical ordered word with
exponent function `e`. -/
theorem exponentBasis_apply (b : Module.Basis I R L) (e : I →₀ ℕ) :
    exponentBasis b e = basisWord b (orderedWordExponentEquiv.symm e).val := by
  rw [exponentBasis, Module.Basis.reindex_apply, orderedBasis_apply]
  rfl

/-- The polynomial module coordinates of an enveloping algebra.

The PBW exponent basis and polynomial monomial basis give an `R`-linear equivalence `U_R(L)
≃ₗ[R] MvPolynomial I R`. -/
def polynomialCoordinates (b : Module.Basis I R L) : U ≃ₗ[R] P :=
  (exponentBasis b).repr.trans (MvPolynomial.basisMonomials I R).repr.symm

/-- The monomial coordinate of a PBW exponent basis element.

The basis element indexed by `e` maps to the polynomial monomial `X^e` with coefficient one. -/
@[simp]
theorem polynomialCoordinates_exponentBasis (b : Module.Basis I R L) (e : I →₀ ℕ) :
    polynomialCoordinates b (exponentBasis b e) = MvPolynomial.monomial e 1 := by
  change (MvPolynomial.basisMonomials I R).repr.symm
    ((exponentBasis b).repr (exponentBasis b e)) = _
  rw [Module.Basis.repr_self]
  change (MvPolynomial.basisMonomials I R : (I →₀ ℕ) → P) e = _
  rw [MvPolynomial.coe_basisMonomials]

/-- The polynomial coordinate of an ordered PBW word.

An ordered word maps to the monomial whose exponent function records its letter
multiplicities. -/
theorem polynomialCoordinates_orderedWord (b : Module.Basis I R L) (xs : OrderedWord I) :
    polynomialCoordinates b (orderedWordValue b xs) =
      MvPolynomial.monomial (wordExponent xs.val) 1 := by
  have h : exponentBasis b (orderedWordExponentEquiv xs) = orderedWordValue b xs := by
    rw [exponentBasis_apply, Equiv.symm_apply_apply]
    rfl
  rw [← h, polynomialCoordinates_exponentBasis, orderedWordExponentEquiv_apply]

/-- The polynomial coordinates of a bracket-normalized basis word.

For an arbitrary basis word, its polynomial coordinate is the finite sum of monomials indexed
by its ordered normal-form words, with their normalization coefficients. -/
theorem polynomialCoordinates_basisWord (b : Module.Basis I R L) (xs : List I) :
    polynomialCoordinates b (basisWord b xs) =
      (normalize b xs).sum (fun ys r =>
        r • MvPolynomial.monomial (wordExponent ys.val) 1) := by
  rw [← orderedWordLinear_normalize b xs, orderedWordLinear,
    Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul, polynomialCoordinates_orderedWord]

end UniversalEnvelopingAlgebra.PBW

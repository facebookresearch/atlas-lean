/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.FilteredNormalization

/-!
# Filtered polynomial coordinates of an enveloping algebra

Let `R` be a commutative ring and `L` an `R`-Lie algebra with basis indexed by a linearly
ordered `I`. The degree-`q` enveloping filtration is the span of ordered PBW words of length
at most `q`. The polynomial coordinate equivalence identifies it with polynomials of total
degree at most `q`.

For a word of length at most `q+1`, subtracting the monomial of its multiplicities leaves
polynomial degree at most `q`. Consequently right multiplication by a basis generator has
leading coordinate multiplication by the corresponding polynomial variable: for `u` of
enveloping degree at most `q`, `c(uι(b_i)) - c(u)X_i` has polynomial degree at most `q`. These
are ground-module and filtration comparisons.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R
local notation "N" => (OrderedWord I →₀ R)

/-- The enveloping span of bounded-length ordered PBW words.

For a basis `b`, stage `q` is the `R`-span of enveloping values of ordered words with length
at most `q`. -/
def orderedDegreeSpan (b : Module.Basis I R L) (q : ℕ) : Submodule R U :=
  Submodule.span R (orderedWordValue b '' {xs | xs.val.length ≤ q})

/-- Monotonicity of ordered PBW degree spans.

The spans of ordered words increase with the allowed length bound. -/
theorem orderedDegreeSpan_mono (b : Module.Basis I R L) : Monotone (orderedDegreeSpan b) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hpq, rfl⟩

/-- The degree bound for evaluation of an ordered normal form.

A linear combination of ordered words of length at most `q` evaluates into the corresponding
ordered PBW degree span. -/
theorem orderedWordLinear_mem_degreeSpan (b : Module.Basis I R L) (q : ℕ)
    {z : N} (hz : z ∈ normalFormDegreeSpan q) :
    orderedWordLinear b z ∈ orderedDegreeSpan b q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨xs, hxs, rfl⟩ := hz
      rw [orderedWordLinear_single, one_smul]
      exact Submodule.subset_span ⟨xs, hxs, rfl⟩
  | zero => rw [map_zero]; exact (orderedDegreeSpan b q).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (orderedDegreeSpan b q).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (orderedDegreeSpan b q).smul_mem r ih

/-- The ordered degree span containing a basis word.

The enveloping value of any basis word belongs to the span of ordered words of length at most
its own length. -/
theorem basisWord_mem_orderedDegreeSpan (b : Module.Basis I R L) (xs : List I) :
    basisWord b xs ∈ orderedDegreeSpan b xs.length := by
  rw [← orderedWordLinear_normalize b xs]
  exact orderedWordLinear_mem_degreeSpan b xs.length (normalize_mem_degreeSpan b xs)

private theorem ι_mul_mem_orderedDegreeSpan (b : Module.Basis I R L)
    (q : ℕ) (x : L) {u : U} (hu : u ∈ orderedDegreeSpan b q) :
    UniversalEnvelopingAlgebra.ι R x * u ∈ orderedDegreeSpan b (q + 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨xs, hxs, rfl⟩ := hu
      change xs.val.length ≤ q at hxs
      change UniversalEnvelopingAlgebra.ι R x * basisWord b xs.val ∈ _
      rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
      apply (orderedDegreeSpan b (q + 1)).sum_mem
      intro i hi
      apply (orderedDegreeSpan b (q + 1)).smul_mem
      rw [← basisWord_cons]
      apply orderedDegreeSpan_mono b (show (i :: xs.val).length ≤ q + 1 by
        simp only [List.length_cons]
        omega)
      exact basisWord_mem_orderedDegreeSpan b (i :: xs.val)
  | zero => rw [mul_zero]; exact (orderedDegreeSpan b (q + 1)).zero_mem
  | add u v hu hv ihu ihv =>
      rw [mul_add]
      exact (orderedDegreeSpan b (q + 1)).add_mem ihu ihv
  | smul r u hu ih =>
      rw [mul_smul_comm]
      exact (orderedDegreeSpan b (q + 1)).smul_mem r ih

private theorem word_mem_orderedDegreeSpan (b : Module.Basis I R L) (xs : List L) :
    UniversalEnvelopingAlgebra.word R L xs ∈ orderedDegreeSpan b xs.length := by
  induction xs with
  | nil =>
      let ys : OrderedWord I := ⟨[], List.Pairwise.nil⟩
      exact Submodule.subset_span ⟨ys, by change [].length ≤ [].length; exact le_rfl, rfl⟩
  | cons x xs ih =>
      rw [UniversalEnvelopingAlgebra.word_cons, List.length_cons]
      exact ι_mul_mem_orderedDegreeSpan b xs.length x ih

/-- The enveloping degree filtration as an ordered PBW span.

For every `q`, the enveloping word-degree filtration equals the span of ordered basis words
with length at most `q`. -/
theorem degreeFiltration_eq_orderedDegreeSpan (b : Module.Basis I R L) (q : ℕ) :
    UniversalEnvelopingAlgebra.degreeFiltration R L q = orderedDegreeSpan b q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro u ⟨xs, hxs, rfl⟩
    exact orderedDegreeSpan_mono b hxs (word_mem_orderedDegreeSpan b xs)
  · apply Submodule.span_le.mpr
    rintro u ⟨xs, hxs, rfl⟩
    change xs.val.length ≤ q at hxs
    exact UniversalEnvelopingAlgebra.word_mem_degreeFiltration R L (xs.val.map b) q
      (by simpa only [List.length_map] using hxs)

omit [LinearOrder I] in
private theorem monomial_mem_totalDegree {q : ℕ} {e : I →₀ ℕ} (he : e.degree ≤ q) :
    MvPolynomial.monomial e (1 : R) ∈ MvPolynomial.restrictTotalDegree I R q := by
  rw [MvPolynomial.restrictTotalDegree, MvPolynomial.monomial_mem_restrictSupport]
  exact Or.inl he

/-- The total-degree bound of filtered PBW coordinates.

An element in the ordered PBW span of length at most `q` maps to a polynomial of total degree
at most `q`. -/
theorem polynomialCoordinates_mem_totalDegree (b : Module.Basis I R L) (q : ℕ)
    {u : U} (hu : u ∈ orderedDegreeSpan b q) :
    polynomialCoordinates b u ∈ MvPolynomial.restrictTotalDegree I R q := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨xs, hxs, rfl⟩ := hu
      rw [polynomialCoordinates_orderedWord]
      exact monomial_mem_totalDegree (by rw [wordExponent_degree]; exact hxs)
  | zero => rw [map_zero]; exact (MvPolynomial.restrictTotalDegree I R q).zero_mem
  | add u v hu hv ihu ihv =>
      rw [map_add]
      exact (MvPolynomial.restrictTotalDegree I R q).add_mem ihu ihv
  | smul r u hu ih =>
      rw [map_smul]
      exact (MvPolynomial.restrictTotalDegree I R q).smul_mem r ih

/-- The enveloping degree bound of inverse polynomial coordinates.

A polynomial of total degree at most `q` maps under the inverse PBW coordinate equivalence to
the ordered degree span of bound `q`. -/
theorem polynomialCoordinates_symm_mem_degreeSpan (b : Module.Basis I R L) (q : ℕ)
    {p : P} (hp : p ∈ MvPolynomial.restrictTotalDegree I R q) :
    (polynomialCoordinates b).symm p ∈ orderedDegreeSpan b q := by
  rw [MvPolynomial.restrictTotalDegree, MvPolynomial.restrictSupport_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨e, he, rfl⟩ := hp
      change e.degree ≤ q at he
      change (polynomialCoordinates b).symm (MvPolynomial.monomial e 1) ∈ _
      rw [← polynomialCoordinates_exponentBasis b e, LinearEquiv.symm_apply_apply]
      let xs : OrderedWord I := orderedWordExponentEquiv.symm e
      exact Submodule.subset_span ⟨xs,
        (by change xs.val.length ≤ q; exact (orderedWordExponentEquiv_symm_length e).trans_le he),
        (exponentBasis_apply b e).symm⟩
  | zero => rw [map_zero]; exact (orderedDegreeSpan b q).zero_mem
  | add p r hp hr ihp ihr =>
      rw [map_add]
      exact (orderedDegreeSpan b q).add_mem ihp ihr
  | smul r p hp ih =>
      rw [map_smul]
      exact (orderedDegreeSpan b q).smul_mem r ih

/-- The degree criterion under polynomial PBW coordinates.

The coordinate polynomial of `u ∈ U_R(L)` has total degree at most `q` if and only if `u`
belongs to enveloping filtration stage `q`. -/
theorem polynomialCoordinates_mem_degree_iff (b : Module.Basis I R L) (q : ℕ) (u : U) :
    polynomialCoordinates b u ∈ MvPolynomial.restrictTotalDegree I R q ↔
      u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q := by
  rw [degreeFiltration_eq_orderedDegreeSpan b q]
  constructor
  · intro hu
    simpa only [LinearEquiv.symm_apply_apply] using
      polynomialCoordinates_symm_mem_degreeSpan b q hu
  · exact polynomialCoordinates_mem_totalDegree b q

/-- The polynomial evaluation map on ordered normal forms.

Evaluate a finite linear combination of ordered words in the enveloping algebra and then apply
the polynomial PBW coordinates. -/
def normalizedPolynomialMap (b : Module.Basis I R L) : N →ₗ[R] P :=
  (polynomialCoordinates b).toLinearMap.comp (orderedWordLinear b)

/-- The polynomial coordinate of a single ordered normal-form term.

A normal-form term with ordered word `xs` and coefficient `r` maps to `r` times the monomial
of `xs`'s multiplicities. -/
theorem normalizedPolynomialMap_single (b : Module.Basis I R L) (xs : OrderedWord I) (r : R) :
    normalizedPolynomialMap b (Finsupp.single xs r) =
      r • MvPolynomial.monomial (wordExponent xs.val) 1 := by
  rw [normalizedPolynomialMap, LinearMap.comp_apply, orderedWordLinear_single,
    map_smul]
  change r • polynomialCoordinates b (orderedWordValue b xs) = _
  exact congrArg (fun p : P => r • p) (polynomialCoordinates_orderedWord b xs)

/-- The polynomial coordinate of a normalized basis word.

The polynomial evaluation of the ordered normal form of `xs` equals the PBW coordinate of its
enveloping basis-word value. -/
theorem normalizedPolynomialMap_normalize (b : Module.Basis I R L) (xs : List I) :
    normalizedPolynomialMap b (normalize b xs) = polynomialCoordinates b (basisWord b xs) := by
  change polynomialCoordinates b (orderedWordLinear b (normalize b xs)) = _
  rw [orderedWordLinear_normalize]

private theorem normalizedPolynomialMap_lower_mem (b : Module.Basis I R L)
    (q n : ℕ) (hn : n ≤ q + 1) {z : N} (hz : z ∈ normalFormLowerSpan n) :
    normalizedPolynomialMap b z ∈ MvPolynomial.restrictTotalDegree I R q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨xs, hxs, rfl⟩ := hz
      change xs.val.length < n at hxs
      rw [normalizedPolynomialMap_single, one_smul]
      exact monomial_mem_totalDegree (by rw [wordExponent_degree]; omega)
  | zero => rw [map_zero]; exact (MvPolynomial.restrictTotalDegree I R q).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (MvPolynomial.restrictTotalDegree I R q).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (MvPolynomial.restrictTotalDegree I R q).smul_mem r ih

/-- The leading monomial of a basis word in PBW coordinates.

For a word of length at most `q+1`, its coordinate polynomial minus its multiplicity monomial
has total degree at most `q`. -/
theorem polynomialCoordinates_word_leading (b : Module.Basis I R L)
    (xs : List I) (q : ℕ) (hxs : xs.length ≤ q + 1) :
    polynomialCoordinates b (basisWord b xs) - MvPolynomial.monomial (wordExponent xs) 1 ∈
      MvPolynomial.restrictTotalDegree I R q := by
  have h := normalizedPolynomialMap_lower_mem b q xs.length hxs
    (normalize_sub_canonical_mem_lowerSpan b xs)
  simpa only [map_sub, normalizedPolynomialMap_normalize, normalizedPolynomialMap_single,
    one_smul, canonicalOrderedWord_exponent] using h

/-- The polynomial defect of right multiplication by a Lie basis generator.

For `i ∈ I`, the linear defect map sends `u` to `c(uι(b_i)) - c(u)X_i`, where `c` is the
polynomial PBW equivalence. -/
def rightMultiplicationDefect (b : Module.Basis I R L) (i : I) : U →ₗ[R] P where
  toFun u := polynomialCoordinates b (u * UniversalEnvelopingAlgebra.ι R (b i)) -
    polynomialCoordinates b u * MvPolynomial.X i
  map_add' u v := by
    simp only [add_mul, map_add, add_sub_add_comm]
  map_smul' r u := by
    simp only [smul_mul_assoc, map_smul, smul_sub, RingHom.id_apply]

/-- The degree bound for a right-generator multiplication defect.

If `u` has enveloping degree at most `q`, its right-multiplication defect at a basis generator
has polynomial total degree at most `q`. -/
theorem rightMultiplicationDefect_mem_degree (b : Module.Basis I R L)
    (i : I) (q : ℕ) {u : U}
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    rightMultiplicationDefect b i u ∈ MvPolynomial.restrictTotalDegree I R q := by
  rw [degreeFiltration_eq_orderedDegreeSpan b q] at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨xs, hxs, rfl⟩ := hu
      change xs.val.length ≤ q at hxs
      have h := polynomialCoordinates_word_leading b (xs.val ++ [i]) q (by
        simp only [List.length_append, List.length_singleton]
        omega)
      change polynomialCoordinates b
          (basisWord b xs.val * UniversalEnvelopingAlgebra.ι R (b i)) -
        polynomialCoordinates b (orderedWordValue b xs) * MvPolynomial.X i ∈ _
      rw [polynomialCoordinates_orderedWord]
      simpa only [basisWord_append, basisWord_cons, basisWord_nil, mul_one,
        wordExponent_append, wordExponent_singleton, MvPolynomial.monomial_add_single,
        pow_one] using h
  | zero => rw [map_zero]; exact (MvPolynomial.restrictTotalDegree I R q).zero_mem
  | add u v hu hv ihu ihv =>
      rw [map_add]
      exact (MvPolynomial.restrictTotalDegree I R q).add_mem ihu ihv
  | smul r u hu ih =>
      rw [map_smul]
      exact (MvPolynomial.restrictTotalDegree I R q).smul_mem r ih

end UniversalEnvelopingAlgebra.PBW

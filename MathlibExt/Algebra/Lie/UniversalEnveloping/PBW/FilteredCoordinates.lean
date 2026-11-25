/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.FilteredNormalization

/-!
# Filtered polynomial coordinates of the native UEA

The actual word filtration is the span of the ordered PBW words within the
same length bound. Polynomial coordinates identify it with the native
polynomial total-degree submodule. Right multiplication by a basis Lie
generator is multiplication by its polynomial variable modulo the previous
degree. These are module and filtration statements about the original UEA.
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

/-- Ordered PBW words within an actual enveloping degree bound. -/
def orderedDegreeSpan (b : Module.Basis I R L) (q : ℕ) : Submodule R U :=
  Submodule.span R (orderedWordValue b '' {xs | xs.val.length ≤ q})

theorem orderedDegreeSpan_mono (b : Module.Basis I R L) : Monotone (orderedDegreeSpan b) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hpq, rfl⟩

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

/-- Actual words and actual ordered PBW words define the same degree filtration. -/
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

/-- The actual native UEA degree filtration is exactly polynomial total degree
under the constructed PBW ground-module equivalence. -/
theorem polynomialCoordinates_mem_degree_iff (b : Module.Basis I R L) (q : ℕ) (u : U) :
    polynomialCoordinates b u ∈ MvPolynomial.restrictTotalDegree I R q ↔
      u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q := by
  rw [degreeFiltration_eq_orderedDegreeSpan b q]
  constructor
  · intro hu
    simpa only [LinearEquiv.symm_apply_apply] using
      polynomialCoordinates_symm_mem_degreeSpan b q hu
  · exact polynomialCoordinates_mem_totalDegree b q

/-- Evaluate computed normal forms in their actual polynomial PBW coordinates. -/
def normalizedPolynomialMap (b : Module.Basis I R L) : N →ₗ[R] P :=
  (polynomialCoordinates b).toLinearMap.comp (orderedWordLinear b)

theorem normalizedPolynomialMap_single (b : Module.Basis I R L) (xs : OrderedWord I) (r : R) :
    normalizedPolynomialMap b (Finsupp.single xs r) =
      r • MvPolynomial.monomial (wordExponent xs.val) 1 := by
  rw [normalizedPolynomialMap, LinearMap.comp_apply, orderedWordLinear_single,
    map_smul]
  change r • polynomialCoordinates b (orderedWordValue b xs) = _
  exact congrArg (fun p : P => r • p) (polynomialCoordinates_orderedWord b xs)

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

/-- Every actual word has its commutative monomial as leading PBW coordinate,
with its bracket corrections in the immediately lower polynomial degree. -/
theorem polynomialCoordinates_word_leading (b : Module.Basis I R L)
    (xs : List I) (q : ℕ) (hxs : xs.length ≤ q + 1) :
    polynomialCoordinates b (basisWord b xs) - MvPolynomial.monomial (wordExponent xs) 1 ∈
      MvPolynomial.restrictTotalDegree I R q := by
  have h := normalizedPolynomialMap_lower_mem b q xs.length hxs
    (normalize_sub_canonical_mem_lowerSpan b xs)
  simpa only [map_sub, normalizedPolynomialMap_normalize, normalizedPolynomialMap_single,
    one_smul, canonicalOrderedWord_exponent] using h

/-- The actual right-generator multiplication defect in polynomial coordinates. -/
def rightMultiplicationDefect (b : Module.Basis I R L) (i : I) : U →ₗ[R] P where
  toFun u := polynomialCoordinates b (u * UniversalEnvelopingAlgebra.ι R (b i)) -
    polynomialCoordinates b u * MvPolynomial.X i
  map_add' u v := by
    simp only [add_mul, map_add, add_sub_add_comm]
  map_smul' r u := by
    simp only [smul_mul_assoc, map_smul, smul_sub, RingHom.id_apply]

/-- Right multiplication by an actual basis Lie generator has leading term
its polynomial variable on every actual filtered UEA element. -/
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

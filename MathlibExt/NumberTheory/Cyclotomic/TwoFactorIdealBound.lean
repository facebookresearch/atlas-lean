/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The argument is adapted from `P2M/Sol/S_flt_regular.lean`, lines 3496-3508,
in anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Copyright (c) the flt-regular authors, as recorded in that repository.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Its ATTRIBUTION.md credits the flt-regular project: Alex J. Best,
Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi,
Ruben Van de Velde, and Andrew Yang.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# A common ideal factor of two cyclotomic linear factors

The bound holds for arbitrary inputs in a Dedekind domain containing a
primitive prime-order root of unity. It needs no Fermat equation or oddness
assumption. Ideal divisibility is opposite to ideal inclusion.
-/

public section

namespace IsPrimitiveRoot

open Ideal Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {p : ℕ} {ζ x y η₁ η₂ : R}

/-- The common ideal factor of `x + y * η₁` and `x + y * η₂` divides
`gcd ((x), (y)) * (ζ - 1)` for distinct `p`-th roots, with `p` prime.

This generalizes the number-field helper `CaseII.coprime_c_aux` from the
source cited above; zero inputs and the prime `2` are allowed. -/
lemma span_add_mul_sup_dvd_gcd_mul_sub_one (hζ : IsPrimitiveRoot ζ p)
    (hp : p.Prime) (hη₁ : η₁ ∈ nthRootsFinset p (1 : R))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : R)) (hne : η₁ ≠ η₂) :
    span {x + y * η₁} ⊔ span {x + y * η₂} ∣
      gcd (span {x}) (span {y}) * span {ζ - 1} := by
  have hs : span {ζ - 1} = span {η₁ - η₂} :=
    span_singleton_eq_span_singleton.mpr
      (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hp hη₁ hη₂ hne)
  rw [hs, dvd_iff_le, gcd_eq_sup, Ideal.sup_mul,
    span_singleton_mul_span_singleton, span_singleton_mul_span_singleton,
    sup_le_iff, span_singleton_le_iff_mem, span_singleton_le_iff_mem]
  simp_rw [mem_span_singleton_sup, mem_span_singleton]
  refine ⟨⟨-η₂, _, ⟨η₁, rfl⟩, ?_⟩, ⟨1, _, ⟨-1, rfl⟩, ?_⟩⟩ <;> ring

end IsPrimitiveRoot

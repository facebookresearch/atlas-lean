/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.WordMetricComparison
public import MathlibExt.GroupTheory.IntWordMetric

@[expose] public section

namespace MathlibExtTest.WordMetricComparison

open Group.Generators

/-- Any finite generating family of `Multiplicative ℤ` is bi-Lipschitz equivalent to the standard
one. -/
example {ι : Type*} [Finite ι] (P : Group.Generators (Multiplicative ℤ) ι) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ g, P.wordLength g ≤ K * intGenerators.wordLength g ∧
      intGenerators.wordLength g ≤ K * P.wordLength g :=
  exists_wordLength_bilipschitz P intGenerators

/-- Doubling `n ↦ 2n` is Lipschitz for the standard word length of `Multiplicative ℤ`. -/
example : ∃ K : ℕ, ∀ g : Multiplicative ℤ,
    intGenerators.wordLength (powMonoidHom 2 g) ≤ K * intGenerators.wordLength g :=
  exists_wordLength_le_mul_of_monoidHom intGenerators intGenerators (powMonoidHom 2)

end MathlibExtTest.WordMetricComparison

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering systems in which no modulus divides another (Erdős Problem 586)

Erdős Problem 586 (Schinzel): is there a covering system such that no two of the moduli divide each
other?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CoveringSystem

@[expose] public section

namespace MathlibExt.NumberTheory.CoveringSystemNonDividingModuliErdosProblem586Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #586, https://www.erdosproblems.com/586 (status
DISPROVED). UnsolvedMath record UM-30006942 (`EP-586`), dataset ulamai/UnsolvedMath v1.8.0.

A covering system is a finite family of congruence classes `a i mod m i` with every `m i ≥ 2` whose
union is `ℤ` (a class modulo `1` would cover `ℤ` alone); the covering condition is MathlibExt's
`Int.IsCoveringSystem` of the classes `Int.indexedCoveringClasses m a`. 'No two of the moduli divide
each other' is `¬ m i ∣ m j` for `i ≠ j`, which also forces the moduli to be distinct. Compared with
the formal-conjectures statement `ErdosProblems/586.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 586 (Schinzel): there is a covering system (finitely many congruence classes
`a i mod m i` with all `m i ≥ 2`, covering `ℤ`) in which no modulus divides another. -/
def coveringSystemNonDividingModuli : Prop :=
  ∃ (k : ℕ) (a : Fin k → ℤ) (m : Fin k → ℕ), (∀ i, 2 ≤ m i) ∧ (∀ i j, i ≠ j → ¬ m i ∣ m j) ∧
    Int.IsCoveringSystem (Int.indexedCoveringClasses m a)

/--
Resolved false: Balister, Bollobás, Morris, Sahasrabudhe and Tiba proved Schinzel's conjecture that
every covering system has two moduli one of which divides the other; erdosproblems.com/586 lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #586,
https://www.erdosproblems.com/586 (status DISPROVED); resolution: P. Balister, B. Bollobás, R.
Morris, J. Sahasrabudhe and M. Tiba, On the Erdős covering problem: the density of the uncovered
set, Invent. Math. (2022), 377-414, erdosproblems.com/586: the answer is no, as proved by Balister,
Bollobás, Morris, Sahasrabudhe and Tiba, https://www.erdosproblems.com/586.
-/
public theorem_wanted coveringSystemNonDividingModuli_refuted : ¬ coveringSystemNonDividingModuli

end MathlibExt.NumberTheory.CoveringSystemNonDividingModuliErdosProblem586Wanted

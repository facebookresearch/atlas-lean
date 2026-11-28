/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC CONGRUENCES with a factored modulus: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN1] QUADRATIC CONGRUENCES, p. 249
(comment: "Remains NP-complete even if the instance includes a prime factorization of b and
solutions to the congruence modulo all prime powers occurring in the factorization.");
K. L. Manders and L. M. Adleman, "NP-complete decision problems for binary
quadratics", Journal of Computer and System Sciences 16 (1978), 168-184,
doi:10.1016/0022-0000(78)90044-2, Theorem 2 and the remark after it.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuadraticCongruencesDefs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticCongruencesFactored

/-- An instance: the [AN1] numbers `(a, b, c)` and the factorization of `b` as a list of
entries `(p, e, S)`: a prime `p`, its exponent `e`, and the solutions `S` of `x² ≡ a`
modulo `p ^ e`. -/
abbrev QuadraticCongruencesFactoredInstance :=
  QuadraticCongruences.QuadraticCongruencesInstance × List (ℕ × ℕ × List ℕ)

/-- An entry `(p, e, S)` of the factorization for the residue `a`: `p` is prime, `e` is
positive, and `S` lists without repetition exactly the residues `y < p ^ e` with
`y ^ 2 ≡ a [MOD p ^ e]`. -/
def FactorEntryWellFormed (a : ℕ) (t : ℕ × ℕ × List ℕ) : Prop :=
  t.1.Prime ∧ 0 < t.2.1 ∧ t.2.2.Nodup ∧
    (∀ y ∈ t.2.2, y < t.1 ^ t.2.1 ∧ y ^ 2 ≡ a [MOD t.1 ^ t.2.1]) ∧
    ∀ y < t.1 ^ t.2.1, y ^ 2 ≡ a [MOD t.1 ^ t.2.1] → y ∈ t.2.2

/-- Well-formedness of an instance: `(a, b, c)` is a well-formed [AN1] instance, every entry
of the factorization is well formed for `a`, the primes are distinct, and the product of the
prime powers is `b`. -/
def WellFormed (i : QuadraticCongruencesFactoredInstance) : Prop :=
  QuadraticCongruences.WellFormed i.1 ∧ (∀ t ∈ i.2, FactorEntryWellFormed i.1.1 t) ∧
    (i.2.map Prod.fst).Nodup ∧ (i.2.map fun t => t.1 ^ t.2.1).prod = i.1.2.1

open Classical in
/-- QUADRATIC CONGRUENCES with a factored modulus as a decision problem over bitstrings. -/
noncomputable def quadraticCongruencesFactoredDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticCongruencesFactoredInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticCongruences.QuadraticCongruencesFeasible i.1)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.QuadraticCongruencesFactored

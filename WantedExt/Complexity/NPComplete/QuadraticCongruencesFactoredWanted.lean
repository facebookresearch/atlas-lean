/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC CONGRUENCES with a factored modulus is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.QuadraticCongruencesWanted
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticCongruencesFactored

/-!
# QUADRATIC CONGRUENCES with a factored modulus is NP-complete

QUADRATIC CONGRUENCES ([AN1], `QuadraticCongruencesWanted`) with extra information in the
instance. INSTANCE: positive integers `a`, `b` and `c`, a prime factorization
`b = p₁^{e₁} ⋯ p_r^{e_r}` of `b`, and, for each prime power `p_k^{e_k}` of the factorization,
the solutions of the congruence `x² ≡ a (mod p_k^{e_k})`. QUESTION: is there a positive integer
`x < c` such that `x² ≡ a (mod b)`?

The question is that of `QuadraticCongruencesWanted` on `(a, b, c)`. The factorization is a
list of entries `(p, e, S)`, one per prime: the primes are distinct, the exponents positive, the
product of the prime powers is `b`, and `S` lists, without repetition, every residue
`0 ≤ y < p^e` with `y² ≡ a (mod p^e)`. The numbers use the canonical binary encoding; the
problem is NP-complete in the weak sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **QUADRATIC CONGRUENCES with a factored modulus is NP-complete.** Source: Garey and
Johnson (1979), [AN1], comment; Manders and Adleman (1978). -/
public theorem_wanted quadraticCongruencesFactored_npComplete :
    quadraticCongruencesFactoredDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticCongruencesFactoredDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticCongruencesFactored

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRIMES is in P

Source:
M. Agrawal, N. Kayal, and N. Saxena, "PRIMES is in P", Annals of Mathematics 160 (2004),
781-793.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PrimesInP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# PRIMES is in P

The language of prime numbers, with the natural number decoded from its canonical binary
bitstring encoding, is decidable in deterministic polynomial time. Undecodable bitstrings are
no-instances. This is the AKS theorem: primality testing is in P.
-/

open Classical in
/-- **The primality decision problem.** The primality decision problem is the decision problem
that accepts a bitstring $x$ exactly when decoding $x$ with the canonical bitstring encoding of
the natural numbers (Mathlib's binary encoding) yields a prime number, and rejects $x$ otherwise.
-/
noncomputable def primesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ) x with
  | some n => decide (Nat.Prime n)
  | none => false

/-- **PRIMES is in P.** The primality decision problem, which accepts a bitstring exactly when it
decodes to a prime number under the canonical bitstring encoding of the natural numbers, belongs
to the complexity class P.

Source: M. Agrawal, N. Kayal, and N. Saxena, "PRIMES is in P", Annals
of Mathematics 160 (2004), 781-793. -/
public theorem_wanted primes_in_P :
    primesDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.PrimesInP

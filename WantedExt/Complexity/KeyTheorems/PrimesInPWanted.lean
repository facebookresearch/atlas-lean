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
/-- The primality decision problem over bitstrings. -/
noncomputable def primesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ) x with
  | some n => decide (Nat.Prime n)
  | none => false

/-- **PRIMES is in P.** Source: M. Agrawal, N. Kayal, and N. Saxena, "PRIMES is in P", Annals
of Mathematics 160 (2004), 781-793. -/
public theorem_wanted primes_in_P :
    primesDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.PrimesInP

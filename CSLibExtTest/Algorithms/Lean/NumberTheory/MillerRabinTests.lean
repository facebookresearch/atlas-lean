/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin
public meta import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin
import Mathlib.Tactic.NormNum.Prime

/-!
# Miller–Rabin tests

Executed fixtures check witnesses and costs on the Carmichael number `561` (base `2` passes
Fermat's test but is a Miller–Rabin witness), on `221 = 13 · 17` with the strong liar `174` and
the witness `137`, on primes (including the Mersenne prime `2^89 - 1`), on `2^100 + 1` (whose
`n - 1` is a pure power of two), and on a base outside `1, …, n - 1`. Closed examples instantiate
the one-sided correctness theorems; values of the well-founded definitions are checked with
`decide +kernel`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

open Cslib.Algorithms.Lean.ModularExponentiation

private meta def checkWitness (label : String) (a n : ℕ) (expected : Bool) : IO Unit := do
  let r := witness a n
  unless r.ret == expected do
    throw (IO.userError s!"{label}: got {r.ret}")
  IO.println s!"{label}: witness = {r.ret}, cost {r.time}"

#eval checkWitness "561 = 3·11·17, base 2 (Fermat liar)" 2 561 true
#eval checkWitness "221 = 13·17, base 174 (strong liar)" 174 221 false
#eval checkWitness "221 = 13·17, base 137" 137 221 true
#eval checkWitness "prime 97, base 5" 5 97 false
#eval checkWitness "prime 2, base 1" 1 2 false
#eval checkWitness "9, base 2 (Fermat witness)" 2 9 true
#eval checkWitness "2^100 + 1 = 17 · ..., n - 1 = 2^100, base 3" 3 (2 ^ 100 + 1) true
-- Outside `1, …, n - 1` the answer is not a certificate: `2` is prime.
#eval checkWitness "base outside 1..n-1: a = n = 2" 2 2 true

private meta def checkMR (label : String) (n : ℕ) (bases : List ℕ) (expected : Bool) :
    IO Unit := do
  let r := millerRabin n bases
  unless r.ret == expected do
    throw (IO.userError s!"{label}: got {r.ret}")
  IO.println s!"{label}: {if r.ret then "prime" else "composite"}, cost {r.time}"

#eval checkMR "561 with base 2" 561 [2] false
#eval checkMR "221 with the strong liar 174 only" 221 [174] true
#eval checkMR "221 with bases 174, 137" 221 [174, 137] false
#eval checkMR "97 with every base 1..96" 97 (List.range' 1 96) true
#eval checkMR "Mersenne prime 2^89 - 1 with bases 2, 3, 5, 7" (2 ^ 89 - 1) [2, 3, 5, 7] true

/-- `2` is a Fermat liar for the Carmichael number `561`. -/
example : 2 ^ 560 % 561 = 1 := by decide +kernel

/-- `WITNESS(2, 561)` is `true`, so `561` is composite by the theorem, not by factoring. -/
example : ¬ (561 : ℕ).Prime :=
  not_prime_of_witness (a := 2) (by decide) (by decide) (by decide +kernel)

/-- `174` is a strong liar for `221`: one base can miss, a second base catches it. -/
example : (millerRabin 221 [174]).ret = true ∧ (millerRabin 221 [174, 137]).ret = false := by
  decide +kernel

example : ¬ (221 : ℕ).Prime :=
  not_prime_of_millerRabin_eq_false (bases := [174, 137]) (by decide) (by decide +kernel)

/-- On the prime `97` every base in `1, …, 96` passes. -/
example : (millerRabin 97 (List.range' 1 96)).ret = true :=
  millerRabin_of_prime (by norm_num) _ (fun a ha => by
    simp only [List.mem_range'_1] at ha
    omega)

/-- `2^8 = 256 ≡ 4 (mod 9)`, a Fermat witness, hence a Miller–Rabin witness. -/
example : (witness 2 9).ret = true := witness_of_pow_ne_one (by decide) (by decide)

example : twoAdicSplit 560 = (4, 35) := by decide +kernel
example : twoAdicSplit (2 ^ 100) = (100, 1) := by decide +kernel

example (a n : ℕ) : (witness a n).time ≤
    (modularExponentiation a (twoAdicSplit (n - 1)).2 n).time + (twoAdicSplit (n - 1)).1 :=
  witness_time_le a n

#print axioms witness
#print axioms millerRabin
#print axioms witness_eq_false_of_prime
#print axioms not_prime_of_witness
#print axioms millerRabin_of_prime
#print axioms not_prime_of_millerRabin_eq_false
#print axioms witness_of_pow_ne_one
#print axioms witness_time_le

end Cslib.Algorithms.Lean.MillerRabin

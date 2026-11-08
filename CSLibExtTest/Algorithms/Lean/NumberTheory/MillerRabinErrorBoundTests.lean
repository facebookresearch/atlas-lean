/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound
public meta import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound
import Mathlib.Tactic.NormNum.Prime

/-!
# Miller–Rabin error-bound tests

Executed fixtures count the non-witnesses of odd composites (including the Carmichael numbers
`561` and `1105`, and `2047 = 23 · 89`, a strong pseudoprime to base `2`) and check each count
against the expected value and against the `(n - 1) / 4` bound; a sweep checks the `1/4` bound on
every odd composite below `600`. A second fixture counts the
failing pairs of bases. Closed examples instantiate the bound on a Carmichael number and the
error-count theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

private meta def check (n expected : ℕ) : IO Unit := do
  let c := (nonwitnesses n).card
  unless c == expected && c ≤ (n - 1) / 4 do
    throw (IO.userError s!"n = {n}: {c} non-witnesses")
  IO.println s!"n = {n}: {c} non-witnesses ≤ (n - 1) / 4 = {(n - 1) / 4}"

#eval check 9 2
#eval check 15 2
#eval check 25 4
#eval check 91 18
#eval check 221 6
#eval check 341 50
#eval check 561 10
#eval check 1105 30
#eval check 2047 242

/-- Every odd composite below `600`: the count of non-witnesses never exceeds `(n - 1) / 4`;
report the composites where it is largest relative to `n - 1`. -/
private meta def sweep (bound : ℕ) : IO Unit := do
  let mut worst : List (ℕ × ℕ) := []
  let mut checked := 0
  for n in List.range bound do
    if n % 2 == 1 && 1 < n && !Nat.Prime n then
      let c := (nonwitnesses n).card
      unless c ≤ (n - 1) / 4 do
        throw (IO.userError s!"n = {n}: {c} non-witnesses > (n - 1) / 4")
      checked := checked + 1
      if 8 * c ≥ n - 1 then worst := worst ++ [(n, c)]
  IO.println s!"{checked} odd composites below {bound} checked; with at least (n - 1) / 8 \
    non-witnesses: {worst}"

#eval sweep 600

private meta def checkPairs (n expected : ℕ) : IO Unit := do
  let bad := ((Fintype.piFinset fun _ : Fin 2 => Finset.Ioo 0 n).filter
    fun b => (millerRabin n (List.ofFn b)).ret = true).card
  unless bad == expected && bad ≤ ((n - 1) / 4) ^ 2 do
    throw (IO.userError s!"n = {n}: {bad} failing pairs")
  IO.println s!"n = {n}: {bad} of {(n - 1) ^ 2} pairs of bases answer prime, ≤ {((n - 1) / 4) ^ 2}"

#eval checkPairs 9 4
#eval checkPairs 91 324

/-- `2047` is a strong pseudoprime to base `2`, but at most half of all bases fool the test. -/
example : (witness 2 2047).ret = false := by decide +kernel

/-- The Carmichael number `561`, through Mathlib's `Nat.isCarmichael_561`. -/
example : (nonwitnesses 561).card ≤ 280 :=
  card_nonwitnesses_le_of_carmichael Nat.isCarmichael_561

example : (nonwitnesses 2047).card ≤ 1023 :=
  card_nonwitnesses_le (by norm_num) (by norm_num) (by norm_num)

/-- The `1/4` bound on the strong pseudoprime `2047`, on `561`, and on `9 = 3^2`, where it is
attained (`2` non-witnesses, `1` and `8`). -/
example : (nonwitnesses 2047).card ≤ 511 :=
  card_nonwitnesses_le_quarter (by norm_num) (by norm_num) (by norm_num)

example : (nonwitnesses 561).card ≤ 140 :=
  card_nonwitnesses_le_quarter_of_carmichael Nat.isCarmichael_561

example : (nonwitnesses (3 ^ 2)).card ≤ (3 ^ 2 - 1) / 4 :=
  card_nonwitnesses_le_quarter_of_prime_pow Nat.prime_three le_rfl (by norm_num)

/-- Ten random bases for `2047`: at most `511^10` of the `2046^10` lists answer *prime*. -/
example : ((Fintype.piFinset fun _ : Fin 10 => Finset.Ioo 0 2047).filter
    fun b => (millerRabin 2047 (List.ofFn b)).ret = true).card ≤ 511 ^ 10 :=
  card_millerRabin_errors_le_quarter (by norm_num) (by norm_num) (by norm_num) 10

/-- Ten random bases for `561`: at most `280^10` of the `560^10` lists answer *prime*. -/
example : ((Fintype.piFinset fun _ : Fin 10 => Finset.Ioo 0 561).filter
    fun b => (millerRabin 561 (List.ofFn b)).ret = true).card ≤ 280 ^ 10 :=
  card_millerRabin_errors_le (by norm_num) (by norm_num) (by norm_num) 10

example (n s : ℕ) : (Fintype.piFinset fun _ : Fin s => Finset.Ioo 0 n).card = (n - 1) ^ s :=
  card_bases n s

#print axioms card_nonwitnesses_le
#print axioms card_nonwitnesses_le_of_pow_ne_one
#print axioms card_nonwitnesses_le_of_carmichael
#print axioms card_millerRabin_errors_le
#print axioms witness_eq_false_imp
#print axioms millerRabin_eq_true_iff
#print axioms card_nonwitnesses_le_quarter
#print axioms card_nonwitnesses_le_quarter_of_prime_pow
#print axioms card_nonwitnesses_le_quarter_of_pow_ne_one
#print axioms card_nonwitnesses_le_quarter_of_carmichael
#print axioms card_millerRabin_errors_le_quarter

end Cslib.Algorithms.Lean.MillerRabin

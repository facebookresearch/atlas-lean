/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MetaMathlibExt

@[expose] public section

/--
`replaceDigit N i d` replaces the base-ten digit of `N` at the units-indexed position `i`
by `d`: the first summand preserves the digits above `i`, the second installs `d`, and the
third preserves the digits below `i`. Positions beyond the written numeral are its leading
zeros. This is exactly the requested encoding, with no deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def replaceDigit (N i d : ℕ) : ℕ :=
  N / 10 ^ (i + 1) * 10 ^ (i + 1) + d * 10 ^ i + N % 10 ^ i

/--
`deleteDigit N i` deletes the base-ten digit of `N` at the units-indexed position `i`:
digits above `i` shift down one place and digits below `i` remain fixed. Its use is restricted
to `i < (Nat.digits 10 N).length`; there is no deviation from the requested encoding.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def deleteDigit (N i : ℕ) : ℕ :=
  N / 10 ^ (i + 1) * 10 ^ i + N % 10 ^ i

/--
`insertDigit N i d` inserts `d` as the new base-ten digit at the units-indexed position `i`:
digits at and above `i` shift up, while lower digits remain fixed. Thus `i = 0` appends on the
right, intermediate positions insert between written digits, and positions beyond the length
insert between leading zeros. The case `i = length` coincides with replacing the first leading
zero, so its inclusion adds nothing beyond replacement; otherwise there is no deviation from
the requested encoding.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def insertDigit (N i d : ℕ) : ℕ :=
  N / 10 ^ i * 10 ^ (i + 1) + d * 10 ^ i + N % 10 ^ i

/--
`IsDigitallyRobustComposite N` says that `N` is composite (`1 < N ∧ ¬ N.Prime`) and coprime
to `10`; every genuine digit replacement by a digit below `10` is composite; deleting every
written digit is composite; and inserting every digit below `10` at every position is composite.
Digits are units-indexed and the replacement quantifier includes infinitely many leading zeros.
The insertion case at the written length duplicates replacement of the first leading zero, as
specified; “composite” is expanded rather than given a separate definition, with no mathematical
deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public def IsDigitallyRobustComposite (N : ℕ) : Prop :=
  (1 < N ∧ ¬ N.Prime) ∧
    Nat.Coprime N 10 ∧
      (∀ i d, d < 10 → d ≠ N / 10 ^ i % 10 →
        1 < replaceDigit N i d ∧ ¬ (replaceDigit N i d).Prime) ∧
        (∀ i < (Nat.digits 10 N).length,
          1 < deleteDigit N i ∧ ¬ (deleteDigit N i).Prime) ∧
          ∀ i d, d < 10 → 1 < insertDigit N i d ∧ ¬ (insertDigit N i d).Prime

/--
There are infinitely many natural numbers `N` that satisfy `IsDigitallyRobustComposite N`:
they are composite and coprime to ten, and remain composite under every replacement, permitted
deletion, and insertion encoded above. The set-theoretic infinitude is the requested rendering;
there is no mathematical deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem_wanted infinitelyMany_digitallyRobustComposites :
    {N : ℕ | IsDigitallyRobustComposite N}.Infinite

/--
For positive `b` and prime `p` dividing the integer value `Φ_b(10)`, both implications hold:
if `b < p`, then the multiplicative order of `10 : ZMod p` is `b`; and if `p ≤ b` and
`2 < b`, then `p ∣ b`, every prime divisor `q` of `b` satisfies `q ≤ p`, and `p²` does not
divide `Φ_b(10)`. The “largest prime dividing `b`” clause is expanded into divisibility and
the universal upper-bound condition exactly as requested; there is no other deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Lemma 1.
-/
public theorem_wanted cyclotomicPrimeDivisor_order_and_largestPrime :
    ∀ (b p : ℕ), 0 < b → p.Prime →
      (p : ℤ) ∣ (Polynomial.cyclotomic b ℤ).eval 10 →
        (b < p → orderOf (10 : ZMod p) = b) ∧
          (p ≤ b → 2 < b → p ∣ b ∧
            (∀ q, q.Prime → q ∣ b → q ≤ p) ∧
              ¬ (p : ℤ) ^ 2 ∣ (Polynomial.cyclotomic b ℤ).eval 10)

/--
Replacing the units digit of `25011` by `3` produces `25013`, illustrating the replacement
operation in Theorem 1. This is a characteristic computation, not a claim from the theorem,
and introduces no encoding deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem replaceDigit_25011_units : replaceDigit 25011 0 3 = 25013 := by
  norm_num [replaceDigit]

/--
Deleting position `4`, the ten-thousands digit, from `25011` produces `5011`, illustrating
the deletion operation in Theorem 1. This is a characteristic computation and has no encoding
deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem deleteDigit_25011_tenThousands : deleteDigit 25011 4 = 5011 := by
  norm_num [deleteDigit]

/--
Inserting `1` at position `7` of `25011`, between its second and third leading zeros, produces
`10025011`, illustrating the insertion operation in Theorem 1. This is a characteristic
computation and has no encoding deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem insertDigit_25011_leadingZeros : insertDigit 25011 7 1 = 10025011 := by
  norm_num [insertDigit]

/--
Replacing the leading-zero digit at position `6` of `25011` by `0` leaves `25011` unchanged,
checking the leading-zero interpretation used by the replacement clause. This is a sanity check
and has no encoding deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem replaceDigit_25011_leadingZero : replaceDigit 25011 6 0 = 25011 := by
  norm_num [replaceDigit]

/--
For every natural `N` and units-indexed position `i`, the extracted base-ten digit
`N / 10 ^ i % 10` is below `10`. This records the digit interpretation used in the replacement
clause and introduces no deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem digitValue_lt_ten (N i : ℕ) : N / 10 ^ i % 10 < 10 := by
  exact Nat.mod_lt _ (by norm_num)

/--
The number `25011` is not digitally robust: replacing its units digit `1` by `3` yields the
prime `25013`, contradicting the replacement-composite conjunct of
`IsDigitallyRobustComposite`. This formalizes the paper's counterexample with no deviation.
Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem not_isDigitallyRobustComposite_25011 : ¬ IsDigitallyRobustComposite 25011 := by
  intro h
  obtain ⟨_, _, hreplace, _, _⟩ := h
  have hcomposite := hreplace 0 3 (by norm_num) (by norm_num)
  rw [replaceDigit_25011_units] at hcomposite
  exact hcomposite.2 (by norm_num)

end

end MetaMathlibExt

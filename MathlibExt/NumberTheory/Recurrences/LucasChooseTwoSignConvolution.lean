/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Lucas binomial sums with signs from triangular numbers

For each integer $p$ and natural number $n$, both convolutions of $U(p,-1)$ and $V(p,-1)$
with weights $(-1)^{\binom{k}{2}}\binom{4n+1}{k}$ over $0 \le k \le 4n+1$ equal
$(-1)^n 2^{2n+1} U_{4n+1}(p,-1)$. The signs repeat every four indices, making the weights
symmetric about the midpoint. Adding the two sums lets the Lucas addition formula replace
each pair of products by $2U_{4n+1}(p,-1)$. In the resulting scalar sum, Pascal's rule and the sign
change after two indices give a factor of $-4$ every four rows.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Proposition 3.1 and the symmetry
  argument described in Section 3.
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition).
* The reflection step is analogous to that in `lucasU_lucasV_sum_choose_sq_alternating` in
  `MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum`; the addition formula
  `two_mul_lucasU_add` comes from `MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition`.
-/

namespace MetaMathlibExt

open Finset
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add)

private def chooseTwoSign (k : ℕ) : ℤ := (-1) ^ k.choose 2

private theorem chooseTwoSign_antiperiodic : Function.Antiperiodic chooseTwoSign 2 := by
  intro k
  have hchoose : (k + 2).choose 2 = k.choose 2 + (2 * k + 1) := by
    rw [Nat.choose_succ_succ' (k + 1) 1, Nat.choose_succ_succ' k 1]
    simp only [Nat.choose_one_right, show 1 + 1 = 2 by decide]
    omega
  simp only [chooseTwoSign, hchoose, pow_add, pow_mul, neg_one_sq, one_pow, pow_one,
    mul_neg, mul_one]

private theorem chooseTwoSign_reflect {n k : ℕ} (hk : k ≤ 4 * n + 1) :
    chooseTwoSign (4 * n + 1 - k) = chooseTwoSign k := by
  have hp : Function.Periodic chooseTwoSign 4 := chooseTwoSign_antiperiodic.periodic_two_mul
  rw [← hp.map_mod_nat (4 * n + 1 - k), ← hp.map_mod_nat k,
    show (4 * n + 1 - k) % 4 = (5 - k % 4) % 4 by omega]
  have := Nat.mod_lt k (by decide : 0 < 4)
  interval_cases k % 4 <;> decide

-- Shifting the signs separately from the binomial row makes Pascal's rule a two-term recurrence.
private def signedChooseSum (m j : ℕ) : ℤ :=
  ∑ k ∈ range (m + 1), (m.choose k : ℤ) * chooseTwoSign (k + j)

private theorem signedChooseSum_four_mul_add_one (n : ℕ) :
    signedChooseSum (4 * n + 1) 0 = (-1) ^ n * 2 ^ (2 * n + 1) := by
  have hstep (m j : ℕ) : signedChooseSum (m + 1) j =
      signedChooseSum m j + signedChooseSum m (j + 1) := by
    simpa only [signedChooseSum, Nat.add_assoc, Nat.add_comm 1 j] using
      sum_choose_succ_mul (fun k _ => chooseTwoSign (k + j)) m
  have hshift (m j : ℕ) : signedChooseSum m (j + 2) = -signedChooseSum m j := by
    simp only [signedChooseSum, ← Nat.add_assoc, chooseTwoSign_antiperiodic (_ : ℕ), mul_neg,
      sum_neg_distrib]
  have htwo (m j : ℕ) : signedChooseSum (m + 2) j = 2 * signedChooseSum m (j + 1) := by
    rw [hstep (m + 1) j, hstep m j, hstep m (j + 1), hshift]
    ring
  have hfour (m : ℕ) : signedChooseSum (m + 4) 0 = -4 * signedChooseSum m 0 := by
    rw [htwo (m + 2) 0, htwo m 1, hshift m 0]
    ring
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [show 4 * (n + 1) + 1 = (4 * n + 1) + 4 by omega, hfour, ih, pow_succ (-1 : ℤ) n,
      show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
    ring

set_option backward.proofsInPublic true in
/-- **Binomial sums with signs $(-1)^{\binom{k}{2}}$ and Lucas sequences.** Let $p$ be an integer
and let $U_n$ and $V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$,
$U_1 = 1$, $V_0 = 2$, $V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every
natural number $n$,
$$\sum_{k=0}^{4n+1} (-1)^{\binom{k}{2}} \binom{4n+1}{k} U_k V_{4n+1-k} = (-1)^n 2^{2n+1} U_{4n+1}$$
and
$$\sum_{k=0}^{4n+1} (-1)^{\binom{k}{2}} \binom{4n+1}{k} V_k U_{4n+1-k} = (-1)^n 2^{2n+1} U_{4n+1}.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 3.1. -/
public theorem lucasU_lucasV_sum_choose_sign_choose_two (p : ℤ) (n : ℕ) :
    (∑ k ∈ Finset.range (4 * n + 2),
        ((4 * n + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (4 * n + 1 - k) =
      (-1) ^ n * 2 ^ (2 * n + 1) * lucasU ⟨p, -1, by decide⟩ (4 * n + 1)) ∧
    ∑ k ∈ Finset.range (4 * n + 2),
        ((4 * n + 1).choose k : ℤ) * (-1) ^ k.choose 2 *
          lucasV ⟨p, -1, by decide⟩ k * lucasU ⟨p, -1, by decide⟩ (4 * n + 1 - k) =
      (-1) ^ n * 2 ^ (2 * n + 1) * lucasU ⟨p, -1, by decide⟩ (4 * n + 1) := by
  let m := 4 * n + 1
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let a (k : ℕ) : ℤ := (m.choose k : ℤ) * chooseTwoSign k
  let L := ∑ k ∈ range (m + 1), a k * lucasU P k * lucasV P (m - k)
  let R := ∑ k ∈ range (m + 1), a k * lucasV P k * lucasU P (m - k)
  let rhs := (-1 : ℤ) ^ n * 2 ^ (2 * n + 1) * lucasU P m
  have hreflect : R = L := by
    dsimp only [R, L]
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    have hkm := mem_range_succ_iff.mp hk
    have ha : a (m - k) = a k := by
      dsimp only [a]
      rw [Nat.choose_symm hkm, chooseTwoSign_reflect hkm]
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hkm, ha]
    ac_rfl
  have hdouble : L + R = 2 * rhs := by
    calc
      _ = ∑ k ∈ range (m + 1), a k * (lucasU P k * lucasV P (m - k) +
          lucasV P k * lucasU P (m - k)) := by
        simp only [L, R, mul_add, ← mul_assoc, sum_add_distrib]
      _ = ∑ k ∈ range (m + 1), a k * (2 * lucasU P m) := by
        refine sum_congr rfl fun k hk => ?_
        rw [← two_mul_lucasU_add, Nat.add_sub_of_le (mem_range_succ_iff.mp hk)]
      _ = _ := by
        rw [← sum_mul]
        change signedChooseSum (4 * n + 1) 0 * (2 * lucasU P m) = 2 * rhs
        rw [signedChooseSum_four_mul_add_one]
        dsimp only [rhs]
        ring
  rw [hreflect] at hdouble
  have hL : L = rhs := by omega
  exact ⟨hL, hreflect.trans hL⟩

end MetaMathlibExt

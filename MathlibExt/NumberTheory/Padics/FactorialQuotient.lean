/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Valuation of a factorial quotient

The valuation of a product of consecutive positive integers is bounded by the valuation of the
factorial of its length plus the largest valuation of a factor.
-/

namespace MetaMathlibExt

open Nat Finset

/-- **Valuation of a product of consecutive integers.** Let $m$ and $k$ be natural numbers and
$p$ a prime, and write $v_p(n)$ for the exponent of $p$ in a positive integer $n$. Then
$v_p\bigl((m+k)!/m!\bigr) \le v_p(k!) + \max \{ v_p(m + i) : 1 \le i \le k \}$, where the
maximum is $0$ when $k = 0$.

The quotient $(m+k)!/m! = (m+1) \cdots (m+k)$ is an integer. Unlike the source, the inequality
is stated also for $m = 0$ and $k = 0$.

Source: Carl Pomerance, *Remarks on the Middle Binomial Coefficient*, INTEGERS 26 (2026),
Article A47, Lemma 3 (`integers-2026-A47-lem-3`). -/
public theorem padicValNat_factorial_div_factorial_le (m k p : ℕ) (hp : p.Prime) :
    padicValNat p ((m + k)! / m !) ≤
      padicValNat p k ! + (Finset.Icc 1 k).sup fun i => padicValNat p (m + i) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← ascFactorial_eq_div, ascFactorial_eq_factorial_mul_choose]
  simp only [padicValNat_def]
  rw [Nat.multiplicity_mul (factorial_ne_zero _) (choose_ne_zero (Nat.le_add_left k m))]
  apply Nat.add_le_add_left
  rw [multiplicity_choose' (Nat.lt_succ_self (log p (m + k)))]
  let M := (Icc 1 k).sup fun i => multiplicity p (m + i)
  calc
    _ ≤ (Icc 1 M).card := by
      apply card_le_card
      intro j hj
      obtain ⟨hj, hcarry⟩ := mem_filter.mp hj
      refine mem_Icc.mpr ⟨(mem_Ico.mp hj).1, ?_⟩
      -- A carry at this power puts the next multiple of it in the interval.
      let q := p ^ j
      let i := q - m % q
      have hrem : m % q < q := Nat.mod_lt _ (pow_pos hp.pos _)
      have hi : 0 < i := Nat.sub_pos_of_lt hrem
      have hik : i ≤ k := (Nat.sub_le_iff_le_add.mpr hcarry).trans (Nat.mod_le _ _)
      have hdvd : q ∣ m + i := by
        refine ⟨m / q + 1, ?_⟩
        rw [Nat.mul_add_one]
        dsimp [i]
        have := Nat.mod_add_div m q
        omega
      exact ((Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by omega : m + i ≠ 0)).mp hdvd).trans
        (le_sup (f := fun i => multiplicity p (m + i)) (mem_Icc.mpr ⟨hi, hik⟩))
    _ = M := by simp

end MetaMathlibExt

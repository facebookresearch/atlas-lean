/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# A binomial sum for the Schreier parent sequence

The binomial sum has the initial values and recurrence of `schreierParentD`. In the
recurrence, shifting the positive summands aligns both smaller upper indices for Pascal's rule.

## References

* Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
  Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
  [Article A53](https://math.colgate.edu/~integers/aa53/aa53.pdf), pp. 1–24,
  Section 4, Proposition 2 (pp. 13–15).
-/

namespace MetaMathlibExt

/-- **The parent sequence $d_{u,n}$.** For natural numbers $u$ and $n$, define $d_{u,n}$ by
recursion on $n$: $d_{u,n} = 1$ if $n < 2u$ or $u = 0$, and otherwise
$d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}$.

The paper takes $u \ge 2$ and indexes from $n = 1$, with $d_{u,n} = 1$ for $1 \le n \le 2u - 1$;
here $d_{u,0} = 1$ as well, and the degenerate case $u = 0$ is set to $1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4 (definition of `d_{u,n}`). -/
@[expose] public def schreierParentD (u : ℕ) (n : ℕ) : ℕ :=
  if _h : n < 2 * u ∨ u = 0 then 1
  else schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1)
decreasing_by all_goals omega

private def parentDTerm (u n i : ℕ) : ℕ :=
  ((n + (u - 1) * i - u) / (2 * u - 1)).choose i

private theorem parentDTerm_zero (u n : ℕ) : parentDTerm u n 0 = 1 :=
  Nat.choose_zero_right _

-- A positive index can contribute only once the numerator reaches (2u - 1) * i.
private theorem parentDTerm_eq_zero {u n i : ℕ} (hu : 2 ≤ u) (hi : 0 < i)
    (h : n < u * (i + 1)) : parentDTerm u n i = 0 := by
  apply Nat.choose_eq_zero_of_lt
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * u - 1)).mpr
  rw [show 2 * u - 1 = u - 1 + u by omega, Nat.mul_add i, Nat.mul_comm i (u - 1),
    Nat.mul_comm i u]
  rw [Nat.mul_succ] at h
  have hpos := Nat.mul_pos (show 0 < u by omega) hi
  omega

private theorem parentDTerm_succ {u n : ℕ} (hu : 2 ≤ u) (hn : 2 * u ≤ n) (i : ℕ) :
    parentDTerm u n (i + 1) =
      parentDTerm u (n - u) i + parentDTerm u (n - 2 * u + 1) (i + 1) := by
  unfold parentDTerm
  rw [Nat.mul_succ]
  -- With n ≥ 2u the two smaller numerators agree, and neither truncates.
  have h₁ : n + ((u - 1) * i + (u - 1)) - u =
      (n - u + (u - 1) * i - u) + (2 * u - 1) := by omega
  have h₂ : n - 2 * u + 1 + ((u - 1) * i + (u - 1)) - u =
      n - u + (u - 1) * i - u := by omega
  rw [h₁, h₂, Nat.add_div_right _ (by omega : 0 < 2 * u - 1), Nat.choose_succ_succ']

-- A common upper bound lets both induction hypotheses use the same range.
private theorem parentD_eq_sum_range {u n b : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n)
    (hb : n ≤ u * (b + 1)) :
    schreierParentD u n = ∑ i ∈ Finset.range (b + 1), parentDTerm u n i := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hsmall : n < 2 * u
    · have hsum : ∑ i ∈ Finset.range b, parentDTerm u n (i + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply parentDTerm_eq_zero hu (Nat.succ_pos i)
        rw [Nat.mul_succ, Nat.mul_succ]
        omega
      rw [schreierParentD, Finset.sum_range_succ', parentDTerm_zero, hsum]
      simp [hsmall]
    · have hlarge : 2 * u ≤ n := Nat.le_of_not_gt hsmall
      have hrec : schreierParentD u n =
          schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1) := by
        rw [schreierParentD]
        simp [hsmall, show u ≠ 0 by omega]
      rw [hrec, ih (n - u) (by omega) (by omega) (by omega),
        ih (n - 2 * u + 1) (by omega) (by omega) (by omega)]
      have hbpos : 0 < b := Nat.pos_of_ne_zero fun hbzero => by
        subst b
        simp only [Nat.zero_add, Nat.mul_one] at hb
        omega
      have hlast := parentDTerm_eq_zero hu hbpos (show n - u < u * (b + 1) by omega)
      rw [Finset.sum_range_succ (parentDTerm u (n - u)) b, hlast, add_zero,
        Finset.sum_range_succ' (parentDTerm u (n - 2 * u + 1)) b,
        Finset.sum_range_succ' (parentDTerm u n) b]
      simp only [parentDTerm_zero, parentDTerm_succ hu hlarge, Finset.sum_add_distrib]
      ac_rfl

/-- **Binomial sum formula for the parent sequence.** For all natural numbers $u \ge 2$ and
$n \ge 1$, the parent sequence $d_{u,n}$ satisfies
$$
d_{u,n} = \sum_{i=0}^{\lfloor (n-1)/u \rfloor} \binom{\lfloor (n + (u-1)i - u)/(2u-1) \rfloor}{i}.
$$

The numerator $n + (u-1)i - u$ is negative only when $i = 0$ and $n < u$. There it is read as
$0$ (truncated subtraction), so the term is $\binom{0}{0} = 1$, which agrees with the paper's
$\binom{-1}{0} = 1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 2 (`integers-2026-A53-prop-2`). -/
public theorem schreierParentD_eq_sum_choose {u n : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n) :
    schreierParentD u n =
      ∑ i ∈ Finset.range ((n - 1) / u + 1), ((n + (u - 1) * i - u) / (2 * u - 1)).choose i := by
  apply parentD_eq_sum_range hu hn
  have h : n - 1 < u * ((n - 1) / u + 1) := by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < u)).mp (Nat.lt_succ_self _)
  omega

end MetaMathlibExt

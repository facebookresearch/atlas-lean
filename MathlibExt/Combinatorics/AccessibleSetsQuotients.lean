/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AccessibleSets

/-!
# Integral quotients of accessible sets

Pull a coloring back along the positive block quotient. After restricting the gaps to
multiples of the divisor, taking quotients divides each gap exactly.

## References

* Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
  pp. 1–23, Theorem 11(i) (pp. 5–6), using the divisible subset in Theorem 11(ii) (p. 6).

Quester credits the following antecedents to Theorem 11:

* Bruce M. Landman, Aaron Robertson and Quinn Robertson,
  *Ramsey properties for integer sequences with restricted gaps*, Moscow Journal of Combinatorics
  and Number Theory 12 (2023), no. 3, pp. 181–195 (the even Fibonacci case).
* William J. Wesley, *Improved Ramsey-type theorems for Fibonacci numbers and other sequences*,
  INTEGERS 25 (2025), Article A29, pp. 1–17, Corollary 2 (p. 9, the divisor-two rounding argument).
-/

namespace MetaMathlibExt

/-- **Integral quotients of an accessible set.** Let $d \ge 1$ and $r$ be natural numbers and let
$A$ be a set of natural numbers. If $A$ is $rd$-accessible, then the set $\{n \ge 1 : nd \in A\}$,
that is, the positive integers of the form $a/d$ with $a \in A$, is $r$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 11(i). -/
public theorem accessible_integral_quotients (A : Set ℕ) (d r : ℕ)
    (hd : 0 < d) (hA : IsRAccessible (r * d) A) :
    IsRAccessible r {n : ℕ | 0 < n ∧ ∃ a ∈ A, a = n * d} := by
  obtain ⟨hpos, hr, hseq⟩ := accessible_divisible_subset A d r hd hA
  refine ⟨fun _ h ↦ h.1, hr, ?_⟩
  intro c k hk
  -- The first block, 1 through d, must also have a positive quotient.
  let q (t : ℕ+) : ℕ+ := ⟨((t : ℕ) - 1) / d + 1, Nat.succ_pos _⟩
  obtain ⟨x, hmono, hdiff⟩ := hseq (fun t ↦ c (q t)) k hk
  refine ⟨fun i ↦ q (x i), hmono, ?_⟩
  intro i hi
  let u := x ⟨i, by omega⟩
  let v := x ⟨i + 1, hi⟩
  obtain ⟨a, ha, hgap⟩ := hdiff i hi
  change (v : ℤ) - (u : ℤ) = a at hgap
  obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero ha.2
  have hbpos : 0 < b := by
    have ha' : 0 < a := hpos ha
    rw [hb] at ha'
    exact Nat.pos_of_mul_pos_left ha'
  have huv : (v : ℕ) = (u : ℕ) + d * b := by
    rw [hb] at hgap
    exact_mod_cast (sub_eq_iff_eq_add'.mp hgap)
  have hshift : (v : ℕ) - 1 = ((u : ℕ) - 1) + d * b := by
    have := u.pos
    omega
  -- The divisible gaps keep the shifted residues fixed, so taking floors preserves the gap / d.
  have hq : (q v : ℕ) = (q u : ℕ) + b := by
    change ((v : ℕ) - 1) / d + 1 = ((u : ℕ) - 1) / d + 1 + b
    rw [hshift, Nat.add_mul_div_left _ _ hd, Nat.add_right_comm]
  refine ⟨b, ⟨hbpos, a, ha.1, hb.trans (Nat.mul_comm d b)⟩, ?_⟩
  change (q v : ℤ) - (q u : ℤ) = b
  exact sub_eq_iff_eq_add'.mpr (by exact_mod_cast hq)

end MetaMathlibExt

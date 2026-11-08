/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.Radical.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Longest arithmetic progressions in the reduced residue systems `R_m(n)`

For integers `m` and `n > 1`, Phothila, Thoket and Kanasri study the reduced residue system
`R_m(n) = {a ∈ ℤ | m + 1 ≤ a ≤ m + n, gcd(a, n) = 1}` modulo `n`, the length `f_m(n)` of the
longest arithmetic progressions contained in it, the length `f_m(d, n)` of the longest ones
with common difference `d`, and `g(n) = f_{-⌈n/2⌉}(n)` for the system of absolute least
reduced residues. Throughout, `gpf(n)` is written `n.primeFactors.sup id` (the largest prime
factor of `n` for `n > 1`) and `rad(n)` is `UniqueFactorizationMonoid.radical n`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

@[expose] public section

open UniqueFactorizationMonoid

/-- The reduced residue system `R_m(n) = {a ∈ ℤ | m + 1 ≤ a ≤ m + n, gcd(a, n) = 1}` modulo `n`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public def reducedResidueWindow (m : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (m + 1) (m + n)).filter fun a => Int.gcd a n = 1

/-- `f_m(d, n)`: the length of the longest arithmetic progressions with common difference `d`
contained in `R_m(n)`. The paper uses it for `d > 0`, where the set of lengths is bounded by
`n` (`apLength_le`).

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 2. -/
public noncomputable def longestAPLengthWithDiff (m : ℤ) (n d : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- `f_m(n)`: the length of the longest arithmetic progressions (positive common difference;
a single term counts as a progression of length `1`) contained in `R_m(n)`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def longestAPLength (m : ℤ) (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∃ d : ℕ, 0 < d ∧ ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- `g(n) = f_{-⌈n/2⌉}(n)`: the length of the longest arithmetic progressions contained in the
system `R(n) = R_{-⌈n/2⌉}(n)` of absolute least reduced residues modulo `n`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def absLeastAPLength (n : ℕ) : ℕ :=
  longestAPLength (-⌈(n : ℚ) / 2⌉) n

/-- An arithmetic progression with positive common difference inside `R_m(n)` has at most `n`
terms.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (`R_m(n) ⊆ [m + 1, m + n]`). -/
public theorem apLength_le {m b : ℤ} {n d s : ℕ} (hd : 0 < d)
    (h : ∀ i < s, b + i * d ∈ reducedResidueWindow m n) : s ≤ n := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Nat.zero_le _
  have h0 := h 0 hs
  have h1 := h (s - 1) (by omega)
  simp only [reducedResidueWindow, Finset.mem_filter, Finset.mem_Icc] at h0 h1
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hs' : ((s - 1 : ℕ) : ℤ) ≤ ((s - 1 : ℕ) : ℤ) * d :=
    le_mul_of_one_le_right (by positivity) hd'
  have : ((s - 1 : ℕ) : ℤ) ≤ n - 1 := by
    have := h0.1.1; have := h1.1.2; push_cast at *; linarith
  omega

/-- `f_m(n) ≤ n`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (`R_m(n)` has at most `n`
elements). -/
public theorem longestAPLength_le (m : ℤ) (n : ℕ) : longestAPLength m n ≤ n :=
  csSup_le' fun _ ⟨_, _, hd, h⟩ => apLength_le hd h

/-- `R(5) = R_{-3}(5) = {-2, -1, 1, 2}`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Example 1(i). -/
public theorem mem_reducedResidueWindow_neg_three_five (a : ℤ) :
    a ∈ reducedResidueWindow (-3) 5 ↔ a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by
  simp only [reducedResidueWindow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    norm_num at h1 h2
    interval_cases a <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> decide

/-- `g(5) = 2`.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Example 1(i). -/
public theorem absLeastAPLength_five : absLeastAPLength 5 = 2 := by
  have hc : (-⌈((5 : ℕ) : ℚ) / 2⌉ : ℤ) = -3 := by
    rw [neg_inj, Int.ceil_eq_iff]; norm_num
  unfold absLeastAPLength longestAPLength
  rw [hc]
  apply le_antisymm
  · apply csSup_le'
    rintro s ⟨b, d, hd, h⟩
    by_contra hs
    have h0 := (mem_reducedResidueWindow_neg_three_five _).1 (h 0 (by omega))
    have h1 := (mem_reducedResidueWindow_neg_three_five _).1 (h 1 (by omega))
    have h2 := (mem_reducedResidueWindow_neg_three_five _).1 (h 2 (by omega))
    push_cast at h0 h1 h2
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    omega
  · refine le_csSup ⟨5, fun s ⟨b, d, hd, h⟩ => apLength_le hd h⟩ ⟨-2, 1, one_pos, ?_⟩
    intro i hi
    rw [mem_reducedResidueWindow_neg_three_five]
    interval_cases i <;> norm_num

/-- Lemma 1(i): if a prime `p` divides `n` but not `d > 0`, then `f_m(d, n) ≤ p - 1`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(i) (`integers-2026-A6-lem-1`). -/
public theorem_wanted longestAPLengthWithDiff_le_prime_sub_one (m : ℤ) {n d p : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hp : p.Prime) (hpn : p ∣ n) (hpd : ¬ p ∣ d) :
    longestAPLengthWithDiff m n d ≤ p - 1

/-- Lemma 1(ii): if `n > 1` is squarefree and `d > 0`, then `f_m(d, n) ≤ gpf(n) - 1`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(ii) (`integers-2026-A6-lem-1`). -/
public theorem_wanted longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree (m : ℤ) {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hsq : Squarefree n) :
    longestAPLengthWithDiff m n d ≤ n.primeFactors.sup id - 1

/-- Theorem 1, prime case `p ≡ 1 (mod 4)`: `g(p) = (p - 1) / 2`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) : absLeastAPLength p = (p - 1) / 2

/-- Theorem 1, prime case `p ≡ 3 (mod 4)`: `g(p) = (p + 1) / 2`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 3) : absLeastAPLength p = (p + 1) / 2

/-- Theorem 1, prime-power cases: `g(p ^ r) = p ^ (r - 1)` for an odd prime `p` and `r > 1`, and
for `p = 2` and `r ≥ 1`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : absLeastAPLength (p ^ r) = p ^ (r - 1)

/-- Theorem 1, odd squarefree non-prime `n`: with `P = gpf(n)` and `d = n / P`,
`g(n) = ⌊P - (P + 1) / (2d)⌋`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_odd_squarefree {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hsq : Squarefree n) (hnp : ¬ n.Prime) :
    (absLeastAPLength n : ℤ) =
      ⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        ((n.primeFactors.sup id : ℕ) + 1) / (2 * ((n / n.primeFactors.sup id : ℕ) : ℚ))⌋

/-- Theorem 1, `n = 2p` with `p` an odd prime: `g(2p) = p - 1`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    absLeastAPLength (2 * p) = p - 1

/-- Theorem 1, `n` neither a prime power nor squarefree (odd or even):
`g(n) = max(n / rad(n), gpf(n) - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_of_not_squarefree_of_not_isPrimePow {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    absLeastAPLength n = max (n / radical n) (n.primeFactors.sup id - 1)

/-- Theorem 1, Equation (3) and the "in particular" clause: for an even squarefree `n` with at
least three prime factors, `P = gpf(n)` and `d = n / P`,
`⌊P - 2P / d⌋ ≤ g(n) ≤ P - 1`, and `g(n) = P - 1` when `d ≥ 2P`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_even_squarefree_bounds {n : ℕ} (heven : Even n)
    (hsq : Squarefree n) (h3 : 3 ≤ n.primeFactors.card) :
    (⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        2 * (n.primeFactors.sup id : ℕ) / ((n / n.primeFactors.sup id : ℕ) : ℚ)⌋ ≤
        (absLeastAPLength n : ℤ) ∧
      absLeastAPLength n ≤ n.primeFactors.sup id - 1) ∧
    (2 * n.primeFactors.sup id ≤ n / n.primeFactors.sup id →
      absLeastAPLength n = n.primeFactors.sup id - 1)

/-- Theorem 2: for `n > 1`, `max_{m ∈ ℤ} f_m(n) = max(n / rad(n), gpf(n) - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 2 (`integers-2026-A6-thm-2`). -/
public theorem_wanted isGreatest_longestAPLength {n : ℕ} (hn : 1 < n) :
    IsGreatest (Set.range fun m : ℤ => longestAPLength m n)
      (max (n / radical n) (n.primeFactors.sup id - 1))

/-- Theorem 3, prime case `p ≡ 1 (mod 4)`: `min_{m ∈ ℤ} f_m(p) = (p - 1) / 2`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p - 1) / 2)

/-- Theorem 3, prime case `p ≡ 3 (mod 4)`: `min_{m ∈ ℤ} f_m(p) = (p + 1) / 2`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 3) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p + 1) / 2)

/-- Theorem 3, prime-power case: for a prime `p` and `r > 1`, `min_{m ∈ ℤ} f_m(p ^ r) = p ^ (r - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 < r) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m (p ^ r)) (p ^ (r - 1))

/-- Theorem 3, `n` neither squarefree nor a prime power:
`n / rad(n) ≤ min_{m ∈ ℤ} f_m(n) ≤ max(n / rad(n), gpf(n) - 1)`, and the minimum equals
`n / rad(n)` when `n / rad(n) ≥ gpf(n) - 1`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted longestAPLength_min_of_not_squarefree_of_not_isPrimePow {n : ℕ}
    (hn : 1 < n) (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    ((∀ m : ℤ, n / radical n ≤ longestAPLength m n) ∧
      ∃ m : ℤ, longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1)) ∧
    (n.primeFactors.sup id - 1 ≤ n / radical n →
      IsLeast (Set.range fun m : ℤ => longestAPLength m n) (n / radical n))

/-- Corollary 1: for a non-squarefree `n` with `n / rad(n) ≥ gpf(n) - 1`,
`(1 / n) ∑_{m=0}^{n-1} f_m(n) = n / rad(n)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Corollary 1 (`integers-2026-A6-cor-1`). -/
public theorem_wanted average_longestAPLength_of_not_squarefree {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    (1 / (n : ℚ)) * ∑ m ∈ Finset.range n, (longestAPLength m n : ℚ) = (n : ℚ) / radical n

end

end MetaMathlibExt

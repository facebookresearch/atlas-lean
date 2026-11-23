/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.IntervalCases

/-!
# Lengths of arithmetic progressions in reduced residue systems

For a squarefree modulus, the largest prime factor bounds the length of a progression
with fixed positive difference in any reduced residue window.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The reduced residue system $R_m(n)$.** For an integer $m$ and a natural number $n$, the
reduced residue system $R_m(n)$ modulo $n$ is the finite set
$R_m(n) = \{a \in \mathbb{Z} : m + 1 \le a \le m + n,\ \gcd(a, n) = 1\}$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public def reducedResidueWindow (m : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (m + 1) (m + n)).filter fun a => Int.gcd a n = 1

/-- **Longest progression with a given common difference.** For an integer $m$ and natural numbers
$n$ and $d$, let $R_m(n)$ be the set of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(d, n)$ is the supremum of the natural numbers $s$ for which some
integer $b$ has $b + i d \in R_m(n)$ for every natural number $i < s$. For $d > 0$ every such $s$
is at most $n$, so $f_m(d, n)$ is the length of the longest arithmetic progression with common
difference $d$ contained in $R_m(n)$; the paper uses it only for $d > 0$, and for $d = 0$ the
definition gives $0$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 2. -/
public noncomputable def longestAPLengthWithDiff (m : ℤ) (n d : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- **Length of the longest arithmetic progression in a reduced residue system.** For an
integer $m$ and a natural number $n$, let $R_m(n)$ be the reduced residue system of the
integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then $f_m(n)$ is the largest
natural number $s$ for which there are an integer $b$ and a positive integer $d$ such that
$b, b + d, \dots, b + (s - 1)d$ all lie in $R_m(n)$. So it is the length of the longest
arithmetic progression with positive common difference contained in $R_m(n)$, where a single
term counts as a progression of length $1$, and $f_m(n) = 0$ when $R_m(n)$ is empty.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def longestAPLength (m : ℤ) (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ b : ℤ, ∃ d : ℕ, 0 < d ∧ ∀ i < s, b + i * d ∈ reducedResidueWindow m n}

/-- **Longest progression in the absolute least reduced residues.** For a natural number $n$,
let $R(n)$ be the set of integers $a$ with $1 - \lceil n/2 \rceil \le a \le n - \lceil n/2 \rceil$
and $\gcd(a, n) = 1$, the system of absolute least reduced residues modulo $n$. Then $g(n)$ is
the largest $s \ge 0$ for which there are an integer $b$ and a positive integer $d$ with
$b + i d \in R(n)$ for every $0 \le i < s$: the length of the longest arithmetic progression
with positive common difference contained in $R(n)$. Equivalently,
$g(n) = f_{-\lceil n/2 \rceil}(n)$, where $f_m(n)$ is the same length for the set
$R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 1. -/
public noncomputable def absLeastAPLength (n : ℕ) : ℕ :=
  longestAPLength (-⌈(n : ℚ) / 2⌉) n

/-- **Length bound for progressions in a reduced residue window.** Let $m$ be an integer and $n$
a natural number, and let $R_m(n)$ be the set of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. If $b$ is an integer, $d$ a positive integer and $s$ a natural number such
that $b + i d \in R_m(n)$ for every $0 \le i < s$, then $s \le n$.

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

/-- **The longest progression length is at most the modulus.** For every integer $m$ and natural
number $n$, $f_m(n) \le n$, where $f_m(n)$ is the length of the longest arithmetic progression
with positive common difference contained in the set $R_m(n)$ of integers $a$ with
$m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (`R_m(n)` has at most `n`
elements). -/
public theorem longestAPLength_le (m : ℤ) (n : ℕ) : longestAPLength m n ≤ n :=
  csSup_le' fun _ ⟨_, _, hd, h⟩ => apLength_le hd h

/-- **The reduced residue system $R_{-3}(5)$.** The reduced residue system $R_{-3}(5)$ of the
integers $a$ with $-2 \le a \le 2$ and $\gcd(a, 5) = 1$ is $\{-2, -1, 1, 2\}$: an integer $a$
lies in $R_{-3}(5)$ if and only if $a$ is one of $-2$, $-1$, $1$, $2$.

Since $\lceil 5/2 \rceil = 3$, this is the system $R(5) = R_{-\lceil 5/2 \rceil}(5)$ of absolute
least reduced residues modulo $5$.

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

/-- **Longest progressions of absolute least residues modulo 5.** The length $g(5)$ of the
longest arithmetic progression in the absolute least reduced residue system modulo $5$ is $2$.

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

private theorem exists_dvd_progression_term (b : ℤ) {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    ∃ i : ℕ, i < p ∧ (p : ℤ) ∣ b + i * d := by
  let : Fact p.Prime := ⟨hp⟩
  let x := -(b : ZMod p) / (d : ZMod p)
  have hd : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.natCast_eq_zero_iff ..).mp h)
  refine ⟨x.val, x.val_lt, (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hd, add_neg_cancel]

/-- **Squarefree bound for progressions with a fixed difference.** Let $m$ be an integer, $n > 1$
a squarefree natural number with largest prime factor $\operatorname{gpf}(n)$, and $d > 0$ a
natural number. Then $f_m(d, n) \le \operatorname{gpf}(n) - 1$, where $f_m(d, n)$ is the length of
the longest arithmetic progression with common difference $d$ contained in the set $R_m(n)$ of
integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(ii) (`integers-2026-A6-lem-1`). -/
public theorem longestAPLengthWithDiff_le_gpf_sub_one_of_squarefree (m : ℤ) {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hsq : Squarefree n) :
    longestAPLengthWithDiff m n d ≤ n.primeFactors.sup id - 1 := by
  apply csSup_le'
  rintro s ⟨b, h⟩
  by_cases hsub : n.primeFactors ⊆ d.primeFactors
  · have hnd := (Nat.prod_primeFactors_dvd_iff hd.ne').mpr hsub
    rw [Nat.prod_primeFactors_of_squarefree hsq] at hnd
    have hle := Nat.le_of_dvd hd hnd
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
    have hp₂ := (Nat.prime_of_mem_primeFactors hp).two_le
    have hmax : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hp
    have hs : s ≤ 1 := by
      by_contra! hs
      have h₀ := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h 0 (by omega))).1).1
      have h₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h 1 hs)).1).2
      simp at h₀ h₁
      omega
    omega
  · obtain ⟨p, hpn, hpd⟩ := Finset.not_subset.mp hsub
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hmax : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hpn
    obtain ⟨i, hip, hdiv⟩ := exists_dvd_progression_term b hp
      (fun h => hpd (hp.mem_primeFactors h hd.ne'))
    have hsi : s ≤ i := by
      by_contra! hi
      have hgcd := (Finset.mem_filter.mp (h i hi)).2
      have hcommon := Int.dvd_coe_gcd hdiv
        (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors hpn))
      rw [hgcd] at hcommon
      exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hcommon)
    omega

end

end MetaMathlibExt

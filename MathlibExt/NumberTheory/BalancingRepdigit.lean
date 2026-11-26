/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Periodic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Balancing numbers and decimal repdigits

Among Lucas-balancing numbers, only 17 and 577 have exactly two runs of equal decimal digits.
The proof compares the recurrence and the two blocks modulo 24640 and 79424.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Balancing numbers.** The balancing numbers are the integers $B_n$ for $n \in \mathbb{N}$
defined by $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 6 B_{n+1} - B_n$ for all $n$.

Source: standard definition used in "Balancing and Lucas-Balancing Numbers as
the Difference of Two Repdigits" (Integers 2025, A15); the values
`B_2 = 6`, `B_3 = 35` are those displayed in its Theorem 2. -/
public def balancingNum : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * balancingNum (n + 1) - balancingNum n

/-- **The balancing number $B_2$ is $6$.** The balancing number $B_2$ equals $6$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_two : balancingNum 2 = 6 := rfl

/-- **The balancing number $B_3$ is $35$.** The balancing number $B_3$ equals $35$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem balancingNum_three : balancingNum 3 = 35 := rfl

/-- **Lucas-balancing numbers (shifted indexing).** The shifted sequence $(L_n)_{n \ge 0}$ has
$L_0 = 3$, $L_1 = 1$ and $L_{n+2} = 6L_{n+1} - L_n$.

Section 1 of Mohapatra, Bhoi and Panda defines the standard sequence by $C_0 = 1$, $C_1 = 3$
and the same recurrence. Thus `lucasBalancingNum (n + 1)` equals $C_n$ for every $n \ge 0$.
Their Theorem 3 lists the shifted values $L_2 = 3$ and $L_3 = 17$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public def lucasBalancingNum : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | n + 2 => 6 * lucasBalancingNum (n + 1) - lucasBalancingNum n

/-- **The Lucas-balancing number $C_2$ is $3$.** For the Lucas-balancing numbers defined by
$C_0 = 3$, $C_1 = 1$ and $C_{n+2} = 6C_{n+1} - C_n$, we have $C_2 = 3$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_two : lucasBalancingNum 2 = 3 := rfl

/-- **The Lucas-balancing number $C_3$ is $17$.** For the Lucas-balancing numbers defined by
$C_0 = 3$, $C_1 = 1$ and $C_{n+2} = 6C_{n+1} - C_n$, we have $C_3 = 17$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3. -/
public theorem lucasBalancingNum_three : lucasBalancingNum 3 = 17 := rfl

/-- **Decimal repdigits.** A natural number $n$ is a repdigit if there are natural numbers $d$
and $m$ with $1 \le d \le 9$ and $m \ge 1$ such that $9n = d(10^m - 1)$. Equivalently, $n$ is
the positive integer whose decimal expansion consists of $m$ copies of the digit $d$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public def IsRepdigit (n : ℕ) : Prop :=
  ∃ d m : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ m ∧ 9 * n = d * (10 ^ m - 1)

/-- **Eleven is a repdigit.** The number $11$ is a repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigit_eleven : IsRepdigit 11 :=
  ⟨1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Nonzero single digits are repdigits.** Every natural number $d$ with $1 \le d \le 9$ is a
repdigit.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Section 1 (definition of repdigit). -/
public theorem isRepdigit_of_le (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ 9) :
    IsRepdigit d :=
  ⟨d, 1, h1, h2, le_rfl, by ring⟩

/-- **Concatenations of two decimal repdigits.** A natural number $n$ is a concatenation of two
repdigits if there are digits $d_1, d_2$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$ and
$d_1 \ne d_2$, and block lengths $m_1, m_2 \ge 1$, such that the decimal expansion of $n$ is
$m_1$ copies of $d_1$ followed by $m_2$ copies of $d_2$; that is,
$9n = d_1 (10^{m_1} - 1) 10^{m_2} + d_2 (10^{m_2} - 1)$. Equivalently, the decimal expansion of
$n$ has exactly two runs of equal digits.

Because of the condition $d_1 \ne d_2$, a repdigit such as $99$ is not a concatenation of two
repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 3 and 5. -/
public def IsConcatTwoRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ m₁ m₂ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ d₁ ≠ d₂ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ m₂ + d₂ * (10 ^ m₂ - 1)

/-- **Concatenations of three decimal repdigits.** A natural number $n$ is a concatenation of
three repdigits if there are digits $d_1, d_2, d_3$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$,
$0 \le d_3 \le 9$, $d_1 \ne d_2$ and $d_2 \ne d_3$, and block lengths $m_1, m_2, m_3 \ge 1$, such
that the decimal expansion of $n$ is $m_1$ copies of $d_1$, then $m_2$ copies of $d_2$, then $m_3$
copies of $d_3$; that is,
$$9n = d_1 (10^{m_1} - 1) 10^{m_2 + m_3} + d_2 (10^{m_2} - 1) 10^{m_3} + d_3 (10^{m_3} - 1).$$
Equivalently, the decimal expansion of $n$ has exactly three runs of equal digits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 4 and 6. -/
public def IsConcatThreeRepdigits (n : ℕ) : Prop :=
  ∃ d₁ d₂ d₃ m₁ m₂ m₃ : ℕ, 1 ≤ d₁ ∧ d₁ ≤ 9 ∧ d₂ ≤ 9 ∧ d₃ ≤ 9 ∧
    1 ≤ m₁ ∧ 1 ≤ m₂ ∧ 1 ≤ m₃ ∧ d₁ ≠ d₂ ∧ d₂ ≠ d₃ ∧
    9 * n = d₁ * (10 ^ m₁ - 1) * 10 ^ (m₂ + m₃) + d₂ * (10 ^ m₂ - 1) * 10 ^ m₃ +
      d₃ * (10 ^ m₃ - 1)

/-- **$35$ is a concatenation of two repdigits.** The number $35$, whose decimal expansion consists
of the one-digit blocks $3$ and $5$, is a concatenation of two repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3. -/
public theorem isConcatTwoRepdigits_thirtyFive : IsConcatTwoRepdigits 35 :=
  ⟨3, 5, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- **$204$ is a concatenation of three repdigits.** The number $204$, whose decimal expansion
consists of the one-digit blocks $2$, $0$ and $4$, is a concatenation of three repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4. -/
public theorem isConcatThreeRepdigits_twoZeroFour : IsConcatThreeRepdigits 204 :=
  ⟨2, 0, 4, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Differences of two repdigits.** A natural number $n$ is a difference of two repdigits if
there are repdigits $a$ and $b$ with $a = n + b$, that is, $n = a - b$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorems 2 and 3. -/
public def IsRepdigitDiff (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsRepdigit a ∧ IsRepdigit b ∧ a = n + b

/-- **Six is a difference of two repdigits.** The number $6$ is a difference of two repdigits:
$6 = 11 - 5$, where $11$ and $5$ are repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2. -/
public theorem isRepdigitDiff_six : IsRepdigitDiff 6 :=
  ⟨11, 5, isRepdigit_eleven, isRepdigit_of_le 5 (by norm_num) (by norm_num),
    rfl⟩

namespace lucasBalancingNum_concatTwoRepdigits

/-- Compute consecutive terms together to avoid branching recursion in the finite checks. -/
private def pair : ℕ → ℤ × ℤ
  | 0 => (3, 1)
  | n + 1 => let (x, y) := pair n; (y, 6 * y - x)

private theorem pair_eq (n : ℕ) :
    pair n = (lucasBalancingNum n, lucasBalancingNum (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pair, ih]; rfl

private def residues (M : ℤ) (p : ℕ) : List ℤ :=
  (List.range p).map fun i => (9 * (pair i).1) % M

/-- Checking that the initial pair returns suffices to certify a period of the recurrence. -/
private theorem mem_residues {M : ℤ} {p : ℕ} (hp : 0 < p)
    (h : (pair p).1 ≡ 3 [ZMOD M] ∧ (pair p).2 ≡ 1 [ZMOD M]) (k : ℕ) :
    (9 * lucasBalancingNum k) % M ∈ residues M p := by
  have step (n : ℕ) : (pair (n + p)).1 ≡ (pair n).1 [ZMOD M] ∧
      (pair (n + p)).2 ≡ (pair n).2 [ZMOD M] := by
    induction n with
    | zero => simpa only [Nat.zero_add, pair] using h
    | succ n ih =>
      rw [Nat.succ_add]
      exact ⟨ih.2, (ih.2.mul_left 6).sub ih.1⟩
  have per : Function.Periodic (fun n => (9 * (pair n).1) % M) p :=
    fun n => ((step n).1.mul_left 9).eq
  exact List.mem_map.mpr ⟨k % p, List.mem_range.mpr (Nat.mod_lt _ hp),
    (per.map_mod_nat k).trans (by simp only [pair_eq])⟩

/-- Beyond the sixth digit, powers of ten are periodic modulo each sieve modulus. -/
private theorem power_representative {M : ℤ} {p : ℕ} (hp : 0 < p)
    (h : (10 : ℤ) ^ (6 + p) ≡ 10 ^ 6 [ZMOD M]) {m : ℕ} (hm : 0 < m) :
    ∃ i < 6 + p, 0 < i ∧ (i < 6 → m = i) ∧ (10 : ℤ) ^ m ≡ 10 ^ i [ZMOD M] := by
  by_cases hs : m < 6
  · exact ⟨m, by omega, hm, fun _ => rfl, .rfl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hs)
  have per : Function.Periodic (fun n : ℕ => (10 : ℤ) ^ (6 + n) % M) p := by
    intro j
    change (10 : ℤ) ^ (6 + (j + p)) ≡ 10 ^ (6 + j) [ZMOD M]
    rw [show 6 + (j + p) = 6 + p + j by omega, pow_add _ (6 + p) j, pow_add _ 6 j]
    exact h.mul_right _
  exact ⟨6 + n % p, Nat.add_lt_add_left (Nat.mod_lt _ hp) _, by omega, by omega,
    (per.map_mod_nat n).symm⟩

/-- Nine times the concatenation with digits `a`, `b` and block lengths `i`, `j`. -/
private def blocks (a b i j : ℕ) : ℤ :=
  a * ((10 : ℤ) ^ i - 1) * 10 ^ j + b * ((10 : ℤ) ^ j - 1)

private theorem blocks_congr {M : ℤ} {m n i j : ℕ} (a b : ℕ)
    (hi : (10 : ℤ) ^ m ≡ 10 ^ i [ZMOD M]) (hj : (10 : ℤ) ^ n ≡ 10 ^ j [ZMOD M]) :
    blocks a b m n ≡ blocks a b i j [ZMOD M] :=
  (((hi.sub_right 1).mul_left a).mul hj).add ((hj.sub_right 1).mul_left b)

/-- The first sieve leaves two small solutions and one family ending in 99. -/
private theorem first_sieve :
    ∀ (a b : Fin 10) (i j : Fin 12),
      0 < a.val → a.val ≠ b.val → 0 < i.val → 0 < j.val →
      blocks a b i j % 24640 ∈ residues 24640 24 →
      (a.val = 1 ∧ b.val = 7 ∧ i.val = 1 ∧ j.val = 1) ∨
      (a.val = 5 ∧ b.val = 7 ∧ i.val = 1 ∧ j.val = 2) ∨ (a.val = 8 ∧ b.val = 9 ∧ j.val = 2) := by
  decide +kernel

/-- The second sieve excludes a block of eights followed by 99. -/
private theorem second_sieve :
    ∀ i < 22, 0 < i → blocks 8 9 i 2 % 79424 ∉ residues 79424 72 := by
  decide +kernel

end lucasBalancingNum_concatTwoRepdigits

open lucasBalancingNum_concatTwoRepdigits in
/-- **Lucas-balancing numbers that are concatenations of two repdigits.** For every natural
number $k$, if the decimal expansion of the Lucas-balancing number $C_k$ consists of exactly two
runs of equal digits, that is, $C_k$ is a block of one repeated digit followed by a block of a
different repeated digit, then $C_k = 17$ or $C_k = 577$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 5 (`integers-2025-A15-lem-5`). -/
public theorem lucasBalancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 17 ∨ lucasBalancingNum k = 577 := by
  obtain ⟨a, b, m, n, ha, ha', hb, hm, hn, hab, heq⟩ := h
  have pos : 0 < (lucasBalancingNum k).toNat := by
    have hpow : 1 < 10 ^ m := Nat.one_lt_pow (by omega) (by decide)
    by_contra! hz
    have : 0 < a * (10 ^ m - 1) * 10 ^ n :=
      Nat.mul_pos (Nat.mul_pos ha (Nat.sub_pos_of_lt hpow)) (by positivity)
    omega
  have eqn : 9 * lucasBalancingNum k = blocks a b m n := by
    unfold blocks
    have hm' : 1 ≤ (10 : ℕ) ^ m := Nat.one_le_pow _ _ (by decide)
    have hn' : 1 ≤ (10 : ℕ) ^ n := Nat.one_le_pow _ _ (by decide)
    have hcast := congrArg (Nat.cast : ℕ → ℤ) heq
    push_cast [Nat.cast_sub hm', Nat.cast_sub hn'] at hcast
    rwa [Int.toNat_of_nonneg (by omega)] at hcast
  obtain ⟨i, hi, hi₀, hmi, hxi⟩ :=
    power_representative (M := 24640) (p := 6) (by decide) (by decide) hm
  obtain ⟨j, hj, hj₀, hnj, hxj⟩ :=
    power_representative (M := 24640) (p := 6) (by decide) (by decide) hn
  have hmem := mem_residues (M := 24640) (p := 24) (by decide) (by decide +kernel) k
  rw [eqn, (blocks_congr a b hxi hxj).eq] at hmem
  rcases first_sieve ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨i, hi⟩ ⟨j, hj⟩ ha hab hi₀ hj₀ hmem with
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [hmi (by decide), hnj (by decide)] at eqn
    norm_num [blocks] at eqn
    omega
  · rw [hmi (by decide), hnj (by decide)] at eqn
    norm_num [blocks] at eqn
    omega
  · obtain rfl := hnj (by decide)
    obtain ⟨l, hl, hl₀, _, hxl⟩ :=
      power_representative (M := 79424) (p := 16) (by decide) (by decide) hm
    have hmem' := mem_residues (M := 79424) (p := 72) (by decide) (by decide +kernel) k
    rw [eqn, (blocks_congr 8 9 hxl (Int.ModEq.rfl (a := (10 : ℤ) ^ 2))).eq] at hmem'
    exact (second_sieve l hl hl₀ hmem').elim

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Shakov's 2-regular divisor-counting sequence

We show that the sequence is nonnegative at positive indices, counts the divisors of
`m ^ 2 + 1` through its fibers, and takes Fibonacci values along Shakov's auxiliary sequence.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

/-- **Shakov's $2$-regular sequence.** The integer sequence $s$ with $s(0) = s(1) = 0$,
$s(2) = s(3) = 1$ and, for every $k \ge 1$, $s(4k) = 2s(2k) - s(k)$,
$s(4k+1) = 2s(2k) + s(2k+1)$, $s(4k+2) = 2s(2k+1) + s(2k)$ and $s(4k+3) = 2s(2k+1) - s(k)$.

The value $s(0)$ plays no role in the recursion; the source's sequence starts at $n = 1$. -/
def shakovSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | n + 4 =>
      if (n + 4) % 4 = 0 then
        2 * shakovSeq (2 * ((n + 4) / 4)) - shakovSeq ((n + 4) / 4)
      else if (n + 4) % 4 = 1 then
        2 * shakovSeq (2 * ((n + 4) / 4)) +
          shakovSeq (2 * ((n + 4) / 4) + 1)
      else if (n + 4) % 4 = 2 then
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) +
          shakovSeq (2 * ((n + 4) / 4))
      else
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) - shakovSeq ((n + 4) / 4)
  termination_by n => n
  decreasing_by all_goals omega

namespace fiber_card

/- We keep the tree label `(d, m)` together with the complementary divisor `e`.
The two child values are `m + d` and `m + e`, so the gaps recover both divisors. -/
private def leftGap (n : ℕ) : ℤ :=
  shakovSeq (2 * n) - shakovSeq n

private def rightGap (n : ℕ) : ℤ :=
  shakovSeq (2 * n + 1) - shakovSeq n

private theorem index_cases (n : ℕ) (hn : 1 ≤ n) :
    n = 1 ∨ (∃ k, 1 ≤ k ∧ n = 2 * k) ∨ (∃ k, 1 ≤ k ∧ n = 2 * k + 1) := by
  by_cases h : n = 1
  · exact Or.inl h
  · by_cases he : n % 2 = 0
    · exact Or.inr (Or.inl ⟨n / 2, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨n / 2, by omega, by omega⟩)

private theorem sequence_steps (k : ℕ) (hk : 1 ≤ k) :
    shakovSeq (4 * k) = 2 * shakovSeq (2 * k) - shakovSeq k ∧
    shakovSeq (4 * k + 1) = 2 * shakovSeq (2 * k) + shakovSeq (2 * k + 1) ∧
    shakovSeq (4 * k + 2) = 2 * shakovSeq (2 * k + 1) + shakovSeq (2 * k) ∧
    shakovSeq (4 * k + 3) = 2 * shakovSeq (2 * k + 1) - shakovSeq k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (4 * k - 4) + 4 = 4 * k := by omega
    rw [← h, shakovSeq.eq_5, h]
    simp [show (4 * k) / 4 = k by omega]
  · have h : (4 * k + 1 - 4) + 4 = 4 * k + 1 := by omega
    rw [← h, shakovSeq.eq_5, h]
    simp [show (4 * k + 1) / 4 = k by omega]
  · have h : (4 * k + 2 - 4) + 4 = 4 * k + 2 := by omega
    rw [← h, shakovSeq.eq_5, h]
    simp [show (4 * k + 2) / 4 = k by omega]
  · have h : (4 * k + 3 - 4) + 4 = 4 * k + 3 := by omega
    rw [← h, shakovSeq.eq_5, h]
    simp [show (4 * k + 3) / 4 = k by omega]

private theorem left_child (k : ℕ) (hk : 1 ≤ k) :
    shakovSeq (2 * k) = shakovSeq k + leftGap k ∧
    leftGap (2 * k) = leftGap k ∧
    rightGap (2 * k) = rightGap k + 2 * shakovSeq k + leftGap k := by
  obtain ⟨h₀, h₁, _, _⟩ := sequence_steps k hk
  unfold leftGap rightGap
  rw [show 2 * (2 * k) = 4 * k by omega, h₀, h₁]
  omega

private theorem right_child (k : ℕ) (hk : 1 ≤ k) :
    shakovSeq (2 * k + 1) = shakovSeq k + rightGap k ∧
    leftGap (2 * k + 1) = leftGap k + 2 * shakovSeq k + rightGap k ∧
    rightGap (2 * k + 1) = rightGap k := by
  obtain ⟨_, _, h₂, h₃⟩ := sequence_steps k hk
  unfold leftGap rightGap
  rw [show 2 * (2 * k + 1) = 4 * k + 2 by omega, h₂,
    show 4 * k + 2 + 1 = 4 * k + 3 by omega, h₃]
  omega

private theorem label_properties (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ shakovSeq n ∧ 0 < leftGap n ∧ 0 < rightGap n ∧
      leftGap n * rightGap n = shakovSeq n ^ 2 + 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases index_cases n hn with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · norm_num [leftGap, rightGap, shakovSeq]
    · obtain ⟨hm, hd, he, hde⟩ := ih k (by omega) hk
      obtain ⟨hm', hd', he'⟩ := left_child k hk
      rw [hm', hd', he']
      refine ⟨by omega, hd, by omega, ?_⟩
      linear_combination hde
    · obtain ⟨hm, hd, he, hde⟩ := ih k (by omega) hk
      obtain ⟨hm', hd', he'⟩ := right_child k hk
      rw [hm', hd', he']
      refine ⟨by omega, by omega, he, ?_⟩
      linear_combination hde

/- Each positive label value has a unique parent. The smaller factor specifies the
branch, and subtracting it from the value gives the parent's value. -/
private theorem existsUnique_label (m : ℕ) (d e : ℤ)
    (hd : 0 < d) (he : 0 < e) (hde : d * e = (m : ℤ) ^ 2 + 1) :
    ∃! n : ℕ, 1 ≤ n ∧ shakovSeq n = (m : ℤ) ∧ leftGap n = d ∧ rightGap n = e := by
  induction m using Nat.strong_induction_on generalizing d e with
  | ind m ih =>
    by_cases hm : m = 0
    · subst m
      have hd' : d = 1 := by
        have h := mul_le_mul_of_nonneg_left (show 1 ≤ e by omega) hd.le
        simp at hde
        omega
      have he' : e = 1 := by simpa [hd'] using hde
      subst d
      subst e
      refine ⟨1, by norm_num [leftGap, rightGap, shakovSeq], ?_⟩
      rintro n ⟨hn, hnm, _, _⟩
      rcases index_cases n hn with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rfl
      · have ⟨ha, hb, _, _⟩ := label_properties k hk
        have := (left_child k hk).1
        omega
      · have ⟨ha, _, hc, _⟩ := label_properties k hk
        have := (right_child k hk).1
        omega
    have hm' : shakovSeq 1 ≠ (m : ℤ) := by
      rw [shakovSeq.eq_2]
      omega
    by_cases hleft : d ≤ (m : ℤ)
    · let p := ((m : ℤ) - d).toNat
      have hp : (p : ℤ) = (m : ℤ) - d := Int.toNat_of_nonneg (by omega)
      have hprod : d * (e - 2 * (m : ℤ) + d) = (p : ℤ) ^ 2 + 1 := by
        rw [hp]
        linear_combination hde
      have he' : 0 < e - 2 * (m : ℤ) + d := by
        by_contra! h
        have := mul_nonpos_of_nonneg_of_nonpos hd.le h
        nlinarith [sq_nonneg (p : ℤ)]
      obtain ⟨k, ⟨hk, hkm, hkd, hke⟩, huniq⟩ := ih p (by omega) d _ hd he' hprod
      obtain ⟨ha, hb, hc⟩ := left_child k hk
      refine ⟨2 * k, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      rintro n ⟨hn, hnm, hnd, hne⟩
      rcases index_cases n hn with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (hm' hnm).elim
      · obtain ⟨ha', hb', hc'⟩ := left_child j hj
        have hjk := huniq j ⟨hj, by omega, by omega, by omega⟩
        rw [hjk]
      · obtain ⟨hj₀, hj₁, _, _⟩ := label_properties j hj
        obtain ⟨ha', hb', _⟩ := right_child j hj
        omega
    · have hright : e ≤ (m : ℤ) := by
        by_contra! h
        have hlarge : ((m : ℤ) + 1) * ((m : ℤ) + 1) ≤ d * e :=
          mul_le_mul (by omega) (by omega) (by omega) hd.le
        have hm_pos : (0 : ℤ) < m := by omega
        nlinarith only [hlarge, hde, hm_pos]
      let p := ((m : ℤ) - e).toNat
      have hp : (p : ℤ) = (m : ℤ) - e := Int.toNat_of_nonneg (by omega)
      have hprod : (d - 2 * (m : ℤ) + e) * e = (p : ℤ) ^ 2 + 1 := by
        rw [hp]
        linear_combination hde
      have hd' : 0 < d - 2 * (m : ℤ) + e := by
        by_contra! h
        have := mul_nonpos_of_nonpos_of_nonneg h he.le
        nlinarith [sq_nonneg (p : ℤ)]
      obtain ⟨k, ⟨hk, hkm, hkd, hke⟩, huniq⟩ := ih p (by omega) _ e hd' he hprod
      obtain ⟨ha, hb, hc⟩ := right_child k hk
      refine ⟨2 * k + 1, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      rintro n ⟨hn, hnm, hnd, hne⟩
      rcases index_cases n hn with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · exact (hm' hnm).elim
      · have ⟨hj₀, _, _, _⟩ := label_properties j hj
        obtain ⟨ha', hb', _⟩ := left_child j hj
        omega
      · obtain ⟨ha', hb', hc'⟩ := right_child j hj
        have hjk := huniq j ⟨hj, by omega, by omega, by omega⟩
        rw [hjk]

end fiber_card

open fiber_card in
/-- **Shakov's sequence counts the divisors of $m^2 + 1$.** Let $s$ be Shakov's $2$-regular
sequence and let $\tau(N)$ denote the number of positive divisors of $N$. Then $s(n) \ge 0$ for
every $n \ge 1$, and for every natural number $m$ the set $\{n \ge 1 : s(n) = m\}$ is finite
and has exactly $\tau(m^2 + 1)$ elements.

This is the coefficientwise form of the identity
$\sum_{m \ge 0} \tau(m^2 + 1) x^m = \sum_{n \ge 1} x^{s(n)}$ of formal power series.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Theorem 4. -/
theorem fiber_card (m : ℕ) :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ shakovSeq n) ∧
      ∃ F : Finset ℕ,
        (∀ n : ℕ, n ∈ F ↔ 1 ≤ n ∧ shakovSeq n = (m : ℤ)) ∧
          F.card = (m ^ 2 + 1).divisors.card := by
  classical
  have uniqueIndex (d : ℕ) (hd : d ∈ (m ^ 2 + 1).divisors) :
      ∃! n : ℕ, 1 ≤ n ∧ shakovSeq n = (m : ℤ) ∧ leftGap n = (d : ℤ) := by
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hd_pos := Nat.pos_of_dvd_of_pos hdvd (by positivity)
    obtain ⟨e, hde⟩ := hdvd
    have he_pos : 0 < e := by
      by_contra! he
      have he_zero : e = 0 := by omega
      simp [he_zero] at hde
    have hd_pos_int : (0 : ℤ) < d := by exact_mod_cast hd_pos
    have he_pos_int : (0 : ℤ) < e := by exact_mod_cast he_pos
    have hprod : (d : ℤ) * e = (m : ℤ) ^ 2 + 1 := by exact_mod_cast hde.symm
    obtain ⟨n, ⟨hn, hnm, hnd, _⟩, huniq⟩ :=
      existsUnique_label m d e hd_pos_int he_pos_int hprod
    refine ⟨n, ⟨hn, hnm, hnd⟩, ?_⟩
    rintro k ⟨hk, hkm, hkd⟩
    have h := (label_properties k hk).2.2.2
    rw [hkm, hkd] at h
    exact huniq k ⟨hk, hkm, hkd, mul_left_cancel₀ hd_pos_int.ne' (h.trans hprod.symm)⟩
  let index (d : {d : ℕ // d ∈ (m ^ 2 + 1).divisors}) : ℕ :=
    (uniqueIndex d d.property).exists.choose
  have index_spec (d : {d : ℕ // d ∈ (m ^ 2 + 1).divisors}) :
      1 ≤ index d ∧ shakovSeq (index d) = (m : ℤ) ∧ leftGap (index d) = (d.val : ℤ) :=
    (uniqueIndex d d.property).exists.choose_spec
  have index_injective : Function.Injective index := by
    intro a b h
    apply Subtype.ext
    have ha := (index_spec a).2.2
    have hb := (index_spec b).2.2
    rw [h] at ha
    exact_mod_cast ha.symm.trans hb
  refine ⟨fun n hn ↦ (label_properties n hn).1,
    (m ^ 2 + 1).divisors.attach.map ⟨index, index_injective⟩, ?_, by simp⟩
  intro n
  rw [Finset.mem_map]
  constructor
  · rintro ⟨d, _, rfl⟩
    exact ⟨(index_spec d).1, (index_spec d).2.1⟩
  · rintro ⟨hn, hnm⟩
    obtain ⟨_, hd, he, hde⟩ := label_properties n hn
    have hleft : ((leftGap n).toNat : ℤ) = leftGap n := Int.toNat_of_nonneg hd.le
    have hright : ((rightGap n).toNat : ℤ) = rightGap n := Int.toNat_of_nonneg he.le
    have hprod : m ^ 2 + 1 = (leftGap n).toNat * (rightGap n).toNat := by
      rw [hnm, ← hleft, ← hright] at hde
      exact_mod_cast hde.symm
    let d : {d : ℕ // d ∈ (m ^ 2 + 1).divisors} :=
      ⟨(leftGap n).toNat, Nat.mem_divisors.mpr ⟨⟨(rightGap n).toNat, hprod⟩, by positivity⟩⟩
    exact ⟨d, Finset.mem_attach _ _, (uniqueIndex d d.property).unique
      (index_spec d) ⟨hn, hnm, hleft.symm⟩⟩

/-- **Shakov's auxiliary sequence.** The integer sequence $a$ with $a(0) = 0$, $a(1) = 1$ and,
for every $n \ge 2$, $a(n) = 2a(n-1)$ if $n \equiv 0 \pmod 4$, $a(n) = a(n-1) + 1$ if
$n \equiv 1 \pmod 4$, $a(n) = 2a(n-1) + 1$ if $n \equiv 2 \pmod 4$, and $a(n) = a(n-1) - 1$ if
$n \equiv 3 \pmod 4$.

The value $a(0)$ plays no role in the recursion; the source's sequence starts at $n = 1$. -/
def shakovA : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 4 = 0 then 2 * shakovA (n + 1)
      else if (n + 2) % 4 = 1 then shakovA (n + 1) + 1
      else if (n + 2) % 4 = 2 then 2 * shakovA (n + 1) + 1
      else shakovA (n + 1) - 1

/-- The next two auxiliary indices are the two children of the current odd-indexed term,
with their order alternating. -/
private theorem shakovA_children (k : ℕ) (hk : 0 < shakovA (2 * k + 1)) :
    0 < shakovA (2 * k + 3) ∧
      let p := (shakovA (2 * k + 1)).toNat
      if k % 2 = 0 then
        (shakovA (2 * k + 2)).toNat = 2 * p + 1 ∧ (shakovA (2 * k + 3)).toNat = 2 * p
      else
        (shakovA (2 * k + 2)).toNat = 2 * p ∧ (shakovA (2 * k + 3)).toNat = 2 * p + 1 := by
  dsimp only
  have he := shakovA.eq_3 (2 * k)
  have ho := shakovA.eq_3 (2 * k + 1)
  simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] at he ho
  by_cases h : k % 2 = 0
  · have heMod : (2 * k + 2) % 4 = 2 := by omega
    have hoMod : (2 * k + 3) % 4 = 3 := by omega
    norm_num only [heMod, hoMod, ite_false, ite_true] at he ho
    rw [ite_eq_left h]
    exact ⟨by omega, by omega, by omega⟩
  · have heMod : (2 * k + 2) % 4 = 0 := by omega
    have hoMod : (2 * k + 3) % 4 = 1 := by omega
    norm_num only [heMod, hoMod, ite_false, ite_true] at he ho
    rw [ite_eq_right h]
    exact ⟨by omega, by omega, by omega⟩

private theorem fib_steps (m : ℕ) :
    (Nat.fib (m + 3) : ℤ) = 2 * (Nat.fib (m + 2) : ℤ) - Nat.fib m ∧
      (Nat.fib (m + 4) : ℤ) = 2 * (Nat.fib (m + 2) : ℤ) + Nat.fib (m + 1) := by
  have step (i : ℕ) : (Nat.fib (i + 2) : ℤ) = (Nat.fib i : ℤ) + Nat.fib (i + 1) := by
    exact_mod_cast Nat.fib_add_two (n := i)
  have h₀ := step m
  have h₁ : (Nat.fib (m + 3) : ℤ) = (Nat.fib (m + 1) : ℤ) + Nat.fib (m + 2) := step (m + 1)
  have h₂ : (Nat.fib (m + 4) : ℤ) = (Nat.fib (m + 2) : ℤ) + Nat.fib (m + 3) := step (m + 2)
  exact ⟨by omega, by omega⟩

/- Keep the values at a parent and both of its children. The next pair consists of the
same-side and opposite-side children of the last term, in that order. -/
private theorem shakovA_fib_triple (k : ℕ) :
    0 < shakovA (2 * k + 1) ∧
      shakovSeq (shakovA (2 * k + 1)).toNat = (Nat.fib (2 * k) : ℤ) ∧
      shakovSeq (shakovA (2 * k + 2)).toNat = (Nat.fib (2 * k + 1) : ℤ) ∧
      shakovSeq (shakovA (2 * k + 3)).toNat = (Nat.fib (2 * k + 2) : ℤ) := by
  induction k with
  | zero => norm_num [shakovA, shakovSeq, Nat.fib]
  | succ k ih =>
    obtain ⟨hpos, hparent, hsibling, hcurrent⟩ := ih
    obtain ⟨hpos', hchildren⟩ := shakovA_children k hpos
    obtain ⟨_, hnext⟩ := shakovA_children (k + 1) hpos'
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at hnext ⊢
    let p := (shakovA (2 * k + 1)).toNat
    change shakovSeq p = _ at hparent
    have hp : 1 ≤ p := by dsimp [p]; omega
    obtain ⟨s₀, s₁, s₂, s₃⟩ := fiber_card.sequence_steps p hp
    obtain ⟨f₃, f₄⟩ := fib_steps (2 * k)
    refine ⟨hpos', hcurrent, ?_⟩
    by_cases h : k % 2 = 0
    · have h' : (k + 1) % 2 ≠ 0 := by omega
      rw [ite_eq_left h] at hchildren
      rw [ite_eq_right h'] at hnext
      obtain ⟨hsib, hcur⟩ := hchildren
      obtain ⟨hn₁, hn₂⟩ := hnext
      change (shakovA (2 * k + 2)).toNat = 2 * p + 1 at hsib
      change (shakovA (2 * k + 3)).toNat = 2 * p at hcur
      rw [hsib] at hsibling
      rw [hcur] at hcurrent hn₁ hn₂
      rw [hn₁, hn₂, show 2 * (2 * p) = 4 * p by omega, s₀, s₁,
        hparent, hsibling, hcurrent, f₃, f₄]
      exact ⟨rfl, rfl⟩
    · have h' : (k + 1) % 2 = 0 := by omega
      rw [ite_eq_right h] at hchildren
      rw [ite_eq_left h'] at hnext
      obtain ⟨hsib, hcur⟩ := hchildren
      obtain ⟨hn₁, hn₂⟩ := hnext
      change (shakovA (2 * k + 2)).toNat = 2 * p at hsib
      change (shakovA (2 * k + 3)).toNat = 2 * p + 1 at hcur
      rw [hsib] at hsibling
      rw [hcur] at hcurrent hn₁ hn₂
      rw [hn₁, hn₂, show 2 * (2 * p + 1) = 4 * p + 2 by omega,
        show 4 * p + 2 + 1 = 4 * p + 3 by omega, s₃, s₂, hparent, hsibling, hcurrent, f₃, f₄]
      exact ⟨rfl, rfl⟩

/-- **Shakov's sequence takes Fibonacci values along the auxiliary sequence.** Let $s$ be
Shakov's $2$-regular sequence, let $a$ be Shakov's auxiliary sequence, and let $F_k$ denote the
$k$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 1$,
$s(\max(a(n), 0)) = F_{n-1}$.

The source shows that $a(n)$ is a positive integer and numbers the Fibonacci numbers so that
this reads $s(a(n)) = F_n$.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 9. -/
theorem shakovSeq_shakovA (n : ℕ) (hn : 1 ≤ n) :
    shakovSeq (shakovA n).toNat = (Nat.fib (n - 1) : ℤ) := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k : ℕ, n = 2 * k + 1 ∨ n = 2 * k + 2 :=
    ⟨(n - 1) / 2, by omega⟩
  · exact (shakovA_fib_triple k).2.1
  · exact (shakovA_fib_triple k).2.2.1

end MathlibExt.NumberTheory.ShakovTwoRegularWanted

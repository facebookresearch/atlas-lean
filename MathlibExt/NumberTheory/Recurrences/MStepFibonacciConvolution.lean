/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/-! # Fibonacci m-step convolution
-/

private lemma geom_two : ∀ t : ℕ, (∑ i ∈ Finset.range t, 2 ^ i) + 1 = 2 ^ t := by
  intro t
  induction t with
  | zero => simp only [Finset.sum_range_zero, pow_zero, Nat.zero_add]
  | succ t ih => rw [Finset.sum_range_succ, pow_succ]; omega

private lemma conv_succ (F : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1 + 1), 2 ^ j * F (n + 1 - j)) =
      F (n + 1) + 2 * (∑ j ∈ Finset.range (n + 1), 2 ^ j * F (n - j)) := by
  have h : (∑ j ∈ Finset.range (n + 1 + 1), 2 ^ j * F (n + 1 - j)) =
      (∑ k ∈ Finset.range (n + 1), 2 ^ (k + 1) * F (n + 1 - (k + 1))) +
        2 ^ 0 * F (n + 1 - 0) :=
    Finset.sum_range_succ' _ _
  have h0 : (2 : ℕ) ^ 0 * F (n + 1 - 0) = F (n + 1) := by simp
  have hsub : ∀ x, n + 1 - (x + 1) = n - x := by intro x; omega
  have h1 : ∀ x ∈ Finset.range (n + 1),
      2 ^ (x + 1) * F (n + 1 - (x + 1)) = 2 * (2 ^ x * F (n - x)) := by
    intro x _
    rw [pow_succ, hsub x]
    ring
  have hsum : (∑ x ∈ Finset.range (n + 1), 2 ^ (x + 1) * F (n + 1 - (x + 1))) =
      2 * (∑ j ∈ Finset.range (n + 1), 2 ^ j * F (n - j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact h1 x hx
  omega

private lemma mstep_add (F : ℕ → ℕ) (m k : ℕ) (hm : 1 ≤ m)
    (hrec : ∀ k : ℕ, 2 ≤ k → F k = ∑ j ∈ Finset.range m, F (k - (j + 1)))
    (hk2 : 2 ≤ k) (hkm : m ≤ k) :
    F (k + 1) + F (k - m) = 2 * F k := by
  obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  subst hr
  have hk1 : 2 ≤ k + 1 := by omega
  have e1 := hrec k hk2
  have e2 := hrec (k + 1) hk1
  have hsub : ∀ j, k + 1 - (j + 1) = k - j := by intro j; omega
  have hcongr : (∑ j ∈ Finset.range (r + 1), F (k + 1 - (j + 1))) =
      ∑ j ∈ Finset.range (r + 1), F (k - j) :=
    Finset.sum_congr rfl (fun j _ => by rw [hsub j])
  rw [hcongr] at e2
  have h : (∑ j ∈ Finset.range (r + 1), F (k - j)) =
      (∑ k_1 ∈ Finset.range r, F (k - (k_1 + 1))) + F (k - 0) :=
    Finset.sum_range_succ' _ _
  have hk0 : k - 0 = k := by omega
  have hk0F : F (k - 0) = F k := by rw [hk0]
  have hA : (∑ j ∈ Finset.range (r + 1), F (k - j)) =
      F k + ∑ j ∈ Finset.range r, F (k - (j + 1)) := by
    omega
  have hB : (∑ j ∈ Finset.range (r + 1), F (k - (j + 1))) =
      (∑ j ∈ Finset.range r, F (k - (j + 1))) + F (k - (r + 1)) := by
    exact Finset.sum_range_succ (fun j => F (k - (j + 1))) r
  omega

private lemma mstep_init (F : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (h0 : F 0 = 0) (h1 : F 1 = 1)
    (hrec : ∀ k : ℕ, 2 ≤ k → F k = ∑ j ∈ Finset.range m, F (k - (j + 1))) :
    F (m + 1) = 2 ^ (m - 1) := by
  have key : ∀ B : ℕ, ∀ i : ℕ, 2 ≤ i → i ≤ B → i ≤ m + 1 → F i = 2 ^ (i - 2) := by
    intro B
    induction B with
    | zero =>
      intro i hi2 hile _
      exfalso
      omega
    | succ B ih =>
      intro i hi2 hile him
      by_cases h : i ≤ B
      · exact ih i hi2 h (by omega)
      · have hi_eq : i = B + 1 := by omega
        subst hi_eq
        have hB1 : 1 ≤ B := by omega
        have hBm : B ≤ m := by omega
        have hrecB : F (B + 1) = ∑ j ∈ Finset.range m, F (B + 1 - (j + 1)) :=
          hrec (B + 1) (by omega)
        have hsub : ∀ j, B + 1 - (j + 1) = B - j := by intro j; omega
        have hcongr : (∑ j ∈ Finset.range m, F (B + 1 - (j + 1))) =
            ∑ j ∈ Finset.range m, F (B - j) :=
          Finset.sum_congr rfl (fun j _ => by rw [hsub j])
        rw [hcongr] at hrecB
        have hsub2 : Finset.range B ⊆ Finset.range m := by
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        have htail : (∑ j ∈ Finset.range m, F (B - j)) =
            ∑ j ∈ Finset.range B, F (B - j) := by
          apply Eq.symm
          apply Finset.sum_subset hsub2
          intro x hxm hxb
          simp only [Finset.mem_range, not_lt] at hxm hxb
          have hx0 : B - x = 0 := by omega
          rw [hx0, h0]
        rw [htail] at hrecB
        obtain ⟨q, hq⟩ : ∃ q, B = q + 1 := ⟨B - 1, by omega⟩
        subst hq
        have hmirror : (∑ j ∈ Finset.range (q + 1), F (q + 1 - j)) =
            ∑ j ∈ Finset.range (q + 1), F (j + 1) := by
          have hrefl : (∑ j ∈ Finset.range (q + 1), F (q + 1 - 1 - j + 1)) =
              ∑ j ∈ Finset.range (q + 1), F (j + 1) :=
            Finset.sum_range_reflect (fun j => F (j + 1)) (q + 1)
          have hL : (∑ j ∈ Finset.range (q + 1), F (q + 1 - j)) =
              ∑ j ∈ Finset.range (q + 1), F (q + 1 - 1 - j + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            have hj' := Finset.mem_range.mp hj
            omega
          rw [hL]
          exact hrefl
        rw [hmirror] at hrecB
        have hsplit : (∑ j ∈ Finset.range (q + 1), F (j + 1)) =
            (∑ k ∈ Finset.range q, F (k + 1 + 1)) + F (0 + 1) :=
          Finset.sum_range_succ' _ _
        have h01 : (0 : ℕ) + 1 = 1 := by omega
        have h01F : F (0 + 1) = F 1 := by rw [h01]
        have hpeel : (∑ j ∈ Finset.range (q + 1), F (j + 1)) =
            F 1 + ∑ j ∈ Finset.range q, F (j + 1 + 1) := by
          omega
        rw [hpeel, h1] at hrecB
        have hinner : (∑ j ∈ Finset.range q, F (j + 1 + 1)) =
            ∑ j ∈ Finset.range q, 2 ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjq : j < q := Finset.mem_range.mp hj
          have g1 : 2 ≤ j + 1 + 1 := by omega
          have g2 : j + 1 + 1 ≤ q + 1 := by omega
          have g3 : j + 1 + 1 ≤ m + 1 := by omega
          have hF := ih (j + 1 + 1) g1 g2 g3
          have hexp : j + 1 + 1 - 2 = j := by omega
          rw [hF, hexp]
        rw [hinner] at hrecB
        have hgeom := geom_two q
        have hexp2 : q + 1 + 1 - 2 = q := by omega
        rw [hexp2]
        omega
  exact key (m + 1) (m + 1) (by omega) le_rfl le_rfl

/--
**Power-weighted convolution of Fibonacci $m$-step numbers.** Let $m \ge 1$ and let
$F \colon \mathbb{N} \to \mathbb{N}$ satisfy $F(0) = 0$, $F(1) = 1$ and
$F(k) = \sum_{j=1}^{m} F(k - j)$ for every $k \ge 2$, where a term $F(k - j)$ with $j > k$ is
read as $F(0) = 0$. Then for every natural number $n$,
$$\sum_{j=0}^{n} 2^j F(n - j) = 2^{n+m-1} - F(n + 1 + m),$$
where the subtraction on the right is taken in $\mathbb{N}$ (truncated at $0$).

The initial conditions are those of the paper's definition of Fibonacci $m$-step numbers
(lines 126–133), whose values at negative indices are $0$. The paper states the theorem for
$m \ge 3$; the cases $m = 1$ and $m = 2$ also hold, so the hypothesis here is $m \ge 1$.

Proves `Wanted` entry `two_pow_convolution_mstep_fibonacci`.

Source: Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving
Fibonacci m-Step Numbers," Journal of Integer Sequences 27 (2024),
Article 24.8.8, Theorem (label power2_conv), lines 453–459,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex
-/
theorem two_pow_convolution_mstep_fibonacci (F : ℕ → ℕ) (m n : ℕ)
    (hm : 1 ≤ m) (h0 : F 0 = 0) (h1 : F 1 = 1)
    (hrec : ∀ k : ℕ, 2 ≤ k → F k = ∑ j ∈ Finset.range m, F (k - (j + 1))) :
    (∑ j ∈ Finset.range (n + 1), 2 ^ j * F (n - j)) =
      2 ^ (n + m - 1) - F (n + 1 + m) := by
  have hinit : F (m + 1) = 2 ^ (m - 1) := mstep_init F m hm h0 h1 hrec
  have key : ∀ N : ℕ,
      (∑ j ∈ Finset.range (N + 1), 2 ^ j * F (N - j)) =
        2 ^ (N + m - 1) - F (N + 1 + m) ∧ F (N + 1 + m) ≤ 2 ^ (N + m - 1) := by
    intro N
    induction N with
    | zero =>
      have e1 : 0 + m - 1 = m - 1 := by omega
      have e2 : 0 + 1 + m = m + 1 := by omega
      have hsum : (∑ j ∈ Finset.range (0 + 1), 2 ^ j * F (0 - j)) = 0 := by
        simp [h0]
      rw [hsum, e1, e2, hinit]
      exact ⟨by omega, by omega⟩
    | succ N ih =>
      obtain ⟨iheq, ihle⟩ := ih
      have hS := conv_succ F N
      have hrr : (N + 1) + 1 = N + 2 := by ring
      have hrr2 : N + 1 + 1 + m = N + 1 + m + 1 := by ring
      have hrr3 : N + 1 + m - 1 = (N + m - 1) + 1 := by omega
      have hk2 : 2 ≤ N + 1 + m := by omega
      have hkm : m ≤ N + 1 + m := by omega
      have hF := mstep_add F m (N + 1 + m) hm hrec hk2 hkm
      have hkm_rw : N + 1 + m - m = N + 1 := by omega
      rw [hkm_rw] at hF
      have hpow : 2 ^ (N + 1 + m - 1) = 2 * 2 ^ (N + m - 1) := by
        rw [hrr3, pow_succ']
      rw [← hrr2] at hF
      have hgoal : (∑ j ∈ Finset.range ((N + 1) + 1), 2 ^ j * F (N + 1 - j)) =
          2 ^ (N + 1 + m - 1) - F (N + 1 + 1 + m) := by
        omega
      have hle : F (N + 1 + 1 + m) ≤ 2 ^ (N + 1 + m - 1) := by
        omega
      have eN : (N + 1) + 1 = N + 1 + 1 := by ring
      have eF : N + 1 + 1 + m = (N + 1) + 1 + m := by ring
      have eP : N + 1 + m - 1 = (N + 1) + m - 1 := by ring
      rw [eN, eF, eP]
      exact ⟨hgoal, hle⟩
  exact (key n).1

end MetaMathlibExt

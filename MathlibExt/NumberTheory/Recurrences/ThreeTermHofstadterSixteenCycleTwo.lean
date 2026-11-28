/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.GetD
public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadter
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# The second sixteen-cycle of the padded three-term Hofstadter-like recurrence

Fox's second sixteen-cycle lemma gives the terms up to and including the cutoff λ.
-/

namespace MetaMathlibExt
namespace threeTermHofstadter_sixteenCycle_two

private def seed (a : List ℤ) (lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ) : List ℤ :=
  a ++ [16, mu₂, 7, ga₂, lam, 16, lam, 16, mu₁, 10, ga₃, mu₂, 7, lam, 16, ga₁]

private def value (lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ) (k r : ℕ) : ℤ :=
  [mu₁ * 2 ^ k + ga₁ - 2 * mu₁, 16, mu₂ * 2 ^ k, 7, 7 * k + ga₂, lam, 16, lam, 16,
    mu₁ * 2 ^ k, 10, 16 * k + ga₃, mu₂ * 2 ^ k, 7, lam, 16].getD r 0

private def Pattern (K : ℕ) (lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ) (xs : Array ℤ) : Prop :=
  ∀ (k r : ℕ), r < 16 → (K : ℤ) + 1 ≤ K + 16 * (k : ℤ) + r →
    (K : ℤ) + 16 * (k : ℤ) + r ≤ xs.size →
    threeTermHofstadterLookup true xs (K + 16 * (k : ℤ) + r) =
      some (value lam mu₁ mu₂ ga₁ ga₂ ga₃ k r)

private theorem length_seed (a : List ℤ) (lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ) :
    (seed a lam mu₁ mu₂ ga₁ ga₂ ga₃).length = a.length + 16 := by
  simp [seed]

private theorem pattern_seed {K : ℕ} {a : List ℤ} (ha : a.length = K)
    (lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ) :
    Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ (seed a lam mu₁ mu₂ ga₁ ga₂ ga₃).toArray := by
  intro k r hr hlo hhi
  simp only [List.size_toArray, length_seed, ha, Nat.cast_add, Nat.cast_ofNat] at hhi
  simp only [threeTermHofstadterLookup, show ¬((K : ℤ) + 16 * (k : ℤ) + r ≤ 0) by omega,
    ite_false, List.getElem?_toArray, seed]
  rw [List.getElem?_append_right (by omega), ha]
  have hindex : ((K : ℤ) + 16 * (k : ℤ) + r - 1).toNat - K = 16 * k + r - 1 := by
    omega
  rw [hindex]
  -- The seed contains residues 1 through 15 of cycle zero and residue 0 of cycle one.
  rcases (show (k = 0 ∧ 1 ≤ r) ∨ (k = 1 ∧ r = 0) by omega) with ⟨rfl, hr₁⟩ | ⟨rfl, rfl⟩
  · interval_cases r <;> simp [value, List.getD]
  · simp [value, List.getD]
    ring

private theorem next {K q r : ℕ} {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ} {xs : Array ℤ}
    (p : Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ xs)
    (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga₁ : lam < ga₁) (hga₂ : lam < ga₂) (hga₃ : lam < ga₃)
    (hstart : K + 16 ≤ xs.size) (hhi : (xs.size : ℤ) + 1 ≤ lam)
    (hr : r < 16) (hn : (xs.size : ℤ) + 1 = K + 16 * ((q + 1 : ℕ) : ℤ) + r) :
    threeTermHofstadterNext true xs = some (value lam mu₁ mu₂ ga₁ ga₂ ga₃ (q + 1) r) := by
  -- Each small backward shift lands in the current or preceding cycle.
  have back (i : ℤ) (hi : 1 ≤ i) (hi' : i ≤ 16) :
      threeTermHofstadterLookup true xs ((xs.size : ℤ) + 1 - i) =
        some (if i ≤ r then value lam mu₁ mu₂ ga₁ ga₂ ga₃ (q + 1) ((r : ℤ) - i).toNat
          else value lam mu₁ mu₂ ga₁ ga₂ ga₃ q ((r : ℤ) + 16 - i).toNat) := by
    split
    · rw [show (xs.size : ℤ) + 1 - i =
        K + 16 * ((q + 1 : ℕ) : ℤ) + ↑((r : ℤ) - i).toNat by omega]
      exact p (q + 1) _ (by omega) (by omega) (by omega)
    · rw [show (xs.size : ℤ) + 1 - i =
        K + 16 * (q : ℤ) + ↑((r : ℤ) + 16 - i).toNat by omega]
      exact p q _ (by omega) (by omega) (by omega)
  have zero (j : ℤ) (hj : j ≤ 0) : threeTermHofstadterLookup true xs j = some 0 := by
    simp [threeTermHofstadterLookup, hj]
  have hpow : 1 ≤ (2 : ℤ) ^ q := one_le_pow₀ (by decide)
  have hpow' : 2 ≤ (2 : ℤ) ^ (q + 1) := by rw [pow_succ]; omega
  have mul_bound {mu : ℤ} (hmu : lam < mu) {k : ℕ} (hk : 1 ≤ (2 : ℤ) ^ k) :
      mu ≤ mu * 2 ^ k :=
    le_mul_of_one_le_right (by omega) hk
  have hm₁ := mul_bound hmu₁ hpow
  have hm₂ := mul_bound hmu₂ hpow
  have hm₁' := mul_bound hmu₁ (k := q + 1) (by omega)
  have hm₂' := mul_bound hmu₂ (k := q + 1) (by omega)
  have hfirst : 2 * mu₁ ≤ mu₁ * 2 ^ (q + 1) := by
    rw [mul_comm 2 mu₁]
    exact mul_le_mul_of_nonneg_left hpow' (by omega)
  simp only [threeTermHofstadterNext, back 1 (by decide) (by decide),
    back 2 (by decide) (by decide), back 3 (by decide) (by decide), Option.bind_some]
  -- Large terms select padded zeros. The other summands shift back by 7, 10 or 16.
  interval_cases r <;>
    dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    simp (disch := omega) only [zero, back 7 (by decide) (by decide),
      back 10 (by decide) (by decide), back 16 (by decide) (by decide),
      Option.bind_some, Option.map_some, Option.some.injEq] <;>
    dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    (try simp only [pow_succ]) <;> ring

private theorem pattern_push {K k r : ℕ} {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ} {xs : Array ℤ}
    (p : Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ xs) (hr : r < 16)
    (hn : (xs.size : ℤ) + 1 = K + 16 * (k : ℤ) + r) :
    Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ (xs.push (value lam mu₁ mu₂ ga₁ ga₂ ga₃ k r)) := by
  intro q s hs hlo hhi
  rw [threeTermHofstadterLookup_push]
  split
  · have hq : q = k := by omega
    have hs' : s = r := by omega
    rw [hq, hs']
  · simp only [Array.size_push, Nat.cast_add, Nat.cast_one] at hhi
    exact p q s hs hlo (by omega)

private theorem extend {K : ℕ} {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ}
    (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga₁ : lam < ga₁) (hga₂ : lam < ga₂) (hga₃ : lam < ga₃)
    (steps : ℕ) {xs : Array ℤ} (p : Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ xs)
    (hstart : K + 16 ≤ xs.size) (hend : (xs.size : ℤ) + steps ≤ lam) :
    ∃ ys, threeTermHofstadterExtend true steps xs = some ys ∧
      ys.size = xs.size + steps ∧ Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ ys := by
  induction steps generalizing xs with
  | zero => exact ⟨xs, rfl, rfl, p⟩
  | succ steps ih =>
    let d := xs.size + 1 - (K + 16)
    let q := d / 16
    let r := d % 16
    have hr : r < 16 := by dsimp [r]; omega
    have hn : (xs.size : ℤ) + 1 = K + 16 * ((q + 1 : ℕ) : ℤ) + r := by
      dsimp [r, q, d]
      omega
    have hnext := next p hmu₁ hmu₂ hga₁ hga₂ hga₃ hstart (by omega) hr hn
    have hp := pattern_push p hr hn
    obtain ⟨ys, hext, hsize, hy⟩ := ih hp (by simp; omega) (by simp; omega)
    refine ⟨ys, ?_, ?_, hy⟩
    · simpa [threeTermHofstadterExtend, hnext] using hext
    · simp only [Array.size_push] at hsize
      omega

end threeTermHofstadter_sixteenCycle_two

open threeTermHofstadter_sixteenCycle_two

set_option linter.unusedVariables false in
/-- **Second sixteen-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$
be a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$ be
integers with $\lambda > 31 + K$ and $\mu_1, \mu_2, \gamma_1, \gamma_2, \gamma_3 > \lambda$. Let
$a_1, \dots, a_K$ be arbitrary integers and let $B$ be the padded three-term Hofstadter-like
sequence with initial conditions $a_1, \dots, a_K, 16, \mu_2, 7, \gamma_2, \lambda, 16, \lambda,
16, \mu_1, 10, \gamma_3, \mu_2, 7, \lambda, 16, \gamma_1$. Then for all natural numbers $k$ and
$r \le 15$ with $K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and
these terms are $B(K + 16k) = \mu_1 2^k + \gamma_1 - 2\mu_1$, $B(K + 16k + 1) = 16$,
$B(K + 16k + 2) = \mu_2 2^k$, $B(K + 16k + 3) = 7$, $B(K + 16k + 4) = 7k + \gamma_2$,
$B(K + 16k + 5) = \lambda$, $B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \lambda$,
$B(K + 16k + 8) = 16$, $B(K + 16k + 9) = \mu_1 2^k$, $B(K + 16k + 10) = 10$,
$B(K + 16k + 11) = 16k + \gamma_3$, $B(K + 16k + 12) = \mu_2 2^k$, $B(K + 16k + 13) = 7$,
$B(K + 16k + 14) = \lambda$ and $B(K + 16k + 15) = 16$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 7,
citing the author's thesis, Proposition 9.16 (`jis-2024-24.7.4-lem-7`). -/
public theorem threeTermHofstadter_sixteenCycle_two {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga₁ ga₂ ga₃ : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁)
    (hmu₂ : lam < mu₂) (hga₁ : lam < ga₁) (hga₂ : lam < ga₂) (hga₃ : lam < ga₃)
    (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16) (hlo : K + 1 ≤ K + 16 * k + r)
    (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [16, mu₂, 7, ga₂, lam, 16, lam, 16, mu₁, 10, ga₃, mu₂, 7, lam, 16, ga₁])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ k + ga₁ - 2 * mu₁, 16, mu₂ * 2 ^ k, 7, 7 * k + ga₂, lam, 16, lam, 16,
        mu₁ * 2 ^ k, 10, 16 * k + ga₃, mu₂ * 2 ^ k, 7, lam, 16].getD r 0) := by
  let init := seed a lam mu₁ mu₂ ga₁ ga₂ ga₃
  let n := K + 16 * k + r
  change threeTermHofstadterTerm true init n = some (value lam mu₁ mu₂ ga₁ ga₂ ga₃ k r)
  change (n : ℤ) ≤ lam at hhi
  have hn : (n : ℤ) = K + 16 * (k : ℤ) + r := by simp [n]
  have hlen : init.length = K + 16 := by rw [length_seed, ha]
  have hsize : init.toArray.size = K + 16 := by simpa using hlen
  have p : Pattern K lam mu₁ mu₂ ga₁ ga₂ ga₃ init.toArray :=
    pattern_seed ha lam mu₁ mu₂ ga₁ ga₂ ga₃
  obtain ⟨ys, hext, hy, hp⟩ := extend hmu₁ hmu₂ hga₁ hga₂ hga₃ (n - init.length)
    p (by omega) (by omega)
  simp only [threeTermHofstadterTerm, threeTermHofstadterPrefix, hext, Option.bind_some, hn]
  exact hp k r hr (by omega) (by omega)

end MetaMathlibExt

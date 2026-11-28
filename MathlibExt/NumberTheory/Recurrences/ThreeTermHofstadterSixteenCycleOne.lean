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
# The first sixteen-cycle of the padded three-term Hofstadter-like recurrence

For a natural number $K\ge 1$, integers $\lambda>31+K$ and $\mu_1,\mu_2,\gamma>\lambda$, and an
arbitrary prefix of $K$ integers followed by the eighteen specified seeds, the padded recurrence
follows the sixteen residue formulas from index $K+1$ through $\lambda$, inclusive. The seed block
ends at residue $2$ in cycle $1$, so computing a new term at residue $0$, $1$ or $2$ only happens in
cycle $2$ or later. This is when the backward shift by $25$ reaches residues $7$, $8$ or $9$ two
cycles earlier. The parameter bounds are those of journal Lemma 6. At residue $12$, the thesis
gives the exponent $k+1$, consistent with the seeds and recurrence; the journal prints $k$ there.
At residue $0$, the index range forces $k\ge 1$.

## References

* Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial
  Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6, pp. 14–15.
* Nathan Harel Fox, *An Exploration of Nested Recurrences Using Experimental Mathematics*,
  PhD thesis, Rutgers, The State University of New Jersey, 2017, Proposition 9.13, pp. 128–129.
* The prefix invariant, seed check and backward-shift argument adapt `Pattern`, `pattern_seed`,
  `next` and `pattern_push` in `ThreeTermHofstadterSixteenCycleTwo`.
-/

namespace MetaMathlibExt
namespace threeTermHofstadter_sixteenCycle_one

private def seed (a : List ℤ) (lam mu₁ mu₂ ga : ℤ) : List ℤ :=
  a ++ [lam, 7, mu₂, 16, mu₂, 16, mu₁, lam, 7, mu₂, 16, 2 * mu₂, 16, mu₂, 25, ga, lam, 7]

private def value (lam mu₁ mu₂ ga : ℤ) (k r : ℕ) : ℤ :=
  [mu₁ * 2 ^ (k - 1) + ga - mu₁, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ k, 16,
    mu₁ * 2 ^ k, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ (k + 1), 16, mu₂ * 2 ^ k, 25].getD r 0

private def Pattern (K : ℕ) (lam mu₁ mu₂ ga : ℤ) (xs : Array ℤ) : Prop :=
  ∀ (k r : ℕ), r < 16 → (K : ℤ) + 1 ≤ K + 16 * (k : ℤ) + r →
    (K : ℤ) + 16 * (k : ℤ) + r ≤ xs.size →
    threeTermHofstadterLookup true xs (K + 16 * (k : ℤ) + r) = some (value lam mu₁ mu₂ ga k r)

private theorem length_seed (a : List ℤ) (lam mu₁ mu₂ ga : ℤ) :
    (seed a lam mu₁ mu₂ ga).length = a.length + 18 := by
  simp [seed]

private theorem pattern_seed {K : ℕ} (hK : 1 ≤ K) {a : List ℤ} (ha : a.length = K)
    (lam mu₁ mu₂ ga : ℤ) : Pattern K lam mu₁ mu₂ ga (seed a lam mu₁ mu₂ ga).toArray := by
  intro k r hr hlo hhi
  simp only [List.size_toArray, length_seed, ha, Nat.cast_add, Nat.cast_ofNat] at hhi
  have hKpos : (0 : ℤ) < K := by exact_mod_cast (show 0 < K from hK)
  rw [threeTermHofstadterLookup_of_pos _ _ (by omega), List.getElem?_toArray, seed,
    List.getElem?_append_right (by omega), ha]
  have hindex : ((K : ℤ) + 16 * (k : ℤ) + r - 1).toNat - K = 16 * k + r - 1 := by omega
  rw [hindex]
  -- Cycle zero contributes residues 1–15; cycle one contributes residues 0–2.
  rcases (show (k = 0 ∧ 1 ≤ r) ∨ (k = 1 ∧ r ≤ 2) by omega) with ⟨rfl, hr₁⟩ | ⟨rfl, hr₂⟩
  · (interval_cases r <;> simp [value, List.getD]); ring
  · interval_cases r <;> simp [value, List.getD]

private theorem next {K q r : ℕ} {lam mu₁ mu₂ ga : ℤ} {xs : Array ℤ}
    (p : Pattern K lam mu₁ mu₂ ga xs) (hlam : 0 ≤ lam) (hmu₁ : lam < mu₁)
    (hmu₂ : lam < mu₂) (hga : lam < ga)
    (hstart : K + 18 ≤ xs.size) (hhi : (xs.size : ℤ) + 1 ≤ lam)
    (hr : r < 16) (hn : (xs.size : ℤ) + 1 = K + 16 * ((q + 1 : ℕ) : ℤ) + r) :
    threeTermHofstadterNext true xs = some (value lam mu₁ mu₂ ga (q + 1) r) := by
  -- The predecessors and the shifts by 7 and 16 are at most one cycle back.
  have back (i : ℤ) (hi : 1 ≤ i) (hi' : i ≤ 16) :
      threeTermHofstadterLookup true xs ((xs.size : ℤ) + 1 - i) =
        some (if i ≤ r then value lam mu₁ mu₂ ga (q + 1) ((r : ℤ) - i).toNat
          else value lam mu₁ mu₂ ga q ((r : ℤ) + 16 - i).toNat) := by
    split
    · rw [show (xs.size : ℤ) + 1 - i =
        K + 16 * ((q + 1 : ℕ) : ℤ) + ↑((r : ℤ) - i).toNat by omega]
      exact p (q + 1) _ (by omega) (by omega) (by omega)
    · rw [show (xs.size : ℤ) + 1 - i =
        K + 16 * (q : ℤ) + ↑((r : ℤ) + 16 - i).toNat by omega]
      exact p q _ (by omega) (by omega) (by omega)
  have back25 (h : r ≤ 2) :
      threeTermHofstadterLookup true xs ((xs.size : ℤ) + 1 - 25) =
        some (value lam mu₁ mu₂ ga (q - 1) (r + 7)) := by
    rw [show (xs.size : ℤ) + 1 - 25 =
      K + 16 * ((q - 1 : ℕ) : ℤ) + ↑(r + 7) by omega]
    exact p (q - 1) (r + 7) (by omega) (by omega) (by omega)
  have mul_bound {mu : ℤ} (hmu : lam < mu) (k : ℕ) : mu ≤ mu * 2 ^ k :=
    le_mul_of_one_le_right (by omega) (one_le_pow₀ (by decide))
  have hm₁ := mul_bound hmu₁ q
  have hm₂ := mul_bound hmu₂ q
  have hm₁' := mul_bound hmu₁ (q + 1)
  have hm₂' := mul_bound hmu₂ (q + 1)
  have hm₂'' := mul_bound hmu₂ (q + 1 + 1)
  have hpow (h : r = 0) : (2 : ℤ) ^ q = 2 ^ (q - 1) * 2 := by
    conv_lhs => rw [show q = q - 1 + 1 by omega, pow_succ]
  rw [threeTermHofstadterNext_eq _ _ (back 1 (by decide) (by decide))
    (back 2 (by decide) (by decide)) (back 3 (by decide) (by decide))]
  -- Every remaining lookup either hits the padded zero region or uses one of the three shifts.
  interval_cases r <;>
    dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    simp (disch := omega) only [threeTermHofstadterLookup_true_of_nonpos,
      back 7 (by decide) (by decide), back 16 (by decide) (by decide), back25,
      Option.bind_some, Option.map_some, Option.some.injEq] <;>
    dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    (try simp (disch := omega) only [hpow, pow_succ]) <;> ring

private theorem pattern_push {K k r : ℕ} {lam mu₁ mu₂ ga : ℤ} {xs : Array ℤ}
    (p : Pattern K lam mu₁ mu₂ ga xs) (hr : r < 16)
    (hn : (xs.size : ℤ) + 1 = K + 16 * (k : ℤ) + r) :
    Pattern K lam mu₁ mu₂ ga (xs.push (value lam mu₁ mu₂ ga k r)) := by
  intro q s hs hlo hhi
  rw [threeTermHofstadterLookup_push]
  split
  · have hq : q = k := by omega
    have hs' : s = r := by omega
    rw [hq, hs']
  · simp only [Array.size_push, Nat.cast_add, Nat.cast_one] at hhi
    exact p q s hs hlo (by omega)

end threeTermHofstadter_sixteenCycle_one

open threeTermHofstadter_sixteenCycle_one

/-- **First sixteen-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$ be
a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma$ be integers with $\lambda > 31 + K$
and $\mu_1, \mu_2, \gamma > \lambda$. Let $a_1, \dots, a_K$ be arbitrary integers and let $B$ be
the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, \lambda, 7, \mu_2, 16, \mu_2, 16, \mu_1, \lambda, 7, \mu_2, 16, 2\mu_2, 16,
\mu_2, 25, \gamma, \lambda, 7$. Then for all natural numbers $k$ and $r \le 15$ with
$K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and these terms are
$B(K + 16k) = \mu_1 2^{k-1} + \gamma - \mu_1$, $B(K + 16k + 1) = \lambda$, $B(K + 16k + 2) = 7$,
$B(K + 16k + 3) = \mu_2 2^k$, $B(K + 16k + 4) = 16$, $B(K + 16k + 5) = \mu_2 2^k$,
$B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \mu_1 2^k$, $B(K + 16k + 8) = \lambda$,
$B(K + 16k + 9) = 7$, $B(K + 16k + 10) = \mu_2 2^k$, $B(K + 16k + 11) = 16$,
$B(K + 16k + 12) = \mu_2 2^{k+1}$, $B(K + 16k + 13) = 16$, $B(K + 16k + 14) = \mu_2 2^k$ and
$B(K + 16k + 15) = 25$.

Corrected: the paper prints $B(K + 16k + 12) = \mu_2 2^k$, which contradicts its own initial
value $B(K + 12) = 2\mu_2$; the exponent $k + 1$ matches the initial conditions and every later
term.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6,
citing the author's thesis, Proposition 9.13 (`jis-2024-24.7.4-lem-6`). -/
public theorem threeTermHofstadter_sixteenCycle_one {K : ℕ} (hK : 1 ≤ K)
    {lam mu₁ mu₂ ga : ℤ} (hlam : 31 + (K : ℤ) < lam) (hmu₁ : lam < mu₁) (hmu₂ : lam < mu₂)
    (hga : lam < ga) (a : List ℤ) (ha : a.length = K) (k r : ℕ) (hr : r < 16)
    (hlo : K + 1 ≤ K + 16 * k + r) (hhi : ((K + 16 * k + r : ℕ) : ℤ) ≤ lam) :
    threeTermHofstadterTerm true
        (a ++ [lam, 7, mu₂, 16, mu₂, 16, mu₁, lam, 7, mu₂, 16, 2 * mu₂, 16, mu₂, 25, ga, lam, 7])
        (K + 16 * k + r) =
      some ([mu₁ * 2 ^ (k - 1) + ga - mu₁, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ k, 16,
        mu₁ * 2 ^ k, lam, 7, mu₂ * 2 ^ k, 16, mu₂ * 2 ^ (k + 1),
        16, mu₂ * 2 ^ k, 25].getD r 0) := by
  let init := seed a lam mu₁ mu₂ ga
  let n := K + 16 * k + r
  change threeTermHofstadterTerm true init n = some (value lam mu₁ mu₂ ga k r)
  change (n : ℤ) ≤ lam at hhi
  have hn : (n : ℤ) = K + 16 * (k : ℤ) + r := by simp [n]
  have hlen : init.toArray.size = K + 18 := by rw [List.size_toArray, length_seed, ha]
  refine threeTermHofstadterTerm_of_invariant true init n
    (P := fun xs => K + 18 ≤ xs.size ∧ Pattern K lam mu₁ mu₂ ga xs)
    ⟨hlen.ge, pattern_seed hK ha lam mu₁ mu₂ ga⟩ ?_ ?_
  · intro xs ⟨hsize, hp⟩ hlt
    let d := xs.size + 1 - (K + 16)
    let q := d / 16
    let s := d % 16
    have hs : s < 16 := by dsimp [s]; omega
    have hindex : (xs.size : ℤ) + 1 = K + 16 * ((q + 1 : ℕ) : ℤ) + s := by
      dsimp [q, s, d]
      omega
    exact ⟨_, next hp (by omega) hmu₁ hmu₂ hga hsize (by omega) hs hindex,
      by simp only [Array.size_push]; omega, pattern_push hp hs hindex⟩
  · intro xs ⟨_, hp⟩ hs
    rw [hn]
    exact hp k r hr (by omega) (by omega)

end MetaMathlibExt

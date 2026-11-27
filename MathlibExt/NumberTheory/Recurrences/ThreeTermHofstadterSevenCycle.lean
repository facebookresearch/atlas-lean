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

/-!
# The seven-cycle of the padded three-term Hofstadter-like recurrence

Fox's seven-cycle lemma gives the terms through a residue-dependent endpoint.
-/

namespace MetaMathlibExt
namespace threeTermHofstadter_sevenCycle

private def value (K L M lam mu k : ℤ) (r : ℕ) : ℤ :=
  [L + 7 * k + 7, M + 7 * k + 2, M + 7 * k + 4, 7, 2 * K + 2 * k + lam,
    2 * K + k + mu, K - 2].getD r 0

-- Only these parts of a computed prefix are ever read. In particular, no hypothesis
-- about the values of the arbitrary middle block is needed.
private structure Pattern (K L M lam mu : ℤ) (xs : Array ℤ) : Prop where
  linear (j : ℤ) : 1 ≤ j → j ≤ K → threeTermHofstadterLookup true xs j = some j
  six : threeTermHofstadterLookup true xs (K + 1) = some 6
  cycle (k : ℤ) (r : ℕ) : r < 7 → M - 3 ≤ M + 7 * k + r → M + 7 * k + r ≤ xs.size →
    threeTermHofstadterLookup true xs (M + 7 * k + r) = some (value K L M lam mu k r)

-- The endpoint ensures that the small linear lookup stays within 1,...,K, and that
-- subtracting a large term in positions 4 or 5 selects a padded zero.
private structure Bounds (K lam mu n k : ℤ) (r : ℕ) : Prop where
  small : r ≤ 2 → n ≤ 2 * K - 2
  prevLam : r = 0 → n ≤ 2 * K + 2 * (k - 1) + lam
  prevMu : r ≤ 1 → n ≤ 2 * K + (k - 1) + mu
  currLam : 5 ≤ r → n ≤ 2 * K + 2 * k + lam
  currMu : r = 6 → n ≤ 2 * K + k + mu

private theorem bounds {K M c lam mu k : ℤ} {γ r : ℕ} (hγ : γ ≤ 6) (hr : r < 7)
    (hM : M = 2 * K - 7 * c - γ + 5)
    (hlam : -2 * c + [2, 1, 4, 3, 2, 1, 0].getD γ 0 ≤ lam)
    (hmu : -c + [0, 0, 3, 2, 1, 0, -1].getD γ 0 ≤ mu)
    (hhi : M + 7 * k + r ≤ 2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0) :
    Bounds K lam mu (M + 7 * k + r) k r := by
  interval_cases γ <;>
    dsimp [List.getD, List.getElem?_cons_zero, Option.getD_some] at hlam hmu hhi <;>
    constructor <;> intro h <;> omega

private theorem next {K L M lam mu k : ℤ} {r : ℕ} {xs : Array ℤ}
    (p : Pattern K L M lam mu xs) (hK : 7 ≤ K) (hL : 0 ≤ L) (hM : M = K + L + 5)
    (hk : 0 ≤ k) (hr : r < 7) (hn : (xs.size : ℤ) + 1 = M + 7 * k + r)
    (b : Bounds K lam mu (M + 7 * k + r) k r) :
    threeTermHofstadterNext true xs = some (value K L M lam mu k r) := by
  obtain ⟨hsmall, hprevLam, hprevMu, hcurrLam, hcurrMu⟩ := b
  -- A shift back by i positions can cross into the preceding cycle. Euclidean division
  -- accounts for that crossing even at the first step, where the cycle number becomes -1.
  have back (i : ℤ) (hi : 1 ≤ i) (hlo : M - 3 ≤ M + 7 * k + r - i) :
      threeTermHofstadterLookup true xs (M + 7 * k + r - i) =
        some (value K L M lam mu (k + ((r : ℤ) - i) / 7) (((r : ℤ) - i) % 7).toNat) := by
    have he : M + 7 * k + r - i =
        M + 7 * (k + ((r : ℤ) - i) / 7) + ((((r : ℤ) - i) % 7).toNat : ℤ) := by omega
    rw [he]
    apply p.cycle <;> omega
  have zero (j : ℤ) (hj : j ≤ 0) : threeTermHofstadterLookup true xs j = some 0 := by
    simp [threeTermHofstadterLookup, hj]
  have six (j : ℤ) (hj : j = K + 1) : threeTermHofstadterLookup true xs j = some 6 := hj ▸ p.six
  have seven (j : ℤ) (hj : j = M + 7 * k + r - 7) (hlo : M - 3 ≤ j) :
      threeTermHofstadterLookup true xs j = some (value K L M lam mu (k - 1) r) := by
    rw [show j = M + 7 * (k - 1) + r by omega]
    exact p.cycle _ _ hr (by omega) (by omega)
  simp only [threeTermHofstadterNext, hn, back 1 (by decide) (by omega),
    back 2 (by decide) (by omega), back 3 (by decide) (by omega), Option.bind_some]
  -- The seven residue cases now read padded zeros, initial values, or the same
  -- position in the preceding cycle (when the subtracted term is 7).
  interval_cases r <;>
    dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;>
    simp (disch := omega) only [zero, p.linear, six, seven, Option.bind_some,
      Option.map_some, Option.some.injEq] <;>
    (try dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some]) <;> omega

private theorem lookup_push (xs : Array ℤ) (v j : ℤ) :
    threeTermHofstadterLookup true (xs.push v) j =
      if j = (xs.size : ℤ) + 1 then some v else threeTermHofstadterLookup true xs j := by
  by_cases hj : j ≤ 0
  · simp [threeTermHofstadterLookup, hj, show j ≠ (xs.size : ℤ) + 1 by omega]
  · simp only [threeTermHofstadterLookup, hj, ite_false, Array.getElem?_push]
    simp only [show ((j - 1).toNat = xs.size) ↔ j = (xs.size : ℤ) + 1 by omega]

private theorem pattern_push {K L M lam mu k : ℤ} {r : ℕ} {xs : Array ℤ}
    (p : Pattern K L M lam mu xs) (hK : K + 1 ≤ xs.size)
    (hr : r < 7) (hn : (xs.size : ℤ) + 1 = M + 7 * k + r) :
    Pattern K L M lam mu (xs.push (value K L M lam mu k r)) := by
  constructor
  · intro j hj h
    simpa [lookup_push, show j ≠ (xs.size : ℤ) + 1 by omega] using p.linear j hj h
  · simpa [lookup_push, show K + 1 ≠ (xs.size : ℤ) + 1 by omega] using p.six
  · intro q s hs hlo hhi
    rw [lookup_push]
    split
    · have hq : q = k := by omega
      have hs' : s = r := by omega
      rw [hq, hs']
    · simp only [Array.size_push] at hhi
      exact p.cycle q s hs hlo (by omega)

private def seed (K : ℕ) (a : List ℤ) (lam mu : ℤ) : List ℤ :=
  (List.range K).map (fun i : ℕ => (i : ℤ) + 1) ++ [6] ++ a ++
    [2 * K + lam - 2, 2 * K + mu - 1, K - 2]

private theorem length_seed (K : ℕ) (a : List ℤ) (lam mu : ℤ) :
    (seed K a lam mu).length = K + a.length + 4 := by
  simp [seed]
  omega

private theorem pattern_seed (K : ℕ) (a : List ℤ) (lam mu : ℤ) :
    Pattern K a.length (K + (a.length : ℤ) + 5) lam mu (seed K a lam mu).toArray := by
  let front := (List.range K).map fun i : ℕ => (i : ℤ) + 1
  have hfront : front.length = K := by simp [front]
  have hlength : (front ++ [6] ++ a).length = K + a.length + 1 := by
    simp [hfront]
    omega
  constructor
  · intro j hj hK
    simp only [threeTermHofstadterLookup, show ¬j ≤ 0 by omega, ite_false, List.getElem?_toArray]
    change (front ++ [6] ++ a ++ _)[(j - 1).toNat]? = some j
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by simp [hfront]; omega),
      List.getElem?_append_left (by omega)]
    rw [getElem?_pos front _ (by omega)]
    simp only [front, List.getElem_map, List.getElem_range, Option.some.injEq]
    omega
  · simp only [threeTermHofstadterLookup, show ¬((K : ℤ) + 1 ≤ 0) by omega, ite_false,
      add_sub_cancel_right, Int.toNat_natCast, List.getElem?_toArray]
    change (front ++ [6] ++ a ++ _)[K]? = some 6
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by simp [hfront]),
      List.getElem?_append_right (by omega), hfront, Nat.sub_self]
    rfl
  · intro k r hr hlo hhi
    simp only [List.size_toArray, length_seed] at hhi
    have hk : k = -1 := by omega
    subst k
    have hr' : 4 ≤ r := by omega
    simp only [threeTermHofstadterLookup, show ¬((K : ℤ) + a.length + 5 + 7 * (-1) + r ≤ 0)
      by omega, ite_false, List.getElem?_toArray]
    change (front ++ [6] ++ a ++ _)[_]? = _
    rw [List.getElem?_append_right (by omega), hlength]
    rw [show ((K : ℤ) + a.length + 5 + 7 * (-1) + r - 1).toNat - (K + a.length + 1) =
      r - 4 by omega]
    interval_cases r <;>
      dsimp [value, List.getD, List.getElem?_cons_zero, Option.getD_some] <;> congr 1 <;> omega

private theorem extend {K L M lam mu last : ℤ}
    (hK : 7 ≤ K) (hL : 0 ≤ L) (hM : M = K + L + 5)
    (hb : ∀ (k : ℤ) (r : ℕ), r < 7 → M + 7 * k + r ≤ last →
      Bounds K lam mu (M + 7 * k + r) k r)
    (steps : ℕ) {xs : Array ℤ} (p : Pattern K L M lam mu xs)
    (hstart : M - 1 ≤ xs.size) (hend : (xs.size : ℤ) + steps ≤ last) :
    ∃ ys, threeTermHofstadterExtend true steps xs = some ys ∧
      ys.size = xs.size + steps ∧ Pattern K L M lam mu ys := by
  induction steps generalizing xs with
  | zero => exact ⟨xs, rfl, rfl, p⟩
  | succ steps ih =>
    let d := (xs.size : ℤ) + 1 - M
    let k := d / 7
    let r := (d % 7).toNat
    have hr : r < 7 := by dsimp [r]; omega
    have hk : 0 ≤ k := by dsimp [k, d]; omega
    have hn : (xs.size : ℤ) + 1 = M + 7 * k + r := by dsimp [r, k, d]; omega
    have hnext := next p hK hL hM hk hr hn (hb k r hr (by omega))
    have pp := pattern_push p (by omega) hr hn
    obtain ⟨ys, hext, hsize, pat⟩ := ih pp (by simp; omega) (by simp; omega)
    refine ⟨ys, ?_, ?_, pat⟩
    · simpa [threeTermHofstadterExtend, hnext] using hext
    · rw [Array.size_push] at hsize
      omega

end threeTermHofstadter_sevenCycle

open threeTermHofstadter_sevenCycle

/-- **Seven-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K$, $c$ and
$\gamma$ be natural numbers with $K \ge 7$, $c \ge 1$, $\gamma \le 6$ and $7c + \gamma \le K$, and
put $L = K - 7c - \gamma$ and $M = K + L + 5$. For a tuple $(t_0, \dots, t_6)$ write
$(t_0, \dots, t_6)_\gamma$ for its entry $t_\gamma$. Let $\lambda$ and $\mu$ be integers with
$\lambda \ge -2c + (2, 1, 4, 3, 2, 1, 0)_\gamma$ and $\mu \ge -c + (0, 0, 3, 2, 1, 0, -1)_\gamma$,
and put $\nu = (-2, -2, 2, 1, 0, -1, -2)_\gamma$. Let $a_1, \dots, a_L$ be arbitrary integers and
let $B$ be the padded three-term Hofstadter-like sequence with initial conditions
$1, 2, \dots, K, 6, a_1, \dots, a_L, 2K + \lambda - 2, 2K + \mu - 1, K - 2$. Then for every
integer $k$ and every $r \in \{0, 1, \dots, 6\}$ with $M - 3 \le M + 7k + r \le 2K + \nu$, the
term $B(M + 7k + r)$ is defined, and these terms are $B(M + 7k) = L + 7k + 7$,
$B(M + 7k + 1) = M + 7k + 2$, $B(M + 7k + 2) = M + 7k + 4$, $B(M + 7k + 3) = 7$,
$B(M + 7k + 4) = 2K + 2k + \lambda$, $B(M + 7k + 5) = 2K + k + \mu$ and $B(M + 7k + 6) = K - 2$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 3
(`jis-2024-24.7.4-lem-3`). -/
public theorem threeTermHofstadter_sevenCycle {K c γ : ℕ} (hK : 7 ≤ K) (hc : 1 ≤ c)
    (hγ : γ ≤ 6) (hL : 7 * c + γ ≤ K) {lam mu : ℤ}
    (hlam : -2 * (c : ℤ) + [2, 1, 4, 3, 2, 1, 0].getD γ 0 ≤ lam)
    (hmu : -(c : ℤ) + [0, 0, 3, 2, 1, 0, -1].getD γ 0 ≤ mu)
    (a : List ℤ) (ha : a.length = K - 7 * c - γ) (k : ℤ) (r : ℕ) (hr : r < 7)
    (hlo : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) - 3 ≤ (2 * K - 7 * c - γ + 5 : ℕ) + 7 * k + r)
    (hhi : ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r ≤
      2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0) :
    threeTermHofstadterTerm true
        ((List.range K).map (fun i : ℕ => (i : ℤ) + 1) ++ [6] ++ a ++
          [2 * K + lam - 2, 2 * K + mu - 1, K - 2])
        (((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + r).toNat =
      some ([((K - 7 * c - γ : ℕ) : ℤ) + 7 * k + 7, ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 2,
        ((2 * K - 7 * c - γ + 5 : ℕ) : ℤ) + 7 * k + 4, 7, 2 * K + 2 * k + lam, 2 * K + k + mu,
        K - 2].getD r 0) := by
  let L := K - 7 * c - γ
  let M := 2 * K - 7 * c - γ + 5
  let init := seed K a lam mu
  let n := ((M : ℤ) + 7 * k + r).toNat
  change threeTermHofstadterTerm true init n = some (value K L M lam mu k r)
  change (M : ℤ) - 3 ≤ M + 7 * k + r at hlo
  change (M : ℤ) + 7 * k + r ≤ _ at hhi
  have hML : (M : ℤ) = K + (L : ℤ) + 5 := by dsimp [M, L]; omega
  have hn : (n : ℤ) = M + 7 * k + r := by dsimp [n]; omega
  have hlen : init.length = K + L + 4 := by rw [length_seed, ha]
  have p : Pattern K L M lam mu init.toArray := by
    rw [hML, ← show a.length = L from ha]
    exact pattern_seed K a lam mu
  have hν : (-2 : ℤ) ≤ [-2, -2, 2, 1, 0, -1, -2].getD γ 0 := by
    interval_cases γ <;> decide
  have hseedEnd : (init.length : ℤ) ≤ 2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0 := by
    dsimp [L] at hlen
    omega
  have hb (q : ℤ) (s : ℕ) (hs : s < 7)
      (he : (M : ℤ) + 7 * q + s ≤ 2 * K + [-2, -2, 2, 1, 0, -1, -2].getD γ 0) :=
    bounds hγ hs (K := (K : ℤ)) (M := (M : ℤ)) (by dsimp [M]; omega) hlam hmu he
  obtain ⟨ys, hext, hsize, pat⟩ := extend (K := (K : ℤ)) (by omega) (by omega) hML hb
    (n - init.length) p (by rw [List.size_toArray]; omega) (by rw [List.size_toArray]; omega)
  simp only [threeTermHofstadterTerm, threeTermHofstadterPrefix, hext, Option.bind_some, hn]
  exact pat.cycle k r hr hlo (by simp at hsize; omega)

end MetaMathlibExt

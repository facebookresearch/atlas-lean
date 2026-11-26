/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
import Mathlib.Tactic.LinearCombination

/-!
# 1-metered parking functions

This file proves `meteredParkingCount_one_binet`, a Binet formula for the number
`meteredParkingCount 1 m n` of 1-metered `(m, n)`-parking functions when `m ≤ n + 1` and
`2 < n`.

In the 1-metered scheme a car parks in its preferred spot unless the previous car holds that spot;
then it parks in the next spot, or fails if there is none. Counting the 1-metered parking functions
by the spot of their last car shows that, for `1 ≤ m ≤ n`, those with `m` cars whose last car
parks in the last spot are as many as the 1-metered parking functions with `m - 1` cars. Hence
the counts satisfy `mpf (m + 1) = n * mpf m - mpf (m - 1)` for `1 ≤ m ≤ n`, with `mpf 0 = 1` and
`mpf 1 = n`, and the formula follows from the roots `(n ± √(n ^ 2 - 4)) / 2` of
`x ^ 2 - n * x + 1`.

## References

* Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
  Functions*, INTEGERS 25 (2025), Article A73, pp. 1–37. See Lemmas 2–3 (pp. 13–14) for the
  last-spot counts, Theorem 2 (p. 15) for the recurrence, Corollary 5 (p. 16) for the Binet
  formula, and Proposition 7 (p. 19) for the three-car count.
-/

namespace MetaMathlibExt

namespace meteredParkingCount_one_binet

/-- The spot of the last car in the 1-metered outcome of the preferences `L` on `n` spots, or
`none` when there is no car or the last car fails to park. -/
private def lastSpot (n : ℕ) (L : List ℕ) : Option ℕ :=
  ((meteredOutcome 1 n L).getLast?).bind id

/-- The spot taken, in the 1-metered scheme on `n` spots, by a car preferring spot `a` when the
previous car holds the spot `o` (`none` if no car holds a spot), or `none` if the car fails. -/
private def nextSpot (n : ℕ) (o : Option ℕ) (a : ℕ) : Option ℕ :=
  (List.range' a (n - a)).find? fun s => decide (s ∉ o.toList)

/-- The number of 1-metered parking functions with `m` cars and `n` spots whose last car parks in
spot `q`. -/
private def lastSpotCount (m n q : ℕ) : ℕ :=
  (Finset.univ.filter fun g : Fin m → Fin n =>
    IsMeteredParkingFunction 1 g ∧ lastSpot n (List.ofFn fun i => (g i : ℕ)) = some q).card

-- With a meter of one, only the spot of the last entry of the outcome is occupied.
private theorem drop_length_sub_one_filterMap (out : List (Option ℕ)) :
    (out.drop (out.length - 1)).filterMap id = (out.getLast?.bind id).toList := by
  induction out using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => cases x <;> simp

private theorem meteredOutcome_one_append (n : ℕ) (L : List ℕ) (a : ℕ) :
    meteredOutcome 1 n (L ++ [a]) = meteredOutcome 1 n L ++ [nextSpot n (lastSpot n L) a] := by
  have h : meteredOutcome 1 n (L ++ [a]) = meteredOutcome 1 n L ++
      [(List.range' a (n - a)).find? fun s => decide
        (s ∉ ((meteredOutcome 1 n L).drop ((meteredOutcome 1 n L).length - 1)).filterMap id)] := by
    simp only [meteredOutcome, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  rw [h, drop_length_sub_one_filterMap]
  rfl

private theorem lastSpot_append (n : ℕ) (L : List ℕ) (a : ℕ) :
    lastSpot n (L ++ [a]) = nextSpot n (lastSpot n L) a := by
  rw [lastSpot, meteredOutcome_one_append]
  simp

private theorem nextSpot_eq_some_iff {n a j : ℕ} {o : Option ℕ} (ha : a < n) :
    nextSpot n o a = some j ↔ (o ≠ some a ∧ j = a) ∨ (o = some a ∧ j = a + 1 ∧ a + 1 < n) := by
  obtain ⟨k, hk⟩ : ∃ k, n - a = k + 1 := ⟨n - a - 1, by omega⟩
  rw [nextSpot, hk, List.range'_succ]
  by_cases ho : o = some a
  · subst ho
    rw [List.find?_cons_of_neg (by simp)]
    rcases k with _ | k
    · simp
      omega
    · rw [List.range'_succ, List.find?_cons_of_pos (by simp)]
      simp
      omega
  · rw [List.find?_cons_of_pos (by cases o <;> simp_all [eq_comm])]
    simp [ho, eq_comm]

private theorem nextSpot_eq_none_iff {n a : ℕ} {o : Option ℕ} (ha : a < n) :
    nextSpot n o a = none ↔ o = some a ∧ a + 1 = n := by
  obtain ⟨k, hk⟩ : ∃ k, n - a = k + 1 := ⟨n - a - 1, by omega⟩
  rw [nextSpot, hk, List.range'_succ]
  by_cases ho : o = some a
  · subst ho
    rw [List.find?_cons_of_neg (by simp)]
    rcases k with _ | k
    · simp
      omega
    · rw [List.range'_succ, List.find?_cons_of_pos (by simp)]
      simp
      omega
  · rw [List.find?_cons_of_pos (by cases o <;> simp_all [eq_comm])]
    simp [ho]

private theorem ofFn_snoc {m n : ℕ} (g : Fin m → Fin n) (a : Fin n) :
    (List.ofFn fun i => ((Fin.snoc g a : Fin (m + 1) → Fin n) i : ℕ)) =
      (List.ofFn fun i => (g i : ℕ)) ++ [(a : ℕ)] := by
  rw [List.ofFn_succ_last]
  simp

private theorem isMeteredParkingFunction_snoc_iff {m n : ℕ} (g : Fin m → Fin n) (a : Fin n) :
    IsMeteredParkingFunction 1 (Fin.snoc g a : Fin (m + 1) → Fin n) ↔
      IsMeteredParkingFunction 1 g ∧
        nextSpot n (lastSpot n (List.ofFn fun i => (g i : ℕ))) a ≠ none := by
  simp only [IsMeteredParkingFunction, ofFn_snoc, meteredOutcome_one_append, List.mem_append,
    List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun o ho => h o (Or.inl ho), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ o (ho | rfl)
    exacts [h1 o ho, h2]

private theorem lastSpot_snoc {m n : ℕ} (g : Fin m → Fin n) (a : Fin n) :
    lastSpot n (List.ofFn fun i => ((Fin.snoc g a : Fin (m + 1) → Fin n) i : ℕ)) =
      nextSpot n (lastSpot n (List.ofFn fun i => (g i : ℕ))) a := by
  rw [ofFn_snoc, lastSpot_append]

-- Count the maps on `m + 1` cars by their restriction to the first `m` cars and the last value.
private theorem card_filter_snoc {m n : ℕ} (P : (Fin (m + 1) → Fin n) → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ g : Fin m → Fin n, (Finset.univ.filter fun a : Fin n => P (Fin.snoc g a)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.snocEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type_right]
  rfl

-- Whatever spot the previous car holds, exactly one preference makes the next car fail when that
-- spot is the last one, and none otherwise.
private theorem card_nextSpot_ne_none {n : ℕ} (hn : 0 < n) (o : Option ℕ) :
    (Finset.univ.filter fun a : Fin n => nextSpot n o a ≠ none).card +
        (if o = some (n - 1) then 1 else 0) = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => nextSpot n o a ≠ none)
  simp only [not_not, Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun a : Fin n => nextSpot n o a = none).card =
      if o = some (n - 1) then 1 else 0 := by
    split_ifs with ho
    · subst ho
      rw [Finset.card_eq_one]
      refine ⟨⟨n - 1, by omega⟩, ?_⟩
      ext a
      simp [nextSpot_eq_none_iff a.2, Fin.ext_iff]
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ h
      rw [nextSpot_eq_none_iff a.2] at h
      exact ho (h.1.trans (by congr 1; omega))
  omega

-- The next car parks in spot `0` exactly when it prefers spot `0` and the previous car does not
-- hold it.
private theorem card_nextSpot_eq_zero {n : ℕ} (hn : 0 < n) (o : Option ℕ) :
    (Finset.univ.filter fun a : Fin n => nextSpot n o a = some 0).card +
        (if o = some 0 then 1 else 0) = 1 := by
  rcases o with _ | p
  · have : (Finset.univ.filter fun a : Fin n => nextSpot n none a = some 0) = {⟨0, hn⟩} := by
      ext a
      simp [nextSpot_eq_some_iff a.2, Fin.ext_iff]
      omega
    simp [this]
  · by_cases hp : p = 0
    · subst hp
      have : (Finset.univ.filter fun a : Fin n => nextSpot n (some 0) a = some 0) = ∅ := by
        ext a
        simp [nextSpot_eq_some_iff a.2]
      simp [this]
    · have : (Finset.univ.filter fun a : Fin n => nextSpot n (some p) a = some 0) = {⟨0, hn⟩} := by
        ext a
        simp [nextSpot_eq_some_iff a.2, Fin.ext_iff]
        omega
      simp [this, hp]

-- The next car parks in spot `j + 1` when it prefers that spot and the previous car does not hold
-- it, or when it prefers spot `j` and the previous car holds spot `j`.
private theorem card_nextSpot_eq_succ {n j : ℕ} (hj : j + 1 < n) (o : Option ℕ) :
    (Finset.univ.filter fun a : Fin n => nextSpot n o a = some (j + 1)).card +
        (if o = some (j + 1) then 1 else 0) = 1 + (if o = some j then 1 else 0) := by
  rcases o with _ | p
  · have : (Finset.univ.filter fun a : Fin n => nextSpot n none a = some (j + 1)) =
        {⟨j + 1, hj⟩} := by
      ext a
      simp [nextSpot_eq_some_iff a.2, Fin.ext_iff]
      omega
    simp [this]
  · by_cases h1 : p = j + 1
    · subst h1
      have : (Finset.univ.filter fun a : Fin n => nextSpot n (some (j + 1)) a = some (j + 1)) =
          ∅ := by
        ext a
        simp [nextSpot_eq_some_iff a.2]
        omega
      simp [this]
    · by_cases h2 : p = j
      · subst h2
        have : (Finset.univ.filter fun a : Fin n => nextSpot n (some p) a = some (p + 1)) =
            {⟨p, by omega⟩, ⟨p + 1, hj⟩} := by
          ext a
          simp [nextSpot_eq_some_iff a.2, Fin.ext_iff]
          omega
        rw [this, Finset.card_pair (by simp [Fin.ext_iff])]
        simp
      · have : (Finset.univ.filter fun a : Fin n => nextSpot n (some p) a = some (j + 1)) =
            {⟨j + 1, hj⟩} := by
          ext a
          simp [nextSpot_eq_some_iff a.2, Fin.ext_iff]
          omega
        simp [this, h1, h2]

private theorem lastSpotCount_eq_sum (m n q : ℕ) :
    lastSpotCount m n q =
      ∑ g ∈ Finset.univ.filter (fun g : Fin m → Fin n => IsMeteredParkingFunction 1 g),
        if lastSpot n (List.ofFn fun i => (g i : ℕ)) = some q then 1 else 0 := by
  rw [lastSpotCount, ← Finset.card_filter, Finset.filter_filter]

private theorem lastSpotCount_zero_left (n q : ℕ) : lastSpotCount 0 n q = 0 := by
  rw [lastSpotCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ h
  simp [lastSpot, meteredOutcome] at h

private theorem count_zero (n : ℕ) : meteredParkingCount 1 0 n = 1 := by
  rw [meteredParkingCount, Finset.filter_true_of_mem fun g _ => ?_]
  · simp
  · simp [IsMeteredParkingFunction, meteredOutcome]

private theorem count_succ (m n : ℕ) :
    meteredParkingCount 1 (m + 1) n =
      ∑ g ∈ Finset.univ.filter (fun g : Fin m → Fin n => IsMeteredParkingFunction 1 g),
        (Finset.univ.filter fun a : Fin n =>
          nextSpot n (lastSpot n (List.ofFn fun i => (g i : ℕ))) a ≠ none).card := by
  rw [meteredParkingCount, card_filter_snoc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [isMeteredParkingFunction_snoc_iff]
  split_ifs with hg <;> simp [hg]

private theorem lastSpotCount_succ (m n q : ℕ) :
    lastSpotCount (m + 1) n q =
      ∑ g ∈ Finset.univ.filter (fun g : Fin m → Fin n => IsMeteredParkingFunction 1 g),
        (Finset.univ.filter fun a : Fin n =>
          nextSpot n (lastSpot n (List.ofFn fun i => (g i : ℕ))) a = some q).card := by
  rw [lastSpotCount, card_filter_snoc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [isMeteredParkingFunction_snoc_iff, lastSpot_snoc]
  split_ifs with hg
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg]
    exact ⟨fun h => h.2, fun h => ⟨by simp [h], h⟩⟩
  · simp [hg]

-- A car can be added after a 1-metered parking function in `n` ways, except in `n - 1` ways when
-- the last car parks in the last spot.
private theorem count_succ_add_lastSpotCount (m : ℕ) {n : ℕ} (hn : 0 < n) :
    meteredParkingCount 1 (m + 1) n + lastSpotCount m n (n - 1) =
      n * meteredParkingCount 1 m n := by
  rw [count_succ, lastSpotCount_eq_sum, ← Finset.sum_add_distrib, meteredParkingCount,
    Finset.card_eq_sum_ones, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [mul_one]; exact card_nextSpot_ne_none hn _

private theorem lastSpotCount_succ_zero (m : ℕ) {n : ℕ} (hn : 0 < n) :
    lastSpotCount (m + 1) n 0 + lastSpotCount m n 0 = meteredParkingCount 1 m n := by
  rw [lastSpotCount_succ, lastSpotCount_eq_sum, ← Finset.sum_add_distrib, meteredParkingCount,
    Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun g _ => card_nextSpot_eq_zero hn _

private theorem lastSpotCount_succ_succ (m : ℕ) {n j : ℕ} (hj : j + 1 < n) :
    lastSpotCount (m + 1) n (j + 1) + lastSpotCount m n (j + 1) =
      meteredParkingCount 1 m n + lastSpotCount m n j := by
  rw [lastSpotCount_succ, lastSpotCount_eq_sum, lastSpotCount_eq_sum, ← Finset.sum_add_distrib,
    meteredParkingCount, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun g _ => card_nextSpot_eq_succ hj _

-- For `m ≤ j < n`, as many 1-metered parking functions with `m + 1` cars end in spot `j` as there
-- are 1-metered parking functions with `m` cars.
private theorem lastSpotCount_succ_eq (n : ℕ) :
    ∀ m j, m ≤ j → j < n → lastSpotCount (m + 1) n j = meteredParkingCount 1 m n := by
  intro m
  induction m with
  | zero =>
    intro j _ hj
    rcases j with _ | j
    · have := lastSpotCount_succ_zero 0 hj
      rw [lastSpotCount_zero_left] at this
      omega
    · have := lastSpotCount_succ_succ 0 hj
      rw [lastSpotCount_zero_left, lastSpotCount_zero_left] at this
      omega
  | succ m ih =>
    intro j hmj hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h := lastSpotCount_succ_succ (m + 1) hj
    rw [ih (j + 1) (by omega) hj, ih j (by omega) (by omega)] at h
    omega

private theorem count_recursion {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    meteredParkingCount 1 (m + 1) n + meteredParkingCount 1 (m - 1) n =
      n * meteredParkingCount 1 m n := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h := count_succ_add_lastSpotCount (m + 1) (n := n) (by omega)
  rw [lastSpotCount_succ_eq n m (n - 1) (by omega) (by omega)] at h
  simpa using h

private theorem count_one {n : ℕ} (hn : 0 < n) : meteredParkingCount 1 1 n = n := by
  have h := count_succ_add_lastSpotCount 0 hn
  rw [lastSpotCount_zero_left, count_zero] at h
  simpa using h

-- A sequence with `T 0 = 1`, `T 1 = n` and `T (k + 2) = n * T (k + 1) - T k` while `k < N` is
-- given by the Binet formula up to `N + 1`.
private theorem binet_of_recursion (N : ℕ) {n s : ℝ} (hn : 3 ≤ n) (hs2 : s ^ 2 = n ^ 2 - 4)
    (hs : 0 < s) (T : ℕ → ℝ) (h0 : T 0 = 1) (h1 : T 1 = n)
    (hrec : ∀ k, k + 1 ≤ N → T (k + 2) = n * T (k + 1) - T k) :
    ∀ m ≤ N + 1, T m = (n * (n + s) - 2) / (n * (n + s) - 4) * ((n + s) / 2) ^ m +
        (n * (n - s) - 2) / (n * (n - s) - 4) * ((n - s) / 2) ^ m := by
  have hu : n * (n + s) - 4 ≠ 0 := by nlinarith
  have hv : n * (n - s) - 4 ≠ 0 := by
    intro h
    have h' : (n - s) * s = 0 := by linear_combination -h - hs2
    rcases mul_eq_zero.mp h' with h'' | h''
    · have : n = s := by linarith
      subst this
      linarith
    · linarith
  have hA : (n * (n + s) - 2) / (n * (n + s) - 4) = (n + s) / (2 * s) := by
    rw [div_eq_div_iff hu (by positivity)]
    linear_combination n * hs2
  have hB : (n * (n - s) - 2) / (n * (n - s) - 4) = -(n - s) / (2 * s) := by
    rw [div_eq_div_iff hv (by positivity)]
    linear_combination -n * hs2
  have hα : ((n + s) / 2) ^ 2 = n * ((n + s) / 2) - 1 := by linear_combination (1 / 4) * hs2
  have hβ : ((n - s) / 2) ^ 2 = n * ((n - s) / 2) - 1 := by linear_combination (1 / 4) * hs2
  have key : ∀ k, k ≤ N → T k * s = ((n + s) / 2) ^ (k + 1) - ((n - s) / 2) ^ (k + 1) ∧
      T (k + 1) * s = ((n + s) / 2) ^ (k + 2) - ((n - s) / 2) ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [h0, h1]
      constructor <;> ring
    | succ k ih =>
      intro hk
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      have hR : T (k + 1 + 1) = n * T (k + 1) - T k := hrec k (by omega)
      refine ⟨ih1, ?_⟩
      linear_combination s * hR + n * ih1 - ih0 - ((n + s) / 2) ^ (k + 1) * hα +
        ((n - s) / 2) ^ (k + 1) * hβ
  intro m hm
  have hTm : T m * s = ((n + s) / 2) ^ (m + 1) - ((n - s) / 2) ^ (m + 1) := by
    rcases m with _ | m
    · exact (key 0 (Nat.zero_le _)).1
    · exact (key m (by omega)).2
  rw [hA, hB]
  apply mul_right_cancel₀ hs.ne'
  rw [hTm]
  field_simp
  ring

end meteredParkingCount_one_binet

/-- **Binet formula for 1-metered parking functions.** Let $m, n$ be natural numbers with
$m \le n + 1$ and $n > 2$. Then the number $\mathrm{mpf}_{m,n}(1)$ of $1$-metered
$(m, n)$-parking functions satisfies, as real numbers,
$$\mathrm{mpf}_{m,n}(1) = \frac{n(n + \sqrt{n^2-4}) - 2}{n(n + \sqrt{n^2-4}) - 4}
\left(\frac{n + \sqrt{n^2-4}}{2}\right)^m +
\frac{n(n - \sqrt{n^2-4}) - 2}{n(n - \sqrt{n^2-4}) - 4}
\left(\frac{n - \sqrt{n^2-4}}{2}\right)^m.$$

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 5 (`integers-2025-A73-cor-5`). -/
public theorem meteredParkingCount_one_binet {m n : ℕ} (hm : m ≤ n + 1) (hn : 2 < n) :
    (meteredParkingCount 1 m n : ℝ) =
      (n * (n + Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n + Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n + Real.sqrt (n ^ 2 - 4)) / 2) ^ m +
        (n * (n - Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n - Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n - Real.sqrt (n ^ 2 - 4)) / 2) ^ m := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 - 4 := by nlinarith
  refine meteredParkingCount_one_binet.binet_of_recursion n hn3 (Real.sq_sqrt hpos.le)
    (Real.sqrt_pos.mpr hpos) (fun k => (meteredParkingCount 1 k n : ℝ)) ?_ ?_ ?_ m hm
  · simp [meteredParkingCount_one_binet.count_zero]
  · simp [meteredParkingCount_one_binet.count_one (by omega : 0 < n)]
  · intro k hk
    have h := meteredParkingCount_one_binet.count_recursion (m := k + 1) (n := n) (by omega)
      (by omega)
    rw [Nat.add_sub_cancel] at h
    have h' : (meteredParkingCount 1 (k + 2) n : ℝ) + meteredParkingCount 1 k n =
        n * meteredParkingCount 1 (k + 1) n := by exact_mod_cast h
    linarith

/-- **1-metered parking functions with three cars.** For every natural number $n \ge 2$, the
number of $1$-metered $(3, n)$-parking functions is $\mathrm{mpf}_{3,n}(1) = n^3 - 2n$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 7 (`integers-2025-A73-prop-7`). -/
public theorem meteredParkingCount_one_three {n : ℕ} (hn : 2 ≤ n) :
    meteredParkingCount 1 3 n = n ^ 3 - 2 * n := by
  have hone := meteredParkingCount_one_binet.count_one (by omega : 0 < n)
  have htwo : meteredParkingCount 1 2 n + 1 = n ^ 2 := by
    have h := meteredParkingCount_one_binet.count_recursion (m := 1) (n := n) (by decide)
      (by omega)
    change meteredParkingCount 1 2 n + meteredParkingCount 1 0 n =
      n * meteredParkingCount 1 1 n at h
    simpa only [meteredParkingCount_one_binet.count_zero, hone, pow_two] using h
  have hthree : meteredParkingCount 1 3 n + n = n * meteredParkingCount 1 2 n := by
    have h := meteredParkingCount_one_binet.count_recursion (m := 2) (n := n) (by decide) hn
    change meteredParkingCount 1 3 n + meteredParkingCount 1 1 n =
      n * meteredParkingCount 1 2 n at h
    simpa only [hone] using h
  have hscaled : n * meteredParkingCount 1 2 n + n = n ^ 3 := by
    simpa only [Nat.mul_add, Nat.mul_one, pow_succ' n 2] using congrArg (n * ·) htwo
  omega

end MetaMathlibExt

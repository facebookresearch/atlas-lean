/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating sum- and difference-dominated sets from shifted copies

A finite set `A ⊆ ℤ` is MSTD (sum-dominated) when `|A + A| > |A - A|` and MDTS
(difference-dominated) when `|A - A| > |A + A|`; both are written out with Mathlib's pointwise
`Finset` operations.

The main result, `alternating_sequence_of_copies`, is the construction of Theorem 2.1 of
Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and Steven Senger,
*Additional Constructions of Sequences of Alternating Sum and Difference Dominated Sets*
(arXiv:2509.12829; INTEGERS 26 (2026), Article A88): start from an MSTD set `A₁ ⊆ [0, n)`
containing `0` that satisfies two counting conditions, and alternately adjoin the point `l * n`
and the copy `A₁ + {l * n}`. The resulting sets increase strictly and are alternately MDTS and
MSTD.

The bounds `0 ≤ a < n` for `a ∈ A₁` are part of the statement. The arXiv statement asks only for
`0 ∈ A₁` and `n > max A₁`, and the conclusion can fail without `0 ≤ a`: the translate
`A₁ = {-14, -12, -11, -10, -7, -3, -2, 0}` of the Conway set with `n = 3` meets those hypotheses
and both counting conditions, yet `A₁ ∪ (A₁ + {3})` has `33` sums and `33` differences.

## Proof outline

Write `S = A₁ + A₁` and `D = A₁ - A₁`. The odd-indexed set `A (2 * k + 1)` is the union of the
copies `A₁ + {j * n}` for `0 ≤ j ≤ k`. Its sumset is `S` plus the multiples `0, n, …, 2 * k * n`,
and its difference set is a translate of `D` plus the same multiples. The elements of `S`, and
those of `D`, are less than `2 * n` apart, so adding these multiples adds `2 * k` new elements per
residue class modulo `n` that the set meets. By condition (a), `S` and `D` meet equally many
classes, so every odd-indexed set keeps the excess `|S| - |D| > 0` of sums over differences.
Adjoining `l * n` to `A (2 * l - 1)` adds at most `x + 1` sums and at least `2 * y` differences,
so condition (b) makes `A (2 * l)` difference-dominated.
-/

namespace MetaMathlibExt

open scoped Pointwise

namespace AlternatingSequenceOfCopies

/-- The integers `t + j * n` with `t ∈ T` and `0 ≤ j ≤ m`. -/
private def shifts (T : Finset ℤ) (n : ℤ) (m : ℕ) : Finset ℤ :=
  T + (Finset.range (m + 1)).image fun j : ℕ => (j : ℤ) * n

private theorem mem_shifts {T : Finset ℤ} {n : ℤ} {m : ℕ} {z : ℤ} :
    z ∈ shifts T n m ↔ ∃ t ∈ T, ∃ j : ℕ, j ≤ m ∧ t + j * n = z := by
  simp only [shifts, Finset.mem_add, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨t, ht, j, by omega, rfl⟩
  · rintro ⟨t, ht, j, hj, rfl⟩
    exact ⟨t, ht, _, ⟨j, by omega, rfl⟩, rfl⟩

/-- In a set whose elements are less than `2 * n` apart, the elements `t` with `t + n` outside
the set meet each residue class modulo `n` of the set exactly once. -/
private theorem card_filter_add_notMem {n : ℤ} (hn : 0 < n) {T : Finset ℤ}
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t' < t + 2 * n) :
    (T.filter fun t => t + n ∉ T).card = (T.image (· % n)).card := by
  rw [← Finset.card_image_of_injOn (f := (· % n))]
  · congr 1
    ext r
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨t, ⟨ht, _⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      by_cases htn : t + n ∈ T
      · refine ⟨t + n, ⟨htn, fun h => ?_⟩, Int.add_emod_right t n⟩
        have := hT t ht _ h
        linarith
      · exact ⟨t, ⟨ht, htn⟩, rfl⟩
  · intro t ht t' ht' h
    have ht := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    have ht' := Finset.mem_filter.1 (Finset.mem_coe.1 ht')
    obtain ⟨k, hk⟩ := Int.ModEq.dvd (n := n) (a := t) (b := t') h
    have h1 := hT t ht.1 t' ht'.1
    have h2 := hT t' ht'.1 t ht.1
    have hk2 : k < 2 := by nlinarith
    have hk2' : -2 < k := by nlinarith
    interval_cases k
    · exact absurd ((show t = t' + n by linarith) ▸ ht.1) ht'.2
    · linarith
    · exact absurd ((show t' = t + n by linarith) ▸ ht'.1) ht.2

/-- Adding the multiples `0, n, …, m * n` to a set whose elements are less than `2 * n` apart
adds `m` new elements per residue class modulo `n` met by the set. -/
private theorem card_shifts {n : ℤ} (hn : 0 < n) {T : Finset ℤ}
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t' < t + 2 * n) (m : ℕ) :
    (shifts T n m).card = T.card + m * (T.filter fun t => t + n ∉ T).card := by
  induction m with
  | zero =>
    have h : shifts T n 0 = T := by
      ext z
      rw [mem_shifts]
      constructor
      · rintro ⟨t, ht, j, hj, rfl⟩
        obtain rfl : j = 0 := by omega
        simpa using ht
      · intro hz
        exact ⟨z, hz, 0, le_rfl, by simp⟩
    simp [h]
  | succ m ih =>
    set U := (T.filter fun t => t + n ∉ T).image (· + ((m + 1 : ℕ) : ℤ) * n) with hU
    have hsplit : shifts T n (m + 1) = shifts T n m ∪ U := by
      ext z
      simp only [hU, Finset.mem_union, Finset.mem_image, Finset.mem_filter, mem_shifts]
      constructor
      · rintro ⟨t, ht, j, hj, rfl⟩
        rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
        · exact Or.inl ⟨t, ht, j, by omega, rfl⟩
        · obtain rfl : j = m + 1 := by omega
          by_cases htn : t + n ∈ T
          · refine Or.inl ⟨t + n, htn, m, le_rfl, ?_⟩
            push_cast
            ring
          · exact Or.inr ⟨t, ⟨ht, htn⟩, rfl⟩
      · rintro (⟨t, ht, j, hj, rfl⟩ | ⟨t, ⟨ht, _⟩, rfl⟩)
        · exact ⟨t, ht, j, by omega, rfl⟩
        · exact ⟨t, ht, m + 1, le_rfl, rfl⟩
    have hdisj : Disjoint (shifts T n m) U := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      rw [mem_shifts] at hz
      obtain ⟨t', ht', j, hj, rfl⟩ := hz
      simp only [hU, Finset.mem_image, Finset.mem_filter] at hz'
      obtain ⟨t, ⟨ht, htn⟩, he⟩ := hz'
      push_cast at he
      have hj' : (j : ℤ) ≤ m := by exact_mod_cast hj
      have hlt := hT t ht t' ht'
      have key : t' - t = ((m : ℤ) + 1 - j) * n := by linear_combination -he
      have hk2 : (m : ℤ) + 1 - j < 2 := by
        by_contra hcon
        have hcon := not_lt.1 hcon
        nlinarith
      have hjm : (j : ℤ) = m := by omega
      rw [hjm] at key
      exact htn ((show t' = t + n by linarith) ▸ ht')
    have hcardU : U.card = (T.filter fun t => t + n ∉ T).card :=
      Finset.card_image_of_injective _ (add_left_injective _)
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, hcardU]
    ring

end AlternatingSequenceOfCopies

open AlternatingSequenceOfCopies in
/-- **Alternating sum- and difference-dominated sets from shifted copies.** For a set $S$ of
integers write $S + S = \{s + s' : s, s' \in S\}$ and $S - S = \{s - s' : s, s' \in S\}$. Let $A_1$
be a finite set of integers with $|A_1 - A_1| < |A_1 + A_1|$ and $0 \in A_1$, and let $n$ be an
integer with $0 \le a < n$ for every $a \in A_1$. Suppose that (a) $A_1 + A_1$ and $A_1 - A_1$
meet the same number of residue classes modulo $n$, and (b) with
$x = \#\{a \in A_1 : n + a \notin A_1 + A_1\}$ and $y = \#\{b \in A_1 : n - b \notin A_1 - A_1\}$
we have $2y - x - 1 > |A_1 + A_1| - |A_1 - A_1|$. Let $A_1, A_2, A_3, \dots$ be finite sets of
integers, starting with this $A_1$, such that for every $l \ge 1$, $A_{2l} = A_{2l-1} \cup \{ln\}$
and $A_{2l+1} = A_{2l-1} \cup \{a + ln : a \in A_1\}$. Then for every $l \ge 1$,
$|A_{2l} + A_{2l}| < |A_{2l} - A_{2l}|$, $|A_{2l+1} - A_{2l+1}| < |A_{2l+1} + A_{2l+1}|$ and
$A_{2l-1} \subsetneq A_{2l} \subsetneq A_{2l+1}$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 1 (`integers-2026-A88-thm-1`). -/
public theorem alternating_sequence_of_copies (A₁ : Finset ℤ) (n : ℤ)
    (hmstd : (A₁ - A₁).card < (A₁ + A₁).card) (h0 : 0 ∈ A₁) (hn : ∀ a ∈ A₁, 0 ≤ a ∧ a < n)
    (hmod : ((A₁ + A₁).image (· % n)).card = ((A₁ - A₁).image (· % n)).card)
    (hxy : 2 * ((A₁.filter fun b => n - b ∉ A₁ - A₁).card : ℤ) -
        (A₁.filter fun a => n + a ∉ A₁ + A₁).card - 1 >
      ((A₁ + A₁).card : ℤ) - (A₁ - A₁).card)
    (A : ℕ → Finset ℤ) (h1 : A 1 = A₁)
    (heven : ∀ l ≥ 1, A (2 * l) = A (2 * l - 1) ∪ {(l : ℤ) * n})
    (hodd : ∀ l ≥ 1, A (2 * l + 1) = A (2 * l - 1) ∪ (A₁ + {(l : ℤ) * n})) :
    ∀ l ≥ 1, (A (2 * l) + A (2 * l)).card < (A (2 * l) - A (2 * l)).card ∧
      (A (2 * l + 1) - A (2 * l + 1)).card < (A (2 * l + 1) + A (2 * l + 1)).card ∧
      A (2 * l - 1) ⊂ A (2 * l) ∧ A (2 * l) ⊂ A (2 * l + 1) := by
  have hn0 : 0 < n := (hn 0 h0).2
  -- The odd-indexed sets are the unions of the copies `A₁ + j * n`, `0 ≤ j ≤ k`.
  have hoddmem (k : ℕ) (z : ℤ) :
      z ∈ A (2 * k + 1) ↔ ∃ a ∈ A₁, ∃ j : ℕ, j ≤ k ∧ a + j * n = z := by
    induction k generalizing z with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, h1]
      constructor
      · intro hz
        exact ⟨z, hz, 0, le_rfl, by simp⟩
      · rintro ⟨a, ha, j, hj, rfl⟩
        obtain rfl : j = 0 := by omega
        simpa using ha
    | succ k ih =>
      have hA := hodd (k + 1) (by omega)
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hA
      rw [hA, Finset.mem_union, ih, Finset.mem_add]
      simp only [Finset.mem_singleton]
      constructor
      · rintro (⟨a, ha, j, hj, rfl⟩ | ⟨a, ha, _, rfl, rfl⟩)
        · exact ⟨a, ha, j, by omega, rfl⟩
        · exact ⟨a, ha, k + 1, le_rfl, rfl⟩
      · rintro ⟨a, ha, j, hj, rfl⟩
        rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · exact Or.inl ⟨a, ha, j, by omega, rfl⟩
        · obtain rfl : j = k + 1 := by omega
          exact Or.inr ⟨a, ha, _, rfl, rfl⟩
  -- Bounds on the copies.
  have hbound (k : ℕ) (z : ℤ) (hz : z ∈ A (2 * k + 1)) : 0 ≤ z ∧ z < ((k : ℤ) + 1) * n := by
    obtain ⟨a, ha, j, hj, rfl⟩ := (hoddmem k z).1 hz
    have hj' : (j : ℤ) ≤ k := by exact_mod_cast hj
    have := hn a ha
    constructor <;> nlinarith
  set S := A₁ + A₁ with hSdef
  set D := A₁ - A₁ with hDdef
  have hSsep : ∀ t ∈ S, ∀ t' ∈ S, t' < t + 2 * n := by
    intro t ht t' ht'
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 ht
    obtain ⟨a', ha', b', hb', rfl⟩ := Finset.mem_add.1 ht'
    linarith [hn a ha, hn b hb, hn a' ha', hn b' hb']
  have hDsep : ∀ t ∈ D, ∀ t' ∈ D, t' < t + 2 * n := by
    intro t ht t' ht'
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 ht
    obtain ⟨a', ha', b', hb', rfl⟩ := Finset.mem_sub.1 ht'
    linarith [hn a ha, hn b hb, hn a' ha', hn b' hb']
  set R := (S.filter fun t => t + n ∉ S).card with hRdef
  have hRD : (D.filter fun t => t + n ∉ D).card = R := by
    rw [hRdef, card_filter_add_notMem hn0 hSsep, card_filter_add_notMem hn0 hDsep, hmod]
  -- Sums and differences of the odd-indexed sets.
  have hsum (k : ℕ) : (A (2 * k + 1) + A (2 * k + 1)).card = S.card + 2 * k * R := by
    have h : A (2 * k + 1) + A (2 * k + 1) = shifts S n (2 * k) := by
      ext z
      rw [Finset.mem_add, mem_shifts]
      constructor
      · rintro ⟨u, hu, v, hv, rfl⟩
        obtain ⟨a, ha, j, hj, rfl⟩ := (hoddmem k u).1 hu
        obtain ⟨b, hb, i, hi, rfl⟩ := (hoddmem k v).1 hv
        refine ⟨a + b, Finset.add_mem_add ha hb, j + i, by omega, ?_⟩
        push_cast
        ring
      · rintro ⟨s, hs, i, hi, rfl⟩
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hs
        refine ⟨a + ((min i k : ℕ) : ℤ) * n, (hoddmem k _).2 ⟨a, ha, _, min_le_right i k, rfl⟩,
          b + ((i - min i k : ℕ) : ℤ) * n, (hoddmem k _).2 ⟨b, hb, _, by omega, rfl⟩, ?_⟩
        have hi' : ((min i k : ℕ) : ℤ) + ((i - min i k : ℕ) : ℤ) = i := by
          exact_mod_cast (show min i k + (i - min i k) = i by omega)
        linear_combination n * hi'
    rw [h, card_shifts hn0 hSsep]
  have hdiff (k : ℕ) : (A (2 * k + 1) - A (2 * k + 1)).card = D.card + 2 * k * R := by
    have h : shifts D n (2 * k) = (A (2 * k + 1) - A (2 * k + 1)).image (· + (k : ℤ) * n) := by
      ext w
      rw [mem_shifts, Finset.mem_image]
      constructor
      · rintro ⟨d, hd, i, hi, rfl⟩
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 hd
        refine ⟨(a + ((i - k : ℕ) : ℤ) * n) - (b + ((k - i : ℕ) : ℤ) * n),
          Finset.sub_mem_sub ((hoddmem k _).2 ⟨a, ha, _, by omega, rfl⟩)
            ((hoddmem k _).2 ⟨b, hb, _, by omega, rfl⟩), ?_⟩
        have hi' : ((i - k : ℕ) : ℤ) + k = i + ((k - i : ℕ) : ℤ) := by
          exact_mod_cast (show i - k + k = i + (k - i) by omega)
        linear_combination n * hi'
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.1 hz
        obtain ⟨a, ha, j, hj, rfl⟩ := (hoddmem k u).1 hu
        obtain ⟨b, hb, i, hi, rfl⟩ := (hoddmem k v).1 hv
        refine ⟨a - b, Finset.sub_mem_sub ha hb, j + k - i, by omega, ?_⟩
        have hi' : ((j + k - i : ℕ) : ℤ) + i = j + k := by
          exact_mod_cast (show j + k - i + i = j + k by omega)
        linear_combination n * hi'
    rw [← Finset.card_image_of_injective _ (add_left_injective ((k : ℤ) * n)), ← h,
      card_shifts hn0 hDsep, hRD]
  -- A nonzero element of `A₁`: otherwise `A₁ = {0}` has as many sums as differences.
  obtain ⟨a₀, ha₀, ha₀0⟩ : ∃ a ∈ A₁, a ≠ 0 := by
    by_contra! h
    have hA : A₁ = {0} := Finset.eq_singleton_iff_unique_mem.2 ⟨h0, h⟩
    simp [hSdef, hDdef, hA] at hmstd
  intro l hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  set C := A (2 * k + 1)
  set c₀ : ℤ := ((k + 1 : ℕ) : ℤ) * n with hc₀
  have hE : A (2 * (k + 1)) = C ∪ {c₀} := by
    rw [heven (k + 1) (by omega), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hF : A (2 * (k + 1) + 1) = C ∪ (A₁ + {c₀}) := by
    rw [hodd (k + 1) (by omega), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hc₀C : c₀ ∉ C := fun h => by
    have := (hbound k c₀ h).2
    rw [hc₀] at this
    push_cast at this
    exact lt_irrefl _ this
  have hc₀' : c₀ = ((k : ℤ) + 1) * n := by
    rw [hc₀]
    push_cast
    ring
  have hnc₀ : n ≤ c₀ := by
    rw [hc₀']
    have hk0 : (0 : ℤ) ≤ k := by positivity
    nlinarith
  -- `A (2 * l)` has at most `x + 1` sums outside `C + C`.
  have hsumE : (A (2 * (k + 1)) + A (2 * (k + 1))).card ≤
      (C + C).card + (A₁.filter fun a => n + a ∉ S).card + 1 := by
    set X := (A₁.filter fun a => n + a ∉ S).image (· + (2 * (k : ℤ) + 1) * n)
    have hshift (u : ℤ) (hu : u ∈ C) : u + c₀ ∈ C + C ∪ X := by
      obtain ⟨a, ha, j, hj, rfl⟩ := (hoddmem k u).1 hu
      rcases Nat.lt_or_ge j k with hjk | hjk
      · refine Finset.mem_union_left _ (Finset.mem_add.2 ⟨a + ((j + 1 : ℕ) : ℤ) * n,
          (hoddmem k _).2 ⟨a, ha, j + 1, by omega, rfl⟩, 0 + (k : ℤ) * n,
          (hoddmem k _).2 ⟨0, h0, k, le_rfl, rfl⟩, ?_⟩)
        rw [hc₀']
        push_cast
        ring
      · have hjk' : (j : ℤ) = k := by exact_mod_cast le_antisymm hj hjk
        by_cases has : n + a ∈ S
        · obtain ⟨b, hb, b', hb', hbb⟩ := Finset.mem_add.1 has
          refine Finset.mem_union_left _ (Finset.mem_add.2 ⟨b + (k : ℤ) * n,
            (hoddmem k _).2 ⟨b, hb, k, le_rfl, rfl⟩, b' + (k : ℤ) * n,
            (hoddmem k _).2 ⟨b', hb', k, le_rfl, rfl⟩, ?_⟩)
          rw [hc₀']
          linear_combination hbb - n * hjk'
        · refine Finset.mem_union_right _
            (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, has⟩, ?_⟩)
          rw [hc₀']
          linear_combination (-n) * hjk'
    have hsub : A (2 * (k + 1)) + A (2 * (k + 1)) ⊆ (C + C ∪ X) ∪ {c₀ + c₀} := by
      rw [hE]
      intro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 hz
      rw [Finset.mem_union, Finset.mem_singleton] at hu hv
      rcases hu with hu | rfl <;> rcases hv with hv | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.add_mem_add hu hv))
      · exact Finset.mem_union_left _ (hshift u hu)
      · rw [add_comm c₀ v]
        exact Finset.mem_union_left _ (hshift v hv)
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    calc _ ≤ ((C + C ∪ X) ∪ {c₀ + c₀}).card := Finset.card_le_card hsub
      _ ≤ (C + C ∪ X).card + 1 := by
          simpa using Finset.card_union_le (C + C ∪ X) {c₀ + c₀}
      _ ≤ (C + C).card + X.card + 1 := by
          gcongr
          exact Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left Finset.card_image_le _) _
  -- `A (2 * l)` has at least `2 * y` differences outside `C - C`.
  have hdiffE : (C - C).card + (A₁.filter fun b => n - b ∉ D).card +
      (A₁.filter fun b => n - b ∉ D).card ≤ (A (2 * (k + 1)) - A (2 * (k + 1))).card := by
    set Y := A₁.filter fun b => n - b ∉ D
    have hnot (u : ℤ) (hu : u ∈ C) (v : ℤ) (hv : v ∈ C) (b : ℤ) (hb : b ∈ Y) :
        u - v ≠ c₀ - b := by
      intro he
      obtain ⟨a, ha, j, hj, rfl⟩ := (hoddmem k u).1 hu
      obtain ⟨a', ha', j', hj', rfl⟩ := (hoddmem k v).1 hv
      obtain ⟨hbA, hbD⟩ := Finset.mem_filter.1 hb
      have hj1 : (j : ℤ) ≤ k := by exact_mod_cast hj
      have hj2 : (0 : ℤ) ≤ j' := by positivity
      rw [hc₀'] at he
      have key : ((k : ℤ) + 1 - j + j') * n = a - a' + b := by linear_combination -he
      have hq2 : (k : ℤ) + 1 - j + j' < 2 := by
        by_contra hcon
        have hcon := not_lt.1 hcon
        nlinarith [hn a ha, hn a' ha', hn b hbA]
      have hq : (k : ℤ) + 1 - j + j' = 1 := by omega
      rw [hq, one_mul] at key
      exact hbD (Finset.mem_sub.2 ⟨a, ha, a', ha', by linarith⟩)
    have hYp : (Y.image (c₀ - ·)).card = Y.card :=
      Finset.card_image_of_injective _ sub_right_injective
    have hYm : (Y.image (· - c₀)).card = Y.card :=
      Finset.card_image_of_injective _ sub_left_injective
    have hd1 : Disjoint (C - C) (Y.image (c₀ - ·)) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.1 hz
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 hz'
      exact hnot u hu v hv b hb hbe.symm
    have hd2 : Disjoint (C - C ∪ Y.image (c₀ - ·)) (Y.image (· - c₀)) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz'
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_sub.1 hz
        exact hnot v hv u hu b hb (by linarith)
      · -- `c₀ - b' = b - c₀` would give `2 * c₀ = b + b' < 2 * n ≤ 2 * c₀`.
        obtain ⟨b', hb', he⟩ := Finset.mem_image.1 hz
        have := hn b (Finset.mem_filter.1 hb).1
        have := hn b' (Finset.mem_filter.1 hb').1
        linarith
    have hsub : C - C ∪ Y.image (c₀ - ·) ∪ Y.image (· - c₀) ⊆
        A (2 * (k + 1)) - A (2 * (k + 1)) := by
      rw [hE]
      have hCE : C ⊆ C ∪ {c₀} := Finset.subset_union_left
      have hc₀E : c₀ ∈ C ∪ {c₀} := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hYC (b : ℤ) (hb : b ∈ Y) : b ∈ C ∪ {c₀} :=
        Finset.mem_union_left _
          ((hoddmem k b).2 ⟨b, (Finset.mem_filter.1 hb).1, 0, Nat.zero_le _, by simp⟩)
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · rcases Finset.mem_union.1 hz with hz | hz
        · exact Finset.sub_subset_sub hCE hCE hz
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
          exact Finset.sub_mem_sub hc₀E (hYC b hb)
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
        exact Finset.sub_mem_sub (hYC b hb) hc₀E
    calc (C - C).card + Y.card + Y.card =
          (C - C ∪ Y.image (c₀ - ·) ∪ Y.image (· - c₀)).card := by
          rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hYp, hYm]
      _ ≤ _ := Finset.card_le_card hsub
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (C + C).card = S.card + 2 * k * R := hsum k
    have h2 : (C - C).card = D.card + 2 * k * R := hdiff k
    omega
  · rw [hsum (k + 1), hdiff (k + 1)]
    omega
  · rw [hE]
    exact (Finset.ssubset_iff_of_subset Finset.subset_union_left).2
      ⟨c₀, Finset.mem_union_right _ (Finset.mem_singleton_self _), hc₀C⟩
  · rw [hE, hF]
    have hsub : C ∪ {c₀} ⊆ C ∪ (A₁ + {c₀}) := by
      refine Finset.union_subset_union (subset_refl C) ?_
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_add.2 ⟨0, h0, c₀, Finset.mem_singleton_self _, zero_add _⟩
    refine (Finset.ssubset_iff_of_subset hsub).2 ⟨a₀ + c₀, Finset.mem_union_right _
      (Finset.add_mem_add ha₀ (Finset.mem_singleton_self _)), ?_⟩
    rw [Finset.mem_union, Finset.mem_singleton]
    have ha₀n := hn a₀ ha₀
    rintro (h | h)
    · have := (hbound k _ h).2
      rw [← hc₀'] at this
      linarith
    · exact ha₀0 (by linarith)

end MetaMathlibExt

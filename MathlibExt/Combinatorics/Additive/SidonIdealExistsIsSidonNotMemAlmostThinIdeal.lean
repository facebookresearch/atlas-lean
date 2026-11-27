/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SidonIdeal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A Sidon set outside the almost thin ideal (Nowik)

We prove that there is a Sidon set `A ⊆ ℕ` that is not contained in any finite
union of almost thin sets.

The witness is the greedy Sidon sequence starting from `0` (the Mian-Chowla
construction): each new term is the least number above all previous terms that
keeps all pairwise sums distinct. Since a candidate is blocked only by the at
most `(n+1)^3` values of the form `x + y - z` with `x, y, z` among the first
`n + 1` terms, the `n`-th term is at most `(n+1)^4`, so the greedy set meets
every initial interval `[0, Z^4]` in at least `Z` points.

On the other hand, every almost thin set grows at least geometrically past some
point, so it meets `[0, X]` in at most `A + B * Nat.log 2 X` points for fixed
`A, B`. A finite union of almost thin sets satisfies the same kind of bound.
For `X = (2^m)^4` this bound is `A' + B' * (m * 4)`, which the greedy set's
`2^m` points eventually exceed. Hence the greedy set lies in no such union.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Proposition 1. The greedy bound is the argument of A. M. Mian and S. Chowla,
*On the B₂ sequences of Sidon*, Proc. Nat. Acad. Sci. India Sect. A 14 (1944).
-/

namespace MetaMathlibExt

@[expose] public section

/-- Values blocked for extending a Sidon set: `m` can join `T` only if it is not
of the form `x + y - z` with `x, y, z ∈ T`. -/
private def sidonGreedyForbidden (T : Finset ℕ) : Finset ℕ :=
  ((T ×ˢ T) ×ˢ T).image fun w => w.1.1 + w.1.2 - w.2

private theorem mem_sidonGreedyForbidden {T : Finset ℕ} {m : ℕ} :
    m ∈ sidonGreedyForbidden T ↔ ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T, x + y - z = m := by
  constructor
  · intro h
    rw [sidonGreedyForbidden, Finset.mem_image] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [Finset.mem_product, Finset.mem_product] at hw
    obtain ⟨⟨hx, hy⟩, hz⟩ := hw
    exact ⟨w.1.1, hx, w.1.2, hy, w.2, hz, rfl⟩
  · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
    rw [sidonGreedyForbidden, Finset.mem_image]
    refine ⟨((x, y), z), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_product]
    exact ⟨⟨hx, hy⟩, hz⟩

private theorem card_sidonGreedyForbidden_le (T : Finset ℕ) :
    (sidonGreedyForbidden T).card ≤ T.card ^ 3 := by
  calc (sidonGreedyForbidden T).card ≤ ((T ×ˢ T) ×ˢ T).card := Finset.card_image_le
    _ = (T.card * T.card) * T.card := by
        rw [Finset.card_product, Finset.card_product]
    _ = T.card ^ 3 := by ring

/-- There is always a candidate above a nonempty set that avoids the forbidden
values, and it can be chosen close by: among `F.card + 1` consecutive numbers,
one lies outside `F`. -/
private theorem exists_bounded_avoid (T : Finset ℕ) (hT : T.Nonempty) :
    ∃ w ≤ T.max' hT + (sidonGreedyForbidden T).card + 1,
      (∀ x ∈ T, x < w) ∧ w ∉ sidonGreedyForbidden T := by
  have hcard : (Finset.Icc (T.max' hT + 1) (T.max' hT + (sidonGreedyForbidden T).card + 1)).card
      = (sidonGreedyForbidden T).card + 1 := by
    rw [Nat.card_Icc]
    omega
  have hex : ∃ w ∈ Finset.Icc (T.max' hT + 1)
      (T.max' hT + (sidonGreedyForbidden T).card + 1),
      w ∉ sidonGreedyForbidden T := by
    by_contra hcon
    have hsub : Finset.Icc (T.max' hT + 1)
        (T.max' hT + (sidonGreedyForbidden T).card + 1) ⊆ sidonGreedyForbidden T := by
      intro w hw
      by_contra hmem
      exact hcon ⟨w, hw, hmem⟩
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨w, hwR, hwF⟩ := hex
  rw [Finset.mem_Icc] at hwR
  exact ⟨w, by omega, fun x hx => lt_of_le_of_lt (Finset.le_max' T x hx) (by omega),
    hwF⟩

private theorem sidonGreedyNext_exists (T : Finset ℕ) :
    ∃ w, (∀ x ∈ T, x < w) ∧ w ∉ sidonGreedyForbidden T := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · refine ⟨0, fun x hx => by simp at hx, ?_⟩
    simp [sidonGreedyForbidden]
  · obtain ⟨w, -, hw⟩ := exists_bounded_avoid T hT
    exact ⟨w, hw⟩

/-- The next greedy term: the least number above `T` avoiding the forbidden values. -/
private def sidonGreedyNext (T : Finset ℕ) : ℕ :=
  Nat.find (sidonGreedyNext_exists T)

private theorem lt_of_mem_sidonGreedyNext {T : Finset ℕ} {x : ℕ} (hx : x ∈ T) :
    x < sidonGreedyNext T :=
  (Nat.find_spec (sidonGreedyNext_exists T)).1 x hx

private theorem not_mem_forbidden_sidonGreedyNext (T : Finset ℕ) :
    sidonGreedyNext T ∉ sidonGreedyForbidden T :=
  (Nat.find_spec (sidonGreedyNext_exists T)).2

private theorem sidonGreedyNext_le (T : Finset ℕ) (hT : T.Nonempty) :
    sidonGreedyNext T ≤ T.max' hT + (sidonGreedyForbidden T).card + 1 := by
  obtain ⟨w, hwle, hw⟩ := exists_bounded_avoid T hT
  exact (Nat.find_min' (sidonGreedyNext_exists T) hw).trans hwle

/-- Extending a Sidon set by a fresh number outside the forbidden values keeps it
Sidon: a sum involving the new number exactly once would exhibit it as a blocked
value, and it is too large to appear twice in a repeated sum. -/
private theorem isSidon_insert_of_forbidden {T : Finset ℕ} {m : ℕ}
    (hSidon : (↑T : Set ℕ).IsSidon)
    (hmem : m ∉ sidonGreedyForbidden T)
    (hmax : ∀ x ∈ T, x < m) :
    (↑(insert m T) : Set ℕ).IsSidon := by
  intro p hp q hq r hr s hs hsum
  simp only [Finset.mem_coe, Finset.mem_insert] at hp hq hr hs
  rcases hp with rfl | hp <;> rcases hq with rfl | hq <;>
    rcases hr with rfl | hr <;> rcases hs with rfl | hs
  · exact Or.inl ⟨rfl, rfl⟩
  · have h1 := hmax s hs
    omega
  · have h1 := hmax r hr
    omega
  · have h1 := hmax r hr
    have h2 := hmax s hs
    omega
  · have h1 := hmax q hq
    omega
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨rfl, by omega⟩
  · exact absurd (mem_sidonGreedyForbidden.2 ⟨r, hr, s, hs, q, hq, by omega⟩) hmem
  · have h1 := hmax p hp
    omega
  · exact Or.inr ⟨by omega, rfl⟩
  · exact Or.inl ⟨by omega, rfl⟩
  · exact absurd (mem_sidonGreedyForbidden.2 ⟨r, hr, s, hs, p, hp, by omega⟩) hmem
  · have h1 := hmax p hp
    have h2 := hmax q hq
    omega
  · exact absurd (mem_sidonGreedyForbidden.2 ⟨p, hp, q, hq, s, hs, by omega⟩) hmem
  · exact absurd (mem_sidonGreedyForbidden.2 ⟨p, hp, q, hq, r, hr, by omega⟩) hmem
  · exact hSidon _ (Finset.mem_coe.2 hp) _ (Finset.mem_coe.2 hq)
      _ (Finset.mem_coe.2 hr) _ (Finset.mem_coe.2 hs) hsum

/-- The first `n + 1` greedy terms: start from `{0}` and adjoin the next term. -/
private def sidonGreedyPrefix : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 => insert (sidonGreedyNext (sidonGreedyPrefix n)) (sidonGreedyPrefix n)

/-- The greedy Sidon sequence. -/
private def sidonGreedySeq : ℕ → ℕ
  | 0 => 0
  | n + 1 => sidonGreedyNext (sidonGreedyPrefix n)

private theorem mem_prefix_self (n : ℕ) : sidonGreedySeq n ∈ sidonGreedyPrefix n := by
  cases n with
  | zero => decide
  | succ n => exact Finset.mem_insert_self _ _

private theorem prefix_nonempty (n : ℕ) : (sidonGreedyPrefix n).Nonempty :=
  ⟨sidonGreedySeq n, mem_prefix_self n⟩

private theorem prefix_eq_image (n : ℕ) :
    sidonGreedyPrefix n = (Finset.range (n + 1)).image sidonGreedySeq := by
  induction n with
  | zero => decide
  | succ n ih =>
    change insert (sidonGreedySeq (n + 1)) (sidonGreedyPrefix n) = _
    rw [ih, ← Finset.image_insert, ← Finset.range_add_one]

private theorem seq_strictMono : StrictMono sidonGreedySeq :=
  strictMono_nat_of_lt_succ fun n => lt_of_mem_sidonGreedyNext (mem_prefix_self n)

private theorem seq_injective : Function.Injective sidonGreedySeq :=
  seq_strictMono.injective

private theorem card_prefix (n : ℕ) : (sidonGreedyPrefix n).card = n + 1 := by
  rw [prefix_eq_image, Finset.card_image_of_injective _ seq_injective,
    Finset.card_range]

private theorem max'_prefix_le (n : ℕ) (hT : (sidonGreedyPrefix n).Nonempty) :
    (sidonGreedyPrefix n).max' hT ≤ sidonGreedySeq n := by
  apply Finset.max'_le
  intro y hy
  rw [prefix_eq_image, Finset.mem_image] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  rw [Finset.mem_range] at hk
  exact seq_strictMono.monotone (by omega)

/-- The Mian-Chowla bound: the `n`-th greedy term is at most `(n+1)^4`. -/
private theorem seq_le (n : ℕ) : sidonGreedySeq n ≤ (n + 1) ^ 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hnext := sidonGreedyNext_le (sidonGreedyPrefix n) (prefix_nonempty n)
    have hmax := max'_prefix_le n (prefix_nonempty n)
    have hcard := card_sidonGreedyForbidden_le (sidonGreedyPrefix n)
    rw [card_prefix] at hcard
    have hexpand : (n + 1 + 1) ^ 4
        = (n + 1) ^ 4 + 4 * (n + 1) ^ 3 + 6 * (n + 1) ^ 2 + 4 * (n + 1) + 1 := by
      ring
    have h2 : (0 : ℕ) ≤ (n + 1) ^ 2 := Nat.zero_le _
    have h3 : (0 : ℕ) ≤ (n + 1) ^ 3 := Nat.zero_le _
    have h1 : (0 : ℕ) ≤ n + 1 := Nat.zero_le _
    change sidonGreedyNext (sidonGreedyPrefix n) ≤ _
    omega

private theorem prefix_sidon (n : ℕ) : (↑(sidonGreedyPrefix n) : Set ℕ).IsSidon := by
  induction n with
  | zero =>
    change (↑({0} : Finset ℕ) : Set ℕ).IsSidon
    intro a ha b hb c hc d hd _
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb hc hd
    subst ha
    subst hb
    subst hc
    subst hd
    exact Or.inl ⟨rfl, rfl⟩
  | succ n ih =>
    change (↑(insert (sidonGreedyNext (sidonGreedyPrefix n)) (sidonGreedyPrefix n)) :
      Set ℕ).IsSidon
    exact isSidon_insert_of_forbidden ih
      (not_mem_forbidden_sidonGreedyNext (sidonGreedyPrefix n))
      (fun x hx => lt_of_mem_sidonGreedyNext hx)

/-- The greedy Sidon set. -/
private def sidonGreedySet : Set ℕ := Set.range sidonGreedySeq

private theorem isSidon_greedy : sidonGreedySet.IsSidon := by
  intro a ha b hb c hc d hd hsum
  simp only [sidonGreedySet, Set.mem_range] at ha hb hc hd
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨l, rfl⟩ := hd
  let N := max (max i j) (max k l)
  have hiN : i ≤ N := le_trans (le_max_left i j) (le_max_left _ _)
  have hjN : j ≤ N := le_trans (le_max_right i j) (le_max_left _ _)
  have hkN : k ≤ N := le_trans (le_max_left k l) (le_max_right _ _)
  have hlN : l ≤ N := le_trans (le_max_right k l) (le_max_right _ _)
  have hmem : ∀ t ≤ N, sidonGreedySeq t ∈ (↑(sidonGreedyPrefix N) : Set ℕ) := by
    intro t ht
    rw [prefix_eq_image]
    exact Finset.mem_coe.2
      (Finset.mem_image.2 ⟨t, Finset.mem_range.2 (by omega), rfl⟩)
  exact prefix_sidon N _ (hmem i hiN) _ (hmem j hjN) _ (hmem k hkN) _
    (hmem l hlN) hsum

/-- The greedy set meets `[0, Z^4]` in at least `Z` points. -/
private theorem ncard_inter_Icc_ge (Z : ℕ) :
    Z ≤ (sidonGreedySet ∩ Set.Icc 0 (Z ^ 4)).ncard := by
  have hEcard : ((Finset.range Z).image sidonGreedySeq).card = Z := by
    rw [Finset.card_image_of_injective _ seq_injective, Finset.card_range]
  have hsub : (((Finset.range Z).image sidonGreedySeq : Finset ℕ) : Set ℕ)
      ⊆ sidonGreedySet ∩ Set.Icc 0 (Z ^ 4) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_range] at hk
    refine ⟨Set.mem_range_self k, Set.mem_Icc.2 ⟨Nat.zero_le _, ?_⟩⟩
    calc sidonGreedySeq k ≤ (k + 1) ^ 4 := seq_le k
      _ ≤ Z ^ 4 := pow_le_pow_left₀ (Nat.zero_le _) (by omega) 4
  have hfin : (sidonGreedySet ∩ Set.Icc 0 (Z ^ 4)).Finite :=
    (Set.finite_Icc 0 (Z ^ 4)).subset Set.inter_subset_right
  calc Z = ((Finset.range Z).image sidonGreedySeq).card := hEcard.symm
    _ = ((((Finset.range Z).image sidonGreedySeq : Finset ℕ) : Set ℕ)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (sidonGreedySet ∩ Set.Icc 0 (Z ^ 4)).ncard :=
        Set.ncard_le_ncard hsub hfin

/-- An almost thin set meets `[0, X]` in `O(log X)` points: past some index its
enumeration grows at least geometrically. -/
private theorem exists_log_bound_inter_Icc {S : Set ℕ} (hS : IsAlmostThinSet S) :
    ∃ A B : ℕ, ∀ X : ℕ,
      (S ∩ Set.Icc 0 X).ncard ≤ A + B * Nat.log 2 X := by
  obtain ⟨hinf, α, hα, hratio⟩ := hS
  let a := Nat.nth (· ∈ S)
  have ha : StrictMono a := Nat.nth_strictMono hinf
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hratio
  let N₁ := max N₀ 1
  have hge : ∀ n, n ≤ a n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have h := ha (show n < n + 1 by omega); omega
  have age1 : ∀ n, N₁ ≤ n → 1 ≤ a n := by
    intro n hn
    have h1 : (1 : ℕ) ≤ N₁ := le_max_right _ _
    have h2 := hge n
    omega
  have hN₀' : (a N₁ : ℝ) / a (N₁ + 1) ≤ α := hN₀ N₁ (le_max_left _ _)
  have hαpos : 0 < α := by
    have hpos1 : (0 : ℝ) < a N₁ := by exact_mod_cast age1 N₁ le_rfl
    have hpos2 : (0 : ℝ) < a (N₁ + 1) := by
      exact_mod_cast age1 (N₁ + 1) (Nat.le_succ _)
    exact (div_pos hpos1 hpos2).trans_le hN₀'
  have hr : 1 < α⁻¹ := (one_lt_inv₀ hαpos).2 hα
  have step : ∀ n, N₁ ≤ n → (a n : ℝ) * α⁻¹ ≤ a (n + 1) := by
    intro n hn
    have hcast : (0 : ℝ) < a (n + 1) := by
      exact_mod_cast age1 (n + 1) (hn.trans (Nat.le_succ n))
    have hle : (a n : ℝ) / a (n + 1) ≤ α := hN₀ n ((le_max_left _ _).trans hn)
    have hm : (a n : ℝ) ≤ (a (n + 1) : ℝ) * α := by
      rw [mul_comm]
      exact (div_le_iff₀ hcast).1 hle
    have hαne : α ≠ 0 := ne_of_gt hαpos
    calc (a n : ℝ) * α⁻¹ ≤ (a (n + 1) : ℝ) * α * α⁻¹ :=
          mul_le_mul_of_nonneg_right hm (inv_nonneg.2 hαpos.le)
      _ = a (n + 1) := by rw [mul_assoc, mul_inv_cancel₀ hαne, mul_one]
  have grow : ∀ n, N₁ ≤ n → ∀ j, (a n : ℝ) * (α⁻¹) ^ j ≤ a (n + j) := by
    intro n hn j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right ih (zero_le_one.trans hr.le)).trans
        (step (n + j) (by omega))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 : ℝ) hr
  have hkpos : 0 < k := by
    by_contra hz
    have hkzero : k = 0 := by omega
    rw [hkzero, pow_zero] at hk
    norm_num at hk
  have dbl : ∀ n, N₁ ≤ n → (2 : ℝ) * a n ≤ a (n + k) := by
    intro n hn
    have h1 : (a n : ℝ) * (α⁻¹) ^ k ≤ a (n + k) := grow n hn k
    have h2 : (2 : ℝ) ≤ (α⁻¹) ^ k := hk.le
    have h3 : (0 : ℝ) ≤ a n := by positivity
    calc (2 : ℝ) * a n ≤ (α⁻¹) ^ k * a n := mul_le_mul_of_nonneg_right h2 h3
      _ = (a n : ℝ) * (α⁻¹) ^ k := mul_comm _ _
      _ ≤ a (n + k) := h1
  have gepow : ∀ j, 2 ^ j ≤ a (N₁ + j * k) := by
    intro j
    induction j with
    | zero =>
      simp only [zero_mul, add_zero, pow_zero]
      exact age1 N₁ le_rfl
    | succ j ih =>
      have heq : N₁ + (j + 1) * k = (N₁ + j * k) + k := by ring
      rw [heq]
      have ihR : (2 : ℝ) ^ j ≤ a (N₁ + j * k) := by exact_mod_cast ih
      have h2 : (2 : ℝ) ^ (j + 1) ≤ a ((N₁ + j * k) + k) := by
        have h := dbl (N₁ + j * k) (by omega)
        calc (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
          _ ≤ 2 * (a (N₁ + j * k) : ℝ) :=
            mul_le_mul_of_nonneg_left ihR (by norm_num)
          _ ≤ a ((N₁ + j * k) + k) := h
      exact_mod_cast h2
  refine ⟨N₁ + k + 1, k, fun X => ?_⟩
  have hkey : ∀ n, a n ≤ X → n ≤ N₁ + k + k * Nat.log 2 X := by
    intro n hn
    by_cases hnN : n < N₁
    · omega
    · have hnN' : N₁ ≤ n := by omega
      have hdiv := Nat.div_add_mod (n - N₁) k
      have hmod : (n - N₁) % k < k := Nat.mod_lt _ hkpos
      have hcomm : (n - N₁) / k * k = k * ((n - N₁) / k) := mul_comm _ _
      have hne : n = N₁ + (n - N₁) / k * k + (n - N₁) % k := by omega
      have hmono : a (N₁ + (n - N₁) / k * k) ≤ a n :=
        ha.monotone (by omega)
      have h2X : 2 ^ ((n - N₁) / k) ≤ X :=
        (gepow ((n - N₁) / k)).trans (hmono.trans hn)
      have hqlog : (n - N₁) / k ≤ Nat.log 2 X := by
        have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) X
        have h2lt : (2 : ℕ) ^ ((n - N₁) / k) < 2 ^ ((Nat.log 2 X).succ) :=
          lt_of_le_of_lt h2X hlt
        have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2lt
        omega
      have hqk : (n - N₁) / k * k ≤ Nat.log 2 X * k :=
        Nat.mul_le_mul_right k hqlog
      have hcomm2 : Nat.log 2 X * k = k * Nat.log 2 X := mul_comm _ _
      omega
  have hfin : (S ∩ Set.Icc 0 X).Finite :=
    (Set.finite_Icc 0 X).subset Set.inter_subset_right
  have hrange : Set.range a = S := Nat.range_nth_of_infinite hinf
  have hsub : S ∩ Set.Icc 0 X
      ⊆ (((Finset.range (N₁ + k + k * Nat.log 2 X + 1)).image a : Finset ℕ) :
        Set ℕ) := by
    intro x hx
    obtain ⟨hxS, hxX⟩ := hx
    rw [← hrange, Set.mem_range] at hxS
    obtain ⟨n, rfl⟩ := hxS
    rw [Set.mem_Icc] at hxX
    have hn := hkey n hxX.2
    exact Finset.mem_coe.2
      (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
  have hle : (S ∩ Set.Icc 0 X).ncard ≤ N₁ + k + k * Nat.log 2 X + 1 := by
    have h1 : (S ∩ Set.Icc 0 X).ncard
        ≤ (((Finset.range (N₁ + k + k * Nat.log 2 X + 1)).image a : Finset ℕ)).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have h2 : (((Finset.range (N₁ + k + k * Nat.log 2 X + 1)).image a : Finset ℕ)).card
        ≤ N₁ + k + k * Nat.log 2 X + 1 := by
      calc (((Finset.range (N₁ + k + k * Nat.log 2 X + 1)).image a :
          Finset ℕ)).card
          ≤ (Finset.range (N₁ + k + k * Nat.log 2 X + 1)).card :=
            Finset.card_image_le
        _ = N₁ + k + k * Nat.log 2 X + 1 := Finset.card_range _
    exact h1.trans h2
  omega

/-- Squares are eventually below powers of two. -/
private theorem sq_lt_two_pow (m : ℕ) (hm : 5 ≤ m) : m * m < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hexpand : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by ring
    have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    have h5n : 5 * n ≤ n * n := Nat.mul_le_mul_right n hn
    omega

/-- Exponentials beat linear functions. -/
private theorem exists_pow_gt_linear (C D : ℕ) : ∃ m, C + D * m < 2 ^ m := by
  refine ⟨max 5 (C + D + 1) + 1, ?_⟩
  set m := max 5 (C + D + 1) with hmdef
  have hm5 : 5 ≤ m + 1 := by omega
  have hC : C ≤ m := by omega
  have hD : D ≤ m := by omega
  have hsq := sq_lt_two_pow (m + 1) hm5
  have hDm : D * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ hD
  have hexpand : (m + 1) * (m + 1) = m * (m + 1) + (m + 1) := by ring
  omega

private theorem not_mem_generatedIdeal :
    sidonGreedySet ∉ generatedIdeal IsAlmostThinSet := by
  rintro ⟨n, S, hS, hsub⟩
  have hmem : ∀ j, ∃ A B : ℕ, ∀ X : ℕ,
      (S j ∩ Set.Icc 0 X).ncard ≤ A + B * Nat.log 2 X :=
    fun j => exists_log_bound_inter_Icc (hS j)
  choose A B hB using hmem
  obtain ⟨m, hm⟩ := exists_pow_gt_linear (∑ j, A j) ((∑ j, B j) * 4)
  set X := (2 ^ m) ^ 4 with hXdef
  have hlog : Nat.log 2 X = m * 4 := by
    rw [hXdef, ← pow_mul]
    exact Nat.log_eq_of_pow_le_of_lt_pow le_rfl
      (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hun : (⋃ j, S j) ∩ Set.Icc 0 X = ⋃ j, (S j ∩ Set.Icc 0 X) := Set.iUnion_inter _ _
  have hfinT : ((⋃ j, S j) ∩ Set.Icc 0 X).Finite :=
    (Set.finite_Icc 0 X).subset Set.inter_subset_right
  have hcard : ((⋃ j, S j) ∩ Set.Icc 0 X).ncard
      ≤ ∑ j, (A j + B j * Nat.log 2 X) := by
    have hfin : ∀ j, (S j ∩ Set.Icc 0 X).Finite :=
      fun j => (Set.finite_Icc 0 X).subset Set.inter_subset_right
    have h1 : (⋃ j, (S j ∩ Set.Icc 0 X))
        = ((Finset.univ.biUnion (fun j => (hfin j).toFinset) : Finset ℕ) :
          Set ℕ) := by
      apply Set.ext
      intro x
      simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    have h2 : (⋃ j, (S j ∩ Set.Icc 0 X)).ncard
        ≤ ∑ j, ((S j ∩ Set.Icc 0 X).ncard) := by
      rw [h1, Set.ncard_coe_finset]
      calc (Finset.univ.biUnion (fun j => (hfin j).toFinset)).card
          ≤ ∑ j ∈ Finset.univ, ((hfin j).toFinset).card := Finset.card_biUnion_le
        _ = ∑ j, ((S j ∩ Set.Icc 0 X).ncard) :=
          Finset.sum_congr rfl
            (fun j _ => (Set.ncard_eq_toFinset_card _ (hfin j)).symm)
    have h3 : ∑ j, ((S j ∩ Set.Icc 0 X).ncard)
        ≤ ∑ j, (A j + B j * Nat.log 2 X) :=
      Finset.sum_le_sum (fun j _ => hB j X)
    rw [hun]
    exact h2.trans h3
  have hgreedy : 2 ^ m ≤ (sidonGreedySet ∩ Set.Icc 0 X).ncard := by
    have h := ncard_inter_Icc_ge (2 ^ m)
    rw [← hXdef] at h
    exact h
  have hsub2 : sidonGreedySet ∩ Set.Icc 0 X
      ⊆ (⋃ j, S j) ∩ Set.Icc 0 X := by
    intro x hx
    obtain ⟨hxA, hxX⟩ := hx
    exact ⟨hsub hxA, hxX⟩
  have hmono : (sidonGreedySet ∩ Set.Icc 0 X).ncard
      ≤ ((⋃ j, S j) ∩ Set.Icc 0 X).ncard :=
    Set.ncard_le_ncard hsub2 hfinT
  have hsum : ∑ j, (A j + B j * Nat.log 2 X)
      = (∑ j, A j) + (∑ j, B j) * Nat.log 2 X := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsum, hlog] at hcard
  have heq : (∑ j, B j) * (m * 4) = (∑ j, B j) * 4 * m := by ring
  omega

/-- **A Sidon set outside the almost thin ideal.** There is a Sidon set $A \subseteq \mathbb{N}$
that is not contained in any finite union of almost thin sets; that is, $A$ does not belong to the
ideal generated by the almost thin sets.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Proposition 1 (`integers-2025-A91-prop-1`). -/
public theorem exists_isSidon_not_mem_almostThinIdeal :
    ∃ A : Set ℕ, A.IsSidon ∧ A ∉ generatedIdeal IsAlmostThinSet :=
  ⟨sidonGreedySet, isSidon_greedy, not_mem_generatedIdeal⟩

end

end MetaMathlibExt

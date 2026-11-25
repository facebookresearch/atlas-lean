/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SetFamily.UnionFreeVanishingDensity
import all MathlibExt.Combinatorics.SetFamily.UnionFreeVanishingDensity
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import MathlibExt.Probability.BooleanCubeMoments

/-!
# Kleitman's bound for union-free families

The largest union-free family of subsets of an `n`-element set has at most
`(1 + o(1))` times the size of the middle layer. We count the first and subsequent
hits of a permutation chain in a window around the middle. Disjoint block swaps
bound the proportion of chains with an earlier hit given a hit at a fixed level.
A fourth-moment estimate on the Boolean cube controls the sets outside the window.

## Record carried over from the retired `WantedExt/Combinatorics/UnionFreeFamiliesErdosProblem447Wanted.lean`

Source: T. F. Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED
(LEAN)). UnsolvedMath record UM-30006877 (`EP-447`), dataset ulamai/UnsolvedMath v1.8.0.

`[n]` is `Fin n` and the maximum is an `sSup` over a bounded set. The two yes/no questions are
separate targets, and the opening "how large" is not stated beyond them; `(1 + o(1)) C(n, ⌊n/2⌋)` is
stated as: for every `ε > 0`, eventually `|F| ≤ (1 + ε) C(n, ⌊n/2⌋)`. Compared with the
formal-conjectures statement `ErdosProblems/447.lean` (equivalent; no code imported).
-/

namespace MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

/-- **Erdős Problem 447, second question.** The assertion that, for every real $\varepsilon > 0$
and all sufficiently large $n$, the maximum size of a union-free family of subsets of
$\{0, \dots, n-1\}$ is at most $(1 + \varepsilon)\binom{n}{\lfloor n/2 \rfloor}$; that is, it is
at most $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$. -/
@[expose] public def maxUnionFreeSizeCentralBinomial : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (maxUnionFreeSize n : ℝ) ≤ (1 + ε) * n.choose (n / 2)

open Finset

variable {n : ℕ}

private def earlier (F : Finset (Finset (Fin n))) (a l : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ j, a ≤ j ∧ j < l ∧ chain σ j ∈ F

private noncomputable def repeatHit (F : Finset (Finset (Fin n))) (a l : ℕ)
    (σ : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact if chain σ l ∈ F ∧ earlier F a l σ then 1 else 0

private lemma chain_mono (σ : Equiv.Perm (Fin n)) {i j : ℕ} (h : i ≤ j) :
    chain σ i ⊆ chain σ j := fun _ hx => mem_chain.mpr (lt_of_lt_of_le (mem_chain.mp hx) h)

/-- Across the block swaps fixing level `l`, at most one chain has an earlier hit.
Indeed, the two earlier sets would together cover the level-`l` set. -/
private lemma repeat_bound {F : Finset (Finset (Fin n))} (hF : IsUnionFree F) {a l q : ℕ}
    (hal : a ≤ l) (hl : l ≤ n) (hq : q * (l - a) ≤ a) :
    q * ∑ σ, repeatHit F a l σ ≤ ∑ σ, ind F l σ := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, l = a + t := ⟨l - a, by omega⟩
  rw [Nat.add_sub_cancel_left] at hq
  have hblock (i : ℕ) (hi : i < q) : i * t + t ≤ a := by
    simpa [Nat.add_mul] using (Nat.mul_le_mul_right t hi).trans hq
  let ρ (i : ℕ) : Equiv.Perm (Fin n) :=
    if h : i * t + t ≤ a then blockSwap n (i * t) t a h hl else 1
  have top (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < q) :
      chain (σ * ρ i) (a + t) = chain σ (a + t) := by
    simpa only [ρ, dite_eq_left (hblock i hi)] using
      (chain_mul_blockSwap_add (σ := σ) (hblock i hi) hl)
  have bottom (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < q) {x : Fin n} :
      x ∈ chain (σ * ρ i) a ↔ (σ.symm x : ℕ) < a + t ∧
        ¬ (i * t ≤ (σ.symm x : ℕ) ∧ (σ.symm x : ℕ) < i * t + t) := by
    simpa only [ρ, dite_eq_left (hblock i hi)] using
      (mem_chain_mul_blockSwap (σ := σ) (x := x) (hblock i hi) hl)
  have one (σ : Equiv.Perm (Fin n)) (hσ : chain σ (a + t) ∈ F) :
      ((range q).filter fun i => earlier F a (a + t) (σ * ρ i)).card ≤ 1 := by
    rw [card_le_one]
    intro i hi j hj
    obtain ⟨hi, k, hak, hk, hAk⟩ := mem_filter.mp hi
    obtain ⟨hj, m, ham, hm, hAm⟩ := mem_filter.mp hj
    replace hi := mem_range.mp hi
    replace hj := mem_range.mp hj
    by_contra hij
    have hdisj : i * t + t ≤ j * t ∨ j * t + t ≤ i * t := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl (by simpa [Nat.add_mul] using Nat.mul_le_mul_right t h)
      · exact Or.inr (by simpa [Nat.add_mul] using Nat.mul_le_mul_right t h)
    have hcover : chain (σ * ρ i) k ∪ chain (σ * ρ j) m = chain σ (a + t) := by
      apply Subset.antisymm
      · apply union_subset
        · exact top σ hi ▸ chain_mono (σ * ρ i) hk.le
        · exact top σ hj ▸ chain_mono (σ * ρ j) hm.le
      · intro x hx
        have hx' := mem_chain.mp hx
        apply mem_union.mpr
        by_cases h : x ∈ chain (σ * ρ i) a
        · exact Or.inl (chain_mono _ hak h)
        · apply Or.inr
          apply chain_mono _ ham
          rw [bottom σ hi] at h
          rw [bottom σ hj]
          omega
    have ne_top {τ : Equiv.Perm (Fin n)} {r : ℕ} (hr : r < a + t) :
        chain τ r ≠ chain σ (a + t) := by
      intro he
      have := congrArg Finset.card he
      rw [card_chain _ (hr.le.trans hl), card_chain _ hl] at this
      omega
    apply hF _ hAk _ hAm _ hσ _ (ne_top hk) (ne_top hm) hcover
    intro he
    rw [he, union_idempotent] at hcover
    exact ne_top hm hcover
  have pointwise (σ : Equiv.Perm (Fin n)) :
      ∑ i ∈ range q, repeatHit F a (a + t) (σ * ρ i) ≤ ind F (a + t) σ := by
    simp only [repeatHit, ind]
    by_cases hσ : chain σ (a + t) ∈ F
    · rw [ite_eq_left hσ, sum_boole, Nat.cast_id]
      exact (card_le_card (monotone_filter_right _ (fun _ _ h => h.2))).trans (one σ hσ)
    · rw [ite_eq_right hσ]
      refine le_of_eq (sum_eq_zero ?_)
      intro i hi
      rw [top σ (mem_range.mp hi), ite_eq_right (fun h => hσ h.1)]
  calc q * ∑ σ, repeatHit F a (a + t) σ
      = ∑ i ∈ range q, ∑ σ, repeatHit F a (a + t) (σ * ρ i) := by
          symm
          calc _ = ∑ _i ∈ range q, ∑ σ, repeatHit F a (a + t) σ :=
                  sum_congr rfl fun i _ =>
                    Fintype.sum_equiv (Equiv.mulRight (ρ i)) _ _ (fun _ => rfl)
            _ = _ := by rw [sum_const, card_range, smul_eq_mul]
    _ = ∑ σ, ∑ i ∈ range q, repeatHit F a (a + t) (σ * ρ i) := sum_comm
    _ ≤ _ := sum_le_sum fun σ _ => pointwise σ

/-- At most one hit on a chain can be its first hit in the window. -/
private lemma hits_le_one_add_repeats (F : Finset (Finset (Fin n))) (a b : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    ∑ l ∈ Icc a b, ind F l σ ≤ 1 + ∑ l ∈ Icc a b, repeatHit F a l σ := by
  classical
  let first (l : ℕ) := chain σ l ∈ F ∧ ¬ earlier F a l σ
  have hfirst : ((Icc a b).filter first).card ≤ 1 := by
    rw [card_le_one]
    intro k hk l hl
    obtain ⟨hk, hFk, hnk⟩ := mem_filter.mp hk
    obtain ⟨hl, hFl, hnl⟩ := mem_filter.mp hl
    rcases lt_trichotomy k l with h | h | h
    · exact (hnl ⟨k, (mem_Icc.mp hk).1, h, hFk⟩).elim
    · exact h
    · exact (hnk ⟨l, (mem_Icc.mp hl).1, h, hFl⟩).elim
  have split (l : ℕ) : ind F l σ = (if first l then 1 else 0) + repeatHit F a l σ := by
    by_cases h : chain σ l ∈ F <;> by_cases e : earlier F a l σ <;>
      simp [ind, repeatHit, first, h, e]
  simpa only [split, sum_add_distrib, sum_boole, Nat.cast_id, Nat.add_le_add_iff_right] using hfirst

private lemma window_weight (F : Finset (Finset (Fin n))) {a b : ℕ} (hb : b ≤ n) :
    n.factorial * (F.filter fun A => A.card ∈ Icc a b).card ≤
      n.choose (n / 2) * ∑ k ∈ Icc a b, ∑ σ, ind F k σ := by
  rw [← sum_card_fiberwise_eq_card_filter, mul_sum, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have hkn := (mem_Icc.mp hk).2.trans hb
  rw [sum_ind F hkn, ← Nat.choose_mul_factorial_mul_factorial hkn]
  calc _ = n.choose k * ((F.filter fun A => A.card = k).card *
            (k.factorial * (n - k).factorial)) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.choose_le_middle k n)

/-- The expected number of hits is at most `(q+1)/q` when the bottom level
accommodates `q+1` disjoint blocks of the window width. -/
private lemma sharp_window_bound {F : Finset (Finset (Fin n))} (hF : IsUnionFree F)
    {a b q : ℕ} (hb : b ≤ n) (hq : (q + 1) * (b - a) ≤ a) :
    q * (F.filter fun A => A.card ∈ Icc a b).card ≤ (q + 1) * n.choose (n / 2) := by
  classical
  let S := ∑ l ∈ Icc a b, ∑ σ, ind F l σ
  let R := ∑ l ∈ Icc a b, ∑ σ, repeatHit F a l σ
  have hR : (q + 1) * R ≤ S := by
    dsimp [R, S]
    rw [mul_sum]
    refine sum_le_sum fun l hl => ?_
    obtain ⟨hal, hlb⟩ := mem_Icc.mp hl
    exact repeat_bound hF hal (hlb.trans hb)
      ((Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hlb a)).trans hq)
  have hS : S ≤ n.factorial + R := by
    have h := sum_le_sum (s := (univ : Finset (Equiv.Perm (Fin n))))
      (fun σ _ => hits_le_one_add_repeats F a b σ)
    simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, card_univ,
      Fintype.card_perm, Fintype.card_fin, sum_comm (s := univ)] using h
  have hweight := window_weight F (a := a) hb
  change _ ≤ _ * S at hweight
  have hcount : q * S ≤ (q + 1) * n.factorial := by
    have := Nat.mul_le_mul_left (q + 1) hS
    rw [mul_add] at this
    nlinarith only [this, hR]
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos n)
  calc _ = q * (n.factorial * (F.filter fun A => A.card ∈ Icc a b).card) := by ring
    _ ≤ q * (n.choose (n / 2) * S) := Nat.mul_le_mul_left _ hweight
    _ = n.choose (n / 2) * (q * S) := by ring
    _ ≤ n.choose (n / 2) * ((q + 1) * n.factorial) := Nat.mul_le_mul_left _ hcount
    _ = _ := by ring

/-- The fourth moment on the Boolean cube bounds the number of sets far from the middle. -/
private lemma fourth_moment_tail (T : Finset (Finset (Fin n))) (d : ℕ)
    (hT : ∀ A ∈ T, d + 2 * A.card ≤ n ∨ n + d ≤ 2 * A.card) :
    T.card * d ^ 4 ≤ 2 ^ n * (3 * n ^ 2) := by
  classical
  let bits (A : Finset (Fin n)) (i : Fin n) := decide (i ∉ A)
  have inj : Function.Injective bits := by
    intro A B h
    ext i
    simpa [bits] using congrFun h i
  let weight (σ : Fin n → Bool) := (∑ i, BooleanCube.cubeVal (σ i)) ^ 4
  have hsum (A : Finset (Fin n)) :
      ∑ i, BooleanCube.cubeVal (bits A i) = (n : ℝ) - 2 * A.card := by
    have term (i : Fin n) : BooleanCube.cubeVal (bits A i) =
        1 - 2 * (if i ∈ A then (1 : ℝ) else 0) := by
      by_cases h : i ∈ A <;> norm_num [bits, BooleanCube.cubeVal, h]
    simp [term, sum_sub_distrib, mul_comm]
  have h : (T.card : ℝ) * (d : ℝ) ^ 4 ≤ (2 : ℝ) ^ n * (3 * (n : ℝ) ^ 2) := by
    calc _ = ∑ _A ∈ T, (d : ℝ) ^ 4 := by simp
      _ ≤ ∑ A ∈ T, weight (bits A) := by
        refine sum_le_sum fun A hA => ?_
        dsimp only [weight]
        rw [hsum, ← (show Even 4 by decide).pow_abs ((n : ℝ) - 2 * A.card)]
        apply pow_le_pow_left₀ (by positivity)
        apply le_abs.mpr
        rcases hT A hA with h | h
        · left
          exact le_sub_iff_add_le.mpr (by exact_mod_cast h)
        · right
          have h' : (n : ℝ) + d ≤ 2 * A.card := by exact_mod_cast h
          linarith
      _ = ∑ σ ∈ T.image bits, weight σ := (sum_image inj.injOn).symm
      _ ≤ ∑ σ, weight σ := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
        intro σ _ _
        dsimp [weight]
        positivity
      _ ≤ _ := MetaMathlibExt.sum_cubeVal_fourth_le n
  exact_mod_cast h

/-- For a window of fixed relative width, the tails cost at most a `1/q` fraction
of the middle layer once `n` is sufficiently large. -/
private lemma tail_le_middle {q c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hn : 0 < n)
    (hlarge : 6 * q * c ^ 4 ≤ n) (hwidth : n ≤ c * d) (T : Finset (Finset (Fin n)))
    (hT : ∀ A ∈ T, d + 2 * A.card ≤ n ∨ n + d ≤ 2 * A.card) :
    q * T.card ≤ n.choose (n / 2) := by
  have hmid : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := by
    calc 2 ^ n = ∑ k ∈ range (n + 1), n.choose k := (Nat.sum_range_choose n).symm
      _ ≤ ∑ _k ∈ range (n + 1), n.choose (n / 2) :=
        sum_le_sum fun k _ => Nat.choose_le_middle k n
      _ = _ := by simp
  have hcoef : q * (3 * n ^ 2) * (n + 1) ≤ d ^ 4 := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos hc (n := 4))
    calc c ^ 4 * (q * (3 * n ^ 2) * (n + 1))
        ≤ c ^ 4 * (q * (3 * n ^ 2) * (2 * n)) := by gcongr; omega
      _ = (6 * q * c ^ 4) * n ^ 3 := by ring
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hlarge
      _ = n ^ 4 := by ring
      _ ≤ (c * d) ^ 4 := Nat.pow_le_pow_left hwidth _
      _ = c ^ 4 * d ^ 4 := mul_pow _ _ _
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos hd (n := 4))
  calc d ^ 4 * (q * T.card) = q * (T.card * d ^ 4) := by ring
    _ ≤ q * (2 ^ n * (3 * n ^ 2)) := Nat.mul_le_mul_left _ (fourth_moment_tail T d hT)
    _ ≤ q * (((n + 1) * n.choose (n / 2)) * (3 * n ^ 2)) := by gcongr
    _ = (q * (3 * n ^ 2) * (n + 1)) * n.choose (n / 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcoef

private lemma card_le_middle_of_large {q : ℕ} (hq : 0 < q)
    (hn : 6 * q * (8 * (q + 1)) ^ 4 ≤ n) {F : Finset (Finset (Fin n))}
    (hF : IsUnionFree F) : q * F.card ≤ (q + 2) * n.choose (n / 2) := by
  let c := 8 * (q + 1)
  let w := n / c
  let a := n / 2 - w
  let b := n / 2 + w
  have hc : 0 < c := by dsimp [c]; positivity
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hbudget : 8 * ((q + 1) * w) ≤ n := by
    rw [← mul_assoc]
    exact Nat.mul_div_le n c
  have hw : w ≤ (q + 1) * w := Nat.le_mul_of_pos_left _ (by omega)
  have hab : b - a = 2 * w := by dsimp [a, b]; omega
  have hwidth : (q + 1) * (b - a) ≤ a := by
    rw [hab, mul_left_comm]
    dsimp only [a]
    omega
  have hcenter := sharp_window_bound hF (b := b) (by dsimp [b]; omega) hwidth
  let T := F.filter fun A => A.card ∉ Icc a b
  have htail : q * T.card ≤ n.choose (n / 2) := by
    refine tail_le_middle hc (d := w + 1) (by omega) hnpos hn
      (Nat.lt_mul_div_succ n hc).le T ?_
    intro A hA
    have := (mem_filter.mp hA).2
    simp only [mem_Icc, a, b] at this
    omega
  have hsplit := card_filter_add_card_filter_not (s := F) (fun A => A.card ∈ Icc a b)
  change _ + T.card = F.card at hsplit
  rw [← hsplit, mul_add]
  calc _ ≤ (q + 1) * n.choose (n / 2) + n.choose (n / 2) := Nat.add_le_add hcenter htail
    _ = _ := by ring

/--
**Kleitman's bound for union-free families (Erdős Problem 447).** For every real
$\varepsilon > 0$ and all sufficiently large $n$, the maximum size of a union-free family of
subsets of $\{0, \dots, n-1\}$ is at most $(1 + \varepsilon)\binom{n}{\lfloor n/2 \rfloor}$; that
is, it is at most $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$.

Source: T. F. Bloom, Erdős Problems, Problem #447,
https://www.erdosproblems.com/447 (status PROVED (LEAN)); resolution: D. Kleitman, Collections of
subsets containing no two sets and their union, Proceedings of the LA Meeting AMS (1971), 153-155,
|F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
public theorem maxUnionFreeSizeCentralBinomial_holds : maxUnionFreeSizeCentralBinomial := by
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / ε)
  have hqreal : (0 : ℝ) < q := (by positivity : 0 < 2 / ε).trans hq
  have hqnat : 0 < q := by exact_mod_cast hqreal
  have hεq := (div_lt_iff₀ hε).mp hq
  filter_upwards [Filter.eventually_ge_atTop (6 * q * (8 * (q + 1)) ^ 4)] with n hn
  classical
  have hne : {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k}.Nonempty :=
    ⟨0, ∅, fun A hA => absurd hA (notMem_empty A), card_empty⟩
  have hbdd : BddAbove {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k} := by
    refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro k ⟨F, -, rfl⟩
    exact card_le_univ F
  obtain ⟨F, hF, heq⟩ := Nat.sSup_mem hne hbdd
  change F.card = maxUnionFreeSize n at heq
  rw [← heq]
  have h : (q : ℝ) * F.card ≤ (q + 2) * n.choose (n / 2) := by
    exact_mod_cast card_le_middle_of_large hqnat hn hF
  apply le_of_mul_le_mul_left _ hqreal
  calc _ ≤ ((q : ℝ) + 2) * n.choose (n / 2) := h
    _ ≤ (q + q * ε) * n.choose (n / 2) := by gcongr
    _ = _ := by ring

end MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

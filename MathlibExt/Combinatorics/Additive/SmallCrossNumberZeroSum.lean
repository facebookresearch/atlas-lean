/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.SymmDiff
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Good sequences in cyclic groups of order `35 ^ k`

We bound the threshold for a random sequence to contain a nonempty zero-sum subsequence
of cross number at most one by counting collisions between subset sums.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Good sequences in a finite abelian group.** Let $\Gamma$ be a finite abelian group, written
additively, and let $g = (g_1, \dots, g_t)$ be a sequence of $t$ elements of $\Gamma$. The
sequence $g$ is *good* if there is a nonempty set $S \subseteq \{1, \dots, t\}$ of indices with
$\sum_{i \in S} g_i = 0$ whose cross number $\sum_{i \in S} 1/|g_i|$ is at most $1$, where
$|g_i|$ is the order of $g_i$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1 (definition of good sequences). -/
def IsGoodSequence {Γ : Type*} [AddCommGroup Γ] [Finite Γ] {t : ℕ} (g : Fin t → Γ) : Prop :=
  ∃ s : Finset (Fin t), s.Nonempty ∧ ∑ i ∈ s, g i = 0 ∧
    ∑ i ∈ s, (1 : ℚ) / addOrderOf (g i) ≤ 1

/-- **Probability that a random sequence is good.** Let $\Gamma$ be a finite abelian group and
$t \ge 0$ an integer. A sequence $g_1, \dots, g_t$ in $\Gamma$ is good if some nonempty set
$S \subseteq \{1, \dots, t\}$ of indices has $\sum_{i \in S} g_i = 0$ and
$\sum_{i \in S} 1/\operatorname{ord}(g_i) \le 1$, where $\operatorname{ord}(g_i)$ is the order
of $g_i$. The good-sequence probability of $\Gamma$ at length $t$ is the number of good sequences
of length $t$ in $\Gamma$ divided by $|\Gamma|^t$, that is, the probability that a uniformly
random sequence of length $t$ in $\Gamma$ is good.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (the event `E_Γ(t)`). -/
noncomputable def goodSequenceProb (Γ : Type*) [AddCommGroup Γ] [Finite Γ] (t : ℕ) : ℝ :=
  ({g : Fin t → Γ | IsGoodSequence g}.ncard : ℝ) / (Nat.card Γ : ℝ) ^ t

/-- **Threshold functions.** Let $P : \mathbb{N} \times \mathbb{N} \to \mathbb{R}$, where
$P(k, s)$ is read as the probability of an event in the $k$-th space when $s$ random elements
are chosen. A function $t : \mathbb{N} \to \mathbb{R}$ is a *threshold function* for $P$ if
$t(k) > 0$ for all sufficiently large $k$ and, for every function $f : \mathbb{N} \to \mathbb{N}$,
$P(k, f(k)) \to 1$ as $k \to \infty$ whenever $t = o(f)$, and $P(k, f(k)) \to 0$ as
$k \to \infty$ whenever $f = o(t)$.

The source's thresholds are positive functions; since little-o ignores sign, without the
positivity condition $-t$ would be a threshold function whenever $t$ is.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of a threshold and of
`τ(G)`). -/
def IsThresholdFunction (P : ℕ → ℕ → ℝ) (t : ℕ → ℝ) : Prop :=
  (∀ᶠ k in Filter.atTop, 0 < t k) ∧ ∀ f : ℕ → ℕ,
    (t =o[Filter.atTop] (fun k => (f k : ℝ)) →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 1)) ∧
      ((fun k => (f k : ℝ)) =o[Filter.atTop] t →
        Filter.Tendsto (fun k => P k (f k)) Filter.atTop (nhds 0))

open Finset Filter
open scoped symmDiff

variable {G : Type*} [AddCommGroup G] {s : ℕ}

/-- Negate the coordinates in a chosen set of indices. -/
private def signChange (a : Finset (Fin s)) (g : Fin s → G) (i : Fin s) : G :=
  if i ∈ a then -g i else g i

/-- A collision of subset sums yields a zero sum after changing signs on the first subset. -/
private lemma good_of_collision [Finite G] {g : Fin s → G} (hs : 0 < s)
    (hg : ∀ i, s ≤ addOrderOf (g i)) {a b : Finset (Fin s)} (hab : a ≠ b)
    (heq : ∑ i ∈ a, g i = ∑ i ∈ b, g i) : IsGoodSequence (signChange a g) := by
  refine ⟨b ∆ a, symmDiff_nonempty.mpr hab.symm, ?_, ?_⟩
  · rw [Finset.symmDiff_def, sum_union disjoint_sdiff_sdiff]
    have hb : ∑ i ∈ b \ a, signChange a g i = ∑ i ∈ b \ a, g i :=
      sum_congr rfl fun i hi => ite_eq_right (mem_sdiff.mp hi).2
    have ha : ∑ i ∈ a \ b, signChange a g i = ∑ i ∈ a \ b, -g i :=
      sum_congr rfl fun i hi => ite_eq_left (mem_sdiff.mp hi).1
    rw [hb, ha, sum_neg_distrib, ← sub_eq_add_neg, sum_sdiff_sub_sum_sdiff, heq, sub_self]
  · have hpos : (0 : ℚ) < s := by exact_mod_cast hs
    calc
      _ ≤ ∑ _i ∈ b ∆ a, (1 : ℚ) / s := by
        apply sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le hpos
        have h : s ≤ addOrderOf (signChange a g i) := by
          by_cases hi : i ∈ a <;> simpa [signChange, hi] using hg i
        exact_mod_cast h
      _ = ((b ∆ a).card : ℚ) / s := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast card_finset_fin_le _)

open Classical in
/-- Among sign choices for a sequence of large-order elements, at most `|G|` are bad:
each bad choice must have a distinct subset sum. -/
private lemma card_bad_signs_le [Fintype G] {g : Fin s → G} (hs : 0 < s)
    (hg : ∀ i, s ≤ addOrderOf (g i)) :
    (univ.filter fun a => ¬IsGoodSequence (signChange a g)).card ≤ Fintype.card G := by
  classical
  rw [← card_univ]
  apply card_le_card_of_injOn (fun a => ∑ i ∈ a, g i) (fun _ _ => mem_univ _)
  intro a ha b _ heq
  by_contra hab
  exact (mem_filter.mp ha).2 (good_of_collision hs hg hab heq)

open Classical in
/-- Count the good pairs of a large-order sequence and a sign choice in both orders. -/
private lemma large_order_sequences_le (G : Type*) [AddCommGroup G] [Fintype G]
    (s : ℕ) (hs : 0 < s) (hn : 2 * Fintype.card G ≤ 2 ^ s) :
    Fintype.card {x : G // s ≤ addOrderOf x} ^ s ≤
      2 * (univ.filter (IsGoodSequence (Γ := G) (t := s))).card := by
  let H := {x : G // s ≤ addOrderOf x}
  let signed (a : Finset (Fin s)) (g : Fin s → H) := signChange a (fun i => (g i).val)
  let good := univ.filter (IsGoodSequence (Γ := G) (t := s))
  have row (g : Fin s → H) :
      2 ^ s ≤ 2 * (univ.filter fun a => IsGoodSequence (signed a g)).card := by
    have hbad := card_bad_signs_le (g := fun i => (g i).val) hs (fun i => (g i).property)
    have hall := card_filter_add_card_filter_not (s := univ) (fun a => IsGoodSequence (signed a g))
    simp only [card_univ, Fintype.card_finset, Fintype.card_fin] at hall
    change (univ.filter fun a => ¬IsGoodSequence (signed a g)).card ≤ _ at hbad
    omega
  have col (a : Finset (Fin s)) :
      (univ.filter fun g => IsGoodSequence (signed a g)).card ≤ good.card := by
    apply card_le_card_of_injOn (signed a)
      (fun _ hg => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hg).2⟩)
    intro g _ h _ heq
    funext i
    apply Subtype.ext
    have hi := congrFun heq i
    by_cases hia : i ∈ a <;> simpa [signed, signChange, hia] using hi
  have hsum :
      (∑ g : Fin s → H, (univ.filter fun a => IsGoodSequence (signed a g)).card) =
        ∑ a : Finset (Fin s), (univ.filter fun g => IsGoodSequence (signed a g)).card := by
    calc
      _ = ∑ g : Fin s → H, ∑ a : Finset (Fin s), if IsGoodSequence (signed a g)
          then (1 : ℕ) else 0 := sum_congr rfl fun _ _ => (sum_boole _ _).symm
      _ = ∑ a : Finset (Fin s), ∑ g : Fin s → H, if IsGoodSequence (signed a g)
          then (1 : ℕ) else 0 := sum_comm
      _ = _ := sum_congr rfl fun _ _ => sum_boole _ _
  have hb := calc
    ∑ _g : Fin s → H, 2 ^ s ≤ ∑ g : Fin s → H,
        2 * (univ.filter fun a => IsGoodSequence (signed a g)).card :=
      sum_le_sum fun g _ => row g
    _ = 2 * ∑ a : Finset (Fin s), (univ.filter fun g => IsGoodSequence (signed a g)).card := by
      rw [← mul_sum, hsum]
    _ ≤ 2 * ∑ _a : Finset (Fin s), good.card :=
      Nat.mul_le_mul_left _ (sum_le_sum fun a _ => col a)
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_finset,
    smul_eq_mul] at hb
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ s) _ (by positivity)
  simpa only [mul_assoc, mul_left_comm, mul_comm, H, good] using hb

open Classical in
/-- There are at most `s²` elements of order below `s` in a cyclic group. For each
positive `d < s`, at most `d` elements are killed by `d`. -/
private lemma small_order_card_le (G : Type*) [AddCommGroup G] [Fintype G] [IsAddCyclic G]
    (s : ℕ) : (univ.filter fun x : G => ¬s ≤ addOrderOf x).card ≤ s ^ 2 := by
  let roots (i : ℕ) := univ.filter fun x : G => (i + 1) • x = 0
  calc
    _ ≤ ((range s).biUnion roots).card := by
      apply card_le_card
      intro x hx
      have hlt := lt_of_not_ge (mem_filter.mp hx).2
      have hpos := addOrderOf_pos x
      refine mem_biUnion.mpr ⟨addOrderOf x - 1, mem_range.mpr (by omega), ?_⟩
      simp [roots, Nat.sub_add_cancel hpos]
    _ ≤ ∑ i ∈ range s, (roots i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ range s, s := by
      apply sum_le_sum
      intro i hi
      exact (IsAddCyclic.card_nsmul_eq_zero_le (α := G) (Nat.succ_pos i)).trans (mem_range.mp hi)
    _ = _ := by simp [pow_two]

/-- If the group is large compared to the number of small-order coordinates and small
compared to the number of sign choices, at least a quarter of all sequences are good. -/
private lemma quarter_le_good_prob (n s : ℕ) [NeZero n] (hs : 0 < s)
    (hsmall : 2 * s ^ 3 ≤ n) (hsigns : 2 * n ≤ 2 ^ s) :
    1 / 4 ≤ goodSequenceProb (ZMod n) s := by
  classical
  let H := {x : ZMod n // s ≤ addOrderOf x}
  let h := (Fintype.card H : ℝ)
  let b := ((univ.filter fun x : ZMod n => ¬s ≤ addOrderOf x).card : ℝ)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hh : 0 ≤ h := Nat.cast_nonneg _
  have hsum : h + b = n := by
    dsimp only [h, b, H]
    rw [Fintype.card_subtype, ← Nat.cast_add, card_filter_add_card_filter_not, card_univ, ZMod.card]
  have hb : b ≤ (s : ℝ) ^ 2 := by
    dsimp only [b]
    exact_mod_cast small_order_card_le (ZMod n) s
  have hcost : (2 : ℝ) * s ^ 3 ≤ n := by exact_mod_cast hsmall
  have hbn : 2 * (s : ℝ) * b ≤ n := by
    calc
      _ ≤ 2 * (s : ℝ) * s ^ 2 := by gcongr
      _ = _ := by ring
      _ ≤ _ := hcost
  have hhalf : (1 : ℝ) / 2 ≤ (h / n) ^ s := by
    have hratio : 1 + -(b / n) = h / n := by
      field_simp
      linarith
    have hber := one_add_mul_le_pow (a := -(b / (n : ℝ)))
      (by rw [← neg_div, le_div_iff₀ hn]; linarith : (-2 : ℝ) ≤ -(b / n)) s
    rw [hratio] at hber
    refine le_trans ?_ hber
    rw [mul_neg, ← mul_div_assoc, ← sub_eq_add_neg]
    have := (div_le_iff₀ hn).mpr (show (s : ℝ) * b ≤ 1 / 2 * n by linarith)
    linarith
  let good := univ.filter (IsGoodSequence (Γ := ZMod n) (t := s))
  have hcount : h ^ s ≤ 2 * (good.card : ℝ) := by
    dsimp only [h, good, H]
    exact_mod_cast large_order_sequences_le (ZMod n) s hs (by simpa only [ZMod.card] using hsigns)
  rw [div_pow, le_div_iff₀ (pow_pos hn s)] at hhalf
  have hprob : goodSequenceProb (ZMod n) s = (good.card : ℝ) / (n : ℝ) ^ s := by
    simp [goodSequenceProb, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, good]
  rw [hprob, le_div_iff₀ (pow_pos hn s)]
  linarith

/-- At length `7k`, the probability of a good sequence stays bounded away from zero. -/
private lemma quarter_le_good_prob_seven_mul :
    ∀ᶠ k : ℕ in atTop, 1 / 4 ≤ goodSequenceProb (ZMod (35 ^ k)) (7 * k) := by
  filter_upwards [eventually_ge_atTop 3] with k hk
  apply quarter_le_good_prob _ _ (by omega)
  · induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      have hk' : 7 * (k + 1) ≤ 2 * (7 * k) := by omega
      calc
        2 * (7 * (k + 1)) ^ 3 ≤ 2 * (2 * (7 * k)) ^ 3 := by gcongr
        _ = 8 * (2 * (7 * k) ^ 3) := by ring
        _ ≤ 8 * 35 ^ k := Nat.mul_le_mul_left _ ih
        _ ≤ 35 ^ (k + 1) := by rw [pow_succ, mul_comm]; gcongr; decide
  · calc
      2 * 35 ^ k ≤ 2 ^ k * (2 ^ 6) ^ k := by
        gcongr <;> first | decide | exact Nat.le_self_pow (by omega) _
      _ = 2 ^ (7 * k) := by rw [← mul_pow, show 2 * 2 ^ 6 = 2 ^ 7 by decide, pow_mul]

/-- Test the small-sample half of the threshold condition just where the threshold
exceeds `k²`. On those indices the sample of length `7k` is little-o of the threshold. -/
private lemma threshold_le_sq {t : ℕ → ℝ}
    (ht : IsThresholdFunction (fun k s => goodSequenceProb (ZMod (35 ^ k)) s) t) :
    ∀ᶠ k : ℕ in atTop, t k ≤ (k : ℝ) ^ 2 := by
  let f (k : ℕ) := if (k : ℝ) ^ 2 < t k then 7 * k else 0
  have hf : (fun k => (f k : ℝ)) =o[atTop] t := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (7 / c)] with k hk
    by_cases h : (k : ℝ) ^ 2 < t k
    · have hc' := (div_le_iff₀ hc).mp hk
      have htk : 0 ≤ t k := (sq_nonneg _).trans h.le
      simp only [f, ite_eq_left h, Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs,
        abs_of_nonneg htk, abs_of_nonneg (show 0 ≤ 7 * (k : ℝ) by positivity)]
      calc
        _ ≤ ((k : ℝ) * c) * k := by gcongr
        _ = c * (k : ℝ) ^ 2 := by ring
        _ ≤ _ := by gcongr
    · simp only [f, ite_eq_right h, Nat.cast_zero, norm_zero]
      exact mul_nonneg hc.le (norm_nonneg _)
  have hlim := (ht.2 f).2 hf
  filter_upwards [hlim.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num),
    quarter_le_good_prob_seven_mul] with k hlt hle
  by_contra! h
  exact (not_lt_of_ge hle) (by simpa only [f, ite_eq_left h] using hlt)

/-- **Threshold for good sequences in $\mathbb{Z}/35^k\mathbb{Z}$.** Write $\lg = \log_2$. Let $t$
be a threshold function, in $k$, for the probability that a uniformly random sequence of $s$
elements of $\mathbb{Z}/35^k\mathbb{Z}$ is good. Then there is a real constant $C$ such that for
all sufficiently large $k$,
$$t(k) \le k^2 \exp\left((3 \lg 5 \lg 7 \lg k)^{1/3} - \tfrac{2}{3} \lg \lg k + C\right).$$

The source writes the prefactor as $n$; here $n = k^2$, the factor $k^d$ of the source's
Theorem 4 at $d = 2$, since $\mathbb{Z}/35^k\mathbb{Z} \cong \mathbb{Z}/5^k\mathbb{Z} \times
\mathbb{Z}/7^k\mathbb{Z}$. The constant $C$ depends on $t$: thresholds are only determined up to
constant factors, so no single $C$ serves every threshold.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Corollary 2 (`integers-2024-A93-cor-2`). -/
theorem zmod_thirtyFive_pow_good_threshold_le (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun k s => goodSequenceProb (ZMod (35 ^ k)) s) t) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in Filter.atTop,
      t k ≤ (k : ℝ) ^ 2 * Real.exp ((3 * Real.logb 2 5 * Real.logb 2 7 * Real.logb 2 k) ^
          ((1 : ℝ) / 3) - 2 / 3 * Real.logb 2 (Real.logb 2 k) + C) := by
  refine ⟨0, ?_⟩
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlog := Real.log_pos hb
  have h5 : 1 ≤ Real.logb 2 5 :=
    (Real.logb_self_eq_one hb).symm.le.trans
      (Real.logb_le_logb_of_le hb (by norm_num) (by norm_num))
  have h7 : 1 ≤ Real.logb 2 7 :=
    (Real.logb_self_eq_one hb).symm.le.trans
      (Real.logb_le_logb_of_le hb (by norm_num) (by norm_num))
  have hcoef : 1 ≤ 3 * Real.logb 2 5 * Real.logb 2 7 := by
    nlinarith [mul_le_mul h5 h7 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ Real.logb 2 5)]
  have htop := (Real.tendsto_logb_atTop hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogpow := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 3) (by norm_num)).comp_tendsto htop
  filter_upwards [threshold_le_sq ht, hlogpow.def hlog, htop.eventually_ge_atTop 1]
    with k hk hg hx
  let x := Real.logb 2 k
  change 1 ≤ x at hx
  have hx0 : 0 ≤ x := by linarith
  have hpow := Real.rpow_nonneg hx0 ((1 : ℝ) / 3)
  change ‖Real.log x‖ ≤ Real.log 2 * ‖x ^ ((1 : ℝ) / 3)‖ at hg
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx), Real.norm_eq_abs,
    abs_of_nonneg hpow] at hg
  have hroot : x ^ ((1 : ℝ) / 3) ≤
      (3 * Real.logb 2 5 * Real.logb 2 7 * x) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hx0 (le_mul_of_one_le_left hx0 hcoef) (by norm_num)
  have hl : Real.logb 2 x ≤ x ^ ((1 : ℝ) / 3) :=
    (div_le_iff₀ hlog).mpr (by linarith)
  apply hk.trans
  apply le_mul_of_one_le_right (sq_nonneg _)
  apply Real.one_le_exp_iff.mpr
  change 0 ≤ _ - 2 / 3 * Real.logb 2 x + 0
  linarith

end

end MetaMathlibExt

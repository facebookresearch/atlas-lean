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
import Mathlib.Data.Fintype.CardEmbedding
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

namespace zmod_two_pi_good_threshold_isBigO

variable {d : ℕ}

private lemma two_nsmul_zmod2 {x : Fin d → ZMod 2} : (2 : ℕ) • x = 0 := by
  funext j
  have h : ∀ y : ZMod 2, (2 : ℕ) • y = 0 := by decide
  simpa using h (x j)

private lemma add_self_zmod2 {x : Fin d → ZMod 2} : x + x = 0 := by
  rw [← two_nsmul]
  exact two_nsmul_zmod2

private lemma neg_eq_self_zmod2 {x : Fin d → ZMod 2} : -x = x := by
  exact (eq_neg_of_add_eq_zero_left add_self_zmod2).symm

private lemma addOrderOf_eq {x : Fin d → ZMod 2} (hx : x ≠ 0) : addOrderOf x = 2 := by
  have hdvd : addOrderOf x ∣ 2 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr two_nsmul_zmod2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hx
  · exact h

private lemma good_of_zero {s : ℕ} {g : Fin s → Fin d → ZMod 2} {i : Fin s} (hi : g i = 0) :
    IsGoodSequence g := by
  refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_⟩
  · simp [hi]
  · simp [hi]

private lemma good_of_repeat {s : ℕ} {g : Fin s → Fin d → ZMod 2} {i j : Fin s} (hij : i ≠ j)
    (h : g i = g j) : IsGoodSequence g := by
  by_cases hi : g i = 0
  · exact good_of_zero hi
  · refine ⟨{i, j}, ?_, ?_, ?_⟩
    · exact Finset.insert_nonempty _ _
    · rw [Finset.sum_pair hij, h, add_self_zmod2]
    · rw [Finset.sum_pair hij, addOrderOf_eq hi, addOrderOf_eq (by rwa [h] at hi)]
      norm_num

private lemma good_iff {s : ℕ} {g : Fin s → Fin d → ZMod 2} :
    IsGoodSequence g ↔ (∃ i, g i = 0) ∨ ∃ i j, i ≠ j ∧ g i = g j := by
  constructor
  · intro hgood
    by_contra hcon
    have hzero : ∀ i, g i ≠ 0 := fun i hi => hcon (Or.inl ⟨i, hi⟩)
    have hrep : ∀ i j, i ≠ j → g i ≠ g j := fun i j hij h => hcon (Or.inr ⟨i, j, hij, h⟩)
    have hinj : Function.Injective g := by
      intro i j hij
      by_contra hne
      exact hrep i j hne hij
    obtain ⟨S, hSne, hsum, hcross⟩ := hgood
    have hterm : ∀ i ∈ S, (1 : ℚ) / addOrderOf (g i) = 1 / 2 := by
      intro i _
      rw [addOrderOf_eq (hzero i)]
      norm_num
    have hsumq : ∑ i ∈ S, (1 : ℚ) / addOrderOf (g i) = (S.card : ℚ) / 2 := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsumq] at hcross
    have hcard : S.card ≤ 2 := by
      by_contra hc
      push Not at hc
      have : (2 : ℚ) < S.card := by exact_mod_cast hc
      linarith
    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
    rcases (by omega : S.card = 1 ∨ S.card = 2) with h1 | h2
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
      rw [hi, Finset.sum_singleton] at hsum
      exact hzero i hsum
    · obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h2
      rw [hS, Finset.sum_pair hab] at hsum
      have hab' : g a = g b := by
        have h1 : g a = -g b := eq_neg_of_add_eq_zero_left hsum
        rw [h1, neg_eq_self_zmod2]
      exact (hinj.ne hab) hab'
  · rintro (⟨i, hi⟩ | ⟨i, j, hij, h⟩)
    · exact good_of_zero hi
    · exact good_of_repeat hij h

private lemma descFactorial_eq_prod_range (n s : ℕ) :
    n.descFactorial s = ∏ i ∈ Finset.range s, (n - i) := by
  induction s with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, ih, Finset.prod_range_succ, mul_comm]

private lemma descFactorial_div_le {n s : ℕ} (hsn : s ≤ n) (hsq : 2 * n ≤ s ^ 2)
    (hn : 2 ≤ n) :
    ((n.descFactorial s : ℝ)) ≤ 3 / 4 * (n : ℝ) ^ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  rw [descFactorial_eq_prod_range]
  have hcast : ((∏ i ∈ Finset.range s, (n - i) : ℕ) : ℝ) =
      ∏ i ∈ Finset.range s, ((n : ℝ) - i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i ≤ n := le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hsn
    rw [Nat.cast_sub hi']
  have hprod : (∏ i ∈ Finset.range s, (((n : ℝ) - i) / n)) =
      (∏ i ∈ Finset.range s, ((n : ℝ) - i)) / (n : ℝ) ^ s := by
    rw [Finset.prod_div_distrib]
    simp [Finset.prod_const]
  have hle : ∏ i ∈ Finset.range s, (((n : ℝ) - i) / n) ≤ 3 / 4 := by
    set m := s / 2 with hm_def
    set k := s - m with hk_def
    have hmk : m + k = s := by omega
    have hf0 : ∀ i, i < s → (0 : ℝ) ≤ ((n : ℝ) - i) / n := by
      intro i hi
      apply div_nonneg _ hnR.le
      have : (i : ℝ) ≤ n := by
        have hi' : i ≤ n := le_trans (Nat.le_of_lt hi) hsn
        exact_mod_cast hi'
      linarith
    have hf1 : ∀ i, i < s → ((n : ℝ) - i) / n ≤ 1 := by
      intro i _
      rw [div_le_one hnR]
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hsplit : (∏ i ∈ Finset.range s, (((n : ℝ) - i) / n)) =
        (∏ i ∈ Finset.range m, (((n : ℝ) - i) / n)) *
          ∏ i ∈ Finset.range k, (((n : ℝ) - ((m + i : ℕ) : ℝ)) / n) := by
      conv_lhs => rw [← hmk]
      exact Finset.prod_range_add (fun i => (((n : ℝ) - (i : ℝ)) / n)) m k
    set a := (m : ℝ) / n with ha_def
    set q := 1 - a with hq_def
    have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg m) hnR.le
    have ha1 : a ≤ 1 := by
      rw [ha_def, div_le_one hnR]
      have : m ≤ n := le_trans (Nat.div_le_self s 2) hsn
      exact_mod_cast this
    have hq0 : 0 ≤ q := by linarith
    have hprod1 : (∏ i ∈ Finset.range m, (((n : ℝ) - i) / n)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro i hi
        exact hf0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega : m ≤ s))
      · intro i hi
        exact hf1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega : m ≤ s))
    have hbound : ∀ i ∈ Finset.range k, (((n : ℝ) - ((m + i : ℕ) : ℝ)) / n) ≤ q := by
      intro i hi
      have hi' : m + i ≤ n := by
        have hlt : m + i < s := by
          have h1 : i < k := Finset.mem_range.mp hi
          omega
        exact le_of_lt (lt_of_lt_of_le hlt hsn)
      have hnum : (n : ℝ) - ((m + i : ℕ) : ℝ) ≤ (n : ℝ) - m := by
        rw [Nat.cast_add]
        have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
      calc ((n : ℝ) - ((m + i : ℕ) : ℝ)) / n ≤ ((n : ℝ) - m) / n :=
            div_le_div_of_nonneg_right hnum hnR.le
        _ = q := by
            rw [hq_def, ha_def, sub_div, div_self hnR.ne']
    have hprod2 : (∏ i ∈ Finset.range k, (((n : ℝ) - ((m + i : ℕ) : ℝ)) / n)) ≤ q ^ k := by
      calc (∏ i ∈ Finset.range k, (((n : ℝ) - ((m + i : ℕ) : ℝ)) / n))
          ≤ ∏ _i ∈ Finset.range k, q := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact hf0 (m + i) (by
                have h1 : i < k := Finset.mem_range.mp hi
                omega)
            · intro i hi
              exact hbound i hi
        _ = q ^ k := by rw [Finset.prod_const, Finset.card_range]
    have hkmR : (n : ℝ) ≤ 3 * (k : ℝ) * (m : ℝ) := by
      have hsqR : (2 : ℝ) * n ≤ (s : ℝ) ^ 2 := by exact_mod_cast hsq
      have hmr : s = 2 * m + s % 2 := by omega
      have hkr : k = m + s % 2 := by omega
      have hr1 : s % 2 ≤ 1 := by have h := Nat.mod_lt s (by norm_num : 0 < 2); omega
      have hm1 : 1 ≤ m := by
        have hs2 : 2 ≤ s := by
          by_contra hc
          push Not at hc
          have hle : s ^ 2 ≤ 1 := by
            calc s ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
              _ = 1 := by norm_num
          omega
        omega
      have hrR : ((s % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hr1
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hsR : (s : ℝ) = 2 * m + ((s % 2 : ℕ) : ℝ) := by
        have h := hmr
        exact_mod_cast h
      have hkR : (k : ℝ) = m + ((s % 2 : ℕ) : ℝ) := by
        have h := hkr
        exact_mod_cast h
      nlinarith [hsqR, hsR, hkR, hrR, hmR,
        mul_nonneg (show (0:ℝ) ≤ m by linarith)
          (show (0:ℝ) ≤ ((s % 2 : ℕ) : ℝ) by positivity)]
    have hka : (1 : ℝ) / 3 ≤ (k : ℝ) * a := by
      calc (1 : ℝ) / 3 ≤ ((k : ℝ) * (m : ℝ)) / n :=
            (le_div_iff₀ hnR).mpr (by linarith [hkmR])
        _ = (k : ℝ) * a := by rw [ha_def, mul_div_assoc]
    have hbern : 1 + (k : ℝ) * a ≤ (1 + a) ^ k :=
      one_add_mul_le_pow (by linarith) k
    have hprod1q : q ^ k * (1 + a) ^ k ≤ 1 := by
      rw [← mul_pow]
      have hqa : q * (1 + a) = 1 - a ^ 2 := by rw [hq_def]; ring
      rw [hqa]
      apply pow_le_one₀
      · nlinarith [ha0, ha1]
      · nlinarith [ha0, ha1]
    have hqle : q ^ k ≤ 1 / (1 + (k : ℝ) * a) := by
      rw [le_div_iff₀ (by linarith [hka] : (0:ℝ) < 1 + (k:ℝ)*a)]
      calc q ^ k * (1 + (k : ℝ) * a) ≤ q ^ k * (1 + a) ^ k :=
            mul_le_mul_of_nonneg_left hbern (pow_nonneg hq0 k)
        _ ≤ 1 := hprod1q
    have hfin : (1 : ℝ) / (1 + (k : ℝ) * a) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by linarith [hka] : (0:ℝ) < 1 + (k:ℝ)*a)]
      linarith [hka]
    rw [hsplit]
    calc (∏ i ∈ Finset.range m, (((n : ℝ) - i) / n)) *
          ∏ i ∈ Finset.range k, (((n : ℝ) - ((m + i : ℕ) : ℝ)) / n)
        ≤ 1 * q ^ k := by
          apply mul_le_mul hprod1 hprod2
          · apply Finset.prod_nonneg
            intro i hi
            exact hf0 (m + i) (by
              have h1 : i < k := Finset.mem_range.mp hi
              omega)
          · norm_num
      _ ≤ 3 / 4 := by
          rw [one_mul]
          exact le_trans hqle hfin
  rw [hcast]
  have hEq : (∏ i ∈ Finset.range s, ((n : ℝ) - i)) =
      (∏ i ∈ Finset.range s, (((n : ℝ) - i) / n)) * (n : ℝ) ^ s := by
    rw [hprod, div_mul_cancel₀ _ (pow_ne_zero _ hnR.ne')]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hle (pow_nonneg hnR.le s)

open Classical in
private lemma card_bad_le {d s : ℕ} :
    (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card ≤
      (2 ^ d).descFactorial s := by
  classical
  have hinj : ∀ g : Fin s → Fin d → ZMod 2, ¬ IsGoodSequence g → Function.Injective g := by
    intro g hg i j hij
    by_contra hne
    exact hg (good_iff.mpr (Or.inr ⟨i, j, hne, hij⟩))
  have hcard : Fintype.card {g : Fin s → Fin d → ZMod 2 // ¬ IsGoodSequence g} =
      (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card := by
    rw [Fintype.card_subtype]
  have hEq : Fintype.card (Fin s ↪ (Fin d → ZMod 2)) = (2 ^ d).descFactorial s := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    simp
  have hinj' : Function.Injective (fun g : {g // ¬ IsGoodSequence g} =>
      (⟨g.1, hinj g.1 g.2⟩ : Fin s ↪ (Fin d → ZMod 2))) := by
    intro ⟨g1, h1⟩ ⟨g2, h2⟩ h
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg DFunLike.coe h) i
    exact hi
  rw [← hcard]
  exact le_trans (Fintype.card_le_of_injective _ hinj') (le_of_eq hEq)

open Classical in
private lemma quarter_le_good_prob {d s : ℕ} (hsn : s ≤ 2 ^ d) (hsq : 2 * (2 ^ d) ≤ s ^ 2)
    (hn : 2 ≤ 2 ^ d) :
    (1 : ℝ) / 4 ≤ goodSequenceProb (Fin d → ZMod 2) s := by
  classical
  have hbad := card_bad_le (d := d) (s := s)
  have hdesc := descFactorial_div_le hsn hsq hn
  have hsum : (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => IsGoodSequence g).card +
      (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card =
      (2 ^ d) ^ s := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hprob : goodSequenceProb (Fin d → ZMod 2) s =
      ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => IsGoodSequence g).card : ℝ) /
        ((2 ^ d : ℕ) : ℝ) ^ s := by
    simp [goodSequenceProb, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  have hnR : (0 : ℝ) < (2 ^ d : ℕ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hpowR : (0 : ℝ) < ((2 ^ d : ℕ) : ℝ) ^ s := pow_pos hnR s
  rw [hprob, le_div_iff₀ hpowR]
  have hbadR : ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 =>
      ¬ IsGoodSequence g).card : ℝ) ≤ 3 / 4 * ((2 ^ d : ℕ) : ℝ) ^ s := by
    have h1 : ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 =>
        ¬ IsGoodSequence g).card : ℝ) ≤ ((2 ^ d).descFactorial s : ℝ) := by
      exact_mod_cast hbad
    exact le_trans h1 hdesc
  have hsumR : ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => IsGoodSequence g).card : ℝ) +
      ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card : ℝ) =
      ((2 ^ d : ℕ) : ℝ) ^ s := by
    have h := hsum
    exact_mod_cast h
  linarith [hbadR, hsumR, hpowR]

private lemma logb_two_pow (d : ℕ) : Real.logb 2 ((2 : ℝ) ^ d) = (d : ℝ) := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]

private lemma denom_le {d : ℕ} (ε : ℝ) (hε : 0 < ε) (hd : 2 ≤ d) :
    (Real.logb 2 (d : ℝ)) ^ (1 - ε) ≤ 3 * (d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ Real.logb 2 (d : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by norm_num : (0:ℝ) < 2) hdR
    rwa [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at h
  have hLd : Real.logb 2 (d : ℝ) ≤ (d : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (hdpos)]
    have h : (d : ℝ) ≤ (2 : ℝ) ^ d := by
      have h' : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
      exact_mod_cast h'
    have h2 : (2 : ℝ) ^ (d : ℝ) = (2 : ℝ) ^ d := by
      rw [Real.rpow_natCast]
    rw [h2]
    exact h
  have hr : (1 : ℝ) - ε < 1 := by linarith
  by_cases hneg : (1 : ℝ) - ε ≤ 0
  · have h1 : (Real.logb 2 (d : ℝ)) ^ (1 - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 hneg
    linarith [h1, hdR]
  · push Not at hneg
    have h2 : (Real.logb 2 (d : ℝ)) ^ (1 - ε) ≤ Real.logb 2 (d : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 (show (1:ℝ) - ε ≤ 1 by linarith)
      rwa [Real.rpow_one] at h
    linarith [h2, hLd, hdR]

private lemma one_le_logb_two_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) ≤ Real.logb 2 (d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by norm_num : (0:ℝ) < 2) hdR
  rwa [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at h

private lemma two_pow_eq_exp (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

private lemma s_isLittleO (ε : ℝ) (hε : 0 < ε) :
    (fun d : ℕ => ((2 ^ (d / 2 + 1) : ℕ) : ℝ)) =o[Filter.atTop]
      (fun d : ℕ => (2 : ℝ) ^ d /
        (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set b := Real.log 2 / 2 with hb_def
  have hb : 0 < b := by positivity
  have hpoly : (fun d : ℕ => (d : ℝ)) =o[Filter.atTop]
      (fun d : ℕ => Real.exp (b * (d : ℝ))) := by
    have h := (isLittleO_rpow_exp_pos_mul_atTop (1 : ℝ) hb).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Real.rpow_one, Function.comp_def] using h
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hc6 : (0 : ℝ) < c / 6 := by linarith
  have hbound := (Asymptotics.isLittleO_iff.mp hpoly) hc6
  filter_upwards [hbound, Filter.eventually_ge_atTop 2] with d hd1 hd2
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hdpos : (0 : ℝ) < d := by linarith
  have hlogd : Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) = Real.logb 2 (d : ℝ) := by
    rw [logb_two_pow]
  have hL1 : (1 : ℝ) ≤ Real.logb 2 (d : ℝ) := one_le_logb_two_of_two_le hd2
  have hLpos : (0 : ℝ) < Real.logb 2 (d : ℝ) := by linarith
  have hdenomPos : (0 : ℝ) < (Real.logb 2 (d : ℝ)) ^ (1 - ε) :=
    Real.rpow_pos_of_pos hLpos _
  have hdenom := denom_le ε hε hd2
  have hgpos : (0 : ℝ) < (2 : ℝ) ^ d /
      (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε) := by
    rw [hlogd]
    exact div_pos (pow_pos (by norm_num) d) hdenomPos
  have hd1' : (d : ℝ) ≤ (c / 6) * Real.exp (b * (d : ℝ)) := by
    have h := hd1
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (d:ℝ) by positivity),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h
  have h6 : 6 * (d : ℝ) ≤ c * Real.exp (b * (d : ℝ)) := by
    calc 6 * (d : ℝ) ≤ 6 * ((c / 6) * Real.exp (b * (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hd1' (by norm_num)
      _ = c * Real.exp (b * (d : ℝ)) := by ring
  set E := Real.exp (b * (d : ℝ)) with hE_def
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have he : ((d / 2 + 1 : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have h2n : 2 * (d / 2) ≤ d := Nat.mul_div_le d 2
    have h2 : (2 : ℝ) * ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2n
    push_cast
    linarith
  have hsE : ((2 ^ (d / 2 + 1) : ℕ) : ℝ) ≤ 2 * E := by
    have hcast : ((2 ^ (d / 2 + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (d / 2 + 1) := by
      push_cast
      ring
    rw [hcast, two_pow_eq_exp]
    have hle : ((d / 2 + 1 : ℕ) : ℝ) * Real.log 2 ≤ b * (d : ℝ) + Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right he hlog2.le
      have hEq : ((d : ℝ) / 2 + 1) * Real.log 2 = b * (d : ℝ) + Real.log 2 := by
        rw [hb_def]
        ring
      linarith
    calc Real.exp (((d / 2 + 1 : ℕ) : ℝ) * Real.log 2)
        ≤ Real.exp (b * (d : ℝ) + Real.log 2) := Real.exp_le_exp.mpr hle
      _ = 2 * E := by rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]; ring
  have hpowd : (2 : ℝ) ^ d = E ^ 2 := by
    rw [two_pow_eq_exp]
    have hEq : (d : ℝ) * Real.log 2 = 2 * (b * (d : ℝ)) := by
      rw [hb_def]
      ring
    rw [hEq]
    have hE2 : Real.exp (2 * (b * (d : ℝ))) = E ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul]
    exact hE2
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ((2 ^ (d / 2 + 1) : ℕ) : ℝ)),
    Real.norm_eq_abs, abs_of_pos hgpos]
  calc ((2 ^ (d / 2 + 1) : ℕ) : ℝ) ≤ 2 * E := hsE
    _ ≤ c * (E ^ 2 / (3 * (d : ℝ))) := by
        rw [← mul_div_assoc, le_div_iff₀ (show (0:ℝ) < 3 * (d:ℝ) by positivity)]
        have hmul : 6 * (d : ℝ) * E ≤ c * E * E :=
          mul_le_mul_of_nonneg_right h6 hEpos.le
        calc (2 * E) * (3 * (d : ℝ)) = 6 * (d : ℝ) * E := by ring
          _ ≤ c * E * E := hmul
          _ = c * E ^ 2 := by ring
    _ ≤ c * ((2 : ℝ) ^ d / (Real.logb 2 (d : ℝ)) ^ (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        rw [hpowd]
        exact div_le_div_of_nonneg_left (sq_nonneg E) hdenomPos hdenom
    _ = c * ((2 : ℝ) ^ d /
        (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε)) := by
        rw [hlogd, hpowd]

end zmod_two_pi_good_threshold_isBigO

/-- **Threshold for good sequences in $\mathbb{Z}_2^d$.** Write $\lg = \log_2$. Let $t$ be a
threshold function, in $d$, for the probability that a uniformly random sequence of $s$ elements
of $\mathbb{Z}_2^d$ is good, and write $n = 2^d$. Then for every $\varepsilon > 0$,
$t(d) = O\left(n / (\lg \lg n)^{1-\varepsilon}\right)$ as $d \to \infty$.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 11 (`integers-2024-A93-thm-11`). -/
theorem zmod_two_pi_good_threshold_isBigO (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε) := by
  have hprob : ∀ᶠ d in Filter.atTop,
      (1 : ℝ) / 4 ≤ goodSequenceProb (Fin d → ZMod 2) (2 ^ (d / 2 + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 4] with d hd
    apply zmod_two_pi_good_threshold_isBigO.quarter_le_good_prob
    · apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
      omega
    · have h2e : d + 1 ≤ 2 * (d / 2 + 1) := by omega
      calc 2 * (2 ^ d) = 2 ^ (d + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ (2 * (d / 2 + 1)) := Nat.pow_le_pow_right (by norm_num) h2e
        _ = (2 ^ (d / 2 + 1)) ^ 2 := by
            rw [show 2 * (d / 2 + 1) = (d / 2 + 1) * 2 by omega, pow_mul]
    · calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgpos : ∀ᶠ d in Filter.atTop,
      (0 : ℝ) < (2 : ℝ) ^ d /
        (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with d hd
    rw [zmod_two_pi_good_threshold_isBigO.logb_two_pow]
    apply div_pos (pow_pos (by norm_num) d)
    apply Real.rpow_pos_of_pos
    have hL1 : (1 : ℝ) ≤ Real.logb 2 (d : ℝ) :=
      zmod_two_pi_good_threshold_isBigO.one_le_logb_two_of_two_le hd
    linarith
  have hsO := zmod_two_pi_good_threshold_isBigO.s_isLittleO ε hε
  let f : ℕ → ℕ := fun d =>
    if (2 : ℝ) ^ d / (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε) < t d
      then 2 ^ (d / 2 + 1) else 0
  have hfO : (fun d : ℕ => ((f d : ℕ) : ℝ)) =o[Filter.atTop] t := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [(Asymptotics.isLittleO_iff.mp hsO) hc, ht.1, hgpos] with d hd1 hd2 hd3
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ (d / 2 + 1) : ℕ) : ℝ)),
      Real.norm_eq_abs, abs_of_pos hd3] at hd1
    by_cases h : (2 : ℝ) ^ d / (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε) < t d
    · simp only [f, ite_eq_left h]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ (d / 2 + 1) : ℕ) : ℝ)),
        Real.norm_eq_abs, abs_of_pos hd2]
      exact le_trans hd1 (mul_le_mul_of_nonneg_left h.le hc.le)
    · simp only [f, ite_eq_right h, Nat.cast_zero, Real.norm_eq_abs, abs_zero]
      exact mul_nonneg hc.le (abs_nonneg _)
  have hlim := (ht.2 f).2 hfO
  have hle : ∀ᶠ d in Filter.atTop,
      t d ≤ (2 : ℝ) ^ d / (Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d))) ^ (1 - ε) := by
    filter_upwards [hlim.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num),
      hprob] with d hlt hleprob
    by_contra hcon
    push Not at hcon
    have hfEq : f d = 2 ^ (d / 2 + 1) := by simp only [f, ite_eq_left hcon]
    have hlt' : goodSequenceProb (Fin d → ZMod 2) (2 ^ (d / 2 + 1)) < 1 / 4 := by
      simpa only [hfEq] using hlt
    exact (not_lt_of_ge hleprob) hlt'
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hle, ht.1, hgpos] with d hd1 hd2 hd3
  rw [Real.norm_eq_abs, abs_of_nonneg hd2.le, Real.norm_eq_abs, abs_of_pos hd3, one_mul]
  exact hd1

end

end MetaMathlibExt

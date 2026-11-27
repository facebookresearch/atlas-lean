/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Additive.MaxMinIndecomposability
import MathlibExt.Probability.HoeffdingBounded
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hoeffding extremal lunar numbers

This module defines lunar level counts and Hoeffding extremal lunar numbers, and bounds
the cardinality of the extremal set.

Statements from Benjamin Baily, Justine Dell, Henry L. Fleischmann, Faye Jackson, Ethan Pesikoff,
Steven J. Miller and Luke Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of
Integer Sequences 28 (2025), Article 25.2.7.
-/

namespace MetaMathlibExt

@[expose] public section

open Pointwise Filter Topology
open MeasureTheory ProbabilityTheory

/-- **Level counts of a lunar number.** Let $f$ be a lunar number of base $b$ and degree at most
$n$, with digits $c_0, \dots, c_n \in \{0, \dots, b - 1\}$, and let $i$ be a natural number. The
level count $|f_i|$ is the number of indices $k \le n$ with $c_k \ge i$, that is, the number of
nonzero coefficients of the $i$-level support $f_i = s_i(f)$, the Boolean polynomial with
coefficient $1$ at $x^k$ when $c_k \ge i$ and $0$ otherwise.

A lunar number $f$ is not a monomial $t x^m$ (with $t = 0$ allowed) if and only if $|f_1| \ge 2$,
and $f_i$ is not a monomial if and only if $|f_i| \ge 2$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, Definitions 13 and 16. -/
public def lunarLevelCount {n b : ℕ} (i : ℕ) (f : Fin (n + 1) → Fin b) : ℕ :=
  (Finset.univ.filter fun k => i ≤ (f k : ℕ)).card

/-- **Hoeffding extremal lunar numbers.** Let $b$ and $n$ be natural numbers and $d$ a real
number. Let $\mathcal{L}_b^n$ be the set of lunar numbers of base $b$ and degree at most $n$
(digit strings $c_0, \dots, c_n$ with digits in $\{0, \dots, b - 1\}$), with the max-min product
$\otimes$, and for $f \in \mathcal{L}_b^n$ let $|f_i|$ be the number of its digits that are at
least $i$. The set $\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers consists of the
$h \in \mathcal{L}_b^n$ for which there is an index $i$ with $1 \le i \le b - 1$ such that either
$\bigl||h_i| - (b - i)n/b\bigr| > d/2$, or $h = f \otimes g$ for some $f, g \in \mathcal{L}_b^n$
with $\bigl||f_i| + |g_i| - (b - i)(n + 1)/b\bigr| > d/2$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Definition 23. -/
public def lunarHoeffdingExtremalSet (b n : ℕ) (d : ℝ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ i, 1 ≤ i ∧ i ≤ b - 1 ∧
    (d / 2 < |(lunarLevelCount i h : ℝ) - ((b : ℝ) - i) * n / b| ∨
      ∃ f g : Fin (n + 1) → Fin b, maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i f + lunarLevelCount i g : ℕ) : ℝ) -
          ((b : ℝ) - i) * (n + 1) / b|)}

private lemma uniform_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Set α) :
    (uniformOn (Set.univ : Set α)).real s = (s.ncard : ℝ) / Fintype.card α := by
  classical
  rw [measureReal_def, uniformOn_univ, Measure.count_apply_finite s s.toFinite]
  rw [Set.ncard_eq_toFinset_card s s.toFinite]
  simp

private lemma level_card {b i : ℕ} (hi : i < b) :
    (Finset.univ.filter fun a : Fin b => i ≤ a.val).card = b - i := by
  have h : (Finset.univ.filter fun a : Fin b => i ≤ a.val) =
      Finset.Ici (⟨i, hi⟩ : Fin b) := by
    ext a
    simp [Fin.le_def]
  rw [h]
  simp

private lemma integral_level {b i : ℕ} (hi : i < b) :
    ∫ a : Fin b, (if i ≤ a.val then (1 : ℝ) else 0)
      ∂uniformOn Set.univ = ((b : ℝ) - i) / b := by
  classical
  rw [integral_fintype (Integrable.of_finite)]
  simp_rw [uniform_real, Set.ncard_singleton, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_boole]
  rw [level_card hi]
  rw [Nat.cast_sub (Nat.le_of_lt hi)]
  ring

private lemma count_tail {m b i : ℕ} (hb : 0 < b) (hi : i < b) {t : ℝ}
    (ht : 0 < t) :
    (({x : Fin m → Fin b | t < |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) -
      (m : ℝ) * (((b : ℝ) - i) / b)|} : Set (Fin m → Fin b)).ncard : ℝ) ≤
      2 * Real.exp (-2 * t ^ 2 / m) * (b : ℝ) ^ m := by
  classical
  let : NeZero b := ⟨Nat.ne_of_gt hb⟩
  by_cases hm : m = 0
  · subst m
    simp [not_lt.mpr ht.le]
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  let X : Fin m → (Fin m → Fin b) → ℝ := fun k x => if i ≤ (x k).val then 1 else 0
  let μ : Measure (Fin m → Fin b) := uniformOn Set.univ
  have hpi : μ = Measure.pi (fun _ : Fin m => uniformOn (Set.univ : Set (Fin b))) := by
    simpa [μ] using (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set (Fin b))))
  have hind : iIndepFun X μ := by
    rw [hpi]
    exact iIndepFun_pi (fun _ => (Measurable.of_discrete :
      Measurable (fun a : Fin b => if i ≤ a.val then (1 : ℝ) else 0)).aemeasurable)
  have hmeas : ∀ k, AEMeasurable (X k) μ := fun _ => Measurable.of_discrete.aemeasurable
  have hrange : ∀ k, ∀ᵐ x ∂μ, X k x ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    exact Filter.Eventually.of_forall fun x => by simp [X]; split_ifs <;> norm_num
  have hint : ∀ k, ∫ x, X k x ∂μ = ((b : ℝ) - i) / b := by
    intro k
    rw [hpi]
    dsimp [X]
    exact (integral_comp_eval (μ := fun _ : Fin m => uniformOn (Set.univ : Set (Fin b)))
      (i := k) (f := fun a : Fin b => if i ≤ a.val then (1 : ℝ) else 0)
      Measurable.of_discrete.aestronglyMeasurable).trans (integral_level hi)
  have hsum (x : Fin m → Fin b) : ∑ k, X k x =
      ((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) := by
    simp [X, Finset.sum_boole]
  have havg (x : Fin m → Fin b) :
      (1 / m : ℝ) * ∑ k, X k x - (1 / m : ℝ) * ∑ k, μ[X k] =
        (((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) -
          (m : ℝ) * (((b : ℝ) - i) / b)) / m := by
    rw [hsum]
    simp_rw [hint]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsub : {x : Fin m → Fin b | t <
      |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) -
        (m : ℝ) * (((b : ℝ) - i) / b)|} ⊆
      {x | t / m ≤ |(1 / m : ℝ) * ∑ k, X k x - (1 / m : ℝ) * ∑ k, μ[X k]|} := by
    intro x hx
    change t / m ≤ |(1 / m : ℝ) * ∑ k, X k x - (1 / m : ℝ) * ∑ k, μ[X k]|
    rw [havg, abs_div, abs_of_pos hmpos]
    exact div_le_div_of_nonneg_right hx.le hmpos.le
  have hh := MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le
    hind hmeas hrange (t := t / m) (by positivity)
  have he : (-2 * (m : ℝ) * (t / m) ^ 2 / (1 - 0) ^ 2) = -2 * t ^ 2 / m := by
    field_simp
    ring
  rw [he] at hh
  have hc := (measureReal_mono hsub).trans hh
  rw [uniform_real] at hc
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hc
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ m)).mp hc

private lemma count_shift_tail {m b i : ℕ} (hm : 1 ≤ m) (hb : 0 < b) (hi : i < b)
    {c d : ℝ} (hc : |(m : ℝ) * (((b : ℝ) - i) / b) - c| ≤ 1) (hd : 0 < d) :
    (({x : Fin m → Fin b | d / 2 <
      |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) - c|} :
      Set (Fin m → Fin b)).ncard : ℝ) ≤
      2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * m)) * (b : ℝ) ^ m := by
  classical
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmR
  by_cases hd2 : d ≤ 2
  · have hc0 : (({x : Fin m → Fin b | d / 2 <
        |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) - c|} :
        Set (Fin m → Fin b)).ncard : ℝ) ≤ (b : ℝ) ^ m := by
      have hU := (Set.ncard_le_ncard (Set.subset_univ _) :
        ({x : Fin m → Fin b | d / 2 <
          |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) - c|} :
          Set (Fin m → Fin b)).ncard ≤ Set.univ.ncard)
      simpa using (Nat.cast_le (α := ℝ).mpr hU)
    have he : (0 : ℝ) ≤ 2 - d ^ 2 / (4 * m) := by
      have h : d ^ 2 ≤ 2 * (4 * (m : ℝ)) := by nlinarith
      exact sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr h)
    have hE : (1 : ℝ) ≤ Real.exp 2 * Real.exp (-d ^ 2 / (4 * m)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      simpa only [sub_eq_add_neg, neg_div] using he
    have htwo : (1 : ℝ) ≤ 2 * (Real.exp 2 * Real.exp (-d ^ 2 / (4 * m))) := by
      linarith
    exact hc0.trans (by nlinarith [pow_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) m])
  · have ht : 0 < d / 2 - 1 := by linarith
    have hsub : {x : Fin m → Fin b | d / 2 <
        |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) - c|} ⊆
        {x | d / 2 - 1 < |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) -
          (m : ℝ) * (((b : ℝ) - i) / b)|} := by
      intro x hx
      have htri := abs_sub_le ((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ)
        ((m : ℝ) * (((b : ℝ) - i) / b)) c
      change d / 2 < |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) - c| at hx
      change d / 2 - 1 < |((Finset.univ.filter fun k => i ≤ (x k).val).card : ℝ) -
        (m : ℝ) * (((b : ℝ) - i) / b)|
      linarith
    have hbound := (Nat.cast_le (α := ℝ).mpr (Set.ncard_le_ncard hsub)).trans
      (count_tail hb hi ht)
    have he : -2 * (d / 2 - 1) ^ 2 / (m : ℝ) ≤ 2 + -d ^ 2 / (4 * m) := by
      calc -2 * (d / 2 - 1) ^ 2 / (m : ℝ)
          ≤ (2 * m - d ^ 2 / 4) / m :=
            div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (d - 4)]) hmpos.le
        _ = 2 + -d ^ 2 / (4 * m) := by field_simp; ring
    have hE := Real.exp_le_exp.mpr he
    rw [Real.exp_add] at hE
    exact hbound.trans (by
      nlinarith [pow_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) m])

private lemma factor_cutoff {b n : ℕ} {f g h : Fin (n + 1) → Fin b}
    (hprod : maxMinMul (digitSeq f) (digitSeq g) = digitSeq h) :
    ∃ k : ℕ, k ≤ n ∧ (∀ j : ℕ, k < j → digitSeq f j = 0) ∧
      (∀ j : ℕ, n - k < j → digitSeq g j = 0) := by
  classical
  by_cases hz : ∀ a : Fin (n + 1), (f a : ℕ) = 0
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j _
      simp [digitSeq, hz]
    · intro j hj
      exact digitSeq_of_le g (by omega)
  · let s : Finset (Fin (n + 1)) := Finset.univ.filter fun a => (f a : ℕ) ≠ 0
    have hs : s.Nonempty := by
      obtain ⟨a, ha⟩ := not_forall.mp hz
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup s hs Fin.val
    have hkf : 0 < digitSeq f k := by
      have : (f k : ℕ) ≠ 0 := (Finset.mem_filter.mp hk).2
      simpa [digitSeq, k.isLt] using Nat.pos_of_ne_zero this
    refine ⟨k.val, by omega, ?_, ?_⟩
    · intro j hj
      by_cases hjn : j < n + 1
      · have hf : (f ⟨j, hjn⟩ : ℕ) = 0 := by
          by_contra hf
          have hmem : (⟨j, hjn⟩ : Fin (n + 1)) ∈ s :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
          have hle := Finset.le_sup (f := Fin.val) hmem
          change j ≤ s.sup Fin.val at hle
          rw [hmax] at hle
          omega
        simpa [digitSeq, hjn] using hf
      · exact digitSeq_of_le f (by omega)
    · intro j hj
      by_contra hgj
      have hpair : (k.val, j) ∈ Finset.antidiagonal (k.val + j) :=
        Finset.mem_antidiagonal.mpr rfl
      have hle : min (digitSeq f k.val) (digitSeq g j) ≤
          maxMinMul (digitSeq f) (digitSeq g) (k.val + j) := by
        change min (digitSeq f k.val) (digitSeq g j) ≤
          (Finset.antidiagonal (k.val + j)).sup
            (fun p : ℕ × ℕ => min (digitSeq f p.1) (digitSeq g p.2))
        exact Finset.le_sup
          (f := fun p : ℕ × ℕ => min (digitSeq f p.1) (digitSeq g p.2)) hpair
      have hpos : 0 < maxMinMul (digitSeq f) (digitSeq g) (k.val + j) :=
        (lt_min hkf (Nat.pos_of_ne_zero hgj)).trans_le hle
      rw [hprod, digitSeq_of_le h (by omega : n + 1 ≤ k.val + j)] at hpos
      omega

private lemma digitSeq_prefix {n b k : ℕ} (hk : k ≤ n)
    (f : Fin (n + 1) → Fin b) (hf : ∀ j : ℕ, k < j → digitSeq f j = 0) :
    digitSeq (fun j : Fin (k + 1) => f (j.castLE (Nat.add_le_add_right hk 1))) =
      digitSeq f := by
  funext j
  by_cases hj : j < k + 1
  · simp [digitSeq, hj, lt_of_lt_of_le hj (Nat.add_le_add_right hk 1)]
  · rw [digitSeq_of_le _ (by omega), hf j (by omega)]

private lemma levelCount_prefix {n b k i : ℕ} (hk : k ≤ n) (hi : 1 ≤ i)
    (f : Fin (n + 1) → Fin b) (hf : ∀ j : ℕ, k < j → digitSeq f j = 0) :
    lunarLevelCount i (fun j : Fin (k + 1) => f (j.castLE (Nat.add_le_add_right hk 1))) =
      lunarLevelCount i f := by
  classical
  unfold lunarLevelCount
  apply Finset.card_bij (fun j _ => j.castLE (Nat.add_le_add_right hk 1))
  · intro j hj
    simpa using hj
  · intro a _ b _ hab
    apply Fin.ext
    simpa using congrArg (fun z : Fin (n + 1) => z.val) hab
  · intro j hj
    have hjk : j.val < k + 1 := by
      by_contra h
      have hz := hf j.val (by omega)
      have hz' : (f j : ℕ) = 0 := by simpa [digitSeq, j.isLt] using hz
      have := (Finset.mem_filter.mp hj).2
      omega
    refine ⟨⟨j.val, hjk⟩, ?_, by ext; rfl⟩
    simpa using hj

private lemma level_fraction {b i : ℕ} (hb : 0 < b) (hi : i < b) :
    0 ≤ ((b : ℝ) - i) / b ∧ ((b : ℝ) - i) / b ≤ 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hiR : (i : ℝ) ≤ b := by exact_mod_cast hi.le
  constructor
  · exact div_nonneg (sub_nonneg.mpr hiR) hbR.le
  · apply (div_le_iff₀ hbR).mpr
    simp

private lemma count_direct {b n i : ℕ} (hb : 0 < b) (hi : i < b) {d : ℝ} (hd : 0 < d) :
    (({h : Fin (n + 1) → Fin b | d / 2 < |(lunarLevelCount i h : ℝ) -
      ((b : ℝ) - i) * n / b|} : Set (Fin (n + 1) → Fin b)).ncard : ℝ) ≤
      2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ (n + 1) := by
  have hp := level_fraction hb hi
  have hc : |(n + 1 : ℝ) * (((b : ℝ) - i) / b) - ((b : ℝ) - i) * n / b| ≤ 1 := by
    have he : (n + 1 : ℝ) * (((b : ℝ) - i) / b) - ((b : ℝ) - i) * n / b =
        ((b : ℝ) - i) / b := by ring
    rw [he, abs_of_nonneg hp.1]
    exact hp.2
  have hbound := count_shift_tail (m := n + 1) (by omega) hb hi
    (c := ((b : ℝ) - i) * n / b) (by simpa using hc) hd
  have he : -d ^ 2 / (4 * (n + 1 : ℝ)) ≤ -d ^ 2 / (4 * (n + 2)) := by
    simpa only [neg_div] using neg_le_neg
      (div_le_div_of_nonneg_left (sq_nonneg d)
        (by positivity : (0 : ℝ) < 4 * (n + 1 : ℝ))
        (by linarith : (4 * (n + 1 : ℝ)) ≤ 4 * (n + 2)))
  have hE : Real.exp (-d ^ 2 / (4 * ((n + 1 : ℕ) : ℝ))) ≤
      Real.exp (-d ^ 2 / (4 * (n + 2))) := by
    simpa using Real.exp_le_exp.mpr he
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity))

private lemma count_pairs {b a c i : ℕ} (hb : 0 < b) (hi : i < b) {d : ℝ} (hd : 0 < d) :
    (({fg : (Fin (a + 1) → Fin b) × (Fin (c + 1) → Fin b) |
      d / 2 < |((lunarLevelCount i fg.1 + lunarLevelCount i fg.2 : ℕ) : ℝ) -
        ((b : ℝ) - i) * (a + c + 1) / b|} :
      Set ((Fin (a + 1) → Fin b) × (Fin (c + 1) → Fin b))).ncard : ℝ) ≤
      2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (a + c + 2))) *
        (b : ℝ) ^ (a + c + 2) := by
  classical
  let e := Fin.appendEquiv (α := Fin b) (a + 1) (c + 1)
  have hsum (fg : (Fin (a + 1) → Fin b) × (Fin (c + 1) → Fin b)) :
      (Finset.univ.filter fun j => i ≤ (e fg j).val).card =
        lunarLevelCount i fg.1 + lunarLevelCount i fg.2 := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [← Finset.sum_boole]
    rw [Fin.sum_univ_add]
    simp [e, lunarLevelCount, Finset.sum_boole]
  let S : Set ((Fin (a + 1) → Fin b) × (Fin (c + 1) → Fin b)) :=
    {fg | d / 2 < |((lunarLevelCount i fg.1 + lunarLevelCount i fg.2 : ℕ) : ℝ) -
      ((b : ℝ) - i) * (a + c + 1) / b|}
  have hsub : e '' S ⊆ {x : Fin ((a + 1) + (c + 1)) → Fin b | d / 2 <
      |((Finset.univ.filter fun j => i ≤ (x j).val).card : ℝ) -
        ((b : ℝ) - i) * (a + c + 1) / b|} := by
    rintro x ⟨fg, hfg, rfl⟩
    change d / 2 < |((lunarLevelCount i fg.1 + lunarLevelCount i fg.2 : ℕ) : ℝ) -
      ((b : ℝ) - i) * (a + c + 1) / b| at hfg
    change d / 2 < |((Finset.univ.filter fun j => i ≤ (e fg j).val).card : ℝ) -
      ((b : ℝ) - i) * (a + c + 1) / b|
    rw [hsum]
    exact hfg
  have hp := level_fraction hb hi
  have hc : |(((a + 1) + (c + 1) : ℕ) : ℝ) * (((b : ℝ) - i) / b) -
      ((b : ℝ) - i) * (a + c + 1) / b| ≤ 1 := by
    have he : (((a + 1) + (c + 1) : ℕ) : ℝ) * (((b : ℝ) - i) / b) -
        ((b : ℝ) - i) * (a + c + 1) / b = ((b : ℝ) - i) / b := by push_cast; ring
    rw [he, abs_of_nonneg hp.1]
    exact hp.2
  have hbound := count_shift_tail (m := (a + 1) + (c + 1)) (by omega) hb hi hc hd
  have hn := Set.ncard_le_ncard hsub
  rw [Set.ncard_image_of_injective S e.injective] at hn
  have hh := (Nat.cast_le (α := ℝ).mpr hn).trans hbound
  simpa [S, show a + 1 + (c + 1) = a + c + 2 by omega] using hh

private lemma digitSeq_lt {a b : ℕ} (hb : 0 < b) (f : Fin a → Fin b) (j : ℕ) :
    digitSeq f j < b := by
  unfold digitSeq
  split_ifs with hj
  · exact (f ⟨j, hj⟩).isLt
  · exact hb

private def productDigits {b n a c : ℕ} (hb : 0 < b)
    (fg : (Fin (a + 1) → Fin b) × (Fin (c + 1) → Fin b)) : Fin (n + 1) → Fin b :=
  fun j => ⟨maxMinMul (digitSeq fg.1) (digitSeq fg.2) j, by
    apply (Finset.sup_lt_iff hb).mpr
    intro p _
    exact (min_le_left _ _).trans_lt (digitSeq_lt hb fg.1 p.1)⟩

private lemma count_products {b n i : ℕ} (hb : 0 < b) (hi : 1 ≤ i) (hib : i < b)
    {d : ℝ} (hd : 0 < d) :
    (({h : Fin (n + 1) → Fin b | ∃ f g : Fin (n + 1) → Fin b,
      maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i f + lunarLevelCount i g : ℕ) : ℝ) -
          ((b : ℝ) - i) * (n + 1) / b|} : Set (Fin (n + 1) → Fin b)).ncard : ℝ) ≤
      (n + 1) * (2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) *
        (b : ℝ) ^ (n + 2)) := by
  classical
  let S (k : Fin (n + 1)) : Set ((Fin (k.val + 1) → Fin b) ×
      (Fin (n - k.val + 1) → Fin b)) :=
    {fg | d / 2 < |((lunarLevelCount i fg.1 + lunarLevelCount i fg.2 : ℕ) : ℝ) -
      ((b : ℝ) - i) * (k.val + (n - k.val) + 1) / b|}
  let P (k : Fin (n + 1)) : Set (Fin (n + 1) → Fin b) := productDigits hb '' S k
  have hsub : {h : Fin (n + 1) → Fin b | ∃ f g : Fin (n + 1) → Fin b,
      maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i f + lunarLevelCount i g : ℕ) : ℝ) -
          ((b : ℝ) - i) * (n + 1) / b|} ⊆ ⋃ k : Fin (n + 1), P k := by
    rintro h ⟨f, g, hprod, hdev⟩
    obtain ⟨k, hk, hf, hg⟩ := factor_cutoff hprod
    let k' : Fin (n + 1) := ⟨k, by omega⟩
    let f' : Fin (k + 1) → Fin b := fun j => f (j.castLE (Nat.add_le_add_right hk 1))
    let g' : Fin (n - k + 1) → Fin b :=
      fun j => g (j.castLE (Nat.add_le_add_right (Nat.sub_le n k) 1))
    apply Set.mem_iUnion.mpr
    refine ⟨k', ⟨(f', g'), ?_, ?_⟩⟩
    · change d / 2 < |((lunarLevelCount i f' + lunarLevelCount i g' : ℕ) : ℝ) -
        ((b : ℝ) - i) * (k + (n - k) + 1) / b|
      rw [levelCount_prefix hk hi f hf, levelCount_prefix (Nat.sub_le n k) hi g hg]
      simpa [show k + (n - k) = n by omega] using hdev
    · funext j
      apply Fin.ext
      change maxMinMul (digitSeq f') (digitSeq g') j.val = (h j : ℕ)
      rw [digitSeq_prefix hk f hf, digitSeq_prefix (Nat.sub_le n k) g hg, hprod]
      simp [digitSeq, j.isLt]
  have hn := (Set.ncard_le_ncard hsub).trans (Set.ncard_iUnion_le_of_fintype P)
  have himage : ∑ k : Fin (n + 1), (P k).ncard ≤ ∑ k : Fin (n + 1), (S k).ncard :=
    Finset.sum_le_sum fun k _ => Set.ncard_image_le
  have hnat := hn.trans himage
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  simp only [Nat.cast_sum] at hreal
  refine hreal.trans ?_
  calc ∑ k : Fin (n + 1), ((S k).ncard : ℝ)
      ≤ ∑ _k : Fin (n + 1), 2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) *
          (b : ℝ) ^ (n + 2) := by
        apply Finset.sum_le_sum
        intro k _
        have hh := count_pairs (a := k.val) (c := n - k.val) hb hib hd
        have hsumN : k.val + (n - k.val) = n := by omega
        have hsumR : (k.val : ℝ) + (n - k.val : ℕ) = (n : ℝ) := by exact_mod_cast hsumN
        simpa [S, hsumN, hsumR] using hh
    _ = _ := by simp

/-- **Bound on the number of Hoeffding extremal lunar numbers.** Fix an integer $b \ge 2$. There is
a constant $C > 0$ such that for every integer $n \ge 1$ and every real $d > 0$, the set
$\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers of base $b$ and degree at most $n$
has at most $C n^2 e^{-d^2/(4(n+2))} b^n$ elements.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 24 (`jis-2025-25.2.7-lem-24`). -/
public theorem lunarHoeffdingExtremalSet_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ d : ℝ, 0 < d →
      ((lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
        C * (n : ℝ) ^ 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n
    := by
  classical
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  refine ⟨6 * Real.exp 2 * (b : ℝ) ^ 3, by positivity, ?_⟩
  intro n hn d hd
  let E (i : Fin b) : Set (Fin (n + 1) → Fin b) :=
    {h | 1 ≤ i.val ∧ (d / 2 < |(lunarLevelCount i.val h : ℝ) -
      ((b : ℝ) - i.val) * n / b| ∨
      ∃ f g : Fin (n + 1) → Fin b, maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i.val f + lunarLevelCount i.val g : ℕ) : ℝ) -
          ((b : ℝ) - i.val) * (n + 1) / b|)}
  let K : ℝ := 2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) *
    (b : ℝ) ^ (n + 1) + (n + 1) *
      (2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ (n + 2))
  have hsub : lunarHoeffdingExtremalSet b n d ⊆ ⋃ i : Fin b, E i := by
    rintro h ⟨i, hi, hib, hdev⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, by omega⟩, hi, hdev⟩
  have hE : ∀ i : Fin b, ((E i).ncard : ℝ) ≤ K := by
    intro i
    by_cases hi : 1 ≤ i.val
    · let A : Set (Fin (n + 1) → Fin b) := {h | d / 2 <
        |(lunarLevelCount i.val h : ℝ) - ((b : ℝ) - i.val) * n / b|}
      let B : Set (Fin (n + 1) → Fin b) := {h | ∃ f g : Fin (n + 1) → Fin b,
        maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
          d / 2 < |((lunarLevelCount i.val f + lunarLevelCount i.val g : ℕ) : ℝ) -
            ((b : ℝ) - i.val) * (n + 1) / b|}
      have hs : E i ⊆ A ∪ B := fun _ hh => hh.2
      have hnat := (Set.ncard_le_ncard hs).trans (Set.ncard_union_le A B)
      have hreal := Nat.cast_le (α := ℝ).mpr hnat
      calc ((E i).ncard : ℝ) ≤ ((A.ncard + B.ncard : ℕ) : ℝ) := hreal
        _ = (A.ncard : ℝ) + (B.ncard : ℝ) := Nat.cast_add _ _
        _ ≤ K := add_le_add (count_direct hb0 i.isLt hd) (count_products hb0 hi i.isLt hd)
    · have hzero : E i = ∅ := by ext h; simp [E, hi]
      rw [hzero, Set.ncard_empty, Nat.cast_zero]
      dsimp [K]
      positivity
  have hnat := (Set.ncard_le_ncard hsub).trans (Set.ncard_iUnion_le_of_fintype E)
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  simp only [Nat.cast_sum] at hreal
  have hbound : ((lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤ (b : ℝ) * K :=
    hreal.trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hE i))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb23 : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by nlinarith [sq_nonneg (b : ℝ)]
  have hn2 : (n : ℝ) + 2 ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have hcoeff : (b : ℝ) ^ 2 + (n + 1) * (b : ℝ) ^ 3 ≤
      3 * (b : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
    calc (b : ℝ) ^ 2 + (n + 1) * (b : ℝ) ^ 3
        ≤ (b : ℝ) ^ 3 + (n + 1) * (b : ℝ) ^ 3 := add_le_add hb23 le_rfl
      _ = ((n : ℝ) + 2) * (b : ℝ) ^ 3 := by ring
      _ ≤ (3 * (n : ℝ) ^ 2) * (b : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hn2 (by positivity)
      _ = _ := by ring
  have hfinal := mul_le_mul_of_nonneg_left hcoeff
    (show 0 ≤ 2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n by positivity)
  refine hbound.trans ?_
  calc (b : ℝ) * K =
      (2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n) *
        ((b : ℝ) ^ 2 + (n + 1) * (b : ℝ) ^ 3) := by
        dsimp [K]
        rw [pow_add, pow_add]
        ring
    _ ≤ (2 * Real.exp 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n) *
        (3 * (b : ℝ) ^ 3 * (n : ℝ) ^ 2) := hfinal
    _ = _ := by ring

end

end MetaMathlibExt

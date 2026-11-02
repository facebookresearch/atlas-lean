/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

open Finset BigOperators

namespace MathlibExt.Probability.McDiarmid

/-!
# McDiarmid bounded-differences
-/

/-- Product weights are nonnegative. -/
private lemma prod_weight_nonneg
    {α : Type*}
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (x : Fin n → α) :
    0 ≤ ∏ i : Fin n, p (x i) :=
  Finset.prod_nonneg fun _ _ => hp_nonneg _

/-- Product weights sum to one. -/
private lemma prod_weight_sum
    {α : Type*} [Fintype α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_sum : ∑ a : α, p a = 1) :
    ∑ x : Fin n → α, ∏ i : Fin n, p (x i) = 1 := by
  have h : (∑ x : Fin n → α, ∏ i, p (x i)) = ∏ _i : Fin n, ∑ _a : α, p _a :=
    (Fintype.prod_sum fun _ a => p a).symm
  rw [h, hp_sum, Finset.prod_const_one]

/-- Finite Hoeffding lemma: MGF bound for a bounded function under a finite distribution. -/
private lemma hoeffding_fin
    {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (g : α → ℝ) (a b : ℝ)
    (hg : ∀ x, g x ∈ Set.Icc a b)
    (s : ℝ) :
    ∑ x : α, p x * Real.exp (s * (g x - ∑ y : α, p y * g y))
      ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  by_cases hab : a ≤ b
  · classical
    let : MeasurableSpace α := ⊤
    have : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
    -- the finite distribution as a measure
    set μ : MeasureTheory.Measure α :=
      ∑ x : α, ENNReal.ofReal (p x) • MeasureTheory.Measure.dirac x with hμdef
    have hμuniv : μ Set.univ = 1 := by
      rw [hμdef, MeasureTheory.Measure.finsetSum_apply]
      simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
        Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp_nonneg x), hp_sum,
        ENNReal.ofReal_one]
    have : MeasureTheory.IsProbabilityMeasure μ := ⟨hμuniv⟩
    have hmeas : Measurable g := measurable_of_countable g
    have hb : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc a b := Filter.Eventually.of_forall hg
    -- integral against μ is the weighted sum
    have hint : ∀ F : α → ℝ, ∫ ω, F ω ∂μ = ∑ x : α, p x * F x := by
      intro F
      have hFstrong : MeasureTheory.StronglyMeasurable F :=
        (measurable_of_countable F).stronglyMeasurable
      rw [hμdef, MeasureTheory.integral_finsetSum_measure (fun i _ =>
        (MeasureTheory.integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac' _ _ hFstrong,
        ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]
    have hmean : (∫ ω, g ω ∂μ) = ∑ y : α, p y * g y := hint g
    have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hmeas.aemeasurable hb
    have hmgf := hsub.mgf_le s
    rw [hmean] at hmgf
    unfold ProbabilityTheory.mgf at hmgf
    beta_reduce at hmgf
    have houter := hint (fun ω => Real.exp (s * (g ω - ∑ y : α, p y * g y)))
    rw [houter] at hmgf
    have hcexp : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * s ^ 2 / 2 =
        s ^ 2 * (b - a) ^ 2 / 8 := by
      have hnn : ((‖b - a‖₊ : NNReal) : ℝ) = |b - a| := by simp
      rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_two, hnn, div_pow, sq_abs]
      ring
    rw [hcexp] at hmgf
    exact hmgf
  · have hab' : b < a := lt_of_not_ge hab
    obtain ⟨x0⟩ := ‹Nonempty α›
    have h0 := hg x0
    rw [Set.mem_Icc] at h0
    linarith

/-- Finite Chernoff bound: tail probability via exponential moment. -/
private lemma chernoff_fin
    {α : Type*} [Fintype α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (f : (Fin n → α) → ℝ)
    (mu t s : ℝ) (hs : 0 ≤ s) :
    ∑ x ∈ Finset.univ.filter (fun x => decide (t ≤ f x - mu)), ∏ i : Fin n, p (x i)
      ≤ Real.exp (-s * t) * ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) *
        Real.exp (s * (f x - mu)) := by
  have hw : ∀ x : Fin n → α, 0 ≤ ∏ i : Fin n, p (x i) :=
    fun x => Finset.prod_nonneg fun i _ => hp_nonneg _
  have hterm : ∀ x ∈ Finset.univ.filter (fun x => decide (t ≤ f x - mu)),
      (∏ i : Fin n, p (x i)) ≤ (∏ i : Fin n, p (x i)) *
        (Real.exp (-s * t) * Real.exp (s * (f x - mu))) := by
    intro x hx
    have hxt : t ≤ f x - mu := of_decide_eq_true (Finset.mem_filter.mp hx).2
    have hexp : 1 ≤ Real.exp (-s * t) * Real.exp (s * (f x - mu)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp_of_le
      have : 0 ≤ s * ((f x - mu) - t) := mul_nonneg hs (sub_nonneg.mpr hxt)
      linarith
    calc (∏ i : Fin n, p (x i)) = (∏ i : Fin n, p (x i)) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (hw x)
  calc ∑ x ∈ Finset.univ.filter (fun x => decide (t ≤ f x - mu)), ∏ i : Fin n, p (x i)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => decide (t ≤ f x - mu)),
        (∏ i : Fin n, p (x i)) * (Real.exp (-s * t) * Real.exp (s * (f x - mu))) :=
        Finset.sum_le_sum hterm
    _ = ∑ x ∈ Finset.univ.filter (fun x => decide (t ≤ f x - mu)),
        Real.exp (-s * t) * ((∏ i : Fin n, p (x i)) * Real.exp (s * (f x - mu))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = Real.exp (-s * t) * ∑ x ∈ Finset.univ.filter
        (fun x => decide (t ≤ f x - mu)), (∏ i : Fin n, p (x i)) *
        Real.exp (s * (f x - mu)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-s * t) * ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) *
        Real.exp (s * (f x - mu)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.sum_le_univ_sum_of_nonneg fun x =>
          mul_nonneg (hw x) (Real.exp_pos _).le

/-- MGF bound for bounded-differences functions: the core of McDiarmid. -/
private lemma mgf_bound
    {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1) :
    ∀ (n : ℕ) (f : (Fin n → α) → ℝ) (c : Fin n → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ (i : Fin n) (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) →
    ∀ s : ℝ, ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) *
      Real.exp (s * (f x - ∑ y : Fin n → α, (∏ i : Fin n, p (y i)) * f y))
      ≤ Real.exp (s ^ 2 * (∑ i : Fin n, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro f c _ _ s
    have : Unique (Fin 0 → α) :=
      { default := fun i => i.elim0
        uniq := fun x => funext fun i => i.elim0 }
    simp only [Fintype.sum_unique]
    simp
  | succ n ih =>
    intro f c hc_nonneg hbd s
    -- splitting a sum over `Fin (n+1) → α` by the first coordinate
    have hsplit : ∀ F : (Fin (n + 1) → α) → ℝ,
        (∑ x : Fin (n + 1) → α, F x)
          = ∑ a : α, ∑ y : Fin n → α, F (Fin.cons a y) := by
      intro F
      have hbij : Function.Bijective (fun q : α × (Fin n → α) =>
          Fin.cons (α := fun _ => α) q.1 q.2) := by
        refine ⟨?_, ?_⟩
        · intro q1 q2 h
          obtain ⟨a1, y1⟩ := q1
          obtain ⟨a2, y2⟩ := q2
          have h0 : a1 = a2 := by
            have h0 := congrArg (fun x => x 0) h
            simpa using h0
          have h1 : y1 = y2 := by
            have h1 := congrArg Fin.tail h
            simpa using h1
          subst h0
          subst h1
          rfl
        · intro x
          exact ⟨(x 0, Fin.tail x), Fin.cons_self_tail x⟩
      rw [(Fintype.sum_bijective _ hbij _ _ (fun q => rfl)).symm, Fintype.sum_prod_type]
    -- weights split off the first coordinate
    have hwgt : ∀ (a : α) (y : Fin n → α),
        (∏ i : Fin (n + 1), p ((Fin.cons (α := fun _ => α) a y) i))
          = p a * ∏ i : Fin n, p (y i) := by
      intro a y
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    -- the total mean splits over slices
    have hmean_split : (∑ x : Fin (n + 1) → α, (∏ i, p (x i)) * f x)
        = ∑ a : α, p a * (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y)) := by
      rw [hsplit]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hwgt]
      ring
    -- induction hypothesis on each slice
    have hIH : ∀ a : α, (∑ y : Fin n → α, (∏ i, p (y i)) *
        Real.exp (s * (f (Fin.cons a y) -
          ∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))))
        ≤ Real.exp (s ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8) := by
      intro a
      refine ih (fun y => f (Fin.cons a y)) (fun i => c i.succ) ?_ ?_ s
      · intro i
        exact hc_nonneg _
      · intro i x' y' hxy
        apply hbd (i.succ)
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp
        · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
          rw [Fin.cons_succ, Fin.cons_succ]
          apply hxy
          intro hk
          apply hj
          rw [hk]
    -- slice means differ by at most `c 0`
    have hslice : ∀ a b : α,
        |(∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y))
          - (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons b y))| ≤ c 0 := by
      intro a b
      have hdiff : (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y))
          - (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons b y))
          = ∑ y : Fin n → α, (∏ i, p (y i)) * (f (Fin.cons a y) - f (Fin.cons b y)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [hdiff]
      calc |∑ y : Fin n → α, (∏ i, p (y i)) * (f (Fin.cons a y) - f (Fin.cons b y))|
          ≤ ∑ y : Fin n → α, |(∏ i, p (y i)) * (f (Fin.cons a y) - f (Fin.cons b y))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ y : Fin n → α, (∏ i, p (y i)) * |f (Fin.cons a y) - f (Fin.cons b y)| := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hp_nonneg _)]
        _ ≤ ∑ y : Fin n → α, (∏ i, p (y i)) * c 0 := by
            refine Finset.sum_le_sum fun y _ => ?_
            apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hp_nonneg _)
            apply hbd 0
            intro j hj
            by_cases hj0 : j = 0
            · subst hj0
              exact absurd rfl hj
            · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj0
              simp only [Fin.cons_succ]
        _ = c 0 := by
            rw [← Finset.sum_mul, prod_weight_sum p hp_sum, one_mul]
    -- minimizer of slice means, giving an interval of length `c 0`
    have hstar : ∃ a_star : α, ∀ a : α,
        (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a_star y))
          ≤ (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y)) := by
      obtain ⟨a0⟩ := ‹Nonempty α›
      have hne : (Finset.univ.image
          (fun a => ∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y))).Nonempty := by
        refine ⟨_, Finset.mem_image.mpr ⟨a0, Finset.mem_univ a0, rfl⟩⟩
      obtain ⟨a_star, _, hstar_eq⟩ := Finset.mem_image.mp
        (Finset.min'_mem _ hne)
      refine ⟨a_star, fun a => ?_⟩
      rw [hstar_eq]
      exact Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    obtain ⟨a_star, hstar⟩ := hstar
    have hmem : ∀ a : α, (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y)) ∈
        Set.Icc (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a_star y))
          ((∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a_star y)) + c 0) := by
      intro a
      rw [Set.mem_Icc]
      refine ⟨hstar a, ?_⟩
      have h := hslice a a_star
      rw [abs_le] at h
      linarith
    -- outer Hoeffding bound over slices
    have houter : (∑ a : α, p a * Real.exp (s *
        ((∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y))
          - ∑ a' : α, p a' * (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a' y)))))
        ≤ Real.exp (s ^ 2 * (c 0) ^ 2 / 8) := by
      have h := hoeffding_fin p hp_nonneg hp_sum
        (fun a => ∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a y))
        _ _ hmem s
      have hba : ((∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a_star y)) + c 0)
          - (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a_star y)) = c 0 := by ring
      rw [hba] at h
      exact h
    -- factoring the exponential across slice mean and slice fluctuation
    have hexpfac : ∀ (a : α) (y : Fin n → α) (MU : ℝ),
        Real.exp (s * (f (Fin.cons a y) - MU))
        = Real.exp (s * (f (Fin.cons a y) -
            (∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))))
          * Real.exp (s * ((∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z)) - MU)) := by
      intro a y MU
      rw [← Real.exp_add]
      congr 1
      ring
    have hinner : ∀ (a : α) (MU : ℝ),
        (∑ y : Fin n → α, (∏ i : Fin (n + 1), p ((Fin.cons (α := fun _ => α) a y) i)) *
          Real.exp (s * (f (Fin.cons a y) - MU)))
        = (p a * Real.exp (s *
            ((∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z)) - MU)))
          * (∑ y : Fin n → α, (∏ i, p (y i)) *
            Real.exp (s * (f (Fin.cons a y) -
              (∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))))) := by
      intro a MU
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hwgt a y, hexpfac a y MU]
      ring
    rw [hsplit, hmean_split]
    simp only [hinner]
    calc (∑ a : α, (p a * Real.exp (s *
            ((∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))
              - ∑ a' : α, p a' * (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a' y)))))
          * (∑ y : Fin n → α, (∏ i, p (y i)) *
            Real.exp (s * (f (Fin.cons a y) -
              (∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))))))
        ≤ (∑ a : α, (p a * Real.exp (s *
            ((∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))
              - ∑ a' : α, p a' * (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a' y)))))
          * Real.exp (s ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          apply mul_le_mul_of_nonneg_left (hIH a) _
          apply mul_nonneg (hp_nonneg a) (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8) *
          (∑ a : α, p a * Real.exp (s *
            ((∑ z : Fin n → α, (∏ i, p (z i)) * f (Fin.cons a z))
              - ∑ a' : α, p a' * (∑ y : Fin n → α, (∏ i, p (y i)) * f (Fin.cons a' y))))) := by
          conv_rhs => rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ ≤ Real.exp (s ^ 2 * (∑ i : Fin n, (c i.succ) ^ 2) / 8) *
          Real.exp (s ^ 2 * (c 0) ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left houter (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 * (∑ i : Fin (n + 1), c i ^ 2) / 8) := by
          rw [← Real.exp_add]
          congr 1
          have hS : (∑ i : Fin (n + 1), c i ^ 2)
              = (c 0) ^ 2 + ∑ i : Fin n, (c i.succ) ^ 2 := Fin.sum_univ_succ _
          rw [hS]
          ring

/-- **McDiarmid's inequality when the sensitivities are not all zero.** Let $n \in \mathbb{N}$,
let $\alpha$ be a finite nonempty set with weights $p : \alpha \to \mathbb{R}$ such that
$p(a) \ge 0$ for all $a$ and $\sum_{a \in \alpha} p(a) = 1$, and give each $x \in \alpha^n$ the
product weight $P(x) = \prod_{i<n} p(x_i)$. Let $f : \alpha^n \to \mathbb{R}$ and let
$c_0, \dots, c_{n-1} \ge 0$ be such that $|f(x) - f(y)| \le c_i$ whenever $x, y \in \alpha^n$
agree in every coordinate other than $i$, and suppose $\sum_{i<n} c_i^2 > 0$. Write
$\mu = \sum_{x \in \alpha^n} P(x) f(x)$ for the mean of $f$. Then for every real $t > 0$,
$$
\sum_{x \in \alpha^n,\ f(x) - \mu \ge t} P(x) \le \exp\Big(-\frac{2t^2}{\sum_{i<n} c_i^2}\Big).
$$
-/
theorem mcdiarmid_one_sided_finite_iid_general
    {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ)
    (c : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < ∑ i : Fin n, c i ^ 2)
    (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    let mu : ℝ := ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * f x
    let prob : ℝ :=
      ∑ x ∈ (Finset.univ.filter fun x => decide (t ≤ f x - mu)),
        ∏ i : Fin n, p (x i)
    prob ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  intro mu prob
  have hs_nonneg : 0 ≤ 4 * t / ∑ i : Fin n, c i ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) ht.le) hc_pos.le
  have hcher := chernoff_fin p hp_nonneg f mu t (4 * t / ∑ i : Fin n, c i ^ 2) hs_nonneg
  have hmgf := mgf_bound p hp_nonneg hp_sum n f c hc_nonneg hbd
    (4 * t / ∑ i : Fin n, c i ^ 2)
  calc prob ≤ Real.exp (-(4 * t / ∑ i : Fin n, c i ^ 2) * t) *
        Real.exp ((4 * t / ∑ i : Fin n, c i ^ 2) ^ 2 * (∑ i : Fin n, c i ^ 2) / 8) :=
        hcher.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
    _ = Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
        have hS := hc_pos.ne'
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring

/-- **The upper tail vanishes when every sensitivity is zero.** Let $n \in \mathbb{N}$, let
$\alpha$ be a finite nonempty set with weights $p : \alpha \to \mathbb{R}$ such that
$p(a) \ge 0$ for all $a$ and $\sum_{a \in \alpha} p(a) = 1$, and give each $x \in \alpha^n$ the
product weight $P(x) = \prod_{i<n} p(x_i)$. Let $f : \alpha^n \to \mathbb{R}$ and let
$c_0, \dots, c_{n-1} \ge 0$ be such that $|f(x) - f(y)| \le c_i$ whenever $x, y \in \alpha^n$
agree in every coordinate other than $i$, and suppose $\sum_{i<n} c_i^2 = 0$. Write
$\mu = \sum_{x \in \alpha^n} P(x) f(x)$ for the mean of $f$. Then for every real $t > 0$,
$$
\sum_{x \in \alpha^n,\ f(x) - \mu \ge t} P(x) = 0.
$$

Indeed, changing one coordinate never changes $f$, so the upper tail is empty. -/
theorem mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero
    {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ)
    (c : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_zero : ∑ i : Fin n, c i ^ 2 = 0)
    (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    let mu : ℝ := ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * f x
    let prob : ℝ :=
      ∑ x ∈ (Finset.univ.filter fun x => decide (t ≤ f x - mu)),
        ∏ i : Fin n, p (x i)
    prob = 0 := by
  intro mu prob
  have hle : ∀ s : ℝ, 0 ≤ s → prob ≤ Real.exp (-s * t) := by
    intro s hs
    have h := (chernoff_fin p hp_nonneg f mu t s hs).trans (mul_le_mul_of_nonneg_left
      (mgf_bound p hp_nonneg hp_sum n f c hc_nonneg hbd s) (Real.exp_pos _).le)
    rwa [hc_zero, mul_zero, zero_div, Real.exp_zero, mul_one] at h
  have htend : Filter.Tendsto (fun s : ℝ => Real.exp (-s * t)) Filter.atTop (nhds 0) := by
    simpa only [neg_mul, Function.comp_def, id] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.atTop_mul_const ht)
  exact le_antisymm (ge_of_tendsto htend ((Filter.eventually_ge_atTop 0).mono hle))
    (Finset.sum_nonneg fun x _ => prod_weight_nonneg p hp_nonneg x)

set_option linter.unusedDecidableInType false in
/--
**McDiarmid's bounded-differences inequality, finite i.i.d. case.** Let $n \in \mathbb{N}$, let
$\alpha$ be a finite nonempty set with weights $p : \alpha \to \mathbb{R}$ such that
$p(a) \ge 0$ for all $a$ and $\sum_{a \in \alpha} p(a) = 1$, and give each $x \in \alpha^n$ the
product weight $P(x) = \prod_{i<n} p(x_i)$. Let $f : \alpha^n \to \mathbb{R}$ and let
$c_0, \dots, c_{n-1} \ge 0$ be such that $|f(x) - f(y)| \le c_i$ whenever $x, y \in \alpha^n$
agree in every coordinate other than $i$. Write $\mu = \sum_{x \in \alpha^n} P(x) f(x)$ for the
mean of $f$. Then for every real $t > 0$,
$$
\sum_{x \in \alpha^n,\ f(x) - \mu \ge t} P(x) \le \exp\Big(-\frac{2t^2}{\sum_{i<n} c_i^2}\Big),
$$
where a quotient by $0$ is read as $0$, so the bound is $1$ when every $c_i$ is $0$.

Source: C. McDiarmid, Surveys in Combinatorics 1989, 148-188, DOI 10.1017/CBO9781107359949.008.
When every `c i` is `0` (including `n = 0`), the right-hand side is `Real.exp 0 = 1` by Lean's
convention `x / 0 = 0`; `mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero` gives the sharp value
`prob = 0` there, and `mcdiarmid_one_sided_finite_iid_general` covers `0 < ∑ i, c i ^ 2`. The
instance `[DecidableEq α]` is unused and keeps the source's shape.
Proves `Wanted` entry `mcdiarmid_one_sided_finite_iid`.
-/
theorem mcdiarmid_one_sided_finite_iid
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ)
    (c : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (t : ℝ) (ht : 0 < t)
    (hbd : ∀ (i : Fin n) (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i) :
    let mu : ℝ := ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * f x
    let prob : ℝ :=
      ∑ x ∈ (Finset.univ.filter fun x => decide (t ≤ f x - mu)),
        ∏ i : Fin n, p (x i)
    prob ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  intro mu prob
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (c i)).eq_or_lt with hS | hS
  · exact (mcdiarmid_one_sided_finite_iid_of_sum_sq_eq_zero p hp_nonneg hp_sum f c hc_nonneg
      hS.symm t ht hbd).le.trans (Real.exp_pos _).le
  · exact mcdiarmid_one_sided_finite_iid_general p hp_nonneg hp_sum f c hc_nonneg hS t ht hbd

end MathlibExt.Probability.McDiarmid

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteSanov
public import MathlibExt.InformationTheory.LogSum
public import Mathlib.Analysis.SpecificLimits.Basic

open MathlibExt.InformationTheory.MethodOfTypes Finset Real Filter Topology

/-- The law on `Bool` giving `true` probability `a`. -/
noncomputable def bern (a : ℝ) (b : Bool) : ℝ := if b then a else 1 - a

/-- Gibbs' inequality on `Bool`, from the repository's log-sum inequality: the rate hypothesis of
the Sanov theorems holds with `r = 0` against any strictly positive law. -/
theorem gibbs_bool {Q : Bool → ℝ} (hQ : ∀ b, 0 < Q b) (hQ1 : ∑ b, Q b = 1) (P : Bool → ℝ)
    (hP0 : ∀ a, 0 ≤ P a) (hP1 : ∑ a, P a = 1) : 0 ≤ ∑ a, P a * log (P a / Q a) := by
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div univ P Q
    (fun i _ => hP0 i) (fun i _ => hQ i)
  rw [hP1, hQ1, div_one, log_one, mul_zero] at h
  exact h

/-- Non-vacuity of the non-asymptotic upper bound: `Γ` = all probability vectors on `Bool`,
`Q` uniform, `r = 0`. -/
example (n : ℕ) (hn : n ≠ 0)
    [DecidablePred (· ∈ {P : Bool → ℝ | (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1})] :
    iidProb (fun _ : Bool => (1 / 2 : ℝ))
        (univ.filter fun x : Fin n → Bool =>
          empirical (seqType x) ∈ {P : Bool → ℝ | (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1}) ≤
      ((n : ℝ) + 1) ^ Fintype.card Bool * exp (-(n : ℝ) * 0) :=
  iidProb_empirical_mem_le hn (Q := fun _ : Bool => (1 / 2 : ℝ)) (fun _ => by norm_num)
    _ (r := 0) (fun P _ hP0 hP1 _ => gibbs_bool (fun _ => by norm_num) (by norm_num) P hP0 hP1)

/-- `⌊a n⌋₊ ≤ n` for `a ≤ 1`. -/
theorem floor_mul_le (a : ℝ) (ha1 : a ≤ 1) (n : ℕ) : ⌊a * n⌋₊ ≤ n :=
  Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg n) ha1)

/-- The `n`-type over `Bool` with `⌊a n⌋₊` letters `true`. -/
noncomputable def floorType (a : ℝ) (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : Sym Bool n :=
  ⟨Multiset.replicate ⌊a * n⌋₊ true + Multiset.replicate (n - ⌊a * n⌋₊) false, by
    have := floor_mul_le a ha1 n
    simp only [Multiset.card_add, Multiset.card_replicate]; omega⟩

/-- Empirical frequency of `true` in a floor type. -/
theorem empirical_floorType_true (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    empirical (floorType a ha0 ha1 n) true = (⌊a * n⌋₊ : ℝ) / n := by
  simp [empirical, floorType, Multiset.count_replicate]

/-- Empirical frequency of `false` in a floor type. -/
theorem empirical_floorType_false (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    empirical (floorType a ha0 ha1 n) false = 1 - (⌊a * n⌋₊ : ℝ) / n := by
  have hle := floor_mul_le a ha1 n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : ((floorType a ha0 ha1 n : Sym Bool n) : Multiset Bool).count false =
      n - ⌊a * n⌋₊ := by
    simp [floorType, Multiset.count_replicate]
  rw [empirical, hc, Nat.cast_sub hle]; field_simp

/-- `p ↦ p log (p / q)` is continuous for `q > 0`. -/
theorem continuous_mul_log_div {q : ℝ} (hq : 0 < q) : Continuous fun p : ℝ => p * log (p / q) := by
  have : (fun p : ℝ => p * log (p / q)) = fun p => p * log p - p * log q := by
    funext p
    by_cases h : p = 0
    · simp [h]
    · rw [log_div h hq.ne']; ring
  rw [this]
  exact continuous_mul_log.sub (continuous_id.mul continuous_const)

/-- The divergence of the floor types from `bern a` tends to `0`. -/
theorem tendsto_div_floorType (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => ∑ b, empirical (floorType a ha0.le ha1.le n) b *
      log (empirical (floorType a ha0.le ha1.le n) b / bern a b)) atTop (𝓝 0) := by
  have hT : Tendsto (fun n : ℕ => (⌊a * n⌋₊ : ℝ) / n) atTop (𝓝 a) :=
    (tendsto_nat_floor_mul_div_atTop ha0.le).comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun n : ℕ => empirical (floorType a ha0.le ha1.le n) false) atTop
      (𝓝 (1 - a)) := by
    refine (tendsto_const_nhds.sub hT).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (empirical_floorType_false a ha0.le ha1.le hn.ne').symm
  have hTr : Tendsto (fun n : ℕ => empirical (floorType a ha0.le ha1.le n) true) atTop (𝓝 a) :=
    hT.congr fun n => (empirical_floorType_true a ha0.le ha1.le n).symm
  have h1 := ((continuous_mul_log_div ha0).tendsto a).comp hTr
  have h2 := ((continuous_mul_log_div (by linarith : (0 : ℝ) < 1 - a)).tendsto (1 - a)).comp hF
  have := h1.add h2
  simp only [div_self ha0.ne', div_self (by linarith : (1 - a) ≠ 0), log_one, mul_zero,
    add_zero] at this
  refine this.congr fun n => ?_
  simp [bern, add_comm]

/-- The review's set `Γ = {P : P(true) ∈ [2/5, 9/20]}` contains no `1`-type and no `2`-type, so it
violates "an `n`-type in `Γ` for every `n ≥ 1`" while satisfying (III.21). The limit theorem, with
its eventual hypotheses, applies to it: with `Q = bern (9/20)` and the floor types,
`(1/n) log Pr(P̂ₙ ∈ Γ) → 0`. -/
example [DecidablePred (· ∈ {P : Bool → ℝ | P true ∈ Set.Icc (2 / 5 : ℝ) (9 / 20)})] :
    Tendsto (fun n : ℕ =>
      log (iidProb (bern (9 / 20)) (univ.filter fun x : Fin n → Bool =>
        empirical (seqType x) ∈ {P : Bool → ℝ | P true ∈ Set.Icc (2 / 5 : ℝ) (9 / 20)})) / n)
      atTop (𝓝 (-0)) := by
  have hQ : ∀ b, 0 < bern (9 / 20) b := fun b => by cases b <;> norm_num [bern]
  have hQ1 : ∑ b, bern (9 / 20) b = 1 := by norm_num [bern]
  refine tendsto_log_iidProb_empirical_mem_div (fun b => (hQ b).le) (r := 0)
    (fun P _ hP0 hP1 _ => gibbs_bool hQ hQ1 P hP0 hP1)
    (floorType (9 / 20) (by norm_num) (by norm_num)) ?_ (Eventually.of_forall fun _ a _ => hQ a)
    (tendsto_div_floorType (9 / 20) (by norm_num) (by norm_num))
  filter_upwards [eventually_ge_atTop 20] with n hn
  have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  simp only [empirical_floorType_true, Set.mem_Icc]
  have hfl := Nat.floor_le (by positivity : (0 : ℝ) ≤ 9 / 20 * n)
  have hlt := Nat.sub_one_lt_floor (9 / 20 * (n : ℝ))
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- A second instance with all hypotheses jointly satisfied: `Q` uniform, `Γ` all probability
vectors, the floor types with `⌊n/2⌋` letters `true`; here `D(P̂ₙ ‖ Q) → 0 = D(Γ ‖ Q)`. -/
example [DecidablePred (· ∈ {P : Bool → ℝ | (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1})] :
    Tendsto (fun n : ℕ =>
      log (iidProb (bern (1 / 2)) (univ.filter fun x : Fin n → Bool =>
        empirical (seqType x) ∈ {P : Bool → ℝ | (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1})) / n)
      atTop (𝓝 (-0)) := by
  have hQ : ∀ b, 0 < bern (1 / 2) b := fun b => by cases b <;> norm_num [bern]
  have hQ1 : ∑ b, bern (1 / 2) b = 1 := by norm_num [bern]
  refine tendsto_log_iidProb_empirical_mem_div (fun b => (hQ b).le) (r := 0)
    (fun P _ hP0 hP1 _ => gibbs_bool hQ hQ1 P hP0 hP1)
    (floorType (1 / 2) (by norm_num) (by norm_num)) ?_ (Eventually.of_forall fun _ a _ => hQ a)
    (tendsto_div_floorType (1 / 2) (by norm_num) (by norm_num))
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ⟨empirical_nonneg _, sum_empirical hn.ne' _⟩

/-- One letter of Gibbs' inequality with its equality case: for `p ≥ 0` and `q > 0`,
`p log (p / q) - (p - q) ≥ 0`, with equality only at `p = q`. -/
theorem gibbs_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * log (p / q) - (p - q) ∧ (p * log (p / q) - (p - q) = 0 → p = q) := by
  rcases hp.eq_or_lt with rfl | hp'
  · refine ⟨by simp [hq.le], fun h => ?_⟩
    simp at h; linarith
  have hx : 0 < q / p := div_pos hq hp'
  have key : p * log (p / q) - (p - q) = p * (q / p - 1 - log (q / p)) := by
    rw [log_div hq.ne' hp'.ne', log_div hp'.ne' hq.ne']; field_simp; ring
  rw [key]
  refine ⟨mul_nonneg hp'.le (by linarith [log_le_sub_one_of_pos hx]), fun h => ?_⟩
  by_contra hne
  have hx1 : q / p ≠ 1 := fun h1 => hne (by field_simp at h1; linarith)
  have := log_lt_sub_one_of_pos hx hx1
  have : 0 < p * (q / p - 1 - log (q / p)) := mul_pos hp' (by linarith)
  linarith

/-- The equality case of Gibbs' inequality on `Bool`: a distribution at divergence `0` from a
strictly positive law is that law. -/
theorem eq_of_div_eq_zero {Q P : Bool → ℝ} (hQ : ∀ b, 0 < Q b) (hQ1 : ∑ b, Q b = 1)
    (hP0 : ∀ a, 0 ≤ P a) (hP1 : ∑ a, P a = 1) (h : ∑ a, P a * log (P a / Q a) = 0) : P = Q := by
  have hsum : ∑ a, (P a * log (P a / Q a) - (P a - Q a)) = 0 := by
    rw [Finset.sum_sub_distrib, h, Finset.sum_sub_distrib, hP1, hQ1]; ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => (gibbs_term (hP0 a) (hQ a)).1).mp hsum
  funext a
  exact (gibbs_term (hP0 a) (hQ a)).2 (hz a (Finset.mem_univ a))

/-- Non-vacuity of the wanted Gibbs conditioning principle
(`GibbsConditioningWanted.tendsto_iidProb_prefix_div_iidProb`): all its hypotheses hold for `Q`
uniform on `Bool`, `Γ` all probability vectors, `r = 0`, the floor types with `⌊n/2⌋` letters
`true`, and `P* = Q`. -/
example : let Q := bern (1 / 2); let Γ := {P : Bool → ℝ | (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1}
    (∀ a, 0 < Q a) ∧ ∑ a, Q a = 1 ∧ (∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1) ∧
      (∀ P ∈ Γ, (0 : ℝ) ≤ ∑ a, P a * log (P a / Q a)) ∧
      (∀ᶠ n in atTop, empirical (floorType (1 / 2) (by norm_num) (by norm_num) n) ∈ Γ) ∧
      Tendsto (fun n => ∑ a, empirical (floorType (1 / 2) (by norm_num) (by norm_num) n) a *
        log (empirical (floorType (1 / 2) (by norm_num) (by norm_num) n) a / Q a)) atTop (𝓝 0) ∧
      Q ∈ closure Γ ∧ ∑ a, Q a * log (Q a / Q a) = 0 ∧
      (∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = 0 → P = Q) := by
  intro Q Γ
  have hQ : ∀ b, 0 < Q b := fun b => by cases b <;> norm_num [Q, bern]
  have hQ1 : ∑ b, Q b = 1 := by norm_num [Q, bern]
  have hclosed : IsClosed Γ := by
    have h1 : IsClosed {R : Bool → ℝ | ∀ a, 0 ≤ R a} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)
    have h2 : IsClosed {R : Bool → ℝ | ∑ a, R a = 1} :=
      isClosed_eq (continuous_finsetSum _ fun a _ => continuous_apply a) continuous_const
    exact h1.inter h2
  refine ⟨hQ, hQ1, fun P hP => hP, fun P hP => gibbs_bool hQ hQ1 P hP.1 hP.2, ?_,
    tendsto_div_floorType (1 / 2) (by norm_num) (by norm_num),
    subset_closure ⟨fun b => (hQ b).le, hQ1⟩, by simp [fun b => (hQ b).ne'], ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨empirical_nonneg _, sum_empirical hn.ne' _⟩
  · intro P hP hD
    rw [hclosed.closure_eq] at hP
    exact eq_of_div_eq_zero hQ hQ1 hP.1 hP.2 hD

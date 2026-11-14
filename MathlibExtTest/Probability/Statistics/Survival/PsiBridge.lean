/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.PsiBridge
import Mathlib.Tactic

/-!
# Tests for the Ψ bridge

* **Two jumps, from the definitions**: the product integral of an integrator with jumps `1/2` at
  `1` and `-1/3` at `2` over `(0, 3]` is computed from T77's multiplicativity and one-jump
  formula alone, and agrees with `productIntegral_pureJumpFun`: `(1 + 1/2)(1 - 1/3) = 1`.
* **One jump**: `productIntegral_pureJumpFun` with a single jump gives T77's
  `productIntegral_step`.
* **Continuity of `Ψ` in `B` fails without a total-variation bound, and the bridge is not
  claimed**: on the domain of all integrators of bounded variation in `ℓ^∞([0, 3])`, the
  integrators `B_n` with `2 (n + 1)²` alternating jumps `±1/(n + 1)` in `(1, 2)` have sup norm at
  most `1/(n + 1)`, but every `Ψ` given by the two-tag sums has
  `Ψ(0, B_n) 𝟙[1, 3] (3) = (1 - 1/(n + 1)²)^((n + 1)²) ≤ 1/2`, while `Ψ(0, 0) 𝟙[1, 3] (3) = 1`.
  So `B ↦ Ψ(0, B) 𝟙[1, 3]` is not continuous at `0` (`not_tendsto_psi`), and T78's
  `IsStieltjesProductIntegral` fails there for every such `Ψ` and every `P`
  (`not_isStieltjesProductIntegral`; its hypothesis is only the two-tag-sum limit for
  `h = 𝟙[1, 3]` at `A = 0`, which is satisfiable: `psiSum_stepOne_eventually` shows the sums are
  eventually `P(B)(1, 3]`). The bridge's hypotheses `IsPsiOperator` fail there too
  (`not_isPsiOperator`): this domain is closed under `freeze`, so what fails is the uniform bound
  `norm_le`.
* **Consistency of the hypotheses**: at the degenerate horizon `τ = 0` (as in T78's test file) the
  zero operator satisfies `IsPsiOperator`, and the bridge yields an instance of
  `IsStieltjesProductIntegral` for T77's product integral.
-/

@[expose] public section

open Filter Topology Finset
open MathlibExt.Analysis.StieltjesProductIntegral
open MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
open MathlibExt.Probability.Statistics.ContinuousProductIntegral
open MathlibExt.Probability.Statistics.Survival.PsiBridge
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.Survival.PsiBridge

/-! ### Two jumps, computed from the definitions -/

/-- Jumps `1/2` at `1` and `-1/3` at `2`. -/
noncomputable def twoJump (x : ℝ) : ℝ :=
  (if 1 ≤ x then 1 / 2 else 0) + (if 2 ≤ x then -1 / 3 else 0)

theorem twoJump_eq (x : ℝ) :
    pureJumpFun (range 2) (fun j : ℕ => (j : ℝ) + 1) (fun j => if j = 0 then 1 / 2 else -1 / 3) x =
      twoJump x := by
  simp only [pureJumpFun, sum_filter, sum_range_succ, sum_range_zero, twoJump]
  norm_num

theorem isControl_twoJump : IsControl twoJump
    (pureJumpFun (range 2) (fun j : ℕ => (j : ℝ) + 1)
      (fun j => |if j = 0 then (1 / 2 : ℝ) else -1 / 3|)) 0 3 :=
  isControl_of_eqOn (isControl_pureJumpFun _ _ _ 0 3) fun x _ => twoJump_eq x

/-- **The two-jump product integral from T77's definitions**: multiplicativity at `3/2`
(`productIntegral_mul`) and the one-jump formula `productIntegral_step` on each half give
`(1 + 1/2) (1 - 1/3) = 1`. `productIntegral_pureJumpFun` is not used. -/
theorem productIntegral_twoJump : productIntegral twoJump 0 3 = 1 := by
  rw [productIntegral_mul (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num) isControl_twoJump]
  have h₁ : ∀ x ∈ Set.Icc (0 : ℝ) (3 / 2),
      twoJump x = (fun t : ℝ => if 1 ≤ t then (1 / 2 : ℝ) else 0) x := by
    intro x hx
    simp only [twoJump]
    split_ifs <;> (try norm_num) <;> linarith [hx.1, hx.2]
  have h₂ : ∀ x ∈ Set.Icc (3 / 2 : ℝ) 3,
      twoJump x = (fun t : ℝ => if 2 ≤ t then (1 / 2 + -1 / 3 : ℝ) else 1 / 2) x := by
    intro x hx
    simp only [twoJump]
    split_ifs <;> (try norm_num) <;> linarith [hx.1, hx.2]
  rw [productIntegral_congr (by norm_num) h₁, productIntegral_step (by norm_num) (by norm_num),
    productIntegral_congr (by norm_num) h₂, productIntegral_step (by norm_num) (by norm_num)]
  norm_num

/-- The multi-jump theorem gives the same value. -/
theorem productIntegral_twoJump_pureJump :
    productIntegral twoJump 0 3 = (1 + 1 / 2) * (1 - 1 / 3) := by
  have hcongr : ∀ x ∈ Set.Icc (0 : ℝ) 3, twoJump x =
      pureJumpFun (range 2) (fun j : ℕ => (j : ℝ) + 1)
        (fun j => if j = 0 then 1 / 2 else -1 / 3) x := fun x _ => (twoJump_eq x).symm
  rw [productIntegral_congr (by norm_num) hcongr,
    productIntegral_pureJumpFun _ _ _ (fun i _ j _ h => by simpa using h) (by norm_num)]
  rw [filter_true_of_mem fun j hj => by
    simp only [mem_range] at hj
    interval_cases j <;> norm_num]
  simp only [prod_range_succ, prod_range_zero]
  norm_num

example : (1 + 1 / 2 : ℝ) * (1 - 1 / 3) = 1 := by norm_num

/-! ### One jump: T77's `productIntegral_step` -/

theorem pureJumpFun_one (c J : ℝ) :
    pureJumpFun (range 1) (fun _ => c) (fun _ => J) = fun t => if c ≤ t then J else 0 := by
  funext t
  rw [pureJumpFun, sum_filter, sum_range_one]

/-- With one jump, `productIntegral_pureJumpFun` gives `1 + J`. -/
theorem productIntegral_one_jump {c J lo hi : ℝ} (hlc : lo < c) (hch : c ≤ hi) :
    productIntegral (fun t => if c ≤ t then J else 0) lo hi = 1 + J := by
  rw [← pureJumpFun_one, productIntegral_pureJumpFun _ _ _
    (fun i hi j hj _ => by simp only [coe_range, Set.mem_Iio] at hi hj; omega) (hlc.le.trans hch),
    filter_true_of_mem fun _ _ => ⟨hlc, hch⟩, prod_range_one]

/-- T77's one-jump formula for the same integrator: the two agree. -/
example {c J lo hi : ℝ} (hlc : lo < c) (hch : c ≤ hi) :
    productIntegral (fun t => if c ≤ t then J else 0) lo hi = 1 + (J - 0) :=
  productIntegral_step hlc hch

example {c J lo hi : ℝ} (hlc : lo < c) (hch : c ≤ hi) :
    (1 : ℝ) + J = 1 + (J - 0) := by
  rw [← productIntegral_one_jump (J := J) hlc hch, productIntegral_step hlc hch]

/-! ### Continuity of `Ψ` in `B` fails without a total-variation bound -/

local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

theorem sum_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (2 * m), f j = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

theorem prod_range_two_mul (f : ℕ → ℝ) (m : ℕ) :
    ∏ j ∈ range (2 * m), f j = ∏ i ∈ range m, (f (2 * i) * f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ]
    ring

/-- Alternating jumps `ε, -ε, ε, -ε, …`. -/
noncomputable def alt (ε : ℝ) (j : ℕ) : ℝ :=
  if Even j then ε else -ε

theorem alt_even (ε : ℝ) (i : ℕ) : alt ε (2 * i) = ε := by
  simp only [alt, even_two_mul, ↓reduceIte]

theorem alt_odd (ε : ℝ) (i : ℕ) : alt ε (2 * i + 1) = -ε := by
  simp only [alt, Nat.not_even_iff_odd.2 (odd_two_mul_add_one i), ↓reduceIte]

/-- A pure-jump integrator with alternating jumps `±ε` at increasing times stays in `[0, ε]`. -/
theorem abs_pureJumpFun_alt_le {s : ℕ → ℝ} (hs : StrictMono s) {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ)
    (y : ℝ) : |pureJumpFun (range (2 * m)) s (alt ε) y| ≤ ε := by
  have hpair : pureJumpFun (range (2 * m)) s (alt ε) y =
      ∑ i ∈ range m, (if s (2 * i) ≤ y ∧ y < s (2 * i + 1) then ε else 0) := by
    rw [pureJumpFun, sum_filter, sum_range_two_mul]
    refine sum_congr rfl fun i _ => ?_
    have hlt : s (2 * i) < s (2 * i + 1) := hs (by omega)
    rw [alt_even, alt_odd]
    by_cases ha : s (2 * i) ≤ y <;> by_cases hb : s (2 * i + 1) ≤ y
    · simp [ha, hb]
    · simp [ha, hb, lt_of_not_ge hb]
    · exact absurd (hb.trans_lt (lt_of_not_ge ha)) (not_lt.2 hlt.le)
    · simp [ha, hb]
  rw [hpair, ← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : (filter (fun i => s (2 * i) ≤ y ∧ y < s (2 * i + 1)) (range m)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun i hi j hj => ?_
    simp only [mem_filter] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hs.monotone (show 2 * i + 1 ≤ 2 * j by omega)
      linarith [hi.2.2, hj.2.1]
    · have := hs.monotone (show 2 * j + 1 ≤ 2 * i by omega)
      linarith [hj.2.2, hi.2.1]
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)]
  calc _ ≤ (1 : ℝ) * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε
    _ = ε := one_mul ε

/-- Jump times `2 - 1/(j + 2)` in `[3/2, 2)`. -/
noncomputable def jt (j : ℕ) : ℝ :=
  2 - 1 / ((j : ℝ) + 2)

theorem jt_strictMono : StrictMono jt := fun i j hij => by
  have hij' : (i : ℝ) + 2 < (j : ℝ) + 2 := by
    have := (Nat.cast_lt (α := ℝ)).2 hij
    linarith
  have := one_div_lt_one_div_of_lt (by positivity) hij'
  simp only [jt]
  linarith

theorem one_lt_jt (j : ℕ) : 1 < jt j := by
  have h : 1 / ((j : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  simp only [jt]
  linarith

theorem jt_le_three (j : ℕ) : jt j ≤ 3 := by
  have : 0 < 1 / ((j : ℝ) + 2) := by positivity
  simp only [jt]
  linarith

/-- The jump size `1/(n + 1)`. -/
noncomputable def eps (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem eps_nonneg (n : ℕ) : 0 ≤ eps n := by
  unfold eps
  positivity

/-- The oscillating integrator `B_n`: `2 (n + 1)²` alternating jumps `±1/(n + 1)` in `[3/2, 2)`,
as an element of `ℓ^∞([0, 3])`. -/
noncomputable def oscB (n : ℕ) : 𝔻[3] :=
  ⟨fun t => pureJumpFun (range (2 * (n + 1) ^ 2)) jt (alt (eps n)) t,
    memℓp_infty_iff.2 ⟨eps n, by
      rintro _ ⟨t, rfl⟩
      simp only [Real.norm_eq_abs]
      exact abs_pureJumpFun_alt_le jt_strictMono (eps_nonneg n) _ _⟩⟩

theorem extendIcc_oscB (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    extendIcc (oscB n) x = pureJumpFun (range (2 * (n + 1) ^ 2)) jt (alt (eps n)) x := by
  rw [extendIcc_of_mem _ hx]
  rfl

theorem isBV_oscB (n : ℕ) : IsBV (oscB n) :=
  ⟨_, isControl_of_eqOn (isControl_pureJumpFun _ jt (alt (eps n)) 0 3)
    fun _ hx => (extendIcc_oscB n hx).symm⟩

theorem norm_oscB_le (n : ℕ) : ‖oscB n‖ ≤ 1 / ((n : ℝ) + 1) :=
  lp.norm_le_of_forall_le (eps_nonneg n) fun _ =>
    (Real.norm_eq_abs _).trans_le (abs_pureJumpFun_alt_le jt_strictMono (eps_nonneg n) _ _)

/-- `∏_{(1, 3]} (1 + dB_n) = (1 - 1/(n + 1)²)^((n + 1)²)`, by the multi-jump formula. -/
theorem productIntegral_oscB (n : ℕ) :
    productIntegral (extendIcc (oscB n)) 1 3 = (1 - eps n ^ 2) ^ ((n + 1) ^ 2) := by
  have hcongr : ∀ x ∈ Set.Icc (1 : ℝ) 3, extendIcc (oscB n) x =
      pureJumpFun (range (2 * (n + 1) ^ 2)) jt (alt (eps n)) x := fun x hx =>
    extendIcc_oscB n ⟨by linarith [hx.1], hx.2⟩
  rw [productIntegral_congr (by norm_num) hcongr,
    productIntegral_pureJumpFun _ _ _ jt_strictMono.injective.injOn (by norm_num),
    filter_true_of_mem fun j _ => ⟨one_lt_jt j, jt_le_three j⟩, prod_range_two_mul]
  have hpair : ∀ i ∈ range ((n + 1) ^ 2),
      (1 + alt (eps n) (2 * i)) * (1 + alt (eps n) (2 * i + 1)) = 1 - eps n ^ 2 := by
    intro i _
    rw [alt_even, alt_odd]
    ring
  rw [prod_congr rfl hpair, prod_const, card_range]

theorem oscB_value_le_half (n : ℕ) : (1 - eps n ^ 2) ^ ((n + 1) ^ 2) ≤ 1 / 2 := by
  set x := eps n ^ 2 with hxdef
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hx1 : x ≤ 1 := by
    have h : eps n ≤ 1 := by
      unfold eps
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact pow_le_one₀ (eps_nonneg n) h
  have hkx : (((n + 1) ^ 2 : ℕ) : ℝ) * -x = -1 := by
    simp only [hxdef, eps]
    push_cast
    field_simp
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : (1 - x) ^ ((n + 1) ^ 2) ≤ Real.exp (-x) ^ ((n + 1) ^ 2) :=
    pow_le_pow_left₀ (by linarith) h1 _
  rw [← Real.exp_nat_mul, hkx] at h2
  have he : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos := Real.exp_pos (-1)
  nlinarith

/-- The step `𝟙[1, 3]` in `ℓ^∞([0, 3])`. -/
noncomputable def stepOne : 𝔻[3] :=
  ⟨fun t => if 1 ≤ (t : ℝ) then 1 else 0, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨t, rfl⟩
    dsimp only
    split_ifs <;> norm_num⟩⟩

theorem extendIcc_stepOne {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    extendIcc stepOne x = if 1 ≤ x then 1 else 0 := by
  rw [extendIcc_of_mem _ hx]
  rfl

/-- `𝟙[1, 3]` has bounded variation, so it may belong to the class `S`. -/
theorem isBV_stepOne : IsBV stepOne := by
  have hmono : MonotoneOn (fun x : ℝ => if 1 ≤ x then (1 : ℝ) else 0) (Set.Icc 0 3) :=
    fun x _ y _ hxy => by
      simp only
      split_ifs <;> linarith
  exact ⟨_, isControl_of_eqOn (isControl_self_of_monotoneOn hmono)
    fun x hx => (extendIcc_stepOne hx).symm⟩

theorem isBV_zero : IsBV (0 : 𝔻[3]) :=
  ⟨fun _ => 0, fun x y _ _ _ => by simp [extendIcc_zero]⟩

/-- The horizon `3 ∈ [0, 3]`. -/
def t3 : Set.Icc (0 : ℝ) 3 :=
  ⟨3, by norm_num, le_rfl⟩

/-- For `A = 0` and `h = 𝟙[1, 3]`, the two-tag sums at `t = 3` are eventually
`P(B)(1, 3]`: only the cell ending at `1` sees an increment of `h`. -/
theorem psiSum_stepOne_eventually (B : 𝔻[3]) :
    ∀ᶠ s in atTop, psiSum 0 B stepOne (t3 : ℝ) s = productIntegral (extendIcc B) 1 3 := by
  refine eventually_atTop.2 ⟨{1}, fun s hs => ?_⟩
  have h1s : (1 : ℝ) ∈ s := hs (mem_singleton_self 1)
  have ht3 : (t3 : ℝ) = 3 := rfl
  rw [ht3, psiSum, extendIcc_zero, twoTagSum]
  set P := partitionPts 0 3 s with hP
  have h1P : (1 : ℝ) ∈ P :=
    mem_partitionPts.2 (Or.inr (Or.inr ⟨h1s, by norm_num, by norm_num⟩))
  have h0P : (0 : ℝ) ∈ P := left_mem_partitionPts s
  have hk : ∀ x ∈ P, extendIcc stepOne x = if 1 ≤ x then 1 else 0 := fun x hx =>
    extendIcc_stepOne (mem_Icc_of_mem_partitionPts (by norm_num) hx)
  rw [sum_eq_single (1 : ℝ)]
  · obtain ⟨hpm, hpl, -⟩ := prev_spec ⟨0, h0P, one_pos⟩
    simp [hk 1 h1P, hk _ hpm, not_le.2 hpl]
  · intro x hx hx1
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · have := (prev_le P x).trans_lt hlt
      simp [hk x hx, hk _ (prev_mem hx), not_le.2 hlt, not_le.2 this]
    · obtain ⟨-, -, h3⟩ := prev_spec ⟨1, h1P, hgt⟩
      simp [hk x hx, hk _ (prev_mem hx), hgt.le, h3 1 h1P hgt]
  · intro h
    exact absurd h1P h

/-- Any `Ψ` given by the two-tag sums has `Ψ(0, B) 𝟙[1, 3] (3) = P(B)(1, 3]`. -/
theorem psi_apply_t3 {Ψ : 𝔻[3] → 𝔻[3] → 𝔻[3] →L[ℝ] 𝔻[3]} (B : 𝔻[3])
    (hB : Tendsto (psiSum 0 B stepOne (t3 : ℝ)) atTop (𝓝 (Ψ 0 B stepOne t3))) :
    Ψ 0 B stepOne t3 = productIntegral (extendIcc B) 1 3 :=
  tendsto_nhds_unique hB
    (tendsto_const_nhds.congr' ((psiSum_stepOne_eventually B).mono fun _ hs => hs.symm))

/-- The domain of **all** integrators of bounded variation: no total-variation bound. -/
def bvDomain : Set 𝔻[3] :=
  {B | IsBV B}

/-- **Continuity of `Ψ` in `B` fails** on `bvDomain`, for every `Ψ` given by the two-tag sums,
at `A = 0` and `h = 𝟙[1, 3]`: `B_n → 0` in sup norm, but `Ψ(0, B_n) h (3) ≤ 1/2` while
`Ψ(0, 0) h (3) = 1`. -/
theorem not_tendsto_psi (Ψ : 𝔻[3] → 𝔻[3] → 𝔻[3] →L[ℝ] 𝔻[3])
    (hΨ : ∀ B ∈ bvDomain, Tendsto (psiSum 0 B stepOne (t3 : ℝ)) atTop (𝓝 (Ψ 0 B stepOne t3))) :
    ¬ Tendsto (fun B => Ψ 0 B stepOne) (𝓝[bvDomain] 0) (𝓝 (Ψ 0 0 stepOne)) := by
  intro hcont
  have hB : Tendsto oscB atTop (𝓝[bvDomain] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall isBV_oscB⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero]
    exact norm_oscB_le n
  have hcoord : Tendsto (fun n => Ψ 0 (oscB n) stepOne t3) atTop (𝓝 (Ψ 0 0 stepOne t3)) := by
    have hc := hcont.comp hB
    rw [tendsto_iff_norm_sub_tendsto_zero] at hc ⊢
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hc
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (Ψ 0 (oscB n) stepOne - Ψ 0 0 stepOne) t3
    rw [lp.coeFn_sub, Pi.sub_apply] at this
    exact this
  have hval : ∀ n, Ψ 0 (oscB n) stepOne t3 ≤ 1 / 2 := fun n => by
    rw [psi_apply_t3 _ (hΨ _ (isBV_oscB n)), productIntegral_oscB]
    exact oscB_value_le_half n
  have h0 : Ψ 0 0 stepOne t3 = 1 := by
    rw [psi_apply_t3 _ (hΨ _ isBV_zero), extendIcc_zero, productIntegral_const]
  have := le_of_tendsto hcoord (Eventually.of_forall hval)
  rw [h0] at this
  norm_num at this

/-- **The bridge is not claimed on `bvDomain`**: T78's `IsStieltjesProductIntegral` fails for
every product-integral map `P`, every class `S` containing `𝟙[1, 3]`, and every `Ψ` whose value
`Ψ(0, B) 𝟙[1, 3] (3)` is the limit of the two-tag sums. That hypothesis is satisfiable: by
`psiSum_stepOne_eventually` the sums are eventually `P(B)(1, 3]`, so for instance
`Ψ 0 B h = P(B)(1, 3] (h 3 - h 0) 𝟙` meets it. -/
theorem not_isStieltjesProductIntegral {Ψ : 𝔻[3] → 𝔻[3] → 𝔻[3] →L[ℝ] 𝔻[3]} {S : Set 𝔻[3]}
    {C : ℝ}
    (hΨ : ∀ B ∈ bvDomain, Tendsto (psiSum 0 B stepOne (t3 : ℝ)) atTop (𝓝 (Ψ 0 B stepOne t3)))
    (hS : stepOne ∈ S) (P : 𝔻[3] → 𝔻[3]) :
    ¬ IsStieltjesProductIntegral 3 P Ψ bvDomain S C := fun hP =>
  not_tendsto_psi Ψ hΨ (hP.tendsto 0 isBV_zero stepOne hS)

/-- **The bridge's hypotheses fail on `bvDomain`**: `bvDomain` consists of integrators of bounded
variation and is closed under `freeze`, so `IsPsiOperator.tendsto` would give the continuity that
`not_tendsto_psi` refutes; the uniform bound `norm_le` is what cannot hold. -/
theorem not_isPsiOperator {Ψ : 𝔻[3] → 𝔻[3] → 𝔻[3] →L[ℝ] 𝔻[3]} {C : ℝ} :
    ¬ IsPsiOperator 3 Ψ bvDomain {stepOne} C := fun hΨ =>
  not_tendsto_psi Ψ
    (fun B hB => hΨ.tendsto_psiSum 0 isBV_zero B hB stepOne (Set.mem_singleton _) t3)
    (hΨ.tendsto (fun _ hA => hA) (fun _ hA u => IsBV.freeze hA u)
      (fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact isBV_stepOne) isBV_zero
      (Set.mem_singleton _))

/-! ### Consistency at the degenerate horizon `τ = 0` -/

/-- Over `[0, 0]` the partition is `{0}` and every two-tag sum vanishes. -/
theorem psiSum_zero_horizon (A B h : 𝔻[0]) (t : Set.Icc (0 : ℝ) 0) (s : Finset ℝ) :
    psiSum A B h t s = 0 := by
  have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
  have hP : partitionPts (0 : ℝ) 0 s = {0} := by
    ext x
    simp only [mem_partitionPts, mem_singleton]
    constructor
    · rintro (h | h | ⟨-, h1, h2⟩)
      · exact h
      · exact h
      · exact absurd (h1.trans h2) (lt_irrefl 0)
    · intro h
      exact Or.inl h
  rw [psiSum, ht, hP, twoTagSum, sum_singleton, prev_eq_self (by simp), sub_self, mul_zero,
    zero_mul]

/-- The zero operator satisfies the Duhamel-operator hypotheses at `τ = 0`. -/
theorem isPsiOperator_zero_horizon :
    IsPsiOperator 0 (fun _ _ => 0) {A | IsBV A} {h | (Continuous fun t ↦ h t) ∧ IsBV h} 0 where
  norm_le _ _ _ _ := by simp
  tendsto_duhamel A _ B _ t := by
    have : psiSum A B (B - A) t = fun _ => 0 := funext fun s => psiSum_zero_horizon _ _ _ t s
    rw [this]
    simp
  tendsto_psiSum A _ B _ h _ t := by
    have : psiSum A B h t = fun _ => 0 := funext fun s => psiSum_zero_horizon _ _ _ t s
    rw [this]
    simp

/-- The bridge yields T78's hypothesis bundle for T77's product integral at `τ = 0`. -/
example : IsStieltjesProductIntegral 0 (productIntegralLInfty 0) (fun _ _ => 0) {A | IsBV A}
    {h | (Continuous fun t ↦ h t) ∧ IsBV h} 0 :=
  isStieltjesProductIntegral_productIntegralLInfty_continuous isPsiOperator_zero_horizon
    (fun _ hA => hA) (fun _ hA u => IsBV.freeze hA u)

end MathlibExtTest.Probability.Statistics.Survival.PsiBridge

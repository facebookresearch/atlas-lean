/-
Copyright (c) 2026 Sky (GitHub: ChironTheCentaur). All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sky (GitHub: ChironTheCentaur)

Adapted from `PartitionsJensen/Count.lean` of
https://github.com/ChironTheCentaur/rh-lab-partitions-jensen at commit
57beb8dbff7b84e125931fe2e53080f325f4f108.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.CircleMethod
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# `C_r(n)` is the colored-partition count

`CircleMethod` defines `coef r n` analytically, as the `n`-th Taylor coefficient of `F(q)^r` at `0`,
`F = partGen = ∏ (1 − qⁿ⁺¹)⁻¹`. Here it is identified with the count in the statement of
`eventually_jensen_hyperbolic_coloredPartitions`:

  `coef r n = ∑ x ∈ antidiagonalTuple r n, ∏ i, p(x i)`   (`coef_eq_cnt`).

Route:

* `hasSum_card_restricted`: for any predicate `P` on parts and `‖q‖ < 1`, if the partial products
  `∏_{i<N} f_i(q)` converge to `G` (`f_i = (1 − q^{i+1})⁻¹` if `P (i+1)`, else `1`), then
  `∑ₙ #(restricted n P) qⁿ = G`. The formal identity is Mathlib's
  `Nat.Partition.hasProd_powerSeriesMk_card_restricted` (pi topology, i.e. coefficientwise);
  the finite products are evaluated by Cauchy products (`PSum.mul`), their coefficients increase
  to `#(restricted n P)` (`coeff_Phi_mono`), and Tannery's theorem passes to the limit.
* `hasSum_card_partition`: `P = True` gives `∑ₙ p(n) qⁿ = F(q)`.
* `hasSum_cnt`: `∑ₙ cnt r n · qⁿ = F(q)^r` (induction on `r`, splitting the first coordinate
  of the tuple, `sum_antidiagonalTuple_succ`).
* `coef_eq_cnt`: uniqueness of power-series coefficients.
-/

noncomputable section

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

open Finset Filter Topology PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ### Absolutely convergent power series with real coefficients -/

section PSum

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `∑ₙ c n qⁿ = G`, absolutely. -/
def PSum (c : ℕ → ℝ) (q G : 𝕜) : Prop :=
  HasSum (fun n => (c n : 𝕜) * q ^ n) G ∧ Summable (fun n => ‖(c n : 𝕜) * q ^ n‖)

lemma PSum.congr {c c' : ℕ → ℝ} {q G : 𝕜} (h : PSum c q G) (hc : ∀ n, c n = c' n) :
    PSum c' q G := by
  have : c = c' := funext hc
  exact this ▸ h

/- If `∑ c n qⁿ = G` and `∑ d n qⁿ = H` absolutely, then the Cauchy product of `c` and `d` sums
to `G · H` absolutely. -/
lemma PSum.mul {c d : ℕ → ℝ} {q G H : 𝕜} (hc : PSum c q G) (hd : PSum d q H) :
    PSum (fun n => ∑ kl ∈ antidiagonal n, c kl.1 * d kl.2) q (G * H) := by
  have he : ∀ n, ((∑ kl ∈ antidiagonal n, c kl.1 * d kl.2 : ℝ) : 𝕜) * q ^ n =
      ∑ kl ∈ antidiagonal n, ((c kl.1 : 𝕜) * q ^ kl.1) * ((d kl.2 : 𝕜) * q ^ kl.2) := by
    intro n
    rw [RCLike.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [mem_antidiagonal] at hkl
    rw [← hkl, pow_add, RCLike.ofReal_mul]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hc.2 hd.2
  unfold PSum
  simp_rw [he]
  refine ⟨?_, hs⟩
  rw [← hc.1.tsum_eq, ← hd.1.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc.2
      hd.2]
  exact hs.of_norm.hasSum

lemma PSum.delta (q : 𝕜) : PSum (fun n => if n = 0 then 1 else 0) q 1 := by
  have h : HasSum (fun n => (((if n = 0 then 1 else 0 : ℝ)) : 𝕜) * q ^ n) 1 := by
    convert hasSum_single (f := fun n => (((if n = 0 then 1 else 0 : ℝ)) : 𝕜) * q ^ n) 0
      (fun b hb => by simp [hb]) using 1
    simp
  refine ⟨h, ?_⟩
  refine (hasSum_single (f := fun n => ‖(((if n = 0 then 1 else 0 : ℝ)) : 𝕜) * q ^ n‖) 0
    (fun b hb => by simp [hb])).summable

end PSum

/-! ### The factors `∑ⱼ q^{(i+1)j}` (or `1`) -/

section Factor

variable (P : ℕ → Prop) [DecidablePred P]

/-- Coefficients of the `i`-th factor: `∑ⱼ X^{(i+1)j}` if `P (i+1)`, else `1`. -/
def facCoef (i n : ℕ) : ℝ :=
  if P (i + 1) then (if (i + 1) ∣ n then 1 else 0) else (if n = 0 then 1 else 0)

/-- Value of the `i`-th factor: `(1 − q^{i+1})⁻¹` if `P (i+1)`, else `1`. -/
def facVal {𝕜 : Type*} [RCLike 𝕜] (i : ℕ) (q : 𝕜) : 𝕜 :=
  if P (i + 1) then (1 - q ^ (i + 1))⁻¹ else 1

lemma facCoef_nonneg (i n : ℕ) : 0 ≤ facCoef P i n := by
  unfold facCoef; split_ifs <;> norm_num

lemma facCoef_zero (i : ℕ) : facCoef P i 0 = 1 := by
  unfold facCoef; split_ifs <;> simp_all

lemma psum_geom {𝕜 : Type*} [RCLike 𝕜] (i : ℕ) {q : 𝕜} (hq : ‖q‖ < 1) :
    PSum (fun n => if (i + 1) ∣ n then 1 else 0) q (1 - q ^ (i + 1))⁻¹ := by
  have hinj : Function.Injective fun j : ℕ => (i + 1) * j :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.succ_pos i) h
  have hzero : ∀ (g : ℕ → ℝ) (n : ℕ), n ∉ Set.range (fun j : ℕ => (i + 1) * j) →
      ¬ (i + 1) ∣ n := by
    intro g n hn ⟨k, hk⟩; exact hn ⟨k, hk.symm⟩
  have hqi : ‖q ^ (i + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero i)
  constructor
  · rw [← hinj.hasSum_iff (fun n hn => by simp [hzero (fun _ => 0) n hn])]
    convert hasSum_geometric_of_norm_lt_one hqi using 1
    funext j; simp [pow_mul]
  · rw [← hinj.summable_iff (fun n hn => by simp [hzero (fun _ => 0) n hn])]
    convert summable_geometric_of_lt_one (norm_nonneg _) hqi using 1
    funext j; simp [pow_mul, norm_pow]

lemma psum_fac {𝕜 : Type*} [RCLike 𝕜] (i : ℕ) {q : 𝕜} (hq : ‖q‖ < 1) :
    PSum (facCoef P i) q (facVal P i q) := by
  unfold facCoef facVal
  split_ifs with h
  · exact psum_geom i hq
  · exact PSum.delta q

/- The `i`-th factor as a formal power series is Mathlib's. -/
private lemma mk_facCoef (i : ℕ) :
    PowerSeries.mk (facCoef P i) =
        if P (i + 1) then ∑' j : ℕ, (X : ℝ⟦X⟧) ^ ((i + 1) * j) else 1 := by
  unfold facCoef
  split_ifs with h
  · symm
    refine HasSum.tsum_eq ((WithPiTopology.hasSum_iff_hasSum_coeff ℝ).2 fun d => ?_)
    simp only [coeff_X_pow, coeff_mk]
    by_cases hd : (i + 1) ∣ d
    · obtain ⟨k, rfl⟩ := hd
      rw [ite_eq_left (dvd_mul_right _ _)]
      convert hasSum_ite_eq k (1 : ℝ) using 2 with j
      simp only [Nat.mul_left_cancel_iff (Nat.succ_pos i), eq_comm]
    · rw [ite_eq_right hd]
      convert hasSum_zero with j
      rw [ite_eq_right]; rintro rfl; exact hd (dvd_mul_right _ _)
  · ext n; simp [coeff_one]

/-- The finite products `∏_{i<N}` of the factors. -/
def Phi (N : ℕ) : ℝ⟦X⟧ := ∏ i ∈ range N, PowerSeries.mk (facCoef P i)

lemma coeff_Phi_succ (N n : ℕ) : coeff n (Phi P (N + 1)) =
    ∑ kl ∈ antidiagonal n, coeff kl.1 (Phi P N) * facCoef P N kl.2 := by
  rw [Phi, prod_range_succ, ← Phi, coeff_mul]
  simp only [coeff_mk]

lemma psum_Phi {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) (N : ℕ) :
    PSum (fun n => coeff n (Phi P N)) q (∏ i ∈ range N, facVal P i q) := by
  induction N with
  | zero =>
    simp only [Phi, range_zero, prod_empty]
    exact (PSum.delta q).congr fun n => by simp [coeff_one]
  | succ N ih =>
    rw [prod_range_succ]
    exact (ih.mul (psum_fac P N hq)).congr fun n => (coeff_Phi_succ P N n).symm

lemma coeff_Phi_nonneg (N n : ℕ) : 0 ≤ coeff n (Phi P N) := by
  induction N generalizing n with
  | zero => simp only [Phi, range_zero, prod_empty, coeff_one]; split_ifs <;> norm_num
  | succ N ih =>
    rw [coeff_Phi_succ]
    exact sum_nonneg fun kl _ => mul_nonneg (ih _) (facCoef_nonneg P _ _)

lemma coeff_Phi_mono (n : ℕ) : Monotone fun N => coeff n (Phi P N) := by
  refine monotone_nat_of_le_succ fun N => ?_
  rw [coeff_Phi_succ]
  have hmem : (n, 0) ∈ antidiagonal n := by simp
  refine le_trans (le_of_eq ?_) (single_le_sum (f := fun kl : ℕ × ℕ =>
    coeff kl.1 (Phi P N) * facCoef P N kl.2) (fun kl _ => mul_nonneg (coeff_Phi_nonneg P _ _)
      (facCoef_nonneg P _ _)) hmem)
  simp [facCoef_zero]

lemma tendsto_coeff_Phi (n : ℕ) :
    Tendsto (fun N => coeff n (Phi P N)) atTop (𝓝 (#(Nat.Partition.restricted n P) : ℝ)) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℝ P
  simp_rw [← mk_facCoef] at h
  have := ((WithPiTopology.continuous_coeff (R := ℝ) n).tendsto _).comp h.tendsto_prod_nat
  simpa [Function.comp_def, Phi] using this

lemma coeff_Phi_le (N n : ℕ) : coeff n (Phi P N) ≤ #(Nat.Partition.restricted n P) :=
  (coeff_Phi_mono P n).ge_of_tendsto (tendsto_coeff_Phi P n) N

/- A crude bound on the real partial products. -/
private lemma prod_facVal_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (N : ℕ) :
    ∏ i ∈ range N, facVal P i t ≤ Real.exp ((∑' i : ℕ, t ^ (i + 1)) / (1 - t)) := by
  have hs : Summable fun i : ℕ => t ^ (i + 1) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one ht0 ht1).mul_right t
  have h1t : 0 < 1 - t := by linarith
  have hfac : ∀ i, facVal P i t ≤ Real.exp (t ^ (i + 1) / (1 - t)) := by
    intro i
    have hx0 : 0 ≤ t ^ (i + 1) := pow_nonneg ht0 _
    have hxt : t ^ (i + 1) ≤ t := pow_le_of_le_one ht0 ht1.le (show i + 1 ≠ 0 by omega)
    unfold facVal
    split_ifs
    · have h1x : 0 < 1 - t ^ (i + 1) := by linarith
      refine le_trans ?_ (Real.add_one_le_exp _)
      rw [inv_eq_one_div, div_le_iff₀ h1x]
      have : t ^ (i + 1) ≤ t ^ (i + 1) / (1 - t) * (1 - t ^ (i + 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ h1t]
        nlinarith [mul_le_mul_of_nonneg_left hxt hx0]
      nlinarith [this]
    · exact Real.one_le_exp (div_nonneg hx0 h1t.le)
  calc ∏ i ∈ range N, facVal P i t ≤ ∏ i ∈ range N, Real.exp (t ^ (i + 1) / (1 - t)) := by
        refine prod_le_prod₀ (fun i _ => ?_) fun i _ => hfac i
        unfold facVal; split_ifs
        · have := pow_le_of_le_one ht0 ht1.le (show i + 1 ≠ 0 by omega)
          exact inv_nonneg.2 (by linarith)
        · norm_num
    _ = Real.exp ((∑ i ∈ range N, t ^ (i + 1)) / (1 - t)) := by
        rw [← Real.exp_sum, sum_div]
    _ ≤ _ := by
        gcongr
        exact hs.sum_le_tsum _ (fun i _ => pow_nonneg ht0 _)

lemma summable_card_restricted {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n => (#(Nat.Partition.restricted n P) : ℝ) * t ^ n := by
  refine summable_of_sum_range_le (c := Real.exp ((∑' i : ℕ, t ^ (i + 1)) / (1 - t)))
    (fun n => by positivity) fun M => ?_
  have hlim : Tendsto (fun N => ∑ n ∈ range M, coeff n (Phi P N) * t ^ n) atTop
      (𝓝 (∑ n ∈ range M, (#(Nat.Partition.restricted n P) : ℝ) * t ^ n)) :=
    tendsto_finsetSum _ fun n _ => (tendsto_coeff_Phi P n).mul_const _
  refine le_of_tendsto' hlim fun N => ?_
  have hN := psum_Phi P (𝕜 := ℝ) (q := t) (by rwa [Real.norm_of_nonneg ht0]) N
  exact (sum_le_hasSum _ (fun n _ => mul_nonneg (coeff_Phi_nonneg P _ _) (pow_nonneg ht0 _))
    hN.1).trans (prod_facVal_le P ht0 ht1 N)

/- For `‖q‖ < 1`: if the partial products `∏_{i<N} facVal P i q` tend to `G`, then
`∑ₙ #(partitions of n with parts in P) qⁿ = G`, absolutely. -/
private theorem hasSum_card_restricted {q : ℂ} (hq : ‖q‖ < 1) {G : ℂ}
    (hG : Tendsto (fun N => ∏ i ∈ range N, facVal P i q) atTop (𝓝 G)) :
    HasSum (fun n => (#(Nat.Partition.restricted n P) : ℂ) * q ^ n) G ∧
      Summable fun n => ‖(#(Nat.Partition.restricted n P) : ℂ) * q ^ n‖ := by
  have hb := summable_card_restricted P (norm_nonneg q) hq
  have hnorm : (fun n => ‖(#(Nat.Partition.restricted n P) : ℂ) * q ^ n‖) =
      fun n => (#(Nat.Partition.restricted n P) : ℝ) * ‖q‖ ^ n := by
    funext n; simp [norm_pow]
  have hsum : Summable fun n => (#(Nat.Partition.restricted n P) : ℂ) * q ^ n :=
    Summable.of_norm (hnorm ▸ hb)
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N n => ((coeff n (Phi P N) : ℝ) : ℂ) * q ^ n)
    (g := fun n => (#(Nat.Partition.restricted n P) : ℂ) * q ^ n) hb
    (fun n => by
      have := (Complex.continuous_ofReal.tendsto _).comp (tendsto_coeff_Phi P n)
      simpa using this.mul_const (q ^ n))
    (Eventually.of_forall fun N n => by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (coeff_Phi_nonneg P N n)]
      exact mul_le_mul_of_nonneg_right (coeff_Phi_le P N n) (pow_nonneg (norm_nonneg _) _))
  have hT' : Tendsto (fun N => ∏ i ∈ range N, facVal P i q) atTop
      (𝓝 (∑' n, (#(Nat.Partition.restricted n P) : ℂ) * q ^ n)) := by
    refine hT.congr fun N => ?_
    exact (psum_Phi P (𝕜 := ℂ) hq N).1.tsum_eq
  rw [← tendsto_nhds_unique hT' hG]
  exact ⟨hsum.hasSum, hnorm ▸ hb⟩

end Factor

/-! ### The partition function and colored partitions -/

/- **`∑ₙ p(n) qⁿ = F(q)`** on `‖q‖ < 1`, absolutely. -/
private theorem hasSum_card_partition {q : ℂ} (hq : ‖q‖ < 1) :
    PSum (fun n => (Fintype.card (Nat.Partition n) : ℝ)) q (partGen q) := by
  have hG : Tendsto (fun N => ∏ i ∈ range N, facVal (fun _ => True) i q) atTop (𝓝 (partGen q)) := by
    have h := (tendsto_eulerP hq).inv₀ (eulerP_ne_zero hq)
    simpa [facVal, partGen, prod_inv_distrib] using h
  have h := hasSum_card_restricted (fun _ => True) hq hG
  have hc : ∀ n, (#(Nat.Partition.restricted n fun _ => True) : ℂ) =
      ((Fintype.card (Nat.Partition n) : ℝ) : ℂ) := by
    intro n; simp [Nat.Partition.restricted, Finset.card_univ]
  simp_rw [hc] at h
  exact h

/-- The colored-partition count of the statement:
`C_r(n) = ∑_{m_1 + ⋯ + m_r = n} p(m_1) ⋯ p(m_r)`. -/
def cnt (r n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Nat.antidiagonalTuple r n, ∏ i, Fintype.card (Nat.Partition (x i))

/- Split off the first coordinate of a tuple in `antidiagonalTuple (k + 1) n`. -/
private lemma sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple (k + 1) n, f x =
      ∑ p ∈ antidiagonal n, ∑ y ∈ Finset.Nat.antidiagonalTuple k p.2, f (Fin.cons p.1 y) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨(x 0, n - x 0), Fin.tail x⟩)
    (fun s _ => Fin.cons s.1.1 s.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hx
    simp only [Finset.mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨by omega, ?_⟩
    simp only [Fin.tail]; omega
  · rintro ⟨⟨a, b⟩, y⟩ hs
    simp only [Finset.mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at hs
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  · intro x _; simp
  · rintro ⟨⟨a, b⟩, y⟩ hs
    simp only [Finset.mem_sigma, mem_antidiagonal] at hs
    simp only [Fin.cons_zero, Fin.tail_cons, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true,
      true_and]
    omega
  · intro x _; simp

lemma cnt_succ (k n : ℕ) :
    cnt (k + 1) n = ∑ p ∈ antidiagonal n, cnt k p.2 * Fintype.card (Nat.Partition p.1) := by
  rw [cnt, sum_antidiagonalTuple_succ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cnt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_succ, mul_comm]
  simp

lemma cnt_zero (n : ℕ) : cnt 0 n = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp [cnt, Finset.Nat.antidiagonalTuple_zero_zero]
  · simp [cnt, Finset.Nat.antidiagonalTuple_zero_succ]

/- **`∑ₙ C_r(n) qⁿ = F(q)^r`** on `‖q‖ < 1`, absolutely. -/
private theorem psum_cnt (r : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    PSum (fun n => (cnt r n : ℝ)) q (partGen q ^ r) := by
  induction r with
  | zero => exact (PSum.delta q).congr fun n => by rw [cnt_zero]; split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul (hasSum_card_partition hq)).congr fun n => ?_
    rw [cnt_succ]
    push_cast
    rw [← Finset.Nat.sum_antidiagonal_swap]
    simp [mul_comm]

/- Uniqueness of Taylor coefficients: any absolutely convergent expansion of `F(q)^r` on the unit
disc has the coefficients `coef r n`. -/
private lemma coef_eq_of_psum (r : ℕ) (a : ℕ → ℝ) (h : ∀ q : ℂ, ‖q‖ < 1 → PSum a q (partGen q ^ r))
    (n : ℕ) : coef r n = (a n : ℂ) := by
  set R : NNReal := ⟨1 / 2, by norm_num⟩
  have hR0 : (0 : NNReal) < R := by change (0 : ℝ) < 1 / 2; norm_num
  have hR1 : (R : ℝ) < 1 := by change (1 / 2 : ℝ) < 1; norm_num
  have hP : HasFPowerSeriesOnBall (fun q => partGen q ^ r)
      (FormalMultilinearSeries.ofScalars ℂ fun n => (a n : ℂ)) 0 R := by
    refine ⟨?_, by exact_mod_cast hR0, fun {y} hy => ?_⟩
    · refine FormalMultilinearSeries.le_radius_of_summable _ ?_
      have hs := (h ((R : ℝ) : ℂ) (by simpa [Complex.norm_real] using hR1)).2
      simpa [FormalMultilinearSeries.ofScalars_norm, norm_pow, Complex.norm_real] using hs
    · have hy' : ‖y‖ < 1 := by
        have : ‖y‖ < (R : ℝ) := by
          rw [Metric.eball, Set.mem_ofPred_eq, edist_zero_right] at hy
          exact_mod_cast hy
        linarith
      have := (h y hy').1
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this
  have h1 := (hasFPowerSeriesOnBall_partGen_pow r hR0 hR1).hasFPowerSeriesAt
  have h2 : cauchyPowerSeries (fun q => partGen q ^ r) 0 R =
      cauchyPowerSeries (fun q => partGen q ^ r) 0 (1 / 2) := rfl
  rw [coef, ← h2, h1.eq_formalMultilinearSeries hP.hasFPowerSeriesAt,
    FormalMultilinearSeries.coeff_ofScalars]

/-- **Count bridge.** The `n`-th Taylor coefficient of `F(q)^r`, `F(q) = ∏_{k ≥ 1} (1 − qᵏ)⁻¹`, is
`∑_{m₁ + ⋯ + m_r = n} p(m₁) ⋯ p(m_r)`. -/
theorem coef_eq_cnt (r n : ℕ) : coef r n = (cnt r n : ℂ) := by
  have := coef_eq_of_psum r (fun n => (cnt r n : ℝ)) (fun q hq => psum_cnt r hq) n
  simpa using this

end

end MetaMathlibExt.ColoredPartitionsJensen

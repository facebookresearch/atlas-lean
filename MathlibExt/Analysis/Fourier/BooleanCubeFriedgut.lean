/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeSpectral
public import MathlibExt.Probability.Hypercontractivity.SmallSetExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Friedgut's junta theorem with explicit constants

For a Boolean function `f : {-1, 1}ⁿ → {-1, 1}`, small-set expansion applied to the derivative
`D_i f(x) = x_i (f(x) - f(x^{⊕i}))/2`, a function with values in `{-1, 0, 1}` and
`Pr[D_i f ≠ 0] = Inf_i[f]`, bounds its noise stability at `1/3`, the `1/3`-stable influence
`Inf_i^{(1/3)}[f] = ∑_{S ∋ i} 3^{1-|S|} f̂(S)²`, by `Inf_i[f]^{3/2}` (O'Donnell's Corollary 9.12).
Summing over the coordinates of small influence gives O'Donnell's Theorem 9.28:
with `τ = ε² 9^{-k} / I[f]²` and `J = {j : Inf_j[f] ≥ τ}`, the Fourier weight on sets of size at
most `k` that leave `J` is at most `ε`, and `|J| ≤ I[f]³ 9^k / ε²`. Taking `k = ⌈I[f]/ε⌉`
(Proposition 3.2) and rounding the restriction of the Fourier expansion to `J` to its sign
(Proposition 3.31) gives Friedgut's junta theorem in explicit form.

## Main statements

* `BooleanCube.boolFourierCoeff_coordDerivative`: the Fourier expansion of `D_i f`.
* `BooleanCube.stableInfluence_third_le`: Corollary 9.12, `Inf_i^{(1/3)}[f] ≤ Inf_i[f]^{3/2}`.
* `BooleanCube.boolNoiseStab_derivative_le`: the same bound for the Laplacian `L_i f`,
  `Stab_{1/3}[L_i f] ≤ Inf_i[f]^{3/2} / 3`.
* `BooleanCube.sum_sq_not_subset_le_of_influence`: the spectral part of Theorem 9.28.
* `BooleanCube.card_influential_le`: `|J| ≤ I[f]³ 9^k / ε²`.
* `BooleanCube.exists_junta_boolDist_le`: Friedgut's junta theorem, explicit form.

## References

* E. Friedgut, *Boolean functions with low average sensitivity depend on few coordinates*,
  Combinatorica 18 (1998), 27-35.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Proposition 2.19, Corollaries 9.8 and 9.12 (Section 9.2), Theorem 9.28
  and Friedgut's Junta Theorem (Section 9.6).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators
open StatMech.Probability

variable {n : ℕ}

/-- **Fourier expansion of the coordinate derivative.** For `f : BoolCube n → ℝ` and a
coordinate `i`, the derivative `D_i f(x) = x_i (f(x) - f(x^{⊕i}))/2`, which is
`(f(x^{i↦1}) - f(x^{i↦-1}))/2`, has Fourier coefficient `0` at every `S ∋ i` and `f̂(S ∪ {i})` at
every `S ∌ i`; that is, `D_i f = ∑_{S ∋ i} f̂(S) χ_{S∖{i}}` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Definition 2.16 and Proposition 2.19). -/
theorem boolFourierCoeff_coordDerivative (f : BoolCube n → ℝ) (i : Fin n) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun x => cubeVal (x i) * ((f x - f (flipCoord x i)) / 2)) S =
      if i ∈ S then 0 else boolFourierCoeff n f (insert i S) := by
  have key := boolFourierCoeff_derivative f i
  rw [boolFourierCoeff_eq_expect]
  split_ifs with hS
  · have h : ∀ x : BoolCube n, cubeVal (x i) * ((f x - f (flipCoord x i)) / 2) * cubeChi n S x =
        (f x - f (flipCoord x i)) / 2 * cubeChi n (S.erase i) x := by
      intro x
      rw [cubeChi, ← Finset.mul_prod_erase S (fun j => cubeVal (x j)) hS, cubeChi]
      have hc := cubeVal_mul_self (x i)
      linear_combination ((f x - f (flipCoord x i)) / 2 * ∏ j ∈ S.erase i, cubeVal (x j)) * hc
    simp_rw [h, ← boolFourierCoeff_eq_expect, key]
    simp
  · have h : ∀ x : BoolCube n, cubeVal (x i) * ((f x - f (flipCoord x i)) / 2) * cubeChi n S x =
        (f x - f (flipCoord x i)) / 2 * cubeChi n (insert i S) x := by
      intro x
      rw [cubeChi, cubeChi, Finset.prod_insert hS]
      ring
    simp_rw [h, ← boolFourierCoeff_eq_expect, key]
    simp

/-- **Corollary 9.12: stable influences of Boolean functions.** For `f : BoolCube n → ℝ` with
values `±1` and a coordinate `i`, the `1/3`-stable influence
`Inf_i^{(1/3)}[f] = Stab_{1/3}[D_i f] = ∑_{S ∋ i} (1/3)^{|S|-1} f̂(S)²` satisfies
`Inf_i^{(1/3)}[f] ≤ Inf_i[f]^{3/2}`, written `Inf_i[f] · √(Inf_i[f])` (R. O'Donnell, *Analysis of
Boolean Functions*, 2014, Corollary 9.12; the source derives it from Corollary 9.8, the
Small-Set Expansion bound at `ρ = 1/3`, applied to the `{-1, 0, 1}`-valued `D_i f`). -/
theorem stableInfluence_third_le {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (i : Fin n) :
    ∑ S with i ∈ S, (1 / 3 : ℝ) ^ (S.card - 1) * boolFourierCoeff n f S ^ 2 ≤
      boolInfluence f i * Real.sqrt (boolInfluence f i) := by
  set D : BoolCube n → ℝ := fun x => cubeVal (x i) * ((f x - f (flipCoord x i)) / 2) with hD
  have hval : ∀ x, |D x| ^ ((4 : ℝ) / 3) = ((f x - f (flipCoord x i)) / 2) ^ 2 := by
    intro x
    have hc : |cubeVal (x i)| = 1 := by cases x i <;> simp [cubeVal]
    rcases hf x with h1 | h1 <;> rcases hf (flipCoord x i) with h2 | h2 <;>
      norm_num [hD, abs_mul, hc, h1, h2]
  have hpow : bnt_qnormPow (1 + 1 / 3) D = boolInfluence f i := by
    rw [bnt_qnormPow, bnt_uexp_eq_expect, boolInfluence]
    norm_num only
    exact Finset.expect_congr rfl fun x _ => hval x
  have hI0 : 0 ≤ boolInfluence f i := boolInfluence_nonneg f i
  have hstab := boolNoiseStab_le_bnt_qnorm_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) ≤ 1) D
  rw [bnt_qnorm, hpow] at hstab
  have hnorm : (boolInfluence f i ^ (1 / (1 + 1 / 3 : ℝ))) ^ 2 =
      boolInfluence f i * Real.sqrt (boolInfluence f i) := by
    rw [← Real.rpow_mul_natCast hI0, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hI0 (by norm_num)]
    norm_num
  -- `Stab_{1/3}[D_i f] = ∑_{S ∋ i} (1/3)^{|S|-1} f̂(S)²`.
  have hfourier : boolNoiseStab (1 / 3) D =
      ∑ S with i ∈ S, (1 / 3 : ℝ) ^ (S.card - 1) * boolFourierCoeff n f S ^ 2 := by
    rw [boolNoiseStab_eq_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => i ∈ S)]
    have h0 : ∑ S with i ∈ S, (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n D S ^ 2 = 0 :=
      Finset.sum_eq_zero fun S hS => by
        rw [hD, boolFourierCoeff_coordDerivative, ite_eq_left (Finset.mem_filter.mp hS).2]
        simp
    rw [h0, zero_add]
    refine Finset.sum_nbij' (fun S => insert i S) (fun T => T.erase i) ?_ ?_ ?_ ?_ ?_
    · intro S _
      simp
    · intro T _
      simp
    · intro S hS
      exact Finset.erase_insert (Finset.mem_filter.mp hS).2
    · intro T hT
      exact Finset.insert_erase (Finset.mem_filter.mp hT).2
    · intro S hS
      have hiS := (Finset.mem_filter.mp hS).2
      rw [hD, boolFourierCoeff_coordDerivative, ite_eq_right hiS, Finset.card_insert_of_notMem hiS,
        Nat.add_sub_cancel]
  rw [← hfourier, ← hnorm]
  exact hstab

/-- The Fourier form of the noise stability of a coordinate Laplacian. -/
private theorem boolNoiseStab_derivative_eq (f : BoolCube n → ℝ) (i : Fin n) :
    boolNoiseStab (1 / 3) (fun x => (f x - f (flipCoord x i)) / 2) =
      ∑ S with i ∈ S, (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 := by
  rw [boolNoiseStab_eq_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_derivative]
  split_ifs <;> simp

/-- **Noise stability of a coordinate Laplacian.** For `f : BoolCube n → ℝ` with values `±1` and
a coordinate `i`, the coordinate Laplacian `L_i f(x) = (f x - f x^{⊕i})/2` satisfies
`Stab_{1/3}[L_i f] ≤ Inf_i[f]^{3/2} / 3`, written `Inf_i[f] · √(Inf_i[f]) / 3`. Since
`Stab_{1/3}[L_i f] = ∑_{S ∋ i} 3^{-|S|} f̂(S)² = Inf_i^{(1/3)}[f] / 3`, this is Corollary 9.12
(`stableInfluence_third_le`) restated for `L_i f` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Corollary 9.12). -/
theorem boolNoiseStab_derivative_le {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (i : Fin n) :
    boolNoiseStab (1 / 3) (fun x => (f x - f (flipCoord x i)) / 2) ≤
      boolInfluence f i * Real.sqrt (boolInfluence f i) / 3 := by
  rw [boolNoiseStab_derivative_eq, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  refine le_trans (le_of_eq ?_) (stableInfluence_third_le hf i)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨i, (Finset.mem_filter.mp hS).2⟩)
  rw [hm, Nat.add_sub_cancel, pow_succ]
  ring

/-- **Spectral part of Friedgut's argument.** Let `f : BoolCube n → ℝ` take values `±1`, with
`I[f] > 0`, and let `0 < ε` and `k ∈ ℕ`. Put `τ = ε² / (I[f]² 9^k)` and
`J = {j : Inf_j[f] ≥ τ}`. Then the Fourier weight of `f` on the sets `S` with `|S| ≤ k` and
`S ⊄ J` is at most `ε` (R. O'Donnell, *Analysis of Boolean Functions*, 2014, Theorem 9.28: the
spectrum is `ε`-concentrated on `{S : S ⊆ J} ∪ {S : |S| > k}`). -/
theorem sum_sq_not_subset_le_of_influence {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hI : 0 < boolTotalInfluence f) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∑ S with S.card ≤ k ∧
        ¬S ⊆ Finset.univ.filter
          (fun j => ε ^ 2 / (boolTotalInfluence f ^ 2 * 9 ^ k) ≤ boolInfluence f j),
      boolFourierCoeff n f S ^ 2 ≤ ε := by
  set I := boolTotalInfluence f with hIdef
  set τ := ε ^ 2 / (I ^ 2 * 9 ^ k) with hτ
  set J : Finset (Fin n) := Finset.univ.filter (fun j => τ ≤ boolInfluence f j) with hJ
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hsqrtτ : Real.sqrt τ = ε / (I * 3 ^ k) := by
    rw [hτ, show (9 : ℝ) ^ k = (3 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      ← mul_pow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hε.le,
      Real.sqrt_sq (by positivity)]
  -- Lower bound: the stable influences outside `J` see every set that leaves `J`.
  have hswap : ∑ S : Finset (Fin n), ∑ j : Fin n,
      (if j ∉ J ∧ j ∈ S then (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 else 0) =
      ∑ j with j ∉ J, ∑ S with j ∈ S, (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∉ J
    · simp [hj, Finset.sum_filter]
    · simp [hj]
  have hlow : (1 / 3 : ℝ) ^ k * ∑ S with S.card ≤ k ∧ ¬S ⊆ J, boolFourierCoeff n f S ^ 2 ≤
      ∑ j with j ∉ J, ∑ S with j ∈ S, (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 := by
    rw [← hswap, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun S _ => ?_
    split_ifs with hS
    · obtain ⟨j, hjS, hjJ⟩ := Finset.not_subset.mp hS.2
      have hterm : (1 / 3 : ℝ) ^ k * boolFourierCoeff n f S ^ 2 ≤
          (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hS.1
      refine hterm.trans ?_
      have := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if j ∉ J ∧ j ∈ S then (1 / 3 : ℝ) ^ S.card *
          boolFourierCoeff n f S ^ 2 else 0)
        (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ j)
      simpa [hjS, hjJ] using this
    · refine Finset.sum_nonneg fun j _ => ?_
      split_ifs <;> positivity
  -- Upper bound: Corollary 9.12 (via `boolNoiseStab_derivative_le`) and `Inf_j < τ` outside `J`.
  have hup : ∑ j with j ∉ J, ∑ S with j ∈ S,
      (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2 ≤ Real.sqrt τ * I := by
    calc ∑ j with j ∉ J, ∑ S with j ∈ S, (1 / 3 : ℝ) ^ S.card * boolFourierCoeff n f S ^ 2
        ≤ ∑ j with j ∉ J, boolInfluence f j * Real.sqrt (boolInfluence f j) :=
          Finset.sum_le_sum fun j _ => by
            rw [← boolNoiseStab_derivative_eq]
            refine (boolNoiseStab_derivative_le hf j).trans ?_
            have := mul_nonneg (boolInfluence_nonneg f j) (Real.sqrt_nonneg (boolInfluence f j))
            linarith
      _ ≤ ∑ j with j ∉ J, Real.sqrt τ * boolInfluence f j :=
          Finset.sum_le_sum fun j hj => by
            have hlt : boolInfluence f j < τ := by
              have := (Finset.mem_filter.mp hj).2
              simpa [hJ] using this
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlt.le)
              (boolInfluence_nonneg f j)
      _ ≤ ∑ j, Real.sqrt τ * boolInfluence f j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => mul_nonneg (Real.sqrt_nonneg _) (boolInfluence_nonneg f j)
      _ = Real.sqrt τ * I := by rw [← Finset.mul_sum]; rfl
  have hR : Real.sqrt τ * I = ε / 3 ^ k := by
    rw [hsqrtτ]
    field_simp
  have hcomb := (hlow.trans hup).trans_eq hR
  have hdiv : (∑ S with S.card ≤ k ∧ ¬S ⊆ J, boolFourierCoeff n f S ^ 2) / 3 ^ k ≤ ε / 3 ^ k := by
    refine le_of_eq_of_le ?_ hcomb
    rw [one_div_pow]
    ring
  exact (div_le_div_iff_of_pos_right h3).mp hdiv

/-- **Few coordinates have large influence.** For `f : BoolCube n → ℝ` with `I[f] > 0`, `ε > 0`
and `k ∈ ℕ`, the set `J = {j : Inf_j[f] ≥ ε² / (I[f]² 9^k)}` has `|J| ≤ I[f]³ 9^k / ε²`
(R. O'Donnell, *Analysis of Boolean Functions*, 2014, Theorem 9.28). -/
theorem card_influential_le (f : BoolCube n → ℝ) (hI : 0 < boolTotalInfluence f) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) :
    ((Finset.univ.filter
        (fun j => ε ^ 2 / (boolTotalInfluence f ^ 2 * 9 ^ k) ≤ boolInfluence f j)).card : ℝ) ≤
      boolTotalInfluence f ^ 3 * 9 ^ k / ε ^ 2 := by
  set I := boolTotalInfluence f
  set τ := ε ^ 2 / (I ^ 2 * 9 ^ k) with hτ
  have hτ0 : 0 < τ := by positivity
  have hsum : ((Finset.univ.filter (fun j => τ ≤ boolInfluence f j)).card : ℝ) * τ ≤ I := by
    calc ((Finset.univ.filter (fun j => τ ≤ boolInfluence f j)).card : ℝ) * τ
        = ∑ j with τ ≤ boolInfluence f j, τ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j with τ ≤ boolInfluence f j, boolInfluence f j :=
          Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j, boolInfluence f j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => boolInfluence_nonneg f j
      _ = I := rfl
  rw [← le_div_iff₀ hτ0] at hsum
  refine hsum.trans_eq ?_
  rw [hτ]
  field_simp

/-- The restriction `∑_{S ⊆ J} f̂(S) χ_S` depends only on the coordinates in `J`. -/
private theorem restrict_eq_of_agree (f : BoolCube n → ℝ) (J : Finset (Fin n))
    {x y : BoolCube n} (hxy : ∀ i ∈ J, x i = y i) :
    ∑ S, (if S ⊆ J then boolFourierCoeff n f S else 0) * cubeChi n S x =
      ∑ S, (if S ⊆ J then boolFourierCoeff n f S else 0) * cubeChi n S y := by
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hxy i (hS hi)]
  · simp

/-- **Friedgut's junta theorem, explicit form.** Let `f : BoolCube n → ℝ` take values `±1` and
let `ε > 0`. Then there are a set `J` of coordinates with
`|J| ≤ I[f]³ 9^{⌈I[f]/ε⌉} / ε²` and a `±1`-valued `h` depending only on the coordinates in `J`
with `dist(f, h) ≤ 2ε` (E. Friedgut, 1998; R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Theorem 9.28 with `k = ⌈I[f]/ε⌉` from Proposition 3.2, and Proposition 3.31; the source gets
`ε` in place of `2ε` from Exercise 3.34). -/
theorem exists_junta_boolDist_le {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (J : Finset (Fin n)) (h : BoolCube n → ℝ),
      (J.card : ℝ) ≤ boolTotalInfluence f ^ 3 * 9 ^ ⌈boolTotalInfluence f / ε⌉₊ / ε ^ 2 ∧
      (∀ x, h x = 1 ∨ h x = -1) ∧
      (∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → h x = h y) ∧
      boolDist f h ≤ 2 * ε := by
  set I := boolTotalInfluence f with hIdef
  rcases (boolTotalInfluence_nonneg f).eq_or_lt with h0 | hpos
  · -- `I[f] = 0`: `f` is constant, a junta on no coordinates.
    refine ⟨∅, f, by rw [hIdef, ← h0]; simp, hf, fun x y _ => ?_,
      by rw [show boolDist f f = 0 by simp [boolDist]]; positivity⟩
    have hvar : boolVariance f = 0 :=
      le_antisymm (h0 ▸ boolVariance_le_boolTotalInfluence f) (boolVariance_nonneg f)
    have hc : ∀ z, f z = 𝔼 w, f w := fun z => by
      have h := (Finset.expect_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun _ _ => sq_nonneg _)).mp hvar z (Finset.mem_univ z)
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    rw [hc x, hc y]
  set k := ⌈I / ε⌉₊ with hk
  set J : Finset (Fin n) :=
    Finset.univ.filter (fun j => ε ^ 2 / (I ^ 2 * 9 ^ k) ≤ boolInfluence f j) with hJ
  set g : BoolCube n → ℝ := fun x =>
    ∑ S, (if S ⊆ J then boolFourierCoeff n f S else 0) * cubeChi n S x with hg
  refine ⟨J, fun x => if 0 ≤ g x then 1 else -1, card_influential_le f hpos hε k,
    fun x => by dsimp only; split_ifs <;> simp, fun x y hxy => ?_, ?_⟩
  · simp only [hg, restrict_eq_of_agree f J hxy]
  · refine (boolDist_le_expect_sq_sub hf (g := g) (fun x => by split_ifs <;> simp)
      fun x => by split_ifs with h <;> [linarith; linarith [not_le.mp h]]).trans ?_
    -- `‖f - g‖₂² = ∑_{S ⊄ J} f̂(S)²`.
    have hcoef : ∀ S, boolFourierCoeff n (fun x => f x - g x) S =
        if S ⊆ J then 0 else boolFourierCoeff n f S := fun S => by
      rw [boolFourierCoeff_sub, hg, boolFourierCoeff_sum_mul_cubeChi]
      split_ifs <;> ring
    rw [expect_sq_eq_sum_boolFourierCoeff_sq]
    simp_rw [hcoef]
    have hsplit : ∑ S, (if S ⊆ J then (0 : ℝ) else boolFourierCoeff n f S) ^ 2 ≤
        ∑ S with S.card ≤ k ∧ ¬S ⊆ J, boolFourierCoeff n f S ^ 2 +
          ∑ S with I / ε < (S.card : ℝ), boolFourierCoeff n f S ^ 2 := by
      simp_rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun S _ => ?_
      have key : ¬S.card ≤ k → I / ε < (S.card : ℝ) := fun hSk =>
        lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast not_le.mp hSk)
      have hnn : ∀ p : Prop, ∀ [Decidable p],
          0 ≤ (if p then boolFourierCoeff n f S ^ 2 else 0) := fun p _ => by
        split_ifs <;> positivity
      by_cases hSJ : S ⊆ J
      · rw [ite_eq_left hSJ, zero_pow two_ne_zero]
        exact add_nonneg (hnn _) (hnn _)
      · rw [ite_eq_right hSJ]
        by_cases hSk : S.card ≤ k
        · rw [ite_eq_left ⟨hSk, hSJ⟩]
          exact le_add_of_nonneg_right (hnn _)
        · rw [ite_eq_left (key hSk)]
          exact le_add_of_nonneg_left (hnn _)
    have h1 := sum_sq_not_subset_le_of_influence hf hpos hε k
    have h2 := sum_sq_card_gt_le_of_pos f hε
    linarith

/-- `9 ^ m ≤ exp (8 m)`, from `log 9 ≤ 8`. -/
private theorem nine_pow_le_exp (m : ℕ) : (9 : ℝ) ^ m ≤ Real.exp (8 * m) := by
  have hlog : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  calc (9 : ℝ) ^ m = Real.exp (Real.log 9) ^ m := by rw [Real.exp_log (by norm_num)]
    _ = Real.exp (m * Real.log 9) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (8 * m) := Real.exp_le_exp.mpr
      ((mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg m)))

/-- **Friedgut's Junta Theorem.** There is a universal constant `C` such that for every
`f : BoolCube n → ℝ` with values `±1` and every `0 < ε ≤ 1`, `f` is `ε`-close to a `±1`-valued
function `g` that depends only on the coordinates in a set `J` with
`|J| ≤ exp(C · I[f] / ε)` (E. Friedgut, 1998; R. O'Donnell, *Analysis of Boolean Functions*,
2014, Friedgut's Junta Theorem, Section 9.6, stated there as "`ε`-close to an
`exp(O(I[f]/ε))`-junta"). -/
theorem friedgut_junta_theorem :
    ∃ C : ℝ, ∀ (n : ℕ) (f : BoolCube n → ℝ), (∀ x, f x = 1 ∨ f x = -1) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (J : Finset (Fin n)) (g : BoolCube n → ℝ),
          (J.card : ℝ) ≤ Real.exp (C * boolTotalInfluence f / ε) ∧
          (∀ x, g x = 1 ∨ g x = -1) ∧
          (∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → g x = g y) ∧
          boolDist f g ≤ ε := by
  refine ⟨180, fun n f hf ε hε hε1 => ?_⟩
  obtain ⟨J, g, hJ, hg, hjunta, hdist⟩ := exists_junta_boolDist_le hf (half_pos hε)
  refine ⟨J, g, ?_, hg, hjunta, by linarith⟩
  set I := boolTotalInfluence f with hIdef
  set u := I / ε with hu
  have hI0 : 0 ≤ I := boolTotalInfluence_nonneg f
  have hu0 : 0 ≤ u := div_nonneg hI0 hε.le
  set m := ⌈I / (ε / 2)⌉₊ with hm
  have hm2 : (m : ℝ) < 2 * u + 1 := by
    have h := Nat.ceil_lt_add_one (div_nonneg hI0 (half_pos hε).le : 0 ≤ I / (ε / 2))
    have : I / (ε / 2) = 2 * u := by rw [hu]; field_simp
    rw [← hm, this] at h
    exact h
  -- `|J| ≤ 4 u³ 9^m`.
  have hB : (J.card : ℝ) ≤ 4 * u ^ 3 * 9 ^ m := by
    refine hJ.trans ?_
    have hI : I = u * ε := by rw [hu]; field_simp
    rw [hI, div_le_iff₀ (by positivity)]
    have h9 : (0 : ℝ) ≤ u ^ 3 * 9 ^ m := by positivity
    calc (u * ε) ^ 3 * 9 ^ m = ε * ε ^ 2 * (u ^ 3 * 9 ^ m) := by ring
      _ ≤ 1 * ε ^ 2 * (u ^ 3 * 9 ^ m) := by gcongr
      _ = 4 * u ^ 3 * 9 ^ m * (ε / 2) ^ 2 := by ring
  rcases Nat.eq_zero_or_pos J.card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hone : (1 : ℝ) ≤ J.card := by exact_mod_cast hpos
  -- Small `u` is impossible: then `|J| ≤ 36 u³ < 1`.
  have hularge : 1 / 10 < u := by
    by_contra hsmall'
    have hsmall : u ≤ 1 / 10 := not_lt.mp hsmall'
    have hm1 : m ≤ 1 := by
      have : (m : ℝ) < 2 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have h9 : (9 : ℝ) ^ m ≤ 9 := by
      calc (9 : ℝ) ^ m ≤ 9 ^ 1 := pow_le_pow_right₀ (by norm_num) hm1
        _ = 9 := by norm_num
    have hu3 : u ^ 3 ≤ (1 / 10) ^ 3 := pow_le_pow_left₀ hu0 hsmall 3
    nlinarith [pow_nonneg hu0 3]
  -- Large `u`: `4 u³ 9^m ≤ exp(8) exp(3u) exp(16u + 8) ≤ exp(180 u)`.
  have hu3 : u ^ 3 ≤ Real.exp (3 * u) := by
    have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc u ^ 3 ≤ Real.exp u ^ 3 := pow_le_pow_left₀ hu0 h1 3
      _ = Real.exp (3 * u) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 8 := by
    have := nine_pow_le_exp 1
    norm_num at this
    linarith
  have h9 : (9 : ℝ) ^ m ≤ Real.exp (16 * u + 8) :=
    (nine_pow_le_exp m).trans (Real.exp_le_exp.mpr (by linarith))
  calc (J.card : ℝ) ≤ 4 * u ^ 3 * 9 ^ m := hB
    _ ≤ Real.exp 8 * Real.exp (3 * u) * Real.exp (16 * u + 8) := by gcongr
    _ = Real.exp (19 * u + 16) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (180 * I / ε) := by
      refine Real.exp_le_exp.mpr ?_
      have : 180 * I / ε = 180 * u := by rw [hu]; ring
      rw [this]
      linarith

end BooleanCube

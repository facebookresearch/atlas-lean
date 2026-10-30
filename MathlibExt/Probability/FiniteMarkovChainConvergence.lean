/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovMixing
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of finite Markov chains

Let `P` be a stochastic matrix on a finite state space `S` (`P ∈ Matrix.rowStochastic ℝ S`) and
`π` a stationary distribution (`π ≥ 0`, `∑ y, π y = 1`, `π ᵥ* P = π`). The total variation distance
of the row `Pⁿ(x, ·)` from `π` is `tvDist (fun y => (P ^ n) x y) π`
(`MathlibExt.Probability.MarkovMixing.tvDist`, `(1/2) ∑_y |μ y - ν y|`).

## Main results

* `tvDist_pow_le_of_minorization`: **Doeblin's argument**. If `δ π(y) ≤ Pʳ(x, y)` for all
  `x, y` (informative for `r > 0`, `δ > 0`), then `d_TV(Pⁿ(x, ·), π) ≤ (1 - δ) ^ ⌊n / r⌋`
  for every `n` and every start `x`.
* `exists_tvDist_pow_le`: **the convergence theorem** (Levin, Peres and Wilmer, Theorem 4.9).
  If `P` is primitive (`Matrix.IsPrimitive`: some power has all entries positive; for a
  stochastic matrix this is irreducible and aperiodic), there are `C` and `0 ≤ α < 1` with
  `max_x d_TV(Pⁿ(x, ·), π) ≤ C αⁿ` for all `n`.
* `tendsto_pow_apply`: hence `Pⁿ(x, y) → π(y)` for every `x` and `y`;
  `stationary_unique`: the stationary distribution of a primitive chain is unique;
  `stationary_pos`: it has full support.

## References

* D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, 2nd ed., American
  Mathematical Society, 2017, Theorem 4.9 and its proof.
* W. Doeblin, "Exposé de la théorie des chaînes simples constantes de Markov à un nombre fini
  d'états", *Revue Math. de l'Union Interbalkanique* **2** (1938), 77–105.
-/

@[expose] public section

open Filter Matrix Topology
open MathlibExt.Probability.MarkovMixing

namespace MathlibExt.Probability.FiniteMarkovChainConvergence

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A stochastic matrix preserves the total mass of a signed vector. -/
private theorem sum_vecMul_of_mem {M : Matrix S S ℝ} (hM : M ∈ rowStochastic ℝ S)
    (w : S → ℝ) : ∑ y, (w ᵥ* M) y = ∑ x, w x := by
  simp only [vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, sum_row_of_mem_rowStochastic hM x, mul_one]

/-- Doeblin's contraction: under the minorization `δ π ≤ M`, a stochastic matrix contracts the
`ℓ¹` norm of signed vectors of total mass zero by the factor `1 - δ`. -/
private theorem sum_abs_vecMul_le {M : Matrix S S ℝ} (hM : M ∈ rowStochastic ℝ S)
    {π : S → ℝ} (hπ1 : ∑ y, π y = 1) {δ : ℝ} (hmin : ∀ x y, δ * π y ≤ M x y)
    {w : S → ℝ} (hw : ∑ x, w x = 0) :
    ∑ y, |(w ᵥ* M) y| ≤ (1 - δ) * ∑ x, |w x| := by
  have hrow : ∀ y, (w ᵥ* M) y = ∑ x, w x * (M x y - δ * π y) := by
    intro y
    simp only [vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hw, zero_mul, sub_zero]
  calc ∑ y, |(w ᵥ* M) y| ≤ ∑ y, ∑ x, |w x| * (M x y - δ * π y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [hrow]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmin x y))]
    _ = ∑ x, |w x| * (1 - δ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic hM x,
          ← Finset.mul_sum, hπ1, mul_one]
    _ = (1 - δ) * ∑ x, |w x| := by rw [Finset.mul_sum]; simp only [mul_comm]

private theorem vecMul_pow_of_stat {P : Matrix S S ℝ} {π : S → ℝ} (hstat : π ᵥ* P = π)
    (n : ℕ) : π ᵥ* P ^ n = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← vecMul_vecMul, ih, hstat]

/-- The `ℓ¹` distance of a row of `P ^ (j + r * k)` from `π` decays like `(1 - δ) ^ k`. -/
private theorem sum_abs_row_sub_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    {π : S → ℝ} (hπ1 : ∑ y, π y = 1) (hstat : π ᵥ* P = π) {r : ℕ} {δ : ℝ}
    (hmin : ∀ x y, δ * π y ≤ (P ^ r) x y) (hδ1 : δ ≤ 1) (j : ℕ) (x : S) :
    ∀ k : ℕ, ∑ y, |(P ^ (j + r * k)) x y - π y| ≤
      (1 - δ) ^ k * ∑ y, |(P ^ j) x y - π y| := by
  have hPr : P ^ r ∈ rowStochastic ℝ S := pow_mem hP r
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set w : S → ℝ := fun y => (P ^ (j + r * k)) x y - π y
    have hw : ∑ y, w y = 0 := by
      simp only [w, Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic (pow_mem hP _) x, hπ1,
        sub_self]
    have hstep : ∀ y, (P ^ (j + r * (k + 1))) x y - π y = (w ᵥ* P ^ r) y := by
      intro y
      have h1 : P ^ (j + r * (k + 1)) = P ^ (j + r * k) * P ^ r := by
        rw [← pow_add]; ring_nf
      have h2 : (π ᵥ* P ^ r) y = π y := by rw [vecMul_pow_of_stat hstat]
      rw [h1, Matrix.mul_apply, ← h2]
      simp only [w, vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib]
    calc ∑ y, |(P ^ (j + r * (k + 1))) x y - π y| = ∑ y, |(w ᵥ* P ^ r) y| := by
          simp only [hstep]
      _ ≤ (1 - δ) * ∑ y, |w y| := sum_abs_vecMul_le hPr hπ1 hmin hw
      _ ≤ (1 - δ) * ((1 - δ) ^ k * ∑ y, |(P ^ j) x y - π y|) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - δ) ^ (k + 1) * ∑ y, |(P ^ j) x y - π y| := by ring

/-- **Doeblin's argument** (Levin, Peres and Wilmer, proof of Theorem 4.9): if the `r`-step
transition probabilities dominate `δ π`, then the total variation distance of `Pⁿ(x, ·)` from the
stationary distribution `π` is at most `(1 - δ) ^ ⌊n / r⌋`. The bound is informative when
`r > 0` and `0 < δ`; for `r = 0` (`n / 0 = 0`) or `δ ≤ 0` it reads `d_TV ≤ 1` or weaker. -/
theorem tvDist_pow_le_of_minorization {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    {π : S → ℝ} (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : ∑ y, π y = 1) (hstat : π ᵥ* P = π)
    {r : ℕ} {δ : ℝ} (hmin : ∀ x y, δ * π y ≤ (P ^ r) x y)
    (n : ℕ) (x : S) :
    tvDist (fun y => (P ^ n) x y) π ≤ (1 - δ) ^ (n / r) := by
  have hδ1 : δ ≤ 1 := by
    obtain ⟨y₀⟩ : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hπ1
    have h := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hmin y₀ y
    rw [← Finset.mul_sum, hπ1, mul_one, sum_row_of_mem_rowStochastic (pow_mem hP r) y₀] at h
    exact h
  have hn : n = n % r + r * (n / r) := (Nat.mod_add_div n r).symm
  have h := sum_abs_row_sub_le hP hπ1 hstat hmin hδ1 (n % r) x (n / r)
  rw [← hn] at h
  have h2 : ∑ y, |(P ^ (n % r)) x y - π y| ≤ 2 := by
    calc ∑ y, |(P ^ (n % r)) x y - π y| ≤ ∑ y, ((P ^ (n % r)) x y + π y) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have h0 := nonneg_of_mem_rowStochastic (pow_mem hP (n % r)) (i := x) (j := y)
          rw [abs_le]
          constructor <;> linarith [hπ0 y]
      _ = 2 := by
          rw [Finset.sum_add_distrib, sum_row_of_mem_rowStochastic (pow_mem hP _) x, hπ1]
          norm_num
  have hθ : 0 ≤ (1 - δ) ^ (n / r) := pow_nonneg (by linarith) _
  unfold tvDist
  nlinarith

/-- **The convergence theorem** (Levin, Peres and Wilmer, Theorem 4.9): a primitive
(irreducible and aperiodic) stochastic matrix with stationary distribution `π` converges to `π`
geometrically fast in total variation, uniformly in the starting state. -/
theorem exists_tvDist_pow_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hprim : P.IsPrimitive) {π : S → ℝ} (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : ∑ y, π y = 1)
    (hstat : π ᵥ* P = π) :
    ∃ C α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ (n : ℕ) (x : S), tvDist (fun y => (P ^ n) x y) π ≤ C * α ^ n := by
  obtain ⟨-, r, hr, hpos⟩ := hprim
  have hne : (Finset.univ : Finset (S × S)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    have : IsEmpty S := ⟨fun x => h.false (x, x)⟩
    simp at hπ1
  set δ := (Finset.univ : Finset (S × S)).inf' hne fun p => (P ^ r) p.1 p.2
  have hδ0 : 0 < δ := (Finset.lt_inf'_iff hne).2 fun p _ => hpos p.1 p.2
  have hδle : ∀ x y, δ ≤ (P ^ r) x y := fun x y =>
    Finset.inf'_le (fun p : S × S => (P ^ r) p.1 p.2) (Finset.mem_univ (x, y))
  have hπle : ∀ y, π y ≤ 1 := fun y => by
    rw [← hπ1]
    exact Finset.single_le_sum (fun z _ => hπ0 z) (Finset.mem_univ y)
  have hmin : ∀ x y, δ * π y ≤ (P ^ r) x y := fun x y =>
    (mul_le_of_le_one_right hδ0.le (hπle y)).trans (hδle x y)
  have hδ1 : δ ≤ 1 :=
    (hδle hne.choose.1 hne.choose.2).trans (le_one_of_mem_rowStochastic (pow_mem hP r))
  set θ : ℝ := max (1 - δ) (1 / 2)
  have hθ0 : 0 < θ := lt_max_of_lt_right (by norm_num)
  have hθ1 : θ < 1 := max_lt (by linarith) (by norm_num)
  refine ⟨θ⁻¹, θ ^ (1 / (r : ℝ)), Real.rpow_nonneg hθ0.le _,
    Real.rpow_lt_one hθ0.le hθ1 (by positivity), fun n x => ?_⟩
  have hD := tvDist_pow_le_of_minorization hP hπ0 hπ1 hstat hmin n x
  have h1 : (1 - δ) ^ (n / r) ≤ θ ^ (n / r) :=
    pow_le_pow_left₀ (by linarith) (le_max_left _ _) _
  have hfl : (n : ℝ) / r - 1 ≤ ((n / r : ℕ) : ℝ) := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have h2 : θ ^ (n / r) ≤ θ⁻¹ * (θ ^ (1 / (r : ℝ))) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hθ0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hθ0]
    refine Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1.le ?_
    have : (-1 : ℝ) + 1 / r * n = n / r - 1 := by ring
    linarith
  linarith

/-- For a primitive stochastic matrix with stationary distribution `π`, every row of `Pⁿ`
converges to `π`: `Pⁿ(x, y) → π(y)`. -/
theorem tendsto_pow_apply {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hprim : P.IsPrimitive) {π : S → ℝ} (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : ∑ y, π y = 1)
    (hstat : π ᵥ* P = π) (x y : S) : Tendsto (fun n => (P ^ n) x y) atTop (𝓝 (π y)) := by
  obtain ⟨C, α, hα0, hα1, hb⟩ := exists_tvDist_pow_le hP hprim hπ0 hπ1 hstat
  have hlim : Tendsto (fun n : ℕ => 2 * (C * α ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul C |>.const_mul 2
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
  rw [Real.dist_eq]
  have h1 : |(P ^ n) x y - π y| ≤ ∑ z, |(P ^ n) x z - π z| :=
    Finset.single_le_sum (f := fun z => |(P ^ n) x z - π z|) (fun z _ => abs_nonneg _)
      (Finset.mem_univ y)
  have h2 := hb n x
  unfold tvDist at h2
  linarith

/-- A primitive stochastic matrix has at most one stationary distribution. In fact `π'` may be
any stationary vector of total mass `1`, not necessarily nonnegative. -/
theorem stationary_unique {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hprim : P.IsPrimitive) {π π' : S → ℝ} (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : ∑ y, π y = 1)
    (hstat : π ᵥ* P = π)
    (hπ1' : ∑ y, π' y = 1) (hstat' : π' ᵥ* P = π') : π = π' := by
  funext y
  have hlim : Tendsto (fun n => ∑ x, π' x * (P ^ n) x y) atTop (𝓝 (∑ x, π' x * π y)) :=
    tendsto_finsetSum _ fun x _ =>
      (tendsto_pow_apply hP hprim hπ0 hπ1 hstat x y).const_mul (π' x)
  have hconst : (fun n => ∑ x, π' x * (P ^ n) x y) = fun _ => π' y := by
    funext n
    have := congrFun (vecMul_pow_of_stat hstat' n) y
    simpa [vecMul, dotProduct] using this
  rw [hconst, ← Finset.sum_mul, hπ1', one_mul] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The stationary distribution of a primitive stochastic matrix has full support. -/
theorem stationary_pos {P : Matrix S S ℝ} (hprim : P.IsPrimitive) {π : S → ℝ}
    (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : ∑ y, π y = 1) (hstat : π ᵥ* P = π) (y : S) : 0 < π y := by
  obtain ⟨-, r, -, hpos⟩ := hprim
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < π x := by
    by_contra h
    push Not at h
    have : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun x _ => h x
    linarith
  have hy : π y = ∑ x, π x * (P ^ r) x y := by
    have := congrFun (vecMul_pow_of_stat hstat r) y
    simpa [vecMul, dotProduct] using this.symm
  rw [hy]
  exact lt_of_lt_of_le (mul_pos hx₀ (hpos x₀ y))
    (Finset.single_le_sum (f := fun x => π x * (P ^ r) x y)
      (fun x _ => mul_nonneg (hπ0 x) (hpos x y).le) (Finset.mem_univ x₀))

end MathlibExt.Probability.FiniteMarkovChainConvergence

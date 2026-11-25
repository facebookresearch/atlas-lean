/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Convergence of the alternating direction method of multipliers (ADMM)

ADMM solves `minimize f x + g z subject to A x + B z = c` by alternately minimizing the augmented
Lagrangian `L_ρ(x, z, y) = f x + g z + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²` over `x`
and over `z`, followed by the dual ascent step `y ← y + ρ (A x + B z - c)`. The basic convergence
theorem (Boyd, Parikh, Chu, Peleato and Eckstein, §3.2, proved in Appendix A) says that if `f`
and `g` are closed, proper and convex and the unaugmented Lagrangian `L₀` has a saddle point, then
the residual `A xᵏ + B zᵏ - c` tends to `0` and the objective `f xᵏ + g zᵏ` tends to the optimal
value. The statement below is the special case of real-valued convex `f` and `g` on
finite-dimensional real inner product spaces (real-valued convex functions there are continuous,
hence closed and proper); the iterates are taken as given minimizers, so no claim is made about
the solvability of the subproblems.
-/

@[expose] public section

namespace WantedExt.Analysis.Convex.ADMMConvergenceWanted

open Filter
open scoped InnerProductSpace Topology

section

variable {U P : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- At a block minimizer, convexity allows the quadratic penalty to be replaced by its
linearization. Compare against points on the segment from the minimizer to the trial point. -/
private theorem block_optimality {f : U → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (A : U →L[ℝ] P) (b y : P) (ρ : ℝ) (u : U)
    (hmin : ∀ v, f u + ⟪y, A u + b⟫_ℝ + ρ / 2 * ‖A u + b‖ ^ 2 ≤
      f v + ⟪y, A v + b⟫_ℝ + ρ / 2 * ‖A v + b‖ ^ 2) (v : U) :
    f u ≤ f v + ⟪y + ρ • (A u + b), A v - A u⟫_ℝ := by
  let r := A u + b
  let d := A v - A u
  let bound := f v + ⟪y + ρ • r, d⟫_ℝ
  have htend : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => bound + t * (ρ / 2 * ‖d‖ ^ 2))
      (𝓝[>] 0) (𝓝 bound) := by
    simpa using (tendsto_const_nhds.add (htend.mul_const (ρ / 2 * ‖d‖ ^ 2)) :
      Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 (bound + 0 * (ρ / 2 * ‖d‖ ^ 2))))
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  have hconv := hf.2 (Set.mem_univ u) (Set.mem_univ v) (sub_nonneg.mpr ht.2.le)
    ht.1.le (sub_add_cancel 1 t)
  have h := hmin ((1 - t) • u + t • v)
  have heq : A ((1 - t) • u + t • v) + b = r + t • d := by
    simp only [map_add, map_smul, r, d]
    module
  rw [heq, inner_add_right _ r, real_inner_smul_right, norm_add_sq_real r, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at h
  change f u + ⟪y, r⟫_ℝ + ρ / 2 * ‖r‖ ^ 2 ≤ _ at h
  simp only [smul_eq_mul] at hconv
  change f u ≤ bound + t * (ρ / 2 * ‖d‖ ^ 2)
  apply (mul_le_mul_iff_right₀ ht.1).mp
  dsimp only [bound]
  rw [inner_add_left, real_inner_smul_left]
  linarith only [h, hconv]

/-- Polarization of the two squared distances in the ADMM energy. Here `r` is the primal
residual, `d` is the change in the image of the second block, and `gap` is the objective
gap corrected by the saddle multiplier. -/
private theorem energy_drop {ρ gap : ℝ} (hρ : 0 < ρ) (u b r d : P)
    (hgap : gap ≤ -⟪u, r⟫_ℝ + ρ * ⟪d, r - b⟫_ℝ) (hcross : ⟪d, r⟫_ℝ ≤ 0) :
    2 * ρ * gap + ρ ^ 2 * ‖r‖ ^ 2 ≤
      (‖u - ρ • r‖ ^ 2 + ρ ^ 2 * ‖b - d‖ ^ 2) - (‖u‖ ^ 2 + ρ ^ 2 * ‖b‖ ^ 2) := by
  rw [inner_sub_right, real_inner_comm b d] at hgap
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hρ]
  linarith only [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * ρ by positivity),
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ρ) hcross,
    mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖d‖)]

end

/-- **Convergence of ADMM.** Let `E`, `F`, `P` be finite-dimensional real inner product spaces,
`f : E → ℝ` and `g : F → ℝ` convex, `A : E →L[ℝ] P`, `B : F →L[ℝ] P`, `c : P` and `ρ > 0`, and
write `L_ρ(x, z, y) = f x + g z + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²`. Suppose the
unaugmented Lagrangian `L₀` has a saddle point `(x⋆, z⋆, y⋆)`:
`L₀(x⋆, z⋆, y) ≤ L₀(x⋆, z⋆, y⋆) ≤ L₀(x, z, y⋆)` for all `x, z, y`. If the sequences `xᵏ, zᵏ, yᵏ`
satisfy the ADMM iteration — `xᵏ⁺¹` minimizes `L_ρ(·, zᵏ, yᵏ)`, `zᵏ⁺¹` minimizes
`L_ρ(xᵏ⁺¹, ·, yᵏ)`, and `yᵏ⁺¹ = yᵏ + ρ (A xᵏ⁺¹ + B zᵏ⁺¹ - c)` — then the primal residual
`A xᵏ + B zᵏ - c` tends to `0` and the objective `f xᵏ + g zᵏ` tends to `p⋆ = f x⋆ + g z⋆`, the
optimal value.

Source: S. Boyd, N. Parikh, E. Chu, B. Peleato and J. Eckstein, "Distributed Optimization and
Statistical Learning via the Alternating Direction Method of Multipliers", *Foundations and
Trends in Machine Learning* 3(1), 2011, §3.1 (eqs. (3.1)–(3.4)), §3.2 (Assumptions 1 and 2,
residual and objective convergence) and Appendix A (proof);
https://stanford.edu/~boyd/papers/pdf/admm_distr_stats.pdf.
Real-valued `f`, `g` are a special case of Assumption 1. -/
public theorem admm_residual_and_objective_convergence
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    {f : E → ℝ} {g : F → ℝ} (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g)
    (A : E →L[ℝ] P) (B : F →L[ℝ] P) (c : P) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : E} {zs : F} {ys : P}
    (hsaddle : ∀ (x : E) (z : F) (y : P),
      f xs + g zs + inner ℝ y (A xs + B zs - c) ≤ f xs + g zs + inner ℝ ys (A xs + B zs - c) ∧
        f xs + g zs + inner ℝ ys (A xs + B zs - c) ≤ f x + g z + inner ℝ ys (A x + B z - c))
    {x : ℕ → E} {z : ℕ → F} {y : ℕ → P}
    (hx : ∀ k (x' : E),
      f (x (k + 1)) + g (z k) + inner ℝ (y k) (A (x (k + 1)) + B (z k) - c) +
          ρ / 2 * ‖A (x (k + 1)) + B (z k) - c‖ ^ 2 ≤
        f x' + g (z k) + inner ℝ (y k) (A x' + B (z k) - c) + ρ / 2 * ‖A x' + B (z k) - c‖ ^ 2)
    (hz : ∀ k (z' : F),
      f (x (k + 1)) + g (z (k + 1)) + inner ℝ (y k) (A (x (k + 1)) + B (z (k + 1)) - c) +
          ρ / 2 * ‖A (x (k + 1)) + B (z (k + 1)) - c‖ ^ 2 ≤
        f (x (k + 1)) + g z' + inner ℝ (y k) (A (x (k + 1)) + B z' - c) +
          ρ / 2 * ‖A (x (k + 1)) + B z' - c‖ ^ 2)
    (hy : ∀ k, y (k + 1) = y k + ρ • (A (x (k + 1)) + B (z (k + 1)) - c)) :
    Filter.Tendsto (fun k => A (x k) + B (z k) - c) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => f (x k) + g (z k)) Filter.atTop (nhds (f xs + g zs)) := by
  let r (k : ℕ) := A (x k) + B (z k) - c
  let b (k : ℕ) := B (z k) - B zs
  let d (k : ℕ) := B (z (k + 1)) - B (z k)
  let gap (k : ℕ) := f (x k) + g (z k) + ⟪ys, r k⟫_ℝ - (f xs + g zs)
  let V (k : ℕ) := ‖y k - ys‖ ^ 2 + ρ ^ 2 * ‖b k‖ ^ 2
  have hfeas : A xs + B zs - c = 0 := by
    have h := (hsaddle xs zs (ys + (A xs + B zs - c))).1
    rw [inner_add_left] at h
    apply real_inner_self_nonpos.mp
    linarith
  have hnonneg (k : ℕ) : 0 ≤ gap k := by
    have h := (hsaddle (x k) (z k) ys).2
    simpa [gap, r, hfeas, sub_nonneg] using h
  -- Linearize each block at its new minimizer. Only the first block uses the old z.
  have hx' (k : ℕ) (v : E) :
      f (x (k + 1)) ≤ f v + ⟪y (k + 1) - ρ • d k, A v - A (x (k + 1))⟫_ℝ := by
    have heq : y (k + 1) - ρ • d k = y k + ρ • (A (x (k + 1)) + (B (z k) - c)) := by
      rw [hy]
      dsimp only [d]
      module
    rw [heq]
    apply block_optimality hf
    intro w
    simp only [← add_sub_assoc]
    linarith only [hx k w]
  have hz' (k : ℕ) (v : F) :
      g (z (k + 1)) ≤ g v + ⟪y (k + 1), B v - B (z (k + 1))⟫_ℝ := by
    rw [hy, add_comm (A (x (k + 1))) (B (z (k + 1))), add_sub_assoc]
    apply block_optimality hg
    intro w
    simp only [← add_sub_assoc, add_comm (B _) (A _)]
    linarith only [hz k w]
  have hupper (k : ℕ) : gap (k + 1) ≤
      -⟪y (k + 1) - ys, r (k + 1)⟫_ℝ + ρ * ⟪d k, r (k + 1) - b (k + 1)⟫_ℝ := by
    have hsum : (A xs - A (x (k + 1))) + (B zs - B (z (k + 1))) = -r (k + 1) := by
      dsimp only [r]
      rw [← sub_eq_zero.mp hfeas]
      abel
    have hdiff : r (k + 1) - b (k + 1) = -(A xs - A (x (k + 1))) := by
      dsimp only [r, b]
      rw [← sub_eq_zero.mp hfeas]
      abel
    have hxstar := hx' k xs
    have hzstar := hz' k zs
    rw [inner_sub_left, real_inner_smul_left] at hxstar
    have hid := congrArg (fun w => ⟪y (k + 1), w⟫_ℝ) hsum
    simp only [inner_add_right, inner_neg_right] at hid
    dsimp only [gap]
    rw [inner_sub_left, hdiff, inner_neg_right]
    linarith only [hxstar, hzstar, hid]
  -- Compare two successive second-block optimality inequalities to control the cross term.
  have hcross (k : ℕ) : ⟪d (k + 1), r (k + 2)⟫_ℝ ≤ 0 := by
    have hprev := hz' k (z (k + 2))
    have hnext := hz' (k + 1) (z (k + 1))
    change g (z (k + 1)) ≤ g (z (k + 2)) + ⟪y (k + 1), d (k + 1)⟫_ℝ at hprev
    rw [← neg_sub (B (z (k + 2))) (B (z (k + 1))), inner_neg_right] at hnext
    change g (z (k + 2)) ≤ g (z (k + 1)) + -⟪y (k + 2), d (k + 1)⟫_ℝ at hnext
    rw [hy (k + 1), inner_add_left, real_inner_smul_left] at hnext
    rw [real_inner_comm]
    apply nonpos_of_mul_nonpos_right _ hρ
    linarith only [hprev, hnext]
  have hdrop (k : ℕ) : 2 * ρ * gap (k + 2) + ρ ^ 2 * ‖r (k + 2)‖ ^ 2 ≤
      V (k + 1) - V (k + 2) := by
    have h := energy_drop hρ _ _ _ _ (hupper (k + 1)) (hcross k)
    have hu : y (k + 2) - ys - ρ • r (k + 2) = y (k + 1) - ys := by
      rw [hy (k + 1)]
      dsimp only [r]
      abel
    have hb : b (k + 2) - d (k + 1) = b (k + 1) := by
      dsimp only [b, d]
      abel
    simpa only [hu, hb, V] using h
  have hV : Antitone (fun k => V (k + 1)) := by
    apply antitone_nat_of_succ_le
    intro k
    linarith only [hdrop k, mul_nonneg (show 0 ≤ 2 * ρ by positivity) (hnonneg (k + 2)),
      mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖r (k + 2)‖)]
  have hlim := tendsto_atTop_ciInf hV (show BddBelow (Set.range (fun k => V (k + 1))) by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    dsimp only [V]
    positivity)
  have hdec : Tendsto (fun k => V (k + 1) - V (k + 2)) atTop (𝓝 0) := by
    simpa using hlim.sub ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hres : Tendsto r atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 2).mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hs : Tendsto (fun k => ‖r (k + 2)‖ ^ 2) atTop (𝓝 0) := by
      apply squeeze_zero (fun k => sq_nonneg _) _ (by
        simpa using hdec.div_const (ρ ^ 2))
      intro k
      apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
      linarith only [hdrop k, mul_nonneg (show 0 ≤ 2 * ρ by positivity) (hnonneg (k + 2))]
    simpa using hs.sqrt
  refine ⟨hres, ?_⟩
  have hgap : Tendsto gap atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 2).mp
    apply squeeze_zero (fun k => hnonneg _) _ (by
      simpa using hdec.div_const (2 * ρ))
    intro k
    apply (le_div_iff₀ (by positivity : 0 < 2 * ρ)).mpr
    linarith only [hdrop k, mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖r (k + 2)‖)]
  have hinner : Tendsto (fun k => ⟪ys, r k⟫_ℝ) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ys)).inner hres
  have hid (k : ℕ) : gap k - ⟪ys, r k⟫_ℝ + (f xs + g zs) = f (x k) + g (z k) := by
    dsimp only [gap]
    abel
  simpa only [hid, sub_zero, zero_add] using ((hgap.sub hinner).add_const (f xs + g zs))

end WantedExt.Analysis.Convex.ADMMConvergenceWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import MathlibExt.Analysis.InnerProductSpace.Opial

/-!
# Browder's demiclosedness principle in Hilbert spaces

A map `T : E → E` is **nonexpansive** when `dist (T x) (T y) ≤ dist x y`,
i.e. `LipschitzWith 1 T`. Browder's demiclosedness principle (F. E. Browder,
"Fixed-point theorems for noncompact mappings in Hilbert space",
Proc. Nat. Acad. Sci. USA 53 (1965), 1272--1276) says that `T - id` is
demiclosed at `0`: if `u n ⇀ x` weakly and `u n - T (u n) → 0`, then
`T x = x`. In other words, a weak limit of approximate fixed points is a
fixed point. The proof is a direct consequence of the squared-norm identity
behind Opial's property: writing `d = ‖x - T x‖` and
`ε n = ‖u n - T (u n)‖`, nonexpansiveness gives
`‖u n - T x‖ ≤ ‖u n - x‖ + ε n`, while the identity gives
`‖u n - T x‖² = ‖u n - x‖² + d² + 2 * re ⟪u n - x, x - T x⟫`; cancelling
`‖u n - x‖²` and letting `n → ∞` (the cross term tends to `0` by weak
convergence, and `‖u n - x‖ * ε n → 0` by boundedness) forces `d² ≤ 0`.

This is a companion to the Hilbert-space material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/` (Riesz representation,
orthogonal projection, spectral theory); it is not one of the 72 targets,
and it is not in pinned Mathlib or base MathlibExt.

Main results:

* `demiclosedness_of_lipschitzWith_one`: Browder's demiclosedness
  principle;
* `fixedPoint_of_weakly_tendsto_of_forall_fixedPoint`: the fixed-point set
  of a nonexpansive map is weakly sequentially closed.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.Demiclosedness

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Browder's demiclosedness principle**: if `T` is nonexpansive,
`u n ⇀ x` weakly, and `u n - T (u n) → 0`, then `T x = x`. -/
theorem demiclosedness_of_lipschitzWith_one (T : E → E) (hT : LipschitzWith 1 T)
    (u : ℕ → E) (x : E)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (hres : Tendsto (fun n => u n - T (u n)) atTop (𝓝 0)) :
    T x = x := by
  by_contra hne
  have hdpos : 0 < ‖x - T x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  -- The residual norms tend to `0`.
  have hε : Tendsto (fun n => ‖u n - T (u n)‖) atTop (𝓝 0) := by
    have h := hres.norm
    rwa [norm_zero] at h
  -- `‖u n - x‖` is bounded.
  obtain ⟨C, hC⟩ := Opial.bddAbove_norm_of_weakly_tendsto (𝕜 := 𝕜) u x hw
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC ⟨0, rfl⟩)
  have hbound : ∀ n, ‖u n - x‖ ≤ C + ‖x‖ := fun n =>
    le_trans (norm_sub_le _ _) (by have := hC ⟨n, rfl⟩; linarith)
  -- The product `‖u n - x‖ * ‖u n - T (u n)‖` tends to `0` by squeezing.
  have hprod : Tendsto (fun n => ‖u n - x‖ * ‖u n - T (u n)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro n
      exact mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    · have h := hε.const_mul (C + ‖x‖)
      rw [mul_zero] at h
      exact h
  have hε2 : Tendsto (fun n => ‖u n - T (u n)‖ ^ 2) atTop (𝓝 0) := by
    have h := hε.mul hε
    rw [mul_zero] at h
    exact h.congr (fun n => by rw [pow_two])
  -- The cross term tends to `0`.
  have hcross := Opial.tendsto_re_inner_sub_of_weakly_tendsto (𝕜 := 𝕜) u x hw (T x)
  -- Pointwise inequality: `d² + 2 * cross n ≤ 2 * ‖u n - x‖ * ε n + ε n²`.
  have hineq : ∀ n, ‖x - T x‖ ^ 2 +
      2 * RCLike.re ⟪u n - x, x - T x⟫_𝕜 ≤
      2 * (‖u n - x‖ * ‖u n - T (u n)‖) + ‖u n - T (u n)‖ ^ 2 := by
    intro n
    have hsplit : u n - T x = (u n - x) + (x - T x) := by abel
    have hexp : ‖u n - T x‖ ^ 2 = ‖u n - x‖ ^ 2 + 2 *
        RCLike.re ⟪u n - x, x - T x⟫_𝕜 + ‖x - T x‖ ^ 2 := by
      conv_lhs => rw [hsplit, norm_add_sq (𝕜 := 𝕜)]
    have hle : ‖u n - T x‖ ≤ ‖u n - x‖ + ‖u n - T (u n)‖ := by
      have h' : ‖T (u n) - T x‖ ≤ ‖u n - x‖ := by
        have h := hT.dist_le_mul (u n) x
        simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h
        exact h
      have htri : u n - T x = (u n - T (u n)) + (T (u n) - T x) := by abel
      calc ‖u n - T x‖ = ‖(u n - T (u n)) + (T (u n) - T x)‖ := by rw [htri]
        _ ≤ ‖u n - T (u n)‖ + ‖T (u n) - T x‖ := norm_add_le _ _
        _ ≤ ‖u n - T (u n)‖ + ‖u n - x‖ := add_le_add le_rfl h'
        _ = ‖u n - x‖ + ‖u n - T (u n)‖ := add_comm _ _
    have hsq : ‖u n - T x‖ ^ 2 ≤ (‖u n - x‖ + ‖u n - T (u n)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hexpand : (‖u n - x‖ + ‖u n - T (u n)‖) ^ 2 = ‖u n - x‖ ^ 2 +
        2 * (‖u n - x‖ * ‖u n - T (u n)‖) + ‖u n - T (u n)‖ ^ 2 := by ring
    rw [hexp, hexpand] at hsq
    linarith
  -- Pass to the limit: `d² ≤ 0`, contradicting `d > 0`.
  have hleft : Tendsto (fun n => ‖x - T x‖ ^ 2 +
      2 * RCLike.re ⟪u n - x, x - T x⟫_𝕜) atTop (𝓝 (‖x - T x‖ ^ 2 + 0)) := by
    have h := (tendsto_const_nhds (x := ‖x - T x‖ ^ 2)).add
      (hcross.const_mul (2 : ℝ))
    rw [mul_zero] at h
    exact h
  have hright : Tendsto (fun n => 2 * (‖u n - x‖ * ‖u n - T (u n)‖) +
      ‖u n - T (u n)‖ ^ 2) atTop (𝓝 (2 * 0 + 0)) := by
    have h := (hprod.const_mul (2 : ℝ)).add hε2
    exact h
  have hle_lim : ‖x - T x‖ ^ 2 + 0 ≤ 2 * 0 + 0 :=
    le_of_tendsto_of_tendsto' hleft hright hineq
  simp only [add_zero, mul_zero] at hle_lim
  exact absurd hle_lim (not_le.mpr (sq_pos_of_pos hdpos))

/-- The fixed-point set of a nonexpansive map is weakly sequentially
closed: if every `u n` is a fixed point of `T` and `u n ⇀ x` weakly,
then `T x = x`. -/
theorem fixedPoint_of_weakly_tendsto_of_forall_fixedPoint (T : E → E)
    (hT : LipschitzWith 1 T) (u : ℕ → E) (x : E)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (hfix : ∀ n, T (u n) = u n) :
    T x = x := by
  apply demiclosedness_of_lipschitzWith_one T hT u x hw
  have : (fun n => u n - T (u n)) = fun _ => (0 : E) := by
    funext n
    rw [hfix n, sub_self]
  rw [this]
  exact tendsto_const_nhds

end MathlibExt.Analysis.InnerProductSpace.Demiclosedness

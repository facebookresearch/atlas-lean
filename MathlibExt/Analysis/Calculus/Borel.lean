/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.SmoothSeries

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/

namespace MathlibExt.Analysis.Calculus.BorelWanted

open scoped Topology ContDiff

/-- A fixed smooth bump function: equal to `1` on `[-1,1]`, supported in `(-2,2)`. -/
private noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The polynomial `yᵐ` multiplied by the fixed bump. Smooth with compact support. -/
private noncomputable def poly (m : ℕ) : ℝ → ℝ := fun y => y ^ m * bump y

private lemma contDiff_poly (m : ℕ) : ContDiff ℝ ∞ (poly m) := by
  unfold poly
  exact (contDiff_id.pow m).mul bump.contDiff

private lemma hasCompactSupport_poly (m : ℕ) : HasCompactSupport (poly m) := by
  unfold poly
  exact bump.hasCompactSupport.mul_left

/-- A uniform bound for the iterated derivatives of `poly m` up to order `m`. -/
private noncomputable def polyBound (m : ℕ) : ℝ :=
  Classical.choose ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)

private lemma polyBound_nonneg (m : ℕ) : 0 ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).1

private lemma norm_iteratedFDeriv_poly_le {m i : ℕ} (hi : i ≤ m) (y : ℝ) :
    ‖iteratedFDeriv ℝ i (poly m) y‖ ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).2 i hi y

/-- The `m`-th Taylor coefficient we want to realize, `aₘ / m!`. -/
private noncomputable def coeff (a : ℕ → ℝ) (m : ℕ) : ℝ := a m / (Nat.factorial m : ℝ)

/-- The radius of the `m`-th cutoff, chosen small enough to control the derivatives. -/
private noncomputable def radius (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  min 1 ((1 / 2) ^ m / (|coeff a m| * polyBound m + 1))

private lemma radius_pos (a : ℕ → ℝ) (m : ℕ) : 0 < radius a m := by
  apply lt_min one_pos
  have h := polyBound_nonneg m
  have hden : 0 < |coeff a m| * polyBound m + 1 := by
    have : 0 ≤ |coeff a m| * polyBound m := mul_nonneg (abs_nonneg _) h
    linarith
  exact div_pos (pow_pos (by norm_num) m) hden

private lemma radius_le_one (a : ℕ → ℝ) (m : ℕ) : radius a m ≤ 1 := min_le_left _ _

private lemma radius_bound (a : ℕ → ℝ) (m : ℕ) :
    |coeff a m| * polyBound m * radius a m ≤ (1 / 2) ^ m := by
  have h := polyBound_nonneg m
  have hD : 0 ≤ |coeff a m| * polyBound m := mul_nonneg (abs_nonneg _) h
  have hden : 0 < |coeff a m| * polyBound m + 1 := by linarith
  have hr : radius a m ≤ (1 / 2) ^ m / (|coeff a m| * polyBound m + 1) := min_le_right _ _
  have hpow : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
  calc |coeff a m| * polyBound m * radius a m
      ≤ |coeff a m| * polyBound m * ((1 / 2) ^ m / (|coeff a m| * polyBound m + 1)) :=
        mul_le_mul_of_nonneg_left hr hD
    _ ≤ (1 / 2) ^ m := by
        rw [← mul_div_assoc, div_le_iff₀ hden]
        nlinarith [hpow]

/-- The `m`-th summand: `(aₘ/m!)·xᵐ·bump(x/rₘ)`. -/
private noncomputable def g (a : ℕ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => coeff a m * x ^ m * bump ((radius a m)⁻¹ * x)

private lemma g_eq_scaled (a : ℕ → ℝ) (m : ℕ) :
    g a m = fun x => coeff a m * radius a m ^ m * poly m ((radius a m)⁻¹ * x) := by
  funext x
  have hr : radius a m ≠ 0 := (radius_pos a m).ne'
  simp only [g, poly, mul_pow]
  rw [show coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ m * x ^ m * bump ((radius a m)⁻¹ * x))
        = coeff a m * (radius a m ^ m * (radius a m)⁻¹ ^ m) *
            (x ^ m * bump ((radius a m)⁻¹ * x)) from by ring,
      ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
  ring

private lemma g_contDiff (a : ℕ → ℝ) (m : ℕ) : ContDiff ℝ ∞ (g a m) := by
  unfold g
  exact (contDiff_const.mul (contDiff_id.pow m)).mul
    (bump.contDiff.comp (contDiff_const.mul contDiff_id))

private lemma g_hasCompactSupport (a : ℕ → ℝ) (m : ℕ) : HasCompactSupport (g a m) := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) (2 * radius a m))
    (isCompact_closedBall _ _)
  intro x hx
  have hr : 0 < radius a m := radius_pos a m
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  have hb : bump ((radius a m)⁻¹ * x) = 0 := by
    apply bump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr]
    change (2 : ℝ) ≤ (radius a m)⁻¹ * |x|
    rw [le_inv_mul_iff₀ hr]
    linarith
  simp only [g, hb, mul_zero]

/-- A uniform bound for the `k`-th derivative of `g a m`, from compact support. -/
private noncomputable def gBound (a : ℕ → ℝ) (m k : ℕ) : ℝ :=
  Classical.choose ((g_hasCompactSupport a m).exists_bound_iteratedFDeriv (g_contDiff a m) k)

private lemma norm_iteratedFDeriv_g_le_gBound (a : ℕ → ℝ) (m k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ gBound a m k :=
  (Classical.choose_spec
    ((g_hasCompactSupport a m).exists_bound_iteratedFDeriv (g_contDiff a m) k)).2 k le_rfl x

private lemma iteratedDeriv_g (a : ℕ → ℝ) (m k : ℕ) (x : ℝ) :
    iteratedDeriv k (g a m) x
      = coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ k * iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)) := by
  rw [g_eq_scaled, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul ((contDiff_poly m).of_le (by exact_mod_cast le_top))]

private lemma norm_iteratedFDeriv_g_le_of_lt (a : ℕ → ℝ) {k m : ℕ} (hkm : k < m) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ (1 / 2) ^ m := by
  have hR : 0 < radius a m := radius_pos a m
  have hle1 : radius a m ≤ 1 := radius_le_one a m
  have hD : ‖iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)‖ ≤ polyBound m := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedFDeriv_poly_le hkm.le _
  have key : radius a m ^ m * (radius a m)⁻¹ ^ k = radius a m ^ (m - k) := by
    rw [inv_pow, ← div_eq_mul_inv, eq_comm, eq_div_iff (pow_ne_zero k hR.ne'), ← pow_add,
      Nat.sub_add_cancel hkm.le]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_g]
  rw [show coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ k * iteratedDeriv k (poly m) ((radius a m)⁻¹ * x))
        = coeff a m * (radius a m ^ m * (radius a m)⁻¹ ^ k) *
            iteratedDeriv k (poly m) ((radius a m)⁻¹ * x) from by ring, key]
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (radius a m ^ (m - k)),
    abs_of_nonneg (pow_nonneg hR.le _)]
  calc |coeff a m| * radius a m ^ (m - k) *
        ‖iteratedDeriv k (poly m) ((radius a m)⁻¹ * x)‖
      ≤ |coeff a m| * radius a m ^ (m - k) * polyBound m := by
        apply mul_le_mul_of_nonneg_left hD
        exact mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _)
    _ = |coeff a m| * polyBound m * radius a m ^ (m - k) := by ring
    _ ≤ |coeff a m| * polyBound m * radius a m := by
        apply mul_le_mul_of_nonneg_left
          (pow_le_of_le_one hR.le hle1 (Nat.sub_ne_zero_of_lt hkm))
        exact mul_nonneg (abs_nonneg _) (polyBound_nonneg m)
    _ ≤ (1 / 2) ^ m := radius_bound a m

private lemma g_eventuallyEq (a : ℕ → ℝ) (m : ℕ) :
    g a m =ᶠ[𝓝 (0 : ℝ)] fun x => coeff a m * x ^ m := by
  have hcont : Continuous (fun x : ℝ => (radius a m)⁻¹ * x) := continuous_const.mul continuous_id
  have htend : Filter.Tendsto (fun x : ℝ => (radius a m)⁻¹ * x) (𝓝 0) (𝓝 0) :=
    hcont.tendsto' 0 0 (by simp)
  have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), bump ((radius a m)⁻¹ * x) = 1 := by
    have := htend.eventually bump.eventuallyEq_one
    filter_upwards [this] with x hx
    simpa using hx
  filter_upwards [h1] with x hx
  simp only [g]
  rw [hx, mul_one]

private lemma iteratedDeriv_g_zero (a : ℕ → ℝ) (n m : ℕ) :
    iteratedDeriv n (g a m) 0 = if n = m then a n else 0 := by
  rw [(g_eventuallyEq a m).iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst h
    simp only [coeff]
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  · simp

/--
**Borel's lemma.** For every sequence $(a_n)_{n \ge 0}$ of real numbers there is an infinitely
differentiable function $f : \mathbb{R} \to \mathbb{R}$ whose derivatives at $0$ are
$f^{(n)}(0) = a_n$ for every $n \ge 0$.

Proves `Wanted` entry `borel_jet_real`.

Source: E. Borel, Ann. Sci. Ec. Norm. Sup. (3) 12 (1895), 9-55, DOI 10.24033/asens.406.
-/
theorem borel_jet_real
    (a : ℕ → ℝ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ n : ℕ, iteratedDeriv n f 0 = a n := by
  classical
  set v : ℕ → ℕ → ℝ := fun k m => if m ≤ k then gBound a m k else (1 / 2) ^ m with hv_def
  have hv_summable : ∀ k, Summable (v k) := by
    intro k
    have hgeo : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [← summable_nat_add_iff (k + 1)]
    have heq : (fun n => v k (n + (k + 1))) = fun n => (1 / 2 : ℝ) ^ (n + (k + 1)) := by
      funext n
      simp only [hv_def]
      rw [ite_eq_right (by omega)]
    rw [heq]
    exact (summable_nat_add_iff (k + 1)).mpr hgeo
  have hbound : ∀ k m x, ‖iteratedFDeriv ℝ k (g a m) x‖ ≤ v k m := by
    intro k m x
    simp only [hv_def]
    by_cases hmk : m ≤ k
    · rw [ite_eq_left hmk]
      exact norm_iteratedFDeriv_g_le_gBound a m k x
    · rw [ite_eq_right hmk]
      exact norm_iteratedFDeriv_g_le_of_lt a (by omega) x
  refine ⟨fun x => ∑' m, g a m x, ?_, ?_⟩
  · exact contDiff_tsum (fun m => g_contDiff a m) (fun k _ => hv_summable k)
      (fun k m x _ => hbound k m x)
  · intro n
    have hsummable_fderiv : Summable (fun m => iteratedFDeriv ℝ n (g a m) 0) :=
      Summable.of_norm_bounded (hv_summable n) (fun m => hbound n m 0)
    have heq : iteratedFDeriv ℝ n (fun x => ∑' m, g a m x) 0
        = ∑' m, iteratedFDeriv ℝ n (g a m) 0 :=
      iteratedFDeriv_tsum_apply (fun m => g_contDiff a m) (fun k _ => hv_summable k)
        (fun k m x _ => hbound k m x) le_top 0
    rw [iteratedDeriv_eq_iteratedFDeriv, heq,
      ContinuousMultilinearMap.tsum_eval hsummable_fderiv]
    simp_rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_g_zero]
    rw [tsum_eq_single n (fun m hm => ite_eq_right fun h => hm h.symm), ite_eq_left rfl]

end MathlibExt.Analysis.Calculus.BorelWanted

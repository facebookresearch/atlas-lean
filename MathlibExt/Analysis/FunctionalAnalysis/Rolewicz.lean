/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
public import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex
public import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rolewicz's theorem: multiples of the backward shift are hypercyclic

Let `B` be the backward shift on `ℓ²(ℕ, 𝕜)`, `(B x) n = x (n + 1)`.
*Rolewicz's theorem* (1969) says that the scalar multiple `μ • B` is
hypercyclic — it has an orbit that is dense in `ℓ²(ℕ, 𝕜)` — if and only
if `‖μ‖ > 1`. The forward direction is a boundedness argument: if
`‖μ‖ ≤ 1` then every orbit is contained in the closed ball of radius
`‖x‖` around `0`, so no orbit can be dense. The reverse direction is
the hypercyclicity criterion from `Hypercyclicity.lean`, applied with
`X₀ = Y₀` the span of the single-coordinate vectors (finitely
supported sequences) and `S n y = (μ ^ n)⁻¹ • Fⁿ y`, where `F` is the
forward shift: `Bⁿ` kills finitely supported vectors eventually,
`(‖μ‖⁻¹) ^ n → 0` since `‖μ‖ > 1`, and `Bⁿ Fⁿ = 1`.
The generalized criterion is used with `n_k = id`; the exact inverse
identity supplies its required convergence to `y`.

The countable dense set required by the criterion comes from
`SeparableHilbertBasis.separableSpace_of_countable_hilbertBasis`, applied to
the default Hilbert basis of `ℓ²(ℕ, 𝕜)`, and
`TopologicalSpace.exists_countable_dense`.

This is a companion to the Baire-category, bounded-operator, and
Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`. It is not one of the
72 v1 targets. The proof uses the canonical shifts from `LpShiftOperator`
and their power formulas and left-inverse identity from `ShiftFredholmIndex`,
together with the hypercyclicity criterion above. Classical reference: S. Rolewicz,
"On orbits of elements", *Studia Math.* 32 (1969), 17–22; see also
F. Bayart and É. Matheron, *Dynamics of Linear Operators*, Cambridge
University Press, 2009, Example 1.8.

## Main declarations

* `LpShiftOperator.shiftCLM` / `LpShiftOperator.backwardCLM` : the
  canonical forward and backward shifts used by this proof.
* `ShiftFredholmIndex.shiftCLM_pow_apply` and
  `ShiftFredholmIndex.backwardCLM_pow_apply` : the reused coordinate powers.
* `isHypercyclic_smul_backwardShiftCLM_iff` : Rolewicz's theorem.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.Rolewicz

open Filter Topology Set Metric
open MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
open MathlibExt.Analysis.InnerProductSpace
open scoped _root_.lp ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Norms and scalar multiples of canonical shift powers -/

/-- Powers of the forward shift preserve norms. -/
theorem norm_forwardShiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(LpShiftOperator.shiftCLM ^ n) x‖ = ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, LpShiftOperator.norm_shiftCLM_apply]

/-- Powers of the backward shift do not increase norms. -/
theorem norm_backwardShiftCLM_pow_apply_le (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(LpShiftOperator.backwardCLM ^ n) x‖ ≤ ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact le_trans (ih (LpShiftOperator.backwardCLM x))
      (LpShiftOperator.norm_backwardLinMap_apply_le x)

/-- Powers of a scalar multiple of the backward shift, applied pointwise. -/
theorem smul_backwardShiftCLM_pow_apply (μ : 𝕜) (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (((μ • LpShiftOperator.backwardCLM) ^ n) x) = μ ^ n • (LpShiftOperator.backwardCLM ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc (((μ • LpShiftOperator.backwardCLM) ^ (n + 1)) x)
        = ((μ • LpShiftOperator.backwardCLM) ^ n) ((μ • LpShiftOperator.backwardCLM) x) := by
          rw [pow_succ, mul_apply_eq_comp]
      _ = μ ^ n • (LpShiftOperator.backwardCLM ^ n) ((μ • LpShiftOperator.backwardCLM) x) := by
          rw [ih]
      _ = μ ^ n • (LpShiftOperator.backwardCLM ^ n) (μ • LpShiftOperator.backwardCLM x) := by rfl
      _ = μ ^ n • (μ • (LpShiftOperator.backwardCLM ^ n) (LpShiftOperator.backwardCLM x)) := by
          rw [map_smul]
      _ = (μ ^ n * μ) • (LpShiftOperator.backwardCLM ^ n) (LpShiftOperator.backwardCLM x) := by
          rw [smul_smul]
      _ = μ ^ (n + 1) • (LpShiftOperator.backwardCLM ^ (n + 1)) x := by
          have h1 : μ ^ (n + 1) = μ ^ n * μ := pow_succ _ _
          have h2 : (LpShiftOperator.backwardCLM ^ (n + 1)) x =
              (LpShiftOperator.backwardCLM ^ n) (LpShiftOperator.backwardCLM x) := by
            rw [pow_succ, mul_apply_eq_comp]
          rw [h1, h2]

/-! ### Finitely supported vectors -/

/-- The span of the single-coordinate vectors is dense in `ℓ²(ℕ, 𝕜)`:
every vector is the sum of its canonical series. -/
theorem dense_span_single :
    Dense (↑(Submodule.span 𝕜
      (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜))) := by
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  refine mem_closure_of_tendsto
    ((lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat) ?_
  refine Eventually.of_forall fun s => ?_
  exact sum_mem fun i _ => by
    have h : lp.single (E := fun _ : ℕ => 𝕜) 2 i ((x : ℕ → 𝕜) i) =
        (x : ℕ → 𝕜) i • lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) := by
      rw [← lp.single_smul]
      simp [smul_eq_mul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Every vector in the span of the single-coordinate vectors is
eventually zero: it has finite support. -/
theorem exists_forall_eq_zero_of_mem_span_single {x : ℓ²(ℕ, 𝕜)}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun i => lp.single 2 i (1 : 𝕜))) :
    ∃ N, ∀ i, N ≤ i → (x : ℕ → 𝕜) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨i + 1, fun j hj => ?_⟩
    change (↑(lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) : ℕ → 𝕜) j = 0
    exact lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜) (by omega : j ≠ i)
  | zero => exact ⟨0, fun _ _ => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, h₁⟩ := hy
    obtain ⟨N₂, h₂⟩ := hz
    refine ⟨max N₁ N₂, fun i hi => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, h₁ i (le_trans (le_max_left _ _) hi),
      h₂ i (le_trans (le_max_right _ _) hi), add_zero]
  | smul c y _ hy =>
    obtain ⟨N, hN⟩ := hy
    exact ⟨N, fun i hi => by rw [lp.coeFn_smul, Pi.smul_apply, hN i hi, smul_zero]⟩

/-! ### Rolewicz's theorem -/

/-- **Rolewicz's theorem.** The scalar multiple `μ • B` of the backward
shift on `ℓ²(ℕ, 𝕜)` is hypercyclic if and only if `‖μ‖ > 1`. -/
theorem isHypercyclic_smul_backwardShiftCLM_iff (μ : 𝕜) :
    IsHypercyclic ((μ • LpShiftOperator.backwardCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))) ↔ 1 < ‖μ‖ := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx⟩ := h
    have hbound : ∀ n, ‖((μ • LpShiftOperator.backwardCLM) ^ n) x‖ ≤ ‖x‖ := by
      intro n
      rw [smul_backwardShiftCLM_pow_apply, norm_smul, norm_pow]
      calc ‖μ‖ ^ n * ‖(LpShiftOperator.backwardCLM ^ n) x‖
          ≤ (1 : ℝ) * ‖x‖ :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hlt)
              (norm_backwardShiftCLM_pow_apply_le n x) (norm_nonneg _) zero_le_one
        _ = ‖x‖ := one_mul _
    have hmem : ((‖x‖ + 1 : ℝ) : 𝕜) • lp.single 2 0 (1 : 𝕜) ∈
        closure (Set.range fun n => ((μ • LpShiftOperator.backwardCLM) ^ n) x) := by
      rw [hx.closure_eq]
      exact Set.mem_univ _
    have hsub : closure (Set.range fun n => ((μ • LpShiftOperator.backwardCLM) ^ n) x) ⊆
        Metric.closedBall 0 ‖x‖ := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      rintro y ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hbound n
    have hle := hsub hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)] at hle
    linarith [norm_nonneg x]
  · intro hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hμ
      exact (by norm_num : ¬ (1 : ℝ) < 0) hμ
    let : TopologicalSpace.SeparableSpace (ℓ²(ℕ, 𝕜)) :=
      SeparableHilbertBasis.separableSpace_of_countable_hilbertBasis
        (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜))
    obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (ℓ²(ℕ, 𝕜))
    refine isHypercyclic_of_criterion _ id tendsto_id D
      (↑(Submodule.span 𝕜
        (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜)))
      (↑(Submodule.span 𝕜
        (Set.range fun i => (lp.single 2 i (1 : 𝕜) : ℓ²(ℕ, 𝕜)))) : Set (ℓ²(ℕ, 𝕜)))
      hDcount hDdense
      dense_span_single dense_span_single
      (fun n y => (μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y) ?_ ?_ ?_
    · intro x hx
      change Tendsto (fun n => ((μ • LpShiftOperator.backwardCLM) ^ n) x) atTop (𝓝 0)
      have hx' : x ∈ Submodule.span 𝕜 (Set.range fun i => lp.single 2 i (1 : 𝕜)) := hx
      obtain ⟨N, hN⟩ := exists_forall_eq_zero_of_mem_span_single hx'
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hzero : (LpShiftOperator.backwardCLM ^ n) x = 0 := by
        apply lp.ext
        funext i
        rw [ShiftFredholmIndex.backwardCLM_pow_apply]
        exact hN (i + n) (by omega)
      rw [smul_backwardShiftCLM_pow_apply, hzero, smul_zero]
    · intro y _
      change Tendsto (fun n => (μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y) atTop (𝓝 0)
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hnormlim : Tendsto
        (fun n => ‖(μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y‖) atTop (𝓝 0) := by
        have hnorm : ∀ n, ‖(μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y‖ = (‖μ‖⁻¹) ^ n * ‖y‖ := by
          intro n
          rw [norm_smul, norm_inv, norm_pow, inv_pow, norm_forwardShiftCLM_pow_apply]
        simp_rw [hnorm]
        have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one
          (inv_nonneg.mpr (norm_nonneg μ)) (inv_lt_one_of_one_lt₀ hμ)).mul_const ‖y‖
        simpa using hlim
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hnormlim) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
      rwa [dist_zero_right]
    · intro y _
      have hconstant :
          (fun n => ((μ • LpShiftOperator.backwardCLM) ^ n)
            ((μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y)) = fun _ => y := by
        funext n
        change ((μ • LpShiftOperator.backwardCLM) ^ n)
          ((μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y) = y
        have hBS : (LpShiftOperator.backwardCLM (𝕜 := 𝕜) ^ n)
            ((LpShiftOperator.shiftCLM (𝕜 := 𝕜) ^ n) y) = y := by
          simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
            DFunLike.congr_fun (ShiftFredholmIndex.backwardCLM_pow_comp_shiftCLM_pow n) y
        rw [smul_backwardShiftCLM_pow_apply, map_smul,
          hBS, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero n hμ0), one_smul]
      change Tendsto
        (fun n => ((μ • LpShiftOperator.backwardCLM) ^ n)
          ((μ ^ n)⁻¹ • (LpShiftOperator.shiftCLM ^ n) y)) atTop (𝓝 y)
      rw [hconstant]
      exact tendsto_const_nhds

end MathlibExt.Analysis.FunctionalAnalysis.Rolewicz

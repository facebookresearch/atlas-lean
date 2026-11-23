/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap

import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Composition operators on `ℓ²(ℕ, 𝕜)`

For a map `ψ : ℕ → ℕ`, the composition operator `C_ψ` precomposes a
square-summable sequence with `ψ`: `(C_ψ x) n = x (ψ n)`. It is bounded
exactly when the fibers of `ψ` are uniformly bounded: if every value is
taken at most `M` times, then `‖C_ψ x‖² ≤ M * ‖x‖²`, by regrouping the
sum over fibers. In that case the operator norm is the square root of the
largest fiber count, the adjoint is the fiber-sum operator
`((C_ψ)† y) m = ∑_{n ∈ ψ⁻¹'{m}} y n`, composition of operators is
composition of symbols in the reversed order, a permutation symbol gives a
unitary operator, `C_ψ` is injective iff `ψ` is surjective and surjective
iff `ψ` is injective, and `C_ψ` is never compact.

This is a companion to the Hilbert-space / operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem, the Fredholm alternative, the Green's operator).
It is not one of the 72 v1 targets, and it is not in the pinned Mathlib or
in base MathlibExt: Mathlib has the `ℓ²` space and its inner product, but
no composition operator on it. See e.g. Conway, *A Course in Functional
Analysis*, or Nordgren, "Composition operators", for the classical theory.

## Main declarations

* `HasBoundedFibers ψ M` : every fiber of `ψ` is finite and has at most `M`
  elements.
* `fiberCard ψ m hfin` : the number of preimages of `m` under `ψ`, with
  evidence that this fiber is finite.
* `fiberSup ψ hψ` : the real supremum of the fiber counts of `ψ`, with
  evidence of uniformly bounded finite fibers.
* `compCLM (𝕜 := 𝕜) ψ hψ` : the composition operator as a bounded operator on
  `ℓ²(ℕ, 𝕜)`.
* `norm_compCLM` : `‖C_ψ‖ = √(fiberSup ψ hψ)`.
* `adjoint_compCLM_apply` : `((C_ψ)† y) m = ∑_{n ∈ ψ⁻¹'{m}} y n`.
* `compCLM_comp` : `C_φ ∘L C_ψ = C_{ψ ∘ φ}`.
* `compCLM_mem_unitary` : a permutation symbol gives a unitary operator.
* `injective_compCLM_iff`, `surjective_compCLM_iff` : the
  injectivity / surjectivity criteria.
* `not_isCompactOperator_compCLM` : `C_ψ` is never compact.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.CompositionOperator

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The fibers of `ψ` are finite and uniformly bounded by `M`: every value
is taken at most `M` times. This is the boundedness hypothesis for the
composition operator. -/
def HasBoundedFibers (ψ : ℕ → ℕ) (M : ℕ) : Prop :=
  ∀ m, (ψ ⁻¹' {m}).Finite ∧ (ψ ⁻¹' {m}).ncard ≤ M

/-- The number of preimages of `m` under `ψ`, defined for a finite fiber. -/
noncomputable def fiberCard (ψ : ℕ → ℕ) (m : ℕ) (hfin : (ψ ⁻¹' {m}).Finite) : ℕ :=
  hfin.toFinset.card

/-- On its finite domain, the fiber count agrees with the standard natural cardinality. -/
@[simp] theorem fiberCard_eq_ncard (ψ : ℕ → ℕ) (m : ℕ) (hfin : (ψ ⁻¹' {m}).Finite) :
    fiberCard ψ m hfin = (ψ ⁻¹' {m}).ncard :=
  (Set.ncard_eq_toFinset_card _ hfin).symm

/-- The real supremum of the fiber counts of `ψ`, defined for uniformly bounded finite
fibers. The bound in `hψ` ensures that the real-valued family is bounded above. -/
noncomputable def fiberSup (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) : ℝ :=
  ⨆ m, (fiberCard ψ m (hψ m).1 : ℝ)

/-- On its bounded finite domain, the fiber supremum agrees with the supremum of natural
cardinalities. Its value is independent of the chosen bound and evidence. -/
theorem fiberSup_eq_iSup (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    fiberSup ψ hψ = ⨆ m, ((ψ ⁻¹' {m}).ncard : ℝ) := by
  simp only [fiberSup, fiberCard_eq_ncard]

/-- The composition function: precompose a sequence with `ψ`. -/
def compFun (ψ : ℕ → ℕ) (x : ℕ → 𝕜) (n : ℕ) : 𝕜 := x (ψ n)

/-- The key estimate, at the level of finite partial sums: regrouping the
sum over the fibers of `ψ` bounds `∑_{n ∈ s} ‖x (ψ n)‖²` by `B` times the
total sum, whenever `B` bounds every fiber count. -/
private theorem sum_finset_compFun_norm_sq_le (ψ : ℕ → ℕ)
    (hfin : ∀ m, (ψ ⁻¹' {m}).Finite) {B : ℝ} (hB : ∀ m, ((ψ ⁻¹' {m}).ncard : ℝ) ≤ B)
    (x : ℓ²(ℕ, 𝕜)) (s : Finset ℕ) :
    ∑ n ∈ s, ‖(x : ℕ → 𝕜) (ψ n)‖ ^ (2 : ℝ) ≤ B * ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have hsum : Summable (fun m => ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ)) := by
    have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa only [h2] using h
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) (hB 0)
  have hmaps : ∀ i ∈ s, ψ i ∈ s.image ψ := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun m => ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ))]
  calc ∑ j ∈ s.image ψ, ∑ _i ∈ s.filter (ψ · = j), ‖(x : ℕ → 𝕜) j‖ ^ (2 : ℝ)
      = ∑ j ∈ s.image ψ, ((s.filter (ψ · = j)).card : ℝ) * ‖(x : ℕ → 𝕜) j‖ ^ (2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ s.image ψ, B * ‖(x : ℕ → 𝕜) j‖ ^ (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hsub : (↑(s.filter (ψ · = j)) : Set ℕ) ⊆ ψ ⁻¹' {j} := by
          intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter] at hi
          simpa using hi.2
        have hcard : ((s.filter (ψ · = j)).card : ℝ) ≤ B := by
          have h1 : ((s.filter (ψ · = j)).card : ℝ) ≤ ((ψ ⁻¹' {j}).ncard : ℝ) := by
            have hfin' : (↑(s.filter (ψ · = j)) : Set ℕ).ncard
                = (s.filter (ψ · = j)).card :=
              Set.ncard_coe_finset _
            rw [← hfin']
            exact Nat.cast_le.mpr (Set.ncard_le_ncard hsub (hfin j))
          exact h1.trans (hB j)
        exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (norm_nonneg _) _)
    _ = B * ∑ j ∈ s.image ψ, ‖(x : ℕ → 𝕜) j‖ ^ (2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ B * ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        exact hsum.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)

/-- The composed sequence of an `ℓ²` sequence is in `ℓ²`, under the bounded
fibers hypothesis. -/
theorem memℓp_compFun (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) : Memℓp (compFun ψ (x : ℕ → 𝕜)) 2 := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  refine memℓp_gen' (C := (M : ℝ) * ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ)) ?_
  intro s
  show ∑ _i ∈ s, ‖(x : ℕ → 𝕜) (ψ _i)‖ ^ (2 : ℝ≥0∞).toReal
    ≤ (M : ℝ) * ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ)
  rw [h2]
  exact sum_finset_compFun_norm_sq_le ψ (fun m => (hψ m).1)
    (fun m => Nat.cast_le.mpr (hψ m).2) x s

/-- The squared-norm sum of the composed sequence is at most `fiberSup ψ hψ`
times the squared-norm sum of the original sequence. -/
theorem tsum_compFun_norm_sq_le (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) :
    ∑' n, ‖(x : ℕ → 𝕜) (ψ n)‖ ^ (2 : ℝ)
      ≤ fiberSup ψ hψ * ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ) := by
  have hB : ∀ m, ((ψ ⁻¹' {m}).ncard : ℝ) ≤ fiberSup ψ hψ := by
    intro m
    rw [fiberSup_eq_iSup]
    apply le_ciSup _ m
    exact ⟨(M : ℝ), fun _ ⟨k, hk⟩ => hk ▸ Nat.cast_le.mpr (hψ k).2⟩
  exact Real.tsum_le_of_sum_le (fun n => Real.rpow_nonneg (norm_nonneg _) _)
    (fun s => sum_finset_compFun_norm_sq_le ψ (fun m => (hψ m).1) hB x s)

/-- The composition operator as a linear map. -/
noncomputable def compLinMap (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨compFun ψ (x : ℕ → 𝕜), memℓp_compFun ψ hψ x⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [compFun, lp.coeFn_add, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [compFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- Pointwise action of the composition linear map. -/
theorem compLinMap_apply (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) (i : ℕ) : compLinMap ψ hψ x i = (x : ℕ → 𝕜) (ψ i) :=
  rfl

/-- The squared norm of `C_ψ x` is at most `fiberSup ψ hψ * ‖x‖²`. -/
theorem norm_sq_compLinMap_apply_le (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) :
    ‖compLinMap ψ hψ x‖ ^ (2 : ℝ) ≤ fiberSup ψ hψ * ‖x‖ ^ (2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have htsum_x : ∑' m, ‖(x : ℕ → 𝕜) m‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℝ) := by
    have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
    rw [h2] at h
    exact h.symm
  have htsum_c : ‖compLinMap ψ hψ x‖ ^ (2 : ℝ)
      = ∑' n, ‖(x : ℕ → 𝕜) (ψ n)‖ ^ (2 : ℝ) := by
    have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (compLinMap ψ hψ x)
    rw [h2] at h
    rw [h]
    apply tsum_congr
    intro n
    rw [compLinMap_apply]
  rw [htsum_c, ← htsum_x]
  exact tsum_compFun_norm_sq_le ψ hψ x

/-- `fiberSup ψ hψ` is nonnegative. -/
theorem fiberSup_nonneg (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    0 ≤ fiberSup ψ hψ := by
  rw [fiberSup_eq_iSup]
  exact le_trans (Nat.cast_nonneg _)
    (le_ciSup ⟨(M : ℝ), fun _ ⟨k, hk⟩ => hk ▸ Nat.cast_le.mpr (hψ k).2⟩ 0)

/-- The composition operator is bounded by `√(fiberSup ψ hψ)`. -/
theorem norm_compLinMap_apply_le (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) :
    ‖compLinMap ψ hψ x‖ ≤ Real.sqrt (fiberSup ψ hψ) * ‖x‖ := by
  have hS : 0 ≤ fiberSup ψ hψ := fiberSup_nonneg ψ hψ
  have h := norm_sq_compLinMap_apply_le ψ hψ x
  rw [Real.rpow_two, Real.rpow_two] at h
  calc ‖compLinMap ψ hψ x‖ = Real.sqrt (‖compLinMap ψ hψ x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (fiberSup ψ hψ * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (fiberSup ψ hψ) * ‖x‖ := by
        rw [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)]

/-- The composition operator as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def compCLM (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  (compLinMap ψ hψ).mkContinuous (Real.sqrt (fiberSup ψ hψ))
    (norm_compLinMap_apply_le ψ hψ)

/-- Pointwise action of the composition operator. -/
theorem compCLM_apply (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) (i : ℕ) : compCLM (𝕜 := 𝕜) ψ hψ x i = (x : ℕ → 𝕜) (ψ i) :=
  rfl

/-- The composition operator is bounded by `√(fiberSup ψ hψ)` on every vector. -/
theorem norm_compCLM_apply_le (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (x : ℓ²(ℕ, 𝕜)) :
    ‖compCLM (𝕜 := 𝕜) ψ hψ x‖ ≤ Real.sqrt (fiberSup ψ hψ) * ‖x‖ :=
  norm_compLinMap_apply_le ψ hψ x

/-- The operator norm of `C_ψ` is at most `√(fiberSup ψ hψ)`. -/
theorem norm_compCLM_le (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    ‖compCLM (𝕜 := 𝕜) ψ hψ‖ ≤ Real.sqrt (fiberSup ψ hψ) := by
  show ‖(compLinMap ψ hψ).mkContinuous (Real.sqrt (fiberSup ψ hψ))
      (norm_compLinMap_apply_le ψ hψ)‖ ≤ Real.sqrt (fiberSup ψ hψ)
  exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
    (norm_compLinMap_apply_le ψ hψ)

/-- The norm of `C_ψ` applied to a standard basis vector is the square root
of the corresponding fiber count. -/
theorem norm_compCLM_single (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) (m : ℕ) :
    ‖compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜))‖ =
      Real.sqrt (fiberCard ψ m (hψ m).1 : ℝ) := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have htsum : ‖compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜))‖ ^ (2 : ℝ)
      = (fiberCard ψ m (hψ m).1 : ℝ) := by
    rw [fiberCard_eq_ncard]
    have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜)))
    rw [h2] at h
    rw [h]
    have hpt : ∀ n, ‖(compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜)) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ)
        = if ψ n = m then (1 : ℝ) else 0 := by
      intro n
      rw [compCLM_apply, lp.coeFn_single]
      split_ifs with hn
      · rw [hn, Pi.single_eq_same]
        simp
      · rw [Pi.single_eq_of_ne hn]
        simp
    rw [tsum_congr hpt]
    have hvanish : ∀ n ∉ Set.Finite.toFinset (hψ m).1,
        (if ψ n = m then (1 : ℝ) else 0) = 0 := by
      intro n hn
      rw [Set.Finite.mem_toFinset] at hn
      have hnm : ψ n ≠ m := fun hnm =>
        hn (by rwa [Set.mem_preimage, Set.mem_singleton_iff])
      simp [hnm]
    rw [tsum_eq_sum hvanish]
    have hsum : ∀ n ∈ Set.Finite.toFinset (hψ m).1,
        (if ψ n = m then (1 : ℝ) else 0) = 1 := by
      intro n hn
      rw [Set.Finite.mem_toFinset] at hn
      have hnm : ψ n = m := by rwa [Set.mem_preimage, Set.mem_singleton_iff] at hn
      simp [hnm]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← Set.ncard_eq_toFinset_card _ (hψ m).1]
  rw [Real.rpow_two] at htsum
  rw [← htsum, Real.sqrt_sq (norm_nonneg _)]

/-- The operator norm of the composition operator:
`‖C_ψ‖ = √(fiberSup ψ hψ)`, the square root of the largest fiber count. -/
theorem norm_compCLM (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    ‖compCLM (𝕜 := 𝕜) ψ hψ‖ = Real.sqrt (fiberSup ψ hψ) := by
  apply le_antisymm (norm_compCLM_le (𝕜 := 𝕜) ψ hψ)
  have hnn : 0 ≤ ‖compCLM (𝕜 := 𝕜) ψ hψ‖ := norm_nonneg _
  have hle : fiberSup ψ hψ ≤ ‖compCLM (𝕜 := 𝕜) ψ hψ‖ ^ 2 := by
    rw [fiberSup_eq_iSup]
    apply ciSup_le
    intro m
    have h1 : Real.sqrt (fiberCard ψ m (hψ m).1 : ℝ) ≤ ‖compCLM (𝕜 := 𝕜) ψ hψ‖ := by
      rw [← norm_compCLM_single (𝕜 := 𝕜) ψ hψ m]
      calc ‖compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜))‖
          ≤ ‖compCLM (𝕜 := 𝕜) ψ hψ‖ * ‖(lp.single 2 m (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ :=
            (compCLM (𝕜 := 𝕜) ψ hψ).le_opNorm _
        _ = ‖compCLM (𝕜 := 𝕜) ψ hψ‖ := by
            have hnorm1 : ‖(lp.single 2 m (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ = 1 := by
              rw [lp.norm_single (E := fun _ : ℕ => 𝕜) (p := 2) (by simp) m (1 : 𝕜),
                norm_one]
            rw [hnorm1, mul_one]
    have h3 : Real.sqrt (fiberCard ψ m (hψ m).1 : ℝ) ≤
        Real.sqrt (‖compCLM (𝕜 := 𝕜) ψ hψ‖ ^ 2) := by
      rwa [Real.sqrt_sq hnn]
    rw [fiberCard_eq_ncard] at h3
    exact (Real.sqrt_le_sqrt_iff (sq_nonneg _)).mp h3
  calc Real.sqrt (fiberSup ψ hψ) ≤ Real.sqrt (‖compCLM (𝕜 := 𝕜) ψ hψ‖ ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = ‖compCLM (𝕜 := 𝕜) ψ hψ‖ := Real.sqrt_sq hnn

/-- The adjoint of the composition operator is the fiber-sum operator:
`((C_ψ)† y) m` is the sum of `y` over the fiber of `m`. -/
theorem adjoint_compCLM_apply (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (y : ℓ²(ℕ, 𝕜)) (m : ℕ) :
    (((compCLM (𝕜 := 𝕜) ψ hψ)†) y) m
      = ∑ n ∈ Set.Finite.toFinset (hψ m).1, (y : ℕ → 𝕜) n := by
  have h1 : (⟪lp.single 2 m (1 : 𝕜), (((compCLM (𝕜 := 𝕜) ψ hψ)†) y)⟫_𝕜)
      = (((compCLM (𝕜 := 𝕜) ψ hψ)†) y) m := by
    rw [lp.inner_single_left]
    simp [RCLike.inner_apply]
  have h2 : (⟪lp.single 2 m (1 : 𝕜), (((compCLM (𝕜 := 𝕜) ψ hψ)†) y)⟫_𝕜)
      = ∑ n ∈ Set.Finite.toFinset (hψ m).1, (y : ℕ → 𝕜) n := by
    rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
    have hpt : ∀ n, ⟪((compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜))) : ℓ²(ℕ, 𝕜)) n,
        (y : ℕ → 𝕜) n⟫_𝕜 = if ψ n = m then (y : ℕ → 𝕜) n else 0 := by
      intro n
      rw [compCLM_apply, lp.coeFn_single]
      split_ifs with hn
      · rw [hn, Pi.single_eq_same]
        simp [RCLike.inner_apply]
      · rw [Pi.single_eq_of_ne hn]
        simp
    rw [tsum_congr hpt]
    have hvanish : ∀ n ∉ Set.Finite.toFinset (hψ m).1,
        (if ψ n = m then (y : ℕ → 𝕜) n else 0) = 0 := by
      intro n hn
      rw [Set.Finite.mem_toFinset] at hn
      have hnm : ψ n ≠ m := fun hnm =>
        hn (by rwa [Set.mem_preimage, Set.mem_singleton_iff])
      simp [hnm]
    rw [tsum_eq_sum hvanish]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    have hnm : ψ n = m := by rwa [Set.mem_preimage, Set.mem_singleton_iff] at hn
    simp [hnm]
  rw [h1] at h2
  exact h2

/-- Fiber bounds compose: the fibers of `ψ ∘ φ` are bounded by the product
of the bounds. -/
theorem hasBoundedFibers_comp {φ ψ : ℕ → ℕ} {Mφ Mψ : ℕ}
    (hφ : HasBoundedFibers φ Mφ) (hψ : HasBoundedFibers ψ Mψ) :
    HasBoundedFibers (ψ ∘ φ) (Mψ * Mφ) := by
  intro m
  have hset : (ψ ∘ φ) ⁻¹' {m}
      = ↑((Set.Finite.toFinset (hψ m).1).biUnion
          (fun k => Set.Finite.toFinset (hφ k).1)) := by
    ext n
    constructor
    · intro h
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply] at h
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨φ n, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        simpa using h
      · rw [Set.Finite.mem_toFinset]
        rfl
    · intro h
      rw [Finset.mem_coe, Finset.mem_biUnion] at h
      obtain ⟨k, hk, hkn⟩ := h
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hk hkn
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
      rw [hkn]
      exact hk
  constructor
  · rw [hset]
    exact Finset.finite_toSet _
  · rw [hset]
    have hcard : (↑((Set.Finite.toFinset (hψ m).1).biUnion
          (fun k => Set.Finite.toFinset (hφ k).1)) : Set ℕ).ncard
        = (((Set.Finite.toFinset (hψ m).1).biUnion
          (fun k => Set.Finite.toFinset (hφ k).1)).card) :=
      Set.ncard_coe_finset _
    rw [hcard]
    calc (((Set.Finite.toFinset (hψ m).1).biUnion
          (fun k => Set.Finite.toFinset (hφ k).1)).card)
        ≤ ∑ k ∈ Set.Finite.toFinset (hψ m).1,
            (Set.Finite.toFinset (hφ k).1).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Set.Finite.toFinset (hψ m).1, Mφ := by
          apply Finset.sum_le_sum
          intro k _
          rw [← Set.ncard_eq_toFinset_card _ (hφ k).1]
          exact (hφ k).2
      _ = (Set.Finite.toFinset (hψ m).1).card * Mφ := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
      _ ≤ Mψ * Mφ := by
          apply Nat.mul_le_mul_right
          rw [← Set.ncard_eq_toFinset_card _ (hψ m).1]
          exact (hψ m).2

/-- Composition of composition operators is composition of symbols in the
reversed order: `C_φ ∘L C_ψ = C_{ψ ∘ φ}`. -/
theorem compCLM_comp {φ ψ : ℕ → ℕ} {Mφ Mψ : ℕ}
    (hφ : HasBoundedFibers φ Mφ) (hψ : HasBoundedFibers ψ Mψ)
    (h : HasBoundedFibers (ψ ∘ φ) (Mψ * Mφ)) :
    compCLM (𝕜 := 𝕜) φ hφ ∘L compCLM (𝕜 := 𝕜) ψ hψ = compCLM (𝕜 := 𝕜) (ψ ∘ φ) h := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, compCLM_apply, Function.comp_apply]

/-- If `ψ` is pointwise the identity, `C_ψ` is the identity operator. -/
theorem compCLM_eq_of_forall {ψ : ℕ → ℕ} {M : ℕ} (hψ : HasBoundedFibers ψ M)
    (h : ∀ n, ψ n = n) : compCLM (𝕜 := 𝕜) ψ hψ = 1 := by
  ext x n
  simp only [compCLM_apply, one_apply_eq_self, h]

/-- `C_id` is the identity operator. -/
theorem compCLM_id {M : ℕ} (h : HasBoundedFibers id M) : compCLM (𝕜 := 𝕜) id h = 1 :=
  compCLM_eq_of_forall h (fun _ => rfl)

/-- An injective symbol has fibers of size at most one. -/
theorem hasBoundedFibers_of_injective {ψ : ℕ → ℕ} (hψ : Function.Injective ψ) :
    HasBoundedFibers ψ 1 := by
  intro m
  have hsub : (ψ ⁻¹' {m}).Subsingleton := by
    intro a ha b hb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    exact hψ (ha.trans hb.symm)
  constructor
  · exact hsub.finite
  · have hle : (ψ ⁻¹' {m}).ncard ≤ 1 := by
      apply (Set.ncard_le_one_iff (s := ψ ⁻¹' {m}) hsub.finite).mpr
      intro a b ha hb
      exact hsub ha hb
    exact hle

/-- A permutation symbol has fibers of size one. -/
theorem hasBoundedFibers_equiv (e : ℕ ≃ ℕ) : HasBoundedFibers e 1 :=
  hasBoundedFibers_of_injective e.injective

/-- The adjoint of the composition operator for a permutation symbol is the
composition operator of the inverse permutation. -/
theorem adjoint_compCLM_of_equiv (e : ℕ ≃ ℕ) :
    (compCLM (𝕜 := 𝕜) e (hasBoundedFibers_equiv e))†
      = compCLM (𝕜 := 𝕜) e.symm (hasBoundedFibers_equiv e.symm) := by
  ext y m
  rw [adjoint_compCLM_apply, compCLM_apply]
  have hfinset : Set.Finite.toFinset (hasBoundedFibers_equiv e m).1 = {e.symm m} := by
    apply Finset.ext
    intro n
    rw [Finset.mem_singleton, Set.Finite.mem_toFinset]
    constructor
    · intro hn
      exact (Equiv.eq_symm_apply e).mpr hn
    · intro hn
      rw [hn]
      simp
  rw [hfinset, Finset.sum_singleton]

/-- A permutation symbol gives a unitary composition operator. -/
theorem compCLM_mem_unitary (e : ℕ ≃ ℕ) :
    compCLM (𝕜 := 𝕜) e (hasBoundedFibers_equiv e)
      ∈ unitary (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_compCLM_of_equiv]
  constructor
  · rw [ContinuousLinearMap.mul_def,
      compCLM_comp (hasBoundedFibers_equiv e.symm) (hasBoundedFibers_equiv e)
        (hasBoundedFibers_comp (hasBoundedFibers_equiv e.symm)
          (hasBoundedFibers_equiv e)),
      compCLM_eq_of_forall _ (show ∀ n, (⇑e ∘ ⇑e.symm) n = n from fun n => e.apply_symm_apply n)]
  · rw [ContinuousLinearMap.mul_def,
      compCLM_comp (hasBoundedFibers_equiv e) (hasBoundedFibers_equiv e.symm)
        (hasBoundedFibers_comp (hasBoundedFibers_equiv e)
          (hasBoundedFibers_equiv e.symm)),
      compCLM_eq_of_forall _ (show ∀ n, (⇑e.symm ∘ ⇑e) n = n from fun n => Equiv.symm_apply_apply e n)]

/-- `C_ψ` is injective iff `ψ` is surjective: a missing value gives a
basis vector in the kernel, and a surjective symbol lets every coordinate
be read off from the image. -/
theorem injective_compCLM_iff (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    Function.Injective (compCLM (𝕜 := 𝕜) ψ hψ) ↔ Function.Surjective ψ := by
  constructor
  · intro hinj
    by_contra hnsurj
    obtain ⟨m, hm⟩ : ∃ m, m ∉ Set.range ψ := by
      simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnsurj
    have h0 : compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 m (1 : 𝕜)) = 0 := by
      apply lp.ext
      funext n
      have hne : ψ n ≠ m := fun h => hm ⟨n, h⟩
      rw [compCLM_apply, lp.coeFn_single, Pi.single_eq_of_ne hne]
      simp
    have hne : (lp.single 2 m (1 : 𝕜) : ℓ²(ℕ, 𝕜)) ≠ 0 := by
      intro h
      have hcoord : ((lp.single 2 m (1 : 𝕜) : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) m = 0 := by
        rw [h]
        simp
      rw [lp.coeFn_single, Pi.single_eq_same] at hcoord
      exact one_ne_zero hcoord
    exact hne (hinj (by rw [h0, map_zero]))
  · intro hsurj x y hxy
    apply lp.ext
    funext m
    obtain ⟨n, hn⟩ := hsurj m
    have h1 : (compCLM (𝕜 := 𝕜) ψ hψ x : ℓ²(ℕ, 𝕜)) n
        = (compCLM (𝕜 := 𝕜) ψ hψ y : ℓ²(ℕ, 𝕜)) n := by rw [hxy]
    rw [compCLM_apply, compCLM_apply, hn] at h1
    exact h1

/-- `C_ψ` is surjective iff `ψ` is injective: if `ψ a = ψ b` with
`a ≠ b`, the `a`-th and `b`-th coordinates of every vector in the range
agree, so `e_a` is not in the range; if `ψ` is injective, the preimage of
`y` is obtained by applying the adjoint and reading off the fiber sums. -/
theorem surjective_compCLM_iff (ψ : ℕ → ℕ) {M : ℕ} (hψ : HasBoundedFibers ψ M) :
    Function.Surjective (compCLM (𝕜 := 𝕜) ψ hψ) ↔ Function.Injective ψ := by
  constructor
  · intro hsurj
    by_contra hninj
    obtain ⟨a, b, hψab, hab⟩ := Function.not_injective_iff.mp hninj
    obtain ⟨x, hx⟩ := hsurj (lp.single 2 a (1 : 𝕜))
    have h1 : (compCLM (𝕜 := 𝕜) ψ hψ x : ℓ²(ℕ, 𝕜)) a
        = (compCLM (𝕜 := 𝕜) ψ hψ x : ℓ²(ℕ, 𝕜)) b := by
      rw [compCLM_apply, compCLM_apply, hψab]
    rw [hx] at h1
    rw [lp.coeFn_single, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm] at h1
    exact one_ne_zero h1
  · intro hinj y
    refine ⟨(ContinuousLinearMap.adjoint (compCLM (𝕜 := 𝕜) ψ hψ)) y, ?_⟩
    apply lp.ext
    funext n
    rw [compCLM_apply, adjoint_compCLM_apply]
    have hfinset : Set.Finite.toFinset (hψ (ψ n)).1 = {n} := by
      apply Finset.ext
      intro k
      rw [Finset.mem_singleton, Set.Finite.mem_toFinset]
      constructor
      · intro hk
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
        exact hinj hk
      · intro hk
        rw [hk]
        simp
    rw [hfinset, Finset.sum_singleton]

/-- Halving pairs: the map `n ↦ n / 2` has fibers of size at most two. -/
theorem hasBoundedFibers_div_two : HasBoundedFibers (fun n => n / 2) 2 := by
  intro m
  have hsub : (fun n => n / 2) ⁻¹' {m} ⊆ {2 * m, 2 * m + 1} := by
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  constructor
  · exact ((Set.finite_singleton _).insert _).subset hsub
  · calc ((fun n => n / 2) ⁻¹' {m}).ncard ≤ ({2 * m, 2 * m + 1} : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
      _ ≤ 2 := by
        have h2 : ({2 * m, 2 * m + 1} : Set ℕ).ncard
            ≤ ({2 * m + 1} : Set ℕ).ncard + 1 :=
          Set.ncard_insert_le _ _
        rw [Set.ncard_singleton] at h2
        exact h2

/-- A composition operator on `ℓ²(ℕ, 𝕜)` is never compact: the images of
the basis vectors indexed by the (necessarily infinite) range of `ψ` are
pairwise orthogonal and bounded below in norm, so they have no Cauchy
subsequence. -/
theorem not_isCompactOperator_compCLM (ψ : ℕ → ℕ) {M : ℕ}
    (hψ : HasBoundedFibers ψ M) :
    ¬ IsCompactOperator (compCLM (𝕜 := 𝕜) ψ hψ) := by
  intro hK
  have hrange : (Set.range ψ).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have hU : (Set.univ : Set ℕ).Finite := by
      have hbi : (Set.univ : Set ℕ) = ⋃ m ∈ Set.range ψ, ψ ⁻¹' {m} := by
        ext n
        simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
          true_iff]
        exact ⟨ψ n, ⟨n, rfl⟩, rfl⟩
      rw [hbi]
      exact hfin.biUnion (fun m _ => (hψ m).1)
    exact Set.infinite_univ.not_finite hU
  obtain ⟨f, hf⟩ := Set.Infinite.natEmbedding (Set.range ψ) hrange
  -- The strictly increasing-injectivity sequence of values taken by `ψ`.
  set mseq : ℕ → ℕ := fun k => (f k : ℕ) with hmseq
  have hmseq_inj : Function.Injective mseq := fun a b hab => hf (Subtype.ext hab)
  have hmseq_mem : ∀ k, mseq k ∈ Set.range ψ := fun k => (f k).2
  have hcompact : IsCompact
      (closure (compCLM (𝕜 := 𝕜) ψ hψ '' Metric.closedBall (0 : ℓ²(ℕ, 𝕜)) 1)) :=
    hK.isCompact_closure_image_closedBall 1
  have hu_mem : ∀ k, compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 (mseq k) (1 : 𝕜))
      ∈ closure (compCLM (𝕜 := 𝕜) ψ hψ '' Metric.closedBall (0 : ℓ²(ℕ, 𝕜)) 1) := by
    intro k
    apply subset_closure
    refine ⟨lp.single 2 (mseq k) (1 : 𝕜), ?_, rfl⟩
    have hnorm1 : ‖(lp.single 2 (mseq k) (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ = 1 := by
      rw [lp.norm_single (E := fun _ : ℕ => 𝕜) (p := 2) (by simp) (mseq k) (1 : 𝕜),
        norm_one]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm1]
  obtain ⟨a, ha, φ, hφmono, hφtendsto⟩ := hcompact.tendsto_subseq hu_mem
  set v : ℕ → ℓ²(ℕ, 𝕜) := fun k =>
    compCLM (𝕜 := 𝕜) ψ hψ (lp.single 2 (mseq (φ k)) (1 : 𝕜)) with hv
  have hCauchy : CauchySeq v := hφtendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hCauchy
  obtain ⟨N, hN⟩ := hCauchy 1 one_pos
  have hdist := hN (N + 1) (Nat.le_add_right N 1) N (le_refl N)
  -- The two indices give distinct values of `ψ`.
  have hφne : φ N ≠ φ (N + 1) := (hφmono (Nat.lt_succ_self N)).ne
  have hmne : mseq (φ (N + 1)) ≠ mseq (φ N) :=
    fun h => hφne (hmseq_inj (h.symm))
  -- But their images are at distance at least `√2`.
  have hge : Real.sqrt 2 ≤ dist (v (N + 1)) (v N) := by
    rw [dist_eq_norm]
    have hsq : (2 : ℝ) ≤ ‖v (N + 1) - v N‖ ^ 2 := by
      rw [← Real.rpow_two]
      have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
      have htsum_eq : ‖v (N + 1) - v N‖ ^ (2 : ℝ)
          = ∑' n, ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ) := by
        have h := lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
          (v (N + 1) - v N)
        rw [h2] at h
        exact h
      have hsumm : Summable (fun n => ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ)) := by
        have h := (lp.memℓp (v (N + 1) - v N)).summable
          (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
        simpa only [h2] using h
      set A := mseq (φ (N + 1)) with hA
      set B := mseq (φ N) with hB
      have hAB : A ≠ B := hmne
      have hfinite : ∑ n ∈ Set.Finite.toFinset ((hψ A).1.union (hψ B).1),
          ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ)
          ≤ ∑' n, ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ) :=
        hsumm.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      have hterm : ∀ n ∈ Set.Finite.toFinset ((hψ A).1.union (hψ B).1),
          ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ) = 1 := by
        intro n hn
        rw [Set.Finite.mem_toFinset] at hn
        have hnorm : ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ = 1 := by
          have hsub : ((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n
              = (lp.single 2 A (1 : 𝕜) : ℕ → 𝕜) (ψ n)
                - (lp.single 2 B (1 : 𝕜) : ℕ → 𝕜) (ψ n) := by
            simp only [hv, ← hA, ← hB, lp.coeFn_sub, Pi.sub_apply, compCLM_apply]
          rw [hsub, lp.coeFn_single, lp.coeFn_single]
          rcases hn with hn | hn
          · have hn' : ψ n = A := hn
            rw [hn', Pi.single_eq_same, Pi.single_eq_of_ne hAB]
            simp
          · have hn' : ψ n = B := hn
            rw [hn', Pi.single_eq_same, Pi.single_eq_of_ne hAB.symm]
            simp
        rw [hnorm]
        norm_num
      have hsum_eq : ∑ n ∈ Set.Finite.toFinset ((hψ A).1.union (hψ B).1),
          ‖((v (N + 1) - v N) : ℓ²(ℕ, 𝕜)) n‖ ^ (2 : ℝ)
          = (((Set.Finite.toFinset ((hψ A).1.union (hψ B).1)).card : ℝ)) := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hnc : (ψ ⁻¹' {A} ∪ ψ ⁻¹' {B}).ncard =
          fiberCard ψ A (hψ A).1 + fiberCard ψ B (hψ B).1 := by
        rw [Set.ncard_union_eq _ (hψ A).1 (hψ B).1]
        · simp only [fiberCard_eq_ncard]
        · rw [Set.disjoint_left]
          intro x hx hx2
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx2
          exact hAB (hx.symm.trans hx2)
      have hcard_eq : (Set.Finite.toFinset ((hψ A).1.union (hψ B).1)).card
          = (ψ ⁻¹' {A} ∪ ψ ⁻¹' {B}).ncard :=
        (Set.ncard_eq_toFinset_card _ _).symm
      have hA1 : (1 : ℝ) ≤ (fiberCard ψ A (hψ A).1 : ℝ) := by
        rw [fiberCard_eq_ncard]
        obtain ⟨n, hn⟩ := hmseq_mem (φ (N + 1))
        have hne : (ψ ⁻¹' {A}).Nonempty := ⟨n, hn.trans hA.symm⟩
        have hpos : 0 < (ψ ⁻¹' {A}).ncard :=
          Set.Nonempty.ncard_pos (hψ A).1 hne
        exact Nat.one_le_cast.mpr hpos
      have hB1 : (1 : ℝ) ≤ (fiberCard ψ B (hψ B).1 : ℝ) := by
        rw [fiberCard_eq_ncard]
        obtain ⟨n, hn⟩ := hmseq_mem (φ N)
        have hne : (ψ ⁻¹' {B}).Nonempty := ⟨n, hn.trans hB.symm⟩
        have hpos : 0 < (ψ ⁻¹' {B}).ncard :=
          Set.Nonempty.ncard_pos (hψ B).1 hne
        exact Nat.one_le_cast.mpr hpos
      have hcard : (2 : ℝ) ≤ ((Set.Finite.toFinset ((hψ A).1.union (hψ B).1)).card : ℝ) := by
        rw [hcard_eq, hnc]
        push_cast
        linarith
      rw [← hsum_eq] at hcard
      rw [htsum_eq]
      exact hcard.trans hfinite
    have h1 : Real.sqrt 2 ≤ Real.sqrt (‖v (N + 1) - v N‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h1
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  linarith [hdist, hge, hlt]

end MathlibExt.Analysis.InnerProductSpace.CompositionOperator

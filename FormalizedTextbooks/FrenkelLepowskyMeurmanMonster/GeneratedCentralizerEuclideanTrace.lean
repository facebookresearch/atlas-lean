/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A Euclidean realization of the actual tensor operators and their trace pairing. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerMatrixTrace
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Uncurry the physical spin and lattice coordinates without changing either coordinate. -/
noncomputable def centralizerTensorUncurry :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] ((SpinIndex × Fin 24) → ℝ) where
  toFun T p := T p.1 p.2
  invFun T t i := T (t,i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ordinary Euclidean realization of the actual physical tensor coordinate space. -/
noncomputable def centralizerTensorEuclideanEquiv :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (SpinIndex × Fin 24) :=
  centralizerTensorUncurry.trans (WithLp.linearEquiv 2 ℝ ((SpinIndex × Fin 24) → ℝ)).symm

/-- The same actual matrix multiplication operator, expressed in Euclidean tensor coordinates. -/
noncomputable def centralizerEuclideanMatrix (A : Matrix (Fin 24) (Fin 24) ℝ) :
    Module.End ℝ (EuclideanSpace ℝ (SpinIndex × Fin 24)) :=
  centralizerTensorEuclideanEquiv.conj (conwayMatrixTensorProduct A)

/-- The same actual short-vector multiplication operator in those Euclidean coordinates. -/
noncomputable def centralizerEuclideanShort (r : GriessShortIndex) :
    Module.End ℝ (EuclideanSpace ℝ (SpinIndex × Fin 24)) :=
  centralizerTensorEuclideanEquiv.conj (conwayTensorShortOperator r)

private theorem conj_comp {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
    [Module ℝ U] [Module ℝ V] (e : U ≃ₗ[ℝ] V) (a b : Module.End ℝ U) :
    (e.conj a).comp (e.conj b) = e.conj (a.comp b) := by
  apply LinearMap.ext
  intro x
  change e (a (e.symm (e (b (e.symm x))))) = e (a (b (e.symm x)))
  rw [LinearEquiv.symm_apply_apply]

theorem centralizerEuclideanMatrix_trace_comp (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    LinearMap.trace ℝ _ ((centralizerEuclideanMatrix A).comp (centralizerEuclideanMatrix B)) =
      4096 * ((A.transpose * B.transpose).trace + (5 / 8 : ℝ) * A.trace * B.trace) := by
  rw [centralizerEuclideanMatrix, centralizerEuclideanMatrix, conj_comp, LinearMap.trace_conj']
  exact conwayMatrixTensorProduct_trace_comp A B

theorem centralizerEuclideanMatrix_trace_comp_short (A : Matrix (Fin 24) (Fin 24) ℝ)
    (r : GriessShortIndex) :
    LinearMap.trace ℝ _ ((centralizerEuclideanMatrix A).comp
      (centralizerEuclideanShort r)) = 0 := by
  rw [centralizerEuclideanMatrix, centralizerEuclideanShort, conj_comp, LinearMap.trace_conj']
  exact conwayMatrixTensorProduct_trace_comp_short A r

theorem centralizerEuclideanShort_trace_comp (r s : GriessShortIndex) :
    LinearMap.trace ℝ _ ((centralizerEuclideanShort r).comp (centralizerEuclideanShort s)) =
      if r = s then 294912 else 0 := by
  rw [centralizerEuclideanShort, centralizerEuclideanShort, conj_comp, LinearMap.trace_conj']
  split_ifs with h
  · subst s; exact conwayTensorShortOperator_trace_square r
  · exact conwayTensorShortOperator_trace_comp_of_ne r s h

/-- A finite real algebra linear combination with the physical one-eighth coefficients. -/
noncomputable def centralizerAlgebraRow {E ι : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype ι] (M : E) (P : ι → E) (X : ι → ℝ) : E := M + ∑ i, (X i / 8) • P i

/-- The complete physical multiplication row, transported to Euclidean tensor coordinates. -/
noncomputable def centralizerEuclideanTensorMul (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) : Module.End ℝ (EuclideanSpace ℝ (SpinIndex × Fin 24)) :=
  centralizerAlgebraRow (centralizerEuclideanMatrix A) centralizerEuclideanShort X

private theorem functional_linear_combination {E ι : Type*} [Semiring E]
    [Module ℝ E] [IsScalarTower ℝ E E] [SMulCommClass ℝ E E]
    [Fintype ι] [DecidableEq ι]
    (τ : E →ₗ[ℝ] ℝ) (M N : E) (P : ι → E) (X Y : ι → ℝ) (ν : ℝ)
    (hMP : ∀ i, τ (M * P i) = 0)
    (hPN : ∀ i, τ (P i * N) = 0)
    (hPP : ∀ i j, τ (P i * P j) = if i = j then ν else 0) :
    τ ((M + ∑ i, X i • P i) * (N + ∑ i, Y i • P i)) =
      τ (M * N) + ∑ i, X i * Y i * ν := by
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_add,
    map_sum, map_smul, smul_eq_mul, hMP, hPN, hPP, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem functional_linear_combination_normalized {E ι : Type*} [Semiring E]
    [Module ℝ E] [IsScalarTower ℝ E E] [SMulCommClass ℝ E E]
    [Fintype ι] [DecidableEq ι]
    (τ : E →ₗ[ℝ] ℝ) (M N : E) (P : ι → E) (X Y : ι → ℝ)
    (hMP : ∀ i, τ (M * P i) = 0)
    (hPN : ∀ i, τ (P i * N) = 0)
    (hPP : ∀ i j, τ (P i * P j) = if i = j then 294912 else 0) :
    τ (centralizerAlgebraRow M P X * centralizerAlgebraRow N P Y) =
      τ (M * N) + 4608 * ∑ i, X i * Y i := by
  unfold centralizerAlgebraRow
  rw [functional_linear_combination τ M N P (fun i => X i / 8)
    (fun i => Y i / 8) 294912 hMP hPN hPP, Finset.mul_sum]
  apply congrArg (fun z : ℝ => τ (M * N) + z)
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option backward.isDefEq.respectTransparency true in
/-- The full tensor trace formula, in a genuine equivalent Euclidean realization. -/
theorem centralizerEuclideanTensorMul_trace_comp
    (A B : Matrix (Fin 24) (Fin 24) ℝ) (X Y : GriessShortIndex → ℝ) :
    LinearMap.trace ℝ _ ((centralizerEuclideanTensorMul A X).comp
      (centralizerEuclideanTensorMul B Y)) =
      4096 * ((A.transpose * B.transpose).trace + (5 / 8 : ℝ) * A.trace * B.trace) +
        4608 * ∑ r, X r * Y r := by
  have hMN := centralizerEuclideanMatrix_trace_comp A B
  have hMP := centralizerEuclideanMatrix_trace_comp_short A
  have hPP := centralizerEuclideanShort_trace_comp
  have hPN (r : GriessShortIndex) :
      LinearMap.trace ℝ _ ((centralizerEuclideanShort r).comp
        (centralizerEuclideanMatrix B)) = 0 := by
    rw [LinearMap.trace_comp_comm']
    exact centralizerEuclideanMatrix_trace_comp_short B r
  rw [← Module.End.mul_eq_comp]
  unfold centralizerEuclideanTensorMul
  have h := functional_linear_combination_normalized (LinearMap.trace ℝ _)
    (centralizerEuclideanMatrix A) (centralizerEuclideanMatrix B)
    centralizerEuclideanShort X Y hMP hPN hPP
  rw [h, Module.End.mul_eq_comp, hMN]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

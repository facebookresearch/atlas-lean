/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Trace
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.BlockTrace
public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension.Trace
public import MathlibExt.LinearAlgebra.TensorPower.Cyclic

/-!
# Cyclic rotation and stabilization of generalized trace

Let k be a commutative ring and A a k-module. On
A ⊗[k] A^⊗n, the signed cyclic operator is
t_n(a₀ ⊗ ⋯ ⊗ aₙ) = (−1)^n aₙ ⊗ a₀ ⊗ ⋯ ⊗ a_(n−1).
For a finite matrix index type ι, the closed-cycle generalized trace
Mat_ι(A) ⊗[k] Mat_ι(A)^⊗n → A ⊗[k] A^⊗n commutes with t_n.
This rotation identity requires no multiplication on A.

For independent k-modules M and A, top-left extension by zero from
r×r to s×s matrices, r ≤ s, preserves the generalized trace
Mat_r(M) ⊗[k] Mat_r(A)^⊗n → M ⊗[k] A^⊗n. The equality holds for
the full linear tensor map and includes r = 0. All formulas are integral:
no integer is inverted.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix

variable (k : Type u) [CommRing k]

section Cyclic

variable (A : Type v) [AddCommGroup A] [Module k A]
  (ι : Type z) [Fintype ι]

/-- For a commutative ring k, a k-module A, a finite index type ι
and n ≥ 0, the closed-cycle trace T_n satisfies
t_n^A ∘ T_n = T_n ∘ t_n^Mat on
Mat_ι(A) ⊗[k] Mat_ι(A)^⊗n, where t_n rotates the last factor to the
front and multiplies by (−1)^n. In degree zero t_0 is the identity.
No algebra multiplication on A is assumed. -/
theorem generalizedTrace_cyclic (n : ℕ) :
    (TensorPower.consCyclicOperator k A n).comp (generalizedTrace k ι n) =
      (generalizedTrace k ι n).comp (TensorPower.consCyclicOperator k (Matrix ι ι A) n) := by
  classical
  apply matrix_tensor_ext k A A ι
  intro U₀ m U a
  change TensorPower.consCyclicOperator k A n
      (generalizedTrace k ι n
        ((U₀.map (fun c => c • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => (U j).map (fun c => c • a j)))) =
    generalizedTrace k ι n
      (TensorPower.consCyclicOperator k (Matrix ι ι A) n
        ((U₀.map (fun c => c • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j => (U j).map (fun c => c • a j))))
  cases n with
  | zero =>
      rw [TensorPower.consCyclicOperator_zero, TensorPower.consCyclicOperator_zero]
      rfl
  | succ n =>
      let V : Fin (n + 2) → Matrix ι ι A :=
        Fin.cons (U₀.map (fun c => c • m)) (fun j => (U j).map (fun c => c • a j))
      let v : Fin (n + 2) → A := Fin.cons m a
      have htrace :
          Matrix.trace (U₀ * (List.ofFn U).prod) =
            Matrix.trace ((U (Fin.last n) * U₀) *
              (List.ofFn (fun j : Fin n => U j.castSucc)).prod) := by
        rw [List.ofFn_succ' U, List.prod_concat, ← Matrix.mul_assoc]
        exact Matrix.trace_mul_cycle U₀ _ (U (Fin.last n))
      rw [generalizedTrace_scaled, map_smul]
      change Matrix.trace (U₀ * (List.ofFn U).prod) •
          TensorPower.consCyclicOperator k A (n + 1)
            (v 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail v)) =
        generalizedTrace k ι (n + 1)
          (TensorPower.consCyclicOperator k (Matrix ι ι A) (n + 1)
            (V 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail V)))
      rw [TensorPower.consCyclicOperator_tmul, TensorPower.consCyclicOperator_tmul,
        map_smul]
      have hvlast : v (Fin.last (n + 1)) = a (Fin.last n) := rfl
      have hVlast : V (Fin.last (n + 1)) = (U (Fin.last n)).map
          (fun c => c • a (Fin.last n)) := rfl
      have hvinit : (fun i : Fin (n + 1) => v i.castSucc) =
          Fin.cons m (fun j : Fin n => a j.castSucc) := by
        funext i
        cases i using Fin.cases <;> rfl
      have hVinit : (fun i : Fin (n + 1) => V i.castSucc) =
          Fin.cons (U₀.map (fun c => c • m))
            (fun j : Fin n => (U j.castSucc).map (fun c => c • a j.castSucc)) := by
        funext i
        cases i using Fin.cases <;> rfl
      rw [hvlast, hVlast, hvinit, hVinit]
      change Matrix.trace (U₀ * (List.ofFn U).prod) •
          ((-1 : k) ^ (n + 1) • (a (Fin.last n) ⊗ₜ[k]
            PiTensorProduct.tprod k (Fin.cons m (fun j : Fin n => a j.castSucc)))) =
        (-1 : k) ^ (n + 1) • generalizedTrace k ι (n + 1)
          ((U (Fin.last n)).map (fun c => c • a (Fin.last n)) ⊗ₜ[k]
            PiTensorProduct.tprod k
              (Fin.cons (U₀.map (fun c => c • m))
                (fun j : Fin n => (U j.castSucc).map (fun c => c • a j.castSucc))))
      have htail :
          Fin.cons (U₀.map (fun c => c • m))
              (fun j : Fin n => (U j.castSucc).map (fun c => c • a j.castSucc)) =
            (fun j : Fin (n + 1) =>
              (Fin.cons (α := fun _ : Fin (n + 1) => Matrix ι ι k)
                U₀ (fun i : Fin n => U i.castSucc) j).map
                (fun c => c • (Fin.cons (α := fun _ : Fin (n + 1) => A)
                  m (fun i : Fin n => a i.castSucc) j))) := by
        funext j
        cases j using Fin.cases <;> rfl
      rw [htail, generalizedTrace_scaled]
      simp only [List.ofFn_cons, List.prod_cons]
      rw [← Matrix.mul_assoc, htrace, smul_comm]

end Cyclic

section Stabilization

variable {A : Type v} [AddCommGroup A] [Module k A]
  {M : Type w} [AddCommGroup M] [Module k M]

/-- Let r ≤ s and let X and a₁,…,aₙ be r×r matrices over the
k-modules M and A. In the closed-cycle trace of their zero extensions,
a cycle γ : Fin(n+1) → Fin s that visits an index outside Fin r has a
zero tensor factor. Its summand is therefore zero, including the
coefficient factor when the outside index occurs at γ(0). -/
private theorem zeroExtend_trace_summand_zero {r s n : ℕ} (h : r ≤ s)
    (X : Matrix (Fin r) (Fin r) M) (a : Fin n → Matrix (Fin r) (Fin r) A)
    (γ : Fin (n + 1) → Fin s) (hγ : ∃ j, r ≤ (γ j).val) :
    Matrix.zeroExtend h X (γ 0) (γ 1) ⊗ₜ[k]
      PiTensorProduct.tprod k (fun j => Matrix.zeroExtend h (a j)
        (γ j.succ) (γ (j.succ + 1))) = 0 := by
  obtain ⟨j, hj⟩ := hγ
  cases j using Fin.cases with
  | zero =>
      rw [Matrix.zeroExtend_of_row h X (γ 0) (γ 1) hj, TensorProduct.zero_tmul]
  | succ j =>
      have hz : Matrix.zeroExtend h (a j) (γ j.succ) (γ (j.succ + 1)) = 0 :=
        Matrix.zeroExtend_of_row h (a j) _ _ hj
      rw [(PiTensorProduct.tprod k).map_coord_zero j hz, TensorProduct.tmul_zero]

/-- For k-modules M and A, r ≤ s, n ≥ 0, a coefficient matrix
X ∈ Mat_r(M) and algebra-factor matrices aⱼ ∈ Mat_r(A), extending each
matrix by zero to its top-left s×s block leaves the closed-cycle trace
of X ⊗ a₁ ⊗ ⋯ ⊗ aₙ unchanged. This includes an empty source matrix
index set r = 0. -/
theorem generalizedTrace_zeroExtend {r s : ℕ} (h : r ≤ s) (n : ℕ)
    (X : Matrix (Fin r) (Fin r) M) (a : Fin n → Matrix (Fin r) (Fin r) A) :
    generalizedTrace k (Fin s) n (Matrix.zeroExtend h X ⊗ₜ[k]
      PiTensorProduct.tprod k (fun j => Matrix.zeroExtend h (a j))) =
      generalizedTrace k (Fin r) n (X ⊗ₜ[k] PiTensorProduct.tprod k a) := by
  classical
  rw [generalizedTrace_tmul_tprod, generalizedTrace_tmul_tprod]
  let e : (Fin (n + 1) → Fin r) → (Fin (n + 1) → Fin s) := fun γ j => (γ j).castLE h
  have he : Function.Injective e := by
    intro γ δ hγδ
    funext j
    exact Fin.castLE_injective h (congrFun hγδ j)
  let f := fun γ : Fin (n + 1) → Fin r => X (γ 0) (γ 1) ⊗ₜ[k]
    PiTensorProduct.tprod k (fun j => a j (γ j.succ) (γ (j.succ + 1)))
  let g := fun γ : Fin (n + 1) → Fin s => Matrix.zeroExtend h X (γ 0) (γ 1) ⊗ₜ[k]
    PiTensorProduct.tprod k (fun j => Matrix.zeroExtend h (a j)
      (γ j.succ) (γ (j.succ + 1)))
  have hz (γ : Fin (n + 1) → Fin s) (hγ : γ ∉ Set.range e) : g γ = 0 := by
    apply zeroExtend_trace_summand_zero k h X a γ
    by_contra hn
    have hlt : ∀ j, (γ j).val < r := by
      intro j
      exact Nat.lt_of_not_ge (fun hj => hn ⟨j, hj⟩)
    apply hγ
    refine ⟨fun j => ⟨(γ j).val, hlt j⟩, ?_⟩
    funext j
    exact Fin.ext rfl
  have hv (γ : Fin (n + 1) → Fin r) : f γ = g (e γ) := by
    simp only [f, g, e, Matrix.zeroExtend_castLE]
  exact (Fintype.sum_of_injective e he f g hz hv).symm

/-- For k-modules M and A and r ≤ s, let Z_n extend every factor
from Mat_r(M) ⊗[k] Mat_r(A)^⊗n to
Mat_s(M) ⊗[k] Mat_s(A)^⊗n by zero. The equality T_n^s ∘ Z_n = T_n^r
holds as an equality of k-linear maps, with no restriction on n ≥ 0
or on r = 0. -/
theorem generalizedTrace_comp_zeroExtend {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    (generalizedTrace k (Fin s) n).comp
      (TensorProduct.map (Matrix.zeroExtendLinear (k := k) (A := M) h)
        (PiTensorProduct.map fun _ : Fin n => Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      generalizedTrace k (Fin r) n := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro X
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change generalizedTrace k (Fin s) n
      (TensorProduct.map (Matrix.zeroExtendLinear (k := k) (A := M) h)
        (PiTensorProduct.map fun _ : Fin n => Matrix.zeroExtendLinear (k := k) (A := A) h)
        (X ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    generalizedTrace k (Fin r) n (X ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  exact generalizedTrace_zeroExtend k h n X a

end Stabilization

end ModuleCat.Algebra.Hochschild.Matrix

end

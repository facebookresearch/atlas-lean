/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Square-summable operator coefficients in a Hilbert basis

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For T∈S_b, write
c_b(T)=(T(b_i))_i∈ℓ²(I,K), N_b(T)=‖c_b(T)‖ℓ² and I_b(S,T)=⟪c_b(S),c_b(T)⟫_ℂ. The coefficient
map c_b:S_b→ℓ²(I,K) is complex-linear. Its norm and inner-product functions use the
vector-valued ℓ² norm and inner product, and the basis index need not be countable.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HilbertBasis

universe uI uH uK
variable {I : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Submodule of operators with square-summable basis images.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. The submodule
squareSummableOperators b is S_b={T:H→LK:(T(b_i))_i∈ℓ²(I,K)}.
-/
def squareSummableOperators (b : HilbertBasis I ℂ H) : Submodule ℂ (H →L[ℂ] K) where
  carrier := {T | Memℓp (fun i => T (b i)) 2}
  zero_mem' := by
    change Memℓp (fun _ : I => (0 : K)) 2
    exact zero_mem_ℓp'
  add_mem' := by
    intro T S hT hS
    change Memℓp (fun i => T (b i) + S (b i)) 2
    exact hT.add hS
  smul_mem' := by
    intro c T hT
    change Memℓp (fun i => c • T (b i)) 2
    exact hT.const_smul c

/-- **Vector-valued ℓ² coefficients of an operator.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For T∈S_b,
operatorCoefficients b T∈ℓ²(I,K) is the sequence i↦T(b_i).
-/
def operatorCoefficients (b : HilbertBasis I ℂ H) (T : squareSummableOperators (K := K) b) :
    lp (fun _ : I => K) 2 :=
  ⟨fun i => (T : H →L[ℂ] K) (b i), T.property⟩

/-- **Value of an operator coefficient at a basis index.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For T∈S_b and i∈I,
operatorCoefficients b T i=T(b_i).
-/
theorem operatorCoefficients_apply (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) (i : I) :
    operatorCoefficients b T i = (T : H →L[ℂ] K) (b i) := rfl

/-- **Linear coefficient map into vector-valued ℓ².**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. The complex linear map
operatorCoefficientsLinearMap b:S_b→ℓ²(I,K) sends T to (T(b_i))_i.
-/
def operatorCoefficientsLinearMap (b : HilbertBasis I ℂ H) :
    squareSummableOperators (K := K) b →ₗ[ℂ] lp (fun _ : I => K) 2 where
  toFun := operatorCoefficients b
  map_add' T S := by
    ext i
    rfl
  map_smul' c T := by
    ext i
    rfl

/-- **Basis coefficient norm function.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For T∈S_b,
operatorCoefficientNorm b T=‖(T(b_i))_i‖ℓ², whose square is ∑i‖T(b_i)‖².
-/
def operatorCoefficientNorm (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) : ℝ :=
  ‖operatorCoefficients b T‖

/-- **Basis coefficient inner-product function.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For S,T∈S_b,
operatorCoefficientInner b S T=⟪(S(b_i))_i,(T(b_i))_i⟫ℓ²=∑i⟪S(b_i),T(b_i)⟫_ℂ.
-/
def operatorCoefficientInner (b : HilbertBasis I ℂ H)
    (S T : squareSummableOperators (K := K) b) : ℂ :=
  inner ℂ (operatorCoefficients b S) (operatorCoefficients b T)

/-- **Value of the linear operator coefficient map.**

Let H,K be complex inner product spaces and b:I→H a Hilbert basis with an arbitrary index type
I. Let S_b⊆(H→L[ℂ]K) consist of operators T with ∑i‖T(b_i)‖²<∞. For T∈S_b,
operatorCoefficientsLinearMap b T=operatorCoefficients b T, the sequence i↦T(b_i).
-/
theorem operatorCoefficientsLinearMap_apply (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) :
    operatorCoefficientsLinearMap b T = operatorCoefficients b T := rfl

end HilbertBasis

end

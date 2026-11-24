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
# Actual square-summable operator coefficients relative to a Hilbert basis

The carrier is the submodule of the original bounded operators whose actual
basis-vector images belong to stock lp K2. The coefficient, norm and inner
functions use this literal lp element. No independent completed operator
space, countable basis, norm comparison or basis-independence theorem is an
input. No new norm or completeness instance on the operator subtype is
asserted. These constructors serve the original Hilbert-Schmidt exercise
and trace-factorization statements, including arbitrary-cardinality bases
and zero Hilbert spaces.
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

/-- Original bounded operators with actual square-summable images of the given basis vectors. -/
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

/-- The actual lp class consists of the original operator's values on the original basis. -/
def operatorCoefficients (b : HilbertBasis I ℂ H) (T : squareSummableOperators (K := K) b) :
    lp (fun _ : I => K) 2 :=
  ⟨fun i => (T : H →L[ℂ] K) (b i), T.property⟩

/-- Each original coefficient retains its literal bounded-operator value. -/
theorem operatorCoefficients_apply (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) (i : I) :
    operatorCoefficients b T i = (T : H →L[ℂ] K) (b i) := rfl

/-- The original coefficient assignment is linear on the actual square-summable submodule. -/
def operatorCoefficientsLinearMap (b : HilbertBasis I ℂ H) :
    squareSummableOperators (K := K) b →ₗ[ℂ] lp (fun _ : I => K) 2 where
  toFun := operatorCoefficients b
  map_add' T S := by
    ext i
    rfl
  map_smul' c T := by
    ext i
    rfl

/-- The actual coefficient lp norm, without a new norm on the operator subtype. -/
def operatorCoefficientNorm (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) : ℝ :=
  ‖operatorCoefficients b T‖

/-- The actual coefficient lp inner product on two original square-summable operators. -/
def operatorCoefficientInner (b : HilbertBasis I ℂ H)
    (S T : squareSummableOperators (K := K) b) : ℂ :=
  inner ℂ (operatorCoefficients b S) (operatorCoefficients b T)

/-- The same original scalar and operator combination retains its actual coefficient class. -/
theorem operatorCoefficientsLinearMap_apply (b : HilbertBasis I ℂ H)
    (T : squareSummableOperators (K := K) b) :
    operatorCoefficientsLinearMap b T = operatorCoefficients b T := rfl

end HilbertBasis

end

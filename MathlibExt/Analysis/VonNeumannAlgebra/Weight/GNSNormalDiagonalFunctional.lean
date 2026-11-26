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

public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveOrderNormalMembership
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSCoefficientOrderNormal

/-!
# Normal diagonal functionals from finite square GNS vectors

For a normal extended weight `φ` on a concrete von Neumann algebra, each finite square element
`x ∈ n_φ` gives a normal functional `ψ_x(a)=⟨Λ(x),π(a)Λ(x)⟩` in the closed vector-functional
span `M_*`.

It is the positive diagonal coefficient of the GNS left representation. Faithfulness and
semifiniteness of `φ` are not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Normal functional of a finite square GNS vector.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. for `x ∈
n_φ`, `normalWeightGNSDiagonalFunctional M φ x ∈ M_*` is the bounded coefficient `a ↦
⟨Λ(x),π(a)Λ(x)⟩`. -/
def normalWeightGNSDiagonalFunctional (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) : normalFunctionalSpace M := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let ψ := φ.gnsDiagonalPositiveFunctional x
  have hmember : ψ.toContinuousLinearMap ∈ normalFunctionalSpace M := by
    apply positiveFunctional_mem_normalFunctionalSpace_of_positiveLUBs M ψ
    intro I _preorder _directed _nonempty a s hmono hbound hLUB
    exact gnsDiagonalPositiveFunctional_preserves_boundedPositiveIsLUB M φ hφ x a s
      hmono hbound hLUB
  exact ⟨ψ.toContinuousLinearMap, hmember⟩

/-- **Underlying bounded functional of a normal GNS diagonal.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. for `x ∈
n_φ`, the continuous functional underlying `normalWeightGNSDiagonalFunctional M φ x`
equals `representationCoefficient π (Λ x) (Λ x)`. -/
@[simp]
theorem normalWeightGNSDiagonalFunctional_coe (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) :
    (normalWeightGNSDiagonalFunctional M φ hφ x : StrongDual ℂ M) =
      MathlibExt.Analysis.CStarAlgebra.representationCoefficient
        φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) :=
  rfl

/-- **Value of a normal diagonal GNS functional.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. for `x ∈
n_φ` and `a ∈ M`, `(normalWeightGNSDiagonalFunctional M φ x)(a)=⟨Λ(x),π(a)Λ(x)⟩`. -/
theorem normalWeightGNSDiagonalFunctional_apply (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) (a : M) :
    (normalWeightGNSDiagonalFunctional M φ hφ x : StrongDual ℂ M) a =
      inner ℂ (φ.gnsMap x) ((φ.gnsLeftStarAlgHom a) (φ.gnsMap x)) := by
  rw [normalWeightGNSDiagonalFunctional_coe,
    MathlibExt.Analysis.CStarAlgebra.representationCoefficient_apply]

end

end VonNeumannAlgebra

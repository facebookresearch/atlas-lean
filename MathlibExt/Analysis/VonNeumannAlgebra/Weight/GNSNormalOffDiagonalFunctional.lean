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

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalDiagonalFunctional
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Normal off-diagonal GNS coefficients on finite square vectors

For a normal extended weight on a concrete von Neumann algebra, finite square vectors `x,y ∈
n_φ` define the normal functional `a ↦ ⟨Λ(y),π(a)Λ(x)⟩`.

Polarizing the normal diagonal coefficients puts this off-diagonal coefficient in `M_*`. The
inner product is linear in its second argument; no faithfulness or semifiniteness is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Normal functional of two finite square GNS vectors.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. for `x,y
∈ n_φ`, `normalWeightGNSOffDiagonalFunctional M φ x y` returns `ρ ∈ M_*` whose underlying
bounded functional is `representationCoefficient π (Λ x) (Λ y)`, with value
`ρ(a)=⟨Λ(y),π(a)Λ(x)⟩`. -/
def normalWeightGNSOffDiagonalFunctional (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x y : φ.finiteSquareSubmodule) :
    {ρ : normalFunctionalSpace M // (ρ.val : StrongDual ℂ M) =
      MathlibExt.Analysis.CStarAlgebra.representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap y)} := by
  let D := normalWeightGNSDiagonalFunctional M φ hφ
  let ρ : normalFunctionalSpace M := (4 : ℂ)⁻¹ •
    (D (x + y) - D (x - y) + Complex.I • D (x + Complex.I • y) -
      Complex.I • D (x - Complex.I • y))
  refine ⟨ρ, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  have hD (z : φ.finiteSquareSubmodule) :
      (D z : StrongDual ℂ M) a = ⟪φ.gnsMap z, (φ.gnsLeftStarAlgHom a) (φ.gnsMap z)⟫_ℂ := by
    exact normalWeightGNSDiagonalFunctional_apply M φ hφ z a
  change (4 : ℂ)⁻¹ • ((D (x + y) : StrongDual ℂ M) a - (D (x - y) : StrongDual ℂ M) a +
    Complex.I • (D (x + Complex.I • y) : StrongDual ℂ M) a -
    Complex.I • (D (x - Complex.I • y) : StrongDual ℂ M) a) = _
  rw [hD, hD, hD, hD, MathlibExt.Analysis.CStarAlgebra.representationCoefficient_apply]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end VonNeumannAlgebra

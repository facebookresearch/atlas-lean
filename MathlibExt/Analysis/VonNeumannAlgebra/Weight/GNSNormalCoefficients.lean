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

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalOffDiagonalFunctional
public import MathlibExt.Analysis.CStarAlgebra.RepresentationCoefficientContinuity
public import Mathlib.Topology.DenseEmbedding

/-!
# Normality of all completed GNS vector coefficients

Let `φ` be a normal extended weight on a concrete von Neumann algebra. For all vectors `g,h` in
its completed GNS Hilbert space, the bounded coefficient `a ↦ ⟨h,π(a)g⟩` belongs to `M_*`.

Normality of finite square coefficients extends to all GNS vectors through the norm-dense GNS
domain and coefficient continuity. The weight need not be faithful or semifinite.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open MathlibExt.Analysis.CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Every completed GNS vector coefficient is normal.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. for
arbitrary `g,h ∈ H_φ`, `representationCoefficient π g h ∈ M_*`, with value `a ↦
⟨h,π(a)g⟩`. -/
theorem normalWeightGNSCoefficient_mem (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (g h : φ.GNS) :
    representationCoefficient φ.gnsLeftStarAlgHom g h ∈ normalFunctionalSpace M := by
  have hdense := φ.gnsMap_denseRange
  have hclosed := normalFunctionalSpace_isClosed M
  have hdomain (x : φ.finiteSquareSubmodule) (h : φ.GNS) :
      representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) h ∈ normalFunctionalSpace M := by
    refine hdense.induction_on
      (p := fun h : φ.GNS => representationCoefficient φ.gnsLeftStarAlgHom (φ.gnsMap x) h ∈
        normalFunctionalSpace M) h ?_ ?_
    · exact hclosed.preimage (representationCoefficient_continuous_right φ.gnsLeftStarAlgHom (φ.gnsMap x))
    · intro y
      let ρ := normalWeightGNSOffDiagonalFunctional M φ hφ x y
      rw [← ρ.property]
      exact ρ.val.property
  refine hdense.induction_on
    (p := fun g : φ.GNS => representationCoefficient φ.gnsLeftStarAlgHom g h ∈
      normalFunctionalSpace M) g ?_ ?_
  · exact hclosed.preimage (representationCoefficient_continuous_left φ.gnsLeftStarAlgHom h)
  · intro x
    exact hdomain x h

end

end VonNeumannAlgebra

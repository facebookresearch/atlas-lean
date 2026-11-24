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
# All original GNS vector coefficients of a normal weight are normal functionals

The actual original-domain GNS map is dense in its constructed Hilbert
completion. Its finite-square off-diagonal coefficients are already actual
normal-functional members. Original coefficient continuity in each vector
makes membership a closed property. Two dense-range extensions therefore
give normal membership for every pair of original completed GNS vectors.
No density, normality, GNS model or coefficient-bound certificate is input.
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

/-- Original normal weight gives actual normal-functional membership for all completed GNS vector coefficients. -/
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

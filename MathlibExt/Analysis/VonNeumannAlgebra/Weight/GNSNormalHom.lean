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

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalCoefficients
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.VectorFunctionalCriterion

/-!
# The original normal weight has its computed normal GNS star homomorphism

The existing original unital GNS star map is restricted to the full concrete
operator von Neumann algebra on its actual Hilbert completion. Every vector
functional pullback is exactly its original GNS representation coefficient,
whose actual normal membership is proved from the original normal weight.
The stock vector-functional criterion constructs normality of that same
map. No normal homomorphism, GNS model or output certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open MathlibExt.Analysis.CStarAlgebra
open scoped CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct normality of the same original completed weight GNS star representation. -/
def normalWeightGNSStarAlgHom (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) : NormalStarAlgHom M (⊤ : VonNeumannAlgebra φ.GNS) := by
  let N : VonNeumannAlgebra φ.GNS := ⊤
  let f : M →⋆ₐ[ℂ] N := φ.gnsLeftStarAlgHom.codRestrict N.toStarSubalgebra (by
    intro a
    change φ.gnsLeftStarAlgHom a ∈ (⊤ : StarSubalgebra ℂ (φ.GNS →L[ℂ] φ.GNS))
    exact Set.mem_univ _)
  refine NormalStarAlgHom.ofVectorFunctionalPullbacks f ?_
  intro ξ η
  have hvalue : (vectorFunctional N ξ η).comp
      (⟨LinearMap.ofClass f, map_continuous f⟩ : M →L[ℂ] N) =
      representationCoefficient φ.gnsLeftStarAlgHom η ξ := by
    apply ContinuousLinearMap.ext
    intro a
    change vectorFunctional N ξ η (f a) = representationCoefficient φ.gnsLeftStarAlgHom η ξ a
    rw [vectorFunctional_apply, representationCoefficient_apply]
    rfl
  rw [hvalue]
  exact normalWeightGNSCoefficient_mem M φ hφ η ξ

/-- The actual normal map keeps the same original completed GNS operator at every source element. -/
@[simp]
theorem normalWeightGNSStarAlgHom_apply (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (a : M) :
    (normalWeightGNSStarAlgHom M φ hφ a : φ.GNS →L[ℂ] φ.GNS) = φ.gnsLeftStarAlgHom a :=
  rfl

end

end VonNeumannAlgebra

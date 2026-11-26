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
# Normal star homomorphism of the weight GNS representation

For a normal extended weight on a concrete von Neumann algebra, its GNS left star representation
`π : M → B(H_φ)` is ultraweakly continuous. It therefore defines a normal unital complex star
homomorphism into the full operator von Neumann algebra on `H_φ`.

Its operator value is the completed left multiplication with `π(a)Λ(x)=Λ(a*x)`. Faithfulness and
semifiniteness are not required for this normality construction.
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

/-- **Normal GNS homomorphism of a normal weight.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets.
`normalWeightGNSStarAlgHom M φ : NormalStarAlgHom M B(H_φ)` is the unital star
representation `π`, continuous for the ultraweak topologies. -/
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

/-- **Operator value of the normal GNS homomorphism.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. for `a ∈ M`,
the operator underlying `normalWeightGNSStarAlgHom M φ a` is `φ.gnsLeftStarAlgHom a=π(a)`. -/
@[simp]
theorem normalWeightGNSStarAlgHom_apply (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (a : M) :
    (normalWeightGNSStarAlgHom M φ hφ a : φ.GNS →L[ℂ] φ.GNS) = φ.gnsLeftStarAlgHom a :=
  rfl

end

end VonNeumannAlgebra

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

public import MathlibExt.Analysis.VonNeumannAlgebra.Basic
public import MathlibExt.Analysis.CStarAlgebra.RepresentationCoefficient
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The Banach space spanned by normal vector functionals

Let `M ⊆ B(H)` be a concrete von Neumann algebra on a complete complex Hilbert space. The vector
functional is `ω_(ξ,η)(x)=⟨ξ,xη⟩`, with `‖ω_(ξ,η)‖≤‖ξ‖‖η‖` in the continuous-dual operator norm.

The normal-functional space `M_*` is the norm closure of the complex span of all such vector
functionals in `M*`. It is a closed complex subspace and hence a Banach space. Any norm-closed
complex subspace containing the vector functionals also contains `M_*`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

open MathlibExt.Analysis.CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Coefficient bound for a concrete von Neumann operator.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. for `ξ,η ∈ H` and `x ∈ M`, `|⟨ξ,xη⟩|≤‖ξ‖‖η‖‖x‖`, with the
inherited operator norm on `M`. -/
theorem vectorFunctional_bound (M : VonNeumannAlgebra H) (ξ η : H) (x : M) :
    ‖⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ‖ ≤ (‖ξ‖ * ‖η‖) * ‖x‖ := by
  let φ : StrongDual ℂ M := representationCoefficient (A := M) M.toStarSubalgebra.subtype η ξ
  have hnorm : ‖φ‖ ≤ ‖ξ‖ * ‖η‖ := by
    simpa only [φ, mul_comm] using
      norm_representationCoefficient_le (A := M) M.toStarSubalgebra.subtype η ξ
  calc
    ‖⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ‖ = ‖φ x‖ := by
      dsimp only [φ]
      rw [representationCoefficient_apply (A := M) M.toStarSubalgebra.subtype η ξ x]
      rfl
    _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    _ ≤ (‖ξ‖ * ‖η‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)

/-- **Vector functional on a concrete von Neumann algebra.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. `vectorFunctional M ξ η : M →L[ℂ] ℂ` is `ω_(ξ,η)`, linear in the
operator argument and using the inner product linear in its second vector argument. -/
noncomputable def vectorFunctional (M : VonNeumannAlgebra H) (ξ η : H) : StrongDual ℂ M :=
  representationCoefficient (A := M) M.toStarSubalgebra.subtype η ξ

/-- **Value of a concrete vector functional.** Let `H` be a complete complex Hilbert space and
`M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. for `ξ,η ∈ H` and `x ∈ M`, `vectorFunctional M ξ η x=⟨ξ,(x : B(H))η⟩`. -/
@[simp]
theorem vectorFunctional_apply (M : VonNeumannAlgebra H) (ξ η : H) (x : M) :
    vectorFunctional M ξ η x = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ := by
  change representationCoefficient (A := M) M.toStarSubalgebra.subtype η ξ x =
    ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ
  rw [representationCoefficient_apply (A := M) M.toStarSubalgebra.subtype η ξ x]
  rfl

/-- **Continuous-dual norm of a vector coefficient.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. for `ξ,η ∈ H`, `‖vectorFunctional M ξ η‖≤‖ξ‖*‖η‖`. -/
theorem norm_vectorFunctional_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖vectorFunctional M ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  simpa only [vectorFunctional, mul_comm] using
    norm_representationCoefficient_le (A := M) M.toStarSubalgebra.subtype η ξ

/-- **Norm-closed span of von Neumann vector functionals.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. `normalFunctionalSpace M = closure(span ℂ {ω_(ξ,η) : ξ,η ∈ H})`
inside the normed continuous dual `M*`. -/
noncomputable def normalFunctionalSpace (M : VonNeumannAlgebra H) :
    Submodule ℂ (StrongDual ℂ M) :=
  (Submodule.span ℂ (Set.range fun p : H × H => vectorFunctional M p.1 p.2)).topologicalClosure

/-- **Vector coefficient belongs to the normal-functional space.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. for every `ξ,η ∈ H`, `ω_(ξ,η)∈M_*`. -/
theorem vectorFunctional_mem_normalFunctionalSpace (M : VonNeumannAlgebra H) (ξ η : H) :
    vectorFunctional M ξ η ∈ normalFunctionalSpace M :=
  (Submodule.le_topologicalClosure _)
    (Submodule.subset_span (Set.mem_range_self (ξ, η)))

/-- **Norm closedness of the normal-functional subspace.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. `M_*` is closed in `M*` for the continuous-dual operator norm. -/
theorem normalFunctionalSpace_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (normalFunctionalSpace M : Set (StrongDual ℂ M)) :=
  Submodule.isClosed_topologicalClosure _

/-- **Completeness of the normal-functional Banach space.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. `M_*` is complete for its inherited continuous-dual norm. -/
instance normalFunctionalSpace_completeSpace (M : VonNeumannAlgebra H) :
    CompleteSpace (normalFunctionalSpace M) :=
  (normalFunctionalSpace_isClosed M).isComplete.completeSpace_coe

/-- **Least closed complex space containing the vector functionals.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. if `P` is a norm-closed complex subspace of `M*`
containing every `ω_(ξ,η)`, then `M_*≤P`. -/
theorem normalFunctionalSpace_le (M : VonNeumannAlgebra H)
    {P : Submodule ℂ (StrongDual ℂ M)} (hP : IsClosed (P : Set (StrongDual ℂ M)))
    (hvec : ∀ ξ η : H, vectorFunctional M ξ η ∈ P) : normalFunctionalSpace M ≤ P := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    exact hvec ξ η
  · exact hP

end VonNeumannAlgebra

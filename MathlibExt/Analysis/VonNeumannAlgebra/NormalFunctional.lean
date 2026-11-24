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
# The actual closed space of normal functionals

For a concrete von Neumann algebra on an arbitrary complete complex Hilbert
space, take the norm-closed complex linear span of its actual vector
functionals in the original continuous dual. Evaluation, norm and linear
operations are inherited from that dual. Completeness follows from the
closed-subspace construction.

This supplies the explicit normal-functional carrier for the predual
convention in Connes V Appendix A and Takesaki Definition 3.1.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra

open MathlibExt.Analysis.CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original operator norm bounds each actual vector coefficient. -/
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

/-- The concrete-algebra specialization of representation coefficients,
with the original vector order and literal subtype representation. -/
noncomputable def vectorFunctional (M : VonNeumannAlgebra H) (ξ η : H) : StrongDual ℂ M :=
  representationCoefficient (A := M) M.toStarSubalgebra.subtype η ξ

/-- Evaluation of a vector functional is the original Hilbert coefficient. -/
@[simp]
theorem vectorFunctional_apply (M : VonNeumannAlgebra H) (ξ η : H) (x : M) :
    vectorFunctional M ξ η x = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ := by
  change representationCoefficient (A := M) M.toStarSubalgebra.subtype η ξ x =
    ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ
  rw [representationCoefficient_apply (A := M) M.toStarSubalgebra.subtype η ξ x]
  rfl

/-- The dual norm of an actual vector functional is bounded by the two vector norms. -/
theorem norm_vectorFunctional_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖vectorFunctional M ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  simpa only [vectorFunctional, mul_comm] using
    norm_representationCoefficient_le (A := M) M.toStarSubalgebra.subtype η ξ

/-- The norm-closed complex span of the actual vector functionals in the original dual. -/
noncomputable def normalFunctionalSpace (M : VonNeumannAlgebra H) :
    Submodule ℂ (StrongDual ℂ M) :=
  (Submodule.span ℂ (Set.range fun p : H × H => vectorFunctional M p.1 p.2)).topologicalClosure

/-- Every actual vector functional lies in the canonical closed span. -/
theorem vectorFunctional_mem_normalFunctionalSpace (M : VonNeumannAlgebra H) (ξ η : H) :
    vectorFunctional M ξ η ∈ normalFunctionalSpace M :=
  (Submodule.le_topologicalClosure _)
    (Submodule.subset_span (Set.mem_range_self (ξ, η)))

/-- The canonical normal functional space is closed for the original continuous-dual norm. -/
theorem normalFunctionalSpace_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (normalFunctionalSpace M : Set (StrongDual ℂ M)) :=
  Submodule.isClosed_topologicalClosure _

/-- The original dual norm makes the actual closed normal-functional carrier a Banach space. -/
instance normalFunctionalSpace_completeSpace (M : VonNeumannAlgebra H) :
    CompleteSpace (normalFunctionalSpace M) :=
  (normalFunctionalSpace_isClosed M).isComplete.completeSpace_coe

/-- Any closed complex subspace containing every vector functional contains their actual closed span. -/
theorem normalFunctionalSpace_le (M : VonNeumannAlgebra H)
    {P : Submodule ℂ (StrongDual ℂ M)} (hP : IsClosed (P : Set (StrongDual ℂ M)))
    (hvec : ∀ ξ η : H, vectorFunctional M ξ η ∈ P) : normalFunctionalSpace M ≤ P := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    exact hvec ξ η
  · exact hP

end VonNeumannAlgebra

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


public import MathlibExt.Analysis.CStarAlgebra.Module.Generation
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

/-!
# Countable generation transported by a module unitary

A countable right-coefficient generating sequence remains generating after a
unitary module equivalence. The proof transports the dense span through the
actual continuous linear equivalence; no dense-range output is assumed.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped RightActions

namespace CStarModule.IsCountablyGenerated

universe uB uE uF

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- Countable generation is preserved by a unitary equivalence of right
C-star modules. -/
theorem unitaryEquiv
    (hE : CStarModule.IsCountablyGenerated (B := B) (E := E))
    (U : CStarModule.UnitaryEquiv B E F) :
    CStarModule.IsCountablyGenerated (B := B) (E := F) := by
  rcases hE with ⟨g, hg⟩
  let gF : ℕ → F := fun n => U (g n)
  let M : Submodule ℂ F :=
    Submodule.span ℂ (Set.range fun p : ℕ × B => gF p.1 <• p.2)
  let C : Submodule ℂ F := M.topologicalClosure
  have hCclosed : IsClosed (C : Set F) := M.isClosed_topologicalClosure
  let P : Submodule ℂ E :=
    Submodule.comap U.toAdjointable.toContinuousLinearMap.toLinearMap C
  have hPclosed : IsClosed (P : Set E) := by
    change IsClosed (U ⁻¹' (C : Set F))
    exact hCclosed.preimage U.isometry.continuous
  have hspan :
      Submodule.span ℂ (Set.range fun p : ℕ × B => g p.1 <• p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n, b⟩, rfl⟩
    apply Submodule.mem_comap.mpr
    change U.toAdjointable (g n <• b) ∈ C
    rw [U.toAdjointable.map_right_smul]
    exact M.le_topologicalClosure
      (Submodule.subset_span ⟨(n, b), rfl⟩)
  have hPtop : (⊤ : Submodule ℂ E) ≤ P := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp hg]
    exact Submodule.topologicalClosure_minimal _ hspan hPclosed
  refine ⟨gF, Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_⟩
  apply top_unique
  intro y _hy
  have hy : U (U.symm y) ∈ C :=
    Submodule.mem_comap.mp (hPtop (show U.symm y ∈ (⊤ : Submodule ℂ E) by trivial))
  rwa [U.apply_symm_apply] at hy

end CStarModule.IsCountablyGenerated

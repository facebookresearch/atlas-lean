/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.HahnBanachOneStepExtension

/-!
# One-step Hahn–Banach extension

The one-step extension lemma is the inductive step in the textbook proof
of the Hahn–Banach theorem: a bounded linear functional on a subspace `M`
can be extended to the strictly larger subspace `M ⊔ 𝕜 ∙ x₀`, for any
`x₀ ∉ M`, with the same bound `C`. Unlike the full Hahn–Banach theorem,
which extends to the whole space at once, this statement keeps control of
the intermediate subspace, which is what an inductive / Zorn-lemma
construction of the extension needs.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`,
`HahnBanach.hahn_banach_one_step_extension_bound` (Lemma, March 2, 2021
lecture). The statement is ported verbatim (up to the namespace).
-/

open Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **One-step Hahn–Banach extension.** Let `M ⊆ E` be a subspace and
`f : M →L[𝕜] 𝕜` a bounded linear functional with `‖f m‖ ≤ C ‖m‖` for all
`m ∈ M`. If `x₀ ∉ M`, then there exists a bounded linear functional `g` on
the strictly larger subspace `M'' = M ⊔ 𝕜 ∙ x₀` extending `f` and
satisfying the same bound `‖g v‖ ≤ C ‖v‖` for all `v ∈ M''`. -/
theorem hahn_banach_one_step_extension_bound
    (M : Subspace 𝕜 E) (f : ↥M →L[𝕜] 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hf_bound : ∀ m : M, ‖f m‖ ≤ C * ‖(m : E)‖)
    (x₀ : E) (hx₀ : x₀ ∉ M) :
    ∃ g : ↥(M ⊔ 𝕜 ∙ x₀) →L[𝕜] 𝕜,
      (∀ m : M, g ⟨↑m, mem_sup_left m.2⟩ = f m) ∧
      (∀ v : ↥(M ⊔ 𝕜 ∙ x₀), ‖g v‖ ≤ C * ‖(v : E)‖) ∧
      M < M ⊔ 𝕜 ∙ x₀ := by
  obtain ⟨G, hG_ext, hG_norm⟩ := exists_extension_norm_eq M f
  refine ⟨G.comp (M ⊔ 𝕜 ∙ x₀).subtypeL, ?_, ?_, ?_⟩
  · intro m
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hG_ext m
  · intro v
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have hG_le : ‖G‖ ≤ C := by
      rw [hG_norm]
      exact ContinuousLinearMap.opNorm_le_bound f hC hf_bound
    calc ‖G (v : E)‖ ≤ ‖G‖ * ‖(v : E)‖ := G.le_opNorm (v : E)
      _ ≤ C * ‖(v : E)‖ := mul_le_mul_of_nonneg_right hG_le (norm_nonneg _)
  · apply lt_of_le_of_ne le_sup_left
    intro h
    apply hx₀
    have hx₀_mem : x₀ ∈ (M ⊔ 𝕜 ∙ x₀ : Submodule 𝕜 E) :=
      mem_sup_right (mem_span_singleton_self x₀)
    rwa [← h] at hx₀_mem

end MathlibExt.Analysis.FunctionalAnalysis.HahnBanachOneStepExtension

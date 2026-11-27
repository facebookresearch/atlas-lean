/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Nearest points to closed convex sets in reflexive Banach spaces

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_64.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. The original ATLAS import converted
`theorem ma_proofbench_l2_64 … := by sorry` into the Batteries `theorem_wanted`
`exists_norm_sub_eq_iInf_of_reflexive_of_convex_of_isClosed`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
This change proves the statement and moves it to the proved library.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Semicontinuity.Basic

/-! # Nearest points in reflexive Banach spaces

A bounded closed convex slice is compact in the weak topology, using the weak-star
bidual embedding. The distance to a fixed point is weakly lower semicontinuous because
its sublevel sets are closed balls, and it attains its infimum on that slice.
-/

open Set Metric NormedSpace

namespace MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem isClosed_weak_image {C : Set X} (hc : IsClosed C) (hv : Convex ℝ C) :
    IsClosed (toWeakSpace ℂ X '' C) := by
  have h := hv.toWeakSpace_closure ℂ
  rw [hc.closure_eq] at h
  rw [h]
  exact isClosed_closure

private theorem isCompact_weak_image {C : Set X} (hc : IsClosed C) (hv : Convex ℝ C)
    (hb : Bornology.IsBounded C) (href : Function.Surjective (inclusionInDoubleDual ℂ X)) :
    IsCompact (toWeakSpace ℂ X '' C) := by
  have hclosed := isClosed_weak_image hc hv
  rw [← hclosed.closure_eq]
  apply isCompact_closure_of_isBounded ℂ X
  · rw [Set.preimage_image_eq _ (toWeakSpace ℂ X).injective]
    exact hb
  · intro Φ _
    obtain ⟨x, hx⟩ := href (WeakDual.toStrongDual Φ)
    refine ⟨toWeakSpace ℂ X x, ?_⟩
    rw [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply, hx,
      WeakDual.toWeakDual_toStrongDual]

private theorem lowerSemicontinuous_weak_dist (x₀ : X) :
    LowerSemicontinuous (fun w : WeakSpace ℂ X => ‖x₀ - (toWeakSpace ℂ X).symm w‖) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  have hEq : (fun w : WeakSpace ℂ X => ‖x₀ - (toWeakSpace ℂ X).symm w‖) ⁻¹' Iic r =
      toWeakSpace ℂ X '' closedBall x₀ r := by
    ext w
    constructor
    · intro hw
      refine ⟨(toWeakSpace ℂ X).symm w, ?_, LinearEquiv.apply_symm_apply _ _⟩
      rw [mem_closedBall, dist_comm, dist_eq_norm]
      exact hw
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closedBall, dist_comm, dist_eq_norm] at hy
      simpa only [mem_preimage, mem_Iic, LinearEquiv.symm_apply_apply] using hy
  rw [hEq]
  exact isClosed_weak_image isClosed_closedBall (convex_closedBall x₀ r)

end

/-- **Nearest points in reflexive Banach spaces.** Let $X$ be a reflexive complex Banach space, that
is, the canonical embedding of $X$ into its double dual is surjective, and let $C \subseteq X$ be a
nonempty closed convex set. Then for every $x_0 \in X$ there is $y_0 \in C$ such that
$\|x_0 - y_0\| = \inf_{y \in C} \|x_0 - y\|$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_64.lean`
at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_norm_sub_eq_iInf_of_reflexive_of_convex_of_isClosed
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (hX_reflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ X)) (C : Set X)
  (hC_closed : IsClosed C) (_hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
  ∀ x₀ : X, ∃ y₀ ∈ C, ‖x₀ - y₀‖ = ⨅ y : C, ‖x₀ - (y : X)‖ := by
  intro x₀
  obtain ⟨z, hz⟩ := hC_nonempty
  let r := ‖x₀ - z‖
  let K := C ∩ closedBall x₀ r
  let e := toWeakSpace ℂ X
  let g (w : WeakSpace ℂ X) := ‖x₀ - e.symm w‖
  have hzK : z ∈ K := by
    refine ⟨hz, ?_⟩
    rw [mem_closedBall, dist_comm, dist_eq_norm]
  have hcompact : IsCompact (e '' K) := isCompact_weak_image
    (hC_closed.inter isClosed_closedBall) (_hC_convex.inter (convex_closedBall _ _))
    (isBounded_closedBall.subset inter_subset_right) hX_reflexive
  have hls : LowerSemicontinuous g := lowerSemicontinuous_weak_dist x₀
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (⟨e z, ⟨z, hzK, rfl⟩⟩ : (e '' K).Nonempty) hcompact (hls.lowerSemicontinuousOn _)
  have hle (y : X) (hy : y ∈ K) : ‖x₀ - y₀‖ ≤ ‖x₀ - y‖ := by
    have h := isMinOn_iff.mp hmin (e y) ⟨y, hy, rfl⟩
    simpa only [g, LinearEquiv.symm_apply_apply] using h
  have hleAll (y : C) : ‖x₀ - y₀‖ ≤ ‖x₀ - (y : X)‖ := by
    by_cases hy : ‖x₀ - (y : X)‖ ≤ r
    · apply hle y
      refine ⟨y.property, ?_⟩
      rw [mem_closedBall, dist_comm, dist_eq_norm]
      exact hy
    · exact (hle z hzK).trans (le_of_lt (lt_of_not_ge hy))
  let : Nonempty C := ⟨⟨z, hz⟩⟩
  have hBelow : BddBelow (Set.range (fun y : C => ‖x₀ - (y : X)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _
  exact ⟨y₀, hy₀.1, le_antisymm (le_ciInf hleAll) (ciInf_le hBelow ⟨y₀, hy₀.1⟩)⟩

end MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted

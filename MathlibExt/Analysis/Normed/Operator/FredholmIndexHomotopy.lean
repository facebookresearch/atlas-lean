/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Homotopy invariance of the Fredholm index

The Fredholm index is locally constant in the operator norm (Mathlib:
`ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq`). A continuous
path of Fredholm operators therefore has constant index, because its
parameter set is (pre)connected and the index takes values in the discrete
space `ℤ`.

In particular, adding a finite-rank operator does not change the index: the
segment `T + t • F`, `t ∈ [0, 1]`, is a continuous path of Fredholm
operators (Mathlib: `ContinuousLinearMap.IsFredholm.add_hasFiniteRange`).
This is the finite-rank case of the classical invariance of the index under
compact perturbations. The full compact-perturbation statement is *not*
proved here: it would require the Atkinson characterisation with compact
(rather than finite-range) errors, which is not in Mathlib.

## Main declarations

* `index_eq_of_preconnected`: the index is constant along a continuous
  family of Fredholm operators indexed by a preconnected set.
* `index_eq_of_continuousOn_Icc`: the segment form, for a path defined on
  `[0, 1]`.
* `index_eq_of_continuous_path`: the segment form, for a globally continuous
  path `ℝ → (E →L[𝕜] F)`.
* `index_add_hasFiniteRange`: `(T + F).index = T.index` when `F` has finite
  range, plus the `F + T` and `T - F` forms.
* `hasFiniteRange_smulRight`: a rank-one operator `c.smulRight y` has finite
  range.
-/

namespace MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy

open ContinuousLinearMap Filter Set Topology

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E]

/-- The Fredholm index is constant along a continuous family of Fredholm
operators indexed by a preconnected set, because the index is locally
constant (Mathlib) and takes values in the discrete space `ℤ`. -/
theorem index_eq_of_preconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {γ : X → E →L[𝕜] F} (hγ : ContinuousOn γ s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hfred : ∀ z ∈ s, (γ z).IsFredholm) : (γ x).index = (γ y).index := by
  have hcont : ContinuousOn (fun z => (γ z).index) s := by
    intro z hz
    have h1 : ∀ᶠ T in 𝓝 (γ z), T.index = (γ z).index :=
      (hfred z hz).eventually_nhds_index_eq
    have h2 : ∀ᶠ w in 𝓝[s] z, (γ w).index = (γ z).index :=
      (hγ z hz).eventually h1
    have h2eq : (fun w => (γ w).index) =ᶠ[𝓝[s] z] (fun _ => (γ z).index) := h2
    exact Filter.Tendsto.congr' h2eq.symm tendsto_const_nhds
  exact hs.constant hcont hx hy

/-- The Fredholm index is constant along a continuous path of Fredholm
operators on `[0, 1]`. -/
theorem index_eq_of_continuousOn_Icc {γ : ℝ → E →L[𝕜] F}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hfred : ∀ t ∈ Icc (0 : ℝ) 1, (γ t).IsFredholm) :
    (γ 0).index = (γ 1).index :=
  index_eq_of_preconnected isPreconnected_Icc hγ
    ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ hfred

/-- The Fredholm index is constant along a globally continuous path of
Fredholm operators on `[0, 1]`. -/
theorem index_eq_of_continuous_path {γ : ℝ → E →L[𝕜] F} (hγ : Continuous γ)
    (hfred : ∀ t ∈ Icc (0 : ℝ) 1, (γ t).IsFredholm) :
    (γ 0).index = (γ 1).index :=
  index_eq_of_continuousOn_Icc hγ.continuousOn hfred

end General

/-- A rank-one operator has finite range. -/
theorem hasFiniteRange_smulRight {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    {c : E →L[𝕜] 𝕜} {y : F} :
    (c.smulRight y).toLinearMap.HasFiniteRange := by
  by_cases hc : c = 0
  · subst hc
    simp [ContinuousLinearMap.zero_smulRight]
  · rw [LinearMap.hasFiniteRange_iff_range,
      ContinuousLinearMap.range_smulRight_apply hc]
    exact Submodule.fg_span_singleton y

-- The finite-rank theorems need a real parameter, so they are stated for
-- `RCLike 𝕜` (i.e. `𝕜 = ℝ` or `ℂ`) in their own section: combining a
-- `NontriviallyNormedField 𝕜` variable with a separate `RCLike 𝕜` variable
-- would create overlapping instances for the field structure.
section RCLikeSection

variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E]

/-- Adding a finite-rank operator does not change the Fredholm index.
The proof follows the segment `T + t • F`, `t ∈ [0, 1]`, which is a
continuous path of Fredholm operators. -/
theorem index_add_hasFiniteRange {T G : E →L[𝕜] F} (hT : T.IsFredholm)
    (hG : G.toLinearMap.HasFiniteRange) : (T + G).index = T.index := by
  have hfred : ∀ t ∈ Icc (0 : ℝ) 1, (T + (t : 𝕜) • G).IsFredholm := fun t _ =>
    hT.add_hasFiniteRange (by simpa using hG.smul (t : 𝕜))
  have hcoe : Continuous (fun t : ℝ => (t : 𝕜)) := RCLike.continuous_ofReal
  have hcont : Continuous (fun t : ℝ => T + (t : 𝕜) • G) :=
    continuous_const.add (hcoe.smul continuous_const)
  have h := index_eq_of_continuous_path hcont hfred
  simpa using h.symm

/-- Adding a finite-rank operator on the left does not change the
Fredholm index. -/
theorem index_hasFiniteRange_add {T G : E →L[𝕜] F} (hT : T.IsFredholm)
    (hG : G.toLinearMap.HasFiniteRange) : (G + T).index = T.index := by
  rw [add_comm]
  exact index_add_hasFiniteRange hT hG

/-- Subtracting a finite-rank operator does not change the Fredholm
index. -/
theorem index_sub_hasFiniteRange {T G : E →L[𝕜] F} (hT : T.IsFredholm)
    (hG : G.toLinearMap.HasFiniteRange) : (T - G).index = T.index := by
  rw [sub_eq_add_neg]
  refine index_add_hasFiniteRange hT ?_
  simpa using hG.neg

end RCLikeSection

end MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy

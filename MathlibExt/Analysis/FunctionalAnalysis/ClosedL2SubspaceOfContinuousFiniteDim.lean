/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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

Attribution and modification notice: the statement is adapted from openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_11.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; also distributed in the Hugging Face dataset
openbmb/MA-ProofBench), under the MIT license above. The ATLAS import converted the statement to
`theorem_wanted`, named and documented it in the namespace below, and used a public module import.
This file preserves the ATLAS proposition and declaration documentation, replaces the wanted
statement with a proof, and narrows the imports.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Operator.Banach
import MathlibExt.MeasureTheory.Function.LpDimensionBound

/-!
# Closed subspaces of L² with continuous representatives

On the closed unit interval the bounded inverse theorem controls the supremum norm of each
continuous representative by its L² norm. This gives the almost-everywhere pointwise bound
needed by the existing finite-dimensionality criterion for subspaces of L².
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted

private abbrev I := Icc (0 : ℝ) 1
private abbrev L := Lp ℝ (2 : ENNReal) (volume : Measure I)

/-- Every nonempty relatively open subset of the closed interval has positive measure. -/
private theorem interval_open_pos : (volume : Measure I).IsOpenPosMeasure := by
  refine ⟨?_⟩
  intro U hU hne
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hne
  have hcl : (x : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact x.property
  have hnonempty : (O ∩ Ioo (0 : ℝ) 1).Nonempty :=
    mem_closure_iff.mp hcl O hO hx
  have hpos := (hO.inter isOpen_Ioo).measure_pos (volume : Measure ℝ) hnonempty
  have hsubset : O ∩ Ioo (0 : ℝ) 1 ⊆ Subtype.val '' ((Subtype.val : I → ℝ) ⁻¹' O) := by
    intro y hy
    exact ⟨⟨y, Ioo_subset_Icc_self hy.2⟩, hy.1, rfl⟩
  rw [unitInterval.volume_apply]
  exact (hpos.trans_le (measure_mono hsubset)).ne'

/-- The inverse on the closed subspace takes an L² class to its continuous representative. -/
private theorem exists_representative_map (H : Submodule ℝ L)
    (hclosed : IsClosed (H : Set L))
    (hsubset : H ≤ (ContinuousMap.toLp (E := ℝ) (p := (2 : ENNReal))
      (volume : Measure I) ℝ).range) :
    ∃ T : H →L[ℝ] C(I, ℝ), ∀ y : H, (y : L) =ᵐ[volume] T y := by
  let A : C(I, ℝ) →L[ℝ] L := ContinuousMap.toLp 2 volume ℝ
  let S := H.comap A.toLinearMap
  have hS : IsClosed (S : Set C(I, ℝ)) := hclosed.preimage A.continuous
  let : CompleteSpace S := hS.completeSpace_coe
  let : CompleteSpace H := hclosed.completeSpace_coe
  let : (volume : Measure I).IsOpenPosMeasure := interval_open_pos
  have hA : Function.Injective A := ContinuousMap.toLp_injective _
  let B : S →L[ℝ] H := A.restrict fun _ hf ↦ hf
  have hB : Function.Bijective B := by
    constructor
    · intro f g hfg
      exact Subtype.ext (hA (congrArg Subtype.val hfg))
    · intro y
      obtain ⟨f, hf⟩ := LinearMap.mem_range.mp (hsubset y.property)
      exact ⟨⟨f, show A f ∈ H by rw [show A f = (y : L) from hf]; exact y.property⟩,
        Subtype.ext hf⟩
  let e₀ : S ≃ₗ[ℝ] H := LinearEquiv.ofBijective B.toLinearMap hB
  have hinv : Continuous e₀.symm := by
    rw [continuous_def]
    intro U hU
    rw [← e₀.image_eq_preimage_symm]
    exact ContinuousLinearMap.isOpenMap (σ := RingHom.id ℝ) B hB.surjective U hU
  let inv : H →L[ℝ] S := ⟨e₀.symm.toLinearMap, hinv⟩
  let T : H →L[ℝ] C(I, ℝ) := S.subtypeL.comp inv
  refine ⟨T, fun y ↦ ?_⟩
  have hy : A (T y) = (y : L) := congrArg Subtype.val (e₀.apply_symm_apply y)
  rw [← hy]
  exact ContinuousMap.coeFn_toLp (volume : Measure I) (T y)

/-- **Closed subspaces of $L^2([0,1])$ inside $C([0,1])$ are finite-dimensional.** Let $H$ be a
closed linear subspace of the real space $L^2([0,1])$ with respect to Lebesgue measure, and
suppose that every element of $H$ is the class of a continuous function $[0,1] \to \mathbb{R}$.
Then $H$ is finite-dimensional.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_11.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem finiteDimensional_of_isClosed_of_le_range_toLp
    (H : Submodule ℝ (MeasureTheory.Lp ℝ (2 : ENNReal)
        (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))))
    (hclosed : IsClosed (H : Set (MeasureTheory.Lp ℝ (2 : ENNReal)
          (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1)))))
    (hsubset : H ≤ (ContinuousMap.toLp (E := ℝ) (p := (2 : ENNReal))
        (MeasureTheory.volume : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1)) ℝ).range) :
    FiniteDimensional ℝ ↥H := by
  obtain ⟨T, hT⟩ := exists_representative_map H hclosed hsubset
  refine (Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm H ‖T‖ ?_).1
  intro φ hφ
  let y : H := ⟨φ, hφ⟩
  filter_upwards [hT y] with x hx
  change ‖(y : L) x‖ ≤ ‖T‖ * ‖y‖
  rw [hx]
  exact (ContinuousMap.norm_coe_le_norm (T y) x).trans (T.le_opNorm y)

end MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted

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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

/-!
# Closed subspaces of L² with continuous representatives

On the closed unit interval the bounded inverse theorem bounds the supremum norm of a continuous
representative by its L² norm. Applying that bound to finite linear combinations of orthonormal
vectors bounds their pointwise squared sum. Its integral counts the vectors, so the dimensions of
finite spans in the subspace are uniformly bounded.
-/

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

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

/-- Apply evaluation to the linear combination with the evaluation values as coefficients. -/
private theorem pointwise_sum_sq_le {H : Submodule ℝ L}
    (T : H →L[ℝ] C(I, ℝ)) {ι : Type*} [Fintype ι] (e : ι → H)
    (he : Orthonormal ℝ e) (x : I) : ∑ i, (T (e i) x) ^ 2 ≤ ‖T‖ ^ 2 := by
  classical
  let a : ι → ℝ := fun i ↦ T (e i) x
  let v : H := ∑ i, a i • e i
  have hq : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [v, starRingEnd_apply, star_trivial, pow_two] using
      he.inner_sum a a Finset.univ
  have hv : T v x = ∑ i, (a i) ^ 2 := by
    simp only [v, map_sum, map_smul, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul, pow_two, a]
  have hb : ‖T v x‖ ≤ ‖T‖ * ‖v‖ :=
    (ContinuousMap.norm_coe_le_norm (T v) x).trans (T.le_opNorm v)
  have hb' : ‖v‖ ^ 2 ≤ ‖T‖ * ‖v‖ := by
    rw [hv, ← hq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
    exact hb
  have hvT : ‖v‖ ≤ ‖T‖ := by
    by_contra! hgt
    have hp : 0 < ‖v‖ := (norm_nonneg T).trans_lt hgt
    nlinarith [mul_pos hp (sub_pos.mpr hgt)]
  exact hq ▸ (pow_le_pow_left₀ (norm_nonneg v) hvT 2)

/-- Integrating the pointwise bound gives one unit of mass per orthonormal vector. -/
private theorem card_le_of_orthonormal {H : Submodule ℝ L}
    (T : H →L[ℝ] C(I, ℝ)) (hT : ∀ y : H, (y : L) =ᵐ[volume] T y)
    {ι : Type*} [Fintype ι] {e : ι → H} (he : Orthonormal ℝ e) :
    (Fintype.card ι : ℝ) ≤ ‖T‖ ^ 2 := by
  classical
  have hi (i : ι) : Integrable (fun x : I ↦ (T (e i) x) ^ 2) volume :=
    ((T (e i)).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hone (i : ι) : ∫ x : I, (T (e i) x) ^ 2 = 1 := by
    have hinner : inner ℝ (e i : L) (e i : L) = 1 := by
      rw [real_inner_self_eq_norm_sq]
      change ‖e i‖ ^ 2 = 1
      rw [he.norm_eq_one i, one_pow]
    rw [L2.inner_def] at hinner
    refine (integral_congr_ae ?_).trans hinner
    filter_upwards [hT (e i)] with x hx
    rw [hx]
    simp [Real.norm_eq_abs, sq_abs]
  have h := integral_mono (integrable_finsetSum Finset.univ fun i _ ↦ hi i)
    (integrable_const (‖T‖ ^ 2)) (pointwise_sum_sq_le T e he)
  rw [integral_finsetSum _ (fun i _ ↦ hi i)] at h
  simpa [hone] using h

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
  classical
  obtain ⟨T, hT⟩ := exists_representative_map H hclosed hsubset
  apply Module.rank_lt_aleph0_iff.mp
  refine lt_of_le_of_lt (rank_le (n := ⌈‖T‖ ^ 2⌉₊) ?_) Cardinal.natCast_lt_aleph0
  intro s hs
  let j : Fin s.card ≃ ↥s := (Finset.equivFinOfCardEq (s := s) rfl).symm
  let e : Fin s.card → H := fun i ↦ j i
  have he : LinearIndependent ℝ e := hs.comp j j.injective
  have hon := InnerProductSpace.gramSchmidtNormed_orthonormal he
  have hb := card_le_of_orthonormal T hT hon
  have hc : (s.card : ℝ) ≤ ‖T‖ ^ 2 := by simpa only [Fintype.card_fin] using hb
  exact_mod_cast hc.trans (Nat.le_ceil (‖T‖ ^ 2))

end MathlibExt.Analysis.FunctionalAnalysis.ClosedL2SubspaceOfContinuousFiniteDimWanted

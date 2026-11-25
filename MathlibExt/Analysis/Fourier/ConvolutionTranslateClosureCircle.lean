/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_12.lean` (openbmb/ma-proofbench, commit 31bab4c):
the circle abbreviation and the statement of the closure theorem.
Authors: L. Pu et al. (MA-ProofBench).
Licensed under the MIT License.

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
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Convolutions and translates on the circle

For a real integrable function on the circle, its convolutions with integrable kernels
and the finite linear combinations of its translates have the same closure in `L¹`.
-/

@[expose] public section

open MeasureTheory Topology
open scoped BigOperators Convolution

namespace MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted

local instance instFactLtRealOfNatHMulPi_wantedExt : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨by nlinarith [Real.pi_pos]⟩

/-- **The circle $\mathbb{R}/2\pi\mathbb{Z}$.** The circle $T = \mathbb{R}/2\pi\mathbb{Z}$, the
quotient of the additive group $\mathbb{R}$ by its subgroup $2\pi\mathbb{Z}$. -/
abbrev T := AddCircle (2 * Real.pi)

private noncomputable abbrev L1Circle := Lp ℝ 1 (volume : Measure T)

private noncomputable def translate (v : L1Circle) (t : T) : L1Circle :=
  Lp.compMeasurePreserving (· - t) (measurePreserving_sub_right volume t) v

private lemma continuous_translate (v : L1Circle) : Continuous (translate v) := by
  let shift (t : T) : C(T, T) := ⟨(· - t), continuous_id.sub continuous_const⟩
  have hs : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry _ <|
    continuous_snd.sub continuous_fst
  exact continuous_const.compMeasurePreservingLp hs (measurePreserving_sub_right volume)
    (by simp)

private lemma coe_translate {f : T → ℝ} (hf : MemLp f 1 volume) (t : T) :
    ⇑(translate (hf.toLp f) t) =ᵐ[volume] fun x => f (x - t) :=
  (Lp.coeFn_compMeasurePreserving _ _).trans <|
    (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp

private lemma integrable_weighted_translate (v : L1Circle) {g : T → ℝ} (hg : Integrable g) :
    Integrable (fun t => g t • translate v t) :=
  hg.smul_bdd ‖v‖ (continuous_translate v).aestronglyMeasurable <|
    .of_forall fun t => (Lp.norm_compMeasurePreserving v (measurePreserving_sub_right volume t)).le

-- Integration over a measurable set tests an L¹ class by a continuous linear functional.
private noncomputable def testIntegral (s : Set T) : L1Circle →L[ℝ] ℝ :=
  L1.integralCLM.comp (LpToLpRestrictCLM T ℝ ℝ volume 1 s)

private lemma testIntegral_apply (s : Set T) (u : L1Circle) :
    testIntegral s u = ∫ x in s, u x := by
  rw [testIntegral, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s u)

private lemma coe_integral_translate {f g : T → ℝ} (hf : MemLp f 1 volume) (hg : Integrable g) :
    ⇑(∫ t, g t • translate (hf.toLp f) t) =ᵐ[volume] f ⋆ g := by
  have hfi := memLp_one_iff_integrable.mp hf
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _)
    (hfi.integrable_convolution _ hg)
  intro s _ _
  rw [← testIntegral_apply, ← (testIntegral s).integral_comp_comm
    (integrable_weighted_translate _ hg)]
  calc
    _ = ∫ t, ∫ x in s, g t * f (x - t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [map_smul, testIntegral_apply, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (coe_translate hf t)] with x hx
      exact congrArg (g t * ·) hx
    _ = ∫ x in s, ∫ t, g t * f (x - t) := by
      apply integral_integral_swap
      exact (hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hfi).swap.mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [convolution_eq_swap]
      simp [mul_comm]

-- Finite sums indexed by `Fin N` represent exactly the algebraic span.
private lemma mem_translate_span (v : L1Circle) (u : L1Circle) :
    u ∈ Submodule.span ℝ (Set.range (translate v)) ↔
      ∃ N : ℕ, ∃ a : Fin N → ℝ, ∃ τ : Fin N → T, u = ∑ i, a i • translate v (τ i) := by
  classical
  constructor
  · intro hu
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
    let e := c.support.equivFin
    refine ⟨_, fun i => c (e.symm i), fun i => e.symm i, ?_⟩
    change ∑ t ∈ c.support, c t • translate v t = _
    rw [← Finset.sum_coe_sort]
    exact (e.symm.sum_comp (fun t : c.support => c t • translate v t)).symm
  · rintro ⟨N, a, τ, rfl⟩
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (τ i)))

private lemma coe_sum_translate {f : T → ℝ} (hf : MemLp f 1 volume)
    {N : ℕ} (a : Fin N → ℝ) (τ : Fin N → T) :
    ⇑(∑ i, a i • translate (hf.toLp f) (τ i)) =ᵐ[volume]
      fun x => ∑ i, a i * f (x - τ i) := by
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h (i : Fin N) : ⇑(a i • translate (hf.toLp f) (τ i)) =ᵐ[volume]
      fun x => a i * f (x - τ i) := (Lp.coeFn_smul _ _).trans <|
    (coe_translate hf (τ i)).fun_comp (a i * ·)
  filter_upwards [Filter.eventually_all.mpr h] with x hx
  simpa only [Finset.sum_apply] using Finset.sum_congr rfl (fun i _ => hx i)

-- The kernels are ordinary integrable functions, so membership carries an explicit witness.
private noncomputable def convolutionSpace (v : L1Circle) : Submodule ℝ L1Circle where
  carrier := {u | ∃ g : T → ℝ, Integrable g ∧ u = ∫ t, g t • translate v t}
  zero_mem' := ⟨0, integrable_zero _ _ _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨k, hk, rfl⟩
    refine ⟨g + k, hg.add hk, ?_⟩
    simp only [Pi.add_apply, add_smul, integral_add (integrable_weighted_translate v hg)
      (integrable_weighted_translate v hk)]
  smul_mem' := by
    rintro a _ ⟨g, hg, rfl⟩
    exact ⟨a • g, hg.smul a, by simp [smul_smul, ← integral_smul]⟩

private lemma integral_mem_span_closure (v : L1Circle) {g : T → ℝ} (hg : Integrable g) :
    (∫ t, g t • translate v t) ∈
      (Submodule.span ℝ (Set.range (translate v))).topologicalClosure := by
  let S := (Submodule.span ℝ (Set.range (translate v))).topologicalClosure
  have : IsClosed (S : Set L1Circle) := Submodule.isClosed_topologicalClosure _
  change (∫ t, g t • translate v t) ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL _ = 0
  rw [← S.mkQL.integral_comp_comm (integrable_weighted_translate v hg)]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  rw [map_smul]
  have ht : translate v t ∈ S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self t))
  simp only [Submodule.mkQL_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr ht,
    smul_zero, Pi.zero_apply]

-- Indicator kernels put every set integral of the orbit in the convolution space. In the
-- quotient by its closure the continuous orbit therefore vanishes almost everywhere, hence
-- everywhere since volume gives positive mass to every nonempty open set.
private lemma translate_mem_convolution_closure (v : L1Circle) (t : T) :
    translate v t ∈ (convolutionSpace v).topologicalClosure := by
  let S := (convolutionSpace v).topologicalClosure
  have : IsClosed (S : Set L1Circle) := Submodule.isClosed_topologicalClosure _
  let q := S.mkQL
  have hc : Continuous (fun t => q (translate v t)) := q.continuous.comp (continuous_translate v)
  have hi : Integrable (translate v) :=
    (continuous_translate v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (fun t => q (translate v t)) =ᵐ[volume] 0 := by
    apply (q.integrable_comp hi).ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    rw [q.integral_comp_comm hi.integrableOn]
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    apply (convolutionSpace v).le_topologicalClosure
    refine ⟨s.indicator (fun _ => (1 : ℝ)), (integrable_const _).indicator hs, ?_⟩
    rw [← integral_indicator hs]
    congr 1
    funext x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  exact (Submodule.Quotient.mk_eq_zero S).mp <|
    congrFun (Measure.eq_of_ae_eq hz hc continuous_zero) t

/-- **Convolutions and linear combinations of translates have the same closure.** Let
$T = \mathbb{R}/2\pi\mathbb{Z}$ with the measure induced by Lebesgue measure on $[0, 2\pi)$, and
let $L^1(T)$ be the space of real-valued integrable functions on $T$ modulo equality almost
everywhere. Fix a real-valued integrable $f$ on $T$. Let $B_f \subseteq L^1(T)$ be the set of
classes of the finite linear combinations of translates
$x \mapsto \sum_{i=1}^N a_i f(x - \tau_i)$ with $N \in \mathbb{N}$, $a_i \in \mathbb{R}$ and
$\tau_i \in T$, and let $M_f \subseteq L^1(T)$ be the set of classes of the convolutions
$(f * g)(x) = \int_T f(y)\, g(x - y)\,dy$ with $g$ real-valued and integrable on $T$. Then $M_f$
and $B_f$ have the same closure in $L^1(T)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Commutative Banach algebras and commutative topological algebras),
`benchmark/level2/ma_proofbench_l2_12.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem closure_convolution_set_eq_closure_translate_span
    (f : T → ℝ)
    (hf : MemLp f 1 (volume : Measure T))
    (Bf Mf : Set (Lp ℝ 1 (volume : Measure T)))
    (hBf : Bf =
      {u : Lp ℝ 1 (volume : Measure T) | ∃ N : ℕ, ∃ a : Fin N → ℝ, ∃ τ : Fin N → T,
          (u : T → ℝ) =ᵐ[(volume : Measure T)]
            (fun x : T => ∑ i : Fin N, a i * f (x - τ i))})
    (hMf : Mf =
      {u : Lp ℝ 1 (volume : Measure T) | ∃ g : T → ℝ, MemLp g 1 (volume : Measure T) ∧
          (u : T → ℝ) =ᵐ[(volume : Measure T)] (f ⋆ g)}) :
    closure Mf = closure Bf := by
  classical
  let v := hf.toLp f
  have hM : Mf = (convolutionSpace v : Set L1Circle) := by
    rw [hMf]
    ext u
    constructor
    · rintro ⟨g, hg, hu⟩
      have hi := memLp_one_iff_integrable.mp hg
      exact ⟨g, hi, Lp.ext (hu.trans (coe_integral_translate hf hi).symm)⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, memLp_one_iff_integrable.mpr hg, coe_integral_translate hf hg⟩
  have hB : Bf = (Submodule.span ℝ (Set.range (translate v)) : Set L1Circle) := by
    rw [hBf]
    ext u
    change _ ↔ u ∈ Submodule.span ℝ (Set.range (translate v))
    rw [mem_translate_span]
    constructor
    · rintro ⟨N, a, τ, hu⟩
      exact ⟨N, a, τ, Lp.ext (hu.trans (coe_sum_translate hf a τ).symm)⟩
    · rintro ⟨N, a, τ, rfl⟩
      exact ⟨N, a, τ, coe_sum_translate hf a τ⟩
  rw [hM, hB]
  apply le_antisymm <;> apply closure_minimal _ isClosed_closure
  · rintro _ ⟨g, hg, rfl⟩
    exact integral_mem_span_closure v hg
  · change Submodule.span ℝ (Set.range (translate v)) ≤ (convolutionSpace v).topologicalClosure
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact translate_mem_convolution_closure v t

end MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ComplexAnalysis/Runge.lean` (leanprover/lean-eval), problem `runge_theorem`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest `manifests/problems/runge_theorem.toml`,
rev 1, submitter Kim Morrison, status archived), for the statement of `runge`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The original evaluation problem was
converted to a Batteries wanted declaration in the `MathlibExt.Analysis.RungeWanted` namespace.
This module moves the statement and its docstring from `WantedExt/Analysis/RungeWanted.lean`
and supplies a proof.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Runge's theorem

`MathlibExt.Analysis.RungeWanted.ComplexAnalysis.runge` gives uniform rational approximation
on a compact set `K` for every function analytic on a neighborhood of `K`.

The proof takes the divided difference of the function with one variable in `K`.
Modulo the closed subspace of rational approximants, this gives an entire function of the
other variable. Outside `K` it can be computed using the resolvent of the coordinate function.
Liouville's theorem then puts the original function in the closed subspace.
-/

namespace MathlibExt.Analysis.RungeWanted.ComplexAnalysis

open Filter Set Polynomial
open scoped Topology Polynomial

variable {K U : Set ℂ} {f : ℂ → ℂ}

/-- Strict differentiability controls the divided difference near the diagonal. -/
private theorem continuousAt_dividedDifference {a b : ℂ} (ha : AnalyticAt ℂ f a)
    (hb : AnalyticAt ℂ f b) :
    ContinuousAt (fun p : ℂ × ℂ ↦ dslope f p.1 p.2) (a, b) := by
  by_cases h : b = a
  · subst b
    have hlim := (hasDerivAtFilter_iff_isLittleO.mp ha.hasStrictDerivAt).tendsto_div_nhds_zero
    have hoff := hlim.add (tendsto_const_nhds (x := deriv f a))
    have hon := ha.deriv.continuousAt.comp (continuous_fst.continuousAt (x := (a, a)))
    rw [ContinuousAt, dslope_same]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hon ε hε,
      Metric.tendsto_nhds.mp hoff ε hε] with p hp hq
    change dist (deriv f p.1) (deriv f a) < ε at hp
    change dist ((f p.1 - f p.2 - (p.1 - p.2) * deriv f a) / (p.1 - p.2) + deriv f a)
      (0 + deriv f a) < ε at hq
    by_cases he : p.2 = p.1
    · simpa only [he, dslope_same] using hp
    · rw [dslope_of_ne _ he, slope_def_field]
      rw [zero_add] at hq
      convert hq using 2
      field_simp
      ring
  · have h₁ := ha.continuousAt.comp (continuous_fst.continuousAt (x := (a, b)))
    have h₂ := hb.continuousAt.comp (continuous_snd.continuousAt (x := (a, b)))
    have hn : ∀ᶠ p : ℂ × ℂ in 𝓝 (a, b), p.2 ≠ p.1 :=
      (isOpen_ne_fun continuous_snd continuous_fst).mem_nhds h
    rw [ContinuousAt, dslope_of_ne _ h, slope_def_field]
    refine ((h₂.sub h₁).div (continuous_snd.continuousAt.sub continuous_fst.continuousAt)
      (sub_ne_zero.mpr h)).tendsto.congr' ?_
    filter_upwards [hn] with p hp
    simp [dslope_of_ne _ hp, slope_def_field]

/-- Divided differences restricted in the second variable to the compact set. -/
private noncomputable def dividedDifference (hKU : K ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (a : ℂ) : C(K, ℂ) :=
  ⟨fun z ↦ dslope f a z, ((hf.dslope a).continuousOn.mono hKU).domRestrict⟩

private theorem continuousOn_dividedDifference (hKU : K ⊆ U) (hf : AnalyticOnNhd ℂ f U) :
    ContinuousOn (dividedDifference hKU hf) U := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  intro ⟨a, z⟩ hz
  have hc : ContinuousAt (fun p : ℂ × K ↦ (p.1, (p.2 : ℂ))) (a, z) := by fun_prop
  exact ((continuousAt_dividedDifference (hf a hz.1) (hf z (hKU z.2))).comp
    (f := fun p : ℂ × K ↦ (p.1, (p.2 : ℂ))) hc).continuousWithinAt

/-- The difference quotient in the parameter is a second divided difference.
Continuity in the evaluation point gives the identity also at repeated nodes. -/
private theorem slope_dividedDifference (hKU : K ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    {a b : ℂ} (hba : b ≠ a) :
    slope (dividedDifference hKU hf) a b = dividedDifference hKU (hf.dslope a) b := by
  ext z
  let l := 𝓝[≠] (z : ℂ)
  have hc (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z) (c : ℂ) :
      Tendsto (dslope g c) l (𝓝 (dslope g c z)) :=
    (hg.dslope c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz := hf z (hKU z.2)
  apply tendsto_nhds_unique_of_eventuallyEq
    ((hc f hz b |>.sub (hc f hz a)).const_smul (b - a)⁻¹) (hc _ (hz.dslope a) b)
  filter_upwards [(eventually_cofinite_ne a).filter_mono (nhdsNE_le_cofinite (z : ℂ)),
    (eventually_cofinite_ne b).filter_mono (nhdsNE_le_cofinite (z : ℂ))] with x hxa hxb
  simp only [dslope_of_ne _ hxb, dslope_of_ne _ hxa,
    slope_def_field, dslope_of_ne _ hba, smul_eq_mul]
  field_simp
  ring

private theorem differentiableAt_dividedDifference [CompactSpace K] (hKU : K ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hU : IsOpen U) {a : ℂ} (ha : a ∈ U) :
    DifferentiableAt ℂ (dividedDifference hKU hf) a := by
  refine HasDerivAt.differentiableAt (f' := dividedDifference hKU (hf.dslope a) a) ?_
  rw [hasDerivAt_iff_tendsto_slope]
  apply ((continuousOn_dividedDifference hKU (hf.dslope a)).continuousAt
    (hU.mem_nhds ha)).tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (slope_dividedDifference hKU hf hb).symm

/-- Continuous functions represented on `K` by polynomial quotients whose denominators
are nowhere zero on `K`. -/
private def rationalFunctions (K : Set ℂ) : Submodule ℂ C(K, ℂ) where
  carrier := {g | ∃ p q : ℂ[X], (∀ z : K, q.eval (z : ℂ) ≠ 0) ∧
    ∀ z : K, g z = p.eval (z : ℂ) / q.eval (z : ℂ)}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  add_mem' := by
    rintro g h ⟨p, q, hq, hg⟩ ⟨r, s, hs, hh⟩
    refine ⟨p * s + q * r, q * s, fun z ↦ ?_, fun z ↦ ?_⟩
    · simpa using mul_ne_zero (hq z) (hs z)
    · simp [hg, hh, div_add_div _ _ (hq z) (hs z)]
  smul_mem' := by
    rintro c g ⟨p, q, hq, hg⟩
    exact ⟨C c * p, q, hq, fun z ↦ by simp [hg, mul_div_assoc]⟩

private def coord (K : Set ℂ) : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

private theorem mem_resolventSet_coord {a : ℂ} (ha : a ∉ K) :
    a ∈ resolventSet ℂ (coord K) :=
  (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr fun z ↦
    sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 ha).symm

private theorem resolvent_coord_apply {a : ℂ} (ha : a ∉ K) (z : K) :
    resolvent (coord K) a z = (a - z)⁻¹ := by
  have hu := spectrum.mem_resolventSet_iff.mp (mem_resolventSet_coord ha)
  simpa [resolvent, coord] using hu.map_ringInverse (ContinuousMap.evalAlgHom ℂ ℂ z)

/-- At a parameter outside the compact set, the Cauchy kernel is a rational function. -/
private theorem resolvent_mem_rationalFunctions {a : ℂ} (ha : a ∉ K) :
    resolvent (coord K) a ∈ rationalFunctions K := by
  refine ⟨1, C a - X, fun z ↦ ?_, fun z ↦ ?_⟩
  · simpa using sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 ha).symm
  · simp [resolvent_coord_apply ha, one_div]

/-- In the quotient by the uniform closure of rational functions, the term involving
`f a` in the divided difference vanishes for every `a ∉ K`. -/
private theorem restrict_mem_closure (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) :
    (⟨_, (hf.continuousOn.mono hKU).domRestrict⟩ : C(K, ℂ)) ∈
      (rationalFunctions K).topologicalClosure := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(K, ℂ) := ⟨_, (hf.continuousOn.mono hKU).domRestrict⟩
  let S := (rationalFunctions K).topologicalClosure
  have : IsClosed (S : Set C(K, ℂ)) := (rationalFunctions K).isClosed_topologicalClosure
  let L := S.mkQL
  let R := resolvent (coord K) (R := ℂ)
  let D := dividedDifference hKU hf
  have hR {a : ℂ} (ha : a ∉ K) : L (R a) = 0 :=
    (Submodule.Quotient.mk_eq_zero S).mpr
      (Submodule.le_topologicalClosure _ (resolvent_mem_rationalFunctions ha))
  have hout {a : ℂ} (ha : a ∉ K) : L (D a) = -L (F * R a) := by
    have h : D a = f a • R a - F * R a := by
      ext z
      change dslope f a z = f a * resolvent (coord K) a z - f z * resolvent (coord K) a z
      rw [dslope_of_ne _ (ne_of_mem_of_not_mem z.2 ha), slope_def_field, resolvent_coord_apply ha]
      rw [div_eq_mul_inv, ← neg_sub a (z : ℂ), inv_neg]
      ring
    simp [h, hR ha]
  have hd : Differentiable ℂ (fun a ↦ L (D a)) := by
    intro a
    by_cases ha : a ∈ U
    · exact L.differentiableAt.comp a (differentiableAt_dividedDifference hKU hf hU ha)
    · have haK : a ∉ K := fun h ↦ ha (hKU h)
      have hr := (spectrum.hasDerivAt_resolvent_const_left (mem_resolventSet_coord haK))
      have heq : (fun b ↦ L (D b)) =ᶠ[𝓝 a] fun b ↦ -L (F * R b) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds haK] with b hb using hout hb
      exact (L.differentiableAt.comp a (hr.differentiableAt.const_mul F)).neg.congr_of_eventuallyEq
        heq
  -- Multiply by the parameter. The resulting entire function is zero at the origin,
  -- while its limit at infinity extracts the class of the original function.
  have hlim : Tendsto (fun a ↦ a • L (D a)) (cocompact ℂ) (𝓝 (-L F)) := by
    have hr : Tendsto R (cocompact ℂ) (𝓝 0) := by
      simpa [Metric.cobounded_eq_cocompact] using spectrum.resolvent_tendsto_cobounded (coord K)
        (𝕜 := ℂ)
    have ht := (L.continuous.tendsto _).comp
      ((tendsto_const_nhds (x := F)).mul
        ((tendsto_const_nhds (x := (1 : C(K, ℂ)))).add (hr.const_mul (coord K))))
    apply (show Tendsto (fun a ↦ -L (F * (1 + coord K * R a))) (cocompact ℂ) (𝓝 (-L F)) by
      simpa using ht.neg).congr'
    filter_upwards [hK.compl_mem_cocompact] with a ha
    have hid : 1 + coord K * R a = a • R a := by
      ext z
      change 1 + (z : ℂ) * resolvent (coord K) a z = a * resolvent (coord K) a z
      rw [resolvent_coord_apply ha]
      field_simp [sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 ha).symm]
      ring
    simp [hout ha, hid]
  have hzero := (differentiable_id.smul hd).apply_eq_of_tendsto_cocompact 0 hlim
  exact (Submodule.Quotient.mk_eq_zero S).mp (show L F = 0 by simpa using hzero.symm)

/-- **Runge's theorem.** Let $K \subseteq \mathbb{C}$ be compact, let $U \subseteq \mathbb{C}$ be
open with $K \subseteq U$, and let $f : \mathbb{C} \to \mathbb{C}$ be analytic at every point of
$U$. Then for every real $\varepsilon > 0$ there are complex polynomials $p$ and $q$ such that
$q(z) \ne 0$ for every $z \in K$ and $|f(z) - p(z)/q(z)| < \varepsilon$ for every $z \in K$.

Source: C. Runge, *Zur Theorie der eindeutigen analytischen Funktionen*, Acta Math. 6 (1885),
229-244. Listed as §64 (additional statement 3) in O. Knill, *Some Fundamental Theorems in
Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `runge_theorem`. -/
public theorem runge (K : Set ℂ) (_hK : IsCompact K) (U : Set ℂ) (_hU : IsOpen U)
    (_hKU : K ⊆ U) (f : ℂ → ℂ) (_hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp _hK
  let F : C(K, ℂ) := ⟨_, (_hf.continuousOn.mono _hKU).domRestrict⟩
  have hF : F ∈ closure (rationalFunctions K : Set C(K, ℂ)) :=
    restrict_mem_closure _hK _hU _hKU _hf
  obtain ⟨g, ⟨p, q, hq, hg⟩, hdist⟩ := Metric.mem_closure_iff.mp hF ε _hε
  refine ⟨p, q, fun z hz ↦ hq ⟨z, hz⟩, fun z hz ↦ ?_⟩
  rw [← hg ⟨z, hz⟩, ← dist_eq_norm]
  exact (ContinuousMap.dist_apply_le_dist (f := F) (g := g) ⟨z, hz⟩).trans_lt hdist

end MathlibExt.Analysis.RungeWanted.ComplexAnalysis

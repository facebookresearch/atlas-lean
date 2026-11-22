/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of `exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected` below is
used under the following license.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_69.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_69 … := by sorry` into the Batteries `theorem_wanted`
`exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system. Further changes in this file: the
`theorem_wanted` is now a `theorem` with a proof, and `public import Mathlib` is replaced by
narrower imports; the statement itself is unchanged.
-/

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import MathlibExt.Analysis.Complex.RiemannMapping

/-!
# Harmonic functions on simply connected domains are real parts of holomorphic functions

If `Ω ⊆ ℂ` is open and simply connected and `u` is harmonic on `Ω`, then `u = Re f` on `Ω` for
some `f` holomorphic on `Ω`
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected`), and `f` is
unique up to an additive constant. The second statement, existence together with uniqueness, is
the MA-ProofBench problem `ma_proofbench_l2_69`; it is proved here as
`MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted`'s
`exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected`, the former `WantedExt`
entry.

For `Ω = ℂ` existence is Mathlib's `HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`. Otherwise a
Riemann map `φ : Ω → 𝔻` (MathlibExt's `riemannMapping_normalized`) has a holomorphic inverse
(`Complex.analyticAt_invFunOn`: by the open mapping theorem the inverse is continuous, by the
inverse function rule it is differentiable away from the critical points of `φ`, and these are
isolated, so the removable singularity theorem covers them). Then `u ∘ φ⁻¹` is harmonic on the
disc (`InnerProductSpace.HarmonicAt.comp_analyticAt`, since `u` is locally the real part of a
holomorphic function), Mathlib's disc case `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` gives
`G` with `Re G = u ∘ φ⁻¹`, and `f = G ∘ φ`. Uniqueness: the difference of two such functions is
holomorphic with real part `0` on the connected set `Ω`, so it is constant by the open mapping
theorem (`AnalyticOnNhd.eq_const_of_re_eq_const`).

Mathlib has the disc and plane cases, but not simply connected domains, nor the facts that the
inverse of an injective holomorphic map is holomorphic and that a harmonic function composed with
a holomorphic map is harmonic. Simple connectivity is Mathlib's topological `IsSimplyConnected`;
the textbook defines it for regions by connectedness of the complement in the extended plane,
which is equivalent for open subsets of `ℂ`, but that equivalence is not formalized here.

Rubric-guided revision of v1 ComplexVariables target 25 (`IsHarmonic.exists_holomorphic_re_eq` in
`v1/Atlas/ComplexVariables/code/Lecture16.lean` at commit
6191bf1ba03d204784385ef5be2472be88035b93). The archived proof glued local primitives through
the `sorry`-ed lemma `Complex.IsSimplyConnected.eq_of_hasDerivAt_eq_of_mem`, stated simple
connectivity with the project-local `Complex.IsSimplyConnected` instead of Mathlib's notion, and
needed `set_option backward.isDefEq.respectTransparency false` and an `aesop` step for a
function equality. This proof goes through the Riemann mapping theorem instead, uses Mathlib's
`IsSimplyConnected` and `HarmonicOnNhd`, and has none of these. The archived formalization and
its original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Function Metric Set InnerProductSpace
open scoped Topology

namespace Complex

variable {U : Set ℂ} {φ : ℂ → ℂ}

/-- A map injective on an open set `U` is not constant near any point of `U`. -/
private theorem not_eventually_eq_of_injOn (hU : IsOpen U) (hinj : InjOn φ U) {z : ℂ}
    (hz : z ∈ U) : ¬∀ᶠ y in 𝓝 z, φ y = φ z := by
  intro hc
  have h : ∀ᶠ y in 𝓝[≠] z, (φ y = φ z ∧ y ∈ U) ∧ y ∈ ({z}ᶜ : Set ℂ) :=
    ((hc.and (hU.mem_nhds hz)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨y, ⟨hyz, hyU⟩, hne⟩ := h.exists
  exact hne (hinj hyU hz hyz)

/-- The derivative of an injective holomorphic map has isolated zeros. -/
private theorem eventually_deriv_ne_zero_of_injOn (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ y in 𝓝[≠] z, deriv φ y ≠ 0 := by
  refine ((hφ.analyticAt (hU.mem_nhds hz)).deriv.eventually_eq_zero_or_eventually_ne_zero
    ).resolve_left fun h0 => not_eventually_eq_of_injOn hU hinj hz ?_
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz) h0)
  filter_upwards [ball_mem_nhds z hr] with y hy
  exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
    (hφ.mono fun w hw => (hsub hw).1) (fun w hw => (hsub hw).2) hy (mem_ball_self hr)

/-- The inverse `invFunOn φ U` of a holomorphic map `φ` injective on an open set `U` is
holomorphic at every point of `φ '' U`. -/
public theorem analyticAt_invFunOn (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hinj : InjOn φ U) {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ (invFunOn φ U) (φ z) := by
  set ψ := invFunOn φ U
  have hleft : ∀ y ∈ U, ψ (φ y) = y := fun y hy => hinj.leftInvOn_invFunOn hy
  -- Open mapping theorem: `φ` maps neighbourhoods of `y ∈ U` onto neighbourhoods of `φ y`.
  have hnhds : ∀ y ∈ U, 𝓝 (φ y) ≤ map φ (𝓝 y) := fun y hy =>
    ((hφ.analyticAt (hU.mem_nhds hy)).eventually_constant_or_nhds_le_map_nhds).resolve_left
      (not_eventually_eq_of_injOn hU hinj hy)
  have himage : ∀ y ∈ U, φ '' U ∈ 𝓝 (φ y) := fun y hy =>
    hnhds y hy (mem_map.2 (mem_of_superset (hU.mem_nhds hy) (subset_preimage_image φ U)))
  have hright : ∀ w ∈ φ '' U, φ (ψ w) = w := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hleft y hy]
  have htend : ∀ y ∈ U, Tendsto ψ (𝓝 (φ y)) (𝓝 y) := by
    intro y hy
    rw [tendsto_def]
    intro N hN
    refine hnhds y hy (mem_map.2 (mem_of_superset (inter_mem hN (hU.mem_nhds hy)) fun x hx => ?_))
    change ψ (φ x) ∈ N
    rw [hleft x hx.2]
    exact hx.1
  have hcont : ∀ y ∈ U, ContinuousAt ψ (φ y) := by
    intro y hy
    rw [ContinuousAt, hleft y hy]
    exact htend y hy
  -- Away from the critical points of `φ`, the inverse is differentiable.
  have hdiff : ∀ y ∈ U, deriv φ y ≠ 0 → DifferentiableAt ℂ ψ (φ y) := by
    intro y hy hy'
    have hd : HasDerivAt φ (deriv φ y) (ψ (φ y)) := by
      rw [hleft y hy]
      exact (hφ.differentiableAt (hU.mem_nhds hy)).hasDerivAt
    exact (hd.of_local_left_inverse (hcont y hy) hy'
      (eventually_of_mem (himage y hy) hright)).differentiableAt
  -- Critical points are isolated, so the removable singularity theorem applies.
  refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ (hcont z hz)
  have hne : ∀ᶠ w in 𝓝[≠] (φ z), ψ w ∈ ({z}ᶜ : Set ℂ) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (himage z hz), self_mem_nhdsWithin] with w hw hwz
    rintro (hψw : ψ w = z)
    exact hwz (show w = φ z by rw [← hψw, hright w hw])
  have hψ : Tendsto ψ (𝓝[≠] (φ z)) (𝓝[≠] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ψ
      ((htend z hz).mono_left nhdsWithin_le_nhds) hne
  filter_upwards [mem_nhdsWithin_of_mem_nhds (himage z hz),
    hψ.eventually (eventually_deriv_ne_zero_of_injOn hU hφ hinj hz),
    hψ.eventually (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz))] with w hw hw' hwU
  have h := hdiff (ψ w) hwU hw'
  rwa [hright w hw] at h

end Complex

/-- A harmonic function composed with a holomorphic map is harmonic. -/
public theorem InnerProductSpace.HarmonicAt.comp_analyticAt {u : ℂ → ℝ} {g : ℂ → ℂ} {w : ℂ}
    (hu : HarmonicAt u (g w)) (hg : AnalyticAt ℂ g w) : HarmonicAt (u ∘ g) w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt u) (g w) hu
  have hB : HarmonicOnNhd u (ball (g w) r) := fun y hy => hball hy
  obtain ⟨F, hF, hFu⟩ := hB.exists_analyticOnNhd_ball_re_eq
  have heq : u ∘ g =ᶠ[𝓝 w] fun y => (F (g y)).re := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds (ball_mem_nhds (g w) hr)] with y hy
    exact (hFu hy).symm
  exact (harmonicAt_congr_nhds heq).2 ((hF (g w) (mem_ball_self hr)).comp hg).harmonicAt_re

/-- **Harmonic functions on simply connected domains are real parts of holomorphic functions.**
If `Ω ⊆ ℂ` is open and simply connected and `u` is harmonic on `Ω`, then there is a function `f`
holomorphic on `Ω` with `u = Re f` on `Ω`.

The proof uses the Riemann mapping theorem: for `Ω ≠ ℂ`, transport `u` to the unit disc along the
inverse of a Riemann map, take a holomorphic function with real part `u` there, and pull it back;
for `Ω = ℂ` this is `HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`. -/
public theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected
    {u : ℂ → ℝ} {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩ : IsSimplyConnected Ω)
    (hu : HarmonicOnNhd u Ω) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ Ω.EqOn (fun z => (f z).re) u := by
  by_cases hΩu : Ω = univ
  · subst hΩu
    obtain ⟨F, hF, hFu⟩ := hu.exists_analyticOnNhd_univ_re_eq
    exact ⟨F, hF, fun z _ => congrFun hFu z⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.nonempty
  obtain ⟨φ, hφ, hbij, -⟩ :=
    MathlibExt.Analysis.Complex.RiemannMappingWanted.riemannMapping_normalized hΩo hΩ hΩu hz₀
  set ψ := invFunOn φ Ω
  have hleft : ∀ z ∈ Ω, ψ (φ z) = z := fun z hz => hbij.injOn.leftInvOn_invFunOn hz
  have hψ : ∀ w ∈ ball (0 : ℂ) 1, ψ w ∈ Ω ∧ AnalyticAt ℂ ψ w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
    exact ⟨by rw [hleft z hz]; exact hz, Complex.analyticAt_invFunOn hΩo hφ hbij.injOn hz⟩
  have hv : HarmonicOnNhd (u ∘ ψ) (ball 0 1) := fun w hw =>
    (hu _ (hψ w hw).1).comp_analyticAt (hψ w hw).2
  obtain ⟨G, hG, hGv⟩ := hv.exists_analyticOnNhd_ball_re_eq
  refine ⟨G ∘ φ, fun z hz => (hG _ (hbij.mapsTo hz)).comp (hφ.analyticAt (hΩo.mem_nhds hz)),
    fun z hz => ?_⟩
  exact (hGv (hbij.mapsTo hz)).trans (congrArg u (hleft z hz))

namespace MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted

/-- Let $\Omega \subset \mathbb{C}$ be a simply connected domain and $u$ a real-valued harmonic
function on $\Omega$. Prove that up to a constant, there exists a unique holomorphic function
$f$ on $\Omega$ such that $\operatorname{Re}(f)=u$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level2/ma_proofbench_l2_69.lean` at openbmb/ma-proofbench@31bab4c.

Proves `Wanted` entry `exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected`.
-/
public theorem exists_differentiableOn_re_eq_of_harmonicOnNhd_of_isSimplyConnected
  (Ω : Set ℂ)
  (u : ℂ → ℝ)
  (hΩ_open : IsOpen Ω)
  (hΩ : IsSimplyConnected Ω)
  (hu : InnerProductSpace.HarmonicOnNhd u Ω) :
  (∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ ∀ z : ℂ, z ∈ Ω → Complex.re (f z) = u z) ∧
    (∀ f g : ℂ → ℂ,
      DifferentiableOn ℂ f Ω →
      DifferentiableOn ℂ g Ω →
      (∀ z : ℂ, z ∈ Ω → Complex.re (f z) = u z) →
      (∀ z : ℂ, z ∈ Ω → Complex.re (g z) = u z) →
      ∃ c : ℂ, ∀ z : ℂ, z ∈ Ω → f z = g z + c) := by
  refine ⟨?_, fun f g hf hg hfu hgu => ?_⟩
  · obtain ⟨f, hf, hfu⟩ := hu.exists_analyticOnNhd_re_eq_of_isSimplyConnected hΩ_open hΩ
    exact ⟨f, hf.differentiableOn, fun z hz => hfu hz⟩
  -- `f - g` is holomorphic with real part `0`, so it is constant by the open mapping theorem.
  obtain ⟨c, hc⟩ := ((hf.sub hg).analyticOnNhd hΩ_open).eq_const_of_re_eq_const (c₀ := 0)
    (fun z hz => by simp [hfu z hz, hgu z hz]) hΩ_open hΩ.isPathConnected.isConnected
  exact ⟨c, fun z hz => sub_eq_iff_eq_add'.mp (hc z hz)⟩

end MathlibExt.Analysis.Complex.HarmonicConjugateSimplyConnectedWanted

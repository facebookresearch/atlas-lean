/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import MathlibExt.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Complex.Liouville
import MathlibExt.Analysis.Complex.DSlopeProd

/-!
# The general Cauchy theorem and integral formula (homology form)

Let `f` be holomorphic on an open set `Ω ⊆ ℂ`. A closed path `γ` in `Ω` is *homologous to zero*
in `Ω` (`Complex.IsHomologousToZero γ Ω`, written `γ ∼ 0`) if its winding number `n(γ, a)`
vanishes at every `a ∉ Ω`. Paths are piecewise `C¹` (`Path.IsPiecewiseC1`), `∫_γ φ(ζ) dζ` is
Mathlib's curve integral `∫ᶜ ζ in γ, φ ζ • ContinuousLinearMap.id ℂ ℂ`, and the winding number is
`Complex.windingNumber`.

Main results:
* `Complex.sum_curveIntegral_eq_zero`: Cauchy's theorem for cycles. If `∑ mᵢ γᵢ` is a finite
  integer combination of closed piecewise `C¹` paths in `Ω` with `∑ mᵢ n(γᵢ, a) = 0` for all
  `a ∉ Ω`, then `∑ mᵢ ∫_{γᵢ} f(z) dz = 0`.
* `Complex.isHomologousToZero_of_isPreconnected`: if the complement of `Ω` in the extended plane
  `OnePoint ℂ` is connected, every closed piecewise `C¹` path in `Ω` is homologous to zero.
* `Complex.curveIntegral_eq_zero_of_differentiableOn`: Cauchy's theorem, both parts: `∫_γ f = 0`
  for `γ ∼ 0`, and for every closed `γ` in `Ω` if `Ω` is simply connected.
* `Complex.windingNumber_mul_eq_two_pi_I_inv_mul_curveIntegral`: Cauchy's integral formula
  `n(γ, z) f(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ` for `γ ∼ 0` and `z` off `γ`.
* `Complex.exists_differentiable_of_isHomologousToZero` and
  `Complex.curveIntegral_dslope_eq_zero_and_cauchy_integral_formula`: Claims 2 and 3 of the
  proof of the integral formula. The function `h` given by `(2πi)⁻¹ ∫_γ g(z, ζ) dζ` on `Ω` and
  by `(2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ` on `Ω' = {z ∉ γ | n(γ, z) = 0}`, where
  `g(z, ζ) = dslope f z ζ`, is entire, and `h ≡ 0`, so the integral formula holds.

The proof is Dixon's. For a cycle homologous to zero, `H(w) = ∑ mᵢ ∫_{γᵢ} dslope f w ζ dζ` is
holomorphic on `Ω` (holomorphic dependence on a parameter, using the joint continuity of
`dslope f` from `MathlibExt.Analysis.Complex.DSlopeProd`). Off the cycle it equals
`∑ mᵢ ∫_{γᵢ} f(ζ) / (ζ - w) dζ - 2πi f(w) ∑ mᵢ n(γᵢ, w)`, and the total winding number is locally
constant and vanishes outside `Ω`, so `H` is holomorphic there too. `H` is therefore entire and
tends to `0` at infinity, so `H ≡ 0` by Liouville's theorem. Applied to `ζ ↦ (ζ - w) f(ζ)`, whose
divided difference at `w` is `f`, this gives Cauchy's theorem. The simply connected case holds
because `n(γ, ·)` is locally constant off `γ` and zero near `∞`.

Rubric-guided revision of v1 ComplexVariables targets 13, 15, 16, 20, 21
(`ClosedCurve.IsHomologousToZero`, `ClosedCurve.cauchy_theorem`,
`ClosedCurve.cauchy_integral_formula`, `cauchyPiecewise_differentiable`,
`ClosedCurve.contourIntegral_dslope_eq_zero` in `v1/Atlas/ComplexVariables/code/Lecture13.lean` at
commit 6191bf1ba03d204784385ef5be2472be88035b93). Archived defects fixed:
* curves were the project-local `ClosedCurve`, a single `C¹` parametrization with its own contour
  integral; they are now Mathlib paths that are piecewise `C¹`, integrated with `curveIntegral`;
* Cauchy's theorem omitted its simply connected clause; both parts are now one declaration;
* Claim 3 was stated only on `Ω`, through an unused hypothesis `z ∈ Ω`, and without the integral
  formula; it now states `h ≡ 0` on `Ω` and on `Ω'` together with the formula;
* Claim 2 was stated for an if-then-else function `cauchyPiecewise` whose agreement on `Ω ∩ Ω'`
  was derived from Claim 3; it now asserts `Ω ∪ Ω' = ℂ` and an entire function equal to both
  formulas, proved before and independently of Liouville's theorem;
* the integral formula took a redundant hypothesis `z ∈ Ω`; it now holds for every `z` off `γ`;
* the duplicated integrality proof, the public helper `h_vanishes`, three
  `maxHeartbeats 800000` options and the root-namespace helpers are gone, and Cauchy's theorem
  also covers cycles.

The archived formalization and its original license/provenance remain in `v1/` (the original
license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Function Set Topology
open scoped Real

namespace Complex

/-- A closed path `γ` is *homologous to zero* in `Ω` (`γ ∼ 0`) if it lies in `Ω` and its winding
number `n(γ, a)` vanishes at every point `a ∉ Ω`. Like the winding number, the predicate is
meaningful for piecewise `C¹` paths, the closed curves of the source, which every theorem below
assumes. -/
@[expose] public def IsHomologousToZero {x : ℂ} (γ : Path x x) (Ω : Set ℂ) : Prop :=
  range γ ⊆ Ω ∧ ∀ a ∉ Ω, windingNumber γ a = 0

/-! ### Dixon's argument for cycles -/

section Cycle

variable {ι : Type*} [Fintype ι] {x : ι → ℂ} {γ : ∀ i, Path (x i) (x i)} {m : ι → ℤ}
  {Ω : Set ℂ} {f : ℂ → ℂ}

/-- Claim 2 for cycles: `w ↦ ∑ mᵢ ∫_{γᵢ} dslope f w ζ dζ` is entire. -/
private theorem differentiable_sum_curveIntegral_dslope (hγ : ∀ i, (γ i).IsPiecewiseC1)
    (hΩ : IsOpen Ω) (hγΩ : ∀ i, range (γ i) ⊆ Ω)
    (hhom : ∀ a ∉ Ω, ∑ i, (m i : ℂ) * windingNumber (γ i) a = 0)
    (hf : DifferentiableOn ℂ f Ω) :
    Differentiable ℂ fun w =>
      ∑ i, (m i : ℂ) * ∫ᶜ ζ in γ i, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ := by
  have hK : IsCompact (⋃ i, range (γ i)) :=
    isCompact_iUnion fun i => isCompact_range (γ i).continuous
  intro w₀
  by_cases hw₀ : w₀ ∈ Ω
  · refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.const_mul ?_ _
    exact (differentiableOn_curveIntegral (hγ i) hΩ ((continuousOn_uncurry_dslope hΩ hf).mono
      (prod_mono subset_rfl (hγΩ i))) fun ζ hζ =>
        (dslope_continuousOn_differentiableOn_comm hΩ hf).2.2.1 ζ (hγΩ i hζ)).differentiableAt
      (hΩ.mem_nhds hw₀)
  -- Off `Ω`, the sum agrees near `w₀` with a combination of Cauchy-type integrals.
  have hw₀K : w₀ ∉ ⋃ i, range (γ i) := fun h => hw₀ (iUnion_subset hγΩ h)
  have hγw₀ : ∀ i, w₀ ∉ range (γ i) := fun i h => hw₀K (mem_iUnion_of_mem i h)
  have heq : ∀ᶠ w in 𝓝 w₀,
      (∑ i, (m i : ℂ) * ∫ᶜ ζ in γ i, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ) =
        ∑ i, (m i : ℂ) * ∫ᶜ ζ in γ i, (f ζ / (ζ - w)) • ContinuousLinearMap.id ℂ ℂ := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hw₀K,
      eventually_all.2 fun i => eventually_windingNumber_eq (hγ i) (hγw₀ i)] with w hw hn
    have hsplit : ∀ i, ∫ᶜ ζ in γ i, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ =
        (∫ᶜ ζ in γ i, (f ζ / (ζ - w)) • ContinuousLinearMap.id ℂ ℂ) -
          2 * π * I * windingNumber (γ i) w₀ * f w := fun i => by
      rw [curveIntegral_dslope_of_notMem (hγ i) (hf.continuousOn.mono (hγΩ i))
        fun h => hw (mem_iUnion_of_mem i h), hn i]
    have hzero : ∑ i, (m i : ℂ) * (2 * π * I * windingNumber (γ i) w₀ * f w) = 0 := by
      rw [← mul_zero (2 * π * I * f w), ← hhom w₀ hw₀, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hsplit, mul_sub, Finset.sum_sub_distrib, hzero, sub_zero]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.const_mul ?_ _
  exact (differentiableOn_curveIntegral_div_sub (hγ i)
    (hf.continuousOn.mono (hγΩ i))).differentiableAt
      ((isCompact_range (γ i).continuous).isClosed.isOpen_compl.mem_nhds (hγw₀ i))

/-- Claim 3 for cycles: `∑ mᵢ ∫_{γᵢ} dslope f w ζ dζ = 0` for every `w`, by Liouville's
theorem. -/
private theorem sum_curveIntegral_dslope_eq_zero (hγ : ∀ i, (γ i).IsPiecewiseC1)
    (hΩ : IsOpen Ω) (hγΩ : ∀ i, range (γ i) ⊆ Ω)
    (hhom : ∀ a ∉ Ω, ∑ i, (m i : ℂ) * windingNumber (γ i) a = 0)
    (hf : DifferentiableOn ℂ f Ω) (w : ℂ) :
    ∑ i, (m i : ℂ) * ∫ᶜ ζ in γ i, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ = 0 := by
  have hK : IsCompact (⋃ i, range (γ i)) :=
    isCompact_iUnion fun i => isCompact_range (γ i).continuous
  have hG : Tendsto (fun w =>
      ∑ i, (m i : ℂ) * ∫ᶜ ζ in γ i, (f ζ / (ζ - w)) • ContinuousLinearMap.id ℂ ℂ)
      (cocompact ℂ) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_curveIntegral_div_sub_cocompact (hγ i) (hf.continuousOn.mono (hγΩ i))).const_mul
        (m i : ℂ)
    simp only [mul_zero, Finset.sum_const_zero] at this
    exact this
  refine (differentiable_sum_curveIntegral_dslope hγ hΩ hγΩ hhom hf).apply_eq_of_tendsto_cocompact
    w (hG.congr' ?_)
  filter_upwards [hK.compl_mem_cocompact,
    eventually_all.2 fun i => eventually_windingNumber_eq_zero (hγ i)] with w hw hn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [curveIntegral_dslope_of_notMem (hγ i) (hf.continuousOn.mono (hγΩ i))
    fun h => hw (mem_iUnion_of_mem i h), hn i, mul_zero, zero_mul, sub_zero]

end Cycle

/-- **Cauchy's theorem for cycles.** Let `f` be holomorphic on an open set `Ω`, and let
`∑ mᵢ γᵢ` be a cycle in `Ω`: finitely many closed piecewise `C¹` paths `γᵢ` in `Ω` with integer
multiplicities `mᵢ`. If the cycle is homologous to zero in `Ω`, that is `∑ mᵢ n(γᵢ, a) = 0` for
every `a ∉ Ω`, then `∑ mᵢ ∫_{γᵢ} f(z) dz = 0`. -/
public theorem sum_curveIntegral_eq_zero {ι : Type*} [Fintype ι] {x : ι → ℂ}
    {γ : ∀ i, Path (x i) (x i)} (hγ : ∀ i, (γ i).IsPiecewiseC1) (m : ι → ℤ) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hγΩ : ∀ i, range (γ i) ⊆ Ω)
    (hhom : ∀ a ∉ Ω, ∑ i, (m i : ℂ) * windingNumber (γ i) a = 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) :
    ∑ i, (m i : ℂ) * ∫ᶜ z in γ i, f z • ContinuousLinearMap.id ℂ ℂ = 0 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp
  have hw : x i₀ ∈ Ω := hγΩ i₀ ⟨0, (γ i₀).source⟩
  have hfw : HasDerivAt f (deriv f (x i₀)) (x i₀) :=
    (hf.differentiableAt (hΩ.mem_nhds hw)).hasDerivAt
  -- The divided difference of `ζ ↦ (ζ - w) f ζ` at `w` is `f`.
  have hds : dslope (fun ζ => (ζ - x i₀) * f ζ) (x i₀) = f := by
    funext ζ
    rcases eq_or_ne ζ (x i₀) with rfl | hζ
    · rw [dslope_same]
      simpa using (((hasDerivAt_id (x i₀)).sub_const (x i₀)).fun_mul hfw).deriv
    · rw [dslope_of_ne _ hζ, slope_def_field, sub_self, zero_mul, sub_zero,
        mul_div_cancel_left₀ _ (sub_ne_zero.2 hζ)]
  have key := sum_curveIntegral_dslope_eq_zero hγ hΩ hγΩ hhom
    (f := fun ζ => (ζ - x i₀) * f ζ) ((differentiableOn_id.sub_const _).mul hf) (x i₀)
  rwa [hds] at key

/-- If the complement of `Ω` in the extended plane `OnePoint ℂ` is connected (`Ω` is simply
connected), then every closed piecewise `C¹` path in `Ω` is homologous to zero in `Ω`. -/
public theorem isHomologousToZero_of_isPreconnected {Ω : Set ℂ}
    (hΩc : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ) {x : ℂ} {γ : Path x x}
    (hγ : γ.IsPiecewiseC1) (hγΩ : range γ ⊆ Ω) : IsHomologousToZero γ Ω := by
  refine ⟨hγΩ, fun a ha => ?_⟩
  have hKo : IsOpen (range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  set U := {w | w ∉ range γ ∧ windingNumber γ w = 0}
  set V := {w | w ∉ range γ ∧ windingNumber γ w ≠ 0}
  have hUo : IsOpen U := isOpen_iff_mem_nhds.2 fun w hw => by
    filter_upwards [hKo.mem_nhds hw.1, eventually_windingNumber_eq hγ hw.1] with v hv hvw
    exact ⟨hv, hvw.trans hw.2⟩
  have hVo : IsOpen V := isOpen_iff_mem_nhds.2 fun w hw => by
    filter_upwards [hKo.mem_nhds hw.1, eventually_windingNumber_eq hγ hw.1] with v hv hvw
    exact ⟨hv, fun h => hw.2 (hvw.symm.trans h)⟩
  -- `U` contains a neighbourhood of infinity, so `∞` together with `U` is open in `OnePoint ℂ`.
  have hU : U ∈ cocompact ℂ := by
    filter_upwards [(isCompact_range γ.continuous).compl_mem_cocompact,
      eventually_windingNumber_eq_zero hγ] with w h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨K, hK, hKU⟩ := mem_cocompact.1 hU
  have hUc : IsCompact Uᶜ := hK.of_isClosed_subset hUo.isClosed_compl (compl_subset_comm.1 hKU)
  have hO : IsOpen (((↑) : ℂ → OnePoint ℂ) '' Uᶜ)ᶜ :=
    OnePoint.isOpen_compl_image_coe.2 ⟨hUo.isClosed_compl, hUc⟩
  have hO' : IsOpen (((↑) : ℂ → OnePoint ℂ) '' V) := OnePoint.isOpen_image_coe.2 hVo
  have hdisj : Disjoint (((↑) : ℂ → OnePoint ℂ) '' Uᶜ)ᶜ (((↑) : ℂ → OnePoint ℂ) '' V) := by
    rw [Set.disjoint_left]
    rintro _ hpO ⟨v, hv, rfl⟩
    exact hpO ⟨v, fun hvU => hv.2 hvU.2, rfl⟩
  have hcover : (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ ⊆
      (((↑) : ℂ → OnePoint ℂ) '' Uᶜ)ᶜ ∪ ((↑) : ℂ → OnePoint ℂ) '' V := by
    intro p hp
    by_cases hpO : p ∈ (((↑) : ℂ → OnePoint ℂ) '' Uᶜ)ᶜ
    · exact Or.inl hpO
    · right
      obtain ⟨v, hvU, rfl⟩ := not_not.1 hpO
      have hvK : v ∉ range γ := fun hv => hp ⟨v, hγΩ hv, rfl⟩
      exact ⟨v, ⟨hvK, fun h0 => hvU ⟨hvK, h0⟩⟩, rfl⟩
  have hinf : ((((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ ∩ (((↑) : ℂ → OnePoint ℂ) '' Uᶜ)ᶜ).Nonempty :=
    ⟨OnePoint.infty, OnePoint.infty_notMem_image_coe, OnePoint.infty_notMem_image_coe⟩
  have hsub := hΩc.subset_left_of_subset_union hO hO' hdisj hcover hinf
  have ha' : (a : OnePoint ℂ) ∈ (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ := by
    rintro ⟨b, hb, hba⟩
    exact ha (OnePoint.coe_injective hba ▸ hb)
  by_contra hne
  exact hsub ha' ⟨a, fun haU => hne haU.2, rfl⟩

/-! ### A single closed path -/

section ClosedPath

variable {Ω : Set ℂ} {f : ℂ → ℂ} {x : ℂ} {γ : Path x x}

private theorem differentiable_curveIntegral_dslope (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : γ.IsPiecewiseC1) (hγΩ : IsHomologousToZero γ Ω) :
    Differentiable ℂ fun w => ∫ᶜ ζ in γ, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ := by
  simpa using differentiable_sum_curveIntegral_dslope (ι := Unit) (γ := fun _ => γ)
    (m := fun _ => 1) (fun _ => hγ) hΩ (fun _ => hγΩ.1) (by simpa using hγΩ.2) hf

private theorem curveIntegral_dslope_eq_zero (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    (hγ : γ.IsPiecewiseC1) (hγΩ : IsHomologousToZero γ Ω) (w : ℂ) :
    ∫ᶜ ζ in γ, dslope f w ζ • ContinuousLinearMap.id ℂ ℂ = 0 := by
  simpa using sum_curveIntegral_dslope_eq_zero (ι := Unit) (γ := fun _ => γ) (m := fun _ => 1)
    (fun _ => hγ) hΩ (fun _ => hγΩ.1) (by simpa using hγΩ.2) hf w

/-- **Cauchy's theorem** (homology form). Let `f` be holomorphic on an open set `Ω ⊆ ℂ`. Then:
* `∫_γ f(z) dz = 0` for every closed piecewise `C¹` path `γ` that is homologous to zero in `Ω`
  (it lies in `Ω` and `n(γ, a) = 0` for every `a ∉ Ω`);
* in particular, if `Ω` is simply connected, in the sense that its complement in the extended
  plane `OnePoint ℂ` is connected, then `∫_γ f(z) dz = 0` for every closed piecewise `C¹` path
  `γ` in `Ω`.

The source states the second part for regions; it holds without assuming `Ω` connected. -/
public theorem curveIntegral_eq_zero_of_differentiableOn (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    (∀ {x : ℂ} (γ : Path x x), γ.IsPiecewiseC1 → IsHomologousToZero γ Ω →
        ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ = 0) ∧
      (IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ → ∀ {x : ℂ} (γ : Path x x),
        γ.IsPiecewiseC1 → range γ ⊆ Ω → ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ = 0) := by
  have h1 : ∀ {x : ℂ} (γ : Path x x), γ.IsPiecewiseC1 → IsHomologousToZero γ Ω →
      ∫ᶜ z in γ, f z • ContinuousLinearMap.id ℂ ℂ = 0 := by
    intro x γ hγ hγΩ
    simpa using sum_curveIntegral_eq_zero (ι := Unit) (γ := fun _ => γ) (fun _ => hγ)
      (fun _ => 1) hΩ (fun _ => hγΩ.1) (by simpa using hγΩ.2) hf
  refine ⟨h1, fun hc => ?_⟩
  intro x γ hγ hγΩ
  exact h1 γ hγ (isHomologousToZero_of_isPreconnected hc.isPreconnected hγ hγΩ)

/-- **Cauchy's integral formula** (homology form). Let `f` be holomorphic on an open set `Ω` and
let `γ` be a closed piecewise `C¹` path homologous to zero in `Ω`. Then
`n(γ, z) f(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ` for every `z` off `γ`.

The source states the formula for `z ∈ Ω`; for `z ∉ Ω` both sides vanish. -/
public theorem windingNumber_mul_eq_two_pi_I_inv_mul_curveIntegral (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : γ.IsPiecewiseC1) (hγΩ : IsHomologousToZero γ Ω) {z : ℂ}
    (hz : z ∉ range γ) :
    windingNumber γ z * f z =
      (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ := by
  have h := curveIntegral_dslope_of_notMem hγ (hf.continuousOn.mono hγΩ.1) hz
  rw [curveIntegral_dslope_eq_zero hΩ hf hγ hγΩ z, eq_comm, sub_eq_zero] at h
  rw [h, mul_assoc (2 * π * I), inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- **Claim 2 in the proof of Cauchy's integral formula: `h` is holomorphic.** Let `f` be
holomorphic on an open set `Ω`, let `γ` be a closed piecewise `C¹` path homologous to zero in `Ω`,
let `g(z, ζ) = dslope f z ζ` (that is `(f ζ - f z) / (ζ - z)` for `ζ ≠ z` and `f' z` for
`ζ = z`), and let `Ω' = {z ∉ γ | n(γ, z) = 0}`. Then `Ω ∪ Ω' = ℂ`, and there is an entire function
`h` with `h(z) = (2πi)⁻¹ ∫_γ g(z, ζ) dζ` for `z ∈ Ω` and `h(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ`
for `z ∈ Ω'`. Since `Ω ∪ Ω' = ℂ`, these two conditions determine `h`. -/
public theorem exists_differentiable_of_isHomologousToZero (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : γ.IsPiecewiseC1) (hγΩ : IsHomologousToZero γ Ω) :
    Ω ∪ {z | z ∉ range γ ∧ windingNumber γ z = 0} = univ ∧
      ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
        (∀ z ∈ Ω, h z = (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, dslope f z ζ • ContinuousLinearMap.id ℂ ℂ) ∧
        ∀ z ∉ range γ, windingNumber γ z = 0 →
          h z = (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ := by
  refine ⟨eq_univ_of_forall fun z => ?_,
    fun z => (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, dslope f z ζ • ContinuousLinearMap.id ℂ ℂ,
    (differentiable_curveIntegral_dslope hΩ hf hγ hγΩ).const_mul _, fun z _ => rfl,
    fun z hz hn => ?_⟩
  · by_cases hzΩ : z ∈ Ω
    · exact Or.inl hzΩ
    · exact Or.inr ⟨fun h => hzΩ (hγΩ.1 h), hγΩ.2 z hzΩ⟩
  · change (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, dslope f z ζ • ContinuousLinearMap.id ℂ ℂ = _
    rw [curveIntegral_dslope_of_notMem hγ (hf.continuousOn.mono hγΩ.1) hz, hn, mul_zero, zero_mul,
      sub_zero]

/-- **Claim 3 in the proof of Cauchy's integral formula: `h ≡ 0`, so the formula holds.** Let `f`
be holomorphic on an open set `Ω`, let `γ` be a closed piecewise `C¹` path homologous to zero in
`Ω`, and let `g(z, ζ) = dslope f z ζ`. The function `h` of Claim 2 vanishes on both parts of its
domain `ℂ = Ω ∪ Ω'`:
1. `h(z) = (2πi)⁻¹ ∫_γ g(z, ζ) dζ = 0` for `z ∈ Ω`;
2. `h(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ = 0` for `z ∈ Ω'`, the points off `γ` with
   `n(γ, z) = 0`;

and consequently

3. the Cauchy integral formula `n(γ, z) f(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ` holds for every `z`
   off `γ`. -/
public theorem curveIntegral_dslope_eq_zero_and_cauchy_integral_formula (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : γ.IsPiecewiseC1) (hγΩ : IsHomologousToZero γ Ω) :
    (∀ z ∈ Ω, (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, dslope f z ζ • ContinuousLinearMap.id ℂ ℂ = 0) ∧
      (∀ z ∉ range γ, windingNumber γ z = 0 →
        (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ = 0) ∧
      ∀ z ∉ range γ, windingNumber γ z * f z =
        (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ := by
  have hcif : ∀ z ∉ range γ, windingNumber γ z * f z =
      (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ := fun z hz =>
    windingNumber_mul_eq_two_pi_I_inv_mul_curveIntegral hΩ hf hγ hγΩ hz
  refine ⟨fun z _ => ?_, fun z hz hn => ?_, hcif⟩
  · rw [curveIntegral_dslope_eq_zero hΩ hf hγ hγΩ z, mul_zero]
  · rw [← hcif z hz, hn, zero_mul]

end ClosedPath

end Complex

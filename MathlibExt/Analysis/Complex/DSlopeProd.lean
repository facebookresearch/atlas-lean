/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Divided differences of a holomorphic function

For `f` holomorphic on an open set `Ω`, the divided difference `g z ζ = dslope f z ζ`, equal to
`(f ζ - f z) / (ζ - z)` off the diagonal and to `f′ z` on it, is continuous on `Ω × Ω`, holomorphic
on `Ω` in each variable separately, and symmetric
(`Complex.dslope_continuousOn_differentiableOn_comm`, Claim 1 in the proof of the general Cauchy
integral formula). Supporting results: `dslope_comm` (symmetry for any `f : 𝕜 → E`) and
`Complex.continuousOn_uncurry_dslope` (joint continuity).

Mathlib has continuity and holomorphy of `dslope f c` in the second variable for fixed `c`
(`continuousOn_dslope`, `Complex.differentiableOn_dslope`), but not joint continuity or symmetry.
On the diagonal the joint continuity comes from strict differentiability of the analytic `f`.

Rubric-guided revision of v1 ComplexVariables target 17 (`continuousOn_dividedDiff` in
`v1/Atlas/ComplexVariables/code/Lecture13.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 225–320). The archived declaration stated only
continuity, with symmetry and holomorphy in each variable in separate lemmas, on its own
`dividedDiff` wrapper; the three conclusions are now one declaration on `dslope`. The archived
formalization and its original license/provenance remain in `v1/` (the original license text is
`v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Function Set Topology

/-- `dslope` is symmetric in its two points, as `slope` is (`slope_comm`). -/
public theorem dslope_comm {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) : dslope f a b = dslope f b a := by
  rcases eq_or_ne b a with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

namespace Complex

/-- The divided difference `(z, ζ) ↦ dslope f z ζ` of a function holomorphic on an open set `Ω`
is jointly continuous on `Ω × Ω`. -/
public theorem continuousOn_uncurry_dslope {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) : ContinuousOn (uncurry (dslope f)) (Ω ×ˢ Ω) := by
  rw [(hΩ.prod hΩ).continuousOn_iff]
  rintro ⟨z₀, ζ₀⟩ ⟨hz₀, hζ₀⟩
  rcases eq_or_ne z₀ ζ₀ with rfl | hne
  · -- Near `(z₀, z₀)`, treat the diagonal and its complement separately.
    rw [← continuousWithinAt_univ, ← union_compl_self {p : ℂ × ℂ | p.1 = p.2},
      continuousWithinAt_union]
    constructor
    · -- On the diagonal `dslope f z z = deriv f z`, and `deriv f` is continuous on `Ω`.
      have hd : ContinuousAt (fun p : ℂ × ℂ => deriv f p.1) (z₀, z₀) :=
        ((hf.deriv hΩ).continuousOn.continuousAt (hΩ.mem_nhds hz₀)).comp continuousAt_fst
      refine hd.continuousWithinAt.congr ?_ (dslope_same f z₀)
      rintro ⟨z, ζ⟩ (rfl : z = ζ)
      exact dslope_same f _
    · -- Off the diagonal, the difference quotient tends to `deriv f z₀` because `f` is analytic
      -- at `z₀`, hence strictly differentiable there.
      have hs := hasDerivAtFilter_iff_tendsto.mp
        (hf.analyticAt (hΩ.mem_nhds hz₀)).hasStrictDerivAt
      rw [ContinuousWithinAt, uncurry_apply_pair, dslope_same, tendsto_iff_norm_sub_tendsto_zero]
      refine (hs.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin]
      rintro ⟨z, ζ⟩ (hp : z ≠ ζ)
      have h₁ : z - ζ ≠ 0 := sub_ne_zero.mpr hp
      have h₂ : ζ - z ≠ 0 := sub_ne_zero.mpr hp.symm
      simp only [uncurry_apply_pair, dslope_of_ne f hp.symm, slope_def_field, smul_eq_mul]
      rw [← norm_inv, ← norm_mul]
      congr 1
      field_simp
      ring
  · -- Off the diagonal, `dslope f` agrees near `(z₀, ζ₀)` with the difference quotient, which is
    -- continuous there because `f` is.
    have hc : ∀ w ∈ Ω, ContinuousAt f w := fun w hw =>
      hf.continuousOn.continuousAt (hΩ.mem_nhds hw)
    have hq : ContinuousAt (fun p : ℂ × ℂ => (f p.2 - f p.1) / (p.2 - p.1)) (z₀, ζ₀) :=
      (((hc ζ₀ hζ₀).comp continuousAt_snd).sub ((hc z₀ hz₀).comp continuousAt_fst)).div
        (continuousAt_snd.sub continuousAt_fst) (sub_ne_zero.mpr hne.symm)
    refine hq.congr ?_
    filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds
      (show (z₀, ζ₀) ∈ {p : ℂ × ℂ | p.1 ≠ p.2} from hne)]
    rintro ⟨z, ζ⟩ (hp : z ≠ ζ)
    simp only [uncurry_apply_pair, dslope_of_ne f hp.symm, slope_def_field]

/-- **Divided differences of a holomorphic function.** Let `f` be holomorphic on an open set
`Ω ⊆ ℂ` and let `g z ζ = (f ζ - f z) / (ζ - z)` for `z ≠ ζ` and `g z z = f' z`; this `g` is
Mathlib's `dslope f`. Then `g` is continuous on `Ω × Ω`, holomorphic on `Ω` in each variable
separately, and symmetric: `g z ζ = g ζ z`. -/
public theorem dslope_continuousOn_differentiableOn_comm {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (uncurry (dslope f)) (Ω ×ˢ Ω) ∧
      (∀ z ∈ Ω, DifferentiableOn ℂ (fun ζ => dslope f z ζ) Ω) ∧
      (∀ ζ ∈ Ω, DifferentiableOn ℂ (fun z => dslope f z ζ) Ω) ∧
      ∀ z ∈ Ω, ∀ ζ ∈ Ω, dslope f z ζ = dslope f ζ z :=
  ⟨continuousOn_uncurry_dslope hΩ hf,
    fun _ hz => (differentiableOn_dslope (hΩ.mem_nhds hz)).mpr hf,
    fun ζ hζ => ((differentiableOn_dslope (hΩ.mem_nhds hζ)).mpr hf).congr
      fun z _ => dslope_comm f z ζ,
    fun z _ ζ _ => dslope_comm f z ζ⟩

end Complex

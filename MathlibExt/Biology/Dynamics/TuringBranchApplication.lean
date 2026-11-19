/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.TuringBranches
public import MathlibExt.Biology.Dynamics.TuringBranchesPDE
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Turing pattern branches from the Lyapunov–Schmidt reduction

`MathlibExt.Biology.Dynamics.TuringBranchesPDE` reduces the steady-state map `F(w, d)` of the
two-species Turing system near the homogeneous state to a scalar bifurcation function
`G̃(a, d) = ψ(F(a φ + W(a φ, d), d))` (`lsScalar`) along a fixed kernel vector `φ` and a fixed
functional `ψ` cutting out the range, and turns a factorization `G̃(a, d) = a G(a, d)` with
`G(0, d₀) = 0` and `∂_d G(0, d₀) ≠ 0` into a pattern branch (`lyapunovSchmidt_patternBranch`).
`MathlibExt.Biology.Dynamics.TuringBranches` shows that the critical eigenvalue of the selected
mode crosses zero with positive speed (`leadingEigenvalue_crossing`). This file connects the two:
it computes `G(0, d₀)` and `∂_d G(0, d₀)` from the reduction itself.

A reduction along a fixed kernel vector does not make `G(0, d)` equal to the critical eigenvalue
(the two differ at second order in `d - d₀`); it reproduces the eigenvalue to first order:

* `lsScalar_factor_normalization`: if the linearization of `F` along the trivial branch is
  `L + (d - d₀) L₁` (`L = ∂ₓF(0, d₀)`), then every factor `G` of the scalar bifurcation function
  has `G(0, d₀) = 0` and `∂_d G(0, d₀) = ψ(L₁ φ)`. The hypotheses are about `F` and the
  factorization only; `G(0, d)` for `d ≠ d₀` is never assumed.
* For the Turing linearization `D(d) ∂ₓₓ + J` on Neumann modes, `L₁ = diag(0, 1) ∂ₓₓ`
  (`modeOperator_eq_add_smul`), and with the critical functional normalized by `ψ(φ) = 1`
  (`normalizedCriticalFunctional`), `ψ(L₁ φ) = (d_u k⁴ - f_u k²) / tr (J - k² D(d₀))`, the
  crossing speed of the critical eigenvalue.

## Source receipt

* **Lyapunov–Schmidt reduction and pattern branch**: H. Kielhöfer, *Bifurcation Theory: An
  Introduction with Applications to Partial Differential Equations*, 2nd ed., Springer (2012),
  §I.2; M. G. Crandall and P. H. Rabinowitz, *Bifurcation from simple eigenvalues*, J. Funct.
  Anal. 8 (1971) 321–340, Theorem 1.7. Reused, not reproved: `lyapunovSchmidt_patternBranch`
  (with `hCR := exists_patternBranch`) and the kernel and range of the mode linearization,
  `modeOperator_simpleKernel`.
* **Transversality in reduced form**: the coefficient `∂_d G(0, d₀)` of the reduced equation is
  `ψ(∂²_{x d} F(0, d₀) φ)`, the quantity in the transversality condition of Crandall–Rabinowitz
  (1971), Theorem 1.7; with `ψ(φ) = 1` it is the derivative of the perturbed simple eigenvalue,
  M. G. Crandall and P. H. Rabinowitz, *Bifurcation, perturbation of simple eigenvalues, and
  linearized stability*, Arch. Rational Mech. Anal. 52 (1973) 161–180. Proved here:
  `lsScalar_factor_normalization`, and the Turing computation of `ψ(L₁ φ)`.
* **Critical eigenvalue**: A. M. Turing, *The chemical basis of morphogenesis*, Phil. Trans. R.
  Soc. Lond. B 237 (1952) 37–72; J. D. Murray, *Mathematical Biology II*, 3rd ed., Springer
  (2003), ch. 2. Reused: `leadingEigenvalue_crossing`.

## Main results

* `lsScalar_factor_normalization`: `G(0, d₀) = 0` and `∂_d G(0, d₀) = ψ(L₁ φ)` for every factor
  `G` of the scalar bifurcation function.
* `turing_patternBranch_of_reduction`: for a map `F` on Neumann-mode coefficients whose
  linearization along the trivial branch is the Turing linearization at every `d` near the
  neutral diffusion `d₀` of a critical, non-resonant mode `k` with `f_v ≠ 0`, and a factor `G` of
  the scalar bifurcation function for the normalized critical functional:
  `∂_d G(0, d₀)` is the crossing speed of the critical eigenvalue (so it is positive), `G(0, d)`
  has the sign of the critical eigenvalue near `d₀` (negative before `d₀`, positive after), and
  `F` has a pattern branch through `(0, d₀)` whose states are nonzero steady states.

## Scope

As in `TuringBranchesPDE`, no nonlinear Turing map `F` is constructed, the state space is a
finite set of Neumann modes, and the factorization `G̃ = a G` (which uses `C²` regularity of `F`)
is a hypothesis. As in `turing_patternBranch`, only the selected mode is controlled, so nothing
is claimed about the stability of the homogeneous state or of the branch.
-/

@[expose] public section

open Filter Topology Asymptotics
open ContinuousLinearMap (FredholmPackage)

namespace MathlibExt.Biology.Dynamics.TuringBranchApplication

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches
  MathlibExt.Biology.Dynamics.TuringBranchesPDE

/-! ### The trivial-branch coefficient of the reduced map -/

section Normalization

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {L : E →L[ℝ] Y} (pkg : FredholmPackage L)
  {F : E × ℝ → Y} {F' : E × ℝ →L[ℝ] Y} {d₀ : ℝ}

/-- The correction `W(a φ, d)` of the reduction is `o(a)` as `(a, d) → (0, d₀)`, uniformly in `d`:
it vanishes on the trivial branch and has zero derivative in the kernel direction. -/
private theorem isLittleO_lsSolution (hF : HasStrictFDerivAt F F' ((0 : E), d₀))
    (hFL : F' ∘L .inl ℝ E ℝ = L) (htriv : ∀ᶠ d in 𝓝 d₀, F ((0 : E), d) = 0)
    {φ : E} (hφ : φ ∈ pkg.decDom.X₀) :
    (fun q : ℝ × ℝ => (lsSolution pkg hF hFL (q.1 • ⟨φ, hφ⟩, q.2) : E)) =o[𝓝 ((0 : ℝ), d₀)]
      fun q => q.1 := by
  obtain ⟨W', hW', hW'0⟩ := exists_hasStrictFDerivAt_lsSolution pkg hF hFL
  set φ' : pkg.decDom.X₀ := ⟨φ, hφ⟩ with hφ'
  have ht : Tendsto (fun q : ℝ × ℝ => ((q.1 • φ', q.2), ((0 : pkg.decDom.X₀), q.2)))
      (𝓝 ((0 : ℝ), d₀)) (𝓝 (((0 : pkg.decDom.X₀), d₀), ((0 : pkg.decDom.X₀), d₀))) := by
    have hc : Continuous fun q : ℝ × ℝ => ((q.1 • φ', q.2), ((0 : pkg.decDom.X₀), q.2)) := by
      fun_prop
    simpa using hc.tendsto ((0 : ℝ), d₀)
  have hW0 : ∀ᶠ q : ℝ × ℝ in 𝓝 ((0 : ℝ), d₀),
      lsSolution pkg hF hFL ((0 : pkg.decDom.X₀), q.2) = 0 :=
    (continuous_snd.tendsto ((0 : ℝ), d₀)).eventually
      ((eventually_lsSolution_zero pkg hF hFL htriv).mono fun _ h => h.1)
  have h1 : (fun q : ℝ × ℝ => lsSolution pkg hF hFL (q.1 • φ', q.2)) =o[𝓝 ((0 : ℝ), d₀)]
      fun q => ((q.1 • φ', q.2) - ((0 : pkg.decDom.X₀), q.2) : pkg.decDom.X₀ × ℝ) := by
    refine (hW'.isLittleO.comp_tendsto ht).congr' ?_ EventuallyEq.rfl
    filter_upwards [hW0] with q hq
    have h' : W' ((q.1 • φ', q.2) - ((0 : pkg.decDom.X₀), q.2)) = 0 := by
      rw [Prod.mk_sub_mk, sub_zero, sub_self]
      exact DFunLike.congr_fun hW'0 (q.1 • φ')
    simp only [Function.comp_apply, hq, h', sub_zero]
  have h2 : (fun q : ℝ × ℝ => ((q.1 • φ', q.2) - ((0 : pkg.decDom.X₀), q.2) :
      pkg.decDom.X₀ × ℝ)) =O[𝓝 ((0 : ℝ), d₀)] fun q => q.1 :=
    IsBigO.of_bound ‖φ‖ (Eventually.of_forall fun q => by
      simp only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_def, norm_zero, norm_smul]
      rw [max_eq_left (by positivity), hφ', mul_comm]
      rfl)
  exact (pkg.decDom.X₁.subtypeL.isBigO_comp _ _).trans_isLittleO (h1.trans_isBigO h2)

/-- On a slice `d = const`, a factor `G` of the scalar bifurcation function satisfies
`G(a, d) - (d - d₀) (ψ(L₁ φ) + ψ(L₁ W(a φ, d)) / a) → 0` as `a → 0`. -/
private theorem tendsto_factor_slice (hF : HasStrictFDerivAt F F' ((0 : E), d₀))
    (hFL : F' ∘L .inl ℝ E ℝ = L) {φ : E} (hφ : φ ∈ pkg.decDom.X₀) (ψ : Y →L[ℝ] ℝ)
    (hψL : ∀ x, ψ (L x) = 0) {L₁ : E →L[ℝ] Y} {d : ℝ}
    (hlin : HasFDerivAt (fun x => F (x, d)) (L + (d - d₀) • L₁) 0) (h0 : F ((0 : E), d) = 0)
    (hu : ∀ᶠ a in 𝓝 (0 : ℝ), ‖(lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d) : E)‖ ≤ ‖a‖)
    {G : ℝ × ℝ → ℝ}
    (hfac : ∀ᶠ a in 𝓝 (0 : ℝ), lsScalar pkg hφ ψ hF hFL (a, d) = a * G (a, d)) :
    Tendsto (fun a => G (a, d) - (d - d₀) *
      (ψ (L₁ φ) + ψ (L₁ (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d))) / a)) (𝓝[≠] 0) (𝓝 0) := by
  set u : ℝ → E := fun a => (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d) : E) with hu_def
  have huO : u =O[𝓝 0] fun a => a :=
    IsBigO.of_bound 1 (hu.mono fun a ha => by rw [one_mul]; exact ha)
  have hxO : (fun a : ℝ => a • φ + u a) =O[𝓝 0] fun a => a :=
    (IsBigO.of_bound ‖φ‖ (Eventually.of_forall fun a => by rw [norm_smul, mul_comm])).add huO
  have hx : Tendsto (fun a : ℝ => a • φ + u a) (𝓝 0) (𝓝 0) := hxO.trans_tendsto tendsto_id
  have h1 := (ψ.isBigO_comp _ _).trans_isLittleO
    ((hlin.isLittleO.comp_tendsto hx).trans_isBigO (hxO.congr_left fun a => (sub_zero _).symm))
  have h2 : (fun a : ℝ => lsScalar pkg hφ ψ hF hFL (a, d) -
      (d - d₀) * (a * ψ (L₁ φ) + ψ (L₁ (u a)))) =o[𝓝 0] fun a => a := by
    refine h1.congr_left fun a => ?_
    simp only [Function.comp_apply, h0, sub_zero, add_apply, smul_apply, map_sub, map_add,
      map_smul, hψL, smul_eq_mul, mul_zero, zero_add]
    rfl
  refine (h2.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha ha0
  rw [ha]
  have ha0' : a ≠ 0 := ha0
  field_simp
  ring

/-- **The trivial-branch coefficient of the reduced map.** In the setting of
`lyapunovSchmidt_patternBranch` (trivial branch, `φ ∈ ker L`, `ψ` vanishing on `range L`), assume
that along the trivial branch the linearization of `F` is affine in `d` with slope `L₁`:
`∂ₓF(0, d) = L + (d - d₀) L₁` for `d` near `d₀`. Then every factor `G` of the scalar bifurcation
function, `G̃(a, d) = a G(a, d)` near `(0, d₀)` with `G` strictly differentiable at `(0, d₀)`,
satisfies `G(0, d₀) = 0` and `∂_d G(0, d₀) = ψ(L₁ φ)`: these are the hypotheses `hG0` and (when
`ψ(L₁ φ) ≠ 0`) `htrans` of `lyapunovSchmidt_patternBranch`, now derived. Nothing is assumed
about `G(0, d)` for `d ≠ d₀`; `G` need not be continuous away from `(0, d₀)`. -/
theorem lsScalar_factor_normalization (hF : HasStrictFDerivAt F F' ((0 : E), d₀))
    (hFL : F' ∘L .inl ℝ E ℝ = L) (htriv : ∀ᶠ d in 𝓝 d₀, F ((0 : E), d) = 0)
    {φ : E} (hφ : φ ∈ pkg.decDom.X₀) (ψ : Y →L[ℝ] ℝ) (hψ1 : ∀ y ∈ pkg.decCodom.X₁, ψ y = 0)
    {L₁ : E →L[ℝ] Y}
    (hlin : ∀ᶠ d in 𝓝 d₀, HasFDerivAt (fun x => F (x, d)) (L + (d - d₀) • L₁) 0)
    {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hfac : ∀ᶠ q in 𝓝 ((0 : ℝ), d₀), lsScalar pkg hφ ψ hF hFL q = q.1 * G q)
    (hG : HasStrictFDerivAt G G' (0, d₀)) :
    G (0, d₀) = 0 ∧ G' (0, 1) = ψ (L₁ φ) := by
  have hψL : ∀ x, ψ (L x) = 0 := fun x => hψ1 _ (by rw [← pkg.range_eq]; exact ⟨x, rfl⟩)
  have hu := isLittleO_lsSolution pkg hF hFL htriv hφ
  have hs₀ : Tendsto (fun a : ℝ => (a, d₀)) (𝓝 0) (𝓝 ((0 : ℝ), d₀)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hA := tendsto_factor_slice pkg hF hFL hφ ψ hψL (d := d₀) (L₁ := L₁) hlin.self_of_nhds
    htriv.self_of_nhds ((hs₀.eventually (hu.def one_pos)).mono fun a ha => by simpa using ha)
    (hs₀.eventually hfac)
  simp only [sub_self, zero_mul, sub_zero] at hA
  have hG0 : G (0, d₀) = 0 :=
    tendsto_nhds_unique ((hG.continuousAt.tendsto.comp hs₀).mono_left nhdsWithin_le_nhds) hA
  refine ⟨hG0, eq_of_forall_dist_le fun ε hε => ?_⟩
  set K := ‖ψ‖ * ‖L₁‖ with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := ε / (1 + K) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hpair : Tendsto (fun q : ℝ × ℝ => (q, (q.1, d₀))) (𝓝 ((0 : ℝ), d₀))
      (𝓝 (((0 : ℝ), d₀), ((0 : ℝ), d₀))) := by
    have hc : Continuous fun q : ℝ × ℝ => (q, (q.1, d₀)) := by fun_prop
    simpa using hc.tendsto ((0 : ℝ), d₀)
  have hall := (hpair.eventually (hG.isLittleO.def hδ0)).and
    ((hu.def hδ0).and ((hu.def one_pos).and hfac))
  rw [nhds_prod_eq] at hall
  obtain ⟨pa, hpa, pb, hpb, hbox⟩ := eventually_prod_iff.1 hall
  obtain ⟨d, ⟨hdb, hdlin, hd0⟩, hdne⟩ :=
    (((hpb.and (hlin.and htriv)).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[≠] d₀, x ∈ ({d₀}ᶜ : Set ℝ))).exists
  have ht0 : d - d₀ ≠ 0 := sub_ne_zero.2 hdne
  have hB := tendsto_factor_slice pkg hF hFL hφ ψ hψL hdlin hd0
    (hpa.mono fun a ha => by simpa using (hbox ha hdb).2.2.1)
    (hpa.mono fun a ha => (hbox ha hdb).2.2.2)
  have hD := hB.sub hA
  rw [sub_zero] at hD
  have hbound : ∀ᶠ a in 𝓝[≠] (0 : ℝ), |d - d₀| * |G' (0, 1) - ψ (L₁ φ)| ≤
      (δ * |d - d₀| + K * δ * |d - d₀|) + ‖(G (a, d) - (d - d₀) * (ψ (L₁ φ) +
        ψ (L₁ (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d))) / a)) - G (a, d₀)‖ := by
    filter_upwards [hpa.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha ha0
    have ha0' : a ≠ 0 := ha0
    obtain ⟨h1, h2, -, -⟩ := hbox ha hdb
    have hG'eq : G' ((a, d) - (a, d₀)) = (d - d₀) * G' (0, 1) := by
      have : ((a, d) - (a, d₀) : ℝ × ℝ) = (d - d₀) • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_smul, smul_eq_mul]
    have hnorm : ‖((a, d) - (a, d₀) : ℝ × ℝ)‖ = |d - d₀| := by
      simp [Prod.norm_def]
    simp only at h1 h2
    rw [hG'eq, hnorm] at h1
    set w := ψ (L₁ (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d))) with hw
    have hψu : |w / a| ≤ K * δ := by
      rw [abs_div, div_le_iff₀ (abs_pos.2 ha0')]
      calc |w| ≤ ‖ψ‖ * ‖L₁ (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d))‖ := ψ.le_opNorm _
        _ ≤ ‖ψ‖ * (‖L₁‖ * ‖(lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d) : E)‖) := by
          gcongr; exact L₁.le_opNorm _
        _ ≤ ‖ψ‖ * (‖L₁‖ * (δ * ‖a‖)) := by gcongr
        _ = K * δ * |a| := by rw [Real.norm_eq_abs, hK]; ring
    have key : (d - d₀) * (G' (0, 1) - ψ (L₁ φ)) =
        -(G (a, d) - G (a, d₀) - (d - d₀) * G' (0, 1)) +
          ((G (a, d) - (d - d₀) * (ψ (L₁ φ) + w / a)) - G (a, d₀)) + (d - d₀) * (w / a) := by
      ring
    rw [← abs_mul, key, Real.norm_eq_abs]
    calc _ ≤ |-(G (a, d) - G (a, d₀) - (d - d₀) * G' (0, 1))| +
          |(G (a, d) - (d - d₀) * (ψ (L₁ φ) + w / a)) - G (a, d₀)| + |(d - d₀) * (w / a)| :=
          abs_add_three _ _ _
      _ ≤ δ * |d - d₀| + |(G (a, d) - (d - d₀) * (ψ (L₁ φ) + w / a)) - G (a, d₀)| +
          |d - d₀| * (K * δ) := by
          rw [abs_neg, abs_mul]
          gcongr
          simpa [Real.norm_eq_abs] using h1
      _ = _ := by ring
  have hlim : Tendsto (fun a : ℝ => (δ * |d - d₀| + K * δ * |d - d₀|) +
      ‖(G (a, d) - (d - d₀) * (ψ (L₁ φ) +
        ψ (L₁ (lsSolution pkg hF hFL (a • ⟨φ, hφ⟩, d))) / a)) - G (a, d₀)‖) (𝓝[≠] 0)
      (𝓝 ((δ * |d - d₀| + K * δ * |d - d₀|) + 0)) := by
    simpa using tendsto_const_nhds.add hD.norm
  have hle := ge_of_tendsto hlim hbound
  rw [Real.dist_eq]
  have h3 : |d - d₀| * |G' (0, 1) - ψ (L₁ φ)| ≤ |d - d₀| * ε := by
    calc _ ≤ (δ * |d - d₀| + K * δ * |d - d₀|) + 0 := hle
      _ = |d - d₀| * ((1 + K) * δ) := by ring
      _ = |d - d₀| * ε := by rw [hδ]; field_simp
  exact le_of_mul_le_mul_left h3 (abs_pos.2 ht0)

end Normalization

/-! ### The Turing linearization: crossing speed of the reduced coefficient -/

section Turing

variable {ι : Type*} [Fintype ι]

/-- **The Turing linearization is affine in the inhibitor diffusion.** On Neumann-mode
coefficients, `D(d) ∂ₓₓ + J = (D(d₀) ∂ₓₓ + J) + (d - d₀) diag(0, 1) ∂ₓₓ`, where
`modeOperator 0 0 1 κ` is the mode form `wᵢ ↦ -κᵢ² diag(0, 1) wᵢ` of `diag(0, 1) ∂ₓₓ`. -/
theorem modeOperator_eq_add_smul (J : Matrix (Fin 2) (Fin 2) ℝ) (du d d₀ : ℝ) (κ : ι → ℝ) :
    modeOperator J du d κ = modeOperator J du d₀ κ + (d - d₀) • modeOperator 0 0 1 κ := by
  refine ContinuousLinearMap.ext fun w => funext fun i => funext fun j => ?_
  fin_cases j
  · simp [modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

variable [DecidableEq ι]

/-- The critical functional normalized against the critical mode, `ψ̂ = ψ / ψ(φ)`, so that
`ψ̂ φ = 1` whenever `ψ(φ) = f_v tr (J - k² D) ≠ 0` (`criticalFunctional_criticalMode`). It cuts
out the same range as `criticalFunctional`. -/
noncomputable def normalizedCriticalFunctional (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ)
    (κ : ι → ℝ) (i₀ : ι) : (ι → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (criticalFunctional J du d κ i₀ (criticalMode J du d κ i₀))⁻¹ • criticalFunctional J du d κ i₀

/-- `ψ(φ) = f_v tr (J - k² D)`: the critical functional on the critical mode. -/
theorem criticalFunctional_criticalMode (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ) (κ : ι → ℝ)
    (i₀ : ι) : criticalFunctional J du d κ i₀ (criticalMode J du d κ i₀) =
      J 0 1 * (J.trace - κ i₀ ^ 2 * (du + d)) := by
  rw [← trace_modeMatrix J du d (κ i₀), Matrix.trace_fin_two]
  simp [criticalMode, kerVec]
  ring

/-- `ψ(L₁ φ) = f_v (d_u k⁴ - f_u k²)`: the critical functional on the `d`-derivative of the
linearization applied to the critical mode. -/
theorem criticalFunctional_modeOperator_criticalMode (J : Matrix (Fin 2) (Fin 2) ℝ) (du d : ℝ)
    (κ : ι → ℝ) (i₀ : ι) :
    criticalFunctional J du d κ i₀ (modeOperator 0 0 1 κ (criticalMode J du d κ i₀)) =
      J 0 1 * (du * (κ i₀ ^ 2) ^ 2 - J 0 0 * κ i₀ ^ 2) := by
  have h : modeOperator 0 0 1 κ (criticalMode J du d κ i₀) i₀ =
      ![0, κ i₀ ^ 2 * (J 0 0 - κ i₀ ^ 2 * du)] := by
    funext j
    fin_cases j
    · simp [criticalMode, kerVec, modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
    · simp [criticalMode, kerVec, modeMatrix, diffusionMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
  rw [criticalFunctional_apply, h]
  simp
  ring

/-- A function vanishing at `x₀` with positive derivative there has the sign of `x - x₀` near
`x₀`. -/
private theorem eventually_sign_eq {g : ℝ → ℝ} {σ x₀ : ℝ} (hg : HasDerivAt g σ x₀)
    (h0 : g x₀ = 0) (hσ : 0 < σ) : ∀ᶠ x in 𝓝 x₀, SignType.sign (g x) = SignType.sign (x - x₀) := by
  have hs : ∀ᶠ x in 𝓝[≠] x₀, 0 < slope g x₀ x :=
    (hasDerivAt_iff_tendsto_slope.1 hg).eventually (lt_mem_nhds hσ)
  filter_upwards [eventually_nhdsWithin_iff.1 hs] with x hx
  by_cases hxe : x = x₀
  · simp [hxe, h0]
  · have h := hx hxe
    rw [slope_def_field, h0, sub_zero] at h
    rcases lt_or_gt_of_ne (sub_ne_zero.2 hxe) with hneg | hpos
    · have hgx : g x < 0 := by
        rcases div_pos_iff.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact absurd h2 (not_lt.2 hneg.le)
        · exact h1
      rw [sign_neg hneg, sign_neg hgx]
    · rw [sign_pos hpos, sign_pos ((div_pos_iff_of_pos_right hpos).1 h)]

/-- **Turing pattern branch from the Lyapunov–Schmidt reduction.** Let mode `i₀`, with
wavenumber `k = κ i₀`, be admissible (`0 < f_u k² - d_u k⁴`) with neutral diffusion
`d₀ = d_n(k²)`, negative trace there, `f_v ≠ 0`, and no other mode critical at `d₀`. Let
`F(w, d)` be a map on Neumann-mode coefficients with the trivial branch `F(0, d) = 0`, strictly
differentiable at `(0, d₀)`, whose linearization along the trivial branch is the Turing
linearization `D(d) ∂ₓₓ + J` (`modeOperator J du d κ`) for every `d` near `d₀`. Fix a Fredholm
package of the linearization at `d₀`, and let `G` be a factor, strictly differentiable at
`(0, d₀)`, of the scalar bifurcation function for the critical mode and the normalized critical
functional: `G̃(a, d) = a G(a, d)` near `(0, d₀)`. Then

* `∂_d G(0, d₀)` is the crossing speed `(d_u k⁴ - f_u k²) / tr (J - k² D(d₀))` of the critical
  eigenvalue (`leadingEigenvalue_crossing`), in particular positive;
* near `d₀`, `G(0, d)` has the sign of the critical eigenvalue
  `leadingEigenvalue (J - k² D(d))`;
* there is a branch `d = β(a)` with `β 0 = d₀` and slope `-∂_a G / ∂_d G` at `0` such that near
  `(0, d₀)` the zeros of `F` are exactly the trivial ones `w = 0` and the branch
  `w = a φ + W(a φ, d)`, `d = β(a)`;
* for small `a ≠ 0` the branch state `a φ + W(a φ, β(a))` is a **nonzero** steady state at
  `d = β(a)` (a pattern);
* `G(0, d)` is negative for `d < d₀` and positive for `d > d₀` near `d₀`.

The trivial-branch values `G(0, d)` are not assumed; they are derived from the reduction
(`lsScalar_factor_normalization`), and they agree with the critical eigenvalue only to first
order at `d₀`. -/
theorem turing_patternBranch_of_reduction {J : Matrix (Fin 2) (Fin 2) ℝ} {du d₀ : ℝ}
    {κ : ι → ℝ} {i₀ : ι}
    (htr : J.trace - κ i₀ ^ 2 * (du + d₀) < 0) (hk : 0 < J 0 0 * κ i₀ ^ 2 - du * (κ i₀ ^ 2) ^ 2)
    (hd₀ : d₀ = neutralDiffusion J du (κ i₀ ^ 2)) (hfv : J 0 1 ≠ 0)
    (hnr : ∀ i, i ≠ i₀ → (modeMatrix J du d₀ (κ i)).det ≠ 0)
    (pkg : FredholmPackage (modeOperator J du d₀ κ))
    (hφ : criticalMode J du d₀ κ i₀ ∈ pkg.decDom.X₀)
    {F : (ι → Fin 2 → ℝ) × ℝ → ι → Fin 2 → ℝ}
    {F' : (ι → Fin 2 → ℝ) × ℝ →L[ℝ] ι → Fin 2 → ℝ}
    (hF : HasStrictFDerivAt F F' ((0 : ι → Fin 2 → ℝ), d₀))
    (hFL : F' ∘L .inl ℝ (ι → Fin 2 → ℝ) ℝ = modeOperator J du d₀ κ)
    (htriv : ∀ᶠ d in 𝓝 d₀, F (0, d) = 0)
    (hlin : ∀ᶠ d in 𝓝 d₀, HasFDerivAt (fun w => F (w, d)) (modeOperator J du d κ) 0)
    {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hfac : ∀ᶠ q in 𝓝 ((0 : ℝ), d₀),
      lsScalar pkg hφ (normalizedCriticalFunctional J du d₀ κ i₀) hF hFL q = q.1 * G q)
    (hG : HasStrictFDerivAt G G' (0, d₀)) :
    G' (0, 1) = (du * (κ i₀ ^ 2) ^ 2 - J 0 0 * κ i₀ ^ 2) / (J.trace - κ i₀ ^ 2 * (du + d₀)) ∧
      0 < G' (0, 1) ∧
      (∀ᶠ d in 𝓝 d₀, SignType.sign (G (0, d)) =
        SignType.sign (leadingEigenvalue (modeMatrix J du d (κ i₀)))) ∧
      ∃ β : ℝ → ℝ, β 0 = d₀ ∧ HasStrictDerivAt β (-(G' (1, 0) / G' (0, 1))) 0 ∧
        (∀ᶠ q in 𝓝 ((0 : ι → Fin 2 → ℝ), d₀), (F q = 0 ↔ q.1 = 0 ∨
          ∃ a : ℝ, q.1 = a • criticalMode J du d₀ κ i₀ +
            lsSolution pkg hF hFL (a • ⟨_, hφ⟩, q.2) ∧ q.2 = β a)) ∧
        (∀ᶠ a in 𝓝[≠] (0 : ℝ),
          F (a • criticalMode J du d₀ κ i₀ + lsSolution pkg hF hFL (a • ⟨_, hφ⟩, β a), β a) = 0 ∧
            a • criticalMode J du d₀ κ i₀ + lsSolution pkg hF hFL (a • ⟨_, hφ⟩, β a) ≠ 0) ∧
        (∀ᶠ d in 𝓝[<] d₀, G (0, d) < 0) ∧ ∀ᶠ d in 𝓝[>] d₀, 0 < G (0, d) := by
  have hcrit : (modeMatrix J du d₀ (κ i₀)).det = 0 := by
    rw [det_modeMatrix, dispersionDet_eq_mul_neutralDiffusion_sub hk.ne', ← hd₀, sub_self,
      mul_zero]
  obtain ⟨-, hspan, hψ1, hψ0⟩ := modeOperator_simpleKernel hcrit hfv hnr pkg
  have hψφ : criticalFunctional J du d₀ κ i₀ (criticalMode J du d₀ κ i₀) ≠ 0 := by
    rw [criticalFunctional_criticalMode]
    exact mul_ne_zero hfv htr.ne
  have hn : ∀ y, normalizedCriticalFunctional J du d₀ κ i₀ y =
      (criticalFunctional J du d₀ κ i₀ (criticalMode J du d₀ κ i₀))⁻¹ *
        criticalFunctional J du d₀ κ i₀ y := fun y => rfl
  have hn1 : ∀ y ∈ pkg.decCodom.X₁, normalizedCriticalFunctional J du d₀ κ i₀ y = 0 :=
    fun y hy => by rw [hn, hψ1 y hy, mul_zero]
  have hn0 : ∀ y ∈ pkg.decCodom.X₀, normalizedCriticalFunctional J du d₀ κ i₀ y = 0 → y = 0 :=
    fun y hy h => hψ0 y hy ((mul_eq_zero.1 ((hn y).symm.trans h)).resolve_left (inv_ne_zero hψφ))
  have hlin' : ∀ᶠ d in 𝓝 d₀, HasFDerivAt (fun w => F (w, d))
      (modeOperator J du d₀ κ + (d - d₀) • modeOperator 0 0 1 κ) 0 :=
    hlin.mono fun d hd => modeOperator_eq_add_smul J du d d₀ κ ▸ hd
  obtain ⟨hG0, hG'⟩ := lsScalar_factor_normalization pkg hF hFL htriv hφ _ hn1 hlin' hfac hG
  obtain ⟨hev0, hevd, hevpos⟩ := leadingEigenvalue_crossing htr hk hd₀
  have hσ : G' (0, 1) =
      (du * (κ i₀ ^ 2) ^ 2 - J 0 0 * κ i₀ ^ 2) / (J.trace - κ i₀ ^ 2 * (du + d₀)) := by
    rw [hG', hn, criticalFunctional_modeOperator_criticalMode, criticalFunctional_criticalMode]
    field_simp
  have hσpos : 0 < G' (0, 1) := hσ ▸ hevpos
  have hline : HasDerivAt (fun d => G (0, d)) (G' (0, 1)) d₀ :=
    hG.hasFDerivAt.comp_hasDerivAt d₀ ((hasDerivAt_const d₀ (0 : ℝ)).prodMk (hasDerivAt_id d₀))
  have hsG := eventually_sign_eq hline hG0 hσpos
  have hsev := eventually_sign_eq hevd hev0 hevpos
  obtain ⟨β, hβ0, hβd, hβz, hβF⟩ := lyapunovSchmidt_patternBranch pkg hF hFL htriv hφ
    (criticalMode_ne_zero hfv) hspan _ hn1 hn0 exists_patternBranch hfac hG hG0 hσpos.ne'
  refine ⟨hσ, hσpos, ?_, β, hβ0, hβd, hβz, ?_, ?_, ?_⟩
  · filter_upwards [hsG, hsev] with d h1 h2
    rw [h1, h2]
  · filter_upwards [nhdsWithin_le_nhds hβF, self_mem_nhdsWithin] with a ha ha0
    refine ⟨ha, fun h => ha0 ?_⟩
    have h' := congrArg (kerProj pkg) h
    rw [kerProj_smul_add pkg hφ, map_zero] at h'
    have h'' := congrArg Subtype.val h'
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h''
    exact (smul_eq_zero.1 h'').resolve_right (criticalMode_ne_zero hfv)
  · filter_upwards [nhdsWithin_le_nhds hsG, self_mem_nhdsWithin] with d h1 h2
    rw [sign_neg (sub_neg.2 h2)] at h1
    exact sign_eq_neg_one_iff.1 h1
  · filter_upwards [nhdsWithin_le_nhds hsG, self_mem_nhdsWithin] with d h1 h2
    rw [sign_pos (sub_pos.2 h2)] at h1
    exact sign_eq_one_iff.1 h1

end Turing

end MathlibExt.Biology.Dynamics.TuringBranchApplication

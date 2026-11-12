/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.IsingSHolo
import Code.FrontierA.LeeYangHalfPlaneDiagonal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.OpenMapping

open Filter Set Topology

namespace StatMech.Universality




noncomputable def isingFermionicEntireSquarePrimitive
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.wedgeIntegral 0 z (fun w ↦ f w ^ 2)

@[simp] theorem isingFermionicEntireSquarePrimitive_zero (f : ℂ → ℂ) :
    isingFermionicEntireSquarePrimitive f 0 = 0 := by
  simp [isingFermionicEntireSquarePrimitive, Complex.wedgeIntegral]




theorem isingFermionicEntireSquarePrimitive_hasDerivAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (isingFermionicEntireSquarePrimitive f) (f z ^ 2) z := by
  let g : ℂ → ℂ := fun w ↦ f w ^ 2
  let r : ℝ := ‖z‖ + 1
  have hg : Differentiable ℂ g := hf.pow 2
  have hz : z ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_zero_right, r]
    linarith
  have hconservative : Complex.IsConservativeOn g (Metric.ball 0 r) :=
    hg.differentiableOn.isConservativeOn
  simpa only [isingFermionicEntireSquarePrimitive, g] using
    hconservative.hasDerivAt_wedgeIntegral hg.continuous.continuousOn hz

theorem isingFermionicEntireSquarePrimitive_differentiable
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (isingFermionicEntireSquarePrimitive f) :=
  fun z ↦ (isingFermionicEntireSquarePrimitive_hasDerivAt hf z).differentiableAt





theorem isingFermionicEntireSquarePrimitive_im_eq_of_dense
    {f Phi : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hPhi : Continuous Phi) (S : Set ℂ) (hS : Dense S) (C : ℝ)
    (hEq : Set.EqOn
      (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im)
      (fun z ↦ (Phi z).im + C) S) :
    ∀ z, (isingFermionicEntireSquarePrimitive f z).im = (Phi z).im + C := by
  have hleft : Continuous
      (fun z ↦ (isingFermionicEntireSquarePrimitive f z).im) :=
    Complex.continuous_im.comp
      (isingFermionicEntireSquarePrimitive_differentiable hf).continuous
  have hright : Continuous (fun z ↦ (Phi z).im + C) :=
    (Complex.continuous_im.comp hPhi).add continuous_const
  exact fun z ↦ congrFun (Continuous.ext_on hS hleft hright hEq) z








theorem isingFermionic_primitive_eq_add_real_of_im_eq
    (P Phi : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) (C : ℝ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hP : DifferentiableOn ℂ P U) (hPhi : DifferentiableOn ℂ Phi U)
    (him : ∀ z ∈ U, (P z).im = (Phi z).im + C) :
    ∃ r : ℝ, ∀ z ∈ U, P z = Phi z + (r + C * Complex.I) := by
  have hanalytic : AnalyticOnNhd ℂ (P - Phi) U :=
    (hP.sub hPhi).analyticOnNhd hUopen
  have himSub : ∀ z ∈ U, ((P - Phi) z).im = C := by
    intro z hz
    change (P z).im - (Phi z).im = C
    linarith [him z hz]
  have hU : IsConnected U := ⟨⟨z₀, hz₀⟩, hUconnected⟩
  obtain ⟨r, hr⟩ :=
    hanalytic.eq_const_add_im_mul_I_of_re_eq_const himSub hUopen hU
  refine ⟨r, fun z hz ↦ ?_⟩
  have h := hr z hz
  change P z - Phi z = (r : ℂ) + (C : ℂ) * Complex.I at h
  linear_combination h





theorem isingFermionic_square_eq_of_primitive_im_eq
    (f target P Phi : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) (C : ℝ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hP : DifferentiableOn ℂ P U) (hPhi : DifferentiableOn ℂ Phi U)
    (hPderiv : Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
    (him : ∀ z ∈ U, (P z).im = (Phi z).im + C) :
    ∀ z ∈ U, f z ^ 2 = target z ^ 2 := by
  obtain ⟨r, hr⟩ := isingFermionic_primitive_eq_add_real_of_im_eq
    P Phi U z₀ C hUopen hUconnected hz₀ hP hPhi him
  intro z hz
  have heq : Set.EqOn P
      (fun w ↦ Phi w + ((r : ℂ) + (C : ℂ) * Complex.I)) U := hr
  have hderiv := (heq.deriv hUopen) hz
  rw [deriv_add_const] at hderiv
  calc
    f z ^ 2 = deriv P z := (hPderiv hz).symm
    _ = deriv Phi z := hderiv
    _ = target z ^ 2 := hPhideriv hz




theorem isingFermionic_squareRoot_unique_of_anchor
    (f target : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (htarget : DifferentiableOn ℂ target U)
    (hsquare : ∀ z ∈ U, f z ^ 2 = target z ^ 2)
    (hanchor : f z₀ = target z₀) (htarget_ne : target z₀ ≠ 0) :
    Set.EqOn f target U := by
  have hfAnalytic : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUopen
  have htargetAnalytic : AnalyticOnNhd ℂ target U :=
    htarget.analyticOnNhd hUopen
  have hsumContinuous : ContinuousAt (fun z => f z + target z) z₀ :=
    (hf.differentiableAt (hUopen.mem_nhds hz₀)).continuousAt.add
      (htarget.differentiableAt (hUopen.mem_nhds hz₀)).continuousAt
  have hsumAnchor : f z₀ + target z₀ ≠ 0 := by
    rw [hanchor]
    intro hzero
    exact htarget_ne (add_self_eq_zero.mp hzero)
  have hsum_ne : ∀ᶠ z in 𝓝 z₀, f z + target z ≠ 0 :=
    hsumContinuous.eventually_ne hsumAnchor
  have heq : f =ᶠ[𝓝 z₀] target := by
    filter_upwards [hsum_ne, hUopen.mem_nhds hz₀] with z hsum hzU
    have hprod : (f z - target z) * (f z + target z) = 0 := by
      calc
        (f z - target z) * (f z + target z) = f z ^ 2 - target z ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr (hsquare z hzU)
    rcases mul_eq_zero.mp hprod with hdiff | hsumZero
    · exact sub_eq_zero.mp hdiff
    · exact (hsum hsumZero).elim
  exact hfAnalytic.eqOn_of_preconnected_of_eventuallyEq
    htargetAnalytic hUconnected hz₀ heq





theorem isingFermionic_square_eq_of_squareDeriv_eq
    (f target : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : DifferentiableOn ℂ f U) (htarget : DifferentiableOn ℂ target U)
    (hderiv : Set.EqOn (deriv (fun z => f z ^ 2))
      (deriv (fun z => target z ^ 2)) U)
    (hanchor : f z₀ ^ 2 = target z₀ ^ 2) :
    ∀ z ∈ U, f z ^ 2 = target z ^ 2 := by
  exact hUopen.eqOn_of_deriv_eq hUconnected (hf.pow 2) (htarget.pow 2)
    hderiv hz₀ hanchor












theorem isingFermionic_fullConvergence_of_subsequential_square
    (F : ℕ → ℂ → ℂ) (target : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (htarget : DifferentiableOn ℂ target U) (htarget_ne : target z₀ ≠ 0)
    (hcompact : StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U)
    (hidentify : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ),
      StrictMono φ → StrictMono ψ →
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U →
      (∀ z ∈ U, f z ^ 2 = target z ^ 2) ∧ f z₀ = target z₀) :
    TendstoLocallyUniformlyOn F target atTop U ∧
      TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
  have hfull : TendstoLocallyUniformlyOn F target atTop U :=
    StatMech.FrontierA.tendstoLocallyUniformlyOn_of_subsequential_limits_unique
      F target U hUopen hcompact (fun φ ψ f hφ hψ hlimit => by
        obtain ⟨hsquare, hanchor⟩ := hidentify φ ψ f hφ hψ hlimit
        have hf : DifferentiableOn ℂ f U :=
          hlimit.differentiableOn
            (Eventually.of_forall (fun n => hF (φ (ψ n)))) hUopen
        exact isingFermionic_squareRoot_unique_of_anchor
          f target U z₀ hUopen hUconnected hz₀ hf htarget hsquare
          hanchor htarget_ne)
  exact ⟨hfull, hfull.deriv (Eventually.of_forall hF) hUopen⟩






theorem isingFermionic_fullConvergence_of_subsequential_squareDeriv
    (F : ℕ → ℂ → ℂ) (target : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (htarget : DifferentiableOn ℂ target U) (htarget_ne : target z₀ ≠ 0)
    (hcompact : StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U)
    (hidentifyDeriv : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ),
      StrictMono φ → StrictMono ψ →
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U →
      Set.EqOn (deriv (fun z => f z ^ 2))
        (deriv (fun z => target z ^ 2)) U ∧ f z₀ = target z₀) :
    TendstoLocallyUniformlyOn F target atTop U ∧
      TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
  apply isingFermionic_fullConvergence_of_subsequential_square
    F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hcompact
  intro φ ψ f hφ hψ hlimit
  obtain ⟨hderiv, hanchor⟩ := hidentifyDeriv φ ψ f hφ hψ hlimit
  have hf : DifferentiableOn ℂ f U :=
    hlimit.differentiableOn
      (Eventually.of_forall (fun n => hF (φ (ψ n)))) hUopen
  refine ⟨isingFermionic_square_eq_of_squareDeriv_eq
    f target U z₀ hUopen hUconnected hz₀ hf htarget hderiv ?_, hanchor⟩
  rw [hanchor]





theorem isingFermionic_fullConvergence_of_compactBounds_and_squareDeriv
    (F : ℕ → ℂ → ℂ) (target : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (htarget : DifferentiableOn ℂ target U) (htarget_ne : target z₀ ≠ 0)
    (E : StatMech.FrontierA.CompactExhaustion U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (hidentifyDeriv : ∀ (φ ψ : ℕ → ℕ) (f : ℂ → ℂ),
      StrictMono φ → StrictMono ψ →
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop U →
      Set.EqOn (deriv (fun z => f z ^ 2))
        (deriv (fun z => target z ^ 2)) U ∧ f z₀ = target z₀) :
    TendstoLocallyUniformlyOn F target atTop U ∧
      TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
  have hcompact :
      StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U :=
    StatMech.FrontierA.holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hF hbounded E
  exact isingFermionic_fullConvergence_of_subsequential_squareDeriv
    F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne
    hcompact hidentifyDeriv










theorem isingFermionic_fullConvergence_of_compactBounds_and_primitiveIm
    (F : ℕ → ℂ → ℂ) (target Phi : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (htarget : DifferentiableOn ℂ target U) (htarget_ne : target z₀ ≠ 0)
    (hPhi : DifferentiableOn ℂ Phi U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) U)
    (E : StatMech.FrontierA.CompactExhaustion U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (hidentifyPrimitive : ∀ (phi psi : ℕ → ℕ) (f : ℂ → ℂ),
      StrictMono phi → StrictMono psi →
      TendstoLocallyUniformlyOn (fun n ↦ F (phi (psi n))) f atTop U →
      ∃ (P : ℂ → ℂ) (C : ℝ),
        DifferentiableOn ℂ P U ∧
        Set.EqOn (deriv P) (fun z ↦ f z ^ 2) U ∧
        (∀ z ∈ U, (P z).im = (Phi z).im + C) ∧
        f z₀ = target z₀) :
    TendstoLocallyUniformlyOn F target atTop U ∧
      TendstoLocallyUniformlyOn (deriv ∘ F) (deriv target) atTop U := by
  have hcompact :
      StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact F U :=
    StatMech.FrontierA.holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hF hbounded E
  apply isingFermionic_fullConvergence_of_subsequential_square
    F target U z₀ hUopen hUconnected hz₀ hF htarget htarget_ne hcompact
  intro phi psi f hphi hpsi hlimit
  obtain ⟨P, C, hP, hPderiv, him, hanchor⟩ :=
    hidentifyPrimitive phi psi f hphi hpsi hlimit
  exact ⟨isingFermionic_square_eq_of_primitive_im_eq
    f target P Phi U z₀ C hUopen hUconnected hz₀ hP hPhi
      hPderiv hPhideriv him, hanchor⟩

end StatMech.Universality

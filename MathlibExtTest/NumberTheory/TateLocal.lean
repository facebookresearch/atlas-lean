/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TateLocal

@[expose] public section

open TateLocal IsDedekindDomain MeasureTheory
open scoped NumberField

namespace TateLocalTest

/-- Consumer with the original binders: membership in the test space unfolds
to the two defining properties. -/
example {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  mem_testSpace_iff

/-- Nontrivial instance: the indicator of the whole space in a compact
discrete two-point space lies in the test space, and it is not zero. -/
example : ((Set.univ.indicator fun _ : Fin 2 => (1 : ℂ)) : Fin 2 → ℂ) ∈
      testSpace (Fin 2) ∧
    ((Set.univ.indicator fun _ : Fin 2 => (1 : ℂ)) : Fin 2 → ℂ) ≠ 0 := by
  constructor
  · exact indicator_mem_testSpace isClopen_univ isCompact_univ 1
  · intro h
    have h1 := congrFun h 0
    simp at h1

/-- The zero function is a test function on any locally compact field. -/
example {K : Type*} [Field K] [TopologicalSpace K] :
    (0 : K → ℂ) ∈ testSpace K := by
  rw [mem_testSpace_iff]
  exact ⟨by simpa using
    (IsLocallyConstant.const (0 : ℂ) :
      IsLocallyConstant (Function.const K (0 : ℂ))), HasCompactSupport.zero⟩

/-- Consumer for the conductor API at a finite place of a number field,
with the trivial character. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (s : ℂ) :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 ∧
      localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s =
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
  ⟨conductorExponentAt_one K v, localLFactorAt_one K v s⟩

/-- A reported conductor exponent `0` is a genuine conductor exponent `0`. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (h : conductorExponentAt K v χ = 0) :
    HasConductorExponentAt K v χ 0 :=
  (conductorExponentAt_eq_coe_iff K v).mp h

/-- Without a finite conductor exponent the conductor exponent is `⊤`, not
`0`. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (h : ∀ c, ¬ HasConductorExponentAt K v χ c) :
    conductorExponentAt K v χ = ⊤ ∧ conductorExponentAt K v χ ≠ 0 := by
  have htop := (conductorExponentAt_eq_top_iff K v).mpr h
  exact ⟨htop, by simp [htop]⟩

/-- The trivial character has no positive conductor exponent. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : ℕ)
    (h : conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = (c + 1 : ℕ)) :
    False :=
  not_hasConductorExponentAt_one_succ K v c ((conductorExponentAt_eq_coe_iff K v).mp h)

/-- The unramified `L`-factor evaluates the character at the library's
uniformizer of the completion. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s =
      (1 - (χ (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
  localLFactorAt_of_hasConductorExponentAt_zero K v hχ s

/-- Modulus API on a concrete locally compact field. -/
example : modulus (2 : ℝ) ≠ 0 ∧ modulus (1 : ℝ) = 1 :=
  ⟨modulus_ne_zero (by norm_num), modulus_one⟩

/-- Lebesgue measure on `ℝ` is an additive Haar measure, so it has local zeta
integrals. -/
example (χ : ℝˣ →* ℂˣ) (s : ℂ) : localZeta (volume : Measure ℝ) 0 χ s = 0 :=
  localZeta_zero_fun _ χ s

/-- The zeta integrals and the gamma factors reject a measure that is not an
additive Haar measure, such as the zero measure. -/
example : True := by
  fail_if_success have := localZeta (0 : Measure ℝ) 0 (1 : ℝˣ →* ℂˣ) 0
  fail_if_success have := IsLocalGammaFactor (0 : Measure ℝ) 1 (1 : ℝˣ →* ℂˣ) 0 0
  trivial

/-- Two local gamma factors agree once one test function has a nonzero zeta
integral. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ) (χ : Kˣ →* ℂˣ) (s γ γ' : ℂ) (f : K → ℂ)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0)
    (h : IsLocalGammaFactor μ ψ χ s γ) (h' : IsLocalGammaFactor μ ψ χ s γ') :
    γ = γ' :=
  h.unique h' hf hZ

/-- Under the symmetric local functional equation, every local gamma factor is
the zeta ratio of a test function with nonzero zeta integral. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ) (χ : Kˣ →* ℂˣ) (s γ : ℂ) (f : K → ℂ)
    (hsymm : ∀ f ∈ testSpace K, ∀ g ∈ testSpace K,
      localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s =
        localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0)
    (h : IsLocalGammaFactor μ ψ χ s γ) :
    γ = localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s :=
  h.unique (isLocalGammaFactor_div_of_mul_comm hsymm hf hZ) hf hZ

/-- For a ramified character the local epsilon factors are the local gamma
factors. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    [LocallyCompactSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K))
    [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : ¬ HasConductorExponentAt K v χ 0)
    (s γ : ℂ) (h : IsLocalGammaFactor μ ψ χ s γ) :
    IsLocalEpsilonFactorAt K v μ ψ χ s γ :=
  (isLocalEpsilonFactorAt_iff_of_not_hasConductorExponentAt_zero K v μ ψ hχ s γ).mpr h

/-- For the trivial character the local epsilon factor is the gamma factor
times the ratio of the two Euler factors. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    [LocallyCompactSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K))
    [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ) (s γ : ℂ)
    (h : IsLocalGammaFactor μ ψ 1 s γ) :
    IsLocalEpsilonFactorAt K v μ ψ 1 s
      (γ * (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ /
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))⁻¹) :=
  ⟨γ, h, by
    rw [show (1 : (v.adicCompletion K)ˣ →* ℂˣ)⁻¹ = 1 from MonoidHom.ext fun _ => by simp,
      localLFactorAt_one, localLFactorAt_one]⟩

end TateLocalTest

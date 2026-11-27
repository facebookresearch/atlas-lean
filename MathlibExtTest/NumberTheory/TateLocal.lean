/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TateLocal
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Instances.ZMod

@[expose] public section

open LanglandsTunnell.TateLocal IsDedekindDomain MeasureTheory Metric
open scoped NumberField Pointwise ENNReal

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

/-- At a pole the `L`-factor takes the totalized value `0`: for the trivial character at
`s = 0` the Euler factor is `(1 - 1)⁻¹`, and Lean's `0⁻¹` is `0`. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 = 0 := by
  simp [localLFactorAt, hasConductorExponentAt_one_zero K v]

/-- Modulus API on a concrete locally compact field. -/
example : modulus (2 : ℝ) ≠ 0 ∧ modulus (1 : ℝ) = 1 :=
  ⟨modulus_ne_zero (by norm_num), modulus_one⟩

/-- A unit of `ℤ_[p]` has modulus `1`: multiplication by it maps the closed unit ball, which is
compact and open, onto itself. -/
private theorem modulus_eq_one_of_norm_eq_one {p : ℕ} [Fact p.Prime] {u : ℚ_[p]}
    (hu : ‖u‖ = 1) : modulus u = 1 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [modulus_of_ne_zero hu0]
  let _ : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  have : BorelSpace ℚ_[p] := ⟨rfl⟩
  have hB : Units.mk0 u hu0 • closedBall (0 : ℚ_[p]) 1 = closedBall 0 1 := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, mem_closedBall_zero_iff,
      mem_closedBall_zero_iff, norm_mul, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hu,
      inv_one, one_mul]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.addHaar)
    (s := closedBall (0 : ℚ_[p]) 1) ?_ ?_ ?_
  · exact (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).measure_ne_zero _
      (nonempty_closedBall.mpr zero_le_one)
  · exact (isCompact_closedBall (0 : ℚ_[p]) 1).measure_lt_top.ne
  · rw [hB, ENNReal.coe_one, one_mul]

/-- The measure `mulMeasure μ` gives the units of `ℤ_[p]` and their translate by the
uniformizer `p` equal, positive and finite mass. The additive Haar measure does not: it scales
the translate by the modulus of `p`, which is `p⁻¹`. -/
example (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] :
    let ϖ : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    mulMeasure μ (ϖ • sphere (0 : ℚ_[p]) 1) = mulMeasure μ (sphere 0 1) ∧
      0 < mulMeasure μ (sphere (0 : ℚ_[p]) 1) ∧ mulMeasure μ (sphere (0 : ℚ_[p]) 1) < ⊤ := by
  intro ϖ
  have hUo : IsOpen (sphere (0 : ℚ_[p]) 1) := IsUltrametricDist.isOpen_sphere _ one_ne_zero
  have hUm : MeasurableSet (sphere (0 : ℚ_[p]) 1) := hUo.measurableSet
  have hϖUm : MeasurableSet (ϖ • sphere (0 : ℚ_[p]) 1) := (hUo.smul ϖ).measurableSet
  have hU0 : sphere (0 : ℚ_[p]) 1 ⊆ {0}ᶜ := fun x hx h0 => by simp_all
  have hϖU0 : ϖ • sphere (0 : ℚ_[p]) 1 ⊆ {0}ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ h0
    have : (ϖ : ℚ_[p]) * y = 0 := h0
    rcases mul_eq_zero.mp this with h | h
    · exact ϖ.ne_zero h
    · simp_all
  have hmass : mulMeasure μ (sphere (0 : ℚ_[p]) 1) = μ (sphere 0 1) := by
    rw [mulMeasure, withDensity_apply _ hUm,
      setLIntegral_congr_fun hUm (g := fun _ => 1) fun x hx => by
        simp [modulus_eq_one_of_norm_eq_one (by simpa using hx)],
      setLIntegral_const, one_mul, Measure.restrict_apply hUm, Set.inter_eq_left.mpr hU0]
  have hmass' : mulMeasure μ (ϖ • sphere (0 : ℚ_[p]) 1) = μ (sphere 0 1) := by
    rw [mulMeasure, withDensity_apply _ hϖUm,
      setLIntegral_congr_fun hϖUm (g := fun _ => ((distribHaarChar ℚ_[p] ϖ : ℝ≥0∞))⁻¹) ?_,
      setLIntegral_const, Measure.restrict_apply hϖUm, Set.inter_eq_left.mpr hϖU0,
      ← distribHaarChar_mul μ ϖ, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne') ENNReal.coe_ne_top,
      one_mul]
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ = 1 := by simpa using hy
    simp only [smul_eq_mul, modulus_mul, modulus_coe_units, modulus_eq_one_of_norm_eq_one hy1,
      mul_one]
  refine ⟨hmass'.trans hmass.symm, ?_, ?_⟩
  · rw [hmass]
    exact hUo.measure_pos μ ⟨1, by simp⟩
  · rw [hmass]
    exact (isCompact_sphere (0 : ℚ_[p]) 1).measure_lt_top

/-- On every field where the gamma factors are stated (totally disconnected, hence `T1`),
`mulMeasure μ` gives `{0}` mass zero, with no further hypothesis. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TotallyDisconnectedSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] :
    mulMeasure μ {0} = 0 :=
  mulMeasure_singleton_zero μ

/-- On the discrete field `ZMod 2` an additive Haar measure gives `{0}` positive mass, and
`mulMeasure μ` removes it. -/
example [MeasurableSpace (ZMod 2)] [BorelSpace (ZMod 2)] (μ : Measure (ZMod 2))
    [μ.IsAddHaarMeasure] : 0 < μ {0} ∧ mulMeasure μ {0} = 0 :=
  ⟨(isOpen_discrete {0}).measure_pos μ (Set.singleton_nonempty 0), mulMeasure_singleton_zero μ⟩

/-- `ZMod 2` with the indiscrete topology. -/
private def IndiscreteZMod2 : Type := ZMod 2

private instance : Field IndiscreteZMod2 := inferInstanceAs (Field (ZMod 2))

private instance : Finite IndiscreteZMod2 := inferInstanceAs (Finite (ZMod 2))

private instance : TopologicalSpace IndiscreteZMod2 := ⊤

private instance : IsTopologicalRing IndiscreteZMod2 where
  continuous_add := continuous_top
  continuous_mul := continuous_top
  continuous_neg := continuous_top

private instance : LocallyCompactSpace IndiscreteZMod2 :=
  ⟨fun _ n hn => ⟨n, hn, subset_rfl, n.toFinite.isCompact⟩⟩

private instance : MeasurableSpace IndiscreteZMod2 := borel IndiscreteZMod2

private instance : BorelSpace IndiscreteZMod2 := ⟨rfl⟩

/-- Without measurable singletons `mulMeasure` can charge `0`: on `ZMod 2` with the indiscrete
topology the only measurable set containing `0` is the whole space, so `{0}` gets the full,
positive mass. This is why `mulMeasure_singleton_zero` assumes `MeasurableSingletonClass`. -/
example : 0 < mulMeasure (Measure.addHaar : Measure IndiscreteZMod2) {0} := by
  set μ : Measure IndiscreteZMod2 := Measure.addHaar
  have hmeas : ∀ t : Set IndiscreteZMod2, MeasurableSet t → t = ∅ ∨ t = Set.univ := by
    intro t ht
    have hle : borel IndiscreteZMod2 ≤ ⊥ := MeasurableSpace.generateFrom_le fun u hu => by
      rcases (TopologicalSpace.isOpen_top_iff u).mp hu with rfl | rfl
      · exact @MeasurableSet.empty _ ⊥
      · exact @MeasurableSet.univ _ ⊥
    exact MeasurableSpace.measurableSet_bot_iff.mp (hle t ht)
  have hfull : ∀ (m : Measure IndiscreteZMod2) (s : Set IndiscreteZMod2), s.Nonempty →
      m s = m Set.univ := by
    intro m s hs
    rw [← measure_toMeasurable s]
    rcases hmeas _ (measurableSet_toMeasurable m s) with h | h
    · exact absurd (h ▸ subset_toMeasurable m s)
        (Set.nonempty_iff_ne_empty.mp hs ∘ Set.subset_empty_iff.mp)
    · rw [h]
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [hfull _ _ (Set.singleton_nonempty 0), mulMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc (0 : ℝ≥0∞) < μ Set.univ := Measure.measure_univ_pos.mpr (NeZero.ne μ)
    _ = μ.restrict {0}ᶜ Set.univ := by
          rw [Measure.restrict_apply_univ, hfull μ {0}ᶜ ⟨1, by simp⟩]
    _ = ∫⁻ _, 1 ∂(μ.restrict {0}ᶜ) := by rw [lintegral_one]
    _ ≤ ∫⁻ x, ((modulus x : ℝ≥0∞))⁻¹ ∂(μ.restrict {0}ᶜ) := by
          refine lintegral_mono fun x => ?_
          rcases h01 x with h | h
          · rw [show x = 0 from h, modulus_zero]; simp
          · rw [show x = 1 from h, modulus_one]; simp

/-- Lebesgue measure on `ℝ` is an additive Haar measure, so it has local zeta
integrals. -/
example (χ : ℝˣ →* ℂˣ) (s : ℂ) : localZeta (volume : Measure ℝ) 0 χ s = 0 :=
  localZeta_zero_fun _ χ s

/-- The zeta integrals reject a measure that is not an additive Haar measure,
such as the zero measure. -/
example : True := by
  fail_if_success have := localZeta (0 : Measure ℝ) 0 (1 : ℝˣ →* ℂˣ) 0
  trivial

/-- The gamma factors at a finite place reject the zero measure. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    [LocallyCompactSpace (v.adicCompletion K)] : True := by
  fail_if_success
    have := IsLocalGammaFactor (0 : Measure (v.adicCompletion K)) 1
      (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 0
  trivial

/-- The gamma factors are not defined over `ℝ`, which is not totally disconnected:
its locally constant test space is zero, so the functional equation would hold for
every `γ`. -/
example : True := by
  fail_if_success have := IsLocalGammaFactor (volume : Measure ℝ) 1 (1 : ℝˣ →* ℂˣ) 0 0
  trivial

/-- Admissible data exclude the trivial additive character. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TotallyDisconnectedSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (χ : Kˣ →* ℂˣ)
    (s : ℂ) (h : IsLocalZetaAdmissible μ (1 : AddChar K ℂ) χ s) : False :=
  h.addChar_ne_one rfl

/-- Admissible data make the zeta integrand of every test function integrable. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TotallyDisconnectedSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)
    (χ : Kˣ →* ℂˣ) (s γ : ℂ) (h : IsLocalGammaFactor μ ψ χ s γ) (f : K → ℂ)
    (hf : f ∈ testSpace K) :
    Integrable (fun x => f x * MulChar.ofUnitHom χ x * ((modulus x : ℝ) : ℂ) ^ s)
        (mulMeasure μ) ∧
      Continuous χ :=
  ⟨h.integrable_zeta f hf, h.continuous_char⟩

/-- Two local gamma factors agree once one test function has a nonzero zeta
integral. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TotallyDisconnectedSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)
    (χ : Kˣ →* ℂˣ) (s γ γ' : ℂ) (f : K → ℂ)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0)
    (h : IsLocalGammaFactor μ ψ χ s γ) (h' : IsLocalGammaFactor μ ψ χ s γ') :
    γ = γ' :=
  h.unique h' hf hZ

/-- For admissible data under the symmetric local functional equation, every
local gamma factor is the zeta ratio of a test function with nonzero zeta
integral. -/
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [TotallyDisconnectedSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)
    (χ : Kˣ →* ℂˣ) (s γ : ℂ) (f : K → ℂ) (hadm : IsLocalZetaAdmissible μ ψ χ s)
    (hsymm : ∀ f ∈ testSpace K, ∀ g ∈ testSpace K,
      localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s =
        localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s)
    (hf : f ∈ testSpace K) (hZ : localZeta μ f χ s ≠ 0)
    (h : IsLocalGammaFactor μ ψ χ s γ) :
    γ = localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) / localZeta μ f χ s :=
  h.unique (isLocalGammaFactor_div_of_mul_comm hadm hsymm hf hZ) hf hZ

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

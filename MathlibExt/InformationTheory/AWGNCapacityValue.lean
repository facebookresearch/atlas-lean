/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.GaussianChannelLogDet
public import MathlibExt.InformationTheory.ScalarGaussianCoordinates
public import MathlibExt.Probability.Distributions.GaussianConditioning
import MathlibExt.InformationTheory.AWGNConverse

/-!
# Scalar AWGN variational capacity value

For the scalar additive white Gaussian noise channel `Y = X + Z`, with noise `Z ~ N(0, N)`,
`N > 0`, independent of the input, and power budget `P ≥ 0`, the variational capacity is the
`ℝ≥0∞` supremum of the mutual information `I(X; Y)`, in bits, over **all** input laws under the
scalar total-power model `E X² ≤ P` (a lower integral; no integrability, Gaussianity or centering
is assumed). Its value is

`C(P, N) = ofReal (log (1 + P / N) / (2 log 2))` bits.

The channel is the canonical additive-noise kernel `x ↦ law of x + Z`
(`MetaMathlibExt.noiseKernel id`), and the joint law of an input law `p` is `p ⊗ₘ` that kernel
(`channelJoint`). `map_prod_add_eq_compProd_awgnKernel` identifies it with the joint law of
`(X, X + Z)` for any independent random variables. The supremum `powerCapacity κ P` is defined
for any Markov kernel `κ` on `ℝ`; the assembly lemma, the zero-power value and the feasible-set
lemmas hold for every such `κ`.

Main results:
* `awgnCapacity_eq_ofReal_log`: the capacity value for `P ≥ 0` and `N > 0`, with no further
  hypothesis; its converse `measureMutualInformation_channelJoint_le` reads the all-law bound of
  `MathlibExt.InformationTheory.AWGNConverse` on input laws.
* `awgnCapacity_eq`: the capacity value, given the all-law converse and, for `P > 0`, Gaussian
  attainment as hypotheses over the channel; `awgnCapacity_eq_of_randomVariables` states both
  hypotheses for random variables `(X, X + Z)`.
* `measureMutualInformation_channelJoint_gaussianInput`: Gaussian attainment, the
  one-dimensional instance of the Gaussian-input log-determinant formula.
* `awgnCapacity_eq_of_converse`: the capacity value from the converse alone.
* `powerCapacity_zero`: at `P = 0` the only admissible law is the constant-zero law, so the
  capacity of every channel is `0`, with no hypothesis.
* `exists_mem_inputFeasible_eq_awgnCapacity`, `awgnCapacity_ne_top`, `awgnCapacity_toReal`:
  attainment of the supremum, finiteness, and the real-valued form after finiteness.

Validation: `P = 0` (value `0`, unconditional); `P = N` (value `1 / 2` bit); the feasible set
contains laws other than the centered Gaussian (constant inputs, and the antipodal two-point law,
which is not Gaussian for `P > 0`); violated premises: a negative budget gives capacity `0` while
the formula at `P = -3N` gives `1 / 2`, and the noiseless channel `N = 0` has infinite capacity
while the formula gives `0`.

The all-law converse is `measureMutualInformation_scalarAWGN_le` of
`MathlibExt.InformationTheory.AWGNConverse`. This is a variational formula: it is not an
operational coding theorem and not a statement about bandlimited continuous-time channels
(Shannon-Hartley in bits per second).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal

/-! ### Definitions -/

namespace MathlibExt.InformationTheory.AWGNCapacityValue

open _root_.InformationTheory
open MathlibExt.InformationTheory.ScalarGaussianCoordinates
open MathlibExt.InformationTheory.GaussianChannelLogDet

/-- The scalar AWGN channel with noise variance `N`: the canonical additive-noise kernel
`x ↦ law of x + Z`, `Z ~ N(0, N)`. -/
noncomputable def awgnKernel (N : ℝ≥0) : Kernel ℝ ℝ :=
  MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N)

/-- The scalar AWGN channel is a Markov kernel. -/
instance (N : ℝ≥0) : IsMarkovKernel (awgnKernel N) := by
  unfold awgnKernel
  infer_instance

/-- The all-law feasible set at budget `P`: input laws `p` on `ℝ` under the scalar total-power
model, `P ≥ 0` and `∫⁻ ofReal (x²) ∂p ≤ ofReal P`. Any law qualifies, Gaussian or not, centered
or not. -/
def inputFeasible (P : ℝ) : Set (ProbabilityMeasure ℝ) :=
  {p | scalarPowerBound (p : Measure ℝ) id P}

/-- The joint law of input and output for input law `p` through the channel `κ`: `p ⊗ₘ κ`. -/
noncomputable def channelJoint (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (p : ProbabilityMeasure ℝ) :
    ProbabilityMeasure (ℝ × ℝ) :=
  ⟨(p : Measure ℝ) ⊗ₘ κ, inferInstance⟩

/-- The variational power-constrained capacity of a channel `κ` on `ℝ`, in bits: the `ℝ≥0∞`
supremum of the mutual information over all input laws in `inputFeasible P`. -/
noncomputable def powerCapacity (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (P : ℝ) : ℝ≥0∞ :=
  ⨆ p ∈ inputFeasible P, measureMutualInformation (channelJoint κ p)

/-- The scalar AWGN variational capacity at power budget `P` and noise variance `N`, in bits. -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) : ℝ≥0∞ :=
  powerCapacity (awgnKernel N) P

/-- The constant input law `δ_c`. -/
noncomputable def diracInput (c : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac c, inferInstance⟩

/-- The centered Gaussian input law `N(0, P)`; a negative `P` is read as variance `0`. -/
noncomputable def gaussianInput (P : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 P.toNNReal, inferInstance⟩

/-- The antipodal two-point input law, `(δ_a + δ_{-a}) / 2`; not Gaussian when `a ≠ 0`. -/
noncomputable def antipodalLaw (a : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(2 : ℝ≥0∞)⁻¹ • (Measure.dirac a + Measure.dirac (-a)), ⟨by
    rw [_root_.smul_apply, _root_.add_apply, measure_univ, measure_univ, smul_eq_mul,
      one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩⟩

/-! ### Abstract channel -/

/-- Every admissible input law gives mutual information at most the capacity. -/
theorem le_powerCapacity (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] {P : ℝ}
    {p : ProbabilityMeasure ℝ} (hp : p ∈ inputFeasible P) :
    measureMutualInformation (channelJoint κ p) ≤ powerCapacity κ P := by
  exact le_iSup₂_of_le (f := fun p _ => measureMutualInformation (channelJoint κ p)) p hp le_rfl

/-- **Capacity assembly.** If every admissible law gives mutual information at most `v` (a
converse) and some admissible law `p₀` gives exactly `v` (attainment), the capacity is `v`. -/
theorem powerCapacity_eq_of_le_of_attains (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] {P : ℝ}
    {v : ℝ≥0∞} (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint κ p) ≤ v)
    {p₀ : ProbabilityMeasure ℝ} (hp₀ : p₀ ∈ inputFeasible P)
    (hatt : measureMutualInformation (channelJoint κ p₀) = v) :
    powerCapacity κ P = v := by
  exact le_antisymm (iSup₂_le hconv) (hatt ▸ le_powerCapacity κ hp₀)

/-- A negative budget admits no input law: the nonnegativity conjunct of the power model. -/
theorem inputFeasible_eq_empty_of_neg {P : ℝ} (hP : P < 0) : inputFeasible P = ∅ := by
  exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => absurd hp.1 (not_le.mpr hP)

/-- Measurability of the power integrand. -/
private theorem measurable_ofReal_sq : Measurable fun x : ℝ => ENNReal.ofReal ((id x) ^ 2) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)

/-- A constant input `c` is admissible whenever `c² ≤ P`. -/
private theorem diracInput_mem_inputFeasible_aux {c P : ℝ} (hc : c ^ 2 ≤ P) :
    diracInput c ∈ inputFeasible P := by
  refine ⟨(sq_nonneg c).trans hc, ?_⟩
  change ∫⁻ x, ENNReal.ofReal ((id x) ^ 2) ∂(Measure.dirac c) ≤ ENNReal.ofReal P
  rw [lintegral_dirac]
  exact ENNReal.ofReal_le_ofReal hc

/-- At budget `0` the only admissible input law is the constant-zero law `δ₀`. -/
theorem inputFeasible_zero :
    inputFeasible 0 = {diracInput 0} := by
  ext p
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hp⟩
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero, lintegral_eq_zero_iff measurable_ofReal_sq] at hp
    have hae : (id : ℝ → ℝ) =ᵐ[(p : Measure ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [hp] with x hx
      have h2 : (id x) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
      have h3 : (id x) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h3
    apply ProbabilityMeasure.toMeasure_injective
    change (p : Measure ℝ) = Measure.dirac 0
    calc (p : Measure ℝ) = (p : Measure ℝ).map id := Measure.map_id.symm
      _ = (p : Measure ℝ).map (fun _ => (0 : ℝ)) := Measure.map_congr hae
      _ = Measure.dirac 0 := by rw [Measure.map_const, measure_univ, one_smul]
  · rintro rfl
    exact diracInput_mem_inputFeasible_aux (by norm_num)

/-- A constant input carries no information through any channel. -/
theorem measureMutualInformation_channelJoint_dirac (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (a : ℝ) :
    measureMutualInformation
        (channelJoint κ (diracInput a)) = 0 := by
  have hJ : Measure.dirac a ⊗ₘ κ = (Measure.dirac a).prod (κ a) := by
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.prod_apply hs, lintegral_dirac]
  unfold measureMutualInformation channelJoint
  change klDiv (Measure.dirac a ⊗ₘ κ) (((Measure.dirac a ⊗ₘ κ).map Prod.fst).prod
    ((Measure.dirac a ⊗ₘ κ).map Prod.snd)) / ENNReal.ofReal (Real.log 2) = 0
  rw [hJ, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, measure_univ, one_smul,
    one_smul, klDiv_self, ENNReal.zero_div]

/-- **Zero power.** At budget `0` the capacity of every channel is `0`, attained by the
constant-zero law. -/
theorem powerCapacity_zero (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] : powerCapacity κ 0 = 0 := by
  unfold powerCapacity
  rw [inputFeasible_zero, iSup_singleton]
  exact measureMutualInformation_channelJoint_dirac κ 0

/-- The centered Gaussian of variance `P ≥ 0` is admissible at budget `P`. -/
theorem gaussianInput_mem_inputFeasible {P : ℝ} (hP : 0 ≤ P) :
    gaussianInput P ∈ inputFeasible P := by
  have h := scalarPowerBound_gaussianReal 0 P hP
  have e : gaussianReal 0 P.toNNReal = gaussianReal 0 ⟨P, hP⟩ := by
    congr 1
    ext
    exact Real.coe_toNNReal P hP
  change scalarPowerBound (gaussianReal 0 P.toNNReal) id P
  rw [e]
  simpa using h

/-! ### Random-variable bridge -/

/-- The joint law of `(X, X + Z)`, for an input `X` independent of the noise `Z ~ N(0, N)`, is the
channel joint law of the input law. -/
theorem map_prod_add_eq_compProd_awgnKernel {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) {N : ℝ≥0}
    (hZlaw : μ.map Z = gaussianReal 0 N) :
    μ.map (fun ω => (X ω, X ω + Z ω)) = μ.map X ⊗ₘ awgnKernel N := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hind
  have hg : Measurable fun p : ℝ × ℝ => (p.1, p.1 + p.2) := by fun_prop
  have hmap : μ.map (fun ω => (X ω, X ω + Z ω)) =
      (μ.map fun ω => (X ω, Z ω)).map fun p => (p.1, p.1 + p.2) := by
    rw [Measure.map_map hg (by fun_prop)]
    rfl
  rw [hmap, hprod, hZlaw]
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun y => ?_
  rw [awgnKernel, MetaMathlibExt.noiseKernel_apply,
    Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

/-- The scalar power bound on a measurable input is membership of its law in the feasible set. -/
theorem mem_inputFeasible_map_iff {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (P : ℝ) :
    (⟨μ.map X, inferInstance⟩ : ProbabilityMeasure ℝ) ∈ inputFeasible P ↔
      scalarPowerBound μ X P := by
  change scalarPowerBound (μ.map X) id P ↔ scalarPowerBound μ X P
  unfold scalarPowerBound
  rw [lintegral_map measurable_ofReal_sq hX]
  rfl

/-! ### AWGN capacity value -/

/-- **Scalar AWGN variational capacity** (headline). For `P ≥ 0` and `N > 0`, given the all-law
converse (every admissible input law gives at most `log (1 + P / N) / (2 log 2)` bits) and, when
`P > 0`, Gaussian attainment (the centered Gaussian input of variance `P` gives exactly that
value), the supremum of the mutual information over all admissible input laws is
`ofReal (log (1 + P / N) / (2 log 2))`. At `P = 0` neither hypothesis is used. The noise premise
`N > 0` is part of the statement but unused by the assembly, since it enters only through the
converse (which fails for the noiseless channel, see `awgnCapacity_noiseless`). For the attainment
discharged, see `awgnCapacity_eq_of_converse`; for both, `awgnCapacity_eq_ofReal_log`. -/
theorem awgnCapacity_eq {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (_hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)))
    (hgauss : 0 < P → measureMutualInformation (channelJoint (awgnKernel N)
        (gaussianInput P)) =
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    awgnCapacity P N = ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) := by
  rcases hP.eq_or_lt with h0 | hpos
  · subst h0
    rw [awgnCapacity, powerCapacity_zero]
    simp
  · exact powerCapacity_eq_of_le_of_attains _ hconv (gaussianInput_mem_inputFeasible hP)
      (hgauss hpos)

/-- The canonical realization of an input law `p`: on `ℝ × ℝ` with law `p × N(0, N)`, the
coordinates are independent with laws `p` and `N(0, N)`, and the joint law of
`(X, X + Z)` is the channel joint law of `p`. -/
private theorem canonicalRealization (p : ProbabilityMeasure ℝ) (N : ℝ≥0) :
    IndepFun Prod.fst Prod.snd ((p : Measure ℝ).prod (gaussianReal 0 N)) ∧
      ((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.fst = p ∧
      ((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.snd = gaussianReal 0 N ∧
      (⟨((p : Measure ℝ).prod (gaussianReal 0 N)).map (fun ω => (ω.1, ω.1 + ω.2)),
        inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) = channelJoint (awgnKernel N) p := by
  have hfst : ((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.fst = p := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : ((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.snd = gaussianReal 0 N := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hind : IndepFun Prod.fst Prod.snd ((p : Measure ℝ).prod (gaussianReal 0 N)) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable, hfst, hsnd]
    simp
  refine ⟨hind, hfst, hsnd, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change ((p : Measure ℝ).prod (gaussianReal 0 N)).map (fun ω => (ω.1, ω.1 + ω.2)) =
    (p : Measure ℝ) ⊗ₘ awgnKernel N
  have h := map_prod_add_eq_compProd_awgnKernel measurable_fst measurable_snd hind hsnd
  rw [hfst] at h
  exact h

/-- A bound stated for random variables `(X, X + Z)`, `Z ~ N(0, N)` independent of `X`, holds for
the channel joint law of every admissible input law, read on its canonical realization. -/
private theorem channelJoint_le_of_randomVariables {P : ℝ} {N : ℝ≥0} {v : ℝ≥0∞}
    (hconv : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Z : Ω → ℝ), Measurable X → Measurable Z → IndepFun X Z μ →
      μ.map Z = gaussianReal 0 N → scalarPowerBound μ X P →
      measureMutualInformation
          (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ≤ v)
    {p : ProbabilityMeasure ℝ} (hp : p ∈ inputFeasible P) :
    measureMutualInformation (channelJoint (awgnKernel N) p) ≤ v := by
  obtain ⟨hind, hfst, hsnd, hjoint⟩ := canonicalRealization p N
  have hpow : scalarPowerBound ((p : Measure ℝ).prod (gaussianReal 0 N)) Prod.fst P := by
    have hp' : (⟨((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.fst, inferInstance⟩ :
        ProbabilityMeasure ℝ) ∈ inputFeasible P := by
      have he : (⟨((p : Measure ℝ).prod (gaussianReal 0 N)).map Prod.fst, inferInstance⟩ :
          ProbabilityMeasure ℝ) = p := ProbabilityMeasure.toMeasure_injective hfst
      rw [he]
      exact hp
    exact (mem_inputFeasible_map_iff measurable_fst P).1 hp'
  rw [← hjoint]
  exact hconv (ℝ × ℝ) _ Prod.fst Prod.snd measurable_fst measurable_snd hind hsnd hpow

/-- **Scalar AWGN variational capacity, random-variable interfaces.** The headline with the
converse and the Gaussian attainment stated for random variables `(X, X + Z)`, `Z ~ N(0, N)`
independent of `X`, the form in which the scalar converse and the one-dimensional Gaussian-input
formula are proved. -/
theorem awgnCapacity_eq_of_randomVariables {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (hN : 0 < N)
    (hconv : ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Z : Ω → ℝ), Measurable X → Measurable Z → IndepFun X Z μ →
      μ.map Z = gaussianReal 0 N → scalarPowerBound μ X P →
      measureMutualInformation
          (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ≤
        ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)))
    (hgauss : 0 < P → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Z : Ω → ℝ), Measurable X → Measurable Z → IndepFun X Z μ →
      μ.map X = gaussianReal 0 P.toNNReal → μ.map Z = gaussianReal 0 N →
      measureMutualInformation
          (⟨μ.map (fun ω => (X ω, X ω + Z ω)), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) =
        ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    awgnCapacity P N = ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) := by
  refine awgnCapacity_eq hP hN (fun p hp => channelJoint_le_of_randomVariables hconv hp)
    (fun hpos => ?_)
  obtain ⟨hind, hfst, hsnd, hjoint⟩ :=
    canonicalRealization (gaussianInput P) N
  rw [← hjoint]
  exact hgauss hpos (ℝ × ℝ) _ Prod.fst Prod.snd measurable_fst measurable_snd hind hfst hsnd

/-- **Scalar AWGN converse on input laws.** For noise variance `N > 0`, every input law `p` in the
feasible set at budget `P` gives at most `ofReal (log (1 + P / N) / (2 log 2))` bits through the
scalar AWGN channel: the all-law bound `measureMutualInformation_scalarAWGN_le` of
`MathlibExt.InformationTheory.AWGNConverse`, read on the canonical realization of `p`. -/
theorem measureMutualInformation_channelJoint_le {P : ℝ} {N : ℝ≥0} (hN : 0 < N)
    {p : ProbabilityMeasure ℝ} (hp : p ∈ inputFeasible P) :
    measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) :=
  channelJoint_le_of_randomVariables (fun _ _ _ _ _ _ hX hZ hind hZlaw hpow =>
    AWGNConverse.measureMutualInformation_scalarAWGN_le hX hZ hind (NNReal.coe_pos.mpr hN) hZlaw
      hpow) hp

/-- **Gaussian attainment.** For `P ≥ 0` and `N > 0`, the centered Gaussian input of variance `P`
through the scalar AWGN channel gives exactly `log (1 + P / N) / (2 log 2)` bits: the
one-dimensional instance `measureMutualInformation_gaussianInput_fin_one` of the log-determinant
formula, transported along the scalar coordinates. -/
theorem measureMutualInformation_channelJoint_gaussianInput {P : ℝ} (hP : 0 ≤ P) {N : ℝ≥0}
    (hN : 0 < N) :
    measureMutualInformation (channelJoint (awgnKernel N) (gaussianInput P)) =
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) := by
  obtain ⟨hind, hfst, hsnd, hjoint⟩ := canonicalRealization (gaussianInput P) N
  have hN' : (0 : ℝ) < N := NNReal.coe_pos.mpr hN
  have hlaw := map_prod_scalarCoord_add measurable_fst measurable_snd hind (N : ℝ) hN' hsnd
  have h0 : scalarCoord 0 = 0 :=
    map_zero MathlibExt.Analysis.InnerProductSpace.LineIsometry.lineIsometry
  have he : gaussianReal 0 P.toNNReal = gaussianReal 0 ⟨P, hP⟩ := by
    congr 1
    ext
    exact Real.coe_toNNReal P hP
  have hin : ((gaussianInput P : Measure ℝ).prod (gaussianReal 0 N)).map
      (fun ω => scalarCoord ω.1) = multivariateGaussian 0 (!![P] : Matrix (Fin 1) (Fin 1) ℝ) := by
    have hc : (fun ω : ℝ × ℝ => scalarCoord ω.1) = scalarCoord ∘ Prod.fst := rfl
    rw [hc, ← Measure.map_map measurable_scalarCoord measurable_fst, hfst]
    change (gaussianReal 0 P.toNNReal).map scalarCoord = _
    rw [he, map_scalarCoord_gaussianReal 0 P hP, h0]
  have hpair : (channelJoint (awgnKernel N) (gaussianInput P)).map
        (Prod.map scalarCoord scalarCoord) =
      ⟨multivariateGaussian 0 (!![P] : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin _).measurable
          (multivariateGaussian 0 (!![(N : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ)), inferInstance⟩ := by
    have hj : ((gaussianInput P : Measure ℝ).prod (gaussianReal 0 N)).map
        (fun ω => (ω.1, ω.1 + ω.2)) = (gaussianInput P : Measure ℝ) ⊗ₘ awgnKernel N :=
      congrArg ProbabilityMeasure.toMeasure hjoint
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
    change ((gaussianInput P : Measure ℝ) ⊗ₘ awgnKernel N).map _ = _
    rw [← hj, Measure.map_map (measurable_scalarCoord.prodMap measurable_scalarCoord)
      (by fun_prop), ← hin]
    exact hlaw
  rw [← measureMutualInformation_map_scalarCoordPair, hpair,
    measureMutualInformation_gaussianInput_fin_one 1 P N hP hN', one_pow, one_mul]

/-- **Scalar AWGN variational capacity from the converse.** For `P ≥ 0` and `N > 0`, the all-law
converse alone gives the capacity value: the Gaussian attainment hypothesis of `awgnCapacity_eq`
is discharged by `measureMutualInformation_channelJoint_gaussianInput`. -/
theorem awgnCapacity_eq_of_converse {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    awgnCapacity P N = ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) :=
  awgnCapacity_eq hP hN hconv fun _ => measureMutualInformation_channelJoint_gaussianInput hP hN

/-- **Scalar AWGN variational capacity value.** For `P ≥ 0` and `N > 0`, the supremum of the
mutual information over all admissible input laws is `ofReal (log (1 + P / N) / (2 log 2))` bits,
with no further hypothesis: the converse is `measureMutualInformation_channelJoint_le`, and the
centered Gaussian input of variance `P` attains the value
(`measureMutualInformation_channelJoint_gaussianInput`). -/
theorem awgnCapacity_eq_ofReal_log {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (hN : 0 < N) :
    awgnCapacity P N = ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)) :=
  awgnCapacity_eq_of_converse hP hN fun _ hp => measureMutualInformation_channelJoint_le hN hp

/-- The capacity supremum is attained: under the headline hypotheses some admissible input law
achieves it (the centered Gaussian for `P > 0`, the constant-zero law for `P = 0`). -/
theorem exists_mem_inputFeasible_eq_awgnCapacity {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)))
    (hgauss : 0 < P → measureMutualInformation (channelJoint (awgnKernel N)
        (gaussianInput P)) =
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    ∃ p ∈ inputFeasible P,
      measureMutualInformation (channelJoint (awgnKernel N) p) = awgnCapacity P N := by
  rcases hP.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨diracInput 0, diracInput_mem_inputFeasible_aux (by norm_num), ?_⟩
    rw [measureMutualInformation_channelJoint_dirac, awgnCapacity, powerCapacity_zero]
  · refine ⟨_, gaussianInput_mem_inputFeasible hP, ?_⟩
    rw [hgauss hpos, awgnCapacity_eq hP hN hconv hgauss]

/-- Finiteness: under the all-law converse the capacity is finite. -/
theorem awgnCapacity_ne_top {P : ℝ} {N : ℝ≥0}
    (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    awgnCapacity P N ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup₂_le hconv)

/-- **Real-valued capacity**, after finiteness: under the headline hypotheses
`(awgnCapacity P N).toReal = log (1 + P / N) / (2 log 2)`. -/
theorem awgnCapacity_toReal {P : ℝ} {N : ℝ≥0} (hP : 0 ≤ P) (hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible P, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2)))
    (hgauss : 0 < P → measureMutualInformation (channelJoint (awgnKernel N)
        (gaussianInput P)) =
      ENNReal.ofReal (Real.log (1 + P / N) / (2 * Real.log 2))) :
    (awgnCapacity P N).toReal = Real.log (1 + P / N) / (2 * Real.log 2) := by
  rw [awgnCapacity_eq hP hN hconv hgauss, ENNReal.toReal_ofReal]
  have hPN : 0 ≤ P / N := div_nonneg hP N.2
  exact div_nonneg (Real.log_nonneg (by linarith))
    (mul_nonneg zero_le_two (Real.log_nonneg one_le_two))

/-! ### Validation -/

/-- Validation, `P = 0`: the AWGN capacity at zero power is `0` for every noise variance, with no
converse or attainment hypothesis. -/
theorem awgnCapacity_zero_power (N : ℝ≥0) : awgnCapacity 0 N = 0 := by
  exact powerCapacity_zero _

/-- Validation, `P = N`: at signal-to-noise ratio `1` the capacity is `1 / 2` bit. -/
theorem awgnCapacity_self {N : ℝ≥0} (hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible N, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + (N : ℝ) / N) / (2 * Real.log 2)))
    (hgauss : 0 < (N : ℝ) → measureMutualInformation (channelJoint (awgnKernel N)
        (gaussianInput N)) =
      ENNReal.ofReal (Real.log (1 + (N : ℝ) / N) / (2 * Real.log 2))) :
    awgnCapacity N N = ENNReal.ofReal (1 / 2) := by
  rw [awgnCapacity_eq (P := (N : ℝ)) (NNReal.coe_nonneg N) hN hconv hgauss]
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hN)
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  congr 1
  rw [div_self hN', one_add_one_eq_two]
  field_simp

/-- Validation, admissible laws other than the centered Gaussian: a constant input `c` (a
degenerate law, nonzero mean allowed) is admissible at budget `P` whenever `c² ≤ P`. -/
theorem diracInput_mem_inputFeasible {c P : ℝ} (hc : c ^ 2 ≤ P) :
    diracInput c ∈ inputFeasible P := by
  exact diracInput_mem_inputFeasible_aux hc

/-- Validation, a non-Gaussian admissible law: the antipodal two-point law at `±√P` is
admissible at budget `P ≥ 0`; for `P > 0` it is not Gaussian, so the supremum ranges beyond
Gaussian inputs. -/
theorem antipodalLaw_mem_inputFeasible {P : ℝ} (hP : 0 ≤ P) :
    antipodalLaw (Real.sqrt P) ∈ inputFeasible P := by
  refine ⟨hP, le_of_eq ?_⟩
  change ∫⁻ x, ENNReal.ofReal ((id x) ^ 2) ∂((2 : ℝ≥0∞)⁻¹ •
    (Measure.dirac (Real.sqrt P) + Measure.dirac (-Real.sqrt P))) = ENNReal.ofReal P
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac]
  simp only [id_eq, neg_sq, Real.sq_sqrt hP, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Violated premise, negative budget: at `P = -3N` the capacity is `0` (no admissible law),
while the formula evaluates to `1 / 2` (Lean's `log (-2) = log 2`), so `P ≥ 0` is needed. -/
theorem awgnCapacity_neg_power_ne {N : ℝ≥0} (hN : 0 < N) :
    awgnCapacity (-3 * N) N = 0 ∧
      ENNReal.ofReal (Real.log (1 + (-3 * N : ℝ) / N) / (2 * Real.log 2)) =
        ENNReal.ofReal (1 / 2) := by
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hN)
  have hneg : -3 * (N : ℝ) < 0 := by
    have : (0 : ℝ) < N := NNReal.coe_pos.mpr hN
    linarith
  refine ⟨?_, ?_⟩
  · unfold awgnCapacity powerCapacity
    rw [inputFeasible_eq_empty_of_neg hneg, iSup_emptyset]
    rfl
  · have h2 : 1 + (-3 * N : ℝ) / N = -2 := by
      field_simp
      ring
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
    rw [h2, Real.log_neg_eq_log]
    congr 1
    field_simp

/-- Violated premise, noiseless channel `N = 0`: for `P > 0` the capacity is `⊤`, while the
formula evaluates to `0` (Lean's `P / 0 = 0`), so `N > 0` is needed. -/
theorem awgnCapacity_noiseless {P : ℝ} (hP : 0 < P) :
    awgnCapacity P 0 = ⊤ ∧
      ENNReal.ofReal (Real.log (1 + P / ((0 : ℝ≥0) : ℝ)) / (2 * Real.log 2)) = 0 := by
  refine ⟨?_, by simp⟩
  set p : ProbabilityMeasure ℝ := gaussianInput P with hp_def
  have hpf : p ∈ inputFeasible P := gaussianInput_mem_inputFeasible hP.le
  have hv : P.toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hP
  have hatom : ∀ y : ℝ, (p : Measure ℝ) {y} = 0 := fun y =>
    gaussianReal_absolutelyContinuous 0 hv Real.volume_singleton
  set J : Measure (ℝ × ℝ) := (p : Measure ℝ) ⊗ₘ awgnKernel 0 with hJ_def
  have hker : ∀ x : ℝ, awgnKernel 0 x = Measure.dirac x := by
    intro x
    rw [awgnKernel, MetaMathlibExt.noiseKernel_apply, gaussianReal_zero_var, Measure.map_dirac]
    simp
  have hJD : J (Set.diagonal ℝ) = 1 := by
    rw [hJ_def, Measure.compProd_apply measurableSet_diagonal]
    have : ∀ x : ℝ, awgnKernel 0 x (Prod.mk x ⁻¹' Set.diagonal ℝ) = 1 := by
      intro x
      rw [hker]
      exact Measure.dirac_apply_of_mem (show (x, x) ∈ Set.diagonal ℝ from rfl)
    simp_rw [this, lintegral_const, measure_univ, one_mul]
  have hfst : J.map Prod.fst = (p : Measure ℝ) := Measure.fst_compProd _ _
  have hprodD : ((J.map Prod.fst).prod (J.map Prod.snd)) (Set.diagonal ℝ) = 0 := by
    rw [Measure.prod_apply_symm measurableSet_diagonal, hfst]
    have : ∀ y : ℝ, (p : Measure ℝ) ((fun x => (x, y)) ⁻¹' Set.diagonal ℝ) = 0 := by
      intro y
      have hset : (fun x => (x, y)) ⁻¹' Set.diagonal ℝ = {y} := by
        ext x
        simp [Set.mem_diagonal_iff]
      rw [hset]
      exact hatom y
    simp_rw [this, lintegral_zero]
  have hnac : ¬ J ≪ (J.map Prod.fst).prod (J.map Prod.snd) := by
    intro hac
    have := hac hprodD
    rw [hJD] at this
    exact one_ne_zero this
  have hmi : measureMutualInformation (channelJoint (awgnKernel 0) p) = ⊤ := by
    unfold measureMutualInformation channelJoint
    change klDiv J ((J.map Prod.fst).prod (J.map Prod.snd)) / ENNReal.ofReal (Real.log 2) = ⊤
    rw [klDiv_of_not_ac hnac, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
  exact top_le_iff.mp (hmi ▸ le_powerCapacity (awgnKernel 0) hpf)

end MathlibExt.InformationTheory.AWGNCapacityValue

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.VirtualValuation
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! # Myerson's revenue identity for independent bidders

There are finitely many bidders with independent values: bidder `i`'s value has
a continuous positive density `f i` on `[a i, b i]`. A mechanism is an
allocation rule `p` and a payment rule `x` on value profiles; bidder `i`'s
*interim* allocation `Qᵢ(s) = ∫ pᵢ(t₋ᵢ, s) dF₋ᵢ` and interim payment are the
single-parameter objects of `SingleParameter` (Myerson 1981, (4.1)). For a
Bayesian incentive-compatible mechanism, with seller value `t₀ = 0` and no
revision effects, Myerson's identity (4.12) sums the one-bidder identity
(4.10) of `VirtualValuation` over the bidders:

`∫_T ∑ᵢ xᵢ f = ∫_T ∑ᵢ φᵢ(tᵢ) pᵢ(t) f(t) dt − ∑ᵢ Uᵢ(aᵢ)`,

expected revenue is expected virtual surplus minus the lowest types'
utilities. The Corollary is revenue equivalence: expected revenue is
determined by the allocation rule and the lowest-type utilities.

## References

* R. B. Myerson, "Optimal auction design", *Math. Oper. Res.* 6(1) (1981),
  58--73: (4.1), (4.12) and the Corollary, pp. 63--65.
-/

namespace MathlibExt.GameTheory.MechanismDesign.SingleParameter

open MeasureTheory Set

/-- Bidder `i`'s value law: the density `f i` on `[a i, b i]`. -/
noncomputable def valueLaw {ι : Type*} (f : ι → ℝ → ℝ) (a b : ι → ℝ) (i : ι) : Measure ℝ :=
  (volume.restrict (Icc (a i) (b i))).withDensity fun t => ENNReal.ofReal (f i t)

/-- **Interim allocation** (Myerson 1981, (4.1)): `Qᵢ(s) = ∫ pᵢ(t₋ᵢ, s) dF₋ᵢ`,
written as an integral over the whole profile law, whose `i`-th coordinate is
overwritten by `s`. -/
noncomputable def interimAlloc {ι : Type*} [DecidableEq ι] (μ : Measure (ι → ℝ))
    (p : (ι → ℝ) → ι → ℝ) (i : ι) (s : ℝ) : ℝ :=
  ∫ t, p (Function.update t i s) i ∂μ

/-- **Interim payment**: the expected payment of bidder `i` reporting `s`
when the others report truthfully. -/
noncomputable def interimPayment {ι : Type*} [DecidableEq ι] (μ : Measure (ι → ℝ))
    (x : (ι → ℝ) → ι → ℝ) (i : ι) (s : ℝ) : ℝ :=
  ∫ t, x (Function.update t i s) i ∂μ

/-- A bidder's value law is a probability measure when the density is
continuous, positive, and integrates to `1` on its interval. -/
theorem isProbabilityMeasure_valueLaw {ι : Type*} {f : ι → ℝ → ℝ} {a b : ι → ℝ}
    {i : ι} (hab : a i < b i) (hfc : ContinuousOn (f i) (Icc (a i) (b i)))
    (hfpos : ∀ t ∈ Icc (a i) (b i), 0 < f i t) (hf1 : ∫ t in a i..b i, f i t = 1) :
    IsProbabilityMeasure (valueLaw f a b i) := by
  refine ⟨?_⟩
  unfold valueLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hInt : Integrable (f i) (volume.restrict (Icc (a i) (b i))) :=
    hfc.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (a i) (b i))] (f i) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => (hfpos t ht).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  have hIcc : (∫ t in Icc (a i) (b i), f i t ∂volume) = ∫ t in a i..b i, f i t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  rw [hIcc, hf1, ENNReal.ofReal_one]

/-- Overwriting coordinate `i` of an independent profile with an independent
draw from the `i`-th law preserves the product law. -/
theorem measurePreserving_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi ν).prod (ν i)) (Measure.pi ν) := by
  have hMeas : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = i
    · have heq : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2 j) = Prod.snd := by
        ext p
        simp [Function.update, hj]
      rw [heq]
      exact measurable_snd
    · have heq : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2 j) = fun p => p.1 j := by
        ext p
        simp [Function.update, hj]
      rw [heq]
      exact (measurable_pi_apply j).comp measurable_fst
  refine ⟨hMeas, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hMeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (pi univ s)
      = pi univ (Function.update s i univ) ×ˢ s i := by
    ext p
    simp only [mem_preimage, mem_prod, mem_pi, mem_univ]
    constructor
    · intro h
      refine ⟨fun j _ => ?_, by simpa [Function.update] using h i trivial⟩
      by_cases hj : j = i
      · simp [Function.update, hj]
      · have hj' := h j trivial
        simpa [Function.update, hj] using hj'
    · rintro ⟨h1, h2⟩ j _
      by_cases hj : j = i
      · rw [hj]
        simpa [Function.update] using h2
      · have hj' := h1 j trivial
        simpa [Function.update, hj] using hj'
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hprod : (∏ j, ν j (Function.update s i univ j)) = ∏ j ∈ Finset.univ.erase i, ν j (s j) := by
    rw [← Finset.prod_erase_mul _ _ (a := i) (Finset.mem_univ i)]
    have h1 : Function.update s i univ i = univ := by simp [Function.update]
    rw [h1, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h2 : Function.update s i univ j = s j := by simp [Function.update, hji]
    rw [h2]
  rw [hprod]
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- **Marginalization.** Under independent laws, integrating a profile
function equals first integrating out the other coordinates at a fixed
`i`-th value `s`, then integrating `s` against the `i`-th law. -/
theorem integral_eq_integral_integral_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (i : ι)
    {g : (ι → ℝ) → ℝ} (hg : Integrable g (Measure.pi ν)) :
    ∫ t, g t ∂(Measure.pi ν) =
      ∫ s, (∫ t, g (Function.update t i s) ∂(Measure.pi ν)) ∂(ν i) := by
  have hmp := measurePreserving_update_pi ν i
  have hF : Integrable (fun p : (ι → ℝ) × ℝ => g (Function.update p.1 i p.2))
      ((Measure.pi ν).prod (ν i)) :=
    hmp.integrable_comp_of_integrable hg
  have hfm : AEStronglyMeasurable g
      (((Measure.pi ν).prod (ν i)).map (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)) := by
    rw [hmp.map_eq]
    exact hg.aestronglyMeasurable
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hfm]
  exact integral_prod_symm _ hF

/-- Bridge between a bidder's value law and interval integrals against its density. -/
private theorem integral_valueLaw_eq_interval {ι : Type*} (f : ι → ℝ → ℝ) (a b : ι → ℝ) (i : ι)
    (hab : a i < b i) (hfc : ContinuousOn (f i) (Icc (a i) (b i)))
    (hfpos : ∀ t ∈ Icc (a i) (b i), 0 < f i t) (h : ℝ → ℝ) :
    ∫ s, h s ∂(valueLaw f a b i) = ∫ s in a i..b i, h s * f i s := by
  have hAE : AEMeasurable (fun t => ENNReal.ofReal (f i t))
      (volume.restrict (Icc (a i) (b i))) :=
    (hfc.aemeasurable measurableSet_Icc).ennreal_ofReal
  have htop : ∀ᵐ s ∂(volume.restrict (Icc (a i) (b i))), ENNReal.ofReal (f i s) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  unfold valueLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀ hAE htop]
  have hae : ∀ᵐ s ∂(volume.restrict (Icc (a i) (b i))),
      (ENNReal.ofReal (f i s)).toReal • h s = h s * f i s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [ENNReal.toReal_ofReal (hfpos s hs).le, smul_eq_mul, mul_comm]
  have hIcc : (∫ s in Icc (a i) (b i), h s * f i s ∂volume) = ∫ s in a i..b i, h s * f i s := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  exact (integral_congr_ae hae).trans hIcc

/-- **Myerson's revenue identity (4.12)**, for independent values with
continuous positive densities on bounded intervals, seller value `t₀ = 0` and
no revision effects: for a Bayesian incentive-compatible mechanism `(p, x)`,
expected revenue is expected virtual surplus minus the utilities of the
lowest types. The slice-integrability hypothesis only delimits the mechanisms
counted (interim payments are defined at every legal report); the identity
itself needs just joint integrability `hx`. -/
theorem integral_sum_payment_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hfc : ∀ i, ContinuousOn (f i) (Icc (a i) (b i)))
    (hfpos : ∀ i, ∀ t ∈ Icc (a i) (b i), 0 < f i t) (hf1 : ∀ i, ∫ t in a i..b i, f i t = 1)
    {p x : (ι → ℝ) → ι → ℝ} (hpm : ∀ i, Measurable fun t => p t i)
    (hp : ∀ t i, p t i ∈ Icc (0 : ℝ) 1)
    (hx : ∀ i, Integrable (fun t => x t i) (Measure.pi (valueLaw f a b)))
    (_hxs : ∀ i, ∀ s ∈ Icc (a i) (b i), Integrable (fun t => x (Function.update t i s) i)
      (Measure.pi (valueLaw f a b)))
    (hIC : ∀ i, IsIncentiveCompatibleOn (interimAlloc (Measure.pi (valueLaw f a b)) p i)
      (interimPayment (Measure.pi (valueLaw f a b)) x i) (a i) (b i)) :
    ∫ t, ∑ i, x t i ∂(Measure.pi (valueLaw f a b)) =
      ∫ t, ∑ i, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
          ∂(Measure.pi (valueLaw f a b)) -
        ∑ i, truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
          (interimPayment (Measure.pi (valueLaw f a b)) x i) (a i) := by
  have : ∀ j, IsProbabilityMeasure (valueLaw f a b j) := fun j =>
    isProbabilityMeasure_valueLaw (hab j) (hfc j) (hfpos j) (hf1 j)
  have hsupp : ∀ i, ∀ᵐ s ∂(valueLaw f a b i), s ∈ Icc (a i) (b i) := by
    intro i
    apply ae_iff.mpr
    change (valueLaw f a b i) (Icc (a i) (b i))ᶜ = 0
    have h0 : (volume.restrict (Icc (a i) (b i))) (Icc (a i) (b i))ᶜ = 0 := by
      rw [Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self, measure_empty]
    have hac := withDensity_absolutelyContinuous (volume.restrict (Icc (a i) (b i)))
      (fun t => ENNReal.ofReal (f i t))
    exact hac h0
  have heval : ∀ i, ∀ᵐ t ∂(Measure.pi (valueLaw f a b)), t i ∈ Icc (a i) (b i) := by
    intro i
    have hν := hsupp i
    have hmp := measurePreserving_eval (valueLaw f a b) i
    rw [← hmp.map_eq] at hν
    have hmeas : MeasurableSet {x : ℝ | x ∈ Icc (a i) (b i)} :=
      (measurableSet_Icc : MeasurableSet (Icc (a i) (b i)))
    exact (ae_map_iff hmp.measurable.aemeasurable hmeas).mp hν
  have hφcont : ∀ i, ContinuousOn (fun t => virtualValue (f i) (a i) (b i) (hf1 i) t)
      (Icc (a i) (b i)) := by
    intro i
    have hInt : IntegrableOn (f i) (uIcc (a i) (b i)) volume := by
      rw [uIcc_of_le (hab i).le]
      exact (hfc i).integrableOn_Icc
    have hF : ContinuousOn (fun s => ∫ u in a i..s, f i u) (Icc (a i) (b i)) := by
      have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := f i)
        (a := a i) (b := b i) hInt
      rw [uIcc_of_le (hab i).le] at h
      exact h
    have hnum : ContinuousOn (fun s => 1 - ∫ u in a i..s, f i u) (Icc (a i) (b i)) :=
      continuousOn_const.sub hF
    have hdiv : ContinuousOn ((fun s => 1 - ∫ u in a i..s, f i u) / f i) (Icc (a i) (b i)) :=
      hnum.div (hfc i) (fun s hs => ne_of_gt (hfpos i s hs))
    exact continuousOn_id.sub hdiv
  have hφbdd : ∀ i, ∃ C, ∀ s ∈ Icc (a i) (b i),
      ‖virtualValue (f i) (a i) (b i) (hf1 i) s‖ ≤ C := by
    intro i
    obtain ⟨x, _, hxmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (hab i).le) (hφcont i).norm
    exact ⟨‖virtualValue (f i) (a i) (b i) (hf1 i) x‖, fun s hs => hxmax hs⟩
  have hφae : ∀ i, AEStronglyMeasurable (fun t => virtualValue (f i) (a i) (b i) (hf1 i) t)
      (valueLaw f a b i) := by
    intro i
    have h1 : AEStronglyMeasurable (fun t => virtualValue (f i) (a i) (b i) (hf1 i) t)
        (volume.restrict (Icc (a i) (b i))) :=
      ((hφcont i).aemeasurable measurableSet_Icc).aestronglyMeasurable
    exact AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict (Icc (a i) (b i)))
        (fun t => ENNReal.ofReal (f i t))) h1
  have hpint : ∀ i, Integrable (fun t => p t i) (Measure.pi (valueLaw f a b)) := by
    intro i
    apply Integrable.of_bound ((hpm i).aestronglyMeasurable) 1
    apply ae_of_all
    intro t
    have h := mem_Icc.mp (hp t i)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hgint : ∀ i, Integrable (fun t => virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i)
      (Measure.pi (valueLaw f a b)) := by
    intro i
    obtain ⟨C, hC⟩ := hφbdd i
    have hφeval : AEStronglyMeasurable
        (fun t => virtualValue (f i) (a i) (b i) (hf1 i) (t i))
        (Measure.pi (valueLaw f a b)) :=
      (hφae i).comp_measurePreserving (measurePreserving_eval (valueLaw f a b) i)
    refine Integrable.bdd_mul (hpint i) hφeval (c := C) ?_
    filter_upwards [heval i] with t ht
    exact hC (t i) ht
  have hpay : ∀ i, (∫ t, x t i ∂(Measure.pi (valueLaw f a b))) =
      ∫ s in a i..b i, interimPayment (Measure.pi (valueLaw f a b)) x i s * f i s := by
    intro i
    have hmarg := integral_eq_integral_integral_update (valueLaw f a b) i (hx i)
    have hbridge := integral_valueLaw_eq_interval f a b i (hab i) (hfc i) (hfpos i)
      (interimPayment (Measure.pi (valueLaw f a b)) x i)
    exact hmarg.trans hbridge
  have hvirt : ∀ i, (∫ s in a i..b i, virtualValue (f i) (a i) (b i) (hf1 i) s *
      interimAlloc (Measure.pi (valueLaw f a b)) p i s * f i s) =
      ∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
        ∂(Measure.pi (valueLaw f a b)) := by
    intro i
    have hmarg := integral_eq_integral_integral_update (valueLaw f a b) i (hgint i)
    have hbridge := integral_valueLaw_eq_interval f a b i (hab i) (hfc i) (hfpos i)
      (fun s => virtualValue (f i) (a i) (b i) (hf1 i) s *
        interimAlloc (Measure.pi (valueLaw f a b)) p i s)
    have hinner : ∀ s : ℝ, (∫ t, (fun t => virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i)
          (Function.update t i s) ∂(Measure.pi (valueLaw f a b))) =
        virtualValue (f i) (a i) (b i) (hf1 i) s *
          interimAlloc (Measure.pi (valueLaw f a b)) p i s := by
      intro s
      have hred : ∀ t : ι → ℝ, virtualValue (f i) (a i) (b i) (hf1 i) ((Function.update t i s) i) *
          p (Function.update t i s) i =
          virtualValue (f i) (a i) (b i) (hf1 i) s * p (Function.update t i s) i := by
        intro t
        rw [show (Function.update t i s) i = s by simp [Function.update]]
      have h1 : (∫ t, (fun t => virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i)
            (Function.update t i s) ∂(Measure.pi (valueLaw f a b))) =
          ∫ t, virtualValue (f i) (a i) (b i) (hf1 i) s * p (Function.update t i s) i
            ∂(Measure.pi (valueLaw f a b)) :=
        integral_congr_ae (ae_of_all _ hred)
      have h2 : (∫ t, virtualValue (f i) (a i) (b i) (hf1 i) s * p (Function.update t i s) i
            ∂(Measure.pi (valueLaw f a b))) =
          virtualValue (f i) (a i) (b i) (hf1 i) s *
            ∫ t, p (Function.update t i s) i ∂(Measure.pi (valueLaw f a b)) :=
        integral_const_mul _ _
      exact h1.trans h2
    have hEq : (∫ s, virtualValue (f i) (a i) (b i) (hf1 i) s *
        interimAlloc (Measure.pi (valueLaw f a b)) p i s ∂(valueLaw f a b i)) =
        ∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
          ∂(Measure.pi (valueLaw f a b)) :=
      (integral_congr_ae (ae_of_all _ (fun s => (hinner s).symm))).trans hmarg.symm
    exact hbridge.symm.trans hEq
  have hper : ∀ i, (∫ t, x t i ∂(Measure.pi (valueLaw f a b))) =
      (∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
        ∂(Measure.pi (valueLaw f a b))) -
        truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
          (interimPayment (Measure.pi (valueLaw f a b)) x i) (a i) := by
    intro i
    have hax := integral_payment_mul_density (hab i) (hfc i) (hfpos i) (hf1 i) (hIC i)
    rw [hpay i, hax, hvirt i]
  have hLHS : (∫ t, ∑ i, x t i ∂(Measure.pi (valueLaw f a b))) =
      ∑ i, ∫ t, x t i ∂(Measure.pi (valueLaw f a b)) :=
    integral_finsetSum Finset.univ (fun i _ => hx i)
  have hRHS : (∫ t, ∑ i, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
      ∂(Measure.pi (valueLaw f a b))) =
      ∑ i, ∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
        ∂(Measure.pi (valueLaw f a b)) :=
    integral_finsetSum Finset.univ (fun i _ => hgint i)
  rw [hLHS, hRHS]
  calc (∑ i, ∫ t, x t i ∂(Measure.pi (valueLaw f a b)))
      = ∑ i, ((∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
          ∂(Measure.pi (valueLaw f a b))) -
        truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
          (interimPayment (Measure.pi (valueLaw f a b)) x i) (a i)) :=
        Finset.sum_congr rfl (fun i _ => hper i)
    _ = (∑ i, ∫ t, virtualValue (f i) (a i) (b i) (hf1 i) (t i) * p t i
          ∂(Measure.pi (valueLaw f a b))) -
        ∑ i, truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
          (interimPayment (Measure.pi (valueLaw f a b)) x i) (a i) :=
        Finset.sum_sub_distrib _ _

/-- **Revenue equivalence** (Myerson 1981, Corollary): two Bayesian
incentive-compatible mechanisms with the same allocation rule and the same
utilities of the lowest types raise the same expected revenue. -/
theorem integral_sum_payment_eq_of_truthfulUtility_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hfc : ∀ i, ContinuousOn (f i) (Icc (a i) (b i)))
    (hfpos : ∀ i, ∀ t ∈ Icc (a i) (b i), 0 < f i t) (hf1 : ∀ i, ∫ t in a i..b i, f i t = 1)
    {p x₁ x₂ : (ι → ℝ) → ι → ℝ} (hpm : ∀ i, Measurable fun t => p t i)
    (hp : ∀ t i, p t i ∈ Icc (0 : ℝ) 1)
    (hx₁ : ∀ i, Integrable (fun t => x₁ t i) (Measure.pi (valueLaw f a b)))
    (hx₂ : ∀ i, Integrable (fun t => x₂ t i) (Measure.pi (valueLaw f a b)))
    (hxs₁ : ∀ i, ∀ s ∈ Icc (a i) (b i), Integrable (fun t => x₁ (Function.update t i s) i)
      (Measure.pi (valueLaw f a b)))
    (hxs₂ : ∀ i, ∀ s ∈ Icc (a i) (b i), Integrable (fun t => x₂ (Function.update t i s) i)
      (Measure.pi (valueLaw f a b)))
    (hIC₁ : ∀ i, IsIncentiveCompatibleOn (interimAlloc (Measure.pi (valueLaw f a b)) p i)
      (interimPayment (Measure.pi (valueLaw f a b)) x₁ i) (a i) (b i))
    (hIC₂ : ∀ i, IsIncentiveCompatibleOn (interimAlloc (Measure.pi (valueLaw f a b)) p i)
      (interimPayment (Measure.pi (valueLaw f a b)) x₂ i) (a i) (b i))
    (hU : ∀ i, truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
        (interimPayment (Measure.pi (valueLaw f a b)) x₁ i) (a i) =
      truthfulUtility (interimAlloc (Measure.pi (valueLaw f a b)) p i)
        (interimPayment (Measure.pi (valueLaw f a b)) x₂ i) (a i)) :
    ∫ t, ∑ i, x₁ t i ∂(Measure.pi (valueLaw f a b)) =
      ∫ t, ∑ i, x₂ t i ∂(Measure.pi (valueLaw f a b)) := by
  have h1 := integral_sum_payment_eq f a b hab hfc hfpos hf1 hpm hp hx₁ hxs₁ hIC₁
  have h2 := integral_sum_payment_eq f a b hab hfc hfpos hf1 hpm hp hx₂ hxs₂ hIC₂
  rw [h1, h2]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hU i)

end MathlibExt.GameTheory.MechanismDesign.SingleParameter

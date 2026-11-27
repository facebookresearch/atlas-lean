/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Stationary random functions and Scottish Book Problem 180 -/

@[expose] public section

namespace MathlibExt.Probability.ScottishBook180Wanted

/-- **Stationary random functions (Slutsky–Khinchin).** Let $\mu$ be a measure on a measurable
space $\Omega$, and let $v$ assign to each real $t$ a function $v_t : \Omega \to \mathbb{R}$.
Then $v$ is stationary if there are a real number $c$ and a function $R : \mathbb{R} \to \mathbb{R}$
such that for all real $t$ and $h$, $\int v_t \, d\mu = 0$, $\int v_t^2 \, d\mu = c$ and
$\int v_t \, v_{t+h} \, d\mu = R(h)$.

The integrals are Bochner integrals, which are $0$ for non-integrable functions, so integrability
of $v_t$, $v_t^2$ and $v_t v_{t+h}$ is not required. -/
def IsStationary (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (v : ℝ → Ω → ℝ) : Prop :=
  ∃ (c : ℝ) (R : ℝ → ℝ),
    (∀ t : ℝ, ∫ ω, v t ω ∂μ = 0) ∧
    (∀ t : ℝ, ∫ ω, (v t ω) ^ 2 ∂μ = c) ∧
    ∀ t h : ℝ, ∫ ω, v t ω * v (t + h) ω ∂μ = R h

/-- **Scottish Book Problem 180 (Kampé de Fériet's claim).** The claim that for every probability
space $(\Omega, \mu)$ that carries a measurable random variable $U : \Omega \to \mathbb{R}$
uniformly distributed on $[0, 1]$, and every stationary random function $v$ on $\Omega$ (in the
sense of Slutsky and Khinchin) such that each $v_t : \Omega \to \mathbb{R}$ is measurable, there
exist a measurable random variable $A : \Omega \to \mathbb{R}$ uniformly distributed on $[0, 1]$
and a map $\varphi : \mathbb{R} \to \Omega$ such that $A(\varphi(\alpha)) = \alpha$ for every
$\alpha \in [0, 1]$, and such that for all real $t_1 \ne t_2$ the functions
$\alpha \mapsto v_{t_1}(\varphi(\alpha))$ and $\alpha \mapsto v_{t_2}(\varphi(\alpha))$ are
independent with respect to Lebesgue measure on $[0, 1]$.

Here a variable is uniformly distributed on $[0, 1]$ when its law is Lebesgue measure restricted
to $[0, 1]$. The equation $A(\varphi(\alpha)) = \alpha$ is condition (1) of the problem and the
independence, in the sense of Steinhaus, is condition (2). The existence of $U$ is an added
hypothesis; it rules out refutations that only exploit a space carrying no uniform variable. -/
def ScottishBookProblem180Claim : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    (∃ U : Ω → ℝ, Measurable U ∧
      MeasureTheory.Measure.map U μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
    ∀ v : ℝ → Ω → ℝ, (∀ t, Measurable (v t)) → IsStationary Ω μ v →
    ∃ (A : Ω → ℝ) (φ : ℝ → Ω), Measurable A ∧
      MeasureTheory.Measure.map A μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      (∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 → A (φ α) = α) ∧
      ∀ t₁ t₂ : ℝ, t₁ ≠ t₂ →
        ProbabilityTheory.IndepFun (fun α => v t₁ (φ α))
          (fun α => v t₂ (φ α))
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/--
**Scottish Book Problem 180 fails.** The claim of Scottish Book Problem 180 is false: there are a
probability space $(\Omega, \mu)$ carrying a measurable random variable uniformly distributed on
$[0, 1]$ and a stationary random function $v$ on $\Omega$ with every $v_t$ measurable, such that
no measurable random variable $A : \Omega \to \mathbb{R}$ uniformly distributed on $[0, 1]$ and no
map $\varphi : \mathbb{R} \to \Omega$ satisfy both $A(\varphi(\alpha)) = \alpha$ for every
$\alpha \in [0, 1]$ and, for all real $t_1 \ne t_2$, the independence of
$\alpha \mapsto v_{t_1}(\varphi(\alpha))$ and $\alpha \mapsto v_{t_2}(\varphi(\alpha))$ with
respect to Lebesgue measure on $[0, 1]$.

A counterexample is $\Omega = \mathbb{R}$ with $\mu$ Lebesgue measure restricted to $[0, 1]$, the
identity as uniform variable, and $v_t(\omega) = \omega - 1/2$ for every $t$, which is stationary
with $c = R(h) = 1/12$. If $A$ and $\varphi$ existed, $\varphi$ would be injective on $[0, 1]$,
while both functions in the independence condition equal $f(\alpha) = \varphi(\alpha) - 1/2$. A
function independent of itself is almost everywhere constant, and an injective function on
$[0, 1]$ is not. No non-degeneracy hypothesis is added, since the source asks for none.

Source: J. Kampe de Feriet, Problem 180 of the Scottish Book,
typescript PDF pp. 82-83, printed pp. 79-80; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem scottishBook180_refuted : ¬ ScottishBookProblem180Claim := by
  intro hclaim
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let _ : MeasureTheory.IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num⟩
  have hmean : ∫ ω, (ω - 1 / 2 : ℝ) ∂μ = 0 := by
    dsimp only [μ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x), integral_id]
    norm_num
  have hsecond : ∫ ω, (ω - 1 / 2 : ℝ) ^ 2 ∂μ = 1 / 12 := by
    dsimp only [μ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2), integral_pow]
    norm_num
  -- Use the same real-line example in the universe of the claim.
  let e : ULift ℝ ≃ᵐ ℝ := MeasurableEquiv.ulift
  let ν := μ.map e.symm
  let v : ℝ → ULift ℝ → ℝ := fun _ ω ↦ e ω - 1 / 2
  have hv : ∀ t, Measurable (v t) := fun _ ↦ e.measurable.sub_const _
  have hstat : IsStationary (ULift ℝ) ν v := by
    refine ⟨1 / 12, fun _ ↦ 1 / 12, ?_, ?_, ?_⟩
    · intro t
      rw [MeasureTheory.integral_map_equiv e.symm]
      simpa [v] using hmean
    · intro t
      rw [MeasureTheory.integral_map_equiv e.symm]
      simpa [v] using hsecond
    · intro t h
      rw [MeasureTheory.integral_map_equiv e.symm]
      simpa [v, ← pow_two] using hsecond
  obtain ⟨A, φ, hA, _, hleft, hindep⟩ :=
    hclaim (ULift ℝ) ν (by dsimp only [ν]; infer_instance)
      ⟨e, e.measurable, e.map_map_symm⟩ v hv hstat
  -- Apply the measurable map that adds back the centering constant and then applies A.
  -- On [0, 1] this recovers the identity without requiring φ to be measurable.
  let g : ℝ → ℝ := fun x ↦ A (e.symm (x + 1 / 2))
  have hg : Measurable g := hA.comp (e.symm.measurable.comp (measurable_id.add_const _))
  have heq : (fun α ↦ g (e (φ α) - 1 / 2)) =ᵐ[μ] id := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Icc]
      with α hα
    simpa only [g, sub_add_cancel, MeasurableEquiv.symm_apply_apply, id_eq] using hleft α hα
  have hid : ProbabilityTheory.IndepFun (id : ℝ → ℝ) id μ :=
    ((hindep 0 1 zero_ne_one).comp hg hg).congr heq heq
  have hhalf : μ (Set.Iic (1 / 2 : ℝ)) = ENNReal.ofReal (1 / 2) := by
    have hinter : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · exact fun h ↦ ⟨h.2.1, h.1⟩
      · exact fun h ↦ ⟨h.2, h.1, h.2.trans (by norm_num)⟩
    dsimp only [μ]
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic, hinter, Real.volume_Icc, sub_zero]
  have hs : MeasurableSet (Set.Iic (1 / 2 : ℝ)) := measurableSet_Iic
  have h := hid.measure_inter_preimage_eq_mul _ _ hs hs
  rw [Set.preimage_id, Set.inter_self, hhalf] at h
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  have hreal := congrArg ENNReal.toReal h
  norm_num at hreal

end MathlibExt.Probability.ScottishBook180Wanted

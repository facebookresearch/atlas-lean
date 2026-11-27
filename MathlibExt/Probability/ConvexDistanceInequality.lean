/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexDistanceFinite
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Talagrand's convex-distance inequality

For a probability measure `μ` on a measurable space `Ω`, the product probability `P = μ^{⊗N}` on
`Ω^N` and a measurable set `A ⊆ Ω^N`, Talagrand's Theorem 4.1.1 states
`∫ exp(f_c(A, x)² / 4) dP(x) ≤ 1 / P(A)` (`lintegral_exp_convexDistance_sq_le`), hence
`P(f_c(A, ·) ≥ t) ≤ exp(-t² / 4) / P(A)` for `t ≥ 0` (`measure_le_convexDistance_le`), where
`f_c` is the convex distance (`MathlibExt.Probability.ConvexDistance.convexDistance`). The bound
does not depend on `N` or on `μ`; when `P(A) = 0` its right-hand side is `∞`. The inequality is
the source of the concentration inequality for convex Lipschitz functions of independent bounded
variables stated in `MathlibExt.Probability.TalagrandConcentrationWanted`.

## Measurability

The function `f_c(A, ·)` need not be measurable when `A` is measurable, and the source reads the
integral as an upper integral and the probability as an outer probability (its Section 2.1). Both
statements follow from `exists_measurable_ge_exp_convexDistance_sq`, the upper-integral form: a
measurable `G ≥ exp(f_c(A, ·)² / 4)` with `(∫ G dP) · P(A) ≤ 1`. The first statement uses Mathlib's
lower Lebesgue integral `∫⁻`, which is at most `∫ G dP`; the second applies Markov's inequality to
`G`, which bounds the outer measure `P` gives to the possibly non-measurable superlevel set.

## Proof outline

Talagrand's induction on `N`, the argument proved for a finite `Ω` in
`MathlibExt.Probability.ConvexDistanceFinite`, is run for a measurable family of sets
`A_θ = {x | (θ, x) ∈ A}`, `A ⊆ Θ × Ω^N` measurable, so that the majorant `G(θ, x)` can be chosen
jointly measurable.

* Splitting `z ∈ Ω^{N+1}` as `(ω, x)`, the sections `A_θ(ω) = {x | (θ, (ω, x)) ∈ A}` form a
  measurable family indexed by `Θ × Ω`. The projection of `A_θ` used by the source need not be
  measurable; it is replaced by its measurable part `B_θ = {x | μ{ω | (θ, (ω, x)) ∈ A} > 0}`. By
  Fubini's theorem, `P(A_θ) ≤ P(B_θ)` and `P(A_θ(ω)) ≤ P(B_θ)` for `μ`-almost every `ω`.
* The geometric step (the source's (4.1.7), `convexDistance_cons_sq_le`), with `B_θ` in place of
  the projection, gives the majorant `G(θ, (ω, x)) = e^{(1-λ)²/4} G₁((θ, ω), x)^λ G₂(θ, x)^{1-λ}`,
  where `G₁` and `G₂` come from the induction hypothesis for the two families and `λ` is the
  exponent of the source's proof of Lemma 4.1.3 for `r = P(A_θ(ω)) / P(B_θ)`, a measurable
  function of `(θ, ω)`; when `P(B_θ) = 0`, `G(θ, ·) = ∞` and `P(A_θ) = 0`.
* Hölder's inequality, the induction hypothesis and Lemma 4.1.3
  (`exists_exp_le_two_sub_mul_rpow`) bound the integral in `x` by `(2 - r) / P(B_θ)` for almost
  every `ω`; integrating in `ω` and `u (2 - u) ≤ 1` conclude.

## Implementation notes

The two theorems of Theorem 4.1.1 keep the full names they had in the former wanted module, so
their namespace still reads `ConvexDistanceWanted`. The upper-integral form and the helper lemmas
are in the namespace `MathlibExt.Probability.ConvexDistance` of the definitions.

## References

* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Section 2.1 (measurability), Theorem 4.1.1, inequalities
  (4.1.2) and (4.1.3), Lemma 4.1.3 and their proofs.
-/

@[expose] public section

namespace MathlibExt.Probability.ConvexDistance

open MeasureTheory Metric Real
open scoped ENNReal

universe u

/-! ### An explicit exponent in the numerical lemma -/

-- The exponent of the source's proof of Lemma 4.1.3: `1 + 2 log r` for `e^{-1/2} ≤ r ≤ 1` and
-- `0` for `0 ≤ r < e^{-1/2}`; it is clipped to `[0, 1]` so that it lies there for every `r`.
private noncomputable def expo (r : ℝ) : ℝ :=
  if 0 < r then min 1 (max 0 (1 + 2 * log r)) else 0

private theorem expo_nonneg (r : ℝ) : 0 ≤ expo r := by
  unfold expo; split_ifs
  · exact le_min zero_le_one (le_max_left _ _)
  · exact le_rfl

private theorem expo_le_one (r : ℝ) : expo r ≤ 1 := by
  unfold expo; split_ifs
  · exact min_le_left _ _
  · exact zero_le_one

private theorem pos_of_expo_ne_zero {r : ℝ} (h : expo r ≠ 0) : 0 < r := by
  by_contra hr
  exact h (by simp [expo, hr])

private theorem measurable_expo : Measurable expo :=
  Measurable.ite measurableSet_Ioi
    (measurable_const.min (measurable_const.max
      (measurable_const.add (measurable_const.mul Real.measurable_log))))
    measurable_const

-- Talagrand's numerical lemma with the exponent `expo r`: the exponent minimises the convex
-- function `λ ↦ (1 - λ)² / 4 - λ log r` on `[0, 1]`, so it is at least as good as the one given
-- by `exists_exp_le_two_sub_mul_rpow`.
private theorem exp_le_two_sub_mul_rpow_expo {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    exp ((1 - expo r) ^ 2 / 4) ≤ (2 - r) * r ^ expo r := by
  obtain ⟨l, hl0, hl1, hlr, h⟩ := exists_exp_le_two_sub_mul_rpow hr0 hr1
  rcases hr0.lt_or_eq with hr | rfl
  · set L := log r with hLdef
    have hL : L ≤ 0 := log_nonpos hr0 hr1
    have hm : expo r = max 0 (1 + 2 * L) := by
      simp only [expo, hr, ↓reduceIte]
      exact min_eq_right (max_le zero_le_one (by linarith))
    have hq : (1 - expo r) ^ 2 / 4 - L * expo r ≤ (1 - l) ^ 2 / 4 - L * l := by
      rw [hm]
      rcases le_total 0 (1 + 2 * L) with h0 | h0
      · rw [max_eq_right h0]
        nlinarith [sq_nonneg (l - (1 + 2 * L))]
      · rw [max_eq_left h0]
        nlinarith [mul_nonneg hl0 (by linarith : 0 ≤ -(1 + 2 * L))]
    rw [rpow_def_of_pos hr] at h ⊢
    rw [← hLdef] at h ⊢
    have hpos : 0 < exp (L * l) := exp_pos _
    calc exp ((1 - expo r) ^ 2 / 4)
        = exp ((1 - expo r) ^ 2 / 4 - L * expo r) * exp (L * expo r) := by
          rw [← exp_add]; ring_nf
      _ ≤ exp ((1 - l) ^ 2 / 4 - L * l) * exp (L * expo r) := by gcongr
      _ = exp ((1 - l) ^ 2 / 4) * exp (L * expo r) / exp (L * l) := by
          rw [exp_sub]; ring
      _ ≤ (2 - r) * exp (L * l) * exp (L * expo r) / exp (L * l) := by gcongr
      _ = (2 - r) * exp (L * expo r) := by field_simp
  · have hl : l = 0 := hlr.resolve_right (lt_irrefl 0)
    subst hl
    simpa [expo] using h

/-! ### The first coordinate of a product measure -/

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem cons_eq_piFinSuccAbove_symm (N : ℕ) :
    (fun p : Ω × (Fin N → Ω) => (Fin.cons p.1 p.2 : Fin (N + 1) → Ω)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Ω) 0).symm := by
  funext p
  exact (Fin.insertNth_zero' p.1 p.2).symm

private theorem measurableEmbedding_cons (N : ℕ) :
    MeasurableEmbedding (fun p : Ω × (Fin N → Ω) => (Fin.cons p.1 p.2 : Fin (N + 1) → Ω)) := by
  rw [cons_eq_piFinSuccAbove_symm]
  exact MeasurableEquiv.measurableEmbedding _

private theorem measurePreserving_cons (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (fun p : Ω × (Fin N → Ω) => (Fin.cons p.1 p.2 : Fin (N + 1) → Ω))
      (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) := by
  rw [cons_eq_piFinSuccAbove_symm]
  exact MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0)

private theorem lintegral_pi_succ (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    {f : (Fin (N + 1) → Ω) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂Measure.pi (fun _ => μ) =
      ∫⁻ ω, ∫⁻ x, f (Fin.cons ω x) ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [← (measurePreserving_cons μ N).lintegral_comp_emb (measurableEmbedding_cons N) f]
  exact lintegral_prod _ (hf.comp (measurableEmbedding_cons N).measurable).aemeasurable

private theorem pi_succ_apply (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    (s : Set (Fin (N + 1) → Ω)) :
    Measure.pi (fun _ => μ) s = (μ.prod (Measure.pi fun _ => μ))
      ((fun p : Ω × (Fin N → Ω) => (Fin.cons p.1 p.2 : Fin (N + 1) → Ω)) ⁻¹' s) :=
  ((measurePreserving_cons μ N).measure_preimage_emb (measurableEmbedding_cons N) s).symm

/-! ### Talagrand's induction for a measurable family of sets -/

-- Talagrand's induction on `N`, for a measurable family `θ ↦ A_θ = {x | (θ, x) ∈ A}` of subsets
-- of `Ω^N`: a jointly measurable `G` dominates `exp (f_c(A_θ, ·)² / 4)` and has
-- `(∫ G(θ, ·) dP) · P(A_θ) ≤ 1` for every `θ`. The parameter carries the first coordinates
-- removed so far, so that the exponent chosen at each step is a measurable function.
private theorem exists_measurable_ge_param (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    ∀ (Θ : Type u) [MeasurableSpace Θ] (A : Set (Θ × (Fin N → Ω))), MeasurableSet A →
      ∃ G : Θ × (Fin N → Ω) → ℝ≥0∞, Measurable G ∧
        (∀ θ x, ENNReal.ofReal (exp (convexDistance (Prod.mk θ ⁻¹' A) x ^ 2 / 4)) ≤ G (θ, x)) ∧
        ∀ θ, (∫⁻ x, G (θ, x) ∂Measure.pi (fun _ => μ)) *
          Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) ≤ 1 := by
  induction N with
  | zero =>
    intro Θ _ A hA
    classical
    refine ⟨fun p => if p ∈ A then 1 else ⊤, Measurable.ite hA measurable_const measurable_const,
      fun θ x => ?_, fun θ => ?_⟩
    · by_cases hx : (θ, x) ∈ A
      · simp only [hx, ↓reduceIte]
        rw [convexDistance_eq_zero_of_mem (show x ∈ Prod.mk θ ⁻¹' A from hx)]
        simp
      · simp [hx]
    · by_cases h : (θ, (Fin.elim0 : Fin 0 → Ω)) ∈ A
      · have hall : ∀ x : Fin 0 → Ω, (θ, x) ∈ A := fun x => by
          rwa [Subsingleton.elim x Fin.elim0]
        simp only [hall, ↓reduceIte, lintegral_const, measure_univ, mul_one, one_mul]
        exact prob_le_one
      · have hempty : Prod.mk θ ⁻¹' A = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          rwa [Subsingleton.elim x Fin.elim0]
        simp [hempty]
  | succ N ih =>
    intro Θ _ A hA
    classical
    set P : Measure (Fin N → Ω) := Measure.pi fun _ => μ
    have hcons := (measurableEmbedding_cons (Ω := Ω) N).measurable
    -- the sections of `A` at the first coordinate, as a family indexed by `Θ × Ω`
    set A₁ : Set ((Θ × Ω) × (Fin N → Ω)) :=
      {p | (p.1.1, (Fin.cons p.1.2 p.2 : Fin (N + 1) → Ω)) ∈ A}
    have hA₁ : MeasurableSet A₁ :=
      hA.preimage (measurable_fst.fst.prodMk
        (hcons.comp (measurable_fst.snd.prodMk measurable_snd)))
    -- for each `(θ, x)`, the first coordinates `ω` with `(θ, (ω, x)) ∈ A`
    set S : Set ((Θ × (Fin N → Ω)) × Ω) :=
      {q | (q.1.1, (Fin.cons q.2 q.1.2 : Fin (N + 1) → Ω)) ∈ A}
    have hS : MeasurableSet S :=
      hA.preimage (measurable_fst.fst.prodMk
        (hcons.comp (measurable_snd.prodMk measurable_fst.snd)))
    -- a measurable part of the projection of `A_θ` that carries almost all of each section
    set B : Set (Θ × (Fin N → Ω)) := {p | 0 < μ (Prod.mk p ⁻¹' S)}
    have hB : MeasurableSet B :=
      measurableSet_lt measurable_const (measurable_measure_prodMk_left hS)
    obtain ⟨G₁, hG₁m, hG₁le, hG₁int⟩ := ih (Θ × Ω) A₁ hA₁
    obtain ⟨G₂, hG₂m, hG₂le, hG₂int⟩ := ih Θ B hB
    set α : Θ × Ω → ℝ≥0∞ := fun q => P (Prod.mk q ⁻¹' A₁)
    set β : Θ → ℝ≥0∞ := fun θ => P (Prod.mk θ ⁻¹' B)
    have hα : Measurable α := measurable_measure_prodMk_left hA₁
    have hβ : Measurable β := measurable_measure_prodMk_left hB
    set l : Θ × Ω → ℝ := fun q => expo ((α q).toReal / (β q.1).toReal)
    have hl : Measurable l := measurable_expo.comp
      ((ENNReal.measurable_toReal.comp hα).div
        (ENNReal.measurable_toReal.comp (hβ.comp measurable_fst)))
    set G : Θ × (Fin (N + 1) → Ω) → ℝ≥0∞ := fun p => if β p.1 = 0 then ⊤ else
      ENNReal.ofReal (exp ((1 - l (p.1, p.2 0)) ^ 2 / 4)) *
        (G₁ ((p.1, p.2 0), Fin.tail p.2) ^ l (p.1, p.2 0) *
          G₂ (p.1, Fin.tail p.2) ^ (1 - l (p.1, p.2 0))) with hGdef
    have hGm : Measurable G := by
      have h0 : Measurable fun p : Θ × (Fin (N + 1) → Ω) => (p.1, p.2 0) :=
        measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
      have ht : Measurable fun p : Θ × (Fin (N + 1) → Ω) => Fin.tail p.2 :=
        (measurable_pi_iff.mpr fun i : Fin N => measurable_pi_apply (Fin.succ i)).comp
          measurable_snd
      have hlp := hl.comp h0
      refine Measurable.ite ((hβ.comp measurable_fst) (measurableSet_singleton 0))
        measurable_const ?_
      exact (ENNReal.measurable_ofReal.comp (measurable_exp.comp
        (((measurable_const.sub hlp).pow_const 2).div_const 4))).mul
        (((hG₁m.comp (h0.prodMk ht)).pow hlp).mul
          ((hG₂m.comp (measurable_fst.prodMk ht)).pow (measurable_const.sub hlp)))
    -- the part of the projection used in the geometric step
    have hBsub : ∀ θ, Prod.mk θ ⁻¹' B ⊆ projection (Prod.mk θ ⁻¹' A) := by
      intro θ y hy
      obtain ⟨ω', hω'⟩ := nonempty_of_measure_ne_zero (ne_of_gt (show 0 < μ
        (Prod.mk (θ, y) ⁻¹' S) from hy))
      exact ⟨ω', hω'⟩
    refine ⟨G, hGm, fun θ z => ?_, fun θ => ?_⟩
    · -- `G` dominates `exp (f_c² / 4)`
      obtain ⟨ω, x, rfl⟩ : ∃ ω x, z = (Fin.cons ω x : Fin (N + 1) → Ω) :=
        ⟨z 0, Fin.tail z, (Fin.cons_self_tail z).symm⟩
      by_cases hβ0 : β θ = 0
      · simp [hGdef, hβ0]
      simp only [hGdef, hβ0, ↓reduceIte, Fin.cons_zero, Fin.tail_cons]
      set e := l (θ, ω)
      have he0 : 0 ≤ e := expo_nonneg _
      have he1 : e ≤ 1 := expo_le_one _
      have hBne : (Prod.mk θ ⁻¹' B).Nonempty := nonempty_of_measure_ne_zero hβ0
      have hsec : e = 0 ∨ (sectionAt (Prod.mk θ ⁻¹' A) ω).Nonempty := by
        by_cases he : e = 0
        · exact Or.inl he
        · right
          have hr := pos_of_expo_ne_zero he
          have hα0 : α (θ, ω) ≠ 0 := by
            intro h0
            rw [h0, ENNReal.toReal_zero, zero_div] at hr
            exact lt_irrefl 0 hr
          exact nonempty_of_measure_ne_zero hα0
      have hg := convexDistance_cons_sq_le (Prod.mk θ ⁻¹' A) ω x he0 he1
        (hBne.mono (hBsub θ)) hsec
      have hmono : convexDistance (projection (Prod.mk θ ⁻¹' A)) x ≤
          convexDistance (Prod.mk θ ⁻¹' B) x :=
        convexDistance_le_convexDistance_of_subset (hBsub θ) hBne x
      have hsq := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (convexDistance_nonneg _ _) hmono 2) (by linarith : (0 : ℝ) ≤ 1 - e)
      have hreal : exp (convexDistance (Prod.mk θ ⁻¹' A) (Fin.cons ω x) ^ 2 / 4) ≤
          exp ((1 - e) ^ 2 / 4) *
            (exp (convexDistance (sectionAt (Prod.mk θ ⁻¹' A) ω) x ^ 2 / 4) ^ e *
              exp (convexDistance (Prod.mk θ ⁻¹' B) x ^ 2 / 4) ^ (1 - e)) := by
        rw [← exp_mul, ← exp_mul, ← exp_add, ← exp_add]
        exact exp_le_exp.mpr (by nlinarith [hg, hsq])
      calc ENNReal.ofReal (exp (convexDistance (Prod.mk θ ⁻¹' A) (Fin.cons ω x) ^ 2 / 4))
          ≤ ENNReal.ofReal (exp ((1 - e) ^ 2 / 4) *
            (exp (convexDistance (sectionAt (Prod.mk θ ⁻¹' A) ω) x ^ 2 / 4) ^ e *
              exp (convexDistance (Prod.mk θ ⁻¹' B) x ^ 2 / 4) ^ (1 - e))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
            (ENNReal.ofReal (exp (convexDistance (sectionAt (Prod.mk θ ⁻¹' A) ω) x ^ 2 / 4)) ^ e *
              ENNReal.ofReal (exp (convexDistance (Prod.mk θ ⁻¹' B) x ^ 2 / 4)) ^ (1 - e)) := by
            rw [ENNReal.ofReal_mul (exp_pos _).le,
              ENNReal.ofReal_mul (rpow_nonneg (exp_pos _).le _),
              ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le he0,
              ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by linarith)]
        _ ≤ ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
            (G₁ ((θ, ω), x) ^ e * G₂ (θ, x) ^ (1 - e)) := by
            gcongr
            · exact hG₁le (θ, ω) x
            · exact hG₂le θ x
    · -- the integral bound
      have hAθ : MeasurableSet ((fun p : Ω × (Fin N → Ω) => (Fin.cons p.1 p.2 : Fin (N + 1) → Ω))
          ⁻¹' (Prod.mk θ ⁻¹' A)) := (hA.preimage measurable_prodMk_left).preimage hcons
      have hQ : Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) = ∫⁻ ω, α (θ, ω) ∂μ := by
        rw [pi_succ_apply, Measure.prod_apply hAθ]
        rfl
      have hQB : Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) ≤ β θ := by
        rw [pi_succ_apply, Measure.prod_apply_symm hAθ]
        calc ∫⁻ x, μ ((fun ω => (ω, x)) ⁻¹' ((fun p : Ω × (Fin N → Ω) =>
              (Fin.cons p.1 p.2 : Fin (N + 1) → Ω)) ⁻¹' (Prod.mk θ ⁻¹' A))) ∂P
            ≤ ∫⁻ x, (Prod.mk θ ⁻¹' B).indicator 1 x ∂P := lintegral_mono fun x => ?_
          _ = β θ := lintegral_indicator_one (hB.preimage measurable_prodMk_left)
        by_cases hx : (θ, x) ∈ B
        · rw [Set.indicator_of_mem (show x ∈ Prod.mk θ ⁻¹' B from hx)]
          exact prob_le_one
        · rw [Set.indicator_of_notMem (show x ∉ Prod.mk θ ⁻¹' B from hx)]
          exact not_lt.mp hx
      by_cases hβ0 : β θ = 0
      · have hzero : Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) = 0 :=
          le_antisymm (hQB.trans hβ0.le) zero_le
        rw [hzero, mul_zero]
        exact zero_le_one
      -- almost every section has measure at most `β θ`
      have hae : ∀ᵐ ω ∂μ, α (θ, ω) ≤ β θ := by
        set D : Set (Ω × (Fin N → Ω)) :=
          {p | (θ, (Fin.cons p.1 p.2 : Fin (N + 1) → Ω)) ∈ A ∧ (θ, p.2) ∉ B} with hDdef
        have hD : MeasurableSet D :=
          (hA.preimage (measurable_const.prodMk hcons)).inter
            (hB.preimage (measurable_const.prodMk measurable_snd)).compl
        have h0 : (μ.prod P) D = 0 := by
          rw [Measure.prod_apply_symm hD]
          refine le_antisymm ?_ zero_le
          calc ∫⁻ x, μ ((fun ω => (ω, x)) ⁻¹' D) ∂P ≤ ∫⁻ _, 0 ∂P := lintegral_mono fun x => ?_
            _ = 0 := lintegral_zero
          by_cases hx : (θ, x) ∈ B
          · have : (fun ω => (ω, x)) ⁻¹' D = ∅ := by
              ext ω
              simp [hDdef, hx]
            rw [this, measure_empty]
          · calc μ ((fun ω => (ω, x)) ⁻¹' D) ≤ μ (Prod.mk (θ, x) ⁻¹' S) :=
                  measure_mono fun ω hω => hω.1
              _ ≤ 0 := not_lt.mp hx
        filter_upwards [(Measure.measure_prod_null hD).mp h0] with ω hω
        exact measure_mono_ae (ae_subset.mpr hω)
      have hβtop : β θ ≠ ⊤ := measure_ne_top _ _
      set b := (β θ).toReal
      have hb : 0 < b := ENNReal.toReal_pos hβ0 hβtop
      have hβb : β θ = ENNReal.ofReal b := (ENNReal.ofReal_toReal hβtop).symm
      -- the inner integrals, by Hölder's inequality and the induction hypothesis
      have hinner : ∀ᵐ ω ∂μ, ∫⁻ x, G (θ, Fin.cons ω x) ∂P ≤
          ENNReal.ofReal (2 / b - (α (θ, ω)).toReal / b ^ 2) := by
        filter_upwards [hae] with ω hω
        set a := (α (θ, ω)).toReal
        have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
        have hab : a ≤ b := ENNReal.toReal_mono hβtop hω
        set r := a / b with hrdef
        have hr0 : 0 ≤ r := div_nonneg ha0 hb.le
        have hr1 : r ≤ 1 := (div_le_one hb).mpr hab
        set e := expo r
        have he0 : 0 ≤ e := expo_nonneg r
        have he1 : e ≤ 1 := expo_le_one r
        have hnum : exp ((1 - e) ^ 2 / 4) ≤ (2 - r) * r ^ e := exp_le_two_sub_mul_rpow_expo hr0 hr1
        have hGeq : ∀ x, G (θ, Fin.cons ω x) = ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
            (G₁ ((θ, ω), x) ^ e * G₂ (θ, x) ^ (1 - e)) := fun x => by
          simp only [hGdef, hβ0, ↓reduceIte, Fin.cons_zero, Fin.tail_cons]
          rfl
        simp_rw [hGeq]
        have hm₁ : Measurable fun x => G₁ ((θ, ω), x) := hG₁m.comp measurable_prodMk_left
        have hm₂ : Measurable fun x => G₂ (θ, x) := hG₂m.comp measurable_prodMk_left
        have hm : Measurable fun x => G₁ ((θ, ω), x) ^ e * G₂ (θ, x) ^ (1 - e) :=
          (hm₁.pow_const e).mul (hm₂.pow_const _)
        rw [lintegral_const_mul _ hm]
        have hH := ENNReal.lintegral_mul_norm_pow_le (μ := P) hm₁.aemeasurable hm₂.aemeasurable
          he0 (by linarith : 0 ≤ 1 - e) (by ring)
        have h1 : ∫⁻ x, G₁ ((θ, ω), x) ∂P ≤ (α (θ, ω))⁻¹ :=
          ENNReal.le_inv_iff_mul_le.mpr (hG₁int (θ, ω))
        have h2 : ∫⁻ x, G₂ (θ, x) ∂P ≤ (β θ)⁻¹ := ENNReal.le_inv_iff_mul_le.mpr (hG₂int θ)
        have hr2 : 2 / b - a / b ^ 2 = (2 - r) * b⁻¹ := by
          rw [hrdef]; field_simp
        calc ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
              ∫⁻ x, G₁ ((θ, ω), x) ^ e * G₂ (θ, x) ^ (1 - e) ∂P
            ≤ ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
              ((∫⁻ x, G₁ ((θ, ω), x) ∂P) ^ e * (∫⁻ x, G₂ (θ, x) ∂P) ^ (1 - e)) := by
              gcongr
          _ ≤ ENNReal.ofReal (exp ((1 - e) ^ 2 / 4)) *
              ((α (θ, ω))⁻¹ ^ e * (β θ)⁻¹ ^ (1 - e)) := by
              gcongr
          _ ≤ ENNReal.ofReal (2 / b - a / b ^ 2) := by
              rw [hr2]
              rcases eq_or_ne e 0 with he | he
              · rw [he] at hnum ⊢
                rw [rpow_zero, mul_one, sub_zero] at hnum
                rw [ENNReal.rpow_zero, sub_zero, ENNReal.rpow_one, one_mul, hβb,
                  ← ENNReal.ofReal_inv_of_pos hb, ← ENNReal.ofReal_mul (exp_pos _).le]
                exact ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hb.le))
              · have hr : 0 < r := pos_of_expo_ne_zero he
                have ha : 0 < a := (div_pos_iff_of_pos_right hb).mp hr
                have hαa : α (θ, ω) = ENNReal.ofReal a :=
                  (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
                rw [hαa, hβb, ← ENNReal.ofReal_inv_of_pos ha, ← ENNReal.ofReal_inv_of_pos hb,
                  ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr ha.le) he0,
                  ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hb.le) (by linarith),
                  ← ENNReal.ofReal_mul (rpow_nonneg (inv_nonneg.mpr ha.le) _),
                  ← ENNReal.ofReal_mul (exp_pos _).le]
                refine ENNReal.ofReal_le_ofReal ?_
                have hrpos : 0 < r ^ e := rpow_pos_of_pos hr e
                have key : a⁻¹ ^ e * b⁻¹ ^ (1 - e) = (r ^ e)⁻¹ * b⁻¹ := by
                  rw [inv_rpow ha.le, inv_rpow hb.le, rpow_sub hb, rpow_one, hrdef,
                    div_rpow ha0 hb.le]
                  have : 0 < b ^ e := rpow_pos_of_pos hb e
                  have : 0 < a ^ e := rpow_pos_of_pos ha e
                  field_simp
                rw [key]
                calc exp ((1 - e) ^ 2 / 4) * ((r ^ e)⁻¹ * b⁻¹)
                    = exp ((1 - e) ^ 2 / 4) / r ^ e * b⁻¹ := by ring
                  _ ≤ (2 - r) * b⁻¹ := by
                    gcongr
                    rw [div_le_iff₀ hrpos]
                    exact hnum
      -- the outer integral
      have hGθ : Measurable fun z => G (θ, z) := hGm.comp measurable_prodMk_left
      have hαθ : Measurable fun ω => α (θ, ω) := hα.comp measurable_prodMk_left
      set c := ENNReal.ofReal (b ^ 2)⁻¹ with hcdef
      have hrw : ∀ ω, ENNReal.ofReal (2 / b - (α (θ, ω)).toReal / b ^ 2) =
          ENNReal.ofReal (2 / b) - α (θ, ω) * c := by
        intro ω
        rw [ENNReal.ofReal_sub _ (div_nonneg ENNReal.toReal_nonneg (by positivity)),
          div_eq_mul_inv (α (θ, ω)).toReal, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
      have hQc : ∫⁻ ω, α (θ, ω) * c ∂μ = Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) * c := by
        rw [lintegral_mul_const _ hαθ, hQ]
      have hle : ∀ᵐ ω ∂μ, α (θ, ω) * c ≤ ENNReal.ofReal (2 / b) := by
        filter_upwards [hae] with ω hω
        calc α (θ, ω) * c ≤ β θ * c := by gcongr
          _ = ENNReal.ofReal (b * (b ^ 2)⁻¹) := by
            rw [hβb, hcdef, ENNReal.ofReal_mul hb.le]
          _ ≤ ENNReal.ofReal (2 / b) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [show b * (b ^ 2)⁻¹ = 1 / b by field_simp]
            gcongr
            norm_num
      set q := (Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A)).toReal
      have hQq : Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) = ENNReal.ofReal q :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      have hqb : q ≤ b := ENNReal.toReal_mono hβtop hQB
      have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
      calc (∫⁻ z, G (θ, z) ∂Measure.pi (fun _ => μ)) * Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A)
          = (∫⁻ ω, ∫⁻ x, G (θ, Fin.cons ω x) ∂P ∂μ) *
              Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) := by rw [lintegral_pi_succ μ N hGθ]
        _ ≤ (∫⁻ ω, ENNReal.ofReal (2 / b - (α (θ, ω)).toReal / b ^ 2) ∂μ) *
              Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) := by
            gcongr ?_ * _
            exact lintegral_mono_ae hinner
        _ = (ENNReal.ofReal (2 / b) - Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) * c) *
              Measure.pi (fun _ => μ) (Prod.mk θ ⁻¹' A) := by
            have hfin : ∫⁻ ω, α (θ, ω) * c ∂μ ≠ ⊤ := by
              rw [hQc]
              exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
            simp_rw [hrw]
            rw [lintegral_sub (hαθ.mul_const _) hfin hle, lintegral_const, measure_univ,
              mul_one, hQc]
        _ ≤ 1 := by
            rw [hQq, hcdef, ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_sub _ (by positivity),
              ← ENNReal.ofReal_mul' hq0, ENNReal.ofReal_le_one]
            have hid : (2 / b - q * (b ^ 2)⁻¹) * q = 1 - (1 - q / b) ^ 2 := by
              field_simp
              ring
            rw [hid]
            nlinarith [sq_nonneg (1 - q / b)]

/-- **Talagrand's convex-distance inequality, with a measurable majorant** (Talagrand,
*Concentration of measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81
(1995), Theorem 4.1.1, (4.1.2), read with the upper integral of its Section 2.1). Let `μ` be a
probability measure on a measurable space `Ω`, `N` a natural number, `P = μ^{⊗N}` the product
probability on `Ω^N` and `A ⊆ Ω^N` a measurable set. There is a measurable
`G : Ω^N → [0, ∞]` with `exp(f_c(A, x)² / 4) ≤ G(x)` for every `x` and
`(∫ G dP) · P(A) ≤ 1`. -/
theorem exists_measurable_ge_exp_convexDistance_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) {A : Set (Fin N → Ω)} (hA : MeasurableSet A) :
    ∃ G : (Fin N → Ω) → ℝ≥0∞, Measurable G ∧
      (∀ x, ENNReal.ofReal (exp (convexDistance A x ^ 2 / 4)) ≤ G x) ∧
      (∫⁻ x, G x ∂Measure.pi (fun _ => μ)) * Measure.pi (fun _ => μ) A ≤ 1 := by
  obtain ⟨G, hGm, hGle, hGint⟩ := exists_measurable_ge_param μ N PUnit.{u + 1}
    (Prod.snd ⁻¹' A) (hA.preimage measurable_snd)
  exact ⟨fun x => G (PUnit.unit, x), hGm.comp measurable_prodMk_left,
    fun x => hGle PUnit.unit x, hGint PUnit.unit⟩

end MathlibExt.Probability.ConvexDistance

namespace MathlibExt.Probability.ConvexDistanceWanted

open MeasureTheory MathlibExt.Probability.ConvexDistance
open scoped ENNReal

/-- **Talagrand's convex-distance inequality** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem 4.1.1,
(4.1.2)). For every probability measure `μ` on `Ω`, every `N` and every measurable
`A ⊆ Ω^N`, with `P = μ^{⊗N}`: `∫ exp(f_c(A, x)² / 4) dP(x) ≤ 1 / P(A)`. -/
theorem lintegral_exp_convexDistance_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) {A : Set (Fin N → Ω)}
    (hA : MeasurableSet A) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance A x ^ 2 / 4)) ∂Measure.pi (fun _ => μ) ≤
      (Measure.pi (fun _ => μ) A)⁻¹ := by
  obtain ⟨G, -, hGle, hGint⟩ := exists_measurable_ge_exp_convexDistance_sq μ N hA
  exact (lintegral_mono hGle).trans (ENNReal.le_inv_iff_mul_le.mpr hGint)

/-- **Tail form of the convex-distance inequality** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem 4.1.1,
(4.1.3)). Under the hypotheses of `lintegral_exp_convexDistance_sq_le`, for every `t ≥ 0`,
`P(f_c(A, ·) ≥ t) ≤ exp(-t² / 4) / P(A)`. -/
theorem measure_le_convexDistance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) {A : Set (Fin N → Ω)}
    (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun _ => μ) {x | t ≤ convexDistance A x} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / 4)) * (Measure.pi (fun _ => μ) A)⁻¹ := by
  obtain ⟨G, hGm, hGle, hGint⟩ := exists_measurable_ge_exp_convexDistance_sq μ N hA
  set c := ENNReal.ofReal (Real.exp (t ^ 2 / 4)) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hsub : {x | t ≤ convexDistance A x} ⊆ {x | c ≤ G x} := fun x hx =>
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
      have := pow_le_pow_left₀ ht hx 2
      linarith))).trans (hGle x)
  calc Measure.pi (fun _ => μ) {x | t ≤ convexDistance A x}
      ≤ Measure.pi (fun _ => μ) {x | c ≤ G x} := measure_mono hsub
    _ ≤ (∫⁻ x, G x ∂Measure.pi (fun _ => μ)) / c :=
        meas_ge_le_lintegral_div hGm.aemeasurable hc0 ENNReal.ofReal_ne_top
    _ ≤ (Measure.pi (fun _ => μ) A)⁻¹ / c := by
        gcongr
        exact ENNReal.le_inv_iff_mul_le.mpr hGint
    _ = ENNReal.ofReal (Real.exp (-t ^ 2 / 4)) * (Measure.pi (fun _ => μ) A)⁻¹ := by
        rw [div_eq_mul_inv, mul_comm, hcdef, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
          ← Real.exp_neg, neg_div]

end MathlibExt.Probability.ConvexDistanceWanted

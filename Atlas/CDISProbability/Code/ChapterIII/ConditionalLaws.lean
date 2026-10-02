/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic

/-!
# CDIS Probabilités III: conditional laws and conditional expectation

The course's conditional law `P_{Y | X = x}` is Mathlib's kernel `condDistrib Y X P`, unique
`P_X`-almost everywhere (id 53, see `Code/Bridges/ChapterIII.lean`).

* id 54: sweeping formula `P_Y(B) = ∫ P_{Y|X=x}(B) P_X(dx)`, and its discrete form
  `P(Y ∈ B) = Σ_x P(Y ∈ B | X = x) P(X = x)`.
* id 55: `X` and `Y` are independent iff `P_{Y|X=x}` does not depend on `x` (a.e.), and then
  it equals `P_Y`.
* id 56, 57: `E(Y | X = x) = ∫ y P_{Y|X=x}(dy)` and `E(g(X,Y) | X = x) = ∫ g(x,y) P_{Y|X=x}(dy)`;
  `E(Y | X) = ψ(X)` agrees almost surely with Mathlib's conditional expectation.
* id 59: conditional transfer: given `X = x`, `g(X, Y)` has the law of `g(x, Y)` under
  `P_{Y|X=x}`, so `E(g(X,Y) | X = x) = ∫ g(x,y) P_{Y|X=x}(dy)`; with independence the kernel
  is `P_Y`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}

section Sweeping

/-- CDIS P.III, id 54 (sweeping formula): `P_Y(B) = ∫ P_{Y|X=x}(B) P_X(dx)`. -/
theorem map_apply_eq_lintegral_condDistrib (hX : Measurable X) (hY : Measurable Y) {B : Set ℝ}
    (hB : MeasurableSet B) : P.map Y B = ∫⁻ x, condDistrib Y X P x B ∂(P.map X) := by
  have h := compProd_map_condDistrib (μ := P) hX.aemeasurable hY.aemeasurable
  have hYB : P.map Y B = P.map (fun ω ↦ (X ω, Y ω)) (univ ×ˢ B) := by
    rw [Measure.map_apply hY hB, Measure.map_apply (hX.prodMk hY) (MeasurableSet.univ.prod hB)]
    congr 1
    ext ω
    simp
  rw [hYB, ← h, Measure.compProd_apply_prod MeasurableSet.univ hB, Measure.restrict_univ]

/-- CDIS P.III, id 54 (discrete case): if `X` takes values in a countable set `I`, then
`P(Y ∈ B) = Σ_{x ∈ I} P(Y ∈ B | X = x) P(X = x)`. -/
theorem measure_preimage_eq_tsum_cond {I : Set ℝ} (hI : I.Countable) (hXI : ∀ ω, X ω ∈ I)
    (hX : Measurable X) (hY : Measurable Y) {B : Set ℝ} (hB : MeasurableSet B) :
    P (Y ⁻¹' B) = ∑' x : I, P[Y ⁻¹' B | X ⁻¹' {(x : ℝ)}] * P (X ⁻¹' {(x : ℝ)}) := by
  have : Countable I := hI.to_subtype
  have hunion : Y ⁻¹' B = ⋃ x : I, X ⁻¹' {(x : ℝ)} ∩ Y ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, Subtype.exists,
      exists_prop]
    exact ⟨fun h ↦ ⟨X ω, hXI ω, rfl, h⟩, fun ⟨_, _, _, h⟩ ↦ h⟩
  conv_lhs => rw [hunion]
  rw [measure_iUnion]
  · exact tsum_congr fun x ↦ (cond_mul_eq_inter (hX (measurableSet_singleton _)) _ P).symm
  · intro i j hij
    refine Disjoint.mono inter_subset_left inter_subset_left ?_
    refine Disjoint.preimage _ ?_
    simpa [Subtype.coe_inj] using hij
  · exact fun x ↦ (hX (measurableSet_singleton _)).inter (hY hB)

end Sweeping

section Independence

/-- CDIS P.III, id 55 (1): `X` and `Y` are independent iff `P_{Y|X=x} = P_Y` for `P_X`-almost
every `x`. -/
theorem indepFun_iff_condDistrib_ae_eq_const (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y P ↔ condDistrib Y X P =ᵐ[P.map X] Kernel.const ℝ (P.map Y) := by
  have : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 ‹_›
  rw [condDistrib_ae_eq_iff_measure_eq_compProd hX.aemeasurable hY.aemeasurable,
    Measure.compProd_const, indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

/-- CDIS P.III, id 55 (1), in the course's form: if `P_{Y|X=x}` does not depend on `x`
(almost everywhere), the common value is `P_Y` and `X`, `Y` are independent. -/
theorem indepFun_of_condDistrib_ae_eq_const (hX : Measurable X) (hY : Measurable Y)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : condDistrib Y X P =ᵐ[P.map X] Kernel.const ℝ ν) : ν = P.map Y ∧ IndepFun X Y P := by
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 ‹_›
  have hmap := (condDistrib_ae_eq_iff_measure_eq_compProd hX.aemeasurable hY.aemeasurable _).1 h
  rw [Measure.compProd_const] at hmap
  have hν : ν = P.map Y := by
    have := congrArg (Measure.map Prod.snd) hmap
    rw [Measure.map_snd_prod, measure_univ, one_smul,
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        (hX.prodMk hY).aemeasurable] at this
    exact this.symm
  refine ⟨hν, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hmap, hν]

end Independence

section ConditionalExpectation

/-- CDIS P.III, id 56: `E(Y | X = x) = ∫ y P_{Y|X=x}(dy)`. -/
noncomputable def condExpGiven (Y X : Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P] (x : ℝ) : ℝ :=
  ∫ y, y ∂(condDistrib Y X P x)

/-- CDIS P.III, id 57: `E(g(X,Y) | X = x) = ∫ g(x, y) P_{Y|X=x}(dy)`. -/
noncomputable def condExpGivenFun (g : ℝ × ℝ → ℝ) (Y X : Ω → ℝ) (P : Measure Ω)
    [IsFiniteMeasure P] (x : ℝ) : ℝ :=
  ∫ y, g (x, y) ∂(condDistrib Y X P x)

/-- CDIS P.III, id 56: the random variable `E(Y | X) = ψ(X)`, with `ψ(x) = E(Y | X = x)`, is
almost surely Mathlib's conditional expectation of `Y` given `σ(X)`. -/
theorem condExp_ae_eq_condExpGiven (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable Y P) :
    P[Y | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω ↦ condExpGiven Y X P (X ω) := by
  have h := condExp_ae_eq_integral_condDistrib (f := id) hX hY.aemeasurable
    stronglyMeasurable_id hint
  simp only [id] at h
  exact h

/-- CDIS P.III, id 57: `E(g(X,Y) | X) = ψ(X)` with `ψ(x) = E(g(X,Y) | X = x)`, almost surely. -/
theorem condExp_ae_eq_condExpGivenFun (hX : Measurable X) (hY : Measurable Y)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hint : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    P[fun ω ↦ g (X ω, Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω ↦ condExpGivenFun g Y X P (X ω) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY.aemeasurable hg.stronglyMeasurable hint

end ConditionalExpectation

section Transfer

/-- The law of `g(x, Y')` when `Y'` has law `κ x`: `x ↦ (κ x).map (g (x, ·))`, as a kernel. -/
noncomputable def transferKernel (κ : Kernel ℝ ℝ) (g : ℝ × ℝ → ℝ) : Kernel ℝ ℝ :=
  (Kernel.deterministic id measurable_id ×ₖ κ).map g

lemma transferKernel_apply (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) (x : ℝ) : transferKernel κ g x = (κ x).map fun y ↦ g (x, y) := by
  rw [transferKernel, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
  rfl

lemma isMarkovKernel_transferKernel (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) : IsMarkovKernel (transferKernel κ g) :=
  Kernel.IsMarkovKernel.map _ hg

/-- `(μ ⊗ κ).map (x, g(x, y)) = μ ⊗ (transferKernel κ g)`. -/
lemma map_compProd_eq_compProd_transferKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    (μ ⊗ₘ κ).map (fun p ↦ (p.1, g p)) = μ ⊗ₘ transferKernel κ g := by
  have := isMarkovKernel_transferKernel κ hg
  have hm : Measurable fun p : ℝ × ℝ ↦ (p.1, g p) := measurable_fst.prodMk hg
  ext S hS
  rw [Measure.map_apply hm hS, Measure.compProd_apply (hm hS), Measure.compProd_apply hS]
  refine lintegral_congr fun x ↦ ?_
  rw [transferKernel_apply κ hg, Measure.map_apply (by fun_prop) (measurable_prodMk_left hS)]
  rfl

/-- CDIS P.III, id 59 (conditional transfer), kernel form: the conditional law of `g(X, Y)`
given `X = x` is the law of `g(x, Y')` with `Y' ~ P_{Y|X=x}`, for `P_X`-almost every `x`. -/
theorem condDistrib_comp_prod_ae_eq (hX : Measurable X) (hY : Measurable Y) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) :
    condDistrib (fun ω ↦ g (X ω, Y ω)) X P =ᵐ[P.map X] transferKernel (condDistrib Y X P) g := by
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 ‹_›
  have := isMarkovKernel_transferKernel (condDistrib Y X P) hg
  refine condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable
    (hg.comp (hX.prodMk hY)).aemeasurable ?_
  rw [← map_compProd_eq_compProd_transferKernel _ _ hg,
    compProd_map_condDistrib hX.aemeasurable hY.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hX.prodMk hY).aemeasurable]
  rfl

/-- CDIS P.III, id 59 (conditional transfer): for `P_X`-almost every `x`,
`E(g(X,Y) | X = x) = ∫ g(x, y) P_{Y|X=x}(dy)`, where the left side is computed from the
conditional law of the random variable `g(X, Y)` itself. -/
theorem condExpGiven_comp_prod_ae_eq (hX : Measurable X) (hY : Measurable Y) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) :
    ∀ᵐ x ∂(P.map X), condExpGiven (fun ω ↦ g (X ω, Y ω)) X P x = condExpGivenFun g Y X P x := by
  filter_upwards [condDistrib_comp_prod_ae_eq (P := P) hX hY hg] with x hx
  rw [condExpGiven, hx, transferKernel_apply _ hg,
    integral_map (φ := fun y ↦ g (x, y)) (f := fun y : ℝ ↦ y)
      (hg.comp measurable_prodMk_left).aemeasurable aestronglyMeasurable_id]
  rfl

/-- CDIS P.III, id 59, independent case: `E(g(X,Y) | X = x) = ∫ g(x, y) P_Y(dy)`. -/
theorem condExpGiven_comp_prod_ae_eq_of_indepFun (hX : Measurable X) (hY : Measurable Y)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hXY : IndepFun X Y P) :
    ∀ᵐ x ∂(P.map X), condExpGiven (fun ω ↦ g (X ω, Y ω)) X P x = ∫ y, g (x, y) ∂(P.map Y) := by
  filter_upwards [condExpGiven_comp_prod_ae_eq (P := P) hX hY hg,
    (indepFun_iff_condDistrib_ae_eq_const hX hY).1 hXY] with x hx hconst
  rw [hx, condExpGivenFun, hconst, Kernel.const_apply]

end Transfer

end CDIS

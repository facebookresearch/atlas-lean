/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left.lean`
and
`P2M/Sol/S_MeasureTheory_Measure_exists_eq_prod_of_forall_map_add_left.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Disjointed

/-!
# Translation-invariant measures on a product are product measures

A measure on `G × Y`, where `G` is a locally compact second-countable
additive group and `Y` is only a measurable space, that is invariant under
translation in the `G`-coordinate is the product of Haar measure on `G`
with a sigma-finite measure on `Y`, provided the measure is finite on
every strip `K ×ˢ B n` with `K` compact, for a countable measurable cover
`B` of `Y`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure.InvariantProd

private noncomputable def slice {G : Type*} [MeasurableSpace G] {Y : Type*}
    [MeasurableSpace Y] (ρ : Measure (G × Y)) (B : Set Y) : Measure G :=
  (ρ.restrict (univ ×ˢ B)).map Prod.fst

private theorem slice_apply {G : Type*} [MeasurableSpace G] {Y : Type*}
    [MeasurableSpace Y] (ρ : Measure (G × Y)) (B : Set Y) {E : Set G}
    (hE : MeasurableSet E) : slice ρ B E = ρ (E ×ˢ B) := by
  rw [slice, map_apply measurable_fst hE, restrict_apply (measurable_fst hE)]
  congr 1
  ext ⟨x, y⟩
  simp

section Helpers

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {Y : Type*} [MeasurableSpace Y]

private theorem slice_isAddLeftInvariant (ρ : Measure (G × Y)) (B : Set Y)
    (hB : MeasurableSet B)
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ) :
    (slice ρ B).IsAddLeftInvariant := by
  refine ⟨fun a => ?_⟩
  ext E hE
  rw [map_apply (measurable_const_add a) hE, slice_apply ρ B hE,
    slice_apply ρ B (measurable_const_add a hE)]
  have hT : Measurable (fun p : G × Y => (a + p.1, p.2)) :=
    (measurable_const_add a).prodMap measurable_id
  have h := congrArg (fun ν : Measure (G × Y) => ν (E ×ˢ B)) (hinv a)
  beta_reduce at h
  rw [map_apply hT (hE.prod hB)] at h
  convert h using 2
  first | rfl | (ext ⟨x, y⟩; simp [Set.mem_prod, Set.mem_preimage])

private theorem slice_isFiniteMeasureOnCompacts (ρ : Measure (G × Y)) (B : Set Y)
    (hBfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ B) < ⊤) :
    IsFiniteMeasureOnCompacts (slice ρ B) := by
  refine ⟨fun K hK => ?_⟩
  refine (measure_mono subset_closure).trans_lt ?_
  rw [slice_apply ρ B isClosed_closure.measurableSet]
  exact hBfin (closure K) hK.closure

private theorem slice_eq_smul (μ : Measure G) [μ.IsAddHaarMeasure] (ρ : Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (K₀ : Set G) (hK₀m : MeasurableSet K₀) (hK₀pos : μ K₀ ≠ 0) (hK₀top : μ K₀ ≠ ⊤)
    (B : Set Y) (hB : MeasurableSet B)
    (hBfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ B) < ⊤) :
    slice ρ B = (ρ (K₀ ×ˢ B) / μ K₀) • μ := by
  haveI := slice_isAddLeftInvariant ρ B hB hinv
  haveI := slice_isFiniteMeasureOnCompacts ρ B hBfin
  have huniq := isAddLeftInvariant_eq_smul (slice ρ B) μ
  set c := (slice ρ B).addHaarScalarFactor μ with hc
  have huniq' : slice ρ B = (c : ℝ≥0∞) • μ := by
    rw [huniq]
    exact Measure.ext fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  have hval : ρ (K₀ ×ˢ B) = c * μ K₀ := by
    have := congrArg (fun ν : Measure G => ν K₀) huniq'
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rwa [slice_apply ρ B hK₀m] at this
  have hc' : (c : ℝ≥0∞) = ρ (K₀ ×ˢ B) / μ K₀ := by
    rw [hval, ENNReal.mul_div_cancel_right hK₀pos hK₀top]
  rw [huniq', hc']

private theorem rect_of_admissible (μ : Measure G) [μ.IsAddHaarMeasure]
    (ρ : Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (K₀ : Set G) (hK₀m : MeasurableSet K₀) (hK₀pos : μ K₀ ≠ 0) (hK₀top : μ K₀ ≠ ⊤)
    (B : Set Y) (hB : MeasurableSet B)
    (hBfin : ∀ K : Set G, IsCompact K → ρ (K ×ˢ B) < ⊤)
    (E : Set G) (hE : MeasurableSet E) :
    ρ (E ×ˢ B) = μ E * (ρ (K₀ ×ˢ B) / μ K₀) := by
  have h := congrArg (fun ν : Measure G => ν E)
    (slice_eq_smul μ ρ hinv K₀ hK₀m hK₀pos hK₀top B hB hBfin)
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [slice_apply ρ B hE] at h
  rw [h, mul_comm]

end Helpers

end MeasureTheory.Measure.InvariantProd

/-- A measure on `G × Y` invariant under translation in the `G`-coordinate,
and finite on every compact strip over a member of a countable measurable
cover of `Y`, is Haar measure times a sigma-finite measure on `Y`. -/
public theorem MeasureTheory.Measure.exists_eq_prod_of_forall_map_add_left
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    {Y : Type*} [MeasurableSpace Y] (ρ : MeasureTheory.Measure (G × Y))
    (hinv : ∀ a : G, ρ.map (fun p : G × Y => (a + p.1, p.2)) = ρ)
    (hfin : ∃ B : ℕ → Set Y, (∀ n, MeasurableSet (B n)) ∧ (⋃ n, B n) = Set.univ ∧
      ∀ n (K : Set G), IsCompact K → ρ (K ×ˢ B n) < ⊤) :
    ∃ σ : MeasureTheory.Measure Y, MeasureTheory.SigmaFinite σ ∧ ρ = μ.prod σ := by
  classical
  obtain ⟨B, hBm, hBU, hBfin⟩ := hfin
  obtain ⟨K₀, hK₀n, hK₀, hK₀cl⟩ := exists_mem_nhds_isCompact_isClosed (0 : G)
  have hK₀m : MeasurableSet K₀ := hK₀cl.measurableSet
  have hK₀pos : μ K₀ ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK₀n).ne'
  have hK₀top : μ K₀ ≠ ⊤ := hK₀.measure_lt_top.ne
  set σ : Measure Y := (μ K₀)⁻¹ • (ρ.restrict (K₀ ×ˢ univ)).map Prod.snd with hσ
  have hσapp : ∀ C : Set Y, MeasurableSet C → σ C = ρ (K₀ ×ˢ C) / μ K₀ := by
    intro C hC
    rw [hσ, Measure.smul_apply, map_apply measurable_snd hC,
      restrict_apply (measurable_snd hC), smul_eq_mul, ENNReal.div_eq_inv_mul]
    congr 2
    ext ⟨x, y⟩
    simp [and_comm]
  set D : ℕ → Set Y := disjointed B with hD
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hBm
  have hDsub : ∀ n, D n ⊆ B n := fun n => disjointed_le B n
  have hDU : (⋃ n, D n) = univ := by rw [hD, iUnion_disjointed, hBU]
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed B
  have hrect : ∀ (E : Set G) (C : Set Y), MeasurableSet E → MeasurableSet C →
      ρ (E ×ˢ C) = μ E * σ C := by
    intro E C hE hC
    have hCn : ∀ n, ρ (E ×ˢ (C ∩ D n)) = μ E * σ (C ∩ D n) := by
      intro n
      have hfinn : ∀ K : Set G, IsCompact K → ρ (K ×ˢ (C ∩ D n)) < ⊤ := fun K hK =>
        lt_of_le_of_lt
          (measure_mono (Set.prod_mono le_rfl (inter_subset_right.trans (hDsub n))))
          (hBfin n K hK)
      rw [MeasureTheory.Measure.InvariantProd.rect_of_admissible μ ρ hinv K₀ hK₀m
        hK₀pos hK₀top (C ∩ D n)
        (hC.inter (hDm n)) hfinn E hE, hσapp _ (hC.inter (hDm n))]
    have hCU : C = ⋃ n, C ∩ D n := by rw [← inter_iUnion, hDU, inter_univ]
    have hdisj2 : Pairwise (Function.onFun Disjoint fun n => C ∩ D n) := fun i j hij =>
      (hDdisj hij).mono inter_subset_right inter_subset_right
    have hdisj1 : Pairwise (Function.onFun Disjoint fun n => E ×ˢ (C ∩ D n)) :=
      fun i j hij => Set.disjoint_prod.mpr (Or.inr (hdisj2 hij))
    have hEC : E ×ˢ C = ⋃ n, E ×ˢ (C ∩ D n) := by
      conv_lhs => rw [hCU]
      rw [prod_iUnion]
    have hσC : σ C = ∑' n, σ (C ∩ D n) := by
      conv_lhs => rw [hCU]
      exact measure_iUnion hdisj2 (fun n => hC.inter (hDm n))
    rw [hEC, measure_iUnion hdisj1 (fun n => hE.prod (hC.inter (hDm n))), hσC,
      ← ENNReal.tsum_mul_left]
    exact tsum_congr hCn
  have hσfin : SigmaFinite σ := by
    refine ⟨⟨MeasureTheory.Measure.FiniteSpanningSetsIn.mk B (fun _ => Set.mem_univ _)
      (fun n => ?_) hBU⟩⟩
    rw [hσapp _ (hBm n)]
    exact ENNReal.div_lt_top (hBfin n K₀ hK₀).ne hK₀pos
  haveI := hσfin
  exact ⟨σ, hσfin, (Measure.prod_eq hrect).symm⟩

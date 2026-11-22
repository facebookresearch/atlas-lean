/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted from tianyipeng/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero.lean.
Modified for ATLAS: narrow imports, private proof helpers, and public API.
-/
module

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Haar-null zero sets of multivariate polynomials

Over a nondiscrete locally compact second-countable Hausdorff topological
field, the zero set of a nonzero polynomial in finitely many variables has
measure zero for every additive Haar measure. The variable type may be empty.
-/

open MeasureTheory Filter Topology

namespace MvPolynomial

private theorem nhdsNE_zero_neBot (F : Type*) [AddGroup F]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    (hF : ¬ DiscreteTopology F) : (𝓝[≠] (0 : F)).NeBot := by
  exact ⟨fun h => hF (discreteTopology_iff_isOpen_singleton_zero.mpr
    ((isOpen_singleton_iff_punctured_nhds _).mpr h))⟩

private theorem measure_zero_fin (F : Type*) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
    [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) (μF : Measure F) [μF.IsAddHaarMeasure] :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) F), p ≠ 0 →
      (Measure.pi fun _ : Fin n => μF) {x | eval x p = 0} = 0 := by
  have : (𝓝[≠] (0 : F)).NeBot := nhdsNE_zero_neBot F hF
  intro n
  induction n with
  | zero =>
    intro p hp
    have h : {x : Fin 0 → F | eval x p = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [eq_C_of_isEmpty p, eval_C]
      intro h0
      apply hp
      rw [eq_C_of_isEmpty p, h0, C_0]
    rw [h, measure_empty]
  | succ n ih =>
    intro p hp
    classical
    let P := finSuccEquiv F n p
    have hP : P ≠ 0 := by
      intro h
      apply hp
      apply (finSuccEquiv F n).injective
      exact h.trans (map_zero _).symm
    have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => F) 0
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => μF)
        (μF.prod (Measure.pi fun _ : Fin n => μF)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μF) 0
    have hsymm (q : F × (Fin n → F)) :
        e.symm q = (Fin.cons q.1 q.2 : Fin (n + 1) → F) := by
      rw [← Fin.insertNth_zero']
      rfl
    have hZm : MeasurableSet {x : Fin (n + 1) → F | eval x p = 0} :=
      (isClosed_singleton.preimage (continuous_eval p)).measurableSet
    let S := e.symm ⁻¹' {x : Fin (n + 1) → F | eval x p = 0}
    have hS : MeasurableSet S := hZm.preimage e.symm.measurable
    have hZ : {x : Fin (n + 1) → F | eval x p = 0} = e ⁻¹' S := by
      simp only [S, ← Set.preimage_comp, MeasurableEquiv.symm_comp_self,
        Set.preimage_id]
    rw [hZ, hmp.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm hS]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (ih _ hlc)] with y hy
    change ¬ (eval y P.leadingCoeff = 0) at hy
    have hQ : P.map (eval y) ≠ 0 := by
      intro h
      apply hy
      have := congrArg (fun q => q.coeff P.natDegree) h
      simpa only [Polynomial.coeff_map, Polynomial.coeff_natDegree,
        Polynomial.coeff_zero] using this
    refine Set.Finite.measure_zero ?_ μF
    refine ((P.map (eval y)).roots.toFinset.finite_toSet).subset ?_
    intro x hx
    simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, hsymm] at hx
    rw [eval_eq_eval_mv_eval'] at hx
    simpa only [Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots hQ, Polynomial.IsRoot] using hx

-- Retain the source theorem's explicit `Fintype` assumption.
set_option linter.unusedFintypeInType false in
/-- A nonzero multivariate polynomial over a nondiscrete locally compact
second-countable Hausdorff topological field has an additive Haar-null zero set.
This includes the empty variable type. -/
public theorem measure_setOf_eval_eq_zero_of_ne_zero
    (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace F] [T2Space F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type*) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | eval x p = 0} = 0 := by
  classical
  let μF : Measure F := Measure.addHaar
  let π : Measure (ι → F) := Measure.pi fun _ : ι => μF
  have hac : μ ≪ π := Measure.absolutelyContinuous_isAddHaarMeasure μ π
  apply hac
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm)
      (Measure.pi fun _ : Fin (Fintype.card ι) => μF) π :=
    measurePreserving_piCongrLeft (fun _ : ι => μF) σ.symm
  have hZm : MeasurableSet {x : ι → F | eval x p = 0} :=
    (isClosed_singleton.preimage (continuous_eval p)).measurableSet
  rw [← hmp.measure_preimage hZm.nullMeasurableSet]
  have hcoe (g : Fin (Fintype.card ι) → F) :
      ((MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm) g : ι → F) =
        g ∘ σ := by
    funext i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
  have hpre :
      (MeasurableEquiv.piCongrLeft (fun _ : ι => F) σ.symm) ⁻¹'
          {x : ι → F | eval x p = 0} =
        {g : Fin (Fintype.card ι) → F | eval g (rename σ p) = 0} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_rename, hcoe]
  rw [hpre]
  exact measure_zero_fin F hF μF _ _
    (fun h => hp (rename_injective _ σ.injective (h.trans (map_zero _).symm)))

end MvPolynomial

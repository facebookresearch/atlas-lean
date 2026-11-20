/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.PairMixingCofinite
import Code.FrontierB.CurrentLimitTranslation
import Code.Ising.IsingPlusTIFromPlacement

open MeasureTheory Set
open scoped BigOperators

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.ConfigSpace StatMech.FK

theorem siteTranslation_solution_finite {d : Nat} (x y : Site d) :
    {g : Multiplicative (Site d) | g • x = y}.Finite := by
  apply finite_solution_of_injective
  intro z g h hgh
  change Multiplicative.toAdd g + z = Multiplicative.toAdd h + z at hgh
  change Multiplicative.toAdd g = Multiplicative.toAdd h
  exact add_right_cancel hgh

noncomputable def plusEvenExpansionIndices {d : Nat}
    (F : Finset (Sym2 (Site d))) :
    Finset (Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) :=
  F.powerset.sigma fun T => (edgeBoundary (F \ T)).powerset

noncomputable def plusEvenExpansionCoeff {d : Nat} (beta : Real)
    (F : Finset (Sym2 (Site d)))
    (i : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) : Real :=
  edgeExpansionCoeff beta F i.1 *
    plusSpinExpansionCoeff (edgeBoundary (F \ i.1)) i.2

def plusEvenExpansionSupport {d : Nat}
    (i : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) :
    Finset (Site d) := i.2

noncomputable def edgeVertexSupport {d : Nat} (F : Finset (Sym2 (Site d))) :
    Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

theorem mem_edgeVertexSupport_of_mem_edge {d : Nat}
    {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)} (he : e ∈ F)
    {x : Site d} (hx : x ∈ e) : x ∈ edgeVertexSupport F := by
  rw [edgeVertexSupport, Finset.mem_biUnion]
  refine ⟨e, he, ?_⟩
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hx' : x ∈ s(e.out.1, e.out.2) := by
    rw [hout]
    exact hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    (Sym2.mem_iff.mp hx')

theorem iti_monomialBcf_eq_fmu_moInd {d : Nat} (T : Finset (Site d))
    (omega : ConfigSpace (Site d)) :
  iti_monomialBcf T omega = fmu_moInd T omega := by
  rw [fmu_moInd_eq_indicator]
  simp only [iti_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply,
    iti_monomialCM, ContinuousMap.prod_apply]
  exact iti_prod_coordCM_eq_indicator T omega



theorem exp_neg_edgeSpinSum_eq_plusEvenExpansion {d : Nat} (beta : Real)
    (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (omega : ConfigSpace (Site d)) :
    Real.exp (-beta * edgeSpinSum F omega) =
      ∑ i ∈ plusEvenExpansionIndices F,
        plusEvenExpansionCoeff beta F i *
          fmu_moInd (plusEvenExpansionSupport i) omega := by
  rw [exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF]
  simp_rw [spinProd_eq_plusSpinExpansion]
  rw [plusEvenExpansionIndices, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  rw [iti_monomialBcf_eq_fmu_moInd]
  simp only [plusEvenExpansionCoeff, plusEvenExpansionSupport]
  ring

theorem integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion {d : Nat}
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (beta : Real) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu) =
      ∑ i ∈ plusEvenExpansionIndices F,
        plusEvenExpansionCoeff beta F i *
          mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
  have hpoint : (fun omega => Real.exp (-beta * edgeSpinSum F omega)) =
      fun omega => ∑ i ∈ plusEvenExpansionIndices F,
        plusEvenExpansionCoeff beta F i *
          fmu_moInd (plusEvenExpansionSupport i) omega := by
    funext omega
    exact exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F hF omega
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_const_mul, fmu_integral_moInd]
  · intro i hi
    exact (fmu_integrable_moInd (plusEvenExpansionSupport i)).const_mul _



theorem plusState_deletedEdge_pairMixing {d : Nat} (hd : 1 ≤ d)
    {beta : Real} (hbeta : 0 ≤ beta)
    (F F' : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (hF' : ∀ e ∈ F', ¬ e.IsDiag)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint F (currentShiftFinset g F') ∧
      abs ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega))
            ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) -
        (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
            ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (∫ omega, Real.exp (-beta * edgeSpinSum F' omega)
            ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) < epsilon := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let IF := plusEvenExpansionIndices F
  let IF' := plusEvenExpansionIndices F'
  let sentinel : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d) :=
    ⟨∅, edgeVertexSupport F⟩
  let sentinel' : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d) :=
    ⟨∅, edgeVertexSupport F'⟩
  let indices := insert sentinel (insert sentinel' (IF ∪ IF'))
  let c := fun i => if i ∈ IF then plusEvenExpansionCoeff beta F i else 0
  let c' := fun i => if i ∈ IF' then plusEvenExpansionCoeff beta F' i else 0
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    iptp_plusState_isTranslationInvariant hbeta le_rfl
  have hpair : fmu_PairMixing (G := Multiplicative (Site d)) mu :=
    ipe_plusState_pairMixing_of_upperDecay hbeta 0 hti
      (icb_plusState_upperDecay hd hbeta le_rfl hti)
  obtain ⟨g, hdisj, hcorr⟩ := fmu_finsetExpansion_pairMixing
    (fun x y => siteTranslation_solution_finite x y) hti hpair indices
      plusEvenExpansionSupport c c' epsilon hepsilon
  have hIF : IF ⊆ indices := by
    intro i hi
    simp [indices, hi]
  have hIF' : IF' ⊆ indices := by
    intro i hi
    simp [indices, hi]
  have hleftPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices, c i * fmu_moInd (plusEvenExpansionSupport i) omega) =
        Real.exp (-beta * edgeSpinSum F omega) := by
    calc
      (∑ i ∈ indices, c i * fmu_moInd (plusEvenExpansionSupport i) omega) =
          ∑ i ∈ IF, c i * fmu_moInd (plusEvenExpansionSupport i) omega := by
            refine (Finset.sum_subset hIF (fun i hiIndices hiIF => ?_)).symm
            simp [c, hiIF]
      _ = ∑ i ∈ plusEvenExpansionIndices F,
          plusEvenExpansionCoeff beta F i *
            fmu_moInd (plusEvenExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c, IF, hi]
      _ = Real.exp (-beta * edgeSpinSum F omega) :=
        (exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F hF omega).symm
  have hrightPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices, c' i * fmu_moInd (plusEvenExpansionSupport i) omega) =
        Real.exp (-beta * edgeSpinSum F' omega) := by
    calc
      (∑ i ∈ indices, c' i * fmu_moInd (plusEvenExpansionSupport i) omega) =
          ∑ i ∈ IF', c' i * fmu_moInd (plusEvenExpansionSupport i) omega := by
            refine (Finset.sum_subset hIF' (fun i hiIndices hiIF' => ?_)).symm
            simp [c', hiIF']
      _ = ∑ i ∈ plusEvenExpansionIndices F',
          plusEvenExpansionCoeff beta F' i *
            fmu_moInd (plusEvenExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c', IF', hi]
      _ = Real.exp (-beta * edgeSpinSum F' omega) :=
        (exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F' hF' omega).symm
  have hleftMass :
      (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i))) =
        ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu := by
    calc
      (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i))) =
          ∑ i ∈ IF, c i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
            refine (Finset.sum_subset hIF (fun i hiIndices hiIF => ?_)).symm
            simp [c, hiIF]
      _ = ∑ i ∈ plusEvenExpansionIndices F,
          plusEvenExpansionCoeff beta F i *
            mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c, IF, hi]
      _ = ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu :=
        (integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion mu beta F hF).symm
  have hrightMass :
      (∑ i ∈ indices, c' i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i))) =
        ∫ omega, Real.exp (-beta * edgeSpinSum F' omega) ∂mu := by
    calc
      (∑ i ∈ indices, c' i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i))) =
          ∑ i ∈ IF', c' i * mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
            refine (Finset.sum_subset hIF' (fun i hiIndices hiIF' => ?_)).symm
            simp [c', hiIF']
      _ = ∑ i ∈ plusEvenExpansionIndices F',
          plusEvenExpansionCoeff beta F' i *
            mu.real (fmu_multiOpen (plusEvenExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c', IF', hi]
      _ = ∫ omega, Real.exp (-beta * edgeSpinSum F' omega) ∂mu :=
        (integral_exp_neg_edgeSpinSum_eq_plusEvenExpansion mu beta F' hF').symm
  have hsentinel : sentinel ∈ indices := by simp [indices]
  have hsentinel' : sentinel' ∈ indices := by simp [indices]
  have hvertices : Disjoint (edgeVertexSupport F)
      ((edgeVertexSupport F').image (fun x => g⁻¹ • x)) := by
    simpa [sentinel, sentinel', plusEvenExpansionSupport] using
      hdisj sentinel hsentinel sentinel' hsentinel'
  have hedges : Disjoint F (currentShiftFinset g F') := by
    rw [Finset.disjoint_left]
    intro e heF heShift
    rw [currentShiftFinset, Finset.mem_image] at heShift
    obtain ⟨e', heF', heq⟩ := heShift
    have hxF' : e'.out.1 ∈ edgeVertexSupport F' :=
      mem_edgeVertexSupport_of_mem_edge heF' (Sym2.out_fst_mem e')
    have hxedge : g⁻¹ • e'.out.1 ∈ g⁻¹ • e' := by
      change g⁻¹ • e'.out.1 ∈ Sym2.map (fun x => g⁻¹ • x) e'
      exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
    rw [heq] at hxedge
    have hxF : g⁻¹ • e'.out.1 ∈ edgeVertexSupport F :=
      mem_edgeVertexSupport_of_mem_edge heF hxedge
    exact (Finset.disjoint_left.mp hvertices hxF)
      (Finset.mem_image.mpr ⟨e'.out.1, hxF', rfl⟩)
  refine ⟨g, hedges, ?_⟩
  simpa only [hleftPoint, hrightPoint, hleftMass, hrightMass, mu] using hcorr

theorem currentParityAvoidCylinder_inter {E : Type*} [DecidableEq E]
    (F F' : Finset E) :
    currentParityAvoidCylinder F ∩ currentParityAvoidCylinder F' =
      currentParityAvoidCylinder (F ∪ F') := by
  ext m
  simp only [mem_inter_iff, currentParityAvoidCylinder, Set.mem_setOf_eq,
    Finset.mem_union]
  aesop

theorem edgeSpinSum_union {d : Nat} {F F' : Finset (Sym2 (Site d))}
    (hdisj : Disjoint F F') (omega : ConfigSpace (Site d)) :
    edgeSpinSum (F ∪ F') omega =
      edgeSpinSum F omega + edgeSpinSum F' omega := by
  unfold edgeSpinSum
  exact Finset.sum_union hdisj

theorem infinitePlusCurrentMeasure_parityAvoid_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F) =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card := by
  rw [Measure.real,
    infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta F hF,
    ENNReal.toReal_ofReal]
  positivity



theorem infinitePlusCurrentMeasure_parityAvoid_inter_shift_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (F F' : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hF' : (↑F' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint F (currentShiftFinset g F')) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F ∩
          (currentShift g) ⁻¹' currentParityAvoidCylinder F') =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega))
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
        (Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card) := by
  let G := currentShiftFinset g F'
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    currentShiftFinset_lattice d g F' hF'
  have hFG : (↑(F ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ F ∪ G at he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hF h) (fun h => hG h)
  rw [preimage_currentParityAvoidCylinder_currentShift,
    currentParityAvoidCylinder_inter,
    infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta (F ∪ G) hFG]
  have hcard : (F ∪ G).card = F.card + F'.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    congr 1
    dsimp [G, currentShiftFinset]
    rw [Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
  have hint (omega : ConfigSpace (Site d)) :
      Real.exp (-beta * edgeSpinSum (F ∪ G) omega) =
        Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega)) := by
    rw [edgeSpinSum_union hdisj, edgeSpinSum_shift]
    rw [show -beta * (edgeSpinSum F omega + edgeSpinSum G omega) =
        -beta * edgeSpinSum F omega + -beta * edgeSpinSum G omega by ring,
      Real.exp_add]
  rw [show (∫ omega, Real.exp (-beta * edgeSpinSum (F ∪ G) omega)
      ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
        Real.exp (-beta * edgeSpinSum F' (shift g omega))
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with omega
      exact hint omega]
  rw [hcard, pow_add]



theorem infinitePlusCurrentMeasure_parityAvoid_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (F F' : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hF' : (↑F' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint F (currentShiftFinset g F') ∧
      abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder F ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder F') -
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityAvoidCylinder F) *
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityAvoidCylinder F')) < epsilon := by
  let C := Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  let delta := epsilon / (C + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hFdiag : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hF he)
  have hF'diag : ∀ e ∈ F', ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hF' he)
  obtain ⟨g, hdisj, hspin⟩ := plusState_deletedEdge_pairMixing hd hbeta.le
    F F' hFdiag hF'diag delta hdelta
  let G := currentShiftFinset g F'
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    currentShiftFinset_lattice d g F' hF'
  have hFG : (↑(F ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ F ∪ G at he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hF h) (fun h => hG h)
  have hset : currentParityAvoidCylinder F ∩
      (currentShift g) ⁻¹' currentParityAvoidCylinder F' =
        currentParityAvoidCylinder (F ∪ G) := by
    rw [preimage_currentParityAvoidCylinder_currentShift]
    exact currentParityAvoidCylinder_inter F G
  have hcard : (F ∪ G).card = F.card + F'.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    congr 1
    dsimp [G, currentShiftFinset]
    rw [Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
  have hint :
      (∫ omega, Real.exp (-beta * edgeSpinSum (F ∪ G) omega)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
        Real.exp (-beta * edgeSpinSum F' (shift g omega))
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with omega
    rw [edgeSpinSum_union hdisj, edgeSpinSum_shift]
    rw [show -beta * (edgeSpinSum F omega + edgeSpinSum G omega) =
        -beta * edgeSpinSum F omega + -beta * edgeSpinSum G omega by ring,
      Real.exp_add]
  let I := ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
    ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
  let I' := ∫ omega, Real.exp (-beta * edgeSpinSum F' omega)
    ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
  let J := ∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
    Real.exp (-beta * edgeSpinSum F' (shift g omega))
      ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hgap :
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder F ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder F') -
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityAvoidCylinder F) *
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityAvoidCylinder F') = C * (J - I * I') := by
    rw [hset,
      infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta (F ∪ G) hFG,
      infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta F hF,
      infinitePlusCurrentMeasure_parityAvoid_real_eq hbeta F' hF', hint,
      hcard, pow_add]
    dsimp [C, I, I', J]
    ring
  refine ⟨g, hdisj, ?_⟩
  rw [hgap, abs_mul, abs_of_pos hCpos]
  have hspin' : abs (J - I * I') < delta := by
    simpa only [I, I', J] using hspin
  calc
    C * abs (J - I * I') < C * delta :=
      mul_lt_mul_of_pos_left hspin' hCpos
    _ < epsilon := by
      dsimp [delta]
      have hne : C + 1 ≠ 0 := by positivity
      have hpos : 0 < epsilon / (C + 1) := by positivity
      calc
        C * (epsilon / (C + 1)) <
            (C + 1) * (epsilon / (C + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) hpos
        _ = epsilon := mul_div_cancel₀ epsilon hne

end StatMech.FrontierB

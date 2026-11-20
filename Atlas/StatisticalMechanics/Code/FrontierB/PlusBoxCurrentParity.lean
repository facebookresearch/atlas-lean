/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.BoundaryCurrentParity
import Code.FrontierB.FreeBoxEvenLimit
import Code.IsingFK.HisingBoxClose

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.IsingFK

noncomputable def boxCurrentInteriorEquiv (d n : ℕ) :
    ↑(boxCurrentInterior d (n + 1)) ≃ StatMech.FK.boxVerts d n :=
  Equiv.ofBijective
    (fun z => ⟨z.1.1, by
      have hnob : ¬ StatMech.FK.boxBoundary d (n + 1) z.1 := by
        exact (Finset.mem_filter.mp z.2).2
      by_contra hx
      exact hnob ((hbx_boxBoundary_succ_iff d n z.1).2 hx)⟩)
    ⟨by
      intro x y hxy
      have hs : x.1.1 = y.1.1 :=
        congrArg (fun z : StatMech.FK.boxVerts d n => z.1) hxy
      exact Subtype.ext (Subtype.ext hs),
    by
      intro x
      let v : StatMech.FK.boxVerts d (n + 1) :=
        ⟨x.1, box_subset_succ d n x.2⟩
      have hvnot : ¬ StatMech.FK.boxBoundary d (n + 1) v := by
        rw [hbx_boxBoundary_succ_iff]
        exact not_not_intro x.2
      let z : ↑(boxCurrentInterior d (n + 1)) :=
        ⟨v, by simp [boxCurrentInterior, hvnot]⟩
      exact ⟨z, Subtype.ext rfl⟩⟩

noncomputable def boxCurrentInteriorConfigEquiv (d n : ℕ) :
    ConfigSpace ↑(boxCurrentInterior d (n + 1)) ≃
      ConfigSpace (StatMech.FK.boxVerts d n) :=
  Equiv.arrowCongr (boxCurrentInteriorEquiv d n) (Equiv.refl Bool)

theorem extendInteriorPlus_configEquiv_symm
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (v : StatMech.FK.boxVerts d (n + 1)) :
    extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau) v =
      if h : v.1 ∈ box d n then tau ⟨v.1, h⟩ else true := by
  by_cases hv : v.1 ∈ box d n
  · rw [dif_pos hv]
    have hvnot : ¬ StatMech.FK.boxBoundary d (n + 1) v := by
      rw [hbx_boxBoundary_succ_iff]
      exact not_not_intro hv
    have hvint : v ∈ boxCurrentInterior d (n + 1) := by
      simp [boxCurrentInterior, hvnot]
    rw [extendInteriorPlus]
    simp only [dif_pos hvint]
    change tau (boxCurrentInteriorEquiv d n ⟨v, hvint⟩) = tau ⟨v.1, hv⟩
    congr 1
  · rw [dif_neg hv]
    have hvbd : StatMech.FK.boxBoundary d (n + 1) v :=
      (hbx_boxBoundary_succ_iff d n v).2 hv
    apply extendInteriorPlus_outside
    simp [boxCurrentInterior, hvbd]

theorem extendInteriorPlus_configEquiv_symm_eq_glue
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (v : StatMech.FK.boxVerts d (n + 1)) :
    extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau) v =
      glue (plusField d) tau v.1 := by
  rw [extendInteriorPlus_configEquiv_symm]
  by_cases hv : v.1 ∈ box d n
  · rw [dif_pos hv, glue_mem]
  · rw [dif_neg hv, glue_not_mem _ _ hv]
    rfl

noncomputable def boxPullbackEdges (d n : ℕ)
    (F : Finset (Sym2 (Site d))) :
    Finset (Sym2 (StatMech.FK.boxVerts d (n + 1))) :=
  (StatMech.FK.boxGraph d (n + 1)).edgeFinset.filter
    (fun e => StatMech.FK.edgeIncl d (n + 1) e ∈ F)

theorem boxPullbackEdges_subset (d n : ℕ)
    (F : Finset (Sym2 (Site d))) :
    boxPullbackEdges d n F ⊆
      (StatMech.FK.boxGraph d (n + 1)).edgeFinset :=
  Finset.filter_subset _ _

theorem image_boxPullbackEdges
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    (boxPullbackEdges d n F).image (StatMech.FK.edgeIncl d (n + 1)) = F := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact (Finset.mem_filter.mp hf).2
  · intro he
    have himage := StatMech.IsingFK.hbx_touch_subset_image d n (hF he)
    rw [Finset.mem_image] at himage
    obtain ⟨f, hfedge, hfe⟩ := himage
    rw [Finset.mem_image]
    exact ⟨f, Finset.mem_filter.mpr ⟨hfedge, hfe ▸ he⟩, hfe⟩

theorem bond_extendInteriorPlus_eq_glue
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (e : Sym2 (StatMech.FK.boxVerts d (n + 1))) :
    bond (extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau)) e =
      bond (glue (plusField d) tau) (StatMech.FK.edgeIncl d (n + 1) e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [bond_mk, StatMech.FK.edgeIncl, Sym2.map_mk, bond_mk]
      simp only [spin]
      rw [extendInteriorPlus_configEquiv_symm_eq_glue,
        extendInteriorPlus_configEquiv_symm_eq_glue]

theorem edgeSpinSum_boxPullbackEdges
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (tau : ConfigSpace (StatMech.FK.boxVerts d n)) :
    edgeSpinSum (boxPullbackEdges d n F)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      edgeSpinSum F (glue (plusField d) tau) := by
  unfold edgeSpinSum
  simp_rw [bond_extendInteriorPlus_eq_glue]
  rw [← Finset.sum_image
    (StatMech.FK.edgeIncl_injective d (n + 1)).injOn]
  rw [image_boxPullbackEdges d n F hF]

theorem boltzmannJ_extendInteriorPlus_eq_fvWeight
    (d n : ℕ) (beta : ℝ)
    (tau : ConfigSpace (StatMech.FK.boxVerts d n)) :
    boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      Real.exp (beta *
          ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
              (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \
            bondFinsetTouch d n).card) *
        fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau := by
  calc
    boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      isingWiredWeight (StatMech.FK.boxGraph d (n + 1))
        (StatMech.FK.boxBoundary d (n + 1)) beta (latToBox d n tau) := by
      unfold boltzmannJ isingWiredWeight
      rw [if_pos (boundaryFixed_latToBox d n tau)]
      congr 1
      apply congrArg (fun x : ℝ => beta * x)
      apply Finset.sum_congr rfl
      intro e he
      simp only [one_mul]
      rw [bond_extendInteriorPlus_eq_glue,
        hbx_isingBond_latToBox_eq]
    _ = _ := hbx_isingWiredWeight_latToBox d n beta tau

theorem boundaryPartitionJ_box_eq_fvZ
    (d n : ℕ) (beta : ℝ) :
    boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) (boxCurrentInterior d (n + 1)) =
      Real.exp (beta *
          ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
              (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \
            bondFinsetTouch d n).card) *
        fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
  unfold boundaryPartitionJ fvZ
  rw [← (boxCurrentInteriorConfigEquiv d n).symm.sum_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tau htau
  exact boltzmannJ_extendInteriorPlus_eq_fvWeight d n beta tau

theorem boundarySpinExpectation_box_eq_plusIntegral
    (d n : ℕ) (beta : ℝ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    ((∑ s : ConfigSpace ↑(boxCurrentInterior d (n + 1)),
        boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s) *
          Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s))) /
      boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) (boxCurrentInterior d (n + 1))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  let C : ℝ :=
    ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
        (StatMech.FK.boxGraph d (n + 1)).edgeFinset \
      bondFinsetTouch d n).card : ℝ)
  let E : ℝ := Real.exp (beta * C)
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ s : ConfigSpace ↑(boxCurrentInterior d (n + 1)),
        boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s) *
          Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s))) =
        E * ∑ tau : ConfigSpace (StatMech.FK.boxVerts d n),
          fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
            Real.exp (-beta * edgeSpinSum F (glue (plusField d) tau)) := by
    rw [← (boxCurrentInteriorConfigEquiv d n).symm.sum_comp,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    rw [boltzmannJ_extendInteriorPlus_eq_fvWeight,
      edgeSpinSum_boxPullbackEdges d n F hF]
    change Real.exp (beta * C) * _ * _ = E * (_ * _)
    rw [← show E = Real.exp (beta * C) from rfl]
    ring
  have hden :
      boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) (boxCurrentInterior d (n + 1)) =
        E * fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
    rw [boundaryPartitionJ_box_eq_fvZ]
  rw [hnum, hden, mul_div_mul_left _ _ hE0]
  change _ = ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
    ∂fvMeasure (plusField d) n (bondFinsetTouch d n) beta 0
  rw [integral_fvMeasure_eq_sum]
  unfold fvProb
  rw [Finset.sum_div]
  congr 1
  funext tau
  ring

def currentParityAvoidCylinder {E : Type*} (F : Finset E) :
    Set (InfiniteCurrentConfig E) :=
  {m | ∀ e ∈ F, Even (m e)}

theorem preimage_currentParityAvoidCylinder_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    extendBoxCurrent d (n + 1) ⁻¹'
        currentParityAvoidCylinder F =
      {m | Disjoint
        (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
        (boxPullbackEdges d n F)} := by
  ext m
  constructor
  · intro hm
    change ∀ e ∈ F, Even (extendBoxCurrent d (n + 1) m e) at hm
    change Disjoint
      (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
      (boxPullbackEdges d n F)
    rw [Finset.disjoint_left]
    intro e heParity heBox
    have heEdge := boxPullbackEdges_subset d n F heBox
    let es : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨e, heEdge⟩
    have hodd : Odd (m es) := by
      simpa [es] using
        (mem_currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m es).mp
          heParity
    have heF : StatMech.FK.edgeIncl d (n + 1) e ∈ F :=
      (Finset.mem_filter.mp heBox).2
    have heven := hm (StatMech.FK.edgeIncl d (n + 1) e) heF
    have heq : extendBoxCurrent d (n + 1) m
        (StatMech.FK.edgeIncl d (n + 1) e) = m es := by
      exact extendBoxCurrent_included d (n + 1) m es
    rw [heq] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  · intro hm e heFmem
    change Disjoint
      (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
      (boxPullbackEdges d n F) at hm
    have himage : e ∈
        (boxPullbackEdges d n F).image (StatMech.FK.edgeIncl d (n + 1)) := by
      rw [image_boxPullbackEdges d n F hF]
      exact heFmem
    rw [Finset.mem_image] at himage
    obtain ⟨f, hfBox, hfe⟩ := himage
    have hfEdge := boxPullbackEdges_subset d n F hfBox
    let fs : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨f, hfEdge⟩
    have hnotOdd : ¬ Odd (m fs) := by
      intro hodd
      have hfParity : f ∈
          currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m := by
        exact (mem_currentParitySupport
          (StatMech.FK.boxGraph d (n + 1)) m fs).mpr hodd
      exact Finset.disjoint_left.mp hm hfParity hfBox
    have heq : extendBoxCurrent d (n + 1) m e = m fs := by
      rw [← hfe]
      exact extendBoxCurrent_included d (n + 1) m fs
    rw [heq]
    exact Nat.not_odd_iff_even.mp hnotOdd

theorem plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n) :
    (plusBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  have hbox : boxPullbackEdges d n F ⊆ G.edgeFinset :=
    boxPullbackEdges_subset d n F
  have hcard : (boxPullbackEdges d n F).card = F.card := by
    have hi := congrArg Finset.card (image_boxPullbackEdges d n F hF)
    rw [Finset.card_image_of_injective _
      (StatMech.FK.edgeIncl_injective d (n + 1))] at hi
    exact hi
  have hmeas : MeasurableSet (currentParityAvoidCylinder F) := by
    have hset : currentParityAvoidCylinder F =
        (restrictCurrent F) ⁻¹' {a : ↑F → ℕ | ∀ e, Even (a e)} := by
      ext m
      simp [currentParityAvoidCylinder, restrictCurrent]
    rw [hset]
    exact (continuous_restrictCurrent F).measurable MeasurableSet.of_discrete
  calc
    (plusBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (boundaryCurrentPMF G beta (fun _ => 1) hbeta
        (fun _ => zero_le_one) interior).toMeasure
          {m | Disjoint (currentParitySupport G m)
            (boxPullbackEdges d n F)} := by
        change Measure.map (extendBoxCurrent d (n + 1))
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta
            (fun _ => zero_le_one) interior).toMeasure
            (currentParityAvoidCylinder F) = _
        rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hmeas,
          preimage_currentParityAvoidCylinder_extendBoxCurrent d n F hF]
    _ = (boundaryParityPMF G beta hbeta interior).toMeasure
          {H | Disjoint H (boxPullbackEdges d n F)} := by
        rw [boundaryParityPMF, PMF.toMeasure_map_apply]
        · rfl
        · exact Measurable.of_discrete
        · exact MeasurableSet.of_discrete
    _ = ENNReal.ofReal
        (((∑ s : ConfigSpace ↑interior,
            boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) *
              Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
                (extendInteriorPlus interior s))) /
          boundaryPartitionJ G beta (fun _ => 1) interior) *
            Real.cosh beta ^ (boxPullbackEdges d n F).card) :=
      boundaryParityMeasure_avoid_eq_spinExpectation G beta hbeta interior
        (boxPullbackEdges d n F) hbox
    _ = _ := by
      rw [boundarySpinExpectation_box_eq_plusIntegral d n beta F hF, hcard]

end StatMech.FrontierB

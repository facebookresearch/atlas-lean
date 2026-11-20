/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Sharpness.HighTempVertexField
import Code.Sharpness.SimonPlusLimit
import Code.Sharpness.MeanfieldIsingMass
import Code.Ising.IsingPlusTIFromPlacement

open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


noncomputable def plusBoundaryEdges (Lambda : Finset (Site d)) :
    Finset (Sym2 (Site d)) :=
  (gvBondTouch Lambda).filter (fun e ↦ ¬ edgeInside Lambda e)


noncomputable def plusBoundaryField (Lambda : Finset (Site d))
    (x : {v // v ∈ Lambda}) : ℝ :=
  ((plusBoundaryEdges Lambda).filter (fun e ↦ x.1 ∈ e)).card

theorem plusBoundaryField_nonneg (Lambda : Finset (Site d))
    (x : {v // v ∈ Lambda}) :
    0 ≤ plusBoundaryField Lambda x := by
  simp [plusBoundaryField]



theorem gvBondTouch_endpoint {Lambda : Finset (Site d)} {a b : Site d}
    (he : s(a, b) ∈ gvBondTouch Lambda) : a ∈ Lambda ∨ b ∈ Lambda := by
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, hab⟩ := he
  rw [Finset.mem_filter] at hp
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hp.2.2
  · exact hp.2.2.symm



theorem plusBoundary_edge_contribution (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda})
    {e : Sym2 (Site d)} (he : e ∈ plusBoundaryEdges Lambda) :
    (∑ x : {v // v ∈ Lambda}, if x.1 ∈ e then spin tau x else 0) =
      bond (gvGlue (plusField d) Lambda tau) e := by
  rw [plusBoundaryEdges, Finset.mem_filter] at he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := gvBondTouch_endpoint he.1
      have hnot : ¬ (a ∈ Lambda ∧ b ∈ Lambda) := by
        intro h
        apply he.2
        intro v hv
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact h.1
        · exact h.2
      rcases hab with ha | hb
      · have hb' : b ∉ Lambda := fun hb' ↦ hnot ⟨ha, hb'⟩
        have hmem (x : {v // v ∈ Lambda}) :
            (x.1 = a ∨ x.1 = b) ↔ x = ⟨a, ha⟩ := by
          constructor
          · rintro (hxa | hxb)
            · exact Subtype.ext hxa
            · exact absurd (hxb ▸ x.2) hb'
          · rintro rfl
            exact Or.inl rfl
        have hspin : spin (gvGlue (plusField d) Lambda tau) a =
            spin tau ⟨a, ha⟩ := by
          simp [spin, gvGlue, ha]
        simp_rw [Sym2.mem_iff, hmem]
        simp [bond_mk, gvGlue_not_mem, plusField, hb', hspin]
      · have ha' : a ∉ Lambda := fun ha' ↦ hnot ⟨ha', hb⟩
        have hmem (x : {v // v ∈ Lambda}) :
            (x.1 = a ∨ x.1 = b) ↔ x = ⟨b, hb⟩ := by
          constructor
          · rintro (hxa | hxb)
            · exact absurd (hxa ▸ x.2) ha'
            · exact Subtype.ext hxb
          · rintro rfl
            exact Or.inr rfl
        have hspin : spin (gvGlue (plusField d) Lambda tau) b =
            spin tau ⟨b, hb⟩ := by
          simp [spin, gvGlue, hb]
        simp_rw [Sym2.mem_iff, hmem]
        simp [bond_mk, gvGlue_not_mem, plusField, ha', hspin]


theorem plusBoundary_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ plusBoundaryEdges Lambda,
        bond (gvGlue (plusField d) Lambda tau) e) =
      ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
  symm
  calc
    (∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x) =
        ∑ x : {v // v ∈ Lambda}, ∑ e ∈ plusBoundaryEdges Lambda,
          if x.1 ∈ e then spin tau x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [plusBoundaryField, Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      rw [Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split <;> simp_all
    _ = ∑ e ∈ plusBoundaryEdges Lambda,
          ∑ x : {v // v ∈ Lambda}, if x.1 ∈ e then spin tau x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ plusBoundaryEdges Lambda,
          bond (gvGlue (plusField d) Lambda tau) e := by
      apply Finset.sum_congr rfl
      intro e he
      exact plusBoundary_edge_contribution Lambda tau he



theorem plusInternalEdges_eq_map (Lambda : Finset (Site d)) :
    (gvBondTouch Lambda).filter (edgeInside Lambda) =
      (graphS d Lambda).edgeFinset.map
        (Function.Embedding.subtype
          (fun x : Site d ↦ x ∈ Lambda)).sym2Map := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Finset.mem_filter, Finset.mem_map]
      constructor
      · rintro ⟨he, hins⟩
        have ha : a ∈ Lambda :=
          hins a (Sym2.mem_mk_left a b)
        have hb : b ∈ Lambda :=
          hins b (Sym2.mem_mk_right a b)
        refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact gv_bondTouch_subset_edgeSet Lambda s(a, b) he
      · rintro ⟨f, hf, hfe⟩
        induction f using Sym2.inductionOn with
        | _ x y =>
            have hadj : (hypercubicLattice d).Adj x.1 y.1 := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hf
              exact hf
            have heq : s(a, b) = s(x.1, y.1) := hfe.symm
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · refine ⟨gv_mk_mem_bondTouch hadj (Or.inl x.2), ?_⟩
              intro v hv
              rw [Sym2.mem_iff] at hv
              rcases hv with rfl | rfl
              · exact x.2
              · exact y.2
            · refine ⟨gv_mk_mem_bondTouch hadj.symm (Or.inl y.2), ?_⟩
              intro v hv
              rw [Sym2.mem_iff] at hv
              rcases hv with rfl | rfl
              · exact y.2
              · exact x.2


theorem plusInternal_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ (gvBondTouch Lambda).filter (edgeInside Lambda),
        bond (gvGlue (plusField d) Lambda tau) e) =
      ∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e := by
  rw [plusInternalEdges_eq_map]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ a b =>
      change bond (gvGlue (plusField d) Lambda tau) s(a.1, b.1) =
        bond tau s(a, b)
      simp [bond_mk, spin, gvGlue, a.2, b.2]



theorem plusTouch_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ gvBondTouch Lambda,
        bond (gvGlue (plusField d) Lambda tau) e) =
      (∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e) +
        ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
  rw [← plusInternal_bondSum (d := d) Lambda tau,
    ← plusBoundary_bondSum Lambda tau, plusBoundaryEdges]
  exact (Finset.sum_filter_add_sum_filter_not
    (gvBondTouch Lambda) (edgeInside Lambda)
      (fun e ↦ bond (gvGlue (plusField d) Lambda tau) e)).symm


noncomputable def unitEdgeCoupling {V : Type*} (G : SimpleGraph V)
    (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeSet then 1 else 0

theorem unitEdgeCoupling_nonneg {V : Type*} (G : SimpleGraph V)
    (e : Sym2 V) : 0 ≤ unitEdgeCoupling G e := by
  unfold unitEdgeCoupling
  split <;> norm_num

@[simp] theorem unitEdgeCoupling_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    unitEdgeCoupling G e = 1 := by
  rw [unitEdgeCoupling, if_pos]
  exact SimpleGraph.mem_edgeFinset.mp he



theorem gvPlusWeight_eq_vertexFieldWeight (Lambda : Finset (Site d))
    (beta : ℝ) (tau : ConfigSpace {v // v ∈ Lambda}) :
    gvWeight (plusField d) Lambda beta 0 tau =
      vertexFieldWeight (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) tau := by
  unfold gvWeight gvEnergy vertexFieldWeight
  rw [plusTouch_bondSum]
  simp only [zero_mul, sub_zero]
  have hedge :
      (∑ e ∈ (graphS d Lambda).edgeFinset,
          unitEdgeCoupling (graphS d Lambda) e * bond tau e) =
        ∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [unitEdgeCoupling_edgeFinset (graphS d Lambda) he, one_mul]
  rw [hedge]
  congr 1
  ring

theorem gvPlusZ_eq_vertexFieldZ (Lambda : Finset (Site d)) (beta : ℝ) :
    gvZ (plusField d) Lambda beta 0 =
      vertexFieldZ (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) := by
  unfold gvZ vertexFieldZ
  apply Finset.sum_congr rfl
  intro tau _
  exact gvPlusWeight_eq_vertexFieldWeight Lambda beta tau

theorem gvPlusProb_eq_vertexField (Lambda : Finset (Site d))
    (beta : ℝ) (tau : ConfigSpace {v // v ∈ Lambda}) :
    gvProb (plusField d) Lambda beta 0 tau =
      vertexFieldWeight (graphS d Lambda) beta
          (unitEdgeCoupling (graphS d Lambda))
          (plusBoundaryField Lambda) tau /
        vertexFieldZ (graphS d Lambda) beta
          (unitEdgeCoupling (graphS d Lambda))
          (plusBoundaryField Lambda) := by
  unfold gvProb
  rw [gvPlusWeight_eq_vertexFieldWeight, gvPlusZ_eq_vertexFieldZ]



theorem integral_gvMeasure_eq_sum (eta : ConfigSpace (Site d))
    (Lambda : Finset (Site d)) (beta h : ℝ)
    (f : ConfigSpace (Site d) → ℝ) :
    ∫ omega, f omega ∂(gvMeasure eta Lambda beta h) =
      ∑ tau : ConfigSpace {v // v ∈ Lambda},
        gvProb eta Lambda beta h tau * f (gvGlue eta Lambda tau) := by
  unfold gvMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun tau _ ↦ ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (gvProb_nonneg eta Lambda beta h tau)]
  · intro tau _
    exact (integrable_dirac (by simp [enorm_eq_nnnorm])).smul_measure (by simp)



theorem spinProd_sourcePair {V : Type*} [Fintype V] [DecidableEq V]
    (tau : ConfigSpace V) (a b : V) :
    spinProd (sourcePair a b) tau = spin tau a * spin tau b := by
  by_cases hab : a = b
  · subst b
    rw [sourcePair_self, spinProd_empty, spin_sq]
  · rw [sourcePair_eq_pair hab]
    simp [spinProd, hab]



theorem gvPlus_pair_eq_vertexField (Lambda : Finset (Site d))
    (beta : ℝ) (a b : {v // v ∈ Lambda}) :
    (∫ omega, spin omega a.1 * spin omega b.1
        ∂(gvPlusMeasure Lambda beta 0)) =
      vertexFieldTwoPoint (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) a b := by
  unfold gvPlusMeasure
  rw [integral_gvMeasure_eq_sum]
  unfold vertexFieldTwoPoint vertexFieldExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tau _
  rw [gvPlusProb_eq_vertexField]
  have hspin (x : {v // v ∈ Lambda}) :
      spin (gvGlue (plusField d) Lambda tau) x.1 = spin tau x := by
    simp [spin, gvGlue, x.2]
  rw [hspin a, hspin b, spinProd_sourcePair]
  ring



theorem twoPointJ_congr_on_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (J K : Sym2 V → ℝ)
    (hJK : ∀ e ∈ G.edgeFinset, J e = K e) (a b : V) :
    twoPointJ G beta J a b = twoPointJ G beta K a b := by
  have hweight (tau : ConfigSpace V) :
      boltzmannJ G beta J tau = boltzmannJ G beta K tau := by
    unfold boltzmannJ
    apply congrArg Real.exp
    apply congrArg (fun r ↦ beta * r)
    apply Finset.sum_congr rfl
    intro e he
    rw [hJK e he]
  unfold twoPointJ expectationJ partitionJ
  simp_rw [hweight]



theorem twoPointJ_couplingIn_unitEdge (Lambda : Finset (Site d))
    (beta : ℝ) (T : Finset {v // v ∈ Lambda})
    (a b : {v // v ∈ Lambda}) :
    twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) a b =
      twoPointJ (graphS d Lambda) beta (couplingIn (fun _ ↦ 1) T) a b := by
  apply twoPointJ_congr_on_edges
  intro e he
  simp only [couplingIn]
  split
  · rw [unitEdgeCoupling_edgeFinset (graphS d Lambda) he]
  · rfl


noncomputable def plusCutSites {Lambda : Finset (Site d)}
    (T : Finset {v // v ∈ Lambda}) : Finset (Site d) :=
  T.image Subtype.val

@[simp] theorem mem_plusCutSites {Lambda : Finset (Site d)}
    {T : Finset {v // v ∈ Lambda}} {x : {v // v ∈ Lambda}} :
    x.1 ∈ plusCutSites T ↔ x ∈ T := by
  constructor
  · intro hx
    rw [plusCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, hval⟩ := hx
    have hyx : y = x := Subtype.ext hval
    subst y
    exact hy
  · exact fun hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩

noncomputable def plusCutVertexEquiv {Lambda : Finset (Site d)}
    (T : Finset {v // v ∈ Lambda}) :
    {x : {v // v ∈ Lambda} // x ∈ T} ≃
      {z : Site d // z ∈ plusCutSites T} :=
  Equiv.ofBijective
    (fun x ↦ ⟨x.1.1, mem_plusCutSites.mpr x.2⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : {z : Site d // z ∈ plusCutSites T} ↦ z.1) h,
    by
      intro z
      have hz : z.1 ∈ T.image Subtype.val := z.2
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, hval⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hval⟩⟩

theorem plusCutVertexEquiv_adj {Lambda : Finset (Site d)}
    (T : Finset {v // v ∈ Lambda})
    (a b : {x : {v // v ∈ Lambda} // x ∈ T}) :
    ((graphS d Lambda).comap
        (Subtype.val : {x : {v // v ∈ Lambda} // x ∈ T} →
          {v // v ∈ Lambda})).Adj a b ↔
      (graphS d (plusCutSites T)).Adj
        (plusCutVertexEquiv T a) (plusCutVertexEquiv T b) := by
  rfl

theorem corrOriginInner_origin_of_mem (beta : ℝ) (S : Finset (Site d))
    (ho : Percolation.origin d ∈ S) :
    corrOriginInner d beta S (Percolation.origin d) = 1 := by
  unfold corrOriginInner
  rw [dif_pos ho, dif_pos ho]
  exact freeCorr_self d beta S _



theorem plus_localCorr_eq_corrOriginInner
    (Lambda : Finset (Site d)) (beta : ℝ)
    (T : Finset {v // v ∈ Lambda}) {o x : {v // v ∈ Lambda}}
    (ho : o ∈ T) (hx : x ∈ T)
    (horigin : o.1 = Percolation.origin d) :
    twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) o x =
      corrOriginInner d beta (plusCutSites T) x.1 := by
  classical
  rw [twoPointJ_couplingIn_unitEdge]
  by_cases hox : o = x
  · subst x
    rw [twoPointJ_self]
    have homem : Percolation.origin d ∈ plusCutSites T := by
      rw [← horigin]
      exact mem_plusCutSites.mpr ho
    rw [horigin]
    exact (corrOriginInner_origin_of_mem beta (plusCutSites T) homem).symm
  · rw [twoPointJ, sourcePair_eq_pair hox]
    let oT : {z : {v // v ∈ Lambda} // z ∈ T} := ⟨o, ho⟩
    let xT : {z : {v // v ∈ Lambda} // z ∈ T} := ⟨x, hx⟩
    have hbase := expectationJ_couplingIn_one_eq_induced
      (graphS d Lambda) beta T ho hx
    have hrel := Ising.isingExpectation_spinProd_relabel
      ((graphS d Lambda).comap
        (Subtype.val : {z : {v // v ∈ Lambda} // z ∈ T} →
          {v // v ∈ Lambda}))
      (graphS d (plusCutSites T)) (plusCutVertexEquiv T)
      (plusCutVertexEquiv_adj T) beta 0 ({oT, xT} : Finset _)
    have hmap : ({oT, xT} : Finset _).map
        (plusCutVertexEquiv T).toEmbedding =
        ({⟨Percolation.origin d, by simpa [← horigin] using
              (mem_plusCutSites.mpr ho)⟩,
          ⟨x.1, mem_plusCutSites.mpr hx⟩} :
          Finset {z : Site d // z ∈ plusCutSites T}) := by
      ext z
      simp [oT, xT, plusCutVertexEquiv, horigin]
    rw [hmap] at hrel
    rw [hbase, hrel]
    have ho' : Percolation.origin d ∈ plusCutSites T := by
      rw [← horigin]
      exact mem_plusCutSites.mpr ho
    have hx' : x.1 ∈ plusCutSites T := mem_plusCutSites.mpr hx
    unfold corrOriginInner
    rw [dif_pos ho', dif_pos hx']
    unfold freeCorr
    rw [if_neg]
    intro heq
    apply hox
    apply Subtype.ext
    have := congrArg
      (fun z : {z : Site d // z ∈ plusCutSites T} ↦ z.1) heq
    simpa [horigin] using this


noncomputable def sitesInVolume (Lambda T : Finset (Site d)) :
    Finset {v // v ∈ Lambda} :=
  Finset.univ.filter (fun x ↦ x.1 ∈ T)

@[simp] theorem mem_sitesInVolume {Lambda T : Finset (Site d)}
    {x : {v // v ∈ Lambda}} :
    x ∈ sitesInVolume Lambda T ↔ x.1 ∈ T := by
  simp [sitesInVolume]



theorem plusBoundaryField_eq_zero_of_neighbors
    (Lambda T : Finset (Site d))
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (x : {v // v ∈ Lambda}) (hx : x ∈ sitesInVolume Lambda T) :
    plusBoundaryField Lambda x = 0 := by
  unfold plusBoundaryField
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro e he hxe
  rw [plusBoundaryEdges, Finset.mem_filter] at he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hadj : (hypercubicLattice d).Adj a b :=
        gv_bondTouch_subset_edgeSet Lambda s(a, b) he.1
      rw [Sym2.mem_iff] at hxe
      apply he.2
      intro v hv
      rw [Sym2.mem_iff] at hv
      rcases hxe with hxa | hxb
      · have haT : a ∈ T := by simpa [hxa] using hx
        have hbL := hnbr a haT b hadj
        rcases hv with rfl | rfl
        · simpa [hxa] using x.2
        · exact hbL
      · have hbT : b ∈ T := by simpa [hxb] using hx
        have haL := hnbr b hbT a hadj.symm
        rcases hv with rfl | rfl
        · exact haL
        · simpa [hxb] using x.2



theorem gvPlus_simon_subtype
    (Lambda T : Finset (Site d)) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (o z : {v // v ∈ Lambda})
    (ho : o.1 ∈ T) (hz : z.1 ∉ T) :
    (∫ omega, spin omega o.1 * spin omega z.1
        ∂(gvPlusMeasure Lambda beta 0)) ≤
      ∑ x ∈ sitesInVolume Lambda T,
        ∑ y ∈ (Finset.univ \ sitesInVolume Lambda T),
          Real.tanh
              (beta * unitEdgeCoupling (graphS d Lambda) s(x, y)) *
            twoPointJ (graphS d Lambda) beta
              (couplingIn (unitEdgeCoupling (graphS d Lambda))
                (sitesInVolume Lambda T)) o x *
            (∫ omega, spin omega y.1 * spin omega z.1
              ∂(gvPlusMeasure Lambda beta 0)) := by
  rw [gvPlus_pair_eq_vertexField]
  have hfield : ∀ x ∈ sitesInVolume Lambda T,
      plusBoundaryField Lambda x = 0 :=
    plusBoundaryField_eq_zero_of_neighbors Lambda T hnbr
  have hsimon := vertexFieldTwoPoint_simon_finite (graphS d Lambda) beta
    (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda)
    hbeta (unitEdgeCoupling_nonneg (graphS d Lambda))
    (plusBoundaryField_nonneg Lambda) (sitesInVolume Lambda T) hfield
    o z (by simpa using ho) (by simpa using hz)
  simpa only [gvPlus_pair_eq_vertexField] using hsimon

theorem plusCutSites_sitesInVolume (Lambda T : Finset (Site d))
    (hsub : T ⊆ Lambda) :
    plusCutSites (sitesInVolume Lambda T) = T := by
  ext x
  constructor
  · intro hx
    rw [plusCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨⟨x, hsub hx⟩, by simpa using hx, rfl⟩


theorem gvPlus_simon_ambient
    (Lambda T : Finset (Site d)) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsub : T ⊆ Lambda)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (ho : Percolation.origin d ∈ T) (z : Site d)
    (hzL : z ∈ Lambda) (hzT : z ∉ T) :
    (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(gvPlusMeasure Lambda beta 0)) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (gvPlusMeasure Lambda beta 0) := by
  classical
  let oL : {v // v ∈ Lambda} := ⟨Percolation.origin d, hsub ho⟩
  let zL : {v // v ∈ Lambda} := ⟨z, hzL⟩
  let C := (sitesInVolume Lambda T) ×ˢ
    ((Finset.univ : Finset {v // v ∈ Lambda}) \ sitesInVolume Lambda T)
  let A := C.filter (fun p ↦ (graphS d Lambda).Adj p.1 p.2)
  let F : {v // v ∈ Lambda} × {v // v ∈ Lambda} → ℝ := fun p ↦
    Real.tanh (beta * unitEdgeCoupling (graphS d Lambda) s(p.1, p.2)) *
      twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda))
          (sitesInVolume Lambda T)) oL p.1 *
      (∫ omega, spin omega p.2.1 * spin omega z
        ∂(gvPlusMeasure Lambda beta 0))
  have hs := gvPlus_simon_subtype Lambda T beta hbeta hnbr oL zL
    (by simpa [oL] using ho) (by simpa [zL] using hzT)
  have hdouble :
      (∑ x ∈ sitesInVolume Lambda T,
        ∑ y ∈ (Finset.univ \ sitesInVolume Lambda T), F (x, y)) =
        ∑ p ∈ A, F p := by
    rw [← Finset.sum_product]
    change (∑ p ∈ C, F p) = ∑ p ∈ C.filter _ , F p
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hadj : (graphS d Lambda).Adj p.1 p.2
    · rw [if_pos hadj]
    · rw [if_neg hadj]
      have hzero : unitEdgeCoupling (graphS d Lambda) s(p.1, p.2) = 0 := by
        rw [unitEdgeCoupling, if_neg]
        simpa [SimpleGraph.mem_edgeSet] using hadj
      simp [F, hzero]
  have hboundary :
      (∑ p ∈ A, F p) =
        ∑ e ∈ boundaryEdges d T,
          Real.tanh beta * corrOriginInner d beta T e.1 *
            (∫ omega, spin omega e.2 * spin omega z
              ∂(gvPlusMeasure Lambda beta 0)) := by
    symm
    apply Finset.sum_bij
      (fun e he ↦
        (⟨e.1, hsub (shk_mem_boundaryEdges_iff.mp he).1⟩,
         ⟨e.2, hnbr e.1 (shk_mem_boundaryEdges_iff.mp he).1 e.2
            (shk_mem_boundaryEdges_iff.mp he).2.2⟩))
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      simp only [A, Finset.mem_filter, C, Finset.mem_product]
      exact ⟨⟨by simpa using he1, by simpa using he2⟩, hadj⟩
    · intro a ha b hb hab
      exact Prod.ext
        (congrArg (fun p ↦ p.1.1) hab)
        (congrArg (fun p ↦ p.2.1) hab)
    · intro p hp
      simp only [A, Finset.mem_filter, C, Finset.mem_product] at hp
      refine ⟨(p.1.1, p.2.1), ?_, ?_⟩
      · apply shk_mem_boundaryEdges_iff.mpr
        exact ⟨by simpa using hp.1.1, by simpa using hp.1.2, hp.2⟩
      · apply Prod.ext <;> rfl
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      have hedge : unitEdgeCoupling (graphS d Lambda)
          s(⟨e.1, hsub he1⟩,
            ⟨e.2, hnbr e.1 he1 e.2 hadj⟩) = 1 := by
        rw [unitEdgeCoupling, if_pos]
        exact hadj
      have hlocal := plus_localCorr_eq_corrOriginInner Lambda beta
        (sitesInVolume Lambda T)
        (o := oL) (x := ⟨e.1, hsub he1⟩)
        (by simpa [oL] using ho) (by simpa using he1) rfl
      rw [plusCutSites_sitesInVolume Lambda T hsub] at hlocal
      simp [F, hedge, hlocal]
  rw [hdouble, hboundary] at hs
  simpa [F, oL, zL, simonBoundaryIntegral] using hs



theorem plusMeasure_simon_box
    (n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (hsub : T ⊆ boxFinset d n)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y →
      y ∈ boxFinset d n)
    (ho : Percolation.origin d ∈ T) (z : Site d)
    (hzL : z ∈ boxFinset d n) (hzT : z ∉ T) :
    (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [← iptp_gvPlusMeasure_eq_plusMeasure]
  exact gvPlus_simon_ambient (boxFinset d n) T beta hbeta hsub hnbr
    ho z hzL hzT



theorem plusMeasure_simon_eventually
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (z : Site d) (hzT : z ∉ T) (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∀ᶠ n in Filter.atTop,
      (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d)))) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d))) := by
  classical
  let U : Finset (Site d) := insert z (gvCand T)
  obtain ⟨R, hR⟩ := finite_subset_box (U : Set (Site d)) U.finite_toSet
  filter_upwards
    [hphi.tendsto_atTop.eventually (Filter.eventually_ge_atTop R)] with n hn
  have hU (w : Site d) (hw : w ∈ U) : w ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simpa using hw) i).trans hn
  apply plusMeasure_simon_box (phi n) beta hbeta T
  · intro x hx
    apply hU x
    change x ∈ insert z (gvCand T)
    simp only [Finset.mem_insert]
    right
    rw [gvCand, Finset.mem_biUnion]
    exact ⟨x, hx, gv_self_mem_ball x⟩
  · intro x hx y hadj
    apply hU y
    change y ∈ insert z (gvCand T)
    simp only [Finset.mem_insert]
    right
    rw [gvCand, Finset.mem_biUnion]
    exact ⟨x, hx, gv_nbr_mem_ball hadj⟩
  · exact ho
  · exact hU z (Finset.mem_insert_self z _)
  · exact hzT



theorem plusCorr_simon
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (z : Site d) (hzT : z ∉ T) :
    plusCorr d beta (Percolation.origin d) z ≤
      simonBoundaryPlus beta T (Percolation.origin d) z := by
  apply plusCorr_simon_of_eventually_finite
  intro phi hphi
  exact plusMeasure_simon_eventually beta hbeta T ho z hzT phi hphi

end Sharpness
end StatMech

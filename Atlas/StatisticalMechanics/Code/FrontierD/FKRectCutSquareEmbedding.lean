/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCrossingExploration
import Code.FrontierD.FKRectTorusSquareDevelopment
import Code.FK.FKGeneralQConsumer
import Code.FK.FKGeneralQTranslation
import Code.FK.TwoPointPositiveFull











open MeasureTheory StatMech.Lattice SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem freeBoxEvent_le_freeInfinite
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 N)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (FK.boxGraph 2 N) p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 N ⁻¹' A) := by
  have hmeas : MeasurableSet (FK.boxRestrict 2 N ⁻¹' A) :=
    (FK.continuous_boxRestrict 2 N).measurable MeasurableSet.of_discrete
  rw [← FK.freeFiniteMeasure_real_boxRestrictEvent
    N hp hp1 (zero_lt_one.trans_le hq) A hmeas]
  apply ge_of_tendsto
    (FK.fkgq_free_infinite_measure N hp hp1 hq hA)
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hNm ih =>
      exact ih.trans (FK.fkgq_free_succ N m hNm hp hp1 hq hA)


def fkRectSquareSiteOfPair (p : Int × Int) : Site 2 := ![p.1, p.2]

@[simp] theorem fkRectSquareSiteOfPair_zero (p : Int × Int) :
    fkRectSquareSiteOfPair p 0 = p.1 := by
  simp [fkRectSquareSiteOfPair]

@[simp] theorem fkRectSquareSiteOfPair_one (p : Int × Int) :
    fkRectSquareSiteOfPair p 1 = p.2 := by
  simp [fkRectSquareSiteOfPair]

theorem fkRectSquareSiteOfPair_injective :
    Function.Injective fkRectSquareSiteOfPair := by
  intro p q hpq
  apply Prod.ext
  · simpa using congrFun hpq 0
  · simpa using congrFun hpq 1


def fkRectVertexSquareSite (R : FKRectTorus) (x : R.Vertex) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectVertexSquarePoint R x)

theorem fkRectVertexSquareSite_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexSquareSite R) := by
  intro x y hxy
  have hpoint := fkRectSquareSiteOfPair_injective hxy
  have hlift := fkRectSquareDevelopPoint_injective hpoint
  apply Prod.ext
  · apply Fin.ext
    have hxInt : (x.1.val : Int) = y.1.val := by
      simpa only [Prod.fst] using congrArg (fun z => z.1) hlift
    exact_mod_cast hxInt
  · apply Fin.ext
    have hyInt : (x.2.val : Int) = y.2.val := by
      simpa only [Prod.snd] using congrArg (fun z => z.2) hlift
    exact_mod_cast hyInt


theorem fkRectSquareAxisStep_iff_hypercubicAdj (p q : Int × Int) :
    FKRectSquareAxisStep p q ↔
      (hypercubicLattice 2).Adj
        (fkRectSquareSiteOfPair p) (fkRectSquareSiteOfPair q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [fkRectSquareSiteOfPair_zero, fkRectSquareSiteOfPair_one]
  constructor
  · rintro (h | h | h | h)
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 1 := by omega
      have hpq1 : p.2 - q.2 = 0 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 0 := by omega
      have hpq1 : p.2 - q.2 = -1 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = -1 := by omega
      have hpq1 : p.2 - q.2 = 0 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 0 := by omega
      have hpq1 : p.2 - q.2 = 1 := by omega
      rw [hpq0, hpq1]
      norm_num
  · intro h
    have habs :
        (p.1 - q.1).natAbs = 0 ∧ (p.2 - q.2).natAbs = 1 ∨
        (p.1 - q.1).natAbs = 1 ∧ (p.2 - q.2).natAbs = 0 := by
      omega
    rcases habs with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have heq0 : p.1 = q.1 := by
        have := Int.natAbs_eq_zero.mp h0
        omega
      have hone : p.2 - q.2 = 1 ∨ p.2 - q.2 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h1)
      rcases hone with hone | hone
      · right; right; right
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
      · right; left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · have heq1 : p.2 = q.2 := by
        have := Int.natAbs_eq_zero.mp h1
        omega
      have hone : p.1 - q.1 = 1 ∨ p.1 - q.1 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h0)
      rcases hone with hone | hone
      · left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
      · right; right; left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega

@[simp] theorem mem_fkRectHorizontalCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectHorizontalCutEdges R ↔ a.2.2.val = 0 := by
  classical
  rcases a with ⟨b, x, y⟩
  unfold fkRectHorizontalCutEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨b', x'⟩, _, h⟩
    exact congrArg (fun e => e.2.2.val) h.symm
  · intro hy
    refine ⟨(b, x), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa using hy.symm

@[simp] theorem mem_fkRectVerticalCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectVerticalCutEdges R ↔
      a.1 = false ∧ a.2.1.val = 0 := by
  classical
  rcases a with ⟨b, x, y⟩
  unfold fkRectVerticalCutEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y', _, h⟩
    constructor
    · exact congrArg (fun e => e.1) h.symm
    · exact congrArg (fun e => e.2.1.val) h.symm
  · rintro ⟨hb, hx⟩
    refine ⟨y, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · simpa using hb.symm
    · apply Prod.ext
      · apply Fin.ext
        simpa using hx.symm
      · rfl

@[simp] theorem mem_fkRectTorusCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectTorusCutEdges R ↔
      a.2.2.val = 0 ∨ (a.1 = false ∧ a.2.1.val = 0) := by
  simp [fkRectTorusCutEdges]



theorem fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).1 =
      fkRectVertexSquarePoint R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).1) := by
  rcases a with ⟨b, x, y⟩
  rw [mem_fkRectTorusCutEdges_iff] at ha
  push Not at ha
  rcases ha with ⟨hy, hb⟩
  cases b
  · have hx : x.val ≠ 0 := hb rfl
    have hcastx : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    by_cases heven : Even y.val <;>
      simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
        fkRectVertexSquarePoint, fkRectCyclicPred_val,
        heven, hx, hcastx]
  · simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectVertexSquarePoint]

theorem fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).2 =
      fkRectVertexSquarePoint R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).2) := by
  rcases a with ⟨b, x, y⟩
  rw [mem_fkRectTorusCutEdges_iff] at ha
  push Not at ha
  rcases ha with ⟨hy, hb⟩
  have hy0 : y.val ≠ 0 := by simpa using hy
  have hcasty : ((y.val - 1 : Nat) : Int) = (y.val : Int) - 1 := by
    omega
  cases b
  · have hx : x.val ≠ 0 := hb rfl
    have hcastx : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    by_cases heven : Even y.val <;>
      simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
        fkRectVertexSquarePoint, fkRectCyclicPred_val,
        heven, hx, hy, hcastx, hcasty]
  · simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectVertexSquarePoint, fkRectCyclicPred_val, hy, hcasty]



theorem fkRectCutGraph_adj_imp_hypercubicAdj
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectCutGraph R).Adj x y) :
    (hypercubicLattice 2).Adj
      (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
  obtain ⟨htorus, hcut⟩ := (fkRectCutGraph_adj_iff R x y).mp hxy
  obtain ⟨a, hedge⟩ := htorus
  have ha : a ∉ fkRectTorusCutEdges R := by
    intro ha
    apply hcut
    rw [← hedge]
    exact (mem_fkRectTorusCutGraphEdges R a).2 ha
  let p := (fkRectLiftedIndexedEdgeEnds R a).1
  let q := (fkRectLiftedIndexedEdgeEnds R a).2
  have hpair :
      s(fkRectLiftedVertex R p, fkRectLiftedVertex R q) = s(x, y) := by
    exact (fkRectLiftedIndexedEdgeEnds_project R a).symm.trans hedge
  have hstep := fkRectLiftedIndexedEdgeEnds_squareStep R a
  have haxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) :=
    hstep.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hp := fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut
    R a ha
  have hq := fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂
    R a ha
  change fkRectSquareDevelopPoint p = _ at hp
  change fkRectSquareDevelopPoint q = _ at hq
  rw [hp, hq] at haxis
  have hadj :=
    (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mp haxis
  rcases Sym2.eq_iff.mp hpair with horient | horient
  · rw [horient.1, horient.2] at hadj
    simpa only [fkRectVertexSquareSite] using hadj
  · rw [horient.1, horient.2] at hadj
    simpa only [fkRectVertexSquareSite] using hadj.symm

private theorem fkRectSquareDownStep_imp_cutGraph_adj
    (R : FKRectTorus) (x y : R.Vertex)
    (hstep :
      fkRectSquareDevelopPoint (y.1.val, y.2.val) -
          fkRectSquareDevelopPoint (x.1.val, x.2.val) = (-1, 0) ∨
      fkRectSquareDevelopPoint (y.1.val, y.2.val) -
          fkRectSquareDevelopPoint (x.1.val, x.2.val) = (0, 1)) :
    (fkRectCutGraph R).Adj x y := by
  let px : Int × Int := (x.1.val, x.2.val)
  let py : Int × Int := (y.1.val, y.2.val)
  have hrowRecoverX := fkRectSquareDevelopPoint_fst_sub_snd px
  have hrowRecoverY := fkRectSquareDevelopPoint_fst_sub_snd py
  have hcolRecoverX := fkRectSquareDevelopPoint_snd_add_rowHalf px
  have hcolRecoverY := fkRectSquareDevelopPoint_snd_add_rowHalf py
  rcases hstep with hstep | hstep
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    have hrow : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [px, py] at hrowRecoverX hrowRecoverY
      omega
    have hxrow0 : x.2.val ≠ 0 := by
      intro hx0
      have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
      simp only [hx0, Nat.cast_zero] at hrow
      omega
    have hpredRow :
        SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp only [if_neg hxrow0]
      omega
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hxrow : (x.2.val : Int) = 2 * (k : Int) := by
        have hkInt : (x.2.val : Int) = (k : Int) + k := by
          exact_mod_cast hk
        omega
      have hyrow : (y.2.val : Int) = 2 * (k : Int) - 1 := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) - 1 := by
        rw [hyrow]
        omega
      have hcol : (y.1.val : Int) = (x.1.val : Int) - 1 := by
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        omega
      have hxcol0 : x.1.val ≠ 0 := by
        intro hx0
        have hyNonneg : (0 : Int) ≤ y.1.val := by positivity
        simp only [hx0, Nat.cast_zero] at hcol
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos x.1 = y.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg hxcol0]
        omega
      let a : R.EdgeIndex := (false, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
          ↓reduceIte, hevenX]
        rw [hpredCol, hpredRow]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0, hxcol0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hxrow : (x.2.val : Int) = 2 * (k : Int) + 1 := by
        exact_mod_cast hk
      have hyrow : (y.2.val : Int) = 2 * (k : Int) := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) := by
        rw [hyrow]
        omega
      have hcol : y.1 = x.1 := by
        apply Fin.ext
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        exact_mod_cast (show (y.1.val : Int) = x.1.val by omega)
      let a : R.EdgeIndex := (true, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, ↓reduceIte]
        rw [hpredRow]
        rw [show (x.1, y.2) = y by exact Prod.ext hcol.symm rfl]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    have hrow : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [px, py] at hrowRecoverX hrowRecoverY
      omega
    have hxrow0 : x.2.val ≠ 0 := by
      intro hx0
      have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
      simp only [hx0, Nat.cast_zero] at hrow
      omega
    have hpredRow :
        SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp only [if_neg hxrow0]
      omega
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hxrow : (x.2.val : Int) = 2 * (k : Int) := by
        have hkInt : (x.2.val : Int) = (k : Int) + k := by
          exact_mod_cast hk
        omega
      have hyrow : (y.2.val : Int) = 2 * (k : Int) - 1 := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) - 1 := by
        rw [hyrow]
        omega
      have hcol : y.1 = x.1 := by
        apply Fin.ext
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        exact_mod_cast (show (y.1.val : Int) = x.1.val by omega)
      let a : R.EdgeIndex := (true, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, ↓reduceIte]
        rw [hpredRow]
        rw [show (x.1, y.2) = y by exact Prod.ext hcol.symm rfl]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hxrow : (x.2.val : Int) = 2 * (k : Int) + 1 := by
        exact_mod_cast hk
      have hyrow : (y.2.val : Int) = 2 * (k : Int) := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) := by
        rw [hyrow]
        omega
      have hcol : (y.1.val : Int) = (x.1.val : Int) + 1 := by
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        omega
      have hycol0 : y.1.val ≠ 0 := by
        intro hy0
        have hxNonneg : (0 : Int) ≤ x.1.val := by positivity
        simp only [hy0, Nat.cast_zero] at hcol
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos y.1 = x.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg hycol0]
        omega
      let a : R.EdgeIndex := (false, (y.1, x.2))
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
          ↓reduceIte, heven]
        rw [hpredCol, hpredRow]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0, hycol0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩



theorem fkRectCutGraph_adj_iff_hypercubicAdj
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectCutGraph R).Adj x y ↔
      (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
  constructor
  · exact fkRectCutGraph_adj_imp_hypercubicAdj R
  · intro hxy
    have haxis := (fkRectSquareAxisStep_iff_hypercubicAdj
      (fkRectVertexSquarePoint R x)
      (fkRectVertexSquarePoint R y)).mpr (by
        simpa only [fkRectVertexSquareSite] using hxy)
    rcases haxis with h | h | h | h
    · exact fkRectSquareDownStep_imp_cutGraph_adj R x y (Or.inl h)
    · exact fkRectSquareDownStep_imp_cutGraph_adj R x y (Or.inr h)
    · apply (fkRectCutGraph R).symm
      apply fkRectSquareDownStep_imp_cutGraph_adj R y x
      left
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [fkRectVertexSquarePoint, Prod.fst_sub,
          Prod.snd_sub] at h' h'' ⊢ <;>
        omega
    · apply (fkRectCutGraph R).symm
      apply fkRectSquareDownStep_imp_cutGraph_adj R y x
      right
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [fkRectVertexSquarePoint, Prod.fst_sub,
          Prod.snd_sub] at h' h'' ⊢ <;>
        omega



theorem fkRectVertexSquareSite_mem_box
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVertexSquareSite R x ∈
      box 2 (R.width + R.height) := by
  intro i
  fin_cases i
  · simp only [fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint]
    have hu0 : (0 : Int) ≤
        (x.1.val : Int) + ((x.2.val : Int) + 1) / 2 := by
      positivity
    have huCast :
        (((x.1.val : Int) + ((x.2.val : Int) + 1) / 2).natAbs : Int) =
          (x.1.val : Int) + ((x.2.val : Int) + 1) / 2 :=
      Int.natAbs_of_nonneg hu0
    have hInt :
        (((x.1.val : Int) + ((x.2.val : Int) + 1) / 2).natAbs : Int) ≤
          (R.width + R.height : Nat) := by
      rw [huCast]
      have hx := x.1.isLt
      have hy := x.2.isLt
      omega
    exact_mod_cast hInt
  · simp only [fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint]
    calc
      ((x.1.val : Int) - (x.2.val : Int) / 2).natAbs ≤
          (x.1.val : Int).natAbs +
            ((x.2.val : Int) / 2).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ R.width + R.height := by
        have hxCast : ((x.1.val : Int).natAbs : Int) = x.1.val :=
          Int.natAbs_of_nonneg (by positivity)
        have hyCast : (((x.2.val : Int) / 2).natAbs : Int) =
            (x.2.val : Int) / 2 :=
          Int.natAbs_of_nonneg (by positivity)
        have hInt :
            ((x.1.val : Int).natAbs : Int) +
                (((x.2.val : Int) / 2).natAbs : Int) ≤
              (R.width + R.height : Nat) := by
          rw [hxCast, hyCast]
          have hx := x.1.isLt
          have hy := x.2.isLt
          omega
        exact_mod_cast hInt


def fkRectVertexBoxEmbedding (R : FKRectTorus) :
    R.Vertex → FK.boxVerts 2 (R.width + R.height) :=
  fun x => ⟨fkRectVertexSquareSite R x,
    fkRectVertexSquareSite_mem_box R x⟩

theorem fkRectVertexBoxEmbedding_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexBoxEmbedding R) := by
  intro x y hxy
  apply fkRectVertexSquareSite_injective R
  exact congrArg Subtype.val hxy



theorem fkRectCutGraph_boxAdjMatch (R : FKRectTorus) :
    FK.ocd_AdjMatch (fkRectCutGraph R)
      (FK.boxGraph 2 (R.width + R.height))
      (fkRectVertexBoxEmbedding R) := by
  intro x y
  rw [fkRectCutGraph_adj_iff_hypercubicAdj]
  rfl


def fkRectPrimalUnexploredBoxEmbedding
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FKRectPrimalUnexploredVertex R S eta →
      FK.boxVerts 2 (R.width + R.height) :=
  fun x => fkRectVertexBoxEmbedding R x.1

theorem fkRectPrimalUnexploredBoxEmbedding_injective
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    Function.Injective
      (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
  intro x y hxy
  apply Subtype.ext
  exact fkRectVertexBoxEmbedding_injective R hxy

theorem fkRectPrimalUnexplored_boxAdjMatch
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_AdjMatch
      (fkRectPrimalUnexploredInducedGraph R S eta)
      (FK.boxGraph 2 (R.width + R.height))
      (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
  intro x y
  change (fkRectCutGraph R).Adj x.1 y.1 ↔ _
  exact fkRectCutGraph_boxAdjMatch R x.1 y.1



theorem fkRectPrimalUnexplored_freeEvent_le_box
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      ∑ rho,
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (FK.boxGraph 2 (R.width + R.height)) p q rho := by
  exact FK.ocd_free_inner_le_outer_fkProb
    (fkRectPrimalUnexploredInducedGraph R S eta)
    (FK.boxGraph 2 (R.width + R.height))
    (fkRectPrimalUnexploredBoxEmbedding R S eta)
    (fkRectPrimalUnexploredBoxEmbedding_injective R S eta)
    (fkRectPrimalUnexplored_boxAdjMatch R S eta)
    hp hp1 hq hA



theorem fkRectPrimalUnexplored_freeEvent_le_freeInfinite
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 (R.width + R.height) ⁻¹'
          (FK.ocd_innerRestrict
            (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A)) := by
  have hpre : IsIncreasing
      (FK.ocd_innerRestrict
        (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A) := by
    intro rho rho' hrho hmem
    apply hA _ hmem
    intro e
    exact hrho _
  exact (fkRectPrimalUnexplored_freeEvent_le_box
    R S eta hp hp1 hq hA).trans
      (freeBoxEvent_le_freeInfinite
        (R.width + R.height) hp hp1 hq hpre)



def FKRectPrimalUnexploredRightArmEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta) :
    Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta))) :=
  {omega | ∃ target : FKRectPrimalUnexploredVertex R S eta,
    target.1.1 = fkRectRightColumn R ∧
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) omega).Reachable
        source target}

theorem fkRectPrimalUnexploredRightArmEvent_isIncreasing
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta) :
    IsIncreasing
      (FKRectPrimalUnexploredRightArmEvent R S eta source) := by
  intro omega omega' homega
  rintro ⟨target, hright, hreach⟩
  exact ⟨target, hright,
    hreach.mono (FK.openSub_mono _ homega)⟩



theorem fkRectPrimalUnexplored_reachable_box
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (rho : ConfigSpace
      (Sym2 (FK.boxVerts 2 (R.width + R.height))))
    {x y : FKRectPrimalUnexploredVertex R S eta}
    (hreach :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) rho)).Reachable x y) :
    (FK.openSub (FK.boxGraph 2 (R.width + R.height)) rho).Reachable
      (fkRectPrimalUnexploredBoxEmbedding R S eta x)
      (fkRectPrimalUnexploredBoxEmbedding R S eta y) := by
  let f :
      FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
          (FK.ocd_innerRestrict
            (fkRectPrimalUnexploredBoxEmbedding R S eta) rho) →g
        FK.openSub (FK.boxGraph 2 (R.width + R.height)) rho :=
    { toFun := fkRectPrimalUnexploredBoxEmbedding R S eta
      map_rel' := fun {x y} hxy => by
        refine ⟨(fkRectPrimalUnexplored_boxAdjMatch R S eta x y).mp hxy.1, ?_⟩
        simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2 }
  exact hreach.map f



theorem fkRectPrimalUnexplored_rightArmCylinder_subset_boxConnections
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta) :
    FK.boxRestrict 2 (R.width + R.height) ⁻¹'
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
            FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆
      ⋃ target : FKRectPrimalUnexploredVertex R S eta,
        ⋃ _ : target.1.1 = fkRectRightColumn R,
          FK.boxConnEvent 2 (R.width + R.height)
            (fkRectPrimalUnexploredBoxEmbedding R S eta source)
            (fkRectPrimalUnexploredBoxEmbedding R S eta target) := by
  intro omega homega
  rcases homega with ⟨target, hright, hreach⟩
  simp only [Set.mem_iUnion]
  refine ⟨target, hright, ?_⟩
  exact fkRectPrimalUnexplored_reachable_box R S eta
    (FK.boxRestrict 2 (R.width + R.height) omega) hreach



theorem fkRectLeftRightSquareDisplacement_not_mem_box
    (R : FKRectTorus) (i z : Fin R.height) :
    -fkRectVertexSquareSite R (fkRectLeftColumn R, i) +
        fkRectVertexSquareSite R (fkRectRightColumn R, z) ∉
      box 2 (R.width - 2) := by
  let du : Int :=
    (fkRectVertexSquareSite R (fkRectRightColumn R, z) 0) -
      fkRectVertexSquareSite R (fkRectLeftColumn R, i) 0
  let dv : Int :=
    (fkRectVertexSquareSite R (fkRectRightColumn R, z) 1) -
      fkRectVertexSquareSite R (fkRectLeftColumn R, i) 1
  have hsum : (2 : Int) * R.width - 3 ≤ du + dv := by
    dsimp [du, dv, fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint,
      fkRectLeftColumn, fkRectRightColumn]
    have hi := i.isLt
    have hz := z.isLt
    have hw := R.width_gt_two
    omega
  intro hbox
  have h0 := hbox (0 : Fin 2)
  have h1 := hbox (1 : Fin 2)
  have h0' : du.natAbs ≤ R.width - 2 := by
    dsimp [du]
    simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, add_comm] using h0
  have h1' : dv.natAbs ≤ R.width - 2 := by
    dsimp [dv]
    simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, add_comm] using h1
  have h0Int : (du.natAbs : Int) ≤ (R.width - 2 : Nat) := by
    exact_mod_cast h0'
  have h1Int : (dv.natAbs : Int) ≤ (R.width - 2 : Nat) := by
    exact_mod_cast h1'
  have hdu : du ≤ (du.natAbs : Int) := Int.le_natAbs
  have hdv : dv ≤ (dv.natAbs : Int) := Int.le_natAbs
  have hw := R.width_gt_two
  omega



theorem fkRectBox_reachable_global
    (N : Nat) (omega : ConfigSpace (Sym2 (Site 2)))
    {x y : FK.boxVerts 2 N}
    (hreach :
      (FK.openSub (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega)).Reachable
        x y) :
    Connected 2 omega x.1 y.1 := by
  let f :
      FK.openSub (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega) →g
        openSubgraph 2 omega :=
    { toFun := Subtype.val
      map_rel' := fun {x y} hxy => by
        refine ⟨hxy.1, ?_⟩
        simpa [FK.boxRestrict, FK.edgeIncl, FK.ocd_innerEdge_mk] using hxy.2 }
  exact hreach.map f



theorem fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta)
    (hleft : source.1.1 = fkRectLeftColumn R) :
    let sourceSite :=
      (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
    let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
    FK.boxRestrict 2 (R.width + R.height) ⁻¹'
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
            FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆
      (ConfigSpace.shift g) ⁻¹' FK.boxBdryConnEvent 2 (R.width - 2) := by
  dsimp only
  intro omega homega
  rcases homega with ⟨target, hright, hreach⟩
  have hboxReach := fkRectPrimalUnexplored_reachable_box R S eta
    (FK.boxRestrict 2 (R.width + R.height) omega) hreach
  have hconn := fkRectBox_reachable_global
    (R.width + R.height) omega hboxReach
  let sourceSite : Site 2 :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
  let targetSite : Site 2 :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta target).1
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
  have hs : sourceSite =
      fkRectVertexSquareSite R (fkRectLeftColumn R, source.1.2) := by
    change fkRectVertexSquareSite R source.1 = _
    rw [show source.1 = (fkRectLeftColumn R, source.1.2) from
      Prod.ext hleft rfl]
  have ht : targetSite =
      fkRectVertexSquareSite R (fkRectRightColumn R, target.1.2) := by
    change fkRectVertexSquareSite R target.1 = _
    rw [show target.1 = (fkRectRightColumn R, target.1.2) from
      Prod.ext hright rfl]
  have hgsource : g • sourceSite = StatMech.Percolation.origin 2 := by
    funext j
    simp [g, StatMech.Percolation.smul_site_apply,
      StatMech.Percolation.origin]
  have hshiftConn :
      StatMech.Lattice.Connected 2 (ConfigSpace.shift g omega)
        (StatMech.Percolation.origin 2) (g • targetSite) := by
    rw [← hgsource]
    exact (StatMech.Percolation.connected_shift
      g omega sourceSite targetSite).2 hconn
  have houtside : g • targetSite ∉ box 2 (R.width - 2) := by
    have hout := fkRectLeftRightSquareDisplacement_not_mem_box
      R source.1.2 target.1.2
    rw [← hs, ← ht] at hout
    simpa [g, StatMech.Percolation.smul_site_apply] using hout
  exact FK.connectionEvent_subset_boxBdryConnEvent
    (R.width - 2) (by have := R.width_gt_two; omega : 1 ≤ R.width - 2)
    (g • targetSite) houtside hshiftConn



theorem fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta)
    (hleft : source.1.1 = fkRectLeftColumn R)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ omega,
        (FKRectPrimalUnexploredRightArmEvent R S eta source).indicator
            (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  let sourceSite :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
  let C := FK.boxRestrict 2 (R.width + R.height) ⁻¹'
    (FK.ocd_innerRestrict
      (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
        FKRectPrimalUnexploredRightArmEvent R S eta source)
  have hdomain := fkRectPrimalUnexplored_freeEvent_le_freeInfinite
    R S eta hp hp1 hq
      (fkRectPrimalUnexploredRightArmEvent_isIncreasing R S eta source)
  have hsubset : C ⊆
      (ConfigSpace.shift g) ⁻¹' FK.boxBdryConnEvent 2 (R.width - 2) := by
    simpa [C, sourceSite, g] using
      (fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry
        R S eta source hleft)
  have hmono : mu.real C ≤
      mu.real ((ConfigSpace.shift g) ⁻¹'
        FK.boxBdryConnEvent 2 (R.width - 2)) :=
    measureReal_mono hsubset
  have hinv := FK.fkgqt_freeIV_isTranslationInvariant
    (d := 2) hp hp1 hq
  have hinvEvent := hinv.measure_preimage g
    (FK.isClopen_boxBdryConnEvent 2 (R.width - 2)).isOpen.measurableSet
  have hreal :
      mu.real ((ConfigSpace.shift g) ⁻¹'
          FK.boxBdryConnEvent 2 (R.width - 2)) =
        mu.real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
    exact congrArg ENNReal.toReal hinvEvent
  exact hdomain.trans (hmono.trans_eq hreal)

end

end StatMech.FrontierD

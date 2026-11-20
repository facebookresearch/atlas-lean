/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Code.Universality.RSWStripSymmetry
import Code.Universality.RSWLowestCrossing
import Code.FK.MonoBC
import Code.FK.IvProperties
import Code.Percolation.PcUpperViaFK
import Code.Percolation.OffClusterIndep
import Code.Probability.InhomogeneousProduct

open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.FK
open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem rq1_halfBernoulliMeasure_eq {E : Type*} [Countable E] :
    bernoulliProductMeasure (E := E)
        (⟨(1 : ℝ) / 2, by norm_num⟩ : ℝ≥0)
          (by
            change (1 : ℝ) / 2 ≤ 1
            norm_num) =
      bernoulliProductMeasure (E := E) (2⁻¹ : ℝ≥0) half_le_one := by
  have hp : (⟨(1 : ℝ) / 2, by norm_num⟩ : ℝ≥0) = (2⁻¹ : ℝ≥0) := by
    ext
    norm_num
  unfold bernoulliProductMeasure
  congr 1
  funext e
  exact bernoulliMeasure_congr _ _ hp

omit [DecidableEq V] in

theorem rq1_bcWeight_one (C : SimpleGraph V) [DecidableRel C.Adj]
    (p : ℝ) (omega : ConfigSpace (Sym2 V)) :
    bcWeight G C p 1 omega = edgeProduct G p omega := by
  simp [bcWeight]



theorem rq1_bcProb_one_eq_fkProb (C : SimpleGraph V) [DecidableRel C.Adj]
    (p : ℝ) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p 1 omega = fkProb G p 1 omega := by
  simp [bcProb, bcZ, bcWeight, fkProb, fkZ, fkWeight]



theorem rq1_bcEventMass_one_eq_bernoulli
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V)))
    (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V))) :
    ∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p 1 omega =
      (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩
        (by exact_mod_cast hp1.le)).real A := by
  simp_rw [rq1_bcProb_one_eq_fkProb G C p]
  exact fkProbOne_event_eq_bernoulli G hp hp1 A hA





def rq1_finiteMixedSquareEvent (n : ℕ) :
    Set (ConfigSpace (Sym2 (boxVerts 2 n))) :=
  extendEdge 2 n ⁻¹'
    horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)

private theorem rq1_centeredRect_subset_box (n : ℕ) :
    rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ) ⊆ box 2 n := by
  intro z hz
  rw [mem_rect] at hz
  rw [mem_box]
  intro i
  fin_cases i
  · change (z 0).natAbs ≤ n
    by_cases h0 : 0 ≤ z 0
    · have hcast : (((z 0).natAbs : ℕ) : ℤ) = z 0 :=
        Int.natAbs_of_nonneg h0
      omega
    · have hcast : (((z 0).natAbs : ℕ) : ℤ) = -z 0 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega
  · change (z 1).natAbs ≤ n
    by_cases h1 : 0 ≤ z 1
    · have hcast : (((z 1).natAbs : ℕ) : ℤ) = z 1 :=
        Int.natAbs_of_nonneg h1
      omega
    · have hcast : (((z 1).natAbs : ℕ) : ℤ) = -z 1 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega

private theorem rq1_extendEdge_centered_pair (n : ℕ)
    (eta : ConfigSpace (Sym2 (boxVerts 2 n))) {x y : Site 2}
    (hx : x ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
    (hy : y ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :
    extendEdge 2 n eta s(x, y) =
      eta s((⟨x, rq1_centeredRect_subset_box n hx⟩ : boxVerts 2 n),
        (⟨y, rq1_centeredRect_subset_box n hy⟩ : boxVerts 2 n)) := by
  let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n hx⟩
  let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n hy⟩
  have heq : edgeIncl 2 n s(xb, yb) = s(x, y) := by
    simp [edgeIncl, Sym2.map_mk, xb, yb]
  rw [← heq, extendEdge_eq_of_range]



theorem rq1_finiteMixedSquareEvent_dependsOn (n : ℕ) :
    _root_.DependsOn
      ((rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)))
      ((boxGraph 2 n).edgeFinset : Set (Sym2 (boxVerts 2 n))) := by
  intro eta eta' hagree
  have hgraph : openSubgraphInduce 2 (extendEdge 2 n eta)
        (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) =
      openSubgraphInduce 2 (extendEdge 2 n eta')
        (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
    apply SimpleGraph.ext
    ext x y
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n x.2⟩
      let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 n).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_centered_pair n eta x.2 y.2] at hopen
      rw [rq1_extendEdge_centered_pair n eta' x.2 y.2]
      exact heq ▸ hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 n := ⟨x, rq1_centeredRect_subset_box n x.2⟩
      let yb : boxVerts 2 n := ⟨y, rq1_centeredRect_subset_box n y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 n).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_centered_pair n eta' x.2 y.2] at hopen
      rw [rq1_extendEdge_centered_pair n eta x.2 y.2]
      exact heq.symm ▸ hopen
  have hevent : eta ∈ rq1_finiteMixedSquareEvent n ↔
      eta' ∈ rq1_finiteMixedSquareEvent n := by
    change HorizontalCrossing (extendEdge 2 n eta) _ _ _ _ ↔
      HorizontalCrossing (extendEdge 2 n eta') _ _ _ _
    unfold HorizontalCrossing ConnectedWithin
    rw [hgraph]
  by_cases heta : eta ∈ rq1_finiteMixedSquareEvent n
  · rw [Set.indicator_of_mem heta, Set.indicator_of_mem (hevent.mp heta)]
  · rw [Set.indicator_of_notMem heta,
      Set.indicator_of_notMem (fun h => heta (hevent.mpr h))]

private theorem rq1_extend_restrict_centered_pair (n : ℕ)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (hx : x ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
    (hy : y ∈ rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :
    extendEdge 2 n (boxRestrict 2 n omega) s(x, y) = omega s(x, y) := by
  rw [rq1_extendEdge_centered_pair n (boxRestrict 2 n omega) hx hy]
  simp [boxRestrict, edgeIncl, Sym2.map_mk]



theorem rq1_finiteMixedSquareEvent_preimage (n : ℕ) :
    boxRestrict 2 n ⁻¹' rq1_finiteMixedSquareEvent n =
      horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ) := by
  ext omega
  change HorizontalCrossing (extendEdge 2 n (boxRestrict 2 n omega)) _ _ _ _ ↔
    HorizontalCrossing omega _ _ _ _
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
      (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv => rq1_extend_restrict_centered_pair n omega hu hv)).mp hxy
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ))
      (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv => rq1_extend_restrict_centered_pair n omega hu hv)).mpr hxy





theorem rq1_centeredSquare_crossing_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have hbase := rlc_square_half (2 * (n : ℤ)) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * (n : ℤ)) 0 (2 * (n : ℤ))
    (![-(n : ℤ), -(n : ℤ)] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * (n : ℤ)) 0 (2 * (n : ℤ)))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * (n : ℤ)) 0 (2 * (n : ℤ))) := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      zero_add, show 2 * (n : ℤ) + -(n : ℤ) = n by ring] using htrans
  rwa [heq]



theorem rq1_finiteBernoulli_mixedSquare_eq (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (boxVerts 2 n))
      (2⁻¹ : ℝ≥0) half_le_one).real (rq1_finiteMixedSquareEvent n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have hrestrict := bernoulliProduct_boxRestrict_preimage
    (d := 2) (2⁻¹ : ℝ≥0) half_le_one n (rq1_finiteMixedSquareEvent n)
  rw [rq1_finiteMixedSquareEvent_preimage] at hrestrict
  simpa [rba_selfDualMeasure] using hrestrict.symm



theorem rq1_bcMixedSquare_crossing_half (n : ℕ) (hn : 0 < n)
    (C : SimpleGraph (boxVerts 2 n)) [DecidableRel C.Adj] :
    (1 : ℝ) / 2 ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          bcProb (boxGraph 2 n) C ((1 : ℝ) / 2) 1 eta := by
  simp_rw [rq1_bcProb_one_eq_fkProb (boxGraph 2 n) C ((1 : ℝ) / 2)]
  calc
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) :=
      rq1_centeredSquare_crossing_half n hn
    _ = (bernoulliProductMeasure (E := Sym2 (boxVerts 2 n))
          (2⁻¹ : ℝ≥0) half_le_one).real (rq1_finiteMixedSquareEvent n) :=
      (rq1_finiteBernoulli_mixedSquare_eq n).symm
    _ = ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          fkProb (boxGraph 2 n) ((1 : ℝ) / 2) 1 eta := by
      symm
      rw [← rq1_halfBernoulliMeasure_eq]
      exact fkProbOne_event_eq_bernoulli (boxGraph 2 n)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
        (rq1_finiteMixedSquareEvent n) (rq1_finiteMixedSquareEvent_dependsOn n)





def rq1_mixedSquareWiring (n : ℕ) : SimpleGraph (boxVerts 2 n) where
  Adj x y := x ≠ y ∧
    (((x : Site 2) 1 = -(n : ℤ) ∧ (y : Site 2) 1 = -(n : ℤ)) ∨
      ((x : Site 2) 1 = (n : ℤ) ∧ (y : Site 2) 1 = (n : ℤ)))
  symm := by
    rintro x y ⟨hne, h⟩
    refine ⟨Ne.symm hne, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance (n : ℕ) : DecidableRel (rq1_mixedSquareWiring n).Adj := by
  intro x y
  exact Classical.dec _


theorem rq1_mixedSquareWiring_bottom_adj {n : ℕ} {x y : boxVerts 2 n}
    (hne : x ≠ y)
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = -(n : ℤ)) :
    (rq1_mixedSquareWiring n).Adj x y :=
  ⟨hne, Or.inl ⟨hx, hy⟩⟩


theorem rq1_mixedSquareWiring_top_adj {n : ℕ} {x y : boxVerts 2 n}
    (hne : x ≠ y)
    (hx : (x : Site 2) 1 = (n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    (rq1_mixedSquareWiring n).Adj x y :=
  ⟨hne, Or.inr ⟨hx, hy⟩⟩


theorem rq1_mixedSquareWiring_bottom_reachable {n : ℕ} {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = -(n : ℤ)) :
    (rq1_mixedSquareWiring n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.refl x
  · exact (rq1_mixedSquareWiring_bottom_adj hxy hx hy).reachable


theorem rq1_mixedSquareWiring_top_reachable {n : ℕ} {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = (n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    (rq1_mixedSquareWiring n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.refl x
  · exact (rq1_mixedSquareWiring_top_adj hxy hx hy).reachable

private theorem rq1_mixedSquareWiring_adj_preserves_bottom {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ))
    (hxy : (rq1_mixedSquareWiring n).Adj x y) :
    (y : Site 2) 1 = -(n : ℤ) := by
  rcases hxy.2 with hbottom | htop
  · exact hbottom.2
  · omega


theorem rq1_mixedSquareWiring_reachable_preserves_bottom {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ))
    (hxy : (rq1_mixedSquareWiring n).Reachable x y) :
    (y : Site 2) 1 = -(n : ℤ) := by
  have hwalk : ∀ {u v : boxVerts 2 n},
      (rq1_mixedSquareWiring n).Walk u v →
      (u : Site 2) 1 = -(n : ℤ) → (v : Site 2) 1 = -(n : ℤ) := by
    intro u v w hu
    induction w with
    | nil => exact hu
    | @cons a b c hab w ih =>
        exact ih (rq1_mixedSquareWiring_adj_preserves_bottom hn hu hab)
  exact hxy.elim fun w => hwalk w hx



theorem rq1_mixedSquareWiring_top_bottom_not_reachable {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    ¬ (rq1_mixedSquareWiring n).Reachable x y := by
  intro hxy
  have := rq1_mixedSquareWiring_reachable_preserves_bottom hn hx hxy
  omega


theorem rq1_mixedSquareWiring_top_bottom_not_joined {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    ¬ (rq1_mixedSquareWiring n).Adj x y := by
  intro hxy
  exact rq1_mixedSquareWiring_top_bottom_not_reachable hn hx hy hxy.reachable




theorem rq1_mixedSquare_crossing_lower_bound (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (1 + 1 ^ 2) ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          bcProb (boxGraph 2 n) (rq1_mixedSquareWiring n)
            ((1 : ℝ) / 2) 1 eta := by
  norm_num
  exact rq1_bcMixedSquare_crossing_half n hn (rq1_mixedSquareWiring n)



theorem rq1_wiredSquare_crossing_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          wiredFkProb (boxGraph 2 n) (boxBoundary 2 n)
            ((1 : ℝ) / 2) 1 eta := by
  simpa only [bcProb_clique_eq_wiredFkProb] using
    rq1_bcMixedSquare_crossing_half n hn
      (StatMech.Lattice.boundaryCliqueGraph (boxBoundary 2 n))





def rq1_stripDualReflectedSquareEvent (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rss_stripDualReflection (n : ℤ) ⁻¹'
    horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)



theorem rq1_stripDualReflectedSquare_law (n : ℕ) :
    rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have h := (rss_stripDualReflection_measurePreserving (n : ℤ)).measureReal_preimage
    (rlc_horizontalCrossing_measurableSet
      (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)).nullMeasurableSet
  simpa [rq1_stripDualReflectedSquareEvent, rba_selfDualMeasure] using h



theorem rq1_stripDualReflectedSquare_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) := by
  rw [rq1_stripDualReflectedSquare_law]
  exact rq1_centeredSquare_crossing_half n hn

end Universality

end StatMech

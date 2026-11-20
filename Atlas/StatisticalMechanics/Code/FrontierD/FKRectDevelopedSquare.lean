/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutSquareEmbedding
import Code.FrontierD.FKRectRandomClusterGraphBridge
import Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Code.FrontierD.FKRectCriticalDualQuasiInvariant
import Code.RSW.Defs
import Code.BeffaraDC.TorusSquareCrossingCover



open StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section



def fkRectDevelopedSquarePoint (n : Nat) (z : Site 2) : Int × Int :=
  (z 0 + 2 * n, z 1 + n)

def fkRectDevelopedSquareSite (n : Nat) (z : Site 2) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectDevelopedSquarePoint n z)


def fkRectSquareSiteVertex (R : FKRectTorus) (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (z 0, z 1)

@[simp] theorem fkRectSquareSiteVertex_siteOfPair
    (R : FKRectTorus) (p : Int × Int) :
    fkRectSquareSiteVertex R (fkRectSquareSiteOfPair p) =
      fkRectSquareRepresentativeVertex R p := by
  rfl



theorem fkRectDevelopedSquare_sharedPrimalEdge
    (n : Nat) {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge (fkRectDevelopedSquareSite n f)
        (fkRectDevelopedSquareSite n g) =
      Sym2.map (fkRectDevelopedSquareSite n) (sharedPrimalEdge f g) := by
  let t : Site 2 := ![2 * (n : Int), (n : Int)]
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, t,
    StatMech.FK.PeriodicPlanar.siteTranslate] using
      (sharedPrimalEdge_add t f g)


def fkRectDevelopedSquareVertex (R : FKRectTorus) (n : Nat)
    (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (fkRectDevelopedSquarePoint n z)

@[simp] theorem fkRectSquareSiteVertex_developedSquareSite
    (R : FKRectTorus) (n : Nat) (z : Site 2) :
    fkRectSquareSiteVertex R (fkRectDevelopedSquareSite n z) =
      fkRectDevelopedSquareVertex R n z := by
  rfl

theorem fkRectDevelopedSquare_undevelop_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
    0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
  rw [StatMech.RSW.Box.mem_rect] at hz
  dsimp [fkRectDevelopedSquarePoint, fkRectSquareUndevelopPoint]
  constructor
  · omega
  constructor
  · have hhalf :
        (z 0 - z 1 + (n : Int)) / 2 ≤ n := by omega
    omega
  constructor <;> omega



theorem fkRectVertexSquarePoint_developedSquareVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquarePoint n z := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedSquare_undevelop_bounds R n hwidth hheight hz
  change fkRectSquareDevelopPoint
      (((fkRectSquareRepresentativeVertex R t).1.val : Int),
        ((fkRectSquareRepresentativeVertex R t).2.val : Int)) = t
  have hx : ((fkRectSquareRepresentativeVertex R t).1.val : Int) = p.1 := by
    change ((p.1.natMod R.width : Nat) : Int) = p.1
    rw [Int.natMod, Int.emod_eq_of_lt hp.1 hp.2.1]
    exact Int.natCast_toNat_eq_self.mpr hp.1
  have hy : ((fkRectSquareRepresentativeVertex R t).2.val : Int) = p.2 := by
    change ((p.2.natMod R.height : Nat) : Int) = p.2
    rw [Int.natMod, Int.emod_eq_of_lt hp.2.2.1 hp.2.2.2]
    exact Int.natCast_toNat_eq_self.mpr hp.2.2.1
  rw [hx, hy]
  exact fkRectSquareDevelopPoint_undevelopPoint t

theorem fkRectVertexSquareSite_developedSquareVertex
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareSite n z := by
  unfold fkRectVertexSquareSite fkRectDevelopedSquareSite
  rw [fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hz]



theorem fkRectDevelopedSquareVertex_fst_succ_lt
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
    (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
  let t := fkRectDevelopedSquarePoint n z
  let p := fkRectSquareUndevelopPoint t
  have hp := fkRectDevelopedSquare_undevelop_bounds R n hwidth hheight hz
  have hpoint := fkRectVertexSquarePoint_developedSquareVertex
    R n hwidth hheight hz
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx : ((fkRectDevelopedSquareVertex R n z).1.val : Int) = p.1 :=
    congrArg Prod.fst hundev
  rw [StatMech.RSW.Box.mem_rect] at hz
  have hpUpper : p.1 < 3 * (n : Int) := by
    dsimp [p, t, fkRectDevelopedSquarePoint,
      fkRectSquareUndevelopPoint]
    have hhalf :
        (z 0 - z 1 + (n : Int)) / 2 ≤ n := by omega
    omega
  exact_mod_cast (show
    ((fkRectDevelopedSquareVertex R n z).1.val : Int) + 1 < R.width by
      omega)


theorem fkRectDevelopedSquareVertex_injective_on
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height) :
    Set.InjOn (fkRectDevelopedSquareVertex R n)
      (StatMech.RSW.Box.rect 0 n 0 n) := by
  intro z hz w hw hzw
  have hs := congrArg (fkRectVertexSquarePoint R) hzw
  rw [fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hz,
    fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hw] at hs
  change (z 0 + 2 * (n : Int), z 1 + (n : Int)) =
    (w 0 + 2 * (n : Int), w 1 + (n : Int)) at hs
  have h0 := congrArg Prod.fst hs
  have h1 := congrArg Prod.snd hs
  apply funext
  intro i
  fin_cases i
  · exact add_right_cancel h0
  · exact add_right_cancel h1



theorem fkRectDevelopedSquareVertex_cutGraph_adj
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {z w : Site 2} (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    (fkRectCutGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) := by
  rw [fkRectCutGraph_adj_iff_hypercubicAdj,
    fkRectVertexSquareSite_developedSquareVertex R n hwidth hheight hz,
    fkRectVertexSquareSite_developedSquareVertex R n hwidth hheight hw]
  rw [hypercubicLattice_adj] at hzw ⊢
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, Fin.sum_univ_two] using hzw



theorem fkRectLiftedDualEdge_sharedPrimalEdge
    (R : FKRectTorus) (e : R.EdgeIndex)
    (he : e ∉ fkRectTorusCutEdges R)
    (hd : fkRectEdgeToDualEdge R e ∉ fkRectTorusCutEdges R) :
    let d := fkRectEdgeToDualEdge R e
    let df := fkRectLiftedIndexedEdgeEnds R d
    let ep := fkRectLiftedIndexedEdgeEnds R e
    sharedPrimalEdge
        (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.1))
        (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.2)) =
      Sym2.map fkRectSquareSiteOfPair
        s(fkRectSquareDevelopPoint ep.1,
          fkRectSquareDevelopPoint ep.2) := by
  rcases e with ⟨b, x, y⟩
  cases b
  · have hx0 : x.val ≠ 0 := by
      intro hx
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hx]
    have hy0 : y.val ≠ 0 := by
      intro hy
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hy]
    have hxpred : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    have hxne : (x.val : Int) ≠ (x.val : Int) - 1 := by omega
    by_cases heven : Even y.val
    · obtain ⟨k, hk⟩ := heven
      have heven' : Even y.val := ⟨k, hk⟩
      have hyInt : (y.val : Int) = 2 * (k : Int) := by
        exact_mod_cast (show y.val = 2 * k by omega)
      have hdivSucc : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivPred : (2 * (k : Int) - 1) / 2 = k - 1 := by
        have : (0 : Int) < k := by omega
        omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven', hyInt, hxpred, hxne, hdivSucc, hdivPred] <;> omega
    · have hodd : Odd y.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hyInt : (y.val : Int) = 2 * (k : Int) + 1 := by exact_mod_cast hk
      have hdiv : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivSucc : (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven, hyInt, hxpred, hxne, hdiv, hdivSucc] <;> omega
  · have hy0 : y.val ≠ 0 := by
      intro hy
      apply he
      simp [mem_fkRectTorusCutEdges_iff, hy]
    have hx0 : x.val ≠ 0 := by
      intro hx
      apply hd
      simp [fkRectEdgeToDualEdge, mem_fkRectTorusCutEdges_iff, hx]
    have hxpred : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    have hxne : (x.val : Int) ≠ (x.val : Int) - 1 := by omega
    by_cases heven : Even y.val
    · obtain ⟨k, hk⟩ := heven
      have heven' : Even y.val := ⟨k, hk⟩
      have hyInt : (y.val : Int) = 2 * (k : Int) := by
        exact_mod_cast (show y.val = 2 * k by omega)
      have hdivSucc : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivPred : (2 * (k : Int) - 1) / 2 = k - 1 := by
        have : (0 : Int) < k := by omega
        omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven', hyInt, hxpred, hxne, hdivSucc, hdivPred] <;> omega
    · have hodd : Odd y.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hyInt : (y.val : Int) = 2 * (k : Int) + 1 := by exact_mod_cast hk
      have hdiv : (2 * (k : Int) + 1) / 2 = k := by omega
      have hdivSucc : (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega
      simp [fkRectEdgeToDualEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectSquareDevelopPoint, fkRectSquareSiteOfPair,
        sharedPrimalEdge, fkRectCyclicPred_val, hx0, hy0,
        heven, hyInt, hxpred, hxne, hdiv, hdivSucc] <;> omega



theorem fkRectDualEdgeToEdge_not_cut_of_developedSquare
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {f g : Site 2} (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (d : R.EdgeIndex)
    (hedge : fkRectTorusIndexedEdge R d =
      s(fkRectDevelopedSquareVertex R n f,
        fkRectDevelopedSquareVertex R n g))
    (hd : d ∉ fkRectTorusCutEdges R) :
    fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
  rcases d with ⟨b, x, y⟩
  cases b
  · have hxy : y.val ≠ 0 ∧ x.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    simpa [fkRectDualEdgeToEdge,
      mem_fkRectTorusCutEdges_iff] using hxy.1
  · have hy0 : y.val ≠ 0 := by
      simpa [mem_fkRectTorusCutEdges_iff] using hd
    have hedge' := hedge
    simp only [fkRectTorusIndexedEdge, if_pos] at hedge'
    have hxface : x = (fkRectDevelopedSquareVertex R n f).1 ∨
        x = (fkRectDevelopedSquareVertex R n g).1 := by
      rcases Sym2.eq_iff.mp hedge' with h | h
      · exact Or.inl (congrArg Prod.fst h.1)
      · exact Or.inr (congrArg Prod.fst h.1)
    have hxsucc : x.val + 1 < R.width := by
      rcases hxface with hx | hx
      · rw [hx]
        exact fkRectDevelopedSquareVertex_fst_succ_lt R n hn
          hwidth hheight hf
      · rw [hx]
        exact fkRectDevelopedSquareVertex_fst_succ_lt R n hn
          hwidth hheight hg
    have hsucc : (finitePeriodicSucc R.width_pos x).val = x.val + 1 := by
      rw [finitePeriodicSucc_val]
      simp [ne_of_lt hxsucc]
    rw [mem_fkRectTorusCutEdges_iff]
    simp [fkRectDualEdgeToEdge, hy0, hsucc]



def fkRectDevelopedSquarePullback (R : FKRectTorus) (n : Nat)
    (omega : R.Configuration) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => fkRectFullGraphConfiguration R omega
    (Sym2.map (fkRectDevelopedSquareVertex R n) e)

theorem fkRectDevelopedSquarePullback_mono
    (R : FKRectTorus) (n : Nat) {omega tau : R.Configuration}
    (hot : omega ≤ tau) :
    fkRectDevelopedSquarePullback R n omega ≤
      fkRectDevelopedSquarePullback R n tau := by
  intro e
  unfold fkRectDevelopedSquarePullback fkRectFullGraphConfiguration
  split
  · exact hot _
  · rfl



theorem fkRectDevelopedSquarePullback_open_iff
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) {z w : Site 2}
    (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔
      (fkRectOpenGraph R omega).Adj
        (fkRectDevelopedSquareVertex R n z)
        (fkRectDevelopedSquareVertex R n w) := by
  have hcut := fkRectDevelopedSquareVertex_cutGraph_adj R n
    hwidth hheight hz hw hzw
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) :=
    ((fkRectCutGraph_adj_iff R _ _).mp hcut).1
  rw [← fkOpenSub_fullGraphConfiguration]
  rw [StatMech.FK.openSub_adj]
  constructor
  · intro hopen
    refine ⟨htorus, ?_⟩
    simpa [fkRectDevelopedSquarePullback] using hopen
  · rintro ⟨_, hopen⟩
    simpa [fkRectDevelopedSquarePullback] using hopen



noncomputable def fkRectDevelopedSquareOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (StatMech.RSW.Box.rect 0 n 0 n) →g
      fkRectOpenGraph R omega where
  toFun z := fkRectDevelopedSquareVertex R n z
  map_rel' := by
    intro z w hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n omega)).Adj z.1 w.1 at hzw
    rw [openSubgraph_adj] at hzw
    exact (fkRectDevelopedSquarePullback_open_iff R n hwidth hheight
      omega z.2 w.2 hzw.1).mp hzw.2


def fkRectDevelopedSquareHorizontalCrossingEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | StatMech.RSW.Box.HorizontalCrossing
    (fkRectDevelopedSquarePullback R n omega) 0 n 0 n}

theorem fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing
    (R : FKRectTorus) (n : Nat) :
    IsIncreasing (fkRectDevelopedSquareHorizontalCrossingEvent R n) := by
  intro omega tau hot hcross
  exact StatMech.RSW.Box.horizontalCrossingEvent_increasing
    (fkRectDevelopedSquarePullback_mono R n hot) hcross



def fkRectDevelopedSquareFaceDualVerticalEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | StatMech.RSW.Box.VerticalCrossing
    (StatMech.Universality.fci_faceDualConfig
      (fkRectDevelopedSquarePullback R n omega)) 0 n 0 n}


theorem fkRectDevelopedSquare_compl_subset_faceDualVertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n) :
    (fkRectDevelopedSquareHorizontalCrossingEvent R n)ᶜ ⊆
      fkRectDevelopedSquareFaceDualVerticalEvent R n := by
  intro omega hno
  have hband : StatMech.RSW.Box.VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))
      0 ((n : Int) - 1) (-1) n := by
    exact StatMech.Universality.crr_square_compl_subset_faceDualRect_unconditional
      (n : Int) (by omega) hno
  exact StatMech.BeffaraDC.torus_faceBand_verticalCrossing_to_square
    (by omega) hband



theorem fkRectDevelopedSquare_faceDual_adj_imp_dual_adj
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) {f g : Site 2}
    (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hfg : (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj
      (fkRectDevelopedSquareVertex R n f)
      (fkRectDevelopedSquareVertex R n g) := by
  rw [openSubgraph_adj] at hfg
  obtain ⟨hlat, hopen⟩ := hfg
  have hcut := fkRectDevelopedSquareVertex_cutGraph_adj R n
    hwidth hheight hf hg hlat
  obtain ⟨⟨d, hedge⟩, hcutEdge⟩ :=
    (fkRectCutGraph_adj_iff R _ _).mp hcut
  have hd : d ∉ fkRectTorusCutEdges R := by
    intro hd
    apply hcutEdge
    rw [← hedge, mem_fkRectTorusCutGraphEdges]
    exact hd
  let e := fkRectDualEdgeToEdge R d
  have he : e ∉ fkRectTorusCutEdges R :=
    fkRectDualEdgeToEdge_not_cut_of_developedSquare R n hn
      hwidth hheight hf hg d hedge hd
  have hde : fkRectEdgeToDualEdge R e = d := by
    simp [e]
  let dp := fkRectLiftedIndexedEdgeEnds R d
  let ep := fkRectLiftedIndexedEdgeEnds R e
  have hproject :
      s(fkRectLiftedVertex R dp.1, fkRectLiftedVertex R dp.2) =
        s(fkRectDevelopedSquareVertex R n f,
          fkRectDevelopedSquareVertex R n g) := by
    rw [← fkRectLiftedIndexedEdgeEnds_project R d]
    exact hedge
  have hsites := congrArg (Sym2.map (fkRectVertexSquareSite R)) hproject
  have hd1 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut R d hd
  have hd2 :=
    fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂ R d hd
  have hsites' :
      s(fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1),
          fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
        s(fkRectDevelopedSquareSite n f,
          fkRectDevelopedSquareSite n g) := by
    simp only [Sym2.map_pair_eq] at hsites
    rw [fkRectVertexSquareSite_developedSquareVertex R n
          hwidth hheight hf,
        fkRectVertexSquareSite_developedSquareVertex R n
          hwidth hheight hg] at hsites
    change s(fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.1)),
        fkRectSquareSiteOfPair
          (fkRectVertexSquarePoint R (fkRectLiftedVertex R dp.2))) = _ at hsites
    rw [← hd1, ← hd2] at hsites
    exact hsites
  have htadj : (hypercubicLattice 2).Adj
      (fkRectDevelopedSquareSite n f)
      (fkRectDevelopedSquareSite n g) := by
    rw [hypercubicLattice_adj] at hlat ⊢
    simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
      fkRectSquareSiteOfPair, Fin.sum_univ_two] using hlat
  have hshared :
      sharedPrimalEdge (fkRectDevelopedSquareSite n f)
          (fkRectDevelopedSquareSite n g) =
        sharedPrimalEdge
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
          (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) := by
    rcases Sym2.eq_iff.mp hsites' with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact sharedPrimalEdge_comm_of_adj htadj
  have hcross := fkRectLiftedDualEdge_sharedPrimalEdge R e he (by
    simpa [hde] using hd)
  dsimp only at hcross
  rw [hde] at hcross
  change sharedPrimalEdge
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.1))
      (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint dp.2)) =
    Sym2.map fkRectSquareSiteOfPair
      s(fkRectSquareDevelopPoint ep.1,
        fkRectSquareDevelopPoint ep.2) at hcross
  have hplane := hshared.trans hcross
  have hmapped := congrArg (Sym2.map (fkRectSquareSiteVertex R)) hplane
  rw [fkRectDevelopedSquare_sharedPrimalEdge n hlat] at hmapped
  have hedgeMap :
      Sym2.map (fkRectDevelopedSquareVertex R n)
          (sharedPrimalEdge f g) = fkRectTorusIndexedEdge R e := by
    rw [fkRectLiftedIndexedEdgeEnds_project R e]
    simpa [Sym2.map_map, Function.comp_def,
      fkRectSquareRepresentativeVertex_developPoint, ep] using hmapped
  have hpull : fkRectDevelopedSquarePullback R n omega
      (sharedPrimalEdge f g) = false := by
    rw [StatMech.Universality.fci_faceDualConfig,
      StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj hlat] at hopen
    cases hval : fkRectDevelopedSquarePullback R n omega
        (sharedPrimalEdge f g) <;> simp_all
  have heclosed : omega e = false := by
    unfold fkRectDevelopedSquarePullback at hpull
    rw [hedgeMap, fkRectFullGraphConfiguration_indexedEdge] at hpull
    exact hpull
  refine ⟨d, ?_, hedge⟩
  rw [← hde, fkRectDualConfigurationEquiv_apply_edgeToDualEdge]
  simpa [heclosed]



noncomputable def fkRectDevelopedSquareFaceDualToDualPullbackHom
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).induce
          (StatMech.RSW.Box.rect 0 n 0 n) →g
      (openSubgraph 2
        (fkRectDevelopedSquarePullback R n
          (fkRectDualConfigurationEquiv R omega))).induce
            (StatMech.RSW.Box.rect 0 n 0 n) where
  toFun z := ⟨z.1, z.2⟩
  map_rel' := by
    intro z w hzw
    have htorus := fkRectDevelopedSquare_faceDual_adj_imp_dual_adj
      R n hn hwidth hheight omega z.2 w.2 hzw
    change (openSubgraph 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))).Adj z.1 w.1 at hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))).Adj z.1 w.1
    rw [openSubgraph_adj] at hzw ⊢
    exact ⟨hzw.1, (fkRectDevelopedSquarePullback_open_iff
      R n hwidth hheight (fkRectDualConfigurationEquiv R omega)
      z.2 w.2 hzw.1).mpr htorus⟩



theorem fkRectDevelopedSquare_faceDualVertical_imp_dualVertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration)
    (hcross : StatMech.RSW.Box.VerticalCrossing
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega)) 0 n 0 n) :
    StatMech.RSW.Box.VerticalCrossing
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega)) 0 n 0 n := by
  obtain ⟨xb, yt, hconn⟩ := hcross
  refine ⟨xb, yt, ?_⟩
  exact hconn.map
    (fkRectDevelopedSquareFaceDualToDualPullbackHom
      R n hn hwidth hheight omega)


def fkRectDevelopedSquareVerticalCrossingEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | StatMech.RSW.Box.VerticalCrossing
    (fkRectDevelopedSquarePullback R n omega) 0 n 0 n}

theorem fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing
    (R : FKRectTorus) (n : Nat) :
    IsIncreasing (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  intro omega tau hot hcross
  exact StatMech.RSW.Box.verticalCrossingEvent_increasing
    (fkRectDevelopedSquarePullback_mono R n hot) hcross


def fkRectDevelopedSquareCrossingEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  fkRectDevelopedSquareHorizontalCrossingEvent R n ∪
    fkRectDevelopedSquareVerticalCrossingEvent R n

theorem fkRectDevelopedSquareCrossingEvent_isIncreasing
    (R : FKRectTorus) (n : Nat) :
    IsIncreasing (fkRectDevelopedSquareCrossingEvent R n) := by
  intro omega tau hot hcross
  rcases hcross with hcross | hcross
  · exact Or.inl
      (fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing
        R n hot hcross)
  · exact Or.inr
      (fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing
        R n hot hcross)



theorem fkRectDevelopedSquare_dualCompl_subset_crossing
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height) :
    fkRectDualEvent R (fkRectDevelopedSquareCrossingEvent R n)ᶜ ⊆
      fkRectDevelopedSquareCrossingEvent R n := by
  rintro eta ⟨omega, hno, rfl⟩
  have hnoHorizontal :
      omega ∉ fkRectDevelopedSquareHorizontalCrossingEvent R n := by
    intro hcross
    exact hno (Or.inl hcross)
  have hface := fkRectDevelopedSquare_compl_subset_faceDualVertical
    R n hn hnoHorizontal
  exact Or.inr
    (fkRectDevelopedSquare_faceDualVertical_imp_dualVertical
      R n hn hwidth hheight omega hface)



theorem fkRectDevelopedSquareCrossing_ge_one_div_one_add_q
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedSquareCrossingEvent R n) := by
  exact one_div_one_add_q_le_eventMass_of_dualCompl_subset R hq _
    (fkRectDevelopedSquare_dualCompl_subset_crossing
      R n hn hwidth hheight)



theorem fkRectDevelopedSquare_exists_direction_crossing_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
        (fkRectDevelopedSquareHorizontalCrossingEvent R n) ∨
      1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
        (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  have hlower := fkRectDevelopedSquareCrossing_ge_one_div_one_add_q
    R n hn hwidth hheight hq
  have hupper := fkRectCriticalEventMass_union_le_add R
    (zero_lt_one.trans_le hq)
    (fkRectDevelopedSquareHorizontalCrossingEvent R n)
    (fkRectDevelopedSquareVerticalCrossingEvent R n)
  have hcross : 1 / (1 + q) ≤
      fkRectCriticalEventMass R q
          (fkRectDevelopedSquareHorizontalCrossingEvent R n) +
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
    exact hlower.trans (by
      simpa [fkRectDevelopedSquareCrossingEvent] using hupper)
  have hhalf : 1 / (2 * (1 + q)) = (1 / (1 + q)) / 2 := by
    have hden : 1 + q ≠ 0 := by linarith
    field_simp
  rw [hhalf]
  by_contra h
  push_neg at h
  linarith


noncomputable def fkRectDevelopedSquareHorizontalEndpointPairs (n : Nat) :
    Finset ((StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) := by
  classical
  letI := (StatMech.RSW.Box.rect_finite 0 n 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 0 = 0 ∧ p.2.1 0 = n


noncomputable def fkRectDevelopedSquareVerticalEndpointPairs (n : Nat) :
    Finset ((StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) := by
  classical
  letI := (StatMech.RSW.Box.rect_finite 0 n 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 1 = 0 ∧ p.2.1 1 = n

theorem mem_fkRectDevelopedSquareHorizontalEndpointPairs
    (n : Nat) (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n ↔
      p.1.1 0 = 0 ∧ p.2.1 0 = n := by
  classical
  unfold fkRectDevelopedSquareHorizontalEndpointPairs
  simp

theorem mem_fkRectDevelopedSquareVerticalEndpointPairs
    (n : Nat) (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    p ∈ fkRectDevelopedSquareVerticalEndpointPairs n ↔
      p.1.1 1 = 0 ∧ p.2.1 1 = n := by
  classical
  unfold fkRectDevelopedSquareVerticalEndpointPairs
  simp


def fkRectDevelopedSquareEndpointConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) : Set R.Configuration :=
  {omega | StatMech.Lattice.ConnectedWithin 2
    (fkRectDevelopedSquarePullback R n omega)
    (StatMech.RSW.Box.rect 0 n 0 n) p.1 p.2}

theorem fkRectDevelopedSquareEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    IsIncreasing (fkRectDevelopedSquareEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  exact StatMech.TwoDim.connectedWithin_mono
    (fkRectDevelopedSquarePullback_mono R n hot) hconn



theorem fkRectDevelopedSquareEndpointConnection_imp_torusReachable
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n))
    (hconn : omega ∈ fkRectDevelopedSquareEndpointConnectionEvent R n p) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectDevelopedSquareVertex R n p.1)
      (fkRectDevelopedSquareVertex R n p.2) := by
  exact hconn.map (fkRectDevelopedSquareOpenHom
    R n hwidth hheight omega)



def fkRectDevelopedSquareTorusEndpointConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) : Set R.Configuration :=
  {omega | (fkRectOpenGraph R omega).Reachable
    (fkRectDevelopedSquareVertex R n p.1)
    (fkRectDevelopedSquareVertex R n p.2)}

theorem fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
    (R : FKRectTorus) (n : Nat)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    IsIncreasing
      (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) := by
  intro omega tau hot hconn
  apply hconn.mono
  apply fkRectOpenGraph_mono R
  intro e he
  have hle := hot e
  rw [he] at hle
  exact top_le_iff.mp hle

theorem fkRectDevelopedSquareEndpointConnection_subset_torus
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (p : (StatMech.RSW.Box.rect 0 n 0 n) ×
      (StatMech.RSW.Box.rect 0 n 0 n)) :
    fkRectDevelopedSquareEndpointConnectionEvent R n p ⊆
      fkRectDevelopedSquareTorusEndpointConnectionEvent R n p := by
  intro omega hconn
  exact fkRectDevelopedSquareEndpointConnection_imp_torusReachable
    R n hwidth hheight omega p hconn

theorem fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedSquareHorizontalCrossingEvent R n =
      fkRectFiniteEventUnion
        (fkRectDevelopedSquareHorizontalEndpointPairs n)
        (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (StatMech.RSW.Box.rect 0 n 0 n) ×
        (StatMech.RSW.Box.rect 0 n 0 n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedSquareHorizontalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedSquareEndpointConnectionEvent, p] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 0 = 0 ∧ p.2.1 0 = n := by
      classical
      simpa [fkRectDevelopedSquareHorizontalEndpointPairs] using hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedSquareEndpointConnectionEvent] using hxy

theorem fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedSquareVerticalCrossingEvent R n =
      fkRectFiniteEventUnion
        (fkRectDevelopedSquareVerticalEndpointPairs n)
        (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (StatMech.RSW.Box.rect 0 n 0 n) ×
        (StatMech.RSW.Box.rect 0 n 0 n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedSquareVerticalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedSquareEndpointConnectionEvent, p] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 1 = 0 ∧ p.2.1 1 = n := by
      classical
      simpa [fkRectDevelopedSquareVerticalEndpointPairs] using hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedSquareEndpointConnectionEvent] using hxy

theorem fkRectDevelopedSquareHorizontalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedSquareHorizontalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![(n : Int), 0]
  have hx : x ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, x]
  have hy : y ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedSquareHorizontalEndpointPairs, x, y]

theorem fkRectDevelopedSquareVerticalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedSquareVerticalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![0, (n : Int)]
  have hx : x ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, x]
  have hy : y ∈ StatMech.RSW.Box.rect 0 n 0 n := by
    simp [StatMech.RSW.Box.mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedSquareVerticalEndpointPairs, x, y]



theorem fkRectDevelopedSquareHorizontalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedSquareHorizontalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
  classical
  let encode : {p // p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n} →
      Fin (n + 1) × Fin (n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 1), by
        have hp := p.1.1.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 1), by
        have hp := p.1.2.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds : p.1.1.1 0 = 0 ∧ p.1.2.1 0 = n := by
      exact (mem_fkRectDevelopedSquareHorizontalEndpointPairs n p.1).mp p.2
    have hrEnds : r.1.1.1 0 = 0 ∧ r.1.2.1 0 = n := by
      exact (mem_fkRectDevelopedSquareHorizontalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 1) =
        Int.toNat (r.1.1.1 1) :=
      congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 1) =
        Int.toNat (r.1.2.1 1) :=
      congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    rw [StatMech.RSW.Box.mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.1.trans hrEnds.1.symm
      · calc
          p.1.1.1 1 = (Int.toNat (p.1.1.1 1) : Int) :=
            (Int.toNat_of_nonneg hp1.2.2.1).symm
          _ = (Int.toNat (r.1.1.1 1) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 1 := Int.toNat_of_nonneg hr1.2.2.1
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.2.trans hrEnds.2.symm
      · calc
          p.1.2.1 1 = (Int.toNat (p.1.2.1 1) : Int) :=
            (Int.toNat_of_nonneg hp2.2.2.1).symm
          _ = (Int.toNat (r.1.2.1 1) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 1 := Int.toNat_of_nonneg hr2.2.2.1
  rw [← Fintype.card_coe]
  calc
    Fintype.card {p // p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n} ≤
        Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
      Fintype.card_le_of_injective encode hinj
    _ = (n + 1) ^ 2 := by simp [pow_two]



theorem fkRectDevelopedSquareVerticalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedSquareVerticalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
  classical
  let encode : {p // p ∈ fkRectDevelopedSquareVerticalEndpointPairs n} →
      Fin (n + 1) × Fin (n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 0), by
        have hp := p.1.1.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 0), by
        have hp := p.1.2.2
        rw [StatMech.RSW.Box.mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds : p.1.1.1 1 = 0 ∧ p.1.2.1 1 = n := by
      exact (mem_fkRectDevelopedSquareVerticalEndpointPairs n p.1).mp p.2
    have hrEnds : r.1.1.1 1 = 0 ∧ r.1.2.1 1 = n := by
      exact (mem_fkRectDevelopedSquareVerticalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 0) =
        Int.toNat (r.1.1.1 0) :=
      congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 0) =
        Int.toNat (r.1.2.1 0) :=
      congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    rw [StatMech.RSW.Box.mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.1.1 0 = (Int.toNat (p.1.1.1 0) : Int) :=
            (Int.toNat_of_nonneg hp1.1).symm
          _ = (Int.toNat (r.1.1.1 0) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 0 := Int.toNat_of_nonneg hr1.1
      · exact hpEnds.1.trans hrEnds.1.symm
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · calc
          p.1.2.1 0 = (Int.toNat (p.1.2.1 0) : Int) :=
            (Int.toNat_of_nonneg hp2.1).symm
          _ = (Int.toNat (r.1.2.1 0) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 0 := Int.toNat_of_nonneg hr2.1
      · exact hpEnds.2.trans hrEnds.2.symm
  rw [← Fintype.card_coe]
  calc
    Fintype.card {p // p ∈ fkRectDevelopedSquareVerticalEndpointPairs n} ≤
        Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
      Fintype.card_le_of_injective encode hinj
    _ = (n + 1) ^ 2 := by simp [pow_two]



theorem fkRectDevelopedSquare_exists_endpoint_connection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_direction_crossing_ge
      R n hn hwidth hheight hq with hhorizontal | hvertical
  · left
    rw [fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion]
      at hhorizontal
    exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedSquareHorizontalEndpointPairs_nonempty n)
      (fkRectDevelopedSquareEndpointConnectionEvent R n) hhorizontal
  · right
    rw [fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion]
      at hvertical
    exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedSquareVerticalEndpointPairs_nonempty n)
      (fkRectDevelopedSquareEndpointConnectionEvent R n) hvertical



theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤
        ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_endpoint_connection_ge
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_left
    · exact fkRectCriticalEventMass_mono R
        (zero_lt_one.trans_le hq)
        (fkRectDevelopedSquareEndpointConnection_subset_torus
          R n hwidth hheight p)
    · positivity
  · right
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_left
    · exact fkRectCriticalEventMass_mono R
        (zero_lt_one.trans_le hq)
        (fkRectDevelopedSquareEndpointConnection_subset_torus
          R n hwidth hheight p)
    · positivity


theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast
        fkRectDevelopedSquareHorizontalEndpointPairs_card_le n
    · exact fkRectCriticalEventMass_nonneg R
        (zero_lt_one.trans_le hq) _
  · right
    refine ⟨p, hp, hlower.trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast fkRectDevelopedSquareVerticalEndpointPairs_card_le n
    · exact fkRectCriticalEventMass_nonneg R
        (zero_lt_one.trans_le hq) _



theorem fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤
        fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  have hk : (0 : Real) < (((n + 1) ^ 2 : Nat) : Real) := by positivity
  have hqden : (0 : Real) < 2 * (1 + q) := by positivity
  have hreassoc :
      1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) =
        (1 / (2 * (1 + q))) / (((n + 1) ^ 2 : Nat) : Real) := by
    field_simp
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, ?_⟩
    rw [hreassoc, div_le_iff₀ hk]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_comm] using hlower
  · right
    refine ⟨p, hp, ?_⟩
    rw [hreassoc, div_le_iff₀ hk]
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_comm] using hlower



theorem fkRectDevelopedSquare_exists_fkg_attached_torus_endpoint
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) (B : Set R.Configuration)
    (hB : IsIncreasing B) :
    (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n,
      (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) *
          fkRectCriticalEventMass R q B ≤
        fkRectCriticalEventMass R q
          (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨
    (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n,
      (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) *
          fkRectCriticalEventMass R q B ≤
        fkRectCriticalEventMass R q
          (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
  rcases fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div
      R n hn hwidth hheight hq with
    ⟨p, hp, hlower⟩ | ⟨p, hp, hlower⟩
  · left
    refine ⟨p, hp, ?_⟩
    calc
      _ ≤ fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) *
            fkRectCriticalEventMass R q B :=
        mul_le_mul_of_nonneg_right hlower
          (fkRectCriticalEventMass_nonneg R
            (zero_lt_one.trans_le hq) B)
      _ = fkRectCriticalEventMass R q B *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) :=
        mul_comm _ _
      _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
        (fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
          R n p)
  · right
    refine ⟨p, hp, ?_⟩
    calc
      _ ≤ fkRectCriticalEventMass R q
          (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) *
            fkRectCriticalEventMass R q B :=
        mul_le_mul_of_nonneg_right hlower
          (fkRectCriticalEventMass_nonneg R
            (zero_lt_one.trans_le hq) B)
      _ = fkRectCriticalEventMass R q B *
          fkRectCriticalEventMass R q
            (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) :=
        mul_comm _ _
      _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
        (fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing
          R n p)

end

end StatMech.FrontierD

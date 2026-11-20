/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedSquare
import Code.FrontierD.FKRectRightStripConnection
import Code.FK.FKGeneralQConnectionSymmetry



open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph

namespace StatMech.FrontierD

noncomputable section


theorem hypercubicLattice_two_adj_add_left (a x y : Site 2) :
    (hypercubicLattice 2).Adj (a + x) (a + y) ↔
      (hypercubicLattice 2).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  have hsum :
      (∑ i, ((a + x) i - (a + y) i).natAbs) =
        ∑ i, (x i - y i).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hsum]



theorem fkRectCutGraph_adj_of_torusAdj_of_pos
    (R : FKRectTorus) (x y : R.Vertex)
    (hxcol : 0 < x.1.val) (hycol : 0 < y.1.val)
    (hxrow : 0 < x.2.val) (hyrow : 0 < y.2.val)
    (hxy : (fkRectTorusGraph R).Adj x y) :
    (fkRectCutGraph R).Adj x y := by
  apply (fkRectCutGraph_adj_iff R x y).2
  refine ⟨hxy, ?_⟩
  intro hcut
  rw [fkRectTorusCutGraphEdges, Finset.mem_image] at hcut
  obtain ⟨a, ha, hedge⟩ := hcut
  rw [mem_fkRectTorusCutEdges_iff] at ha
  rcases a with ⟨b, col, row⟩
  rcases ha with hrow | ⟨hb, hcol⟩
  · change row.val = 0 at hrow
    have hzero : row.val = 0 := hrow
    cases b with
    | false =>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false] at hedge
      by_cases heven : Even row.val
      · simp only [heven, if_true] at hedge
        rcases Sym2.eq_iff.mp hedge with h | h
        · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
        · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
      · simp only [heven, if_false] at hedge
        rcases Sym2.eq_iff.mp hedge with h | h
        · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
        · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
    | true =>
      simp only [fkRectTorusIndexedEdge, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
      · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
  · change b = false at hb
    change col.val = 0 at hcol
    subst b
    have hzero : col.val = 0 := hcol
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false] at hedge
    by_cases heven : Even row.val
    · simp only [heven, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hxcol.ne' (congrArg (fun v => v.1.val) h.1.symm |>.trans hzero)
      · exact hycol.ne' (congrArg (fun v => v.1.val) h.1.symm |>.trans hzero)
    · simp only [heven, if_false] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hycol.ne' (congrArg (fun v => v.1.val) h.2.symm |>.trans hzero)
      · exact hxcol.ne' (congrArg (fun v => v.1.val) h.2.symm |>.trans hzero)



def fkRectLocalBoxPoint (R : FKRectTorus) (center : R.Vertex)
    (z : Site 2) : Int × Int :=
  ((fkRectVertexSquarePoint R center).1 + z 0,
    (fkRectVertexSquarePoint R center).2 + z 1)


def fkRectLocalBoxVertex (R : FKRectTorus) (center : R.Vertex)
    (z : Site 2) : R.Vertex :=
  fkRectSquareRepresentativeVertex R (fkRectLocalBoxPoint R center z)

@[simp] theorem fkRectSquareRepresentativeVertex_vertexSquarePoint
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectSquareRepresentativeVertex R (fkRectVertexSquarePoint R x) = x := by
  rw [show fkRectVertexSquarePoint R x =
      fkRectSquareDevelopPoint ((x.1.val : Int), (x.2.val : Int)) by rfl,
    fkRectSquareRepresentativeVertex_developPoint]
  apply Prod.ext
  · exact fkRectIntModFin_natCast R.width_pos x.1
  · exact fkRectIntModFin_natCast R.height_pos x.2


def fkRectLocalBoxOrigin (m : Nat) : FK.boxVerts 2 m :=
  ⟨origin 2, fun i => by simp [origin]⟩


def fkRectReflectedDiagonalSite (s : Nat) : Site 2 :=
  ![(s : Int), -(s : Int)]

def fkRectPositiveDiagonalSite (s : Nat) : Site 2 :=
  ![(s : Int), (s : Int)]

theorem fkRectReflectedDiagonalSite_mem_box
    {s m : Nat} (hsm : s <= m) :
    fkRectReflectedDiagonalSite s ∈ box 2 m := by
  intro i
  fin_cases i <;> simp [fkRectReflectedDiagonalSite, hsm]

def fkRectLocalBoxReflectedDiagonal (s m : Nat) (hsm : s <= m) :
    FK.boxVerts 2 m :=
  ⟨fkRectReflectedDiagonalSite s,
    fkRectReflectedDiagonalSite_mem_box hsm⟩

theorem fkRectPositiveDiagonalSite_mem_box
    {s m : Nat} (hsm : s <= m) :
    fkRectPositiveDiagonalSite s ∈ box 2 m := by
  intro i
  fin_cases i <;> simp [fkRectPositiveDiagonalSite, hsm]

def fkRectLocalBoxPositiveDiagonal (s m : Nat) (hsm : s <= m) :
    FK.boxVerts 2 m :=
  ⟨fkRectPositiveDiagonalSite s,
    fkRectPositiveDiagonalSite_mem_box hsm⟩

theorem fk_twoPointFun_eq_connProb
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : Real) (x y : V) :
    FK.twoPointFun G p q x y = FK.connProb G p q x y := by
  rw [FK.twoPointFun_eq_sum_filter]
  rfl



theorem fkRectLocalBox_twoPoint_reflectedDiagonal_eq
    (m s : Nat) (hsm : s <= m) (p q : Real) :
    FK.twoPointFun (FK.boxGraph 2 m) p q
        (fkRectLocalBoxOrigin m)
        (fkRectLocalBoxReflectedDiagonal s m hsm) =
      FK.twoPointFun (FK.boxGraph 2 m) p q
        (fkRectLocalBoxOrigin m)
        (fkRectLocalBoxPositiveDiagonal s m hsm) := by
  rw [fk_twoPointFun_eq_connProb, fk_twoPointFun_eq_connProb]
  have hsym := FK.connProb_boxSym (FK.fkTI_signFlip 2 (1 : Fin 2))
    m p q (fkRectLocalBoxOrigin m)
      (fkRectLocalBoxPositiveDiagonal s m hsm)
  have horigin :
      (FK.fkTI_signFlip 2 (1 : Fin 2)).lift m
          (fkRectLocalBoxOrigin m) = fkRectLocalBoxOrigin m := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [FK.BoxSym.lift, FK.fkTI_signFlip, FK.fkTI_signFlipEquiv,
        fkRectLocalBoxOrigin, origin]
  have hdiag :
      (FK.fkTI_signFlip 2 (1 : Fin 2)).lift m
          (fkRectLocalBoxPositiveDiagonal s m hsm) =
        fkRectLocalBoxReflectedDiagonal s m hsm := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [FK.BoxSym.lift, FK.fkTI_signFlip, FK.fkTI_signFlipEquiv,
        fkRectLocalBoxPositiveDiagonal, fkRectPositiveDiagonalSite,
        fkRectLocalBoxReflectedDiagonal, fkRectReflectedDiagonalSite]
  rw [horigin, hdiag] at hsym
  exact hsym

@[simp] theorem fkRectLocalBoxVertex_origin
    (R : FKRectTorus) (center : R.Vertex) :
    fkRectLocalBoxVertex R center (origin 2) = center := by
  unfold fkRectLocalBoxVertex
  rw [show fkRectLocalBoxPoint R center (origin 2) =
      fkRectVertexSquarePoint R center by
        apply Prod.ext <;> simp [fkRectLocalBoxPoint, origin]]
  exact fkRectSquareRepresentativeVertex_vertexSquarePoint R center

theorem fkRectLocalBoxVertex_reflectedDiagonal_eq
    (R : FKRectTorus) (center target : R.Vertex) (s : Nat)
    (hstep : fkRectVertexSquarePoint R target -
        fkRectVertexSquarePoint R center = ((s : Int), -(s : Int))) :
    fkRectLocalBoxVertex R center (fkRectReflectedDiagonalSite s) = target := by
  unfold fkRectLocalBoxVertex
  rw [show fkRectLocalBoxPoint R center (fkRectReflectedDiagonalSite s) =
      fkRectVertexSquarePoint R target by
        apply Prod.ext
        · have h := congrArg Prod.fst hstep
          simp [fkRectLocalBoxPoint, fkRectReflectedDiagonalSite] at h ⊢
          omega
        · have h := congrArg Prod.snd hstep
          simp [fkRectLocalBoxPoint, fkRectReflectedDiagonalSite] at h ⊢
          omega]
  exact fkRectSquareRepresentativeVertex_vertexSquarePoint R target



def FKRectLocalBoxFits (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) : Prop :=
  upper < R.height ∧ ∀ z : FK.boxVerts 2 m,
    let p := fkRectSquareUndevelopPoint (fkRectLocalBoxPoint R center z)
    (cut : Int) <= p.1 ∧ p.1 < R.width ∧
      (lower : Int) <= p.2 ∧ p.2 <= upper



theorem fkRectLocalBoxFits_of_margin
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hupper : upper < R.height)
    (hcolLower : cut + 2 * m <= center.1.val)
    (hcolUpper : center.1.val + 2 * m < R.width)
    (hrowLower : lower + 2 * m <= center.2.val)
    (hrowUpper : center.2.val + 2 * m <= upper) :
    FKRectLocalBoxFits R center m cut lower upper := by
  refine ⟨hupper, ?_⟩
  intro z
  have hz := z.2
  rw [mem_box] at hz
  have hz0 := hz 0
  have hz1 := hz 1
  dsimp [fkRectLocalBoxPoint, fkRectVertexSquarePoint,
    fkRectSquareDevelopPoint, fkRectSquareUndevelopPoint]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

@[simp] theorem fkRectSquareSiteOfPair_localBoxPoint
    (R : FKRectTorus) (center : R.Vertex) (z : Site 2) :
    fkRectSquareSiteOfPair (fkRectLocalBoxPoint R center z) =
      fkRectVertexSquareSite R center + z := by
  funext i
  fin_cases i <;>
    simp [fkRectSquareSiteOfPair, fkRectLocalBoxPoint,
      fkRectVertexSquareSite]



theorem fkRectVertexSquarePoint_localBoxVertex
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper)
    (z : FK.boxVerts 2 m) :
    fkRectVertexSquarePoint R (fkRectLocalBoxVertex R center z) =
      fkRectLocalBoxPoint R center z := by
  let t := fkRectLocalBoxPoint R center z
  let p := fkRectSquareUndevelopPoint t
  have hp := hfit.2 z
  have hp0 : (0 : Int) <= p.1 :=
    (Int.natCast_nonneg cut).trans hp.1
  have hp2 : (0 : Int) <= p.2 :=
    (Int.natCast_nonneg lower).trans hp.2.2.1
  have hp2lt : p.2 < (R.height : Int) := by
    exact hp.2.2.2.trans_lt (by exact_mod_cast hfit.1)
  change fkRectSquareDevelopPoint
      (((fkRectSquareRepresentativeVertex R t).1.val : Int),
        ((fkRectSquareRepresentativeVertex R t).2.val : Int)) = t
  have hx : ((fkRectSquareRepresentativeVertex R t).1.val : Int) = p.1 := by
    change ((p.1.natMod R.width : Nat) : Int) = p.1
    rw [Int.natMod, Int.emod_eq_of_lt hp0 hp.2.1]
    exact Int.natCast_toNat_eq_self.mpr hp0
  have hy : ((fkRectSquareRepresentativeVertex R t).2.val : Int) = p.2 := by
    change ((p.2.natMod R.height : Nat) : Int) = p.2
    rw [Int.natMod, Int.emod_eq_of_lt hp2 hp2lt]
    exact Int.natCast_toNat_eq_self.mpr hp2
  rw [hx, hy]
  exact fkRectSquareDevelopPoint_undevelopPoint t


def fkRectLocalBoxEmbedding
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    FK.boxVerts 2 m -> FKRectRightStripBandVertex R cut lower upper :=
  fun z => ⟨fkRectLocalBoxVertex R center z, by
    let p := fkRectSquareUndevelopPoint (fkRectLocalBoxPoint R center z)
    have hp := hfit.2 z
    have hpoint := fkRectVertexSquarePoint_localBoxVertex
      R center m cut lower upper hfit z
    have hundev := congrArg fkRectSquareUndevelopPoint hpoint
    simp only [fkRectVertexSquarePoint,
      fkRectSquareUndevelopPoint_developPoint] at hundev
    have hx : ((fkRectLocalBoxVertex R center z).1.val : Int) = p.1 :=
      congrArg Prod.fst hundev
    have hy : ((fkRectLocalBoxVertex R center z).2.val : Int) = p.2 :=
      congrArg Prod.snd hundev
    change cut <= (fkRectLocalBoxVertex R center z).1.val ∧
      lower <= (fkRectLocalBoxVertex R center z).2.val ∧
      (fkRectLocalBoxVertex R center z).2.val <= upper
    constructor
    · exact_mod_cast (hx.symm ▸ hp.1)
    constructor
    · exact_mod_cast (hy.symm ▸ hp.2.2.1)
    · exact_mod_cast (hy.symm ▸ hp.2.2.2)⟩

theorem fkRectLocalBoxEmbedding_injective
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    Function.Injective
      (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
  intro z w hzw
  have hv : fkRectLocalBoxVertex R center z =
      fkRectLocalBoxVertex R center w := congrArg Subtype.val hzw
  have hp := congrArg (fkRectVertexSquarePoint R) hv
  rw [fkRectVertexSquarePoint_localBoxVertex R center m cut lower upper hfit z,
    fkRectVertexSquarePoint_localBoxVertex R center m cut lower upper hfit w] at hp
  apply Subtype.ext
  funext i
  fin_cases i
  · exact add_left_cancel (congrArg Prod.fst hp)
  · exact add_left_cancel (congrArg Prod.snd hp)


theorem fkRectLocalBoxEmbedding_adjMatch
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    FK.ocd_AdjMatch (FK.boxGraph 2 m)
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
      (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
  intro z w
  change (hypercubicLattice 2).Adj z.1 w.1 ↔
    (fkRectTorusGraph R).Adj
      (fkRectLocalBoxVertex R center z)
      (fkRectLocalBoxVertex R center w)
  constructor
  · intro hzw
    have htranslated : (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R center + z.1)
        (fkRectVertexSquareSite R center + w.1) :=
      (hypercubicLattice_two_adj_add_left
        (fkRectVertexSquareSite R center) z.1 w.1).2 hzw
    have hcutAdj : (fkRectCutGraph R).Adj
        (fkRectLocalBoxVertex R center z)
        (fkRectLocalBoxVertex R center w) := by
      rw [fkRectCutGraph_adj_iff_hypercubicAdj]
      simp only [fkRectVertexSquareSite]
      rw [fkRectVertexSquarePoint_localBoxVertex
          R center m cut lower upper hfit z,
        fkRectVertexSquarePoint_localBoxVertex
          R center m cut lower upper hfit w]
      simpa using htranslated
    exact ((fkRectCutGraph_adj_iff R _ _).1 hcutAdj).1
  · intro hzw
    have hzmem := (fkRectLocalBoxEmbedding
      R center m cut lower upper hfit z).2
    have hwmem := (fkRectLocalBoxEmbedding
      R center m cut lower upper hfit w).2
    have hcutAdj := fkRectCutGraph_adj_of_torusAdj_of_pos R
      (fkRectLocalBoxVertex R center z)
      (fkRectLocalBoxVertex R center w)
      (Nat.zero_lt_one.trans_le (hcut.trans hzmem.1))
      (Nat.zero_lt_one.trans_le (hcut.trans hwmem.1))
      (Nat.zero_lt_one.trans_le (hlower.trans hzmem.2.1))
      (Nat.zero_lt_one.trans_le (hlower.trans hwmem.2.1)) hzw
    have htranslated := (fkRectCutGraph_adj_iff_hypercubicAdj R _ _).1 hcutAdj
    simp only [fkRectVertexSquareSite] at htranslated
    rw [fkRectVertexSquarePoint_localBoxVertex
        R center m cut lower upper hfit z,
      fkRectVertexSquarePoint_localBoxVertex
        R center m cut lower upper hfit w] at htranslated
    have htranslated' : (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R center + z.1)
        (fkRectVertexSquareSite R center + w.1) := by
      simpa using htranslated
    exact (hypercubicLattice_two_adj_add_left
      (fkRectVertexSquareSite R center) z.1 w.1).1 htranslated'



theorem fkRectLocalBox_twoPoint_le_strip
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center m cut lower upper)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y : FK.boxVerts 2 m) :
    FK.twoPointFun (FK.boxGraph 2 m) p q x y <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut lower upper)) p q
        (fkRectLocalBoxEmbedding R center m cut lower upper hfit x)
        (fkRectLocalBoxEmbedding R center m cut lower upper hfit y) := by
  let incl := fkRectLocalBoxEmbedding R center m cut lower upper hfit
  have hinj : Function.Injective incl :=
    fkRectLocalBoxEmbedding_injective R center m cut lower upper hfit
  have hadj : FK.ocd_AdjMatch (FK.boxGraph 2 m)
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) incl :=
    fkRectLocalBoxEmbedding_adjMatch R center m cut lower upper
      hcut hlower hfit
  have hsubset :
      FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y ⊆
        FK.connEvent
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper)) (incl x) (incl y) := by
    intro rho hrho
    change (FK.openSub (FK.boxGraph 2 m)
      (FK.ocd_innerRestrict incl rho)).Reachable x y at hrho
    change (FK.openSub
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
      rho).Reachable (incl x) (incl y)
    let hom : FK.openSub (FK.boxGraph 2 m)
        (FK.ocd_innerRestrict incl rho) →g
        FK.openSub
          (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
          rho :=
      { toFun := incl
        map_rel' := by
          intro a b hab
          rw [FK.openSub_adj] at hab ⊢
          refine ⟨(hadj a b).1 hab.1, ?_⟩
          simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hab.2 }
    exact hrho.map hom
  have hdom := FK.bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := FK.connEvent (FK.boxGraph 2 m) x y)
    (FK.connEvent_isIncreasing (FK.boxGraph 2 m) x y)
  unfold FK.twoPointFun
  calc
    (∑ omega, FK.fkProb (FK.boxGraph 2 m) p q omega *
        (FK.connEvent (FK.boxGraph 2 m) x y).indicator
          (fun _ => (1 : Real)) omega) =
      ∑ omega, (FK.connEvent (FK.boxGraph 2 m) x y).indicator
          (fun _ => (1 : Real)) omega *
        FK.fkProb (FK.boxGraph 2 m) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ <= ∑ rho,
        (FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho := hdom
    _ <= ∑ rho,
        FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho *
          (FK.connEvent
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper))
              (incl x) (incl y)).indicator (fun _ => (1 : Real)) rho := by
      apply Finset.sum_le_sum
      intro rho _
      by_cases hin : rho ∈ FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y
      · have hout := hsubset hin
        rw [Set.indicator_of_mem hin, Set.indicator_of_mem hout]
        simpa only [one_mul, mul_one] using
          (le_refl (FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho))
      · rw [Set.indicator_of_notMem hin, zero_mul]
        exact mul_nonneg
          (FK.fkProb_nonneg
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper))
            hp hp1 (zero_lt_one.trans_le hq) rho)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)

end

end StatMech.FrontierD

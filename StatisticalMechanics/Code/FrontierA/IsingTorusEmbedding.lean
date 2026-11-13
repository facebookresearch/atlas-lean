/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusGraph
import Code.FrontierA.IsingDyadicGreenRiemann
import Code.Percolation.PcNontrivial
import Code.Sharpness.IsingSusceptibilityPlus
import Code.Ising.FiniteVolumeRelabel
import Code.FrontierA.IsingCriticalSimonMass

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.Lattice
open StatMech.Percolation

variable {d k R : Nat}

theorem isingSiteToDyadicTorus_injectiveOn_box
    (hside : 2 * R < isingDyadicSide k) :
    Set.InjOn (isingSiteToDyadicTorus k) (box d R) := by
  intro x hx y hy hxy
  funext i
  have hi := congrFun hxy i
  change ((x i : Int) : ZMod (2 ^ (k + 2))) = (y i : Int) at hi
  have hdvd : ((2 ^ (k + 2) : Nat) : Int) ∣ y i - x i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (x i) (y i) (2 ^ (k + 2))).mp hi
  have hnat : (y i - x i).natAbs ≤ 2 * R := by
    calc
      (y i - x i).natAbs ≤ (y i).natAbs + (x i).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ R + R := Nat.add_le_add (hy i) (hx i)
      _ = 2 * R := by omega
  have habs : |y i - x i| < (isingDyadicSide k : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat.trans_lt hside
  have hzero : y i - x i = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem isingSiteToDyadicTorus_injectiveOn_finset
    (S : Finset (Site d)) (hS : ↑S ⊆ box d R)
    (hside : 2 * R < isingDyadicSide k) :
    Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)) :=
  (isingSiteToDyadicTorus_injectiveOn_box hside).mono hS

theorem isingSiteToDyadicTorus_coordShift
    (x : Site d) (i : Fin d) (b : Bool) :
    isingSiteToDyadicTorus k (coordShift x i (stepSign b)) =
      if b then
        isingSiteToDyadicTorus k x + isingTorusStep i
      else
        isingSiteToDyadicTorus k x - isingTorusStep i := by
  funext j
  by_cases hij : j = i
  · subst j
    cases b
    · simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        sub_eq_add_neg]
      have hm : ((-1 : Int) : ZMod (2 ^ (k + 2))) = -1 := by
        rw [show (-1 : Int) = -(1 : Int) by norm_num,
          Int.cast_neg, Int.cast_one]
      rw [← hm]
      exact Int.cast_add (R := ZMod (2 ^ (k + 2))) (x i) (-1)
    · simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        sub_eq_add_neg]
      simpa only [Int.cast_one] using
        (Int.cast_add (R := ZMod (2 ^ (k + 2))) (x i) 1)
  · cases b <;>
      simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        hij, sub_eq_add_neg]

theorem isingSiteToDyadicTorus_map_adj
    {x y : Site d} (hxy : (hypercubicLattice d).Adj x y) :
    (isingTorusGraph d k).Adj
      (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y) := by
  obtain ⟨i, b, rfl⟩ := adj_exists_dir hxy
  rw [isingTorusGraph_adj_iff, isingSiteToDyadicTorus_coordShift]
  by_cases hb : b
  · exact ⟨i, Or.inl (if_pos hb)⟩
  · refine ⟨i, Or.inr ?_⟩
    rw [if_neg hb]
    abel

theorem coordShift_mem_box_succ {x : Site d} (hx : x ∈ box d R)
    (i : Fin d) (b : Bool) :
    coordShift x i (stepSign b) ∈ box d (R + 1) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp only [coordShift, Function.update_self, stepSign]
    have hxi := hx i
    cases b
    · have h := Int.natAbs_sub_le (x i) 1
      norm_num at h
      exact h.trans (by omega)
    · have h := Int.natAbs_add_le (x i) 1
      norm_num at h
      exact h.trans (by omega)
  · rw [coordShift, Function.update_of_ne hji]
    exact (hx j).trans (Nat.le_succ R)

theorem isingSiteToDyadicTorus_reflects_adj_on_box
    {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hxy : (isingTorusGraph d k).Adj
      (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y)) :
    (hypercubicLattice d).Adj x y := by
  rw [isingTorusGraph_adj_iff] at hxy
  rcases hxy with ⟨i, h | h⟩
  · let z := coordShift x i (stepSign true)
    have hz : z ∈ box d (R + 1) := coordShift_mem_box_succ hx i true
    have hy' : y ∈ box d (R + 1) := box_mono d (Nat.le_succ R) hy
    have hcast : isingSiteToDyadicTorus k y =
        isingSiteToDyadicTorus k z := by
      rw [h, isingSiteToDyadicTorus_coordShift]
      simp [z]
    have hyz : y = z :=
      isingSiteToDyadicTorus_injectiveOn_box hside hy' hz hcast
    rw [hyz]
    exact adj_coordShift x i true
  · let z := coordShift y i (stepSign true)
    have hz : z ∈ box d (R + 1) := coordShift_mem_box_succ hy i true
    have hx' : x ∈ box d (R + 1) := box_mono d (Nat.le_succ R) hx
    have hcast : isingSiteToDyadicTorus k x =
        isingSiteToDyadicTorus k z := by
      rw [h, isingSiteToDyadicTorus_coordShift]
      simp [z]
    have hxz : x = z :=
      isingSiteToDyadicTorus_injectiveOn_box hside hx' hz hcast
    rw [hxz]
    exact (adj_coordShift y i true).symm


noncomputable def isingTorusImageFinset
    (k : Nat) (S : Finset (Site d)) : Finset (IsingDyadicTorus d k) :=
  S.image (isingSiteToDyadicTorus k)

@[simp] theorem mem_isingTorusImageFinset
    {S : Finset (Site d)} {z : IsingDyadicTorus d k} :
    z ∈ isingTorusImageFinset k S ↔
      ∃ x ∈ S, isingSiteToDyadicTorus k x = z := by
  simp [isingTorusImageFinset]

@[simp] theorem isingSiteToDyadicTorus_origin :
    isingSiteToDyadicTorus k (Percolation.origin d) = 0 := by
  funext i
  simp [isingSiteToDyadicTorus, Percolation.origin]
  exact Int.cast_zero

theorem zero_mem_isingTorusImageFinset
    {S : Finset (Site d)} (hzero : Percolation.origin d ∈ S) :
    (0 : IsingDyadicTorus d k) ∈ isingTorusImageFinset k S := by
  rw [mem_isingTorusImageFinset]
  exact ⟨Percolation.origin d, hzero, isingSiteToDyadicTorus_origin⟩



noncomputable def isingTorusImageEquiv
    (S : Finset (Site d))
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d))) :
    {x // x ∈ S} ≃ {z // z ∈ isingTorusImageFinset k S} where
  toFun x := ⟨isingSiteToDyadicTorus k x.1, by
    rw [mem_isingTorusImageFinset]
    exact ⟨x.1, x.2, rfl⟩⟩
  invFun z := ⟨(mem_isingTorusImageFinset.mp z.2).choose,
    (mem_isingTorusImageFinset.mp z.2).choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    let hspec := (mem_isingTorusImageFinset.mp
      ((⟨isingSiteToDyadicTorus k x.1, by
        rw [mem_isingTorusImageFinset]
        exact ⟨x.1, x.2, rfl⟩⟩ :
        {z // z ∈ isingTorusImageFinset k S}).2)).choose_spec
    exact hinj hspec.1 x.2 hspec.2
  right_inv z := by
    apply Subtype.ext
    exact (mem_isingTorusImageFinset.mp z.2).choose_spec.2

@[simp] theorem isingTorusImageEquiv_apply
    (S : Finset (Site d))
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (x : {x // x ∈ S}) :
    (isingTorusImageEquiv S hinj x).1 =
      isingSiteToDyadicTorus k x.1 := rfl

theorem isingTorusImageEquiv_adj
    (S : Finset (Site d)) (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (x y : {x // x ∈ S}) :
    (graphS d S).Adj x y ↔
      ((isingTorusGraph d k).comap
        (Subtype.val : {z // z ∈ isingTorusImageFinset k S} →
          IsingDyadicTorus d k)).Adj
        (isingTorusImageEquiv S hinj x)
        (isingTorusImageEquiv S hinj y) := by
  change (hypercubicLattice d).Adj x.1 y.1 ↔
    (isingTorusGraph d k).Adj
      (isingSiteToDyadicTorus k x.1)
      (isingSiteToDyadicTorus k y.1)
  constructor
  · exact isingSiteToDyadicTorus_map_adj
  · exact isingSiteToDyadicTorus_reflects_adj_on_box
      (hS x.2) (hS y.2) hside



theorem isingTorus_localizedTwoPoint_eq_freeCorr
    (S : Finset (Site d)) (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (beta : Real) (a b : {x // x ∈ S}) :
    twoPointJ (isingTorusGraph d k) beta
        (couplingIn (unitEdgeCoupling (isingTorusGraph d k))
          (isingTorusImageFinset k S))
        (isingSiteToDyadicTorus k a.1)
        (isingSiteToDyadicTorus k b.1) =
      freeCorr d beta S a b := by
  classical
  have hinj : Set.InjOn (isingSiteToDyadicTorus k)
      (↑S : Set (Site d)) :=
    isingSiteToDyadicTorus_injectiveOn_finset S hS
      (lt_of_lt_of_le (by omega : 2 * R < 2 * (R + 1)) hside.le)
  let T := isingTorusImageFinset k S
  have haT : isingSiteToDyadicTorus k a.1 ∈ T := by
    rw [mem_isingTorusImageFinset]
    exact ⟨a.1, a.2, rfl⟩
  have hbT : isingSiteToDyadicTorus k b.1 ∈ T := by
    rw [mem_isingTorusImageFinset]
    exact ⟨b.1, b.2, rfl⟩
  by_cases hab : a = b
  · subst b
    simp [freeCorr]
  have habVal : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  have habMap : isingSiteToDyadicTorus k a.1 ≠
      isingSiteToDyadicTorus k b.1 := by
    intro h
    exact habVal (hinj a.2 b.2 h)
  rw [freeCorr, if_neg hab]
  have hunit :
      twoPointJ (isingTorusGraph d k) beta
          (couplingIn (unitEdgeCoupling (isingTorusGraph d k)) T)
          (isingSiteToDyadicTorus k a.1)
          (isingSiteToDyadicTorus k b.1) =
        twoPointJ (isingTorusGraph d k) beta
          (couplingIn (fun _ => 1) T)
          (isingSiteToDyadicTorus k a.1)
          (isingSiteToDyadicTorus k b.1) := by
    apply twoPointJ_congr_on_edges
    intro e he
    unfold couplingIn
    split
    · rw [unitEdgeCoupling_edgeFinset (isingTorusGraph d k) he]
    · rfl
  rw [hunit, twoPointJ, sourcePair_eq_pair habMap]
  have hbase := expectationJ_couplingIn_one_eq_induced
    (isingTorusGraph d k) beta T haT hbT
  rw [hbase]
  let e := isingTorusImageEquiv S hinj
  have hrel := Ising.isingExpectation_spinProd_relabel
    (graphS d S)
    ((isingTorusGraph d k).comap
      (Subtype.val : {z // z ∈ T} → IsingDyadicTorus d k))
    e (isingTorusImageEquiv_adj S hS hside hinj) beta 0
    ({a, b} : Finset {x // x ∈ S})
  have hmap : ({a, b} : Finset {x // x ∈ S}).map e.toEmbedding =
      ({⟨isingSiteToDyadicTorus k a.1, haT⟩,
        ⟨isingSiteToDyadicTorus k b.1, hbT⟩} :
        Finset {z // z ∈ T}) := by
    ext z
    simp [e, isingTorusImageEquiv]
  rw [hmap] at hrel
  exact hrel.symm



theorem freeCorr_le_isingTorusTwoPoint
    (S : Finset (Site d)) (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (beta : Real) (hbeta : 0 ≤ beta) (a b : {x // x ∈ S}) :
    freeCorr d beta S a b ≤
      isingTorusTwoPoint beta
        (isingSiteToDyadicTorus k a.1)
        (isingSiteToDyadicTorus k b.1) := by
  rw [← isingTorus_localizedTwoPoint_eq_freeCorr S hS hside beta a b,
    isingTorusTwoPoint_eq_twoPointJ_unitEdge]
  unfold twoPointJ
  exact expectationJ_couplingIn_le (isingTorusGraph d k) beta
    (unitEdgeCoupling (isingTorusGraph d k)) hbeta
    (unitEdgeCoupling_nonneg (isingTorusGraph d k))
    (isingTorusImageFinset k S)
    (sourcePair (isingSiteToDyadicTorus k a.1)
      (isingSiteToDyadicTorus k b.1))



theorem isingTorus_simonConst_image_eq_phiIsing
    (S : Finset (Site d)) (hzero : Percolation.origin d ∈ S)
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (beta : Real) :
    simonConst (isingTorusImageFinset k S)
        (simonWeightPair (isingTorusGraph d k) beta
          (unitEdgeCoupling (isingTorusGraph d k))
          (isingTorusImageFinset k S) 0)
        (Finset.univ \ isingTorusImageFinset k S) =
      phiIsing d beta S := by
  classical
  let T := isingTorusImageFinset k S
  let C := T ×ˢ ((Finset.univ : Finset (IsingDyadicTorus d k)) \ T)
  let A := C.filter (fun p => (isingTorusGraph d k).Adj p.1 p.2)
  let F : IsingDyadicTorus d k × IsingDyadicTorus d k → Real := fun p =>
    Real.tanh (beta * unitEdgeCoupling (isingTorusGraph d k) s(p.1, p.2)) *
      twoPointJ (isingTorusGraph d k) beta
        (couplingIn (unitEdgeCoupling (isingTorusGraph d k)) T) 0 p.1
  have hdouble :
      (∑ x ∈ T, ∑ y ∈
          (Finset.univ : Finset (IsingDyadicTorus d k)) \ T, F (x, y)) =
        ∑ p ∈ A, F p := by
    rw [← Finset.sum_product]
    change (∑ p ∈ C, F p) = ∑ p ∈ C.filter _, F p
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hadj : (isingTorusGraph d k).Adj p.1 p.2
    · rw [if_pos hadj]
    · rw [if_neg hadj]
      have hcoupling : unitEdgeCoupling (isingTorusGraph d k)
          s(p.1, p.2) = 0 := by
        unfold unitEdgeCoupling
        rw [if_neg]
        simpa [SimpleGraph.mem_edgeSet] using hadj
      simp [F, hcoupling]
  have hinjBox := isingSiteToDyadicTorus_injectiveOn_box
    (d := d) hside
  have hboundary :
      (∑ p ∈ A, F p) =
        Real.tanh beta *
          ∑ e ∈ boundaryEdges d S,
            corrOriginInner d beta S e.1 := by
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_bij
      (fun e _ =>
        (isingSiteToDyadicTorus k e.1,
          isingSiteToDyadicTorus k e.2))
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      simp only [A, Finset.mem_filter, C, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, isingSiteToDyadicTorus_map_adj hadj⟩
      · rw [mem_isingTorusImageFinset]
        exact ⟨e.1, he1, rfl⟩
      · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hmem
        obtain ⟨z, hzS, hz⟩ := mem_isingTorusImageFinset.mp hmem
        have he1box := hS he1
        have he2box : e.2 ∈ box d (R + 1) := by
          obtain ⟨i, b, hib⟩ := adj_exists_dir hadj
          rw [hib]
          exact coordShift_mem_box_succ he1box i b
        have hzbox : z ∈ box d (R + 1) :=
          box_mono d (Nat.le_succ R) (hS hzS)
        have : z = e.2 := hinjBox hzbox he2box hz
        exact he2 (this ▸ hzS)
    · intro e he f hf hef
      apply Prod.ext
      · apply hinjBox
        · exact box_mono d (Nat.le_succ R)
            (hS (shk_mem_boundaryEdges_iff.mp he).1)
        · exact box_mono d (Nat.le_succ R)
            (hS (shk_mem_boundaryEdges_iff.mp hf).1)
        · exact congrArg Prod.fst hef
      · have he2box : e.2 ∈ box d (R + 1) := by
          obtain ⟨i, b, hib⟩ := adj_exists_dir
            (shk_mem_boundaryEdges_iff.mp he).2.2
          rw [hib]
          exact coordShift_mem_box_succ
            (hS (shk_mem_boundaryEdges_iff.mp he).1) i b
        have hf2box : f.2 ∈ box d (R + 1) := by
          obtain ⟨i, b, hib⟩ := adj_exists_dir
            (shk_mem_boundaryEdges_iff.mp hf).2.2
          rw [hib]
          exact coordShift_mem_box_succ
            (hS (shk_mem_boundaryEdges_iff.mp hf).1) i b
        exact hinjBox he2box hf2box (congrArg Prod.snd hef)
    · intro p hp
      simp only [A, Finset.mem_filter, C, Finset.mem_product,
        Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
      obtain ⟨x, hxS, hx⟩ := mem_isingTorusImageFinset.mp hp.1.1
      rw [← hx] at hp
      rw [isingTorusGraph_adj_iff] at hp
      rcases hp.2 with ⟨i, h | h⟩
      · let y := coordShift x i (stepSign true)
        refine ⟨(x, y), ?_, ?_⟩
        · apply shk_mem_boundaryEdges_iff.mpr
          refine ⟨hxS, ?_, adj_coordShift x i true⟩
          intro hyS
          apply hp.1.2
          rw [mem_isingTorusImageFinset]
          refine ⟨y, hyS, ?_⟩
          rw [isingSiteToDyadicTorus_coordShift]
          simpa [y] using h.symm
        · apply Prod.ext
          · exact hx
          · rw [isingSiteToDyadicTorus_coordShift]
            simpa [y] using h.symm
      · let y := coordShift x i (stepSign false)
        refine ⟨(x, y), ?_, ?_⟩
        · apply shk_mem_boundaryEdges_iff.mpr
          refine ⟨hxS, ?_, adj_coordShift x i false⟩
          intro hyS
          apply hp.1.2
          rw [mem_isingTorusImageFinset]
          refine ⟨y, hyS, ?_⟩
          rw [isingSiteToDyadicTorus_coordShift]
          simp only [Bool.false_eq_true, if_false]
          rw [h]
          abel
        · apply Prod.ext
          · exact hx
          · rw [isingSiteToDyadicTorus_coordShift]
            simp only [Bool.false_eq_true, if_false]
            rw [h]
            abel
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      have hedge : unitEdgeCoupling (isingTorusGraph d k)
          s(isingSiteToDyadicTorus k e.1,
            isingSiteToDyadicTorus k e.2) = 1 := by
        unfold unitEdgeCoupling
        rw [if_pos]
        rw [SimpleGraph.mem_edgeSet]
        exact isingSiteToDyadicTorus_map_adj hadj
      have hlocal := isingTorus_localizedTwoPoint_eq_freeCorr
        S hS hside beta
        ⟨Percolation.origin d, hzero⟩ ⟨e.1, he1⟩
      rw [isingSiteToDyadicTorus_origin] at hlocal
      have hcorr :
          twoPointJ (isingTorusGraph d k) beta
              (couplingIn (unitEdgeCoupling (isingTorusGraph d k)) T)
              0 (isingSiteToDyadicTorus k e.1) =
            corrOriginInner d beta S e.1 := by
        unfold corrOriginInner
        rw [dif_pos hzero, dif_pos he1]
        exact hlocal
      simp [F, hedge, hcorr]
  unfold simonConst simonWeightPair phiIsing
  change (∑ x ∈ T, ∑ y ∈
      (Finset.univ : Finset (IsingDyadicTorus d k)) \ T, F (x, y)) = _
  rw [hdouble, hboundary]




theorem isingTorus_susceptibility_eventually_bounded_subcritical
    (hd : 2 ≤ d) (beta : Real) (hbeta : 0 ≤ beta)
    (hlt : beta < IsingFK.betaC (Ising.magnetization d)) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ k : Nat in Filter.atTop,
        (∑ z : IsingDyadicTorus d k,
          isingTorusTwoPoint beta 0 z) ≤ C := by
  rw [isingFK_betaC_eq_tildeBetaCIsing hd] at hlt
  obtain ⟨S, hzero, hphi⟩ :=
    exists_phiIsing_witness_of_lt_tildeBetaCIsing hbeta hlt
  obtain ⟨R, hS⟩ := Lattice.finite_subset_box
    (↑S : Set (Site d)) S.finite_toSet
  let C : Real := (S.card : Real) / (1 - phiIsing d beta S)
  have hdenom : 0 < 1 - phiIsing d beta S := by linarith
  have hScard : 0 < (S.card : Real) := by
    exact_mod_cast S.card_pos.mpr ⟨Percolation.origin d, hzero⟩
  have hC : 0 < C := div_pos hScard hdenom
  refine ⟨C, hC, ?_⟩
  have hsideTendsto : Filter.Tendsto isingDyadicSide
      Filter.atTop Filter.atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  filter_upwards
      [hsideTendsto.eventually_gt_atTop (2 * (R + 1))] with k hk
  have hphiT := isingTorus_simonConst_image_eq_phiIsing
    S hzero hS hk beta
  have hbound := isingTorus_susceptibility_le_of_simon
    beta hbeta (isingTorusImageFinset k S)
    (zero_mem_isingTorusImageFinset hzero)
    (by rw [hphiT]; exact hphi)
  have hinj : Set.InjOn (isingSiteToDyadicTorus k)
      (↑S : Set (Site d)) :=
    isingSiteToDyadicTorus_injectiveOn_finset S hS (by omega)
  have hcard : (isingTorusImageFinset k S).card = S.card := by
    unfold isingTorusImageFinset
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact hinj hx hy hxy
  rw [hphiT, hcard] at hbound
  exact hbound

end StatMech.FrontierA

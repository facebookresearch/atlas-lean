/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.BeffaraDC.TorusSquareCrossingCounterexample
import Code.Universality.ConnectedRCoastClose
import Code.Universality.BXPAllAspect

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.Onsager
open StatMech.RSW.Box
open StatMech.Universality


def torusReduceSite (L : ℕ) (x : Site 2) : ZMod L × ZMod L :=
  ((x 0 : ZMod L), (x 1 : ZMod L))

@[simp] theorem torusReduceSite_mk (L : ℕ) (a b : ℤ) :
    torusReduceSite L ![a, b] = ((a : ZMod L), (b : ZMod L)) := by
  rfl


noncomputable def torusPlanarPullback (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => torusAmbientConfigExtend L omega (Sym2.map (torusReduceSite L) e)


theorem torusReduceSite_adj (L : ℕ) [Fact (2 < L)] {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (onsTorusGraph L).Adj (torusReduceSite L x) (torusReduceSite L y) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxy
  change onsTorusAdj L _ _
  unfold onsTorusAdj torusReduceSite
  have key :
      ((x 0 - y 0).natAbs = 1 ∧ (x 1 - y 1).natAbs = 0) ∨
      ((x 0 - y 0).natAbs = 0 ∧ (x 1 - y 1).natAbs = 1) := by
    omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hy : x 1 = y 1 := by omega
    right
    refine ⟨by simpa using congrArg (fun z : ℤ => (z : ZMod L)) hy, ?_⟩
    rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
    · right
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
  · have hx : x 0 = y 0 := by omega
    left
    refine ⟨by simpa using congrArg (fun z : ℤ => (z : ZMod L)) hx, ?_⟩
    rcases Int.natAbs_eq_iff.mp h1 with h | h
    · left
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
    · right
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this


noncomputable def torusPlanarPrimalHom (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    openSubgraph 2 (torusPlanarPullback L omega) →g
      FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega) where
  toFun := torusReduceSite L
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj]
    refine ⟨torusReduceSite_adj L hxy.1, ?_⟩
    simpa [torusPlanarPullback] using hxy.2



theorem torusReduceSite_val_of_mem_rect (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    (torusReduceSite L x).1.val = Int.toNat (x 0) ∧
      (torusReduceSite L x).2.val = Int.toNat (x 1) := by
  rw [mem_rect] at hx
  letI : NeZero L := ⟨by omega⟩
  have hL : (0 : ℤ) < L := by omega
  constructor
  · change (x 0 : ZMod L).val = Int.toNat (x 0)
    have hxL : x 0 < L := by omega
    apply Nat.cast_injective (R := ℤ)
    calc
      ((x 0 : ZMod L).val : ℤ) = x 0 % (L : ℤ) := ZMod.val_intCast (x 0)
      _ = x 0 := Int.emod_eq_of_lt hx.1 hxL
      _ = (Int.toNat (x 0) : ℤ) := (Int.toNat_of_nonneg hx.1).symm
  · change (x 1 : ZMod L).val = Int.toNat (x 1)
    have hxL : x 1 < L := by omega
    apply Nat.cast_injective (R := ℤ)
    calc
      ((x 1 : ZMod L).val : ℤ) = x 1 % (L : ℤ) := ZMod.val_intCast (x 1)
      _ = x 1 := Int.emod_eq_of_lt hx.2.2.1 hxL
      _ = (Int.toNat (x 1) : ℤ) := (Int.toNat_of_nonneg hx.2.2.1).symm

theorem torusReduceSite_mem_square (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    torusReduceSite L x ∈ torusSquareVertexSet L n := by
  obtain ⟨h0, h1⟩ := torusReduceSite_val_of_mem_rect L n hnL hx
  change (torusReduceSite L x).1.val ≤ n ∧
    (torusReduceSite L x).2.val ≤ n
  rw [h0, h1]
  rw [mem_rect] at hx
  omega



noncomputable def torusPlanarSquarePrimalHom (L n : ℕ) [Fact (2 < L)]
    (hnL : n < L) (omega : TorusAmbientConfig L) :
    (openSubgraph 2 (torusPlanarPullback L omega)).induce
        (rect 0 (n : ℤ) 0 (n : ℤ)) →g
      (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)).induce
        (torusSquareVertexSet L n) where
  toFun x := ⟨torusReduceSite L x, torusReduceSite_mem_square L n hnL x.2⟩
  map_rel' := by
    intro x y hxy
    exact (torusPlanarPrimalHom L omega).map_rel hxy



theorem torusPlanarHorizontalCrossing_imp_torus
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : HorizontalCrossing (torusPlanarPullback L omega)
      0 (n : ℤ) 0 (n : ℤ)) :
    torusSquareHorizontalCrossing L n omega := by
  obtain ⟨x, y, hxy⟩ := h
  have hxR : (x : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) := leftSide_subset x.2
  have hyR : (y : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) := rightSide_subset y.2
  have hxS := torusReduceSite_mem_square L n hnL hxR
  have hyS := torusReduceSite_mem_square L n hnL hyR
  refine ⟨torusReduceSite L x, torusReduceSite L y, hxS, hyS, ?_, ?_, ?_⟩
  · obtain ⟨hx0, _⟩ := torusReduceSite_val_of_mem_rect L n hnL hxR
    rw [hx0, x.2.2]
    simp
  · obtain ⟨hy0, _⟩ := torusReduceSite_val_of_mem_rect L n hnL hyR
    rw [hy0, y.2.2]
    simp
  · exact hxy.map (torusPlanarSquarePrimalHom L n hnL omega)

theorem torus_not_horizontal_imp_planar_not_horizontal
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : ¬ torusSquareHorizontalCrossing L n omega) :
    ¬ HorizontalCrossing (torusPlanarPullback L omega)
      0 (n : ℤ) 0 (n : ℤ) :=
  fun hp => h (torusPlanarHorizontalCrossing_imp_torus L n hnL omega hp)






def torusReduceSwapSite (L : ℕ) (x : Site 2) : ZMod L × ZMod L :=
  ((x 1 : ZMod L), (x 0 : ZMod L))

@[simp] theorem torusReduceSwapSite_mk (L : ℕ) (a b : ℤ) :
    torusReduceSwapSite L ![a, b] = ((b : ZMod L), (a : ZMod L)) := by
  rfl

theorem torusReduceSwapSite_adj (L : ℕ) [Fact (2 < L)] {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (onsTorusGraph L).Adj (torusReduceSwapSite L x)
      (torusReduceSwapSite L y) := by
  simpa [torusReduceSwapSite, torusReduceSite, torusCoordSwap] using
    (onsTorusGraph_adj_coordSwap L (torusReduceSite L x)
      (torusReduceSite L y)).2 (torusReduceSite_adj L hxy)

theorem torusPlanarPullback_horizontal (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) (a b : ℤ) :
    torusPlanarPullback L omega s(![a, b], ![a + 1, b]) =
      omega (torusHorizontalEdge L (a : ZMod L) (b : ZMod L)) := by
  unfold torusPlanarPullback
  rw [Sym2.map_mk]
  have he : s(torusReduceSite L ![a, b], torusReduceSite L ![a + 1, b]) =
      (torusHorizontalEdge L (a : ZMod L) (b : ZMod L) :
        Sym2 (ZMod L × ZMod L)) := by
    simp [torusReduceSite, torusHorizontalEdge_val]
  rw [he, torusAmbientConfigExtend, dif_pos (torusHorizontalEdge L _ _).2]

theorem torusPlanarPullback_vertical (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) (a b : ℤ) :
    torusPlanarPullback L omega s(![a, b], ![a, b + 1]) =
      omega (torusVerticalEdge L (a : ZMod L) (b : ZMod L)) := by
  unfold torusPlanarPullback
  rw [Sym2.map_mk]
  have he : s(torusReduceSite L ![a, b], torusReduceSite L ![a, b + 1]) =
      (torusVerticalEdge L (a : ZMod L) (b : ZMod L) :
        Sym2 (ZMod L × ZMod L)) := by
    simp [torusReduceSite, torusVerticalEdge_val]
  rw [he, torusAmbientConfigExtend, dif_pos (torusVerticalEdge L _ _).2]

theorem torusAmbientSwapEdgeEquiv_symm_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusAmbientSwapEdgeEquiv L).symm (torusHorizontalEdge L x y) =
      torusVerticalEdge L y x := by
  apply Subtype.ext
  simp [torusAmbientSwapEdgeEquiv, torusHorizontalEdge_val,
    torusVerticalEdge_val, torusCoordSwap]

theorem torusAmbientSwapEdgeEquiv_symm_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusAmbientSwapEdgeEquiv L).symm (torusVerticalEdge L x y) =
      torusHorizontalEdge L y x := by
  apply Subtype.ext
  simp [torusAmbientSwapEdgeEquiv, torusHorizontalEdge_val,
    torusVerticalEdge_val, torusCoordSwap]

@[simp] theorem torusAmbientSwapCellDual_horizontal
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) (x y : ZMod L) :
    torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)
        (torusHorizontalEdge L x y) =
      !(omega (torusHorizontalEdge L y (x + 1))) := by
  rw [torusAmbientSwapConfig, torusAmbientSwapEdgeEquiv_symm_horizontal,
    torusCellDualAmbientConfig, torusCellCrossing_symm_vertical]

@[simp] theorem torusAmbientSwapCellDual_vertical
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) (x y : ZMod L) :
    torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)
        (torusVerticalEdge L x y) =
      !(omega (torusVerticalEdge L (y + 1) x)) := by
  rw [torusAmbientSwapConfig, torusAmbientSwapEdgeEquiv_symm_vertical,
    torusCellDualAmbientConfig, torusCellCrossing_symm_horizontal]



noncomputable def torusPlanarFaceDualHom
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    openSubgraph 2 (fci_faceDualConfig (torusPlanarPullback L omega)) →g
      FK.openSub (onsTorusGraph L)
        (torusAmbientConfigExtend L
          (torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega))) where
  toFun := torusReduceSwapSite L
  map_rel' := by
    intro f g hfg
    rw [FK.openSub_adj]
    refine ⟨torusReduceSwapSite_adj L hfg.1, ?_⟩
    have hf : f = ![f 0, f 1] := by
      funext i
      fin_cases i <;> simp
    rw [hf] at hfg ⊢
    rcases crr_face_nbr_cases (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;>
      subst g
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_right] at hopen
      simp only [faceCorner10, faceCorner11] at hopen
      rw [torusPlanarPullback_vertical] at hopen
      have hclosed : omega
          (torusVerticalEdge L ((f 0 + 1 : ℤ) : ZMod L) ((f 1 : ℤ) : ZMod L)) =
          false := by simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0 + 1, f 1]) =
          (torusVerticalEdge L ((f 1 : ℤ) : ZMod L) ((f 0 : ℤ) : ZMod L) :
            Sym2 (ZMod L × ZMod L)) := by
        simp [torusReduceSwapSite, torusVerticalEdge_val]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusVerticalEdge L _ _).2,
        torusAmbientSwapCellDual_vertical]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_left] at hopen
      simp only [faceCorner00, faceCorner01] at hopen
      rw [torusPlanarPullback_vertical] at hopen
      have hclosed : omega
          (torusVerticalEdge L ((f 0 : ℤ) : ZMod L) ((f 1 : ℤ) : ZMod L)) =
          false := by simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0 - 1, f 1]) =
          (torusVerticalEdge L ((f 1 : ℤ) : ZMod L)
            (((f 0 - 1 : ℤ) : ZMod L)) : Sym2 (ZMod L × ZMod L)) := by
        rw [torusVerticalEdge_orientation_independent]
        simp [torusReduceSwapSite]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusVerticalEdge L _ _).2,
        torusAmbientSwapCellDual_vertical]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_top] at hopen
      simp only [faceCorner01, faceCorner11] at hopen
      rw [torusPlanarPullback_horizontal] at hopen
      have hclosed : omega
          (torusHorizontalEdge L ((f 0 : ℤ) : ZMod L)
            ((f 1 + 1 : ℤ) : ZMod L)) = false := by
        simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0, f 1 + 1]) =
          (torusHorizontalEdge L ((f 1 : ℤ) : ZMod L)
            ((f 0 : ℤ) : ZMod L) : Sym2 (ZMod L × ZMod L)) := by
        simp [torusReduceSwapSite, torusHorizontalEdge_val]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusHorizontalEdge L _ _).2,
        torusAmbientSwapCellDual_horizontal]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_bottom] at hopen
      simp only [faceCorner00, faceCorner10] at hopen
      rw [torusPlanarPullback_horizontal] at hopen
      have hclosed : omega
          (torusHorizontalEdge L ((f 0 : ℤ) : ZMod L)
            ((f 1 : ℤ) : ZMod L)) = false := by
        simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0, f 1 - 1]) =
          (torusHorizontalEdge L (((f 1 - 1 : ℤ) : ZMod L))
            ((f 0 : ℤ) : ZMod L) : Sym2 (ZMod L × ZMod L)) := by
        rw [torusHorizontalEdge_orientation_independent]
        simp [torusReduceSwapSite]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusHorizontalEdge L _ _).2,
        torusAmbientSwapCellDual_horizontal]
      simpa using hclosed




theorem torus_walk_first_hit_down
    {eta : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 eta).Walk x y) (i : Fin 2) (t : ℤ)
    (hx : t < x i) (hy : y i ≤ t) :
    ∃ j ≤ p.length, (p.getVert j) i = t ∧
      ∀ m < j, t < (p.getVert m) i := by
  have hlen : (p.getVert p.length) i ≤ t := by
    rw [p.getVert_length]
    exact hy
  classical
  let P : ℕ → Prop := fun m => (p.getVert m) i ≤ t
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : (p.getVert j) i ≤ t := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have habove : ∀ m < j, t < (p.getVert m) i := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : t < (p.getVert k) i := habove k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  have hdiff := bxa_adj_coord_diff_le hadj.1 i
  have habs : |(p.getVert k) i - (p.getVert (k + 1)) i| ≤ 1 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hdiff
  have hge : t ≤ (p.getVert (k + 1)) i := by
    have hstep : (p.getVert k) i - (p.getVert (k + 1)) i ≤ 1 :=
      (le_abs_self _).trans habs
    omega
  refine ⟨j, hjle, ?_, habove⟩
  have hjP' : (p.getVert k.succ) i ≤ t := by
    simpa [hk] using hjP
  have hge' : t ≤ (p.getVert k.succ) i := by
    simpa [Nat.succ_eq_add_one] using hge
  rw [hk]
  exact le_antisymm hjP' hge'





theorem torus_faceBand_verticalCrossing_to_square
    {eta : ConfigSpace (Sym2 (Site 2))} {n : ℤ} (hn : 0 < n)
    (h : VerticalCrossing eta 0 (n - 1) (-1) n) :
    VerticalCrossing eta 0 n 0 n := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxbS : (xb : Site 2) ∈ rect 0 (n - 1) (-1) n := bottomSide_subset xb.2
  have hytS : (yt : Site 2) ∈ rect 0 (n - 1) (-1) n := topSide_subset yt.2
  obtain ⟨w⟩ := hconn
  let p0 : (openSubgraph 2 eta).Walk (xb : Site 2) (yt : Site 2) :=
    w.map (SimpleGraph.Embedding.induce (rect 0 (n - 1) (-1) n)).toHom
  let p : (openSubgraph 2 eta).Walk (yt : Site 2) (xb : Site 2) := p0.reverse
  have hpsupp : ∀ z ∈ p.support, z ∈ rect 0 (n - 1) (-1) n := by
    intro z hz
    have hz0 : z ∈ p0.support := by simpa [p] using hz
    have hsupp := SimpleGraph.Walk.support_map
      (SimpleGraph.Embedding.induce (rect 0 (n - 1) (-1) n)).toHom w
    obtain ⟨z', hz', hz'eq⟩ := (List.mem_map).mp (hsupp ▸ hz0)
    rw [← hz'eq]
    exact z'.2
  have hyt1 : (yt : Site 2) 1 = n := yt.2.2
  have hxb1 : (xb : Site 2) 1 = -1 := xb.2.2
  obtain ⟨j, hjle, hju, hjabove⟩ :=
    torus_walk_first_hit_down p 1 0 (by omega) (by omega)
  let u : Site 2 := p.getVert j
  let q : (openSubgraph 2 eta).Walk (yt : Site 2) u := p.take j
  have hqsupp : ∀ z ∈ q.support, z ∈ rect 0 n 0 n := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS := hpsupp z hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hjp : j ≤ p.length := hjle
    have hzm : z = p.getVert m := by
      have hmplen : m ≤ p.length := hmle.trans hjp
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmplen]
    rw [mem_rect] at hzS ⊢
    have hznonneg : 0 ≤ z 1 := by
      rw [hzm]
      rcases lt_or_eq_of_le hmle with hm | rfl
      · exact le_of_lt (hjabove m hm)
      · exact le_of_eq hju.symm
    omega
  have huT : u ∈ rect 0 n 0 n := hqsupp u q.end_mem_support
  have hytT : (yt : Site 2) ∈ rect 0 n 0 n := hqsupp _ q.start_mem_support
  have hu1 : u 1 = 0 := hju
  refine ⟨⟨u, huT, hu1⟩, ⟨(yt : Site 2), hytT, hyt1⟩, ?_⟩
  exact ⟨(q.reverse.induce (rect 0 n 0 n) (by
    intro z hz
    exact hqsupp z (by simpa using hz)))⟩



theorem torusReduceSwapSite_mem_square (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    torusReduceSwapSite L x ∈ torusSquareVertexSet L n := by
  have h := torusReduceSite_mem_square L n hnL hx
  exact ⟨h.2, h.1⟩

noncomputable def torusPlanarSquareFaceDualHom
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L) :
    (openSubgraph 2
      (fci_faceDualConfig (torusPlanarPullback L omega))).induce
        (rect 0 (n : ℤ) 0 (n : ℤ)) →g
      (FK.openSub (onsTorusGraph L)
        (torusAmbientConfigExtend L
          (torusAmbientSwapConfig L
            (torusCellDualAmbientConfig L omega)))).induce
        (torusSquareVertexSet L n) where
  toFun x := ⟨torusReduceSwapSite L x,
    torusReduceSwapSite_mem_square L n hnL x.2⟩
  map_rel' := by
    intro x y hxy
    exact (torusPlanarFaceDualHom L omega).map_rel hxy



theorem torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : VerticalCrossing
      (fci_faceDualConfig (torusPlanarPullback L omega))
      0 (n : ℤ) 0 (n : ℤ)) :
    torusSquareHorizontalCrossing L n
      (torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)) := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxbR : (xb : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) :=
    bottomSide_subset xb.2
  have hytR : (yt : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) :=
    topSide_subset yt.2
  have hxbS := torusReduceSwapSite_mem_square L n hnL hxbR
  have hytS := torusReduceSwapSite_mem_square L n hnL hytR
  refine ⟨torusReduceSwapSite L xb, torusReduceSwapSite L yt,
    hxbS, hytS, ?_, ?_, ?_⟩
  · obtain ⟨_, hxb1⟩ := torusReduceSite_val_of_mem_rect L n hnL hxbR
    change ((((xb : Site 2) 1 : ℤ) : ZMod L)).val = 0
    change ((((xb : Site 2) 1 : ℤ) : ZMod L)).val =
      Int.toNat ((xb : Site 2) 1) at hxb1
    rw [hxb1, xb.2.2]
    simp
  · obtain ⟨_, hyt1⟩ := torusReduceSite_val_of_mem_rect L n hnL hytR
    change ((((yt : Site 2) 1 : ℤ) : ZMod L)).val = n
    change ((((yt : Site 2) 1 : ℤ) : ZMod L)).val =
      Int.toNat ((yt : Site 2) 1) at hyt1
    rw [hyt1, yt.2.2]
    simp
  · exact hconn.map (torusPlanarSquareFaceDualHom L n hnL omega)






theorem torus_concreteSquareCrossing_dual_cover
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (hn : 1 ≤ n) (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (hno : ¬ torusSquareHorizontalCrossing L n omega) :
    torusCellDualAmbientConfig L omega ∈
      torusSquareVerticalCrossingEvent L n := by
  rw [mem_torusSquareVerticalCrossingEvent]
  let eta := torusPlanarPullback L omega
  have hnoPlanar : ¬ HorizontalCrossing eta 0 (n : ℤ) 0 (n : ℤ) := by
    exact torus_not_horizontal_imp_planar_not_horizontal L n hnL omega hno
  have hband : VerticalCrossing (fci_faceDualConfig eta)
      0 ((n : ℤ) - 1) (-1) (n : ℤ) := by
    exact crr_square_compl_subset_faceDualRect_unconditional (n : ℤ)
      (by omega) hnoPlanar
  have hsquare : VerticalCrossing (fci_faceDualConfig eta)
      0 (n : ℤ) 0 (n : ℤ) :=
    torus_faceBand_verticalCrossing_to_square (by omega) hband
  exact torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal
    L n hnL omega hsquare



theorem torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (hn : 1 ≤ n) (hnL : n < L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q
        (torusSquareHorizontalCrossingEvent L n) := by
  apply torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover
    L n hn hnL hq1
  intro omega hno
  exact torus_concreteSquareCrossing_dual_cover L n hn hnL omega hno

end StatMech.BeffaraDC

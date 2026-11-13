/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopPlusDualContour
import Code.Onsager.SignedLoopRectangularDualPath










open Finset SimpleGraph Set

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section


def ons_plusDualFaceBox (n : Nat) : Set (Site 2) :=
  {f | forall i, -(n : Int) - 1 <= f i ∧ f i <= n}


def ons_plusDualFaceEdgeSet (n : Nat) : Set (Sym2 (Site 2)) :=
  {edge | edge ∈ (hypercubicLattice 2).edgeSet ∧
    forall f, f ∈ edge -> f ∈ ons_plusDualFaceBox n}


abbrev ons_PlusDualFaceVertex (n : Nat) := {f : Site 2 // f ∈ ons_plusDualFaceBox n}


def ons_plusDualFaceGraph (n : Nat) : SimpleGraph (ons_PlusDualFaceVertex n) :=
  (hypercubicLattice 2).induce (ons_plusDualFaceBox n)

private theorem ons_int_bounds_of_natAbs_le {n : Nat} {z : Int}
    (hz : z.natAbs <= n) : -(n : Int) <= z ∧ z <= n := by
  rcases Int.natAbs_eq z with hz' | hz' <;> omega

private theorem ons_natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (hlo : -(n : Int) <= z) (hi : z <= n) : z.natAbs <= n := by
  rcases Int.natAbs_eq z with hz | hz <;> omega

private theorem ons_site_mem_plusDualFaceBox
    (n : Nat) {a b : Int}
    (ha : -(n : Int) - 1 <= a ∧ a <= n)
    (hb : -(n : Int) - 1 <= b ∧ b <= n) :
    (![a, b] : Site 2) ∈ ons_plusDualFaceBox n := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

private theorem ons_site_mem_box_two
    (n : Nat) {a b : Int}
    (ha : -(n : Int) <= a ∧ a <= n)
    (hb : -(n : Int) <= b ∧ b <= n) :
    (![a, b] : Site 2) ∈ box 2 n := by
  rw [mem_box]
  intro i
  fin_cases i
  · simpa using ons_natAbs_le_of_int_bounds ha.1 ha.2
  · simpa using ons_natAbs_le_of_int_bounds hb.1 hb.2

private theorem ons_flankFaces_mem_plusDualFaceBox_of_left
    (n : Nat) {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hp : p ∈ box 2 n) :
    forall f, f ∈ flankFaces p q -> f ∈ ons_plusDualFaceBox n := by
  intro f hf
  have hp0 := ons_int_bounds_of_natAbs_le (hp 0)
  have hp1 := ons_int_bounds_of_natAbs_le (hp 1)
  rcases adj_cases hadj with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold flankFaces at hf
    rw [if_pos h0, Sym2.mem_iff] at hf
    rcases hf with rfl | rfl
    · apply ons_site_mem_plusDualFaceBox n
      · omega
      · rcases hy with hpq | hqp <;> omega
    · apply ons_site_mem_plusDualFaceBox n
      · omega
      · rcases hy with hpq | hqp <;> omega
  · unfold flankFaces at hf
    rw [if_neg (by intro hpq; omega), Sym2.mem_iff] at hf
    rcases hf with rfl | rfl
    · apply ons_site_mem_plusDualFaceBox n
      · rcases hx with hpq | hqp <;> omega
      · omega
    · apply ons_site_mem_plusDualFaceBox n
      · rcases hx with hpq | hqp <;> omega
      · omega

private theorem ons_flankFaces_mem_plusDualFaceBox
    (n : Nat) {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (htouch : p ∈ box 2 n ∨ q ∈ box 2 n) :
    forall f, f ∈ flankFaces p q -> f ∈ ons_plusDualFaceBox n := by
  rcases htouch with hp | hq
  · exact ons_flankFaces_mem_plusDualFaceBox_of_left n hadj hp
  · rw [flankFaces_comm]
    exact ons_flankFaces_mem_plusDualFaceBox_of_left n hadj.symm hq



theorem ons_flankFacesSym_mem_plusDualFaceEdgeSet
    (n : Nat) {edge : Sym2 (Site 2)}
    (hedge : edge ∈ bondFinsetTouch 2 n) :
    flankFacesSym edge ∈ ons_plusDualFaceEdgeSet n := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
      have hdata := hedge
      rw [bondFinsetTouch, Finset.mem_image] at hdata
      obtain ⟨⟨p', q'⟩, hpq, heq⟩ := hdata
      rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product] at hpq
      have hadj : (hypercubicLattice 2).Adj p q :=
        adj_of_mem_bondFinsetTouch hedge
      have htouch : p ∈ box 2 n ∨ q ∈ box 2 n := by
        have hs : s(p', q') = s(p, q) := heq
        rw [Sym2.eq_iff] at hs
        rcases hs with hs | hs
        · simpa [hs.1, hs.2] using hpq.2.2
        · simpa [hs.1, hs.2, or_comm] using hpq.2.2
      refine ⟨?_, ?_⟩
      · obtain ⟨f, g, hfg, hfgadj⟩ := flankFaces_latAdj hadj
        rw [flankFacesSym_mk, hfg, SimpleGraph.mem_edgeSet]
        exact hfgadj
      · simpa only [flankFacesSym_mk] using
          ons_flankFaces_mem_plusDualFaceBox n hadj htouch

private theorem ons_symPrimal_mem_box_touch
    (n : Nat) {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (hf : f ∈ ons_plusDualFaceBox n) (hg : g ∈ ons_plusDualFaceBox n) :
    symPrimal f g ∈ bondFinsetTouch 2 n := by
  rcases adj_cases hadj with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold symPrimal
    rw [if_pos h0]
    apply mk_mem_bondFinsetTouch
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
        latAdj_right (f 0) (max (f 1) (g 1))
    · have hf0 := hf 0
      have hf1 := hf 1
      have hg1 := hg 1
      have hmax : -(n : Int) <= max (f 1) (g 1) ∧
          max (f 1) (g 1) <= n := by
        rcases hy with hfg | hgf <;> constructor <;> omega
      by_cases hlow : f 0 < -(n : Int)
      · right
        exact ons_site_mem_box_two n ⟨by omega, by omega⟩ hmax
      · left
        exact ons_site_mem_box_two n ⟨by omega, by omega⟩ hmax
  · unfold symPrimal
    rw [if_neg (by intro h0; omega)]
    apply mk_mem_bondFinsetTouch
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
        latAdj_top (max (f 0) (g 0)) (min (f 1) (g 1))
    · have hf0 := hf 0
      have hg0 := hg 0
      have hf1 := hf 1
      have hmax : -(n : Int) <= max (f 0) (g 0) ∧
          max (f 0) (g 0) <= n := by
        rcases hx with hfg | hgf <;> constructor <;> omega
      rw [h1]
      by_cases hlow : g 1 < -(n : Int)
      · right
        exact ons_site_mem_box_two n hmax ⟨by omega, by omega⟩
      · left
        exact ons_site_mem_box_two n hmax ⟨by omega, by omega⟩



theorem ons_symPrimalSym_mem_bondFinsetTouch
    (n : Nat) {edge : Sym2 (Site 2)}
    (hedge : edge ∈ ons_plusDualFaceEdgeSet n) :
    symPrimalSym edge ∈ bondFinsetTouch 2 n := by
  rcases hedge with ⟨hadj, hsupp⟩
  induction edge using Sym2.inductionOn with
  | _ f g =>
      rw [SimpleGraph.mem_edgeSet] at hadj
      exact ons_symPrimal_mem_box_touch n hadj
        (hsupp f (Sym2.mem_mk_left f g))
        (hsupp g (Sym2.mem_mk_right f g))



noncomputable def ons_touchingBondEquivPlusDualEdge (n : Nat) :
    {edge // edge ∈ bondFinsetTouch 2 n} ≃
      {edge // edge ∈ ons_plusDualFaceEdgeSet n} where
  toFun edge := ⟨flankFacesSym edge.1,
    ons_flankFacesSym_mem_plusDualFaceEdgeSet n edge.2⟩
  invFun edge := ⟨symPrimalSym edge.1,
    ons_symPrimalSym_mem_bondFinsetTouch n edge.2⟩
  left_inv edge := by
    apply Subtype.ext
    obtain ⟨⟨p, q⟩, hpq⟩ := edge.1.exists_rep
    have he : s(p, q) ∈ bondFinsetTouch 2 n := by
      simpa only [← hpq] using edge.2
    have hadj : (hypercubicLattice 2).Adj p q :=
      adj_of_mem_bondFinsetTouch he
    change symPrimalSym (flankFacesSym edge.1) = edge.1
    rw [← hpq, flankFacesSym_mk]
    exact symPrimalSym_flankFaces hadj
  right_inv edge := by
    apply Subtype.ext
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : s(f, g) ∈ (hypercubicLattice 2).edgeSet := by
      simpa only [← hfg] using edge.2.1
    have hadj : (hypercubicLattice 2).Adj f g :=
      (SimpleGraph.mem_edgeSet _).mp hedge
    change flankFacesSym (symPrimalSym edge.1) = edge.1
    rw [← hfg, symPrimalSym_mk]
    exact flankFacesSym_symPrimal hadj


noncomputable def ons_plusDualCoordEquiv (n : Nat) :
    {z : Int // -(n : Int) - 1 <= z ∧ z <= n} ≃ Fin ((2 * n + 1) + 1) where
  toFun z := ⟨(z.1 + n + 1).toNat, by
    have hz := z.2
    omega⟩
  invFun k := ⟨(k : Int) - n - 1, by
    have hk := k.2
    constructor <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    simp only
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n + 1)]
    omega
  right_inv k := by
    apply Fin.ext
    simp only
    have hk := k.2
    rw [show (k : Int) - n - 1 + n + 1 = (k : Int) by ring]
    exact Int.toNat_natCast k



noncomputable def ons_plusDualFaceEquivRect (n : Nat) :
    ons_PlusDualFaceVertex n ≃ ons_RectDualVertex (2 * n + 1) (2 * n + 1) where
  toFun f :=
    (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩,
      ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩)
  invFun f :=
    ⟨![((ons_plusDualCoordEquiv n).symm f.1).1,
        ((ons_plusDualCoordEquiv n).symm f.2).1], by
      intro i
      fin_cases i
      · exact ((ons_plusDualCoordEquiv n).symm f.1).2
      · exact ((ons_plusDualCoordEquiv n).symm f.2).2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Subtype.val
        ((ons_plusDualCoordEquiv n).symm_apply_apply ⟨f.1 0, f.2 0⟩)
    · exact congrArg Subtype.val
        ((ons_plusDualCoordEquiv n).symm_apply_apply ⟨f.1 1, f.2 1⟩)
  right_inv f := by
    apply Prod.ext <;> exact (ons_plusDualCoordEquiv n).apply_symm_apply _

private theorem ons_plusDualCoordEquiv_dist
    (n : Nat) (x y : {z : Int // -(n : Int) - 1 <= z ∧ z <= n}) :
    Nat.dist (ons_plusDualCoordEquiv n x).val
        (ons_plusDualCoordEquiv n y).val = (x.1 - y.1).natAbs := by
  change Nat.dist (x.1 + n + 1).toNat (y.1 + n + 1).toNat = _
  have hxnat := Int.toNat_of_nonneg (by omega : 0 <= x.1 + n + 1)
  have hynat := Int.toNat_of_nonneg (by omega : 0 <= y.1 + n + 1)
  rcases Int.natAbs_eq (x.1 - y.1) with h | h
  · by_cases hxy : (x.1 + n + 1).toNat <= (y.1 + n + 1).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega :
          (y.1 + n + 1).toNat <= (x.1 + n + 1).toNat)]
      omega
  · by_cases hxy : (x.1 + n + 1).toNat <= (y.1 + n + 1).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega :
          (y.1 + n + 1).toNat <= (x.1 + n + 1).toNat)]
      omega


theorem ons_plusDualFaceEquivRect_adj (n : Nat)
    (f g : ons_PlusDualFaceVertex n) :
    (ons_plusDualFaceGraph n).Adj f g ↔
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj
        (ons_plusDualFaceEquivRect n f) (ons_plusDualFaceEquivRect n g) := by
  rw [show (ons_plusDualFaceGraph n).Adj f g ↔
      (f.1 0 - g.1 0).natAbs + (f.1 1 - g.1 1).natAbs = 1 by
    simp [ons_plusDualFaceGraph, hypercubicLattice_adj, Fin.sum_univ_two]]
  rw [show (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj
      (ons_plusDualFaceEquivRect n f) (ons_plusDualFaceEquivRect n g) ↔
      (f.1 1 = g.1 1 ∧ (f.1 0 - g.1 0).natAbs = 1) ∨
      (f.1 0 = g.1 0 ∧ (f.1 1 - g.1 1).natAbs = 1) by
    change
      ((ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩ =
          ons_plusDualCoordEquiv n ⟨g.1 1, g.2 1⟩ ∧
        Nat.dist (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩).val
          (ons_plusDualCoordEquiv n ⟨g.1 0, g.2 0⟩).val = 1) ∨
       (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩ =
          ons_plusDualCoordEquiv n ⟨g.1 0, g.2 0⟩ ∧
        Nat.dist (ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩).val
          (ons_plusDualCoordEquiv n ⟨g.1 1, g.2 1⟩).val = 1)) ↔ _
    rw [ons_plusDualCoordEquiv_dist n ⟨f.1 0, f.2 0⟩ ⟨g.1 0, g.2 0⟩,
      ons_plusDualCoordEquiv_dist n ⟨f.1 1, f.2 1⟩ ⟨g.1 1, g.2 1⟩]
    simp only [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]]
  omega

noncomputable instance ons_plusDualFaceVertexFintype (n : Nat) :
    Fintype (ons_PlusDualFaceVertex n) :=
  Fintype.ofEquiv (ons_RectDualVertex (2 * n + 1) (2 * n + 1))
    (ons_plusDualFaceEquivRect n).symm



noncomputable def ons_plusDualFaceEdgeLift (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    Sym2 (ons_PlusDualFaceVertex n) :=
  s(⟨edge.1.out.1, edge.2.2 edge.1.out.1 (Sym2.out_fst_mem edge.1)⟩,
    ⟨edge.1.out.2, edge.2.2 edge.1.out.2 (Sym2.out_snd_mem edge.1)⟩)

@[simp] theorem ons_plusDualFaceEdgeLift_map_val (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    Sym2.map Subtype.val (ons_plusDualFaceEdgeLift n edge) = edge.1 := by
  rw [ons_plusDualFaceEdgeLift, Sym2.map_mk]
  exact edge.1.out_eq

theorem ons_plusDualFaceEdgeLift_mem_edgeFinset (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    ons_plusDualFaceEdgeLift n edge ∈ (ons_plusDualFaceGraph n).edgeFinset := by
  rw [ons_plusDualFaceEdgeLift, SimpleGraph.mem_edgeFinset]
  apply (SimpleGraph.mem_edgeSet _).mpr
  change (hypercubicLattice 2).Adj edge.1.out.1 edge.1.out.2
  apply (SimpleGraph.mem_edgeSet _).mp
  simpa only [edge.1.out_eq] using edge.2.1



noncomputable def ons_plusDualFaceEdgeEquivGraphEdge (n : Nat) :
    {edge // edge ∈ ons_plusDualFaceEdgeSet n} ≃
      {edge // edge ∈ (ons_plusDualFaceGraph n).edgeFinset} where
  toFun edge := ⟨ons_plusDualFaceEdgeLift n edge,
    ons_plusDualFaceEdgeLift_mem_edgeFinset n edge⟩
  invFun edge := ⟨Sym2.map Subtype.val edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : s(f, g) ∈ (ons_plusDualFaceGraph n).edgeFinset := by
      simpa only [← hfg] using edge.2
    have hadj : (ons_plusDualFaceGraph n).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      exact hedge
    rw [← hfg, Sym2.map_mk]
    constructor
    · rw [SimpleGraph.mem_edgeSet]
      exact hadj
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact f.2
      · exact g.2⟩
  left_inv edge := by
    apply Subtype.ext
    exact ons_plusDualFaceEdgeLift_map_val n edge
  right_inv edge := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [ons_plusDualFaceEdgeLift_map_val]



noncomputable def ons_plusDualFaceGraphEdgeEquivRectEdge (n : Nat) :
    {edge // edge ∈ (ons_plusDualFaceGraph n).edgeFinset} ≃
      {edge // edge ∈
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset} where
  toFun edge := ⟨Sym2.map (ons_plusDualFaceEquivRect n) edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : (ons_plusDualFaceGraph n).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      simpa only [← hfg] using edge.2
    rw [← hfg, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact (ons_plusDualFaceEquivRect_adj n f g).mp hedge⟩
  invFun edge := ⟨Sym2.map (ons_plusDualFaceEquivRect n).symm edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge :
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      simpa only [← hfg] using edge.2
    rw [← hfg, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact (ons_plusDualFaceEquivRect_adj n _ _).mpr (by simpa using hedge)⟩
  left_inv edge := by
    apply Subtype.ext
    change Sym2.map (ons_plusDualFaceEquivRect n).symm
      (Sym2.map (ons_plusDualFaceEquivRect n) edge.1) = edge.1
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    rw [← hfg, Sym2.map_mk, Sym2.map_mk]
    simp
  right_inv edge := by
    apply Subtype.ext
    change Sym2.map (ons_plusDualFaceEquivRect n)
      (Sym2.map (ons_plusDualFaceEquivRect n).symm edge.1) = edge.1
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    rw [← hfg, Sym2.map_mk, Sym2.map_mk]
    simp



noncomputable def ons_touchingBondEquivRectDualEdge (n : Nat) :
    {edge // edge ∈ bondFinsetTouch 2 n} ≃
      {edge // edge ∈
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset} :=
  (ons_touchingBondEquivPlusDualEdge n).trans
    ((ons_plusDualFaceEdgeEquivGraphEdge n).trans
      (ons_plusDualFaceGraphEdgeEquivRectEdge n))



theorem ons_plusDualContour_subset_plusDualFaceEdgeSet
    (n : Nat) (tau : {x // x ∈ box 2 n} -> Bool) :
    ∀ edge ∈ ons_plusDualContour n tau,
      edge ∈ ons_plusDualFaceEdgeSet n := by
  intro edge hedge
  rw [ons_plusDualContour, Finset.mem_image] at hedge
  obtain ⟨primalEdge, hcut, rfl⟩ := hedge
  apply ons_flankFacesSym_mem_plusDualFaceEdgeSet n
  exact (Finset.mem_filter.mp hcut).1

end

end StatMech.Onsager

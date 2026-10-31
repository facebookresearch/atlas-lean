/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RegionGraphAddEdge
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEulerInduction
import Lean.Elab.Tactic.Omega
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The rotated region graph is the lattice minus a graph

The region graph of `H` is isomorphic, via the quarter-turn rotation, to the lattice with the edges
of `H` deleted (`jbc_rotIso`), so reachability in the region graph is reachability after deleting
primal edges. The file also defines the unit square (`jbc_Pce`, the 4-cycle on the corners of
`[0, 1]²`) as a `PlanarZ2Subgraph`; deleting the square's edges from `ℤ²` leaves its corners
connected around the outside.

## Main definitions

* `StatMech.Lattice.jbc_latticeMinusEdges H`: the square lattice with the edges of `H` deleted.
* `StatMech.Lattice.jbc_rotIso H`: the rotation isomorphism onto `regionGraph H`.
* `StatMech.Lattice.jbc_cyc4`, `StatMech.Lattice.jbc_Pce`: the 4-cycle and the unit square as a
  `PlanarZ2Subgraph`.

## Main results

* `StatMech.Lattice.jbc_regionGraph_reachable_iff`: reachability in the region graph is reachability
  after deleting the primal edges.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

theorem jbc_rot90Inv_rot90Fun (a : Site 2) : rot90Inv (rot90Fun a) = a := by
  have := rot90Equiv.left_inv a; simpa [rot90Equiv] using this

theorem jbc_rot90Fun_rot90Inv (a : Site 2) : rot90Fun (rot90Inv a) = a := by
  have := rot90Equiv.right_inv a; simpa [rot90Equiv] using this

theorem jbc_crossEdge_symm_pair (f g : Site 2) :
    crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
  simp [crossEdge, sym2Congr]

theorem jbc_crossEdge_symm_rot (a b : Site 2) :
    crossEdge.symm s(rot90Fun a, rot90Fun b) = s(a, b) := by
  rw [jbc_crossEdge_symm_pair, jbc_rot90Inv_rot90Fun a, jbc_rot90Inv_rot90Fun b]

/-- The square lattice with the edges of `H` deleted. -/
noncomputable def jbc_latticeMinusEdges (H : SimpleGraph (Site 2)) : SimpleGraph (Site 2) :=
  (hypercubicLattice 2).deleteEdges H.edgeSet

@[simp] theorem jbc_latticeMinusEdges_adj (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (jbc_latticeMinusEdges H).Adj a b ↔
      (hypercubicLattice 2).Adj a b ∧ s(a, b) ∉ H.edgeSet := by
  rw [jbc_latticeMinusEdges, deleteEdges_adj]

theorem jbc_regionGraph_rot_adj (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (regionGraph H).Adj (rot90Fun a) (rot90Fun b) ↔ (jbc_latticeMinusEdges H).Adj a b := by
  rw [regionGraph_adj, jbc_latticeMinusEdges_adj, rot90_adj, jbc_crossEdge_symm_rot]

/-- The quarter-turn rotation is an isomorphism from the lattice minus the edges of `H` onto the
region graph of `H`. -/
noncomputable def jbc_rotIso (H : SimpleGraph (Site 2)) :
    jbc_latticeMinusEdges H ≃g regionGraph H where
  toEquiv := rot90Equiv
  map_rel_iff' := by
    intro a b
    rw [rot90Equiv_apply, rot90Equiv_apply, jbc_regionGraph_rot_adj]

@[simp] theorem jbc_rotIso_apply (H : SimpleGraph (Site 2)) (a : Site 2) :
    jbc_rotIso H a = rot90Fun a := rfl

theorem jbc_regionGraph_reachable_iff (H : SimpleGraph (Site 2)) (a b : Site 2) :
    (regionGraph H).Reachable (rot90Fun a) (rot90Fun b) ↔
      (jbc_latticeMinusEdges H).Reachable a b := by
  constructor
  · intro h
    have := h.map (jbc_rotIso H).symm.toHom
    simpa [jbc_rotIso, jbc_rot90Inv_rot90Fun] using this
  · intro h
    have := h.map (jbc_rotIso H).toHom
    simpa [jbc_rotIso] using this

theorem jbc_deleteRegion_le_lattice (H : SimpleGraph (Site 2)) (e : Set (Sym2 (Site 2))) :
    (regionGraph H).deleteEdges e ≤ hypercubicLattice 2 := by
  intro a b hab
  exact hab.1.1

theorem jbc_deleteRegion_eq_pushSup (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hne : x ≠ y) :
    (regionGraph (jei_pushGraph P K)).deleteEdges {crossEdge s(P.emb x, P.emb y)}
      = regionGraph (jei_pushGraph P (K ⊔ edge x y)) := by
  rw [jei_pushGraph_sup_edge P K x y hne]
  rw [jsf_regionGraph_sup_edge (jei_pushGraph P K) (fun h => hne (P.emb.injective h))]

theorem jbc_dualSide_iff_primalAvoid (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hne : x ≠ y) :
    ((regionGraph (jei_pushGraph P K)).deleteEdges
        {crossEdge s(P.emb x, P.emb y)}).Reachable (rot90Fun (P.emb x)) (rot90Fun (P.emb y))
      ↔ (jbc_latticeMinusEdges (jei_pushGraph P (K ⊔ edge x y))).Reachable
          (P.emb x) (P.emb y) := by
  rw [jbc_deleteRegion_eq_pushSup P K hne, jbc_regionGraph_reachable_iff]

/-- If `x` and `y` are not connected in `K`, they are connected in the lattice minus the image of
`K ⊔ edge x y`. -/
def jbc_BridgeDirection (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → ∀ {x y : P.V}, P.G.Adj x y → ¬ K.Adj x y →
    ¬ K.Reachable x y →
      (jbc_latticeMinusEdges (jei_pushGraph P (K ⊔ edge x y))).Reachable (P.emb x) (P.emb y)

/-- The four corners `(0, 0), (1, 0), (1, 1), (0, 1)` of the unit square, in cyclic order. -/
def jbc_csq (i : Fin 4) : Site 2 :=
  match i with
  | 0 => ![0, 0] | 1 => ![1, 0] | 2 => ![1, 1] | 3 => ![0, 1]

theorem jbc_csq_inj : Function.Injective jbc_csq := by decide +kernel

theorem jbc_csq_y (i : Fin 4) : (jbc_csq i) 1 = 0 ∨ (jbc_csq i) 1 = 1 := by
  fin_cases i <;> simp [jbc_csq]

/-- Adjacency of the 4-cycle `0 – 1 – 2 – 3 – 0`, as a Boolean relation. -/
def jbc_cyc4Rel (i j : Fin 4) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) || (i == 1 && j == 2) || (i == 2 && j == 1) ||
    (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 0) || (i == 0 && j == 3)

/-- The 4-cycle on `Fin 4`. -/
def jbc_cyc4 : SimpleGraph (Fin 4) where
  Adj i j := jbc_cyc4Rel i j
  symm := ⟨by intro i j h; revert h; revert i j; decide⟩
  loopless := ⟨by intro i h; revert h; revert i; decide⟩

@[simp] theorem jbc_cyc4_adj (i j : Fin 4) : jbc_cyc4.Adj i j ↔ jbc_cyc4Rel i j := Iff.rfl

theorem jbc_csq_isSub :
    ∀ ⦃i j : Fin 4⦄, jbc_cyc4.Adj i j → (hypercubicLattice 2).Adj (jbc_csq i) (jbc_csq j) := by
  intro i j h
  rw [jbc_cyc4_adj] at h
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  revert h; fin_cases i <;> fin_cases j <;> simp [jbc_cyc4Rel, jbc_csq]

/-- The vertex `0` of the 4-cycle. -/
def jbc_v0 : Fin 4 := 0

/-- The vertex `1` of the 4-cycle. -/
def jbc_v1 : Fin 4 := 1

theorem jbc_v0_ne_v1 : jbc_v0 ≠ jbc_v1 := by decide

/-- The unit square: the 4-cycle embedded on the corners of `[0, 1]²`. -/
noncomputable def jbc_Pce : PlanarZ2Subgraph where
  V := Fin 4
  finV := inferInstance
  decV := inferInstance
  G := jbc_cyc4
  emb := ⟨jbc_csq, jbc_csq_inj⟩
  isSub := jbc_csq_isSub

theorem jbc_latadj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := by rw [hypercubicLattice_adj]; exact h

theorem jbc_Pce_emb0 : jbc_Pce.emb jbc_v0 = ![0, 0] := rfl
theorem jbc_Pce_emb1 : jbc_Pce.emb jbc_v1 = ![1, 0] := rfl

theorem jbc_Pce_Gadj : jbc_Pce.G.Adj jbc_v0 jbc_v1 := by
  change jbc_cyc4.Adj jbc_v0 jbc_v1; rw [jbc_cyc4_adj]; decide

theorem jbc_not_contour_ym1 {f g : Site 2} (h : (rot90Inv f) 1 = -1) :
    crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
  rw [jbc_crossEdge_symm_pair, SimpleGraph.mem_edgeSet]
  rintro ⟨i, _, _, hi, _⟩
  have : (jbc_csq i) 1 = -1 := by rw [show jbc_csq i = rot90Inv f from hi]; exact h
  rcases jbc_csq_y i with hh | hh <;> rw [hh] at this <;> omega

theorem jbc_not_contour_ym1' {f g : Site 2} (h : (rot90Inv g) 1 = -1) :
    crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet := by
  rw [Sym2.eq_swap]; exact jbc_not_contour_ym1 (f := g) (g := f) h

theorem jbc_vne {a b : Site 2} (h0 : a 0 ≠ b 0 ∨ a 1 ≠ b 1) : a ≠ b := by
  intro h; rcases h0 with hh | hh <;> [exact hh (by rw [h]); exact hh (by rw [h])]

theorem jbc_DR_true_direct :
    (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Reachable
      (rot90Fun (jbc_csq 0)) (rot90Fun (jbc_csq 1)) := by
  have e0 : rot90Fun (jbc_csq 0) = ![0, 0] := by simp [jbc_csq, rot90Fun]
  have e1 : rot90Fun (jbc_csq 1) = ![0, 1] := by simp [jbc_csq, rot90Fun]
  rw [e0, e1]
  have mkadj : ∀ f g : Site 2, (hypercubicLattice 2).Adj f g →
      crossEdge.symm s(f, g) ∉ (jei_pushGraph jbc_Pce jbc_cyc4).edgeSet →
      (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj f g := by
    intro f g hadj hpush; rw [regionGraph_adj]; exact ⟨hadj, hpush⟩
  have a1 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![0, 0] ![1, 0] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1' (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  have a2 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![1, 0] ![1, 1] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1 (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  have a3 : (regionGraph (jei_pushGraph jbc_Pce jbc_cyc4)).Adj ![1, 1] ![0, 1] :=
    mkadj _ _ (jbc_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (jbc_not_contour_ym1 (by rw [rot90Inv_apply]; norm_num [Matrix.cons_val_one]))
  exact a1.reachable.trans (a2.reachable.trans a3.reachable)

end Lattice

end StatMech

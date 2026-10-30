/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Probability.Configuration.ConfigSpace

/-!
# Self-duality of the square lattice

The planar dual of `ℤ²` is again a copy of `ℤ²` (the lattice of face centres). This file encodes the
dual lattice on the same vertex type `Site 2`, the quarter-turn rotation `(a, b) ↦ (-b, a)` and the
bijection it induces on edges, and a "dual" bond configuration built from that rotation.

The rotation does not send a primal edge to the dual edge crossing it: it maps `{(0,0), (1,0)}` to
`{(0,0), (0,1)}`, which shares an endpoint with the original edge. Consequently `dualConfig` is not
the geometric dual configuration, and `dualConfig (dualConfig ω)` is the half-turn of `ω`, not `ω`.
For the geometric crossing of a primal edge and a dual edge use
`StatMech.Lattice.sharedPrimalEdge` (`JordanEnclosure`).

## Main definitions

* `StatMech.Lattice.dualLattice`: the dual square lattice, as a graph on `Site 2`.
* `StatMech.Lattice.rot90Fun`, `StatMech.Lattice.rot90Iso`: the rotation `(a, b) ↦ (-b, a)` and the
  graph automorphism of `ℤ²` it induces.
* `StatMech.Lattice.crossEdge`: the bijection of `Sym2 (Site 2)` induced by the quarter-turn
  rotation.
* `StatMech.Lattice.dualConfig ω`: the configuration in which `e` is open exactly when the edge
  `crossEdge.symm e` (the inverse quarter turn of `e`) is closed in `ω`.

## Main results

* `StatMech.Lattice.isOpen_iff_dual_isClosed`: `e` is open in `ω` iff `crossEdge e` is closed in
  `dualConfig ω`.
* `StatMech.Lattice.dualConfig_dualConfig`: the double dual rotates the configuration by a half
  turn.
-/

@[expose] public section

open SimpleGraph

namespace StatMech

namespace Lattice

/-- The dual square lattice. Its vertices are the face centres of `ℤ²`, relabelled as integer
points, so as a graph it is `hypercubicLattice 2`. -/
def dualLattice : SimpleGraph (Site 2) := hypercubicLattice 2

@[simp]
theorem dualLattice_adj (x y : Site 2) :
    dualLattice.Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := Iff.rfl

/-- The quarter-turn rotation `(a, b) ↦ (-b, a)` of `ℤ²`. -/
def rot90Fun (x : Site 2) : Site 2 := ![- x 1, x 0]

/-- The inverse quarter-turn rotation `(a, b) ↦ (b, -a)` of `ℤ²`. -/
def rot90Inv (x : Site 2) : Site 2 := ![x 1, - x 0]

@[simp] theorem rot90Fun_apply (a b : ℤ) : rot90Fun ![a, b] = ![-b, a] := by
  funext i; fin_cases i <;> simp [rot90Fun]

@[simp] theorem rot90Inv_apply (a b : ℤ) : rot90Inv ![a, b] = ![b, -a] := by
  funext i; fin_cases i <;> simp [rot90Inv]

/-- The quarter-turn rotation as a permutation of `ℤ²`. -/
def rot90Equiv : Site 2 ≃ Site 2 where
  toFun := rot90Fun
  invFun := rot90Inv
  left_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]
  right_inv := by intro x; funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]

@[simp] theorem rot90Equiv_apply (x : Site 2) : rot90Equiv x = rot90Fun x := rfl
@[simp] theorem rot90Equiv_symm_apply (x : Site 2) : rot90Equiv.symm x = rot90Inv x := rfl

theorem rot90_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (rot90Fun x) (rot90Fun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rot90Fun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg, Nat.add_comm]

/-- The quarter-turn rotation as a graph automorphism of the square lattice. -/
def rot90Iso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨rot90Equiv, fun {x y} => rot90_adj x y⟩

@[simp] theorem rot90Iso_apply (x : Site 2) : rot90Iso x = rot90Fun x := rfl

/-- The identity isomorphism between the square lattice and its dual. -/
def selfDual : hypercubicLattice 2 ≃g dualLattice := SimpleGraph.Iso.refl

@[simp] theorem selfDual_apply (x : Site 2) : selfDual x = x := rfl

/-- The isomorphism between the square lattice and its dual given by the quarter-turn rotation. -/
def selfDualCross : hypercubicLattice 2 ≃g dualLattice := rot90Iso

@[simp] theorem selfDualCross_apply (x : Site 2) : selfDualCross x = rot90Fun x := rfl

/-- The bijection between primal and dual edges induced by `rot90Iso`. -/
def crossingEdgeEquiv : (hypercubicLattice 2).edgeSet ≃ dualLattice.edgeSet :=
  rot90Iso.mapEdgeSet

theorem crossingEdgeEquiv_coe (e : (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv e : Sym2 (Site 2)) = Sym2.map (⇑rot90Iso) e := by
  rw [crossingEdgeEquiv, SimpleGraph.Iso.mapEdgeSet]
  exact Hom.mapEdgeSet_coe rot90Iso.toHom e

theorem crossingEdgeEquiv_horizontal (a b : ℤ)
    (he : s(![a, b], ![a + 1, b]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-b, a + 1]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]

theorem crossingEdgeEquiv_vertical (a b : ℤ)
    (he : s(![a, b], ![a, b + 1]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-(b + 1), a]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]

/-- An equivalence `α ≃ β` induces an equivalence of unordered pairs `Sym2 α ≃ Sym2 β`. -/
def sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by intro x; rw [Sym2.map_map]; simp
  right_inv := by intro x; rw [Sym2.map_map]; simp

@[simp] theorem sym2Congr_mk {α β : Type*} (e : α ≃ β) (a b : α) :
    sym2Congr e s(a, b) = s(e a, e b) := by simp [sym2Congr, Sym2.map_mk]

/-- The bijection on unordered pairs of sites induced by the quarter-turn rotation
`(a, b) ↦ (-b, a)`. It maps lattice edges to lattice edges, but not to the dual edge crossing them:
`{(0,0), (1,0)}` goes to `{(0,0), (0,1)}`. For the geometric crossing use `sharedPrimalEdge`. -/
def crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr rot90Equiv

@[simp] theorem crossEdge_mk (x y : Site 2) :
    crossEdge s(x, y) = s(rot90Fun x, rot90Fun y) := by simp [crossEdge]

/-- The configuration in which `e` is open exactly when the inverse quarter turn `crossEdge.symm e`
of `e` is closed in `ω`. This is the dual configuration only up to the rotation: applying it twice
gives the half-turn of `ω` (`dualConfig_dualConfig`), not `ω`. -/
def dualConfig (ω : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => !(ω (crossEdge.symm e))

theorem isOpen_iff_dual_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    ω e = true ↔ dualConfig ω (crossEdge e) = false := by
  unfold dualConfig
  rw [Equiv.symm_apply_apply]
  cases ω e <;> simp

theorem dual_isOpen_iff_isClosed (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig ω e = true ↔ ω (crossEdge.symm e) = false := by
  unfold dualConfig
  cases ω (crossEdge.symm e) <;> simp

theorem dualConfig_dualConfig (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) := by
  unfold dualConfig
  rw [Bool.not_not]

end Lattice

end StatMech

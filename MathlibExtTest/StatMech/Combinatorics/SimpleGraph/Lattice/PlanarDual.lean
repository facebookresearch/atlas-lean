/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual`

Computes the quarter-turn rotation `rot90Fun`, its inverse, `rot90Iso`, `crossingEdgeEquiv` on the
horizontal edge `{(0, 0), (1, 0)}`, `crossEdge`, and `dualConfig` for the configuration with a
single open edge. Checks `isOpen_iff_dual_isClosed` and `dualConfig_dualConfig` on that
configuration.

The last examples record that `crossEdge` is the rotation about the origin, not the geometric
crossing (which would be a rotation about the edge midpoint followed by a half-unit shift): it
sends `{(0, 0), (1, 0)}` to `{(0, 0), (0, 1)}`, and applying `crossEdge.symm` twice is the
half-turn, so `dualConfig (dualConfig ω)` is the half-turn of `ω`, not `ω`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.PlanarDual

open _root_.StatMech _root_.StatMech.Lattice

-- The quarter turn sends `(1, 0)` to `(0, 1)` and `(0, 1)` to `(-1, 0)`.
example : rot90Fun ![1, 0] = ![0, 1] := by simp
example : rot90Fun ![0, 1] = ![-1, 0] := by simp

-- `rot90Inv` undoes `rot90Fun`.
example : rot90Inv (rot90Fun ![3, -2]) = ![3, -2] := by simp

-- `rot90Iso` is a graph automorphism: the edge `(0,0) - (1,0)` maps to the edge `(0,0) - (0,1)`.
example : (hypercubicLattice 2).Adj (rot90Iso ![0, 0]) (rot90Iso ![1, 0]) := by
  rw [rot90Iso.map_adj_iff]; simp [Fin.sum_univ_two]

-- The dual lattice is the square lattice itself.
example : dualLattice.Adj ![0, 0] ![0, 1] := by
  simp [dualLattice, Fin.sum_univ_two]

-- `crossingEdgeEquiv_horizontal` at `(a, b) = (0, 0)`.
example (he : s(![(0 : ℤ), 0], ![0 + 1, 0]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![0, 0], ![0, 1]) := by
  rw [crossingEdgeEquiv_horizontal]; simp

-- `crossEdge` on a concrete pair.
example : crossEdge s(![1, 0], ![1, 1]) = s(![0, 1], ![-1, 1]) := by simp

/-- `crossEdge.symm` is the inverse rotation on unordered pairs. -/
theorem crossEdge_symm_mk (x y : Site 2) :
    crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
  have h : ∀ z : Site 2, rot90Fun (rot90Inv z) = z := fun z => by
    funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]
  rw [Equiv.symm_apply_eq, crossEdge_mk, h, h]

/-- The configuration in which only the edge `{(0, 0), (1, 0)}` is open. -/
def oneEdge : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = s(![0, 0], ![1, 0]))

-- `isOpen_iff_dual_isClosed`: the open primal edge makes its rotated dual edge closed.
example : dualConfig oneEdge (crossEdge s(![0, 0], ![1, 0])) = false :=
  (isOpen_iff_dual_isClosed oneEdge _).mp (by simp [oneEdge])

-- A dual edge whose preimage is closed is open.
example : dualConfig oneEdge s(![5, 5], ![5, 6]) = true := by
  rw [dual_isOpen_iff_isClosed]
  simp [oneEdge, crossEdge_symm_mk, rot90Inv, funext_iff, Fin.forall_fin_two]

-- `crossEdge` is the rotation about the origin: the edge `(0,0) - (1,0)` goes to `(0,0) - (0,1)`,
-- which shares an endpoint with it rather than crossing it.
example : crossEdge s(![0, 0], ![1, 0]) = s(![0, 0], ![0, 1]) := by simp

-- `dualConfig_dualConfig`: the double dual reads `ω` at the half-turned edge, so it is not `ω`.
example : dualConfig (dualConfig oneEdge) s(![0, 0], ![1, 0]) = false := by
  rw [dualConfig_dualConfig]
  simp [oneEdge, crossEdge_symm_mk, rot90Inv, funext_iff, Fin.forall_fin_two]

example : dualConfig (dualConfig oneEdge) ≠ oneEdge := by
  intro h
  have h1 := congrFun h s(![0, 0], ![1, 0])
  rw [dualConfig_dualConfig] at h1
  simp [oneEdge, crossEdge_symm_mk, rot90Inv, funext_iff, Fin.forall_fin_two] at h1

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.PlanarDual

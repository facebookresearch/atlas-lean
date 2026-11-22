/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectBasepoint

/-!
# The full original path homotopy fibre and based diagonal loops

Use the actual original identity-edge basepoint and the proved whole path
diagonal conullity. The existing full-path construction gives a homotopy
equivalence with the ordinary compact-open loop space at the same realized
object. Its forward map and both relative inverse families are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The realization of the literal original path projection diagonal. -/
abbrev realizedDiagonalProjection (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)) ⟶
      SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram) :=
  SSet.toTop.map (SSet.simplicialDiagonalFunctor.map (projection W x))

/-- The same original object realized in the whole original diagonal. -/
abbrev realizedDiagonalPoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram) :=
  SSet.realizedVertex (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from x)

/-- The actual full original path homotopy fibre is homotopy equivalent to the based diagonal loop space. -/
def diagonalHomotopyFibreLoopEquiv (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    ContinuousMap.HomotopyEquiv
      (TopCat.homotopyFiber (realizedDiagonalProjection W x) (realizedDiagonalPoint W x))
      (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
        (realizedDiagonalPoint W x)) :=
  TopCat.realizedConullHomotopyFiberLoopEquiv
    (SSet.simplicialDiagonalFunctor.obj (diagram W x)) (diagonalBasepoint W x)
    (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
    (realizedBasepoint_projection W x) (diagonalTerminal_weak W x)

/-- The forward map is the full projected contraction followed by the same carried path. -/
theorem diagonalHomotopyFibreLoopEquiv_toFun (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (diagonalHomotopyFibreLoopEquiv W x).toFun =
      (TopCat.homotopyFiberToLoopsOfRealizedConull
        (SSet.simplicialDiagonalFunctor.obj (diagram W x)) (diagonalBasepoint W x)
        (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
        (realizedBasepoint_projection W x) (diagonalTerminal_weak W x)).hom :=
  TopCat.realizedConullHomotopyFiberLoopEquiv_toFun _ _ _ _ _ _

/-- The actual original full-path return into the same based loop space. -/
def diagonalHomotopyFibreToLoops (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.homotopyFiber (realizedDiagonalProjection W x) (realizedDiagonalPoint W x) ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
        (realizedDiagonalPoint W x)) :=
  TopCat.ofHom (diagonalHomotopyFibreLoopEquiv W x).toFun

/-- The whole forward map is the existing genuine original full-path return. -/
theorem diagonalHomotopyFibreToLoops_actual (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagonalHomotopyFibreToLoops W x = TopCat.homotopyFiberToLoopsOfRealizedConull
      (SSet.simplicialDiagonalFunctor.obj (diagram W x)) (diagonalBasepoint W x)
      (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
      (realizedBasepoint_projection W x) (diagonalTerminal_weak W x) := by
  apply TopCat.ext
  intro z
  change (diagonalHomotopyFibreLoopEquiv W x).toFun z = _
  rw [diagonalHomotopyFibreLoopEquiv_toFun]

/-- The same actual full-path forward map is a weak homotopy equivalence. -/
theorem diagonalHomotopyFibreToLoops_weak (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (diagonalHomotopyFibreToLoops W x) :=
  TopCat.homotopyEquiv_toFun_mem (diagonalHomotopyFibreLoopEquiv W x)

/-- The existing whole fibre-side inverse family remains relative to the actual identity-edge point. -/
def diagonalHomotopyFibreLoopLeftInverseRel (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :=
  TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel
    (SSet.simplicialDiagonalFunctor.obj (diagram W x)) (diagonalBasepoint W x)
    (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
    (realizedBasepoint_projection W x) (diagonalTerminal_weak W x)

/-- The same loop-side affine inverse family fixes the complete original constant-loop point. -/
def diagonalHomotopyFibreLoopRightInverseRel (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :=
  TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel
    (SSet.simplicialDiagonalFunctor.obj (diagram W x)) (diagonalBasepoint W x)
    (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
    (realizedBasepoint_projection W x) (diagonalTerminal_weak W x)

end SimplicialSpace.LeftDecalageObject

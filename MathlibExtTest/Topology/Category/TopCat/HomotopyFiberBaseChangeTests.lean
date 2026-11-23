/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

variable {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}

-- A standalone consumer can use changing-base invariance at the image point.
example (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B)
    (hs : weakHomotopyEquivalences s) (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences (homotopyFiberMapOfSquare s h comm b) :=
  homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences s h comm b hs hh

-- Repointing a weak-equivalence fiber map along a basepoint equation preserves weakness.
example (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) {b' : B'}
    (e : h b = b') (hs : weakHomotopyEquivalences s)
    (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences (e ▸ homotopyFiberMapOfSquare s h comm b) :=
  homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences_of_basepoint_eq s h comm b
    e hs hh

-- The public characteristic theorem gives the actual postcomposed path.
example (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B)
    (z : homotopyFiber p b) (t : TopCat.I.{u}) :
    homotopyFiberPath q (h b) (homotopyFiberMapOfSquare s h comm b z) t =
      h (homotopyFiberPath p b z t) := by
  exact congrArg (fun γ : C(TopCat.I.{u}, B') => γ t)
    (ConcreteCategory.congr_hom (homotopyFiberMapOfSquare_path s h comm b) z)

-- Naturality retains the given strict-fiber and constant-path comparisons.
example (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    strictFiberMapOfSquare s h comm b ≫ strictFiberToHomotopyFiber q (h b) =
      strictFiberToHomotopyFiber p b ≫ homotopyFiberMapOfSquare s h comm b :=
  strictFiberToHomotopyFiber_naturality s h comm b

#print axioms TopCat.modelCategory.pathEndpoints_fibration
#print axioms TopCat.homotopyPullbackMap_mem_weakHomotopyEquivalences
#print axioms TopCat.homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences
#print axioms TopCat.homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences_of_basepoint_eq
#print axioms TopCat.strictFiberToHomotopyFiber_naturality
#print axioms TopCat.strictFiberToHomotopyFiber_mem_of_square

end TopCat

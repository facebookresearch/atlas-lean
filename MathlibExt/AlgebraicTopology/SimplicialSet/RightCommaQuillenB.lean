/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSkeletalFiberTheorem
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBKFiberTransfer

/-!
# Quillen B for the actual right-comma comparison

Realized weakness of the original postcomposition transitions implies
weakness of the original right-comma homotopy-fiber comparison. The BK
point-fiber theorem supplies the constant-chain comparison used by the
existing transfer to the comma-arrow path.
-/

@[expose] public section

open CategoryTheory

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The actual right-comma comparison is weak whenever every original
postcomposition transition realizes to a weak homotopy equivalence. -/
theorem rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences
    (F : C ⥤ D)
    (hF : ∀ (d d' : D) (g : d ⟶ d'),
      TopCat.weakHomotopyEquivalences
        (toTop.map (nerveMap (CostructuredArrow.map (S := F) g))))
    (d : D) : TopCat.weakHomotopyEquivalences (rightCommaHomotopyFiberComparison F d) := by
  apply rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences_of_bkPointFiberComparison
    F d
  apply bkPointFiberComparison_mem_weakHomotopyEquivalences
    (rightCommaNerveDiagram.{max u w, max v w, u} F)
  intro d d' g
  simpa only [rightCommaNerveDiagram_obj, rightCommaNerveDiagram_map] using hF d d' g

end SSet

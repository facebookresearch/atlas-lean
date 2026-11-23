/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberwiseDetection
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroupUnit

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TopCat.modelCategory

universe u

namespace TopCat

-- Derived total weakness can be consumed by the actual homotopy-fiber map
-- theorem over the identity base, without a separate total-map premise.
example {E E' B : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [HomotopicalAlgebra.Fibration p] [HomotopicalAlgebra.Fibration q]
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B, weakHomotopyEquivalences
      (strictFiberMapOfSquare (p := p) (q := q) s (𝟙 B)
        (by simpa using comm.symm) b)) (b : B) :
    weakHomotopyEquivalences (homotopyFiberMapOfSquare (p := p) (q := q)
      s (𝟙 B) (by simpa using comm.symm) b) := by
  exact homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences s (𝟙 B)
    (by simpa using comm.symm) b
    (mem_weakHomotopyEquivalences_of_strictFiberMaps p q s comm hF)
    (weakHomotopyEquivalences.of_isIso (𝟙 B))

-- For arbitrary projections, actual point-fiber data identifies the
-- fundamental-groupoid equivalence induced by the given map s.
example {E E' B : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (s : E ⟶ E') (comm : s ≫ q = p)
    (hF : ∀ b : B, weakHomotopyEquivalences
      (homotopyFiberMapOfSquare (p := p) (q := q) s (𝟙 B)
        (by simpa using comm.symm) b)) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map s)).IsEquivalence := by
  have h := (TopCat.mem_weakHomotopyEquivalences_iff s).mp
    (mem_weakHomotopyEquivalences_of_homotopyFiberMaps p q s comm hF)
  exact h.isEquivalence_mapFundamentalGroupoid

#print axioms TopCat.mem_weakHomotopyEquivalences_of_strictFiberMaps
#print axioms TopCat.mem_weakHomotopyEquivalences_of_homotopyFiberMaps
#print axioms SSet.KanComplex.π.group_one_eq_instOne

end TopCat

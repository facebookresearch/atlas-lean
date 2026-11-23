/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopCat.MappingCone
public import MathlibExt.Topology.Category.TopPair.HomotopyEquiv

/-!
# The cone-apex pair

The cone with its apex as subspace is pair-homotopy equivalent to the diagonal point pair.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace TopPair

/-- The cone with its apex as subspace is pair-homotopy equivalent to the diagonal point pair. -/
noncomputable def coneApexPairHomotopyEquiv
    (X : TopCat.{u}) [Nonempty X] :
    TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj (Under.mk (TopCat.conePoint X)))
      (TopPair.diag.obj (TopCat.of PUnit.{u + 1})) := by
  let P := PointedTopCat.pointedPair.obj (Under.mk (TopCat.conePoint X))
  let Q := TopPair.diag.obj (TopCat.of PUnit.{u + 1})
  change TopPair.HomotopyEquiv P Q
  let f : P ⟶ Q :=
    TopPair.ofHom (TopCat.isTerminalPUnit.from (TopCat.cone X)) (𝟙 _) (by
      apply TopCat.isTerminalPUnit.hom_ext)
  let g : Q ⟶ P :=
    TopPair.ofHom (TopCat.conePoint X) (𝟙 _) (by rfl)
  refine
    { hom := f
      inv := g
      homotopyHomInvId :=
        { fst := (TopCat.coneContractingHomotopy X).symm
          snd := TopCat.Homotopy.refl (𝟙 _)
          w := by
            apply ConcreteCategory.hom_ext
            intro p
            rcases p with ⟨p, t⟩
            cases p
            change (TopCat.coneContractingHomotopy X).symm
              (TopCat.I.homeomorph t, TopCat.conePoint X PUnit.unit) =
                TopCat.conePoint X PUnit.unit
            exact TopCat.coneContractingHomotopy_apply_conePoint X
              (unitInterval.symm (TopCat.I.homeomorph t)) PUnit.unit }
      homotopyInvHomId :=
        { fst := by
            have h : TopPair.Hom.fst (g ≫ f) =
                TopPair.Hom.fst (𝟙 Q) := by
              apply TopCat.isTerminalPUnit.hom_ext
            rw [h]
            exact TopCat.Homotopy.refl _
          snd := by
            have h : TopPair.Hom.snd (g ≫ f) =
                TopPair.Hom.snd (𝟙 Q) := by
              apply TopCat.isTerminalPUnit.hom_ext
            rw [h]
            exact TopCat.Homotopy.refl _
          w := by
            apply TopCat.isTerminalPUnit.hom_ext } }

end TopPair

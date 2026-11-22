/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceJointCoefficientNerve
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# The SAME original native raw endpoint Hom is weakly contractible

The full original joint-path category has its literal whole-vertex
terminal path. The existing genuine nerve contraction and the original
raw/joint coefficient inverse maps prove weakness of the SAME original
native raw Hom projection to the simplicial point, at every universe.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace

/-- The entire original vertex interval, containing every SAME original necklace joint. -/
def fullJointPath (T : Data) : jointPathCategory.{u} T where
  obj := {
    I := Set.univ
    left := Set.mem_univ _
    right := Set.mem_univ _
    left_le k _hk := Fin.zero_le k.down
    le_right k _hk := Fin.le_last k.down }
  property _j _hj := Set.mem_univ _

/-- Every original joint path includes into the SAME entire original vertex interval. -/
def toFullJointPath (T : Data) (P : jointPathCategory.{u} T) : P ⟶ fullJointPath T :=
  ObjectProperty.homMk ⟨⟨⟨Set.subset_univ _⟩⟩⟩

/-- The literal full original vertex interval is genuinely terminal in the SAME joint-path category. -/
def fullJointPathIsTerminal (T : Data) : IsTerminal (fullJointPath.{u} T) :=
  IsTerminal.ofUniqueHom (toFullJointPath T) (by
    intro P f
    apply ObjectProperty.hom_ext
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _)

/-- The SAME full original joint coefficient terminal projection is weak by the actual path-poset nerve contraction. -/
theorem fullCoefficient_to_point_weak (T : Data) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (fullCoefficient.{u} T)) := by
  have h := NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    (fullJointPathIsTerminal.{u} T)
  have he : (jointCoefficientNerveIso.{u} T).hom ≫
      SSet.stdSimplex.isTerminalObj₀.from (nerve (jointPathCategory T)) =
        SSet.stdSimplex.isTerminalObj₀.from (fullCoefficient T) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ RespectsIso.precomp SSet.realizationWeakEquivalences (jointCoefficientNerveIso T).hom
    (SSet.stdSimplex.isTerminalObj₀.from (nerve (jointPathCategory T))) h

/-- The SAME actual raw native endpoint Hom has its genuinely weak original projection to the simplicial point. -/
theorem rawCoefficient_to_point_weak (T : Data) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (hom T.object.{u} (sourceVertex T) (targetVertex T))) := by
  have he : (rawCoefficientIso.{u} T).hom ≫ SSet.stdSimplex.isTerminalObj₀.from (fullCoefficient T) =
      SSet.stdSimplex.isTerminalObj₀.from (hom T.object (sourceVertex T) (targetVertex T)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ RespectsIso.precomp SSet.realizationWeakEquivalences (rawCoefficientIso T).hom
    (SSet.stdSimplex.isTerminalObj₀.from (fullCoefficient T)) (fullCoefficient_to_point_weak T)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom

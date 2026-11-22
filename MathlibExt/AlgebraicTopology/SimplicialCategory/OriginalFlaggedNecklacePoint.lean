/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# The actual original point flagged category is contractible

The zero-dimensional original necklace is an actual terminal object of
the complete flagged category over the standard point in every scalar
degree. The same original point projection is genuinely weak. This uses
the original outer maps that the full-bead disjoint complex omits.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Point

open OriginalBead.TerminalFlag
open SSet.OriginalNecklace

/-- The same original standard-point vertex. -/
def vertex : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0

/-- The actual original zero-dimensional necklace. -/
def data : Data where
  dimension := 0
  joints := {0}
  source_joint := Finset.mem_singleton_self 0
  target_joint := Finset.mem_singleton_self 0

/-- The original enriched singleton coefficient in every complete scalar degree. -/
def pointCoefficient (q : SimplexCategoryᵒᵖ) : (coefficientObject.{u} 0).obj q :=
  (HomUnitsAndEmpty.unitIso (ULift.up.{u} (0 : Fin 1))).hom.app q PUnit.unit

/-- The same actual original zero necklace and whole singleton flag over the original point. -/
def object (q : SimplexCategoryᵒᵖ) : Object (Δ[0] : SSet.{u}) vertex vertex q where
  necklace := data
  input := (complex data.joints).ι
  source_eq := rfl
  target_eq := rfl
  coefficient := pointCoefficient q
  joints j hj := by
    have h : j = 0 := Finset.mem_singleton.mp hj
    subst j
    exact ((pointCoefficient q).obj 0).left

/-- The entire native original point collapse retains its same original ordinal operator. -/
def necklaceMap (T : Data) : Morphism T data where
  operator := SimplexCategory.const ⦋T.dimension⦌ ⦋0⦌ 0
  source := rfl
  target := rfl
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    apply (mem_complex_iff _ _).mpr
    intro j hj
    have h : j = 0 := Finset.mem_singleton.mp hj
    subst j
    exact Or.inr (fun i => Fin.zero_le _)

/-- Every original flagged necklace over the point has its actual original point-collapse map. -/
def toPoint {q : SimplexCategoryᵒᵖ}
    (T : Object (Δ[0] : SSet.{u}) vertex vertex q) : T ⟶ object q where
  necklaceMap := necklaceMap T.necklace
  over := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  flags := HomUnitsAndEmpty.diagonalSimplex_unique
    (ULift.up.{u} (0 : Fin 1)) q _ _

/-- The whole original point-collapse map is unique, retaining the actual original maps. -/
theorem toPoint_unique {q : SimplexCategoryᵒᵖ}
    (T : Object (Δ[0] : SSet.{u}) vertex vertex q) (f : T ⟶ object q) :
    f = toPoint T := by
  apply Hom.ext
  apply SSet.OriginalNecklace.Morphism.ext
  ext i : 3
  exact @Subsingleton.elim (Fin 1) inferInstance
    (f.necklaceMap.operator.toOrderHom i) ((toPoint T).necklaceMap.operator.toOrderHom i)

/-- The actual zero-dimensional original necklace is terminal in the complete original flagged category. -/
def isTerminal (q : SimplexCategoryᵒᵖ) : IsTerminal (object.{u} q) :=
  IsTerminal.ofUniqueHom toPoint toPoint_unique

/-- The same full original point projection from the entire native flagged-category nerve. -/
def nerveProjection (q : SimplexCategoryᵒᵖ) :
    nerve (Object (Δ[0] : SSet.{u}) vertex vertex q) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- The same original point projection is genuinely weak at every scalar degree. -/
theorem nerveProjection_weak (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (nerveProjection.{u} q) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal (isTerminal q)

/-- The entire original point projection is natural across all original scalar operators. -/
def nerveAugmentation :
    scalarNerveDiagram (Δ[0] : SSet.{u}) vertex vertex ⟶
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (Δ[0] : SSet.{u}) where
  app := nerveProjection
  naturality _q _r _f := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Every component is the same genuine original weak point projection. -/
theorem nerveAugmentation_app_weak (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (nerveAugmentation.{u}.app q) := nerveProjection_weak q

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Point

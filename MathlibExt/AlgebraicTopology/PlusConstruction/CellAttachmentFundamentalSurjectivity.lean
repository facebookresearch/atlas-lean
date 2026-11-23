/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellInnerComponents
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellQuotientVanKampen
public import MathlibExt.Topology.Homotopy.VanKampenFullness

/-!
# Surjectivity for the original two-cell inclusion

The actual annular overlap is full and essentially surjective in the inner
region. The generic two-set van Kampen fullness theorem therefore makes the
outer-region inclusion full. Composing with the constructed homotopy
equivalence from the original space to the outer region shows that the
literal inclusion into the subgroup-indexed two-cell attachment is
surjective on its original based fundamental group.

No connectedness, normality or perfectness hypothesis is needed for this
two-cell surjectivity calculation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open MathlibExt.Topology.Homotopy

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x))

/-- Fullness of the actual outer inclusion implies surjectivity of the
literal original based fundamental-group map. -/
theorem pi1Map_surjective_of_outer_full
    (hOuter : (FundamentalGroupoid.map
      (VanKampenWanted.inclusionSub
        (CellCollarCover.U X 1 (attachingMap X x P)))).Full) :
    Function.Surjective (pi1Map X x P) := by
  let i : C(X, CellCollarCover.U X 1 (attachingMap X x P)) :=
    (CellCollarDeformation.inclusionU X 1 (attachingMap X x P)).hom
  let j : C(CellCollarCover.U X 1 (attachingMap X x P), space X x P) :=
    VanKampenWanted.inclusionSub (CellCollarCover.U X 1 (attachingMap X x P))
  let I := FundamentalGroupoid.map i
  let J := FundamentalGroupoid.map j
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (CellCollarDeformation.homotopyEquiv X 1 (attachingMap X x P))
  let _ : I.IsEquivalence := E.isEquivalence_functor
  let _ : I.Full := inferInstance
  let _ : J.Full := hOuter
  let K := FundamentalGroupoid.map (inclusion X x P).hom
  have hComp : j.comp i = (inclusion X x P).hom :=
    CellQuotientVanKampen.inclusionSub_comp_inclusionU X x P
  have hMap : I ⋙ J = K := by
    exact (FundamentalGroupoid.map_comp j i).symm.trans
      (congrArg FundamentalGroupoid.map hComp)
  let hKFull : K.Full := Functor.Full.of_iso (eqToIso hMap)
  let _ : K.Full := hKFull
  intro q
  let p : K.obj (FundamentalGroupoid.mk x) ⟶
      K.obj (FundamentalGroupoid.mk x) := q.asHom
  obtain ⟨r, hr⟩ := K.map_surjective p
  refine ⟨FundamentalGroup.fromArrow r, ?_⟩
  change FundamentalGroup.mapOfEq (inclusion X x P).hom rfl
      (FundamentalGroup.fromArrow r) = q
  rw [FundamentalGroup.mapOfEq_rfl]
  apply End.ext
  exact hr

/-- The literal original inclusion into the actual subgroup-indexed
two-cell attachment is surjective on the original based fundamental group. -/
theorem pi1Map_surjective :
    Function.Surjective (pi1Map X x P) := by
  let U := CellCollarCover.U X 1 (attachingMap X x P)
  let V := CellCollarCover.V X 1 (attachingMap X x P)
  have hOuter : (FundamentalGroupoid.map
      (VanKampenWanted.inclusionSub U)).Full :=
    VanKampenWanted.inclusionSub_full_of_interRight_full_essSurj
      (CellCollarCover.isOpen_U X 1 (attachingMap X x P))
      (CellCollarCover.isOpen_V X 1 (attachingMap X x P))
      (CellCollarCover.U_union_V X 1 (attachingMap X x P))
      (CellInnerComponents.overlapInclusion_full X (attachingMap X x P))
      (CellInnerComponents.overlapInclusion_essSurj X (attachingMap X x P))
  exact pi1Map_surjective_of_outer_full X x P hOuter

end AlgebraicTopology.LoopCellAttachment

end

end

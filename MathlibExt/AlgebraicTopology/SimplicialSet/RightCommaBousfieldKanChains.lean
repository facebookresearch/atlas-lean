/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotal
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSourceWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSourceWeakEquivalenceCommonUniverse

/-!
# Chains on the right-comma Bousfield--Kan construction

The canonical map from the Bousfield--Kan homotopy colimit of the
right-comma nerve diagram to the source nerve is a realization weak
equivalence.  Consequently it is a quasi-isomorphism on simplicial chains
with arbitrary module coefficients.  Combining this with the bisimplicial
Eilenberg--Zilber equivalence identifies the homology of the signed
Bousfield--Kan total complex with the homology of the source nerve.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace SSet

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The right-comma Bousfield--Kan source map is a quasi-isomorphism on
simplicial chains with arbitrary module coefficients. -/
theorem rightCommaTotalToSource_quasiIso_chainComplexMap
    {R : Type (max u v)} [Ring R] (A : ModuleCat.{max u v} R) (F : C ⥤ D) :
    QuasiIso (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) :=
  realizationWeakEquivalences.quasiIso_chainComplexMap
    (rightCommaTotalToSource_mem_realizationWeakEquivalences_commonUniverse F) A

/-- The right-comma Bousfield--Kan source map is a quasi-isomorphism on
simplicial chains with arbitrary abelian-group coefficients. -/
theorem rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp
    (A : AddCommGrpCat.{max u v}) (F : C ⥤ D) :
    QuasiIso (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) :=
  realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp
    (rightCommaTotalToSource_mem_realizationWeakEquivalences_commonUniverse F) A

/-- The homology of the signed right-comma Bousfield--Kan total complex is
canonically the simplicial homology of the source nerve. -/
noncomputable def rightCommaBKTotalSourceHomologyIso
    {R : Type (max u v)} [Ring R] (A : ModuleCat.{max u v} R) (F : C ⥤ D) (n : ℕ) :
    (bkAlternatingTotalComplex (ModuleCat.{max u v} R) A
        (rightCommaNerveDiagram.{u, v, u} F)).homology n ≅
      ((nerve C).chainComplex A).homology n := by
  let _ : QuasiIso
      (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) :=
    rightCommaTotalToSource_quasiIso_chainComplexMap A F
  exact
    ((bkDiagonalTotalHomotopyEquiv (ModuleCat.{max u v} R) A
      (rightCommaNerveDiagram.{u, v, u} F)).toHomologyIso n).symm ≪≫
      isoOfQuasiIsoAt
        (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) n

/-- The AddCommGrp-valued signed right-comma Bousfield--Kan total complex
has the simplicial homology of the source nerve.  This is the coefficient
form used by `bkHomologySpectralSequence`. -/
-- Keep the established AddCommGrp interface name for existing clients.
@[nolint defsWithUnderscore]
noncomputable def rightCommaBKTotalSourceHomologyIso_addCommGrp
    (A : AddCommGrpCat.{max u v}) (F : C ⥤ D) (n : ℕ) :
    (bkAlternatingTotalComplex AddCommGrpCat.{max u v} A
        (rightCommaNerveDiagram.{u, v, u} F)).homology n ≅
      ((nerve C).chainComplex A).homology n := by
  let _ : QuasiIso
      (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) :=
    rightCommaTotalToSource_quasiIso_chainComplexMap_addCommGrp A F
  exact
    ((bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{max u v} A
      (rightCommaNerveDiagram.{u, v, u} F)).toHomologyIso n).symm ≪≫
      isoOfQuasiIsoAt
        (chainComplexMap (rightCommaTotalToSource.{u, v, 0} F) A) n

end SSet

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.HomotopyEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Bousfield--Kan diagonal and total complexes

Pointwise coproduct linearization commutes canonically with taking the
simplicial diagonal.  The generic bisimplicial Eilenberg--Zilber equivalence
therefore specializes to a homotopy equivalence between alternating chains
on the existing Bousfield--Kan homotopy-colimit carrier and the signed total
complex of the Bousfield--Kan homology bicomplex.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

noncomputable section

universe uJ vJ vA uA

namespace SSet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uJ vJ} A]
  {J : Type uJ} [Category.{vJ} J]

/-- Pointwise linearization of the bisimplicial Bousfield--Kan bar. -/
noncomputable abbrev bkLinearizedBisimplicial (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) : SimplicialObject (SimplicialObject A) :=
  (bisimplicialLinearizationFunctor A R).obj (bkBarBisimplicial D)

/-- Pointwise linearization of the existing Bousfield--Kan diagonal. -/
noncomputable abbrev bkLinearizedHocolim (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) : SimplicialObject A :=
  (coproductLinearizationFunctor A R).obj (bkHocolim D)

omit [Preadditive A] in
/-- Degree objects of diagonal-then-linearize and linearize-then-diagonal
agree. -/
theorem bkDiagonalLinearization_obj_eq (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) :
    ((SimplicialObject.diagonalFunctor A).obj
      (bkLinearizedBisimplicial A R D)).obj a =
      (bkLinearizedHocolim A R D).obj a := by
  rfl

/-- Linearization commutes with the Bousfield--Kan diagonal. -/
noncomputable def bkDiagonalLinearizationIso (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) :
    (SimplicialObject.diagonalFunctor A).obj
        (bkLinearizedBisimplicial A R D) ≅
      bkLinearizedHocolim A R D :=
  NatIso.ofComponents
    (fun a => eqToIso (bkDiagonalLinearization_obj_eq A R D a)) (by
      intro a b f
      rw [eqToIso.hom, eqToIso.hom]
      unfold bkLinearizedBisimplicial bkLinearizedHocolim bkHocolim
      unfold bisimplicialLinearizationFunctor coproductLinearizationFunctor
        simplicialDiagonalFunctor
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      change ((sigmaConst.obj R).map _ ≫ (sigmaConst.obj R).map _) =
        (sigmaConst.obj R).map _
      rw [← Functor.map_comp]
      rfl)

/-- Alternating chains on the two diagonal presentations are canonically
isomorphic. -/
noncomputable def bkDiagonalAlternatingComplexIso (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) :
    AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex
        (bkLinearizedBisimplicial A R D) ≅
      (AlgebraicTopology.alternatingFaceMapComplex A).obj
        (bkLinearizedHocolim A R D) :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso
    (bkDiagonalLinearizationIso A R D)

/-- Alternating chains on the Bousfield--Kan homotopy colimit are homotopy
equivalent to the signed total Bousfield--Kan complex. -/
noncomputable def bkDiagonalTotalHomotopyEquiv (R : A)
    (D : J ⥤ SSet.{max uJ vJ}) :
    HomotopyEquiv
      ((AlgebraicTopology.alternatingFaceMapComplex A).obj
        (bkLinearizedHocolim A R D))
      (bkAlternatingTotalComplex A R D) :=
  (HomotopyEquiv.ofIso (bkDiagonalAlternatingComplexIso A R D).symm).trans
    (AlgebraicTopology.BisimplicialNormalization.homotopyEquiv
      (bkLinearizedBisimplicial A R D))

/-- Homology of alternating chains on the Bousfield--Kan homotopy colimit is
canonically isomorphic to homology of the signed total complex. -/
noncomputable def bkDiagonalTotalHomologyIso
    (R : AddCommGrpCat.{max uJ vJ}) (D : J ⥤ SSet.{max uJ vJ}) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max uJ vJ}).obj
        (bkLinearizedHocolim AddCommGrpCat.{max uJ vJ} R D)).homology n ≅
      (bkAlternatingTotalComplex AddCommGrpCat.{max uJ vJ} R D).homology n :=
  (bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{max uJ vJ} R D).toHomologyIso n

/-- The fixed presentation of actual carrier chains as the original linearized
alternating complex. -/
noncomputable def bkCarrierChainIso (R : A) (D : J ⥤ SSet.{max uJ vJ}) :
    (bkHocolim D).chainComplex R ≅
      (AlgebraicTopology.alternatingFaceMapComplex A).obj
        (bkLinearizedHocolim A R D) :=
  eqToIso (by rfl)

end SSet

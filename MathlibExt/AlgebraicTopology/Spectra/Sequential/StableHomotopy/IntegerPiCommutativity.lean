/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Group.CodiagonalCommutativity
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CoproductIntegerSplitting

/-!
# Commutativity of the original integer stable groups of cofibrant spectra

The actual binary coproduct coordinate equivalence and original fold map
give a group homomorphism whose two factor restrictions are identities.
The original integer stable multiplication consequently commutes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerPiCommutativityGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (X : PointedCGWH.SequentialSpectrum.{u, v}) [IsCofibrant X]

/-- The original whole coproduct fold retains both identity summand maps. -/
def fold : X ⨿ X ⟶ X := coprod.desc (𝟙 X) (𝟙 X)

/-- The actual integer codiagonal is the original fold after the original coproduct-coordinate inverse. -/
def codiagonal (q : ℤ) : (integerStablePiFunctor q).obj X × (integerStablePiFunctor q).obj X →*
    (integerStablePiFunctor q).obj X :=
  ((integerStablePiFunctor q).map (fold X)).hom.comp
    (CoproductIntegerSplittingGeometry.equiv (B := B) X X q).symm.toMonoidHom

/-- The whole original left inclusion makes the codiagonal restrict to the identity. -/
theorem codiagonal_left (q : ℤ) (x : (integerStablePiFunctor q).obj X) :
    codiagonal (B := B) X q (x, 1) = x := by
  let F := integerStablePiFunctor.{u, v} q
  let e := CoproductIntegerSplittingGeometry.equiv (B := B) X X q
  let i : X ⟶ X ⨿ X := coprod.inl
  have he : e.symm (x, 1) = (F.map i).hom x := by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (CoproductIntegerSplittingGeometry.equiv_inl (B := B) X X q x).symm
  have hf : F.map i ≫ F.map (fold X) = 𝟙 (F.obj X) :=
    (F.map_comp i (fold X)).symm.trans
      ((F.congr_map (coprod.inl_desc (𝟙 X) (𝟙 X))).trans (F.map_id X))
  change (F.map (fold X)).hom (e.symm (x, 1)) = x
  rw [he]
  exact ConcreteCategory.congr_hom hf x

/-- The whole original right inclusion makes the codiagonal restrict to the identity. -/
theorem codiagonal_right (q : ℤ) (x : (integerStablePiFunctor q).obj X) :
    codiagonal (B := B) X q (1, x) = x := by
  let F := integerStablePiFunctor.{u, v} q
  let e := CoproductIntegerSplittingGeometry.equiv (B := B) X X q
  let i : X ⟶ X ⨿ X := coprod.inr
  have he : e.symm (1, x) = (F.map i).hom x := by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (CoproductIntegerSplittingGeometry.equiv_inr (B := B) X X q x).symm
  have hf : F.map i ≫ F.map (fold X) = 𝟙 (F.obj X) :=
    (F.map_comp i (fold X)).symm.trans
      ((F.congr_map (coprod.inr_desc (𝟙 X) (𝟙 X))).trans (F.map_id X))
  change (F.map (fold X)).hom (e.symm (1, x)) = x
  rw [he]
  exact ConcreteCategory.congr_hom hf x

/-- Every original integer stable group of a cofibrant native spectrum is commutative. -/
theorem mul_comm (q : ℤ) (a b : (integerStablePiFunctor q).obj X) : a * b = b * a :=
  MonoidHom.CodiagonalCommutativity.mul_comm (codiagonal (B := B) X q)
    (codiagonal_left X q) (codiagonal_right X q) a b

/-- The commutative structure keeps the entire original integer stable group. -/
def commGroup (q : ℤ) : CommGroup ((integerStablePiFunctor q).obj X) :=
  MonoidHom.CodiagonalCommutativity.commGroup (codiagonal (B := B) X q)
    (codiagonal_left X q) (codiagonal_right X q)

/-- The new commutative integer structure has the whole old group record. -/
theorem commGroup_toGroup (q : ℤ) : (commGroup (B := B) X q).toGroup =
    inferInstanceAs (Group ((integerStablePiFunctor q).obj X)) := rfl

end PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerPiCommutativityGeometry

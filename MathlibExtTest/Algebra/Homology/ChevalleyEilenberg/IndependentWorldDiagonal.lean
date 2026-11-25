/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.HomologyDiagonal
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# A nonzero CE homology diagonal with independent scalar and carrier worlds

The scalar field is `ℚ : Type 0`, the Lie carrier is `ULift.{1} ℚ : Type 1`,
and the working category is `ModuleCat.{1} ℚ`. The actual raw coaugmentation
class of the lifted scalar 7 is nonzero. Its actual diagonal into homology
of the native tensor square is nonzero by the actual counit retraction.
This client invokes no same-world Künneth map or collapse theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ChevalleyEilenbergTest.IndependentWorldDiagonal

abbrev L : Type 1 := ULift.{1} ℚ

local instance liftedLieRing : LieRing L := LieRing.ofAssociativeRing
local instance liftedAlgebra : Algebra ℚ L := (ULift.ringEquiv : L ≃+* ℚ).symm.toRingHom.toAlgebra


/-- The larger carrier still uses the original rational scalar action. -/
theorem scalar_action_down (r : ℚ) (x : L) : (r • x).down = r * x.down := rfl

def unitHomologyIso : (ChevalleyEilenberg.nativeUnitComplex.{0,1} ℚ).homology 0 ≅ ModuleCat.of ℚ (ULift.{1} ℚ) :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
    (ModuleCat.of ℚ (ULift.{1} ℚ))

def unitClassSeven : (ChevalleyEilenberg.nativeUnitComplex.{0,1} ℚ).homology 0 := unitHomologyIso.inv (ULift.up (7 : ℚ))

def classSeven : ((ChevalleyEilenberg.canonicalChainData ℚ L).complex).homology 0 :=
  (ChevalleyEilenberg.HomologyCoalgebra.homologyCoaugRaw ℚ L) 0 unitClassSeven

theorem counit_classSeven : unitHomologyIso.hom ((ChevalleyEilenberg.HomologyCoalgebra.homologyCounitRaw ℚ L) 0
  classSeven) = ULift.up (7 : ℚ) := by
  have h := congrFun (ChevalleyEilenberg.HomologyCoalgebra.homologyCoaugRaw_counit ℚ L) 0
  have hv := congrArg (fun f => f unitClassSeven) h
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hv
  rw [show (ChevalleyEilenberg.HomologyCoalgebra.homologyCounitRaw ℚ L) 0 classSeven = unitClassSeven from hv]
  have hi := congrArg (fun f => f (ULift.up (7 : ℚ))) unitHomologyIso.inv_hom_id
  simpa only [unitClassSeven, CategoryTheory.comp_apply, CategoryTheory.id_apply] using hi

theorem classSeven_ne_zero : classSeven ≠ 0 := by
  intro h
  have hv := counit_classSeven
  have h0 := congrArg (fun a => unitHomologyIso.hom.hom
    ((ChevalleyEilenberg.HomologyCoalgebra.homologyCounitRaw ℚ L 0).hom a)) h
  have hz : unitHomologyIso.hom.hom
      ((ChevalleyEilenberg.HomologyCoalgebra.homologyCounitRaw ℚ L 0).hom 0) = 0 :=
    (congrArg unitHomologyIso.hom.hom
      (ChevalleyEilenberg.HomologyCoalgebra.homologyCounitRaw ℚ L 0).hom.map_zero).trans
      unitHomologyIso.hom.hom.map_zero
  have he := hz.symm.trans (h0.symm.trans hv)
  have hd := congrArg ULift.down he
  change (0 : ℚ) = 7 at hd
  norm_num at hd

/-- A genuinely nonzero class maps to a genuinely nonzero class in homology
of the actual larger-world tensor square. -/
theorem diagonal_classSeven_ne_zero : (ChevalleyEilenberg.HomologyCoalgebra.canonicalToTensorHomologyRaw ℚ L) 0
  classSeven ≠ 0 := by
  intro h
  have hr := congrFun
    (ChevalleyEilenberg.HomologyCoalgebra.canonicalToTensorHomologyRaw_retraction ℚ L) 0
  have hv := congrArg (fun f => f classSeven) hr
  change (ChevalleyEilenberg.HomologyCoalgebra.rawDiagonalRetraction ℚ L 0).hom
    ((ChevalleyEilenberg.HomologyCoalgebra.canonicalToTensorHomologyRaw ℚ L 0).hom classSeven) =
    classSeven at hv
  have hzero := congrArg (ChevalleyEilenberg.HomologyCoalgebra.rawDiagonalRetraction ℚ L 0).hom h
  exact classSeven_ne_zero (hv.symm.trans (hzero.trans
    (ChevalleyEilenberg.HomologyCoalgebra.rawDiagonalRetraction ℚ L 0).hom.map_zero))

end ChevalleyEilenbergTest.IndependentWorldDiagonal

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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniverseHomologyCoalgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# An actual independent-world CE homology coalgebra over the original field

The original scalar field is `ℚ : Type 0`, and the original Lie carrier is
`ULift.{1} ℚ : Type 1`. The actual CE homology comonoid is produced from
the earned original-Q larger-world cycle Künneth theorem. Its actual
coaugmentation of lifted scalar 7 is nonzero by its actual native counit
law. The primitive comparison is the genuine native kernel lift; no
kernel/homology isomorphism or caller coalgebra certificate is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace ChevalleyEilenbergTest.ActualIndependentWorldHomologyCoalgebra

abbrev L : Type 1 := ULift.{1} ℚ
local instance liftedLieRing : LieRing L := LieRing.ofAssociativeRing
local instance liftedAlgebra : Algebra ℚ L := (ULift.ringEquiv : L ≃+* ℚ).symm.toRingHom.toAlgebra


local instance actualHomologyComonoid : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R :=
  ℚ)).obj ((ChevalleyEilenberg.canonicalChainData ℚ L).complex)) :=
  ChevalleyEilenberg.UniverseHomologyCoalgebra.homologyComonObj ℚ L
local instance actualUnitComonoid : ComonObj (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{0,1}
  ℚ))) := ComonObj.instTensorUnit (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ))

def actualPoint : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ)) ⟶
  (HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).obj ((ChevalleyEilenberg.canonicalChainData ℚ
    L).complex) :=
  ChevalleyEilenberg.UniverseHomologyCoalgebra.homologyCoaug ℚ L

open scoped ModuleCat.UniverseTensor

local instance : HasFiniteBiproducts (ModuleCat.{1} ℚ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{1} ℚ)
local instance : MonoidalClosed (ModuleCat.{1} ℚ) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{0,1} (R := ℚ)
local instance : ComonObj ((ChevalleyEilenberg.canonicalChainData ℚ L).complex :
    ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ) ℕ) :=
  ChevalleyEilenberg.nativeComonObj ℚ L

local instance canonicalChainComon :
    let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ) ℕ :=
      (ChevalleyEilenberg.canonicalChainData ℚ L).complex
    ComonObj C := ChevalleyEilenberg.nativeComonObj ℚ L

local instance actualPointIsComonHom : IsComonHom actualPoint :=
  ChevalleyEilenberg.UniverseHomologyCoalgebra.homologyCoaugIsComonHom ℚ L

def unitSeven : (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ))) 0 :=
  (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ))).inv
    (ULift.up (7 : ℚ))

def classSeven : ((ChevalleyEilenberg.canonicalChainData ℚ L).complex).homology 0 := actualPoint 0 unitSeven

theorem actual_counit_coordinate :
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ))).hom
      (ε[(HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).obj
        ((ChevalleyEilenberg.canonicalChainData ℚ L).complex)] 0 classSeven) = ULift.up (7 : ℚ) := by
  have h := congrFun (IsComonHom.hom_counit actualPoint) 0
  have hv := congrArg (fun f => f unitSeven) h
  simp only [CategoryTheory.comp_apply, ComonObj.instTensorUnit_counit,
    CategoryTheory.id_apply] at hv
  rw [show ε[(HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).obj
    ((ChevalleyEilenberg.canonicalChainData ℚ L).complex)] 0 classSeven = unitSeven from hv]
  have hi := congrArg (fun f => f (ULift.up (7 : ℚ)))
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ))).inv_hom_id
  simpa only [unitSeven, CategoryTheory.comp_apply, CategoryTheory.id_apply] using hi

theorem actual_classSeven_ne_zero : classSeven ≠ 0 := by
  intro h
  have hv := actual_counit_coordinate
  let ε₀ := (ComonObj.counit (X :=
    (HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).obj
      ((ChevalleyEilenberg.canonicalChainData ℚ L).complex))) 0
  let e := GradedObject.Monoidal.tensorUnit₀ (I := ℕ)
    (C := ModuleCat.UniverseScalarRestriction.Modules.{0,1} ℚ)
  have h0 := congrArg (fun a => e.hom.hom (ε₀.hom a)) h
  have hz : e.hom.hom (ε₀.hom 0) = 0 :=
    (congrArg e.hom.hom ε₀.hom.map_zero).trans e.hom.hom.map_zero
  have he := hz.symm.trans (h0.symm.trans hv)
  have hd := congrArg ULift.down he
  change (0 : ℚ) = 7 at hd
  norm_num at hd

/-- This endpoint is the actual canonical homology coproduct specification,
in the original field and actual larger coefficient category. -/
theorem actual_comul_is_canonical :
    Δ[(HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).obj ((ChevalleyEilenberg.canonicalChainData
      ℚ L).complex)] ≫ HomologicalComplex.UniverseKunneth.tensorator ((ChevalleyEilenberg.canonicalChainData ℚ
        L).complex) ((ChevalleyEilenberg.canonicalChainData ℚ L).complex) =
      (HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).map (ChevalleyEilenberg.nativeComplexComul ℚ
        L) :=
  ChevalleyEilenberg.UniverseHomologyCoalgebra.homologyComul_canonical ℚ L

/-- The comparison is the actual homology map of the original primitive inclusion
after the actual graded primitive-kernel inclusion. No isomorphism is asserted. -/
theorem actual_primitive_comparison_inclusion :
    ChevalleyEilenberg.UniverseHomologyCoalgebra.primitiveHomologyComparison ℚ L ≫
      kernel.ι (HomologicalComplex.UniverseKunneth.homologyPrimitiveEquation ((ChevalleyEilenberg.canonicalChainData ℚ
        L).complex)
        (ChevalleyEilenberg.nativeComplexCoaug ℚ L)) =
      (HomologicalComplex.UniverseKunneth.homologyFunctor.{0,1} (R := ℚ)).map
        (ChevalleyEilenberg.nativePrimitiveInclusion ℚ L) :=
  ChevalleyEilenberg.UniverseHomologyCoalgebra.primitiveHomologyComparison_inclusion ℚ L

end ChevalleyEilenbergTest.ActualIndependentWorldHomologyCoalgebra

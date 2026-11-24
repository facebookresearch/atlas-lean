/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeTensorProjectionMaps

/-!
# Computed cohomology restriction and shift maps

Restriction of scalar rings is fixed on every original module section
and every derived cochain unit. The higher map is built from native
cohomology transport, that source square, and the original exact
restriction unit. The shift identifications are the native derived and
cochain shift factors. These are the scalar identifications needed to
read the K-linear Gauss--Manin cochain boundary on an O_Y-module carrier.

Native Mathlib source: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Reference: Scholze, arXiv:1205.3463v2, Theorem 8.8.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeRestrictionCohomologyMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations NativeFilteredDeRhamOutputs
open NativeScalarProjectionMaps

attribute [local instance] HasDerivedCategory.standard

/-- An intermediate exactness source, fixed on the native cochain resolution units. -/
class ExactCochainUnit {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [EnoughInjectives A] where
  unitIso : ∀ K : CochainComplex.Plus A, IsIso (F.rightDerivedFunctorPlusUnit.app K)

attribute [instance] ExactCochainUnit.unitIso

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (KY SY : Sheaf J CommRingCat.{1}) (KX SX : Sheaf T CommRingCat.{1})
  (ay : KY ⟶ SY) (ax : KX ⟶ SX)
  (k : KY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj KX)
  (s : SY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj SX)
  [(pushforward G KY KX k).IsRightAdjoint] [(pushforward G SY SX s).IsRightAdjoint]
  [EnoughInjectives (Modules KY)] [EnoughInjectives (Modules SY)]
  [EnoughInjectives (Modules KX)] [EnoughInjectives (Modules SX)]

abbrev restrictY := restrict KY SY ay
abbrev restrictX := restrict KX SX ax

local instance restrictYAdditive : (restrictY KY SY ay).Additive := by
  unfold restrictY restrict
  infer_instance

local instance restrictXAdditive : (restrictX KX SX ax).Additive := by
  unfold restrictX restrict
  infer_instance

/-- A scalar-restriction square whose ordinary values and original cochain units are fixed. -/
structure SourceSquare where
  ring_square : ay ≫ s = k ≫ (G.sheafPushforwardContinuous CommRingCat.{1} J T).map ax
  ordinary : pushforward G SY SX s ⋙ restrictY KY SY ay ≅
    restrictX KX SX ax ⋙ pushforward G KY KX k
  ordinary_source : ∀ (M : Modules SX) (U : Cᵒᵖ) (x : M.val.obj (G.op.obj U)),
    (((ordinary.hom.app M).val.app U).hom x) = x
  derived : derivedPushforward G SY SX s ⋙ (restrictY KY SY ay).rightDerivedFunctorPlus ≅
    (restrictX KX SX ax).rightDerivedFunctorPlus ⋙ derivedPushforward G KY KX k
  cochain_source : ∀ K : CochainComplex.Plus (Modules SX),
    (restrictY KY SY ay).rightDerivedFunctorPlusUnit.app
      ((pushforward G SY SX s).mapCochainComplexPlus.obj K) ≫
      (restrictY KY SY ay).rightDerivedFunctorPlus.map
        ((pushforward G SY SX s).rightDerivedFunctorPlusUnit.app K) ≫
      derived.hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map (ordinary.hom.mapCochainComplexPlus.app K) ≫
      (pushforward G KY KX k).rightDerivedFunctorPlusUnit.app
        ((restrictX KX SX ax).mapCochainComplexPlus.obj K) ≫
      (derivedPushforward G KY KX k).map
        ((restrictX KX SX ax).rightDerivedFunctorPlusUnit.app K)

variable (Q : SourceSquare G KY SY KX SX ay ax k s)
  [PreservesFiniteLimits (restrictY KY SY ay)] [PreservesFiniteColimits (restrictY KY SY ay)]
  [ExactCochainUnit (restrictX KX SX ax)]

/-- The actual higher cohomology scalar restriction map on the specified original cochains. -/
def cohomologyMap (K : CochainComplex.Plus (Modules SX)) (i : ℤ) :
    (restrictY KY SY ay).obj
      (cohomology SY ((derivedPushforward G SY SX s).obj (DerivedCategory.Plus.Q.obj K)) i) ⟶
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj ((restrictX KX SX ax).mapCochainComplexPlus.obj K))) i :=
  DerivedCohomology.map (restrictY KY SY ay)
    ((derivedPushforward G SY SX s).obj (DerivedCategory.Plus.Q.obj K)) i ≫
    (DerivedCategory.Plus.homologyFunctor (Modules KY) i).map
      (Q.derived.hom.app (DerivedCategory.Plus.Q.obj K)) ≫
    (DerivedCategory.Plus.homologyFunctor (Modules KY) i).map
      ((derivedPushforward G KY KX k).map
        (inv ((restrictX KX SX ax).rightDerivedFunctorPlusUnit.app K)))

section Shifts

variable (S : Sheaf J CommRingCat.{1})

/-- Native derived cohomology of a shifted complex, with the exact cohomological sign. -/
def cohomologyShiftIso (K : Derived S) (n i j : ℤ) (h : n + i = j) :
    cohomology S (K⟦n⟧) i ≅ cohomology S K j :=
  (DerivedCategory.homologyFunctor (Modules S) i).mapIso
    (((DerivedCategory.Plus.ι (C := Modules S)).commShiftIso n).app K) ≪≫
      ((DerivedCategory.homologyFunctor (Modules S) 0).shiftIso n i j h).app K.obj

end Shifts

end MathlibExt.CategoryTheory.NativeRestrictionCohomologyMaps

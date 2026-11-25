/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeGaussManinOutputs

/-!
# Constructed relative period comparison maps

The original relative complex is linear over the inverse image of the
BASE ring. The actual period complex is constructed degreewise over
the ORIGINAL O_X with its TOTAL relative connection, and is linear over
the inverse image of the BASE structural period ring. Tensoring the
original complex naively over O_X would not define a complex.

The extension map here is the native derived-adjunction mate of the
original source cochain unit. The comparison is the original native
scalar projection followed by that map and native cohomology. No final
comparison morphism or higher bundle is an input, and no IsIso of the
final maps is assumed.

References: Scholze, arXiv:1205.3463v2, Proposition 8.5, Lemma 8.6 and
Theorem 8.8; completed Stacks de Rham source, Tag 07I0.
Native Mathlib: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeRelativePeriodComparisonMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations NativeScalarProjectionMaps

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (SY TY : Sheaf J CommRingCat.{1}) (SX TX : Sheaf T CommRingCat.{1})
  (sy : SY ⟶ TY) (sx : SX ⟶ TX)
  (s : SY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj SX)
  (t : TY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj TX)
  [(pushforward G SY SX s).IsRightAdjoint] [(pushforward G TY TX t).IsRightAdjoint]
  [(pushforward (𝟭 C) SY TY sy).IsRightAdjoint] [(pushforward (𝟭 D) SX TX sx).IsRightAdjoint]
  [EnoughInjectives (Modules SY)] [EnoughInjectives (Modules TY)]
  [EnoughInjectives (Modules SX)] [EnoughInjectives (Modules TX)]
  [PullbackSourceUnit G SY SX s] [PullbackSourceUnit G TY TX t]
  [PullbackSourceUnit (𝟭 D) SX TX sx]
  (Q : SourceSquare G SY TY SX TX sy sx s t)
  (A : DerivedAdjunctionSource G SY SX s) (B : DerivedAdjunctionSource G TY TX t)
  (E : DerivedAdjunctionSource (𝟭 D) SX TX sx)
  (K : CochainComplex.Plus (Modules SX)) (P : CochainComplex.Plus (Modules TX))
  (unit : K ⟶ (pushforward (𝟭 D) SX TX sx).mapCochainComplexPlus.obj P)

/-- The ordinary source cochain unit, through the ORIGINAL native right-derived restriction unit. -/
def sourceUnit : DerivedCategory.Plus.Q.obj K ⟶
    (derivedPushforward (𝟭 D) SX TX sx).obj (DerivedCategory.Plus.Q.obj P) :=
  DerivedCategory.Plus.Q.map unit ≫
    (pushforward (𝟭 D) SX TX sx).rightDerivedFunctorPlusUnit.app P

/-- Native derived-adjunction mate; no desired comparison map is supplied. -/
def extensionMap :
    (scalarX SX TX sx).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ⟶
      DerivedCategory.Plus.Q.obj P :=
  (E.adj.homEquiv (DerivedCategory.Plus.Q.obj K) (DerivedCategory.Plus.Q.obj P)).symm
    (sourceUnit SX TX sx K P unit)

def derivedComparison :
    (scalarY SY TY sy).rightDerivedFunctorPlus.obj
      ((derivedPushforward G SY SX s).obj (DerivedCategory.Plus.Q.obj K)) ⟶
    (derivedPushforward G TY TX t).obj (DerivedCategory.Plus.Q.obj P) :=
  projection G SY TY SX TX sy sx s t Q A B (DerivedCategory.Plus.Q.obj K) ≫
    (derivedPushforward G TY TX t).map (extensionMap SX TX sx E K P unit)

variable [PreservesFiniteLimits (scalarY SY TY sy)] [PreservesFiniteColimits (scalarY SY TY sy)]

/-- The canonical native higher comparison to the constructed period cohomology target. -/
def degreeComparison (i : ℤ) :
    (scalarY SY TY sy).obj
      (cohomology SY ((derivedPushforward G SY SX s).obj (DerivedCategory.Plus.Q.obj K)) i) ⟶
    cohomology TY ((derivedPushforward G TY TX t).obj (DerivedCategory.Plus.Q.obj P)) i :=
  degreeProjection G SY TY SX TX sy sx s t Q A B (DerivedCategory.Plus.Q.obj K) i ≫
    (DerivedCategory.Plus.homologyFunctor (Modules TY) i).map
      ((derivedPushforward G TY TX t).map (extensionMap SX TX sx E K P unit))

end MathlibExt.CategoryTheory.NativeRelativePeriodComparisonMaps

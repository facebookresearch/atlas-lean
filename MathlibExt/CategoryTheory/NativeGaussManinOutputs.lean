/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRestrictionCohomologyMaps

/-!
# Native Gauss--Manin output carrier and cochain boundary

The K-linear boundary comes from the actual short exact sequence
`0 -> f^*Omega_Y tensor DR_X/Y(E)[-1] -> DR_X/K(E)/L^2 -> DR_X/Y(E) -> 0`.
Its middle object is the native cokernel of the original two-base-form
wedge map. Every higher carrier and all scalar/tensor/shift maps are
computed from native functors and the original cochain units.

`CanonicalConnection` is an OUTPUT request on the actual higher de Rham
carrier. Its equation fixes its map through this constructed boundary
and the native finite-form projection; no final flat bundle is input.
Isomorphism of the intermediate tensor projection is requested with its
finite-form guard separately from the final period comparisons.

References: Scholze, arXiv:1205.3463v2, Proposition 8.5 and Theorem 8.8;
Stacks Tags 07HY and 07I0 for the original connection complex.
Native Mathlib source: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeGaussManinOutputs

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations RingSheafModuleTensors NativeFilteredDeRhamOutputs
open NativeRestrictionCohomologyMaps

attribute [local instance] HasDerivedCategory.standard

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
  [PullbackSourceUnit G SY SX s]
  (Ω : Modules SY) (F : FilteredComplex SX)

abbrev TX := NativeTensorProjectionMaps.tensorX G SY SX s Ω
abbrev TY := NativeTensorProjectionMaps.tensorY SY Ω
abbrev FX := restrictX KX SX ax
abbrev FY := restrictY KY SY ay

variable [(TX G SY SX s Ω).Additive] [(TY SY Ω).Additive]
  [(FX KX SX ax).Additive] [(FY KY SY ay).Additive]

local instance derivedKShift : (derivedPushforward G KY KX k).CommShift ℤ := by
  unfold derivedPushforward
  infer_instance

def relativeK : CochainComplex.Plus (Modules KX) :=
  (FX KX SX ax).mapCochainComplexPlus.obj F.total

def tensorK : CochainComplex.Plus (Modules KX) :=
  (FX KX SX ax).mapCochainComplexPlus.obj ((TX G SY SX s Ω).mapCochainComplexPlus.obj F.total)

def kernelK : CochainComplex.Plus (Modules KX) := (tensorK G SY KX SX ax s Ω F)⟦(-1 : ℤ)⟧

/-- The kernel generator uses the ORIGINAL tensor sheafification unit and native cochain shift. -/
def kernelUnit (i : ℤ) (V : Dᵒᵖ) (m : (F.total.obj.X i).val.obj V)
    (w : ((pullback G SY SX s).obj Ω).val.obj V) :
    ((kernelK G SY KX SX ax s Ω F).obj.X (i + 1)).val.obj V :=
  (((((CochainComplex.Plus.ι (Modules KX)).commShiftIso (-1 : ℤ)).inv.app
      (tensorK G SY KX SX ax s Ω F)).f (i + 1)).val.app V).hom
    ((((CochainComplex.shiftFunctorObjXIso (tensorK G SY KX SX ax s Ω F).obj (-1) (i + 1) i
      (by omega)).inv.val.app V).hom)
      (show ((tensorK G SY KX SX ax s Ω F).obj.X i).val.obj V from
        generator SX (F.total.obj.X i) ((pullback G SY SX s).obj Ω) V m w))

/-- The original absolute complex and base-two wedge are qualified on analytic charts outside
this generic constructor. Their middle object here is a NATIVE cokernel. -/
structure CofactorSource where
  absolute : CochainComplex.Plus (Modules KX)
  baseTwo : CochainComplex.Plus (Modules KX)
  wedge : baseTwo ⟶ absolute
  inclusion : kernelK G SY KX SX ax s Ω F ⟶ cokernel wedge
  projection : cokernel wedge ⟶ relativeK KX SX ax F
  zero : inclusion ≫ projection = 0
  exact : (underlyingShortComplex (kernelK G SY KX SX ax s Ω F) (cokernel wedge)
    (relativeK KX SX ax F) inclusion projection zero).ShortExact

variable (B : CofactorSource G SY KX SX ax s Ω F)

/-- The ORIGINAL native short-exact cochain boundary, pushed forward before cohomology. -/
def cochainBoundary :
    (derivedPushforward G KY KX k).obj (DerivedCategory.Plus.Q.obj (relativeK KX SX ax F)) ⟶
    ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F)))⟦(1 : ℤ)⟧ :=
  (derivedPushforward G KY KX k).map
    (boundary (kernelK G SY KX SX ax s Ω F) (cokernel B.wedge)
      (relativeK KX SX ax F) B.inclusion B.projection B.zero B.exact) ≫
    ((derivedPushforward G KY KX k).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F))

def rawBoundary (i : ℤ) :
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (relativeK KX SX ax F))) i ⟶
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F))) (i + 1) :=
  (DerivedCategory.Plus.homologyFunctor (Modules KY) i).map
    (cochainBoundary G KY SY KX SX ax k s Ω F B) ≫
    (cohomologyShiftIso (S := KY)
      ((derivedPushforward G KY KX k).obj
        (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F))) 1 i (i + 1) (by omega)).hom

def kernelShiftIso (i : ℤ) :
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F))) (i + 1) ≅
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (tensorK G SY KX SX ax s Ω F))) i :=
  (DerivedCategory.Plus.homologyFunctor (Modules KY) (i + 1)).mapIso
    ((derivedPushforward G KY KX k).mapIso
      (((DerivedCategory.Plus.Q (C := Modules KX)).commShiftIso (-1 : ℤ)).app
        (tensorK G SY KX SX ax s Ω F)) ≪≫
      ((derivedPushforward G KY KX k).commShiftIso (-1 : ℤ)).app
        (DerivedCategory.Plus.Q.obj (tensorK G SY KX SX ax s Ω F))) ≪≫
    cohomologyShiftIso (S := KY)
      ((derivedPushforward G KY KX k).obj
        (DerivedCategory.Plus.Q.obj (tensorK G SY KX SX ax s Ω F))) (-1) (i + 1) i (by omega)

variable (Q : NativeRestrictionCohomologyMaps.SourceSquare G KY SY KX SX ay ax k s)
  (P : NativeTensorProjectionMaps.SourceSquare G SY SX s Ω)
  (A : DerivedAdjunctionSource G SY SX s)
  [PreservesFiniteLimits (FY KY SY ay)] [PreservesFiniteColimits (FY KY SY ay)]
  [PreservesFiniteLimits (TY SY Ω)] [PreservesFiniteColimits (TY SY Ω)]
  [ExactCochainUnit (FX KX SX ax)] [ExactCochainUnit (TX G SY SX s Ω)]

/-- Higher K-linear carrier identification from the original scalar restriction cochain units. -/
def frontMap (i : ℤ) :=
  cohomologyMap G KY SY KX SX ay ax k s Q F.total i

/-- Native tensor/shift projection to the cochain-boundary target; no IsIso is assumed here. -/
def targetMap (i : ℤ) :
    (FY KY SY ay).obj ((TY SY Ω).obj (higherDeRham G SY SX s F i)) ⟶
    cohomology KY ((derivedPushforward G KY KX k).obj
      (DerivedCategory.Plus.Q.obj (kernelK G SY KX SX ax s Ω F))) (i + 1) :=
  (FY KY SY ay).map
    (NativeTensorProjectionMaps.degree G SY SX s Ω P A (DerivedCategory.Plus.Q.obj F.total) i ≫
      (DerivedCategory.Plus.homologyFunctor (Modules SY) i).map
        ((derivedPushforward G SY SX s).map
          (inv ((TX G SY SX s Ω).rightDerivedFunctorPlusUnit.app F.total)))) ≫
    cohomologyMap G KY SY KX SX ay ax k s Q ((TX G SY SX s Ω).mapCochainComplexPlus.obj F.total) i ≫
    (kernelShiftIso G KY SY KX SX ax k s Ω F i).inv

/-- The actual higher connection map is the normalized cochain boundary transported through
the native tensor/shift target map. Its being a connection and its flatness are proof outputs. -/
def connectionMap (i : ℤ)
    [IsIso (targetMap G KY SY KX SX ay ax k s Ω F Q P A i)] :
    (FY KY SY ay).obj (higherDeRham G SY SX s F i) ⟶
    (FY KY SY ay).obj ((TY SY Ω).obj (higherDeRham G SY SX s F i)) :=
  frontMap G KY SY KX SX ay ax k s F Q i ≫
    rawBoundary G KY SY KX SX ax k s Ω F B i ≫
    inv (targetMap G KY SY KX SX ay ax k s Ω F Q P A i)

omit [(pushforward G KY KX k).IsRightAdjoint] [EnoughInjectives (Modules KY)]
  [(FY KY SY ay).Additive] in
theorem connectionMap_boundary (i : ℤ)
    [IsIso (targetMap G KY SY KX SX ay ax k s Ω F Q P A i)] :
    connectionMap G KY SY KX SX ay ax k s Ω F B Q P A i ≫
        targetMap G KY SY KX SX ay ax k s Ω F Q P A i =
      frontMap G KY SY KX SX ay ax k s F Q i ≫
        rawBoundary G KY SY KX SX ax k s Ω F B i := by
  simp [connectionMap, Category.assoc]

/-- The higher connection is OUTPUT on the constructed native higher de Rham carrier.
The boundary equation fixes its actual map; the base differential is original source input. -/
structure CanonicalConnection (i : ℤ)
    (d : ∀ U : Cᵒᵖ, SY.obj.obj U →+ Ω.val.obj U) where
  map : (FY KY SY ay).obj (higherDeRham G SY SX s F i) ⟶
    (FY KY SY ay).obj ((TY SY Ω).obj (higherDeRham G SY SX s F i))
  leibniz : ∀ (U : Cᵒᵖ) (a : SY.obj.obj U) (x : (higherDeRham G SY SX s F i).val.obj U),
    letI : Module (SY.obj.obj U)
        (((FY KY SY ay).obj ((TY SY Ω).obj (higherDeRham G SY SX s F i))).val.obj U) :=
      inferInstanceAs (Module (SY.obj.obj U)
        (((TY SY Ω).obj (higherDeRham G SY SX s F i)).val.obj U))
    (map.val.app U).hom (a • x) = a • (map.val.app U).hom x +
      (show ((FY KY SY ay).obj ((TY SY Ω).obj (higherDeRham G SY SX s F i))).val.obj U from
        generator SY (higherDeRham G SY SX s F i) Ω U x (d U a))
  boundary_source : map ≫ targetMap G KY SY KX SX ay ax k s Ω F Q P A i =
    frontMap G KY SY KX SX ay ax k s F Q i ≫ rawBoundary G KY SY KX SX ax k s Ω F B i

omit [(pushforward G KY KX k).IsRightAdjoint] [EnoughInjectives (Modules KY)]
  [(FY KY SY ay).Additive] in
/-- Under the separately proved projection isomorphism, the source boundary fixes the output
connection to the constructed map. -/
theorem CanonicalConnection.map_source (i : ℤ)
    (d : ∀ U : Cᵒᵖ, SY.obj.obj U →+ Ω.val.obj U)
    (N : CanonicalConnection G KY SY KX SX ay ax k s Ω F B Q P A i d)
    [IsIso (targetMap G KY SY KX SX ay ax k s Ω F Q P A i)] :
    N.map = connectionMap G KY SY KX SX ay ax k s Ω F B Q P A i := by
  apply (cancel_mono (targetMap G KY SY KX SX ay ax k s Ω F Q P A i)).1
  exact N.boundary_source.trans
    (connectionMap_boundary G KY SY KX SX ay ax k s Ω F B Q P A i).symm

end MathlibExt.CategoryTheory.NativeGaussManinOutputs

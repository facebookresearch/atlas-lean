/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeGaussManinOutputs
public import MathlibExt.RingTheory.ContinuousDeRhamQuotients

/-!
# Original-form normalization of the Gauss--Manin cochain source

The absolute complex is fixed by the original base connection. L^2 has
the native IMAGE terms of the two-base-form wedge. Its map is fixed on
all original native tensor/exterior units. The relative quotient and
kernel inclusion are likewise fixed on the actual form projections,
native tensor units and ORIGINAL cochain shift units. Rescaling the
extension or substituting an arbitrary higher connection cannot satisfy
these equations.

Reference: the Gauss--Manin cochain exact sequence for relative de Rham
cohomology, used in Scholze, arXiv:1205.3463v2, Theorem 8.8.
Native Mathlib source: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`; completed connection source,
AxiomMath/Stacks `c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.GaussManinCofactorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations RingSheafModuleTensors NativeRingInverseImages
open NativeFilteredDeRhamOutputs NativeGaussManinOutputs

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (SY : Sheaf J CommRingCat.{1}) (KX SX OX : Sheaf T CommRingCat.{1})
  (ax : KX ⟶ SX) (η : SX ⟶ OX)
  (s : SY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj SX)
  [(pushforward G SY SX s).IsRightAdjoint]
  [EnoughInjectives (Modules SY)] [EnoughInjectives (Modules SX)]
  [PullbackSourceUnit G SY SX s]
  (ΩY : Modules SY) (F : FilteredComplex SX)
  [(NativeTensorProjectionMaps.tensorX G SY SX s ΩY).Additive]
  [(NativeRestrictionCohomologyMaps.restrictX KX SX ax).Additive]
  (M ΩA ΩR : Modules OX)
  (absolute : CochainComplex.Plus (Modules KX))
  (absoluteTerms : ∀ n : ℕ, absolute.obj.X (n : ℤ) ≅
    (restrict KX OX (ax ≫ η)).obj (tensor OX M (exterior OX ΩA n)))
  (relativeTerms : ∀ n : ℕ, F.total.obj.X (n : ℤ) ≅
    (restrict SX OX η).obj (tensor OX M (exterior OX ΩR n)))
  (β : (pullback G SY SX s).obj ΩY ⟶ (restrict SX OX η).obj ΩA)
  (ρ : ΩA ⟶ ΩR)

local instance (V : Dᵒᵖ) : CommRing ((moduleRing OX).obj.obj V) :=
  inferInstanceAs (CommRing (OX.obj.obj V))

/-- Original base and relative cotangent maps, fixed by ALL native adjunction units and exact forms. -/
def IsCotangentSource
    (dY : ∀ U : Cᵒᵖ, SY.obj.obj U →+ ΩY.val.obj U)
    (dA : ∀ V : Dᵒᵖ, OX.obj.obj V →+ ΩA.val.obj V)
    (dR : ∀ V : Dᵒᵖ, OX.obj.obj V →+ ΩR.val.obj V) : Prop :=
  (∀ (U : Cᵒᵖ) (a : SY.obj.obj U),
    (β.val.app (G.op.obj U)).hom
      ((((adjunction G SY SX s).unit.app ΩY).val.app U).hom (dY U a)) =
      dA (G.op.obj U) ((η.hom.app (G.op.obj U)).hom ((s.hom.app U).hom a))) ∧
    (∀ (V : Dᵒᵖ) (a : OX.obj.obj V), (ρ.val.app V).hom (dA V a) = dR V a)

def absoluteUnit (n : ℕ) (V : Dᵒᵖ) (m : M.val.obj V)
    (w : ⋀[OX.obj.obj V]^n (ΩA.val.obj V)) : (absolute.obj.X (n : ℤ)).val.obj V :=
  ((absoluteTerms n).inv.val.app V).hom
    (show ((restrict KX OX (ax ≫ η)).obj (tensor OX M (exterior OX ΩA n))).val.obj V from
      generator OX M (exterior OX ΩA n) V m (exteriorUnit OX ΩA n V w))

def relativeUnit (n : ℕ) (V : Dᵒᵖ) (m : M.val.obj V)
    (w : ⋀[OX.obj.obj V]^n (ΩA.val.obj V)) : (F.total.obj.X (n : ℤ)).val.obj V :=
  ((relativeTerms n).inv.val.app V).hom
    (show ((restrict SX OX η).obj (tensor OX M (exterior OX ΩR n))).val.obj V from
      generator OX M (exterior OX ΩR n) V m
        (exteriorUnit OX ΩR n V (_root_.exteriorPower.map n (ρ.val.app V).hom w)))

/-- A source construction of the actual two-base-form wedge, fixed on all native units. -/
structure BaseTwoWedgeSource where
  map : ∀ n : ℕ,
    tensor SX ((restrict SX OX η).obj (tensor OX M (exterior OX ΩA n)))
      (exterior SX ((pullback G SY SX s).obj ΩY) 2) ⟶
        (restrict SX OX η).obj (tensor OX M (exterior OX ΩA (n + 2)))
  source : ∀ (n : ℕ) (V : Dᵒᵖ) (m : M.val.obj V)
    (w : ⋀[OX.obj.obj V]^n (ΩA.val.obj V))
    (b c : ((pullback G SY SX s).obj ΩY).val.obj V),
    ((map n).val.app V).hom
      (generator SX ((restrict SX OX η).obj (tensor OX M (exterior OX ΩA n)))
        (exterior SX ((pullback G SY SX s).obj ΩY) 2) V
          (show ((restrict SX OX η).obj (tensor OX M (exterior OX ΩA n))).val.obj V from
            generator OX M (exterior OX ΩA n) V m (exteriorUnit OX ΩA n V w))
          (exteriorUnit SX ((pullback G SY SX s).obj ΩY) 2 V
            (_root_.exteriorPower.ιMulti (SX.obj.obj V) 2 (fun i : Fin 2 => if i = 0 then b else c)))) =
      (show ((restrict SX OX η).obj (tensor OX M (exterior OX ΩA (n + 2)))).val.obj V from
        generator OX M (exterior OX ΩA (n + 2)) V m
          (exteriorUnit OX ΩA (n + 2) V
            (MathlibExt.DeRhamSource.Crystalline.leftWedge (n + 1)
              (show ΩA.val.obj V from (β.val.app V).hom b)
                (MathlibExt.DeRhamSource.Crystalline.leftWedge n
                  (show ΩA.val.obj V from (β.val.app V).hom c) w))))

variable (W : BaseTwoWedgeSource G SY SX OX η s ΩY M ΩA β)
  (B : CofactorSource G SY KX SX ax s ΩY F)

/-- This qualification fixes the entire native cochain extension before any higher output. -/
structure Qualification where
  absolute_source : B.absolute = absolute
  baseTwoTerms : ∀ n : ℕ, B.baseTwo.obj.X ((n + 2 : ℕ) : ℤ) ≅
    (restrict KX SX ax).obj (image (W.map n))
  baseTwo_zero : ∀ i : ℤ, i < 2 → IsZero (B.baseTwo.obj.X i)
  wedge_source : ∀ (n : ℕ) (V : Dᵒᵖ) (x : (B.baseTwo.obj.X ((n + 2 : ℕ) : ℤ)).val.obj V),
    (((absoluteTerms (n + 2)).hom.val.app V).hom)
      (((((eqToHom absolute_source).hom.f ((n + 2 : ℕ) : ℤ))).val.app V).hom
        (((B.wedge.hom.f ((n + 2 : ℕ) : ℤ)).val.app V).hom x)) =
      ((image.ι (W.map n)).val.app V).hom (((baseTwoTerms n).hom.val.app V).hom x)
  projection_source : ∀ (n : ℕ) (V : Dᵒᵖ) (m : M.val.obj V)
    (w : ⋀[OX.obj.obj V]^n (ΩA.val.obj V)),
    ((B.projection.hom.f (n : ℤ)).val.app V).hom
      (((cokernel.π B.wedge).hom.f (n : ℤ)).val.app V
        (((((eqToHom absolute_source.symm).hom.f (n : ℤ))).val.app V).hom
          (absoluteUnit KX SX OX ax η M ΩA absolute absoluteTerms n V m w))) =
      (show ((relativeK KX SX ax F).obj.X (n : ℤ)).val.obj V from
        relativeUnit SX OX η F M ΩA ΩR relativeTerms ρ n V m w)
  inclusion_source : ∀ (n : ℕ) (V : Dᵒᵖ) (m : M.val.obj V)
    (w : ⋀[OX.obj.obj V]^n (ΩA.val.obj V))
    (b : ((pullback G SY SX s).obj ΩY).val.obj V),
    ((B.inclusion.hom.f ((n + 1 : ℕ) : ℤ)).val.app V).hom
      (kernelUnit G SY KX SX ax s ΩY F (n : ℤ) V
        (relativeUnit SX OX η F M ΩA ΩR relativeTerms ρ n V m w) b) =
      (((cokernel.π B.wedge).hom.f ((n + 1 : ℕ) : ℤ)).val.app V).hom
        (((((eqToHom absolute_source.symm).hom.f ((n + 1 : ℕ) : ℤ))).val.app V).hom
          (absoluteUnit KX SX OX ax η M ΩA absolute absoluteTerms (n + 1) V m
            (MathlibExt.DeRhamSource.Crystalline.leftWedge n
              (show ΩA.val.obj V from (β.val.app V).hom b) w)))

end MathlibExt.CategoryTheory.GaussManinCofactorNormalization

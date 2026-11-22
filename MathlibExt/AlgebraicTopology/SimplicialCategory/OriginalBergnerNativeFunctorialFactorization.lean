/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerNativeFactorization

/-!
# Full functoriality of the same original Bergner native factorization

The entire native intermediate functor and both original natural
factor maps are retained. Every arrow square has its same original
intermediate enriched map, full naturality triangles and exact object
and Hom factorization formulas.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily.NativeFactorization

/-- The entire SAME native original combined-generator functorial factorization has the proved original model classes.
-/
def functorialData : MorphismProperty.FunctorialFactorizationData
    (Bergner.cofibrations.{u} ⊓ EnrichedDwyerKan.weakEquivalences) Bergner.localFibrations where
  Z := (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).Z
  i := (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).i
  p := (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).p
  fac := (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).fac
  hi f := left_cofibration_weak f.hom
  hp f := right_localFibration f.hom

/-- Read the same whole original intermediate enriched functor, including every original arrow map. -/
theorem functorialData_Z_original : functorialData.{u}.Z =
    (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).Z := rfl

/-- Read the same whole original native inclusion natural transformation. -/
theorem functorialData_i_original : functorialData.{u}.i =
    (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).i := rfl

/-- Read the same whole original native projection natural transformation. -/
theorem functorialData_p_original : functorialData.{u}.p =
    (SmallObject.functorialFactorizationData generatingTrivialCofibrations Cardinal.aleph0).p := rfl

/-- Every original whole arrow square acts by the same complete native intermediate map. -/
def map {C D C' D' : Carrier.{u}} {f : C ⟶ D} {g : C' ⟶ D'}
    (φ : Arrow.mk f ⟶ Arrow.mk g) : (data f).Z ⟶ (data g).Z := functorialData.Z.map φ

/-- Read the original complete native intermediate map literally. -/
theorem map_original {C D C' D' : Carrier.{u}} {f : C ⟶ D} {g : C' ⟶ D'}
    (φ : Arrow.mk f ⟶ Arrow.mk g) :
    map φ = SmallObject.objMap generatingTrivialCofibrations Cardinal.aleph0 φ := rfl

/-- The same original intermediate map retains the whole native inclusion naturality square. -/
theorem i_map {C D C' D' : Carrier.{u}} {f : C ⟶ D} {g : C' ⟶ D'}
    (φ : Arrow.mk f ⟶ Arrow.mk g) :
    (data f).i ≫ map φ = φ.left ≫ (data g).i := (functorialData.i.naturality φ).symm

/-- The same original intermediate map retains the whole native projection naturality square. -/
theorem map_p {C D C' D' : Carrier.{u}} {f : C ⟶ D} {g : C' ⟶ D'}
    (φ : Arrow.mk f ⟶ Arrow.mk g) :
    map φ ≫ (data g).p = (data f).p ≫ φ.right := functorialData.p.naturality φ

/-- The actual intermediate-map identity is the same original enriched identity. -/
theorem map_id {C D : Carrier.{u}} (f : C ⟶ D) :
    map (𝟙 (Arrow.mk f)) = 𝟙 (data f).Z := functorialData.Z.map_id _

/-- The actual intermediate maps compose as the same whole original native functor. -/
theorem map_comp {C D E C' D' E' : Carrier.{u}}
    {f : C ⟶ C'} {g : D ⟶ D'} {h : E ⟶ E'}
    (φ : Arrow.mk f ⟶ Arrow.mk g) (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    map (φ ≫ ψ) = map φ ≫ map ψ := functorialData.Z.map_comp φ ψ

/-- Every original object has the same full original native factorization equation. -/
theorem object_fac {C D : Carrier.{u}} (f : C ⟶ D) (x : C) :
    (data f).p.obj ((data f).i.obj x) = f.obj x :=
  congrArg (fun G : C ⟶ D => G.obj x) (fac f)

/-- Every entire original Hom map has the same exact native factorization through its true original endpoints. -/
theorem hom_fac {C D : Carrier.{u}} (f : C ⟶ D) (x y : C) :
    ((data f).i.map x y ≫ (data f).p.map ((data f).i.obj x) ((data f).i.obj y)) ≫
      eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) (object_fac f x) (object_fac f y)) =
        f.map x y :=
  EnrichedFunctor.homMap_transport_of_eq (fac f) x y

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily.NativeFactorization

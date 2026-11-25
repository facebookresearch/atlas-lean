/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Selected units and source mates for parametrized adjunctions

A comparison of a right adjoint with the identity determines the left-unit
comparison by adjoint uniqueness. The source maps, both Hom functions and
all input and target parameters retain this selected comparison. The parameter
category is independent of the component categories. Only the unit statements
require the component adjunctions to be endoadjunctions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace CategoryTheory.FunctionUnitAdjunction

universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- The left unit is determined by the given entire right-unit comparison. -/
def leftUnitIso {F G : C ⥤ C} (adj : F ⊣ G) (unitIso : G ≅ 𝟭 C) : F ≅ 𝟭 C :=
  Adjunction.leftAdjointUniq (adj.ofNatIsoRight unitIso) (Adjunction.id (C := C))

/-- The inverse function unit is the adjunct of that same selected left unit. -/
theorem unitInverse_adjoint {F G : C ⥤ C} (adj : F ⊣ G) (unitIso : G ≅ 𝟭 C) (X : C) :
    (adj.homEquiv X X) ((leftUnitIso adj unitIso).hom.app X) = unitIso.inv.app X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight unitIso) (Adjunction.id (C := C)) X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  change (adj.homEquiv X X) ((leftUnitIso adj unitIso).hom.app X) ≫
    unitIso.hom.app X = 𝟙 X at h
  apply (cancel_mono (unitIso.hom.app X)).mp
  exact h.trans (unitIso.inv_hom_id_app X).symm

/-- The inverse adjunction retains the same given unit and selected left map. -/
theorem unitInverse_uncurried {F G : C ⥤ C} (adj : F ⊣ G) (unitIso : G ≅ 𝟭 C) (X : C) :
    (adj.homEquiv X X).symm (unitIso.inv.app X) = (leftUnitIso adj unitIso).hom.app X := by
  rw [← unitInverse_adjoint adj unitIso X]
  exact (adj.homEquiv X X).symm_apply_apply _

/-- A whole original left-unit constructor equality retains its exact given inverse adjunct. -/
theorem unitIso_adjoint_of_hom_eq {F G : C ⥤ C} (adj : F ⊣ G)
    (unitIso : G ≅ 𝟭 C) (leftIso : F ≅ 𝟭 C)
    (h : leftIso.hom = (leftUnitIso adj unitIso).hom) (X : C) :
    (adj.homEquiv X X) (leftIso.hom.app X) = unitIso.inv.app X := by
  have h₀ := NatTrans.congr_app h X
  exact (congrArg (fun f => (adj.homEquiv X X) f) h₀).trans
    (unitInverse_adjoint adj unitIso X)

universe uP vP uD vD

section ParametrizedSource

variable {P : Type uP} [Category.{vP} P] {D : Type uD} [Category.{vD} D]
  {L : P ⥤ (C ⥤ D)} {R : Pᵒᵖ ⥤ (D ⥤ C)} (adj : L ⊣₂ R)

/-- Full original component and endpoint equalities preserve the same source-adjoint formula. -/
theorem sourcePre_adjoint_of_whole_eq
    {S T : P} (f : S ⟶ T)
    (FS FT : C ⥤ D) (GS GT : D ⥤ C)
    (hFS : L.obj S = FS) (hFT : L.obj T = FT)
    (hGS : R.obj (.op S) = GS) (hGT : R.obj (.op T) = GT)
    (adjS : FS ⊣ GS) (adjT : FT ⊣ GT)
    (hAdjS : HEq (adj.adj S) adjS) (hAdjT : HEq (adj.adj T) adjT)
    (sourceMap : FS ⟶ FT) (preMap : GT ⟶ GS)
    (hMap : HEq (L.map f) sourceMap) (hPre : HEq (R.map f.op) preMap)
    {X : C} {Y : D} (g : FT.obj X ⟶ Y) :
    (adjS.homEquiv X Y) (sourceMap.app X ≫ g) =
      (adjT.homEquiv X Y) g ≫ preMap.app Y := by
  cases hFS
  cases hFT
  cases hGS
  cases hGT
  cases (eq_of_heq hAdjS)
  cases (eq_of_heq hAdjT)
  cases (eq_of_heq hMap)
  cases (eq_of_heq hPre)
  exact adj.homEquiv_naturality_one f g

end ParametrizedSource

section ParametrizedUnits

variable {P : Type uP} [Category.{vP} P]
  {L : P ⥤ (C ⥤ C)} {R : Pᵒᵖ ⥤ (C ⥤ C)} (adj : L ⊣₂ R)

/-- Every original source map keeps the full selected unit-adjunct equation. -/
theorem sourcePre_unit_adjoint {S T : P} (f : S ⟶ T)
    (unitIso : R.obj (.op T) ≅ 𝟭 C) (X : C) :
    ((adj.adj S).homEquiv X X)
      ((L.map f).app X ≫ (leftUnitIso (adj.adj T) unitIso).hom.app X) =
      unitIso.inv.app X ≫ (R.map f.op).app X := by
  have h := adj.homEquiv_naturality_one f
    ((leftUnitIso (adj.adj T) unitIso).hom.app X)
  exact h.trans (congrArg (fun k => k ≫ (R.map f.op).app X)
    (unitInverse_adjoint (adj.adj T) unitIso X))

/-- The inverse source equation uses both original maps of the same adjunction. -/
theorem sourcePre_unit_uncurried {S T : P} (f : S ⟶ T)
    (unitIso : R.obj (.op T) ≅ 𝟭 C) (X : C) :
    ((adj.adj S).homEquiv X X).symm (unitIso.inv.app X ≫ (R.map f.op).app X) =
      (L.map f).app X ≫ (leftUnitIso (adj.adj T) unitIso).hom.app X := by
  apply ((adj.adj S).homEquiv X X).injective
  exact (((adj.adj S).homEquiv X X).apply_symm_apply _).trans
    (sourcePre_unit_adjoint adj f unitIso X).symm

/-- Whole original source, adjunction, selected unit and coaugmentation equalities
are identified before any component of the source mate is taken. -/
theorem sourcePre_unit_adjoint_of_whole_eq
    {S T : P} (f : S ⟶ T)
    (FS FT GS GT : C ⥤ C)
    (hFS : L.obj S = FS) (hFT : L.obj T = FT)
    (hGS : R.obj (.op S) = GS) (hGT : R.obj (.op T) = GT)
    (adjS : FS ⊣ GS) (adjT : FT ⊣ GT)
    (hAdjS : HEq (adj.adj S) adjS) (hAdjT : HEq (adj.adj T) adjT)
    (leftIso : FT ≅ 𝟭 C) (unitIso : GT ≅ 𝟭 C)
    (hLeft : leftIso = leftUnitIso adjT unitIso)
    (sourceMap : FS ⟶ FT) (preMap : GT ⟶ GS)
    (hMap : HEq (L.map f) sourceMap) (hPre : HEq (R.map f.op) preMap)
    (η : 𝟭 C ⟶ GS) (hη : η = unitIso.inv ≫ preMap) (X : C) :
    (adjS.homEquiv X X) (sourceMap.app X ≫ leftIso.hom.app X) = η.app X := by
  cases hFS
  cases hFT
  cases hGS
  cases hGT
  cases (eq_of_heq hAdjS)
  cases (eq_of_heq hAdjT)
  cases (eq_of_heq hMap)
  cases (eq_of_heq hPre)
  cases hLeft
  cases hη
  exact sourcePre_unit_adjoint adj f unitIso X

/-- The inverse mate is obtained only after the same complete original data are identified. -/
theorem sourcePre_unit_uncurried_of_whole_eq
    {S T : P} (f : S ⟶ T)
    (FS FT GS GT : C ⥤ C)
    (hFS : L.obj S = FS) (hFT : L.obj T = FT)
    (hGS : R.obj (.op S) = GS) (hGT : R.obj (.op T) = GT)
    (adjS : FS ⊣ GS) (adjT : FT ⊣ GT)
    (hAdjS : HEq (adj.adj S) adjS) (hAdjT : HEq (adj.adj T) adjT)
    (leftIso : FT ≅ 𝟭 C) (unitIso : GT ≅ 𝟭 C)
    (hLeft : leftIso = leftUnitIso adjT unitIso)
    (sourceMap : FS ⟶ FT) (preMap : GT ⟶ GS)
    (hMap : HEq (L.map f) sourceMap) (hPre : HEq (R.map f.op) preMap)
    (η : 𝟭 C ⟶ GS) (hη : η = unitIso.inv ≫ preMap) (X : C) :
    (adjS.homEquiv X X).symm (η.app X) = sourceMap.app X ≫ leftIso.hom.app X := by
  cases hFS
  cases hFT
  cases hGS
  cases hGT
  cases (eq_of_heq hAdjS)
  cases (eq_of_heq hAdjT)
  cases (eq_of_heq hMap)
  cases (eq_of_heq hPre)
  cases hLeft
  cases hη
  exact sourcePre_unit_uncurried adj f unitIso X

end ParametrizedUnits

/-- A whole source adjunct mate retains every target parameter through the same adjunction. -/
theorem sourceAdjunct_target_of_mate {F G : C ⥤ C} (a : F ⊣ G)
    (s : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ G)
    (h : ∀ X : C, (a.homEquiv X X) (s.app X) = η.app X)
    {P X : C} (f : P ⟶ X) :
    (a.homEquiv P X) (s.app P ≫ f) = η.app P ≫ G.map f :=
  (a.homEquiv_naturality_right (s.app P) f).trans
    (congrArg (fun k => k ≫ G.map f) (h P))

/-- The same original whole adjunct mate retains every left input parameter. -/
theorem sourceAdjunct_input_of_mate {F G : C ⥤ C} (a : F ⊣ G)
    (s : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ G)
    (h : ∀ X : C, (a.homEquiv X X) (s.app X) = η.app X)
    {P X : C} (f : P ⟶ X) :
    (a.homEquiv P X) (F.map f ≫ s.app X) = f ≫ η.app X :=
  (a.homEquiv_naturality_left f (s.app X)).trans
    (congrArg (fun k => f ≫ k) (h X))

end CategoryTheory.FunctionUnitAdjunction

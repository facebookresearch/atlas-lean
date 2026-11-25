/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY additive normalization and the original prism homotopy; Native has not been run.
module

public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy

/-!
# The canonical additive normalization isomorphism preserves the actual prism homotopy

The native negative alternating sum commutes with the additive functor.
The existing Moore inclusion and projection comparisons then transport the
actual normalized homotopy components. The original simplicial homotopy
is fixed data; no homotopy compatibility law is supplied by the caller.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped Simplicial

universe uC vC uD vD

namespace AlgebraicTopology.NormalizedQuotient

attribute [local implicit_reducible] normalizedMooreComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The same native normalization projection commutes with additive transport. -/
@[reassoc]
theorem mooreCompMapIso_projection (X : SimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (PInftyToNormalizedMooreComplex X) ≫
        (((mooreCompMapIso F).app X)).hom =
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        PInftyToNormalizedMooreComplex (X ⋙ F) := by
  have hIncl := mooreCompMapIso_hom_inclusion F X
  change ((mooreCompMapIso F).app X).hom ≫ inclusionOfMooreComplexMap (X ⋙ F) =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X at hIncl
  apply (cancel_mono (inclusionOfMooreComplexMap (X ⋙ F))).1
  rw [Category.assoc, hIncl,
    ← Category.assoc, ← (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp,
    PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (PInfty (X := X)) ≫
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom =
    (((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫ PInftyToNormalizedMooreComplex (X ⋙ F)) ≫
      inclusionOfMooreComplexMap (X ⋙ F)
  rw [Category.assoc, PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  exact map_PInfty F X

/-- Native negative alternating-sum components commute with the same additive functor. -/
theorem alternatingTransport_homotopy
    {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : SimplicialObject.Homotopy f g) (n m : ℕ) :
    F.map (H.toChainHomotopy.hom n m) ≫ ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y).hom.f m =
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom.f n ≫
        (H.whiskerRight F).toChainHomotopy.hom n m := by
  change F.map (SimplicialObject.Homotopy.ToChainHomotopy.hom H n m) ≫ 𝟙 _ =
    𝟙 _ ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom (H.whiskerRight F) n m
  rw [Category.comp_id, Category.id_comp]
  by_cases hn : n + 1 = m
  · subst m
    rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp only [Functor.map_neg, Functor.map_sum, Functor.map_zsmul]
    rfl
  · rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hn,
      SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hn, Functor.map_zero]

/-- The original normalized prism homotopy is transported through the canonical
normalization isomorphisms, including every nonzero shifted component. -/
@[reassoc]
theorem mooreCompMapIso_homotopy
    {X Y : SimplicialObject C} {f g : X ⟶ Y} (H : SimplicialObject.Homotopy f g) (n m : ℕ) :
    F.map (H.toNormalizedChainHomotopy.hom n m) ≫ (((mooreCompMapIso F).app Y)).hom.f m =
      (((mooreCompMapIso F).app X)).hom.f n ≫
        (H.whiskerRight F).toNormalizedChainHomotopy.hom n m := by
  let ix := (inclusionOfMooreComplexMap X).f n
  let ix' := (inclusionOfMooreComplexMap (X ⋙ F)).f n
  let py := (PInftyToNormalizedMooreComplex Y).f m
  let py' := (PInftyToNormalizedMooreComplex (Y ⋙ F)).f m
  let ex := (((mooreCompMapIso F).app X)).hom.f n
  let ey := (((mooreCompMapIso F).app Y)).hom.f m
  let tx := ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom.f n
  let ty := ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y).hom.f m
  let hC := H.toChainHomotopy.hom n m
  let hD := (H.whiskerRight F).toChainHomotopy.hom n m
  have hi : ex ≫ ix' = F.map ix ≫ tx := by
    have h := congrArg (fun z => z.f n) (mooreCompMapIso_hom_inclusion F X)
    change ex ≫ ix' = F.map ix ≫ tx at h
    exact h
  have hp : F.map py ≫ ey = ty ≫ py' := by
    have h := congrArg (fun z => z.f m) (mooreCompMapIso_projection F Y)
    change F.map py ≫ ey = ty ≫ py' at h
    exact h
  have hh : F.map hC ≫ ty = tx ≫ hD := alternatingTransport_homotopy F H n m
  let zC := (ix ≫ hC) ≫ py
  let zD := (ix' ≫ hD) ≫ py'
  change F.map ((0 : _) + (zC + 0)) ≫ ey = ex ≫ ((0 : _) + (zD + 0))
  simp only [zero_add, add_zero]
  change F.map ((ix ≫ hC) ≫ py) ≫ ey = ex ≫ ((ix' ≫ hD) ≫ py')
  simp only [F.map_comp, Category.assoc]
  calc
    F.map ix ≫ F.map hC ≫ (F.map py ≫ ey) = F.map ix ≫ F.map hC ≫ (ty ≫ py') :=
      congrArg (fun z => F.map ix ≫ F.map hC ≫ z) hp
    _ = F.map ix ≫ (F.map hC ≫ ty) ≫ py' := by simp only [Category.assoc]
    _ = F.map ix ≫ (tx ≫ hD) ≫ py' := congrArg (fun z => F.map ix ≫ z ≫ py') hh
    _ = (F.map ix ≫ tx) ≫ hD ≫ py' := by simp only [Category.assoc]
    _ = (ex ≫ ix') ≫ hD ≫ py' := congrArg (fun z => z ≫ hD ≫ py') hi.symm
    _ = ex ≫ ix' ≫ hD ≫ py' := by simp only [Category.assoc]

end AlgebraicTopology.NormalizedQuotient

end

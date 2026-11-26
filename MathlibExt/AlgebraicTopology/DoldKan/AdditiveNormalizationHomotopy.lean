/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Normalization of simplicial homotopies commutes with additive functors.
module

public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy

/-!
# Additive transport of normalized simplicial homotopies

Let F : C ⥤ D be an additive functor between abelian categories, whose object and morphism
universes are independent. Write A(X) for the alternating face-map complex, N(X) for the
normalized Moore complex, i_X : N(X) → A(X) for its inclusion and p_X : A(X) → N(X) for the
normalization projection. The comparison isomorphisms e_X : F(N(X)) ≅ N(X ⋙ F) and t_X :
F(A(X)) ≅ A(X ⋙ F) commute with i_X and p_X.

A simplicial homotopy H from f to g induces alternating components h_{n,n+1} = −Σᵢ₌₀ⁿ (−1)ⁱHᵢ
and h_{n,m} = 0 for m ≠ n+1. Its normalized components are i_X,n ≫ h_{n,m} ≫ p_Y,m. Additivity
transports the signed sums, and the inclusion and projection comparisons identify these
components with the normalized homotopy of H whiskered by F.

The sign convention is that of Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy.
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

/-- Normalization projection under additive functors.

Let F : C ⥤ D be additive between abelian categories and X a simplicial object of C. For the
canonical Moore comparison e_X and alternating comparison t_X, the projections satisfy F(p_X)
≫ e_X.hom = t_X.hom ≫ p_{X⋙F}. Here F acts on chain complexes degreewise and p is the
normalization projection. -/
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

/-- Additive transport of alternating homotopy components.

Let H be a simplicial homotopy from f to g in an abelian category C and F : C ⥤ D an additive
functor to an abelian category. If t_X and t_Y are the alternating-complex comparison
isomorphisms, then F(h_H(n,m)) ≫ t_Y,m = t_X,n ≫ h_{H⋙F}(n,m) for every n,m : ℕ. The shifted
component h_H(n,n+1) is −Σᵢ₌₀ⁿ (−1)ⁱHᵢ; all other components are zero. -/
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

/-- Additive transport of normalized homotopy components.

For an additive functor F between abelian categories and a simplicial homotopy H from f to g,
the canonical Moore comparisons e_X and e_Y satisfy F(h_Hᴺ(n,m)) ≫ e_Y,m = e_X,n ≫
h_{H⋙F}ᴺ(n,m) for all natural degrees n,m. The normalized component h_Hᴺ is the composite of
the Moore inclusion, the signed alternating homotopy component and the normalization
projection. -/
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

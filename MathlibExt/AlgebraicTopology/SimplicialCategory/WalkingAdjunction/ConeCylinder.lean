/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinderSimplex
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The natural original cylinder-to-join-cone map

The native colimit of standard simplices and its preservation by the
Cartesian tensor construct `X ⊗ Δ[1] → X ⋆ Δ[0]` for every original
simplicial set. The whole simplex maps commute with every original
operator. Their two endpoints give the entire original join base and
apex, and the construction is natural in whole simplicial maps.
No Kan, quasicategory or semantic-presentation assumption is needed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeCylinder

/-- The original simplex cylinder in native join-cone coordinates. -/
def simplexCone (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n] ⋆ Δ[0] :=
  simplexCollapse n ≫ (joinStdSimplexIso n 0).inv

/-- The whole simplex-cone maps commute with every actual original scalar operator. -/
theorem simplexCone_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u})) ≫ simplexCone n =
      simplexCone m ≫ (join.map (SSet.stdSimplex.map θ)).app Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso n 0).hom).mp
  simp only [simplexCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinStdSimplexIso_natural_left, Iso.inv_hom_id_assoc]
  exact simplexCollapse_naturality θ

/-- The zero cylinder endpoint retains the entire original join base. -/
theorem simplexCone_zero (n : ℕ) : (SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ≫ simplexCone n =
    joinInl Δ[n] Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso n 0).hom).mp
  simp only [simplexCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinInl_comp_joinStdSimplexIso_hom, inl'_eq_δ_last]
  exact simplexCollapse_zero n

/-- The one cylinder endpoint retains the entire constant original apex map. -/
theorem simplexCone_one (n : ℕ) : (SSet.ι₁ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ≫ simplexCone n =
    SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫ joinInr Δ[n] Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso n 0).hom).mp
  simp only [simplexCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinInr_comp_joinStdSimplexIso_hom]
  exact simplexCollapse_one n

/-- The actual compatible simplex cylinders over the native category of original simplices. -/
def cylinderCocone (X : SSet.{u}) :
    Cocone ((CostructuredArrow.proj SSet.stdSimplex X ⋙ SSet.stdSimplex) ⋙ tensorRight (Δ[1] : SSet.{u})) where
  pt := X ⋆ Δ[0]
  ι := {
    app i := simplexCone i.left.len ≫ (join.map i.hom).app Δ[0]
    naturality i j f := by
      change (SSet.stdSimplex.map f.left ▷ (Δ[1] : SSet.{u})) ≫
        (simplexCone j.left.len ≫ (join.map j.hom).app Δ[0]) =
          simplexCone i.left.len ≫ (join.map i.hom).app Δ[0]
      rw [← Category.assoc, simplexCone_naturality, Category.assoc]
      have hm : (join.map (SSet.stdSimplex.map f.left)).app (Δ[0] : SSet.{u}) ≫
          (join.map j.hom).app Δ[0] = (join.map i.hom).app Δ[0] := by
        rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, f.w]
      exact congrArg (fun h => simplexCone i.left.len ≫ h) hm }

/-- The existing native simplex colimit remains a colimit after the actual Cartesian cylinder tensor. -/
def cylinderIsColimit (X : SSet.{u}) :
    IsColimit ((tensorRight (Δ[1] : SSet.{u})).mapCocone (Presheaf.tautologicalCocone'.{u} X)) := by
  let _ : PreservesColimitsOfShape (CostructuredArrow SSet.stdSimplex X) (tensorRight (Δ[1] : SSet.{u})) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight (Δ[1] : SSet.{u}))).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact isColimitOfPreserves (tensorRight (Δ[1] : SSet.{u})) (Presheaf.isColimitTautologicalCocone'.{u} X)

/-- The whole natural map from the original Cartesian cylinder to its original join cone. -/
def coneCylinder (X : SSet.{u}) : X ⊗ (Δ[1] : SSet.{u}) ⟶ X ⋆ Δ[0] :=
  (cylinderIsColimit X).desc (cylinderCocone X)

/-- Every original representable simplex retains its identical entire cylinder-to-cone map. -/
theorem coneCylinder_simplex {X : SSet.{u}} {n : ℕ} (s : (Δ[n] : SSet.{u}) ⟶ X) :
    (s ▷ (Δ[1] : SSet.{u})) ≫ coneCylinder X = simplexCone n ≫ (join.map s).app Δ[0] :=
  (cylinderIsColimit X).fac (cylinderCocone X) (CostructuredArrow.mk s)

/-- The construction retains the entire original map in both its cylinder and join presentations. -/
theorem coneCylinder_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (f ▷ (Δ[1] : SSet.{u})) ≫ coneCylinder Y = coneCylinder X ≫ (join.map f).app Δ[0] := by
  apply (cylinderIsColimit X).hom_ext
  intro i
  let s : (Δ[i.left.len] : SSet.{u}) ⟶ X := i.hom
  change (i.hom ▷ (Δ[1] : SSet.{u})) ≫ ((f ▷ Δ[1]) ≫ coneCylinder Y) =
    (i.hom ▷ Δ[1]) ≫ (coneCylinder X ≫ (join.map f).app Δ[0])
  have hl : (s ▷ (Δ[1] : SSet.{u})) ≫ ((f ▷ Δ[1]) ≫ coneCylinder Y) =
      simplexCone i.left.len ≫ (join.map (s ≫ f)).app Δ[0] :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ coneCylinder Y) (comp_whiskerRight s f Δ[1]).symm).trans
        (coneCylinder_simplex (s ≫ f)))
  have hr : (s ▷ (Δ[1] : SSet.{u})) ≫ (coneCylinder X ≫ (join.map f).app Δ[0]) =
      (simplexCone i.left.len ≫ (join.map s).app Δ[0]) ≫ (join.map f).app Δ[0] :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ (join.map f).app Δ[0]) (coneCylinder_simplex s))
  have hj : simplexCone i.left.len ≫ (join.map (s ≫ f)).app (Δ[0] : SSet.{u}) =
      (simplexCone i.left.len ≫ (join.map s).app Δ[0]) ≫ (join.map f).app Δ[0] := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  exact hl.trans (hj.trans hr.symm)

/-- The whole zero cylinder endpoint is the identical original join inclusion. -/
theorem coneCylinder_zero (X : SSet.{u}) : (SSet.ι₀ : X ⟶ X ⊗ Δ[1]) ≫ coneCylinder X = joinInl X Δ[0] := by
  apply (Presheaf.isColimitTautologicalCocone'.{u} X).hom_ext
  intro i
  let s : (Δ[i.left.len] : SSet.{u}) ⟶ X := i.hom
  change s ≫ (SSet.ι₀ ≫ coneCylinder X) = s ≫ joinInl X Δ[0]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ coneCylinder X) (SSet.ι₀_comp s).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => SSet.ι₀ ≫ h) (coneCylinder_simplex s)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun h => h ≫ (join.map s).app Δ[0]) (simplexCone_zero i.left.len)).trans
              (map_comp_joinInl s Δ[0]).symm)))))

/-- The whole one cylinder endpoint is the constant map at the identical original join apex. -/
theorem coneCylinder_one (X : SSet.{u}) : (SSet.ι₁ : X ⟶ X ⊗ Δ[1]) ≫ coneCylinder X =
    SSet.stdSimplex.isTerminalObj₀.from X ≫ joinInr X Δ[0] := by
  apply (Presheaf.isColimitTautologicalCocone'.{u} X).hom_ext
  intro i
  let s : (Δ[i.left.len] : SSet.{u}) ⟶ X := i.hom
  change s ≫ (SSet.ι₁ ≫ coneCylinder X) =
    s ≫ (SSet.stdSimplex.isTerminalObj₀.from X ≫ joinInr X Δ[0])
  have ht : SSet.stdSimplex.isTerminalObj₀.from (Δ[i.left.len] : SSet.{u}) =
      s ≫ SSet.stdSimplex.isTerminalObj₀.from X := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ coneCylinder X) (SSet.ι₁_comp s).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => SSet.ι₁ ≫ h) (coneCylinder_simplex s)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun h => h ≫ (join.map s).app Δ[0]) (simplexCone_one i.left.len)).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun h => SSet.stdSimplex.isTerminalObj₀.from Δ[i.left.len] ≫ h)
                  (joinInr_comp_map s Δ[0])).trans
                    ((congrArg (fun h => h ≫ joinInr X (Δ[0] : SSet.{u})) ht).trans
                      (Category.assoc _ _ _)))))))))

end SSet.WalkingAdjunction.ConeCylinder

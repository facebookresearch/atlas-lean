/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatCone
public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinderDeformation

/-!
# Whole standard-simplex fat-cone deformation

The actual ordinal retraction unit stays in the original final row.
It therefore descends through the native fat-cone pushout, fixing the
entire apex path. The resulting whole deformation runs from the
identity to the original join comparison followed by its specified
standard-simplex section. The section followed by comparison is the
identical whole join map.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

open ConeCylinder

/-- The complete original zero row is fixed throughout the entire ordinal deformation. -/
theorem deformation_zero_row (n : ℕ) :
    ((SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫ deformationMap n =
      CartesianMonoidalCategory.fst (Δ[n] : SSet.{u}) Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext m
  rcases m with ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro i
    exact deformationMap_fst_of_zero n m
      (((SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]).app _ s.1), s.2) i rfl
  · apply SSet.stdSimplex.ext
    intro i
    exact deformationMap_snd n m
      (((SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]).app _ s.1), s.2) i

/-- The original final row stays in that identical row throughout the entire ordinal deformation. -/
theorem deformation_top_row (n : ℕ) :
    (one (Δ[n] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ deformationMap n =
      ((one (Δ[n] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ deformationMap n ≫
        CartesianMonoidalCategory.fst Δ[n] Δ[1]) ≫ one Δ[n] := by
  apply NatTrans.ext
  funext m
  rcases m with ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro i
    exact deformationMap_snd n m ((one (Δ[n] : SSet.{u})).app _ s.1, s.2) i

/-- Collapsing the actual final row makes its entire deformed cylinder constant at the original apex. -/
theorem deformation_top_cylinder (n : ℕ) :
    (one (Δ[n] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ deformationMap n ≫ cylinder Δ[n] =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[n] ⊗ (Δ[1] : SSet.{u})) ≫ apex Δ[n] := by
  rw [← Category.assoc, deformation_top_row, Category.assoc, one_cylinder, ← Category.assoc]
  exact congrArg (fun p => p ≫ apex (Δ[n] : SSet.{u}))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The actual standard-simplex section, with source the whole original join cone. -/
def joinSection (n : ℕ) : (Δ[n] : SSet.{u}) ⋆ Δ[0] ⟶ obj Δ[n] :=
  (joinStdSimplexIso n 0).hom ≫ ConeCylinder.simplexSection n ≫ cylinder Δ[n]

/-- The section followed by the original comparison is the identical whole join cone map. -/
theorem joinSection_toJoin (n : ℕ) : joinSection.{u} n ≫ toJoin Δ[n] = 𝟙 (Δ[n] ⋆ (Δ[0] : SSet.{u})) := by
  rw [joinSection, Category.assoc, Category.assoc, cylinder_toJoin,
    coneCylinder_stdSimplex, simplexCone, ← Category.assoc (ConeCylinder.simplexSection n),
    simplexSection_collapse, Category.id_comp, Iso.hom_inv_id]

/-- The actual whole endomorphism obtained by original comparison and its specified simplex section. -/
def retraction (n : ℕ) : obj (Δ[n] : SSet.{u}) ⟶ obj Δ[n] := toJoin Δ[n] ≫ joinSection n

/-- The original cylinder of the retraction is the actual section after collapse. -/
theorem cylinder_retraction (n : ℕ) : cylinder (Δ[n] : SSet.{u}) ≫ retraction n =
    simplexCollapse n ≫ ConeCylinder.simplexSection n ≫ cylinder Δ[n] := by
  rw [retraction, ← Category.assoc, cylinder_toJoin, joinSection, coneCylinder_stdSimplex,
    simplexCone, Category.assoc, Iso.inv_hom_id_assoc]

/-- The actual internal path of the original ordinal unit after the final row is collapsed. -/
def cylinderPath (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ pathSpace (obj Δ[n]) :=
  MonoidalClosed.curry ((β_ (Δ[1] : SSet.{u}) (Δ[n] ⊗ Δ[1])).hom ≫
    deformationMap n ≫ cylinder Δ[n])

/-- Initial evaluation is the whole original fat-cone cylinder. -/
theorem cylinderPath_zero (n : ℕ) : cylinderPath.{u} n ≫ eval₀ = cylinder Δ[n] := by
  rw [comp_eval₀_eq_ι₀_braiding_uncurry, cylinderPath, MonoidalClosed.uncurry_curry,
    SymmetricCategory.symmetry_assoc, ← Category.assoc, deformationMap_zero, Category.id_comp]

/-- Final evaluation is the whole original cylinder followed by the retraction. -/
theorem cylinderPath_one (n : ℕ) : cylinderPath.{u} n ≫ eval₁ = cylinder Δ[n] ≫ retraction n := by
  rw [comp_eval₁_eq_ι₁_braiding_uncurry, cylinderPath, MonoidalClosed.uncurry_curry,
    SymmetricCategory.symmetry_assoc, ← Category.assoc, deformationMap_one, cylinder_retraction]
  exact Category.assoc _ _ _

/-- The complete final-row path is the identical original constant apex path. -/
theorem cylinderPath_top (n : ℕ) : one (Δ[n] : SSet.{u}) ≫ cylinderPath n =
    SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫ apex Δ[n] ≫ constPath (obj Δ[n]) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, cylinderPath, MonoidalClosed.uncurry_curry,
    BraidedCategory.braiding_naturality_right_assoc, deformation_top_cylinder]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left, uncurry_constPath]
  rw [CartesianMonoidalCategory.whiskerLeft_snd]
  simpa only [Category.assoc] using congrArg (fun p => p ≫ apex (Δ[n] : SSet.{u}))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext
      ((β_ (Δ[1] : SSet.{u}) Δ[n]).hom ≫
        SSet.stdSimplex.isTerminalObj₀.from (Δ[n] ⊗ (Δ[1] : SSet.{u})))
      ((Δ[1] : SSet.{u}) ◁ SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫
        CartesianMonoidalCategory.snd Δ[1] Δ[0]))

/-- The entire original base path is fixed throughout the actual cylinder deformation. -/
theorem cylinderPath_base (n : ℕ) : (SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ≫ cylinderPath n =
    base Δ[n] ≫ constPath (obj Δ[n]) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, cylinderPath, MonoidalClosed.uncurry_curry,
    BraidedCategory.braiding_naturality_right_assoc]
  rw [← Category.assoc ((SSet.ι₀ : (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1]) ▷ Δ[1]),
    deformation_zero_row, Category.assoc]
  rw [MonoidalClosed.uncurry_natural_left, uncurry_constPath]
  rw [CartesianMonoidalCategory.whiskerLeft_snd]
  rw [← Category.assoc, CartesianMonoidalCategory.braiding_hom_fst, base]

/-- The actual whole fat-cone path descended from the original ordinal unit. -/
def wholePath (n : ℕ) : obj (Δ[n] : SSet.{u}) ⟶ pathSpace (obj Δ[n]) :=
  desc (cylinderPath n) (apex Δ[n] ≫ constPath (obj Δ[n])) (cylinderPath_top n)

/-- The whole descended path retains its original complete cylinder. -/
theorem cylinder_wholePath (n : ℕ) : cylinder (Δ[n] : SSet.{u}) ≫ wholePath n = cylinderPath n :=
  cylinder_desc _ _ _

/-- The entire original apex path is fixed by the whole descended path. -/
theorem apex_wholePath (n : ℕ) : apex (Δ[n] : SSet.{u}) ≫ wholePath n =
    apex Δ[n] ≫ constPath (obj Δ[n]) := apex_desc _ _ _

/-- The complete original base path is fixed by the whole descended fat-cone path. -/
theorem base_wholePath (n : ℕ) : base (Δ[n] : SSet.{u}) ≫ wholePath n =
    base Δ[n] ≫ constPath (obj Δ[n]) := by
  rw [base, Category.assoc, cylinder_wholePath, cylinderPath_base, base]

/-- Initial evaluation of the descended path is the identical original fat-cone map. -/
theorem wholePath_zero (n : ℕ) : wholePath.{u} n ≫ eval₀ = 𝟙 (obj Δ[n]) := by
  apply hom_ext
  · rw [← Category.assoc, cylinder_wholePath, cylinderPath_zero, Category.comp_id]
  · rw [← Category.assoc, apex_wholePath, Category.assoc, eval₀_constPath, Category.comp_id]

/-- The original apex remains fixed by the retraction. -/
theorem apex_retraction (n : ℕ) : apex (Δ[n] : SSet.{u}) ≫ retraction n = apex Δ[n] := by
  let v : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
    SSet.yonedaEquiv.symm (SSet.stdSimplex.const n 0 _)
  have hv : v ≫ SSet.stdSimplex.isTerminalObj₀.from Δ[n] = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h₀ : (one (Δ[n] : SSet.{u}) ≫ cylinder Δ[n]) ≫ retraction n =
      SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫ apex Δ[n] := by
    rw [Category.assoc, ← cylinderPath_one, ← Category.assoc, cylinderPath_top]
    simp only [Category.assoc, eval₁_constPath, Category.comp_id]
  have h : SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫ apex Δ[n] ≫ retraction n =
      SSet.stdSimplex.isTerminalObj₀.from Δ[n] ≫ apex Δ[n] := by
    simpa only [one_cylinder, Category.assoc] using h₀
  have he := congrArg (fun p => v ≫ p) h
  simpa only [← Category.assoc, hv, Category.id_comp] using he

/-- Final evaluation of the descended path is the actual original comparison followed by section. -/
theorem wholePath_one (n : ℕ) : wholePath.{u} n ≫ eval₁ = retraction n := by
  apply hom_ext
  · rw [← Category.assoc, cylinder_wholePath, cylinderPath_one]
  · rw [← Category.assoc, apex_wholePath, Category.assoc, eval₁_constPath, Category.comp_id, apex_retraction]

/-- The complete actual standard-simplex fat-cone homotopy, with its original maps as endpoints. -/
def wholeDeformation (n : ℕ) : Homotopy (𝟙 (obj (Δ[n] : SSet.{u}))) (retraction n) :=
  Homotopy.mkOfH ((β_ (obj Δ[n]) (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry (wholePath n))
    ((comp_eval₀_eq_ι₀_braiding_uncurry _).symm.trans (wholePath_zero n))
    ((comp_eval₁_eq_ι₁_braiding_uncurry _).symm.trans (wholePath_one n))

end SSet.WalkingAdjunction.FatCone

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamiliesNativeCocartesianSectionQuasicategory
public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-!
# Tests for the native cocartesian section quasicategory

The identity fibration is cocartesian, with every edge cocartesian.
Sections of the identity over the nerve of `Fin 2` form a quasicategory
by the main theorem, with an explicit section vertex and an explicit
inner horn that has a filler.
-/

namespace MathlibExtTest.AlgebraicGeometry.DerivedQCohModuleFamiliesNativeCocartesianSectionQuasicategory

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open scoped Simplicial

universe u

/-- The identity is an inner fibration. -/
private theorem innerFibration_id (B : SSet.{u}) : SSet.InnerFibration (𝟙 B) :=
  ⟨MorphismProperty.rlp_of_isIso SSet.innerHornInclusions (𝟙 B)⟩

/-- Every edge is cocartesian for the identity fibration. -/
private theorem isCocartesianEdge_id (B : SSet.{u}) (e : B _⦋1⦌) :
    IsCocartesianEdge (𝟙 B) e := by
  intro n a b j h1 h2 h3
  refine ⟨b, by simpa using h3.symm, Category.comp_id _⟩

/-- The identity is a cocartesian fibration. -/
private theorem cocartesianFibration_id (B : SSet.{u}) :
    CocartesianFibration (𝟙 B) where
  inner := innerFibration_id B
  lift := fun b _ hx ↦ ⟨b, hx.symm, rfl, isCocartesianEdge_id B b⟩

/-- Sections of the identity over the nerve of `Fin 2` form a quasicategory. -/
example : SSet.Quasicategory
    (sectionsOver (𝟙 (nerve (Fin 2))) (𝟙 (nerve (Fin 2)))) :=
  native_cocartesian_section_quasicategory _ _ _ _ _ (cocartesianFibration_id _)

/-- The canonical section vertex over `q` for the identity fibration. -/
private def sectionVertex (B : SSet.{u}) (q : B ⟶ B) :
    (sectionsOver (𝟙 B) q) _⦋0⦌ :=
  ⟨(Functor.HomObj.ofNatTrans q : (mapping B B).obj (op ⦋0⦌)),
    (fun _ _ _ ↦ rfl), (fun j e ↦ isCocartesianEdge_id B
      (((Functor.HomObj.ofNatTrans q : (mapping B B).obj (op ⦋0⦌)).app
        (op ⦋1⦌) (vertexParameter (op ⦋0⦌) j)) e))⟩

/-- A constant inner horn into identity sections. -/
private def sectionHorn (B : SSet.{u}) :
    (Λ[2, 1] : SSet.{u}) ⟶ sectionsOver (𝟙 B) (𝟙 B) where
  app m := ↾fun _ : (Λ[2, 1] : SSet.{u}).obj m ↦
    (⟨(Functor.HomObj.ofNatTrans (𝟙 B) : (mapping B B).obj m),
      (fun _ _ _ ↦ rfl), (fun j e ↦ isCocartesianEdge_id B
        (((Functor.HomObj.ofNatTrans (𝟙 B) : (mapping B B).obj m).app
          (op ⦋1⦌) (vertexParameter m j)) e))⟩ :
      (sectionsOver (𝟙 B) (𝟙 B)).obj m)
  naturality m m' g := by
    ext w
    apply Subtype.ext
    rfl

/-- The inner horn into identity sections over the nerve of `Fin 2` has a filler. -/
example : ∃ σ : Δ[2] ⟶ sectionsOver (𝟙 (nerve (Fin 2))) (𝟙 (nerve (Fin 2))),
    sectionHorn (nerve (Fin 2)) = Λ[2, 1].ι ≫ σ := by
  have hQC : SSet.Quasicategory
      (sectionsOver (𝟙 (nerve (Fin 2))) (𝟙 (nerve (Fin 2)))) :=
    native_cocartesian_section_quasicategory _ _ _ _ _ (cocartesianFibration_id _)
  exact SSet.Quasicategory.hornFilling (by decide) (by decide) (sectionHorn _)

end MathlibExtTest.AlgebraicGeometry.DerivedQCohModuleFamiliesNativeCocartesianSectionQuasicategory

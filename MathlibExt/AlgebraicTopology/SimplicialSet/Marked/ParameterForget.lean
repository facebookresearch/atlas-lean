/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit

/-!
# Forgetting maximal parameter marking on the original mapping complex

The map forgets only the extra parameter-edge condition, retaining the
whole original prism. It is degreewise injective and is onto in degree
zero, since every edge of the original zero parameter is degenerate.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Forget maximal parameter marking through the original identity parameter map. -/
def mappingComplexMaxToMin (X Y : Marked.{u}) :
    mappingComplex .maximal X Y ⟶ mappingComplex .minimal X Y where
  app n := ↾fun f => prodMap (toMax (X := min (SSet.stdSimplex.obj n.unop))
    (𝟙 (SSet.stdSimplex.obj n.unop))) (𝟙 X) ≫ f
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Hom.ext
    ext n a
    rfl

/-- The entire underlying prism is the same original simplicial map after forgetting. -/
theorem mappingComplexMaxToMin_app_hom (X Y : Marked.{u}) (n : SimplexCategoryᵒᵖ)
    (f : (mappingComplex .maximal X Y).obj n) :
    ((mappingComplexMaxToMin X Y).app n f).hom = f.hom := by
  ext m a
  rfl

/-- Forgetting the parameter marking does not identify different whole marked prisms. -/
theorem mappingComplexMaxToMin_app_injective (X Y : Marked.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((mappingComplexMaxToMin X Y).app n) := by
  intro f g h
  apply Hom.ext
  have hh := congrArg Hom.hom h
  rw [mappingComplexMaxToMin_app_hom, mappingComplexMaxToMin_app_hom] at hh
  exact hh

/-- The same zero-prism also preserves maximal parameter marking. -/
def mappingZeroPromote (X Y : Marked.{u}) (f : (mappingComplex .minimal X Y) _⦋0⦌) :
    (mappingComplex .maximal X Y) _⦋0⦌ where
  hom := f.hom
  preserve {e} he := by
    apply f.preserve
    refine ⟨?_, he.2⟩
    change e.1 ∈ Set.range ((Δ[0] : SSet.{u}).σ (0 : Fin 1))
    refine ⟨SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})), ?_⟩
    apply (SSet.yonedaEquiv (X := (Δ[0] : SSet.{u})) (n := ⦋1⦌)).symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Promotion at zero and forgetting retain the same original marked map. -/
theorem mappingComplexMaxToMin_zero_promote (X Y : Marked.{u})
    (f : (mappingComplex .minimal X Y) _⦋0⦌) :
    (mappingComplexMaxToMin X Y).app (op ⦋0⦌) (mappingZeroPromote X Y f) = f := by
  apply Hom.ext
  rw [mappingComplexMaxToMin_app_hom]
  rfl

/-- Original postcomposition commutes with forgetting only the extra parameter marking. -/
theorem mappingComplexMaxToMin_post (X : Marked.{u}) {Y Z : Marked.{u}} (p : Y ⟶ Z) :
    mappingComplexMaxToMin X Y ≫ mappingComplexPost .minimal X p =
      mappingComplexPost .maximal X p ≫ mappingComplexMaxToMin X Z := by
  ext n f
  apply Hom.ext
  ext m a
  rfl

/-- Original precomposition likewise retains both the source map and parameter-forgetful map. -/
theorem mappingComplexMaxToMin_pre {X X' : Marked.{u}} (p : X' ⟶ X) (Y : Marked.{u}) :
    mappingComplexMaxToMin X Y ≫ mappingComplexPre .minimal p Y =
      mappingComplexPre .maximal p Y ≫ mappingComplexMaxToMin X' Y := by
  ext n f
  apply Hom.ext
  ext m a
  rfl

end SSet.Marked

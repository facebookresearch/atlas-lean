/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingComplex

/-!
# Actual zero-simplex evaluation of marked mapping complexes

Both original standard-zero parameter markings are terminal in the marked
category. The original product projection and its original simultaneous lift
form the unit isomorphism. Zero-simplex evaluation therefore identifies the
mapping complex with the actual marked Hom set, retaining both coordinate
maps and pre/postcomposition.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Marked

private def zeroVertex : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0

/-- The original unique parameter-zero map preserves its actual minimal or maximal marking. -/
def toParameterZero (k : ParameterMarking) (X : Marked.{u}) :
    X ⟶ (simplexParameter k).obj ⦋0⦌ := by
  cases k
  · refine { hom := SSet.stdSimplex.isTerminalObj₀.from X.toSSet, preserve := ?_ }
    intro a _
    change _ ∈ Set.range ((Δ[0] : SSet.{u}).σ (0 : Fin 1))
    refine ⟨zeroVertex, ?_⟩
    apply (SSet.yonedaEquiv (X := (Δ[0] : SSet.{u})) (n := ⦋1⦌)).symm.injective
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · exact toMax (SSet.stdSimplex.isTerminalObj₀.from X.toSSet)

/-- The original parameter-zero object is terminal with either actual marking. -/
def parameterZeroIsTerminal (k : ParameterMarking) : IsTerminal ((simplexParameter k).obj ⦋0⦌) :=
  IsTerminal.ofUniqueHom (toParameterZero k) (fun X f => by
    cases k <;> apply Hom.ext <;> exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The actual zero-parameter product projection and lift form the original marked unit
  isomorphism. -/
def zeroParameterUnitIso (k : ParameterMarking) (X : Marked.{u}) :
    prod ((simplexParameter k).obj ⦋0⦌) X ≅ X where
  hom := prodSnd _ _
  inv := prodLift ((parameterZeroIsTerminal k).from X) (𝟙 X)
  hom_inv_id := by
    apply (prodHomEquiv _ _ _).injective
    apply Prod.ext
    · exact (parameterZeroIsTerminal k).hom_ext _ _
    · apply Hom.ext
      rfl
  inv_hom_id := by
    apply Hom.ext
    rfl

/-- The original zero-simplex evaluation is exactly the actual marked Hom set. -/
def mappingComplexZeroEquiv (k : ParameterMarking) (X Y : Marked.{u}) :
    (mappingComplex k X Y) _⦋0⦌ ≃ (X ⟶ Y) where
  toFun f := (zeroParameterUnitIso k X).inv ≫ f
  invFun f := (zeroParameterUnitIso k X).hom ≫ f
  left_inv f := by
    let f₀ : prod ((simplexParameter k).obj ⦋0⦌) X ⟶ Y := f
    change (zeroParameterUnitIso k X).hom ≫ ((zeroParameterUnitIso k X).inv ≫ f₀) = f₀
    exact (zeroParameterUnitIso k X).hom_inv_id_assoc f₀
  right_inv f := by
    change (zeroParameterUnitIso k X).inv ≫ ((zeroParameterUnitIso k X).hom ≫ f) = f
    exact (zeroParameterUnitIso k X).inv_hom_id_assoc f

/-- The original unit inverse is natural in the same source map and parameter coordinate. -/
theorem zeroParameterUnitIso_inv_natural (k : ParameterMarking) {X Y : Marked.{u}} (f : X ⟶ Y) :
    f ≫ (zeroParameterUnitIso k Y).inv =
      (zeroParameterUnitIso k X).inv ≫ prodMap (𝟙 ((simplexParameter k).obj ⦋0⦌)) f := by
  apply (prodHomEquiv _ _ _).injective
  apply Prod.ext
  · exact (parameterZeroIsTerminal k).hom_ext _ _
  · apply Hom.ext
    rfl

/-- Zero evaluation commutes with the same actual target composition. -/
theorem mappingComplexZeroEquiv_post (k : ParameterMarking) (X : Marked.{u})
    {Y Z : Marked.{u}} (f : Y ⟶ Z) (a : (mappingComplex k X Y) _⦋0⦌) :
    mappingComplexZeroEquiv k X Z ((mappingComplexPost k X f).app _ a) =
      mappingComplexZeroEquiv k X Y a ≫ f := by
  let a₀ : prod ((simplexParameter k).obj ⦋0⦌) X ⟶ Y := a
  change (zeroParameterUnitIso k X).inv ≫ (a₀ ≫ f) =
    ((zeroParameterUnitIso k X).inv ≫ a₀) ≫ f
  exact (Category.assoc _ _ _).symm

/-- Zero evaluation commutes with the original marked source map. -/
theorem mappingComplexZeroEquiv_pre (k : ParameterMarking) {X X' : Marked.{u}}
    (f : X' ⟶ X) (Y : Marked.{u}) (a : (mappingComplex k X Y) _⦋0⦌) :
    mappingComplexZeroEquiv k X' Y ((mappingComplexPre k f Y).app _ a) =
      f ≫ mappingComplexZeroEquiv k X Y a := by
  let a₀ : prod ((simplexParameter k).obj ⦋0⦌) X ⟶ Y := a
  change (zeroParameterUnitIso k X').inv ≫
    (prodMap (𝟙 ((simplexParameter k).obj ⦋0⦌)) f ≫ a₀) =
      f ≫ ((zeroParameterUnitIso k X).inv ≫ a₀)
  simpa only [Category.assoc] using congrArg (fun m => m ≫ a₀)
    (zeroParameterUnitIso_inv_natural k f).symm

end SSet.Marked

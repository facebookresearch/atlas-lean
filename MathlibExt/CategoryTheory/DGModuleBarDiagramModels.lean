/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModuleDiagramModels
public import MathlibExt.Algebra.Homology.DGCyclicMixedModels
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Actual category-bar cells of a projective DG-module diagram replacement

The bar summands are indexed by actual composable chains followed by a
map to the diagram target. Every cell is fixed on the literal coefficient
inclusion. Its differential is the alternating category-face formula,
and its augmentation and terminal reindexing are fixed.

An edge homotopy is the degree -1 edge cell composed with the single
joint comparison. Higher chains have their own native cells and face
equations. No independent homotopy callback is substituted for this
whole-diagram construction.

References: Hovey, Model Categories, §5; Bousfield--Kan, XII;
Brav--Dyckerhoff, arXiv:1606.00619v1, diagrams6.5--6.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModuleBarDiagramModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleDiagramModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k] {C : DGCat k}
variable {J : Type u} [Category.{u} J]

/-- An actual category-bar path includes its terminal map to the target index. -/
structure BarChain (J : Type u) [Category.{u} J] (n : ℕ) (j : J) where
  sequence : ComposableArrows J n
  terminal : sequence.obj (Fin.last n) ⟶ j

/-- Reindexing only postcomposes the same literal terminal arrow. -/
def BarChain.postcompose {n : ℕ} {j j' : J} (c : BarChain J n j) (a : j ⟶ j') : BarChain J n j' :=
  ⟨c.sequence, c.terminal ≫ a⟩

/-- The actual injective simplex face functor on the object-chain index. -/
def faceIndex {n : ℕ} (i : Fin (n + 2)) : Fin (n + 1) ⥤ Fin (n + 2) :=
  (Fin.succAboveOrderEmb i).toOrderHom.toFunctor

/-- A category-bar face removes one vertex and keeps the actual terminal composite. -/
def BarChain.face {n : ℕ} {j : J} (c : BarChain J (n + 1) j) (i : Fin (n + 2)) : BarChain J n j :=
  ⟨faceIndex i ⋙ c.sequence,
    c.sequence.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n)))) ≫ c.terminal⟩

/-- The actual first-object map used by the initial category face. -/
def BarChain.firstMap {n : ℕ} {j : J} (c : BarChain J (n + 1) j) (i : Fin (n + 2)) :
    c.sequence.obj 0 ⟶ (c.face i).sequence.obj 0 :=
  c.sequence.map (homOfLE (Fin.zero_le (i.succAbove 0)))

/-- The source diagram's actual bar coefficient module in every total degree. -/
abbrev BarValues (D : J ⥤ RightModule k C) (j : J) (x : Cᵒᵖ) (r : ℤ) :=
  DirectSum ℕ (fun n => DirectSum (BarChain J n j)
    (fun c => ↥(((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x).X (r + (n : ℤ)))))

/-- Native inclusion of one actual category path coefficient into its total bar degree. -/
def includeBar (D : J ⥤ RightModule k C) (j : J) (x : Cᵒᵖ) (r : ℤ)
    (n : ℕ) (c : BarChain J n j) :
      ((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x).X (r + (n : ℤ)) →ₗ[k] BarValues D j x r := by
  classical
  exact
  (DirectSum.lof k ℕ (fun n => DirectSum (BarChain J n j)
    (fun c => ↥(((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x).X (r + (n : ℤ))))) n).comp
    (DirectSum.lof k (BarChain J n j)
      (fun c => ↥(((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x).X (r + (n : ℤ)))) c)

/-- The face cochain is computed from the same source diagram arrow and lower actual bar cell. -/
def faceCell (D : J ⥤ RightModule k C) (Q : J ⥤ RightModule k C)
    (cell : ∀ (n : ℕ) (j : J) (c : BarChain J n j), DGHom k (-(n : ℤ)) (D.obj (c.sequence.obj 0)) (Q.obj j))
    (n : ℕ) (j : J) (c : BarChain J (n + 1) j) (i : Fin (n + 2)) :
    DGHom k (-(n : ℤ)) (D.obj (c.sequence.obj 0)) (Q.obj j) :=
  dgComp k (moduleCycle (D.map (c.firstMap i))) (cell n j (c.face i)) (by omega)

/-- A whole projective replacement is the actual category bar on every chain and coefficient. -/
structure BarProjectiveDiagramReplacement (D : J ⥤ RightModule k C) where
  replacement : ProjectiveDiagramReplacement D
  termIso : ∀ (j : J) (x : Cᵒᵖ) (r : ℤ),
    ((replacement.diagram.obj j).toEnrichedFunctor.obj x).X r ≅ ModuleCat.of k (BarValues D j x r)
  cell : ∀ (n : ℕ) (j : J) (c : BarChain J n j),
    DGHom k (-(n : ℤ)) (D.obj (c.sequence.obj 0)) (replacement.diagram.obj j)
  cell_eq : ∀ (n : ℕ) (j : J) (c : BarChain J n j) (x : Cᵒᵖ) (r : ℤ)
    (z : ((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x).X r),
    (termIso j x (r - (n : ℤ))).hom
      ((DGFunctor.dgApp k (-(n : ℤ)) x (cell n j c) : Cochain _ _ (-(n : ℤ))).v
        r (r - (n : ℤ)) (by omega) z) =
      includeBar D j x (r - (n : ℤ)) n c
        (degreeCast ((D.obj (c.sequence.obj 0)).toEnrichedFunctor.obj x) (by omega) z)
  cell_closed_zero : ∀ (j : J) (c : BarChain J 0 j), dgDifferential k 0 (cell 0 j c) = 0
  cell_boundary : ∀ (n : ℕ) (j : J) (c : BarChain J (n + 1) j),
    dgDifferential k (-((n + 1 : ℕ) : ℤ)) (cell (n + 1) j c) =
      degreeCast (dgHomComplex k (D.obj (c.sequence.obj 0)) (replacement.diagram.obj j)) (by omega)
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • faceCell D replacement.diagram cell n j c i)
  augmentation_zero : ∀ (j : J) (c : BarChain J 0 j),
    dgComp k (cell 0 j c) (moduleCycle (replacement.augmentation.app j)) rfl = moduleCycle (D.map c.terminal)
  augmentation_positive : ∀ (n : ℕ) (j : J) (c : BarChain J (n + 1) j),
    dgComp k (cell (n + 1) j c) (moduleCycle (replacement.augmentation.app j))
      (show -((n + 1 : ℕ) : ℤ) + 0 = -((n + 1 : ℕ) : ℤ) by omega) = 0
  cell_naturality : ∀ (n : ℕ) (j j' : J) (a : j ⟶ j') (c : BarChain J n j),
    dgComp k (cell n j c) (moduleCycle (replacement.diagram.map a)) (by omega) = cell n j' (c.postcompose a)

/-- The actual degree-zero identity bar cell supplies the component section. -/
def barSection {D : J ⥤ RightModule k C} (R : BarProjectiveDiagramReplacement D) (j : J) :
    D.obj j ⟶ R.replacement.diagram.obj j :=
  (DGFunctor.homEquivDGCycles k (D.obj j) (R.replacement.diagram.obj j)).symm
    ⟨R.cell 0 j ⟨ComposableArrows.mk₀ j, 𝟙 j⟩,
      (mem_dgCycles k).mpr (R.cell_closed_zero j ⟨ComposableArrows.mk₀ j, 𝟙 j⟩)⟩

/-- The component on the original diagram is the actual bar section followed by the joint map. -/
def jointComponent {D E : J ⥤ RightModule k C} (R : BarProjectiveDiagramReplacement D)
    {component : ∀ j : J, R.replacement.diagram.obj j ⟶ E.obj j}
    (M : NormalizedDiagramComparison R.replacement component) (j : J) : D.obj j ⟶ E.obj j :=
  barSection R j ≫ M.map.app j

/-- The edge homotopy is the actual degree -1 bar edge cell followed by the one joint comparison. -/
def jointEdgeHomotopy {D E : J ⥤ RightModule k C} (R : BarProjectiveDiagramReplacement D)
    {component : ∀ j : J, R.replacement.diagram.obj j ⟶ E.obj j}
    (M : NormalizedDiagramComparison R.replacement component) {i j : J} (a : i ⟶ j) :
    DGHom k (-1) (D.obj i) (E.obj j) :=
  dgComp k (R.cell 1 j ⟨ComposableArrows.mk₁ a, 𝟙 j⟩) (moduleCycle (M.map.app j)) rfl

/-- Every higher face of the joint comparison comes from the corresponding actual bar-chain cell. -/
def jointChainCell {D E : J ⥤ RightModule k C} (R : BarProjectiveDiagramReplacement D)
    {component : ∀ j : J, R.replacement.diagram.obj j ⟶ E.obj j}
    (M : NormalizedDiagramComparison R.replacement component) (n : ℕ) (j : J) (c : BarChain J n j) :
    DGHom k (-(n : ℤ)) (D.obj (c.sequence.obj 0)) (E.obj j) :=
  dgComp k (R.cell n j c) (moduleCycle (M.map.app j)) (by omega)

end MathlibExt.CategoryTheory.DGModuleBarDiagramModels

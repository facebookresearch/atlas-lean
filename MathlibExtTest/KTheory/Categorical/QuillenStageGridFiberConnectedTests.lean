/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiberConnected

/-!
# Tests for all-degree Quillen Stage-grid fiber connectedness

These tests consume the exact vertex lifts, normalized and raw shell
comparisons, ordered long-shell coherence, all three zero-row naturality
regions, Stage reconstruction, the direct strict-fiber morphism, fixed degrees
zero through two, mixed universes, and the theorem-valued connectedness,
finality, and initiality conclusions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberConnectedTests

open AlgebraicKTheory
open AlgebraicKTheory.QuillenStageGridFiberComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance connectedTestsWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

section ComparisonPipeline

variable {a : SimplexCategory} {q : QuillenQSimplex C a}
variable (X Y : QuillenStageGridFiber q)

example (k : Fin (a.len + 1)) :
    QuillenQ.underlyingIso (vertexIso X Y k) = (extractedIso X Y).app k :=
  vertexIso_underlyingIso X Y k

example {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    QuillenQ.mkHom
          (edgewiseStageShellSpanNormalized X.1.grid.obj k l hkl) ≫
        (QuillenQ.underlyingIso (vertexIso X Y l)).hom =
      (QuillenQ.underlyingIso (vertexIso X Y k)).hom ≫
        QuillenQ.mkHom
          (edgewiseStageShellSpanNormalized Y.1.grid.obj k l hkl) :=
  normalizedShell_naturality X Y hkl

example {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellEndpointIsoComp X.1.grid.obj Y.1.grid.obj hkl hlr
        (shellEndpointIso X Y hkl)
        (shellEndpointIsoRightAligned X Y hkl hlr) =
      shellEndpointIsoLongAligned X Y hkl hlr :=
  shellEndpointIso_comp X Y hkl hlr

example {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseRightIndex_mono hkl)) ≫
        (tailApexIso X Y l).hom =
      (tailApexIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseRightIndex_mono hkl)) :=
  tailApexIso_hom_naturality X Y hkl

example (k : Fin (a.len + 1)) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) ≫
        (tailApexIso X Y k).hom =
      (tailKernelIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) :=
  tailKernelIso_hom_naturality X Y k

example {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_anti hkl)) ≫
        (tailKernelIso X Y k).hom =
      (tailKernelIso X Y l).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_anti hkl)) :=
  tailKernelIso_hom_lower_naturality X Y hkl

example : X.1.grid.obj.zeroRowChain ≅ Y.1.grid.obj.zeroRowChain :=
  zeroRowIso X Y

example : X.1.grid.obj ≅ Y.1.grid.obj :=
  stageIso X Y

example (k : Fin (a.len + 1)) :
    (stageIso X Y).hom.hom.app
        (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
          (edgewiseStageVertex_le a k)) =
      (vertexIso X Y k).hom :=
  stageIso_hom_app_cross X Y k

example :
    (edgewiseStageQuillenSimplexFunctor C a).map (gridIso X Y).hom =
      (extractedIso X Y).hom :=
  gridIso_map X Y

example : X ⟶ Y :=
  fiberHom X Y

end ComparisonPipeline

section PublicResults

variable {a : SimplexCategory} (q : QuillenQSimplex C a)

example : IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

example : (quillenStageGridQProjection C a).Final :=
  quillenStageGridQProjection_final C a

example : (quillenStageGridQProjection C a).Initial :=
  quillenStageGridQProjection_initial C a

end PublicResults

section DegreeZero

variable (q : QuillenQSimplex C ⦋0⦌)

example : IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

example (X Y : QuillenStageGridFiber q) : X ⟶ Y :=
  fiberHom X Y

end DegreeZero

section DegreeOne

variable (q : QuillenQSimplex C ⦋1⦌)

example : IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

example (X Y : QuillenStageGridFiber q) : X ⟶ Y :=
  fiberHom X Y

end DegreeOne

section DegreeTwo

theorem degreeTwo_h01 : (0 : Fin 3) ≤ 1 := by decide
theorem degreeTwo_h12 : (1 : Fin 3) ≤ 2 := by decide

variable (q : QuillenQSimplex C ⦋2⦌)
variable (X Y : QuillenStageGridFiber q)

example : IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

example :
    edgewiseStageShellEndpointIsoComp X.1.grid.obj Y.1.grid.obj
        degreeTwo_h01 degreeTwo_h12
        (shellEndpointIso X Y degreeTwo_h01)
        (shellEndpointIsoRightAligned X Y degreeTwo_h01 degreeTwo_h12) =
      shellEndpointIsoLongAligned X Y degreeTwo_h01 degreeTwo_h12 :=
  shellEndpointIso_comp X Y degreeTwo_h01 degreeTwo_h12

example :
    (shellEndpointIsoLongAligned X Y degreeTwo_h01 degreeTwo_h12).1.hom ≫
        edgewiseStageShellToRight Y.1.grid.obj
          degreeTwo_h01 degreeTwo_h12 =
      edgewiseStageShellToRight X.1.grid.obj
          degreeTwo_h01 degreeTwo_h12 ≫
        (shellEndpointIsoRightAligned X Y
          degreeTwo_h01 degreeTwo_h12).1.hom :=
  shellEndpointIsoLongAligned_hom_right X Y
    degreeTwo_h01 degreeTwo_h12

example : X ⟶ Y :=
  fiberHom X Y

end DegreeTwo

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example (q : QuillenQSimplex C₀ ⦋1⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example (q : QuillenQSimplex C₁ ⦋2⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example (q : QuillenQSimplex C₀₁ ⦋1⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

example (q : QuillenQSimplex C₁₀ ⦋2⦌) :
    IsConnected (QuillenStageGridFiber q) :=
  quillenStageGridFiber_isConnected q

end MixedUniverses

section NegativeClaims

variable {a : SimplexCategory} (q : QuillenQSimplex C a)

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsConnected (QuillenStageGridFiber q)

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Final

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth (quillenStageGridQProjection C a).Initial

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridFiber_contractible

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQProjection_weakEquivalence

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQSComparison

end NegativeClaims

#print axioms AlgebraicKTheory.QuillenStageGridFiberComparison.fiberHom
#print axioms AlgebraicKTheory.quillenStageGridFiber_isConnected
#print axioms AlgebraicKTheory.quillenStageGridQProjection_final
#print axioms AlgebraicKTheory.quillenStageGridQProjection_initial

end MathlibExtTest.KTheory.Categorical.QuillenStageGridFiberConnectedTests

end

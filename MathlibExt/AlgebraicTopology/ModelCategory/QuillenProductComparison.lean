/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantProducts
import MathlibExt.AlgebraicTopology.ModelCategory.CartesianProductWeakEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import MathlibExt.CategoryTheory.AdjunctionProductMate
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Product comparisons of actual Quillen equivalences

The two actual fibrant replacement maps give derived units. Their product
is weak by the fibrant Brown lemma, and its original adjoint mate is the
left product comparison followed by the product of those replacements.
The Cartesian target's tensor Brown theorem then cancels that last map.
No isomorphism or monoidal structure for the left comparison is assumed.
-/

noncomputable section
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Adjunction

section CartesianTarget

variable {D : Type uD} [Category.{vD} D] [ModelCategory D]
  [CartesianMonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]
  [HasBinaryProducts D]

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasBinaryProducts C]
  {L : C ⥤ D} {R : D ⥤ C}

/-- For fibrant cofibrant sources whose product is cofibrant, the actual left
product comparison is weak when the target has the Cartesian pushout-product axiom. -/
theorem prodComparison_weak (adj : L ⊣ R) [adj.IsQuillenEquivalence]
    (hPP : MonoidalPushoutProductAxiom D)
    (X Y : C) [IsFibrant X] [IsFibrant Y]
    [IsCofibrant X] [IsCofibrant Y] [IsCofibrant (X ⨯ Y)] :
    weakEquivalences D (Limits.prodComparison L X Y) := by
  let fx := MorphismProperty.factorizationData (trivialCofibrations D) (fibrations D)
    (terminal.from (L.obj X))
  let fy := MorphismProperty.factorizationData (trivialCofibrations D) (fibrations D)
    (terminal.from (L.obj Y))
  let _ : IsCofibrant (L.obj X) :=
    IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let _ : IsCofibrant (L.obj Y) :=
    IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) inferInstance
  let _ : Cofibration fx.i := (cofibration_iff _).mpr fx.hi.1
  let _ : Cofibration fy.i := (cofibration_iff _).mpr fy.hi.1
  let _ : IsCofibrant fx.Z := isCofibrant_of_cofibration fx.i
  let _ : IsCofibrant fy.Z := isCofibrant_of_cofibration fy.i
  let _ : Fibration fx.p := (fibration_iff _).mpr fx.hp
  let _ : Fibration fy.p := (fibration_iff _).mpr fy.hp
  let _ : IsFibrant fx.Z := (isFibrant_iff_of_isTerminal fx.p terminalIsTerminal).mpr
    inferInstance
  let _ : IsFibrant fy.Z := (isFibrant_iff_of_isTerminal fy.p terminalIsTerminal).mpr
    inferInstance
  let _ : IsFibrant (fx.Z ⨯ fy.Z) := isFibrant_of_fibration
    (prod.fst : fx.Z ⨯ fy.Z ⟶ fx.Z)
  let _ : WeakEquivalence fx.i := (weakEquivalence_iff _).mpr fx.hi.2
  let _ : WeakEquivalence fy.i := (weakEquivalence_iff _).mpr fy.hi.2
  let ux := adj.homEquiv X fx.Z fx.i
  let uy := adj.homEquiv Y fy.Z fy.i
  let _ : WeakEquivalence ux :=
    (IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) fx.i).mp inferInstance
  let _ : WeakEquivalence uy :=
    (IsQuillenEquivalence.weakEquivalence_homEquiv_iff (adj := adj) fy.i).mp inferInstance
  let _ : IsFibrant (R.obj fx.Z) :=
    (IsQuillenAdjunction.preservesFibrantObjects (adj := adj)).isFibrant inferInstance
  let _ : IsFibrant (R.obj fy.Z) :=
    (IsQuillenAdjunction.preservesFibrantObjects (adj := adj)).isFibrant inferInstance
  let _ : ∀ j : WalkingPair, IsFibrant (pairFunction X Y j) := by
    intro j
    cases j <;> dsimp [pairFunction] <;> infer_instance
  let _ : ∀ j : WalkingPair, IsFibrant (pairFunction (R.obj fx.Z) (R.obj fy.Z) j) := by
    intro j
    cases j <;> dsimp [pairFunction] <;> infer_instance
  let uxy : ∀ j : WalkingPair,
      pairFunction X Y j ⟶ pairFunction (R.obj fx.Z) (R.obj fy.Z) j :=
    fun j => match j with
      | .left => ux
      | .right => uy
  let _ : WeakEquivalence (prod.map ux uy) :=
    originalFanMap_weak_of_fibrant
      (X := pairFunction X Y) (Y := pairFunction (R.obj fx.Z) (R.obj fy.Z))
      (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) (prodIsProd X Y)
      (BinaryFan.mk (prod.fst : R.obj fx.Z ⨯ R.obj fy.Z ⟶ R.obj fx.Z) prod.snd)
      (prodIsProd (R.obj fx.Z) (R.obj fy.Z))
      uxy (prod.map ux uy)
      (by
        intro j
        cases j
        · change prod.map ux uy ≫ prod.fst = prod.fst ≫ ux
          exact prod.map_fst ux uy
        · change prod.map ux uy ≫ prod.snd = prod.snd ≫ uy
          exact prod.map_snd ux uy)
      (by
        intro j
        cases j
        · change WeakEquivalence ux
          infer_instance
        · change WeakEquivalence uy
          infer_instance)
  have hm : weakEquivalences C
      (prod.map ux uy ≫ (rightProductIso adj fx.Z fy.Z).inv) :=
    (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences (prod.map ux uy))
      (mem_weakEquivalences _)
  have hc : weakEquivalences D
      (Limits.prodComparison L X Y ≫ prod.map fx.i fy.i) := by
    apply (IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := adj) _).mpr
    rw [homEquiv_product]
    exact hm
  let _ : WeakEquivalence (prod.map fx.i fy.i) := hPP.prodMap_weakEquivalence fx.i fy.i
  exact (weakEquivalences D).of_postcomp _ _ (mem_weakEquivalences _) hc

end CartesianTarget

section Terminal

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- The actual left terminal comparison of a Quillen equivalence is weak
when the original source terminal object is cofibrant. -/
theorem terminalComparison_weak (adj : L ⊣ R) [adj.IsQuillenEquivalence]
    [IsCofibrant (⊤_ C)] : weakEquivalences D (Limits.terminalComparison L) := by
  let _ : R.IsRightAdjoint := adj.isRightAdjoint
  let e := PreservesTerminal.iso R
  let _ : IsFibrant (⊤_ D) :=
    (isFibrant_iff_of_isTerminal (𝟙 (⊤_ D)) terminalIsTerminal).mpr inferInstance
  have he : adj.homEquiv (⊤_ C) (⊤_ D) (Limits.terminalComparison L) = e.inv := by
    apply (cancel_mono e.hom).1
    exact Subsingleton.elim _ _
  apply (IsQuillenEquivalence.homEquiv_weakEquivalence_iff (adj := adj) _).mpr
  rw [he]
  exact mem_weakEquivalences _

end Terminal
end CategoryTheory.Adjunction

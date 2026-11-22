/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentGenerators

/-!
# Actual full original bead maps under arbitrary outer operators

An actual endpoint-preserving simplex operator with its whole input and
coefficient equations gives a genuine original flagged-bead map. No
surjectivity, nondegeneracy or weak-equivalence outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBead

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME entire original bead operator as its genuine native necklace map. -/
def beadOperatorMorphism {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (h₀ : f.toOrderHom 0 = 0) (h₁ : f.toOrderHom (Fin.last n) = Fin.last m) :
    beadData n ⟶ beadData m where
  operator := f
  source := h₀
  target := h₁
  lands := by
    rintro ⟨⟨d⟩⟩ s _hs
    change (SSet.stdSimplex.map f).app (op ⦋d⦌) s ∈ (complex.{0} {0, Fin.last m}).obj (op ⦋d⦌)
    rw [complex_endpoints]
    trivial

/-- The full original input square is precisely the actual original simplex operator equation. -/
theorem beadOperator_over (b c : Bead K x y q) (f : ⦋b.dimension⦌ ⟶ ⦋c.dimension⦌)
    (h₀ : f.toOrderHom 0 = 0) (h₁ : f.toOrderHom (Fin.last b.dimension) = Fin.last c.dimension)
    (hinput : K.map f.op c.simplex = b.simplex) :
    (beadOperatorMorphism f h₀ h₁).map.{u} ≫ (ofBead c).input = (ofBead b).input := by
  change (beadOperatorMorphism f h₀ h₁).map.{u} ≫
    ((complex (beadData c.dimension).joints).ι ≫ SSet.yonedaEquiv.symm c.simplex) =
      (complex (beadData b.dimension).joints).ι ≫ SSet.yonedaEquiv.symm b.simplex
  rw [← Category.assoc, Morphism.map_ι, Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun s => (complex (beadData b.dimension).joints).ι ≫ SSet.yonedaEquiv.symm s) hinput

/-- The SAME actual full original bead map, retaining its complete input and coefficient equations. -/
def beadOperator (b c : Bead K x y q) (f : ⦋b.dimension⦌ ⟶ ⦋c.dimension⦌)
    (h₀ : f.toOrderHom 0 = 0) (h₁ : f.toOrderHom (Fin.last b.dimension) = Fin.last c.dimension)
    (hinput : K.map f.op c.simplex = b.simplex)
    (hflags : (OriginalBead.OuterOperator.map f h₀ h₁).app q b.coefficient = c.coefficient) :
    ofBead b ⟶ ofBead c where
  necklaceMap := beadOperatorMorphism f h₀ h₁
  over := beadOperator_over b c f h₀ h₁ hinput
  flags := hflags

/-- Both SAME whole original beads have the same actual component via the given original outer operator. -/
theorem beadOperator_component (b c : Bead K x y q) (f : ⦋b.dimension⦌ ⟶ ⦋c.dimension⦌)
    (h₀ : f.toOrderHom 0 = 0) (h₁ : f.toOrderHom (Fin.last b.dimension) = Fin.last c.dimension)
    (hinput : K.map f.op c.simplex = b.simplex)
    (hflags : (OriginalBead.OuterOperator.map f h₀ h₁).app q b.coefficient = c.coefficient) :
    ConnectedComponents.mk (ofBead b) = ConnectedComponents.mk (ofBead c) :=
  _root_.Quotient.sound (Zigzag.of_hom (beadOperator b c f h₀ h₁ hinput hflags))

/-- The actual whole original bead map retains its SAME original ordinal on every vertex. -/
theorem beadOperator_operator (b c : Bead K x y q) (f : ⦋b.dimension⦌ ⟶ ⦋c.dimension⦌)
    (h₀ : f.toOrderHom 0 = 0) (h₁ : f.toOrderHom (Fin.last b.dimension) = Fin.last c.dimension)
    (hinput : K.map f.op c.simplex = b.simplex)
    (hflags : (OriginalBead.OuterOperator.map f h₀ h₁).app q b.coefficient = c.coefficient) :
    (beadOperator b c f h₀ h₁ hinput hflags).necklaceMap.operator = f := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

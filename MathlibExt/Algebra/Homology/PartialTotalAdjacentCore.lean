/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalCoreInterval

/-!
# Adjacent page-one intervals of a partial-total filtration

This file packages the two adjacent intervals selected by the increasing
page-one core as one composable diagram.  The diagram is identified with the
corresponding pair of partial-total steps, before any spectral differential
or homology calculation.

No page-two, Tor, abutment, or convergence statement is made.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- The filtration map between the two consecutive upper endpoints selected
by the increasing page-one core. -/
noncomputable def partialTotalE₁CoreSuccessorMap (m q : ℕ) :
    B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m + 1, q)) :=
  B.partialTotalCochainFiltration.map
    (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
      change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
      simp))

/-- The consecutive filtration map in the canonical coordinates of the
`m`th and `(m+1)`st partial-total steps. -/
noncomputable def partialTotalE₁AdjacentCochainMap (m q : ℕ) :
    (B.partialTotalStepCochainShortComplex m).X₂ ⟶
      (B.partialTotalStepCochainShortComplex (m + 1)).X₂ :=
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  (e₀.app 1).inv ≫ B.partialTotalE₁CoreSuccessorMap m q ≫
    (e₁.app 1).hom

/-- The composable pair of adjacent core-interval maps. -/
noncomputable def partialTotalE₁AdjacentCoreDiagram (m q : ℕ) :
    ComposableArrows (CochainComplex C ℤ) 2 :=
  ComposableArrows.mk₂
    (B.partialTotalCochainFiltration.map
      (homOfLE ((core).le₁₂ (m, q))))
    (B.partialTotalE₁CoreSuccessorMap m q)

/-- The same adjacent pair in the canonical step coordinates. -/
noncomputable def partialTotalE₁AdjacentStepDiagram (m q : ℕ) :
    ComposableArrows (CochainComplex C ℤ) 2 :=
  ComposableArrows.mk₂
    (B.partialTotalStepCochainShortComplex m).f
    (B.partialTotalE₁AdjacentCochainMap m q)

/-- Coordinate isomorphism from the adjacent core intervals to the adjacent
partial-total steps. -/
noncomputable def partialTotalE₁AdjacentDiagramIso (m q : ℕ) :
    B.partialTotalE₁AdjacentCoreDiagram m q ≅
      B.partialTotalE₁AdjacentStepDiagram m q := by
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  refine ComposableArrows.isoMk₂
    (e₀.app 0) (e₀.app 1) (e₁.app 1) ?_ ?_
  · exact ComposableArrows.naturality' e₀.hom 0 1
  · dsimp [partialTotalE₁AdjacentCoreDiagram,
      partialTotalE₁AdjacentStepDiagram,
      partialTotalE₁AdjacentCochainMap]
    change
      B.partialTotalE₁CoreSuccessorMap m q ≫ (e₁.app 1).hom =
        (e₀.app 1).hom ≫ (e₀.app 1).inv ≫
          B.partialTotalE₁CoreSuccessorMap m q ≫ (e₁.app 1).hom
    rw [Iso.hom_inv_id_assoc]

end HomologicalComplex₂

end

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
# Adjacent first-page intervals of a partial-total filtration

Let `B` be a first-quadrant bicomplex in an abelian category. Consecutive intervals of the
increasing first-page filtration have upper stages `m` and `m+1`, giving a composable pair of
cochain filtration maps.

The interval-to-step isomorphisms identify this pair with the corresponding partial-total step
map and adjacent upper-stage map. All source, middle, and target coordinates are included in
the diagram isomorphism.
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

/-- The map of consecutive first-page upper filtration stages.

Map the complete cochain filtration upper endpoint selected at `(m,q)` to the upper endpoint
selected at `(m+1,q)`. -/
noncomputable def partialTotalE₁CoreSuccessorMap (m q : ℕ) :
    B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m + 1, q)) :=
  B.partialTotalCochainFiltration.map
    (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
      change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
      simp))

/-- The adjacent upper-stage map in partial-total step coordinates.

Transport the successor filtration map through the middle components of the two interval-to-
step isomorphisms. -/
noncomputable def partialTotalE₁AdjacentCochainMap (m q : ℕ) :
    (B.partialTotalStepCochainShortComplex m).X₂ ⟶
      (B.partialTotalStepCochainShortComplex (m + 1)).X₂ :=
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  (e₀.app 1).inv ≫ B.partialTotalE₁CoreSuccessorMap m q ≫
    (e₁.app 1).hom

/-- The composable diagram of adjacent first-page core intervals.

Use the lower-to-upper map for column `m` followed by the upper-stage successor map. -/
noncomputable def partialTotalE₁AdjacentCoreDiagram (m q : ℕ) :
    ComposableArrows (CochainComplex C ℤ) 2 :=
  ComposableArrows.mk₂
    (B.partialTotalCochainFiltration.map
      (homOfLE ((core).le₁₂ (m, q))))
    (B.partialTotalE₁CoreSuccessorMap m q)

/-- The adjacent filtration diagram in partial-total step coordinates.

Use the step short-complex inclusion followed by the transported adjacent cochain map. -/
noncomputable def partialTotalE₁AdjacentStepDiagram (m q : ℕ) :
    ComposableArrows (CochainComplex C ℤ) 2 :=
  ComposableArrows.mk₂
    (B.partialTotalStepCochainShortComplex m).f
    (B.partialTotalE₁AdjacentCochainMap m q)

/-- The coordinate isomorphism of adjacent core and step diagrams.

The two interval-to-step comparisons identify the adjacent first-page composable diagram with
its partial-total step presentation. -/
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitFromPushoutProduct

/-!
# Comparing an explicit unit witness with the original chosen replacement

An already established, explicitly supplied unit witness compares to any
other actual cofibrant unit replacement through the original lifting
square. Pushout-product Brown invariance verifies the same new map on
both tensor sides. No unit witness or replacement is chosen from
`Nonempty`, and no equality between replacement algorithms is asserted.

This comparison applies when a unit witness is already available. The
construction of a first native ordinary unit witness uses true sphere-unit
cofibrancy in `MonoidalUnitFromPushoutProduct`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

namespace MonoidalUnitAxiomWitness

/-- The actual lifting comparison from the supplied replacement into an
explicit established witness, over the same actual tensor unit. -/
noncomputable def comparison (w : MonoidalUnitAxiomWitness C)
    {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q) : Q ⟶ w.Q := by
  let _ : Cofibration (initial.to Q) := hQ
  let _ : Fibration w.q := ((mem_trivialFibrations_iff (f := w.q)).mp w.q_trivialFibration).1
  let _ : WeakEquivalence w.q :=
    ((mem_trivialFibrations_iff (f := w.q)).mp w.q_trivialFibration).2
  let sq : CommSq (initial.to w.Q) (initial.to Q) w.q q :=
    ⟨initialIsInitial.hom_ext _ _⟩
  exact sq.lift

/-- The chosen comparison retains the original right factor equation. -/
@[reassoc]
theorem comparison_fac (w : MonoidalUnitAxiomWitness C)
    {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q) :
    w.comparison q hQ ≫ w.q = q := by
  let _ : Cofibration (initial.to Q) := hQ
  let _ : Fibration w.q := ((mem_trivialFibrations_iff (f := w.q)).mp w.q_trivialFibration).1
  let _ : WeakEquivalence w.q :=
    ((mem_trivialFibrations_iff (f := w.q)).mp w.q_trivialFibration).2
  let sq : CommSq (initial.to w.Q) (initial.to Q) w.q q :=
    ⟨initialIsInitial.hom_ext _ _⟩
  exact sq.fac_right

/-- Both comparison endpoints are the original cofibrant sources, and
its weakness follows from the same original comparison equation. -/
theorem comparison_weak (w : MonoidalUnitAxiomWitness C)
    {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q)
    (hq : trivialFibrations C q) : weakEquivalences C (w.comparison q hQ) := by
  apply (weakEquivalences C).of_postcomp (w.comparison q hQ) w.q w.q_trivialFibration.2
  rw [w.comparison_fac]
  exact hq.2

/-- The witness's left tensor condition supplies the actual right tensor
condition through the whole braiding Arrow isomorphism. -/
theorem tensorLeft_weak [BraidedCategory C] (w : MonoidalUnitAxiomWitness C)
    (X : C) (hX : IsCofibrant X) : weakEquivalences C (X ◁ w.q) := by
  let e : Arrow.mk (w.q ▷ X) ≅ Arrow.mk (X ◁ w.q) :=
    Arrow.isoMk (β_ w.Q X) (β_ (𝟙_ C) X) (braiding_naturality_left w.q X).symm
  exact ((weakEquivalences C).arrow_mk_iso_iff e).mp (w.tensor_weak X hX)

end MonoidalUnitAxiomWitness

namespace MonoidalPushoutProductAxiom

variable [BraidedCategory C] [MonoidalClosed C]
variable (hPP : MonoidalPushoutProductAxiom C)
include hPP

/-- The original comparison tensor is weak by PP-only Brown invariance
between the two true cofibrant replacement sources. -/
theorem unitWitness_comparison_whiskerRight_weak
    (w : MonoidalUnitAxiomWitness C) {Q : C} (q : Q ⟶ 𝟙_ C)
    (hQ : IsCofibrant Q) (hq : trivialFibrations C q)
    (X : C) (hX : IsCofibrant X) :
    weakEquivalences C (w.comparison q hQ ▷ X) :=
  hPP.whiskerRight_mem_weakEquivalences (w.comparison q hQ) X hX hQ w.Q_cofibrant
    (w.comparison_weak q hQ hq)

/-- The same actual comparison is weak on the other tensor side. -/
theorem unitWitness_comparison_whiskerLeft_weak
    (w : MonoidalUnitAxiomWitness C) {Q : C} (q : Q ⟶ 𝟙_ C)
    (hQ : IsCofibrant Q) (hq : trivialFibrations C q)
    (X : C) (hX : IsCofibrant X) :
    weakEquivalences C (X ◁ w.comparison q hQ) :=
  hPP.whiskerLeft_mem_weakEquivalences X hX (w.comparison q hQ) hQ w.Q_cofibrant
    (w.comparison_weak q hQ hq)

/-- The explicit old witness and actual comparison verify the same given
replacement map on the left tensor side, without unit cofibrancy. -/
theorem unitReplacement_whiskerRight_weak_of_witness
    (w : MonoidalUnitAxiomWitness C) {Q : C} (q : Q ⟶ 𝟙_ C)
    (hQ : IsCofibrant Q) (hq : trivialFibrations C q)
    (X : C) (hX : IsCofibrant X) : weakEquivalences C (q ▷ X) := by
  rw [← w.comparison_fac q hQ, comp_whiskerRight]
  exact (weakEquivalences C).comp_mem _ _
    (hPP.unitWitness_comparison_whiskerRight_weak w q hQ hq X hX) (w.tensor_weak X hX)

/-- The same original map is weak on the right tensor side, with the
braiding counterpart of the explicit old witness. -/
theorem unitReplacement_whiskerLeft_weak_of_witness
    (w : MonoidalUnitAxiomWitness C) {Q : C} (q : Q ⟶ 𝟙_ C)
    (hQ : IsCofibrant Q) (hq : trivialFibrations C q)
    (X : C) (hX : IsCofibrant X) : weakEquivalences C (X ◁ q) := by
  rw [← w.comparison_fac q hQ, whiskerLeft_comp]
  exact (weakEquivalences C).comp_mem _ _
    (hPP.unitWitness_comparison_whiskerLeft_weak w q hQ hq X hX) (w.tensorLeft_weak X hX)

/-- The complete new witness contains exactly the supplied original
replacement and map. Its tensor law follows from the original lifting
comparison and PP Brown invariance. -/
noncomputable def unitAxiomWitnessOfReplacementAndWitness
    (w : MonoidalUnitAxiomWitness C) {Q : C} (q : Q ⟶ 𝟙_ C)
    (hQ : IsCofibrant Q) (hq : trivialFibrations C q) : MonoidalUnitAxiomWitness C where
  Q := Q
  q := q
  Q_cofibrant := hQ
  q_trivialFibration := hq
  tensor_weak X hX := hPP.unitReplacement_whiskerRight_weak_of_witness w q hQ hq X hX

/-- The same caller-supplied initial-unit factor yields the new witness.
The actual established witness is passed explicitly. -/
noncomputable def unitAxiomWitnessOfUnitFactorAndWitness
    (w : MonoidalUnitAxiomWitness C)
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) : MonoidalUnitAxiomWitness C :=
  hPP.unitAxiomWitnessOfReplacementAndWitness w d.p (isCofibrant_unitFactor d) d.hp

@[simp]
theorem unitAxiomWitnessOfUnitFactorAndWitness_Q
    (w : MonoidalUnitAxiomWitness C)
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    (hPP.unitAxiomWitnessOfUnitFactorAndWitness w d).Q = d.Z :=
  rfl

@[simp]
theorem unitAxiomWitnessOfUnitFactorAndWitness_q
    (w : MonoidalUnitAxiomWitness C)
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    (hPP.unitAxiomWitnessOfUnitFactorAndWitness w d).q = d.p :=
  rfl

/-- The new unit witness preserves the original supplied factor equation. -/
theorem unitAxiomWitnessOfUnitFactorAndWitness_fac
    (w : MonoidalUnitAxiomWitness C)
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) :
    d.i ≫ (hPP.unitAxiomWitnessOfUnitFactorAndWitness w d).q = initial.to (𝟙_ C) :=
  d.fac

end MonoidalPushoutProductAxiom

end HomotopicalAlgebra

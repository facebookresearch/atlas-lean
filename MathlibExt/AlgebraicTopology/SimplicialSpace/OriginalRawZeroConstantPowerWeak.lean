/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkRawEClassifyingRows
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Weakness of the original raw constant full-E power

Apply the SAME raw diagonal functor to the original categorical E contraction.
The scalar interval is the whole original raw(E)_0, whose terminal map is
proved weak by the classifying-row construction. No Kan hypothesis on W,
Segal or completeness hypothesis, raw-unit weakness, core weakness, or weak
comparison is an input. Both original E endpoints and the strict section
equation are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalRawZeroConstantPowerWeak
open RezkCompletionRaw WalkingEUnit

/-- The actual original coefficient-power, outer-row evaluation and diagonal,
as a covariant functor of the original target simplicial space. -/
def rawRowFunctor (k : SimplexCategoryᵒᵖ) : SimplicialSpace.{u} ⥤ SSet.{u} :=
  (internalHom (C := SimplicialSpace.{u})).flip ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ SimplicialSpace.{u}ᵒᵖ
      SimplicialSpace.{u}).obj coefficient.op ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SimplicialSpace.{u} SSet.{u}).obj
      (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj k) ⋙
    SSet.simplicialDiagonalFunctor

/-- The functor object is exactly the original raw-completion row. -/
theorem rawRowFunctor_obj (k : SimplexCategoryᵒᵖ) (W : SimplicialSpace.{u}) :
    (rawRowFunctor k).obj W = (rawCompletion W).diagram.obj k := rfl

/-- The functor map is exactly the original whole-power diagonal target map. -/
theorem rawRowFunctor_map (k : SimplexCategoryᵒᵖ)
    {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (rawRowFunctor k).map f = (rawCompletionMap f).hom.app k := rfl

/-- Each native whole-power functor is a right adjoint; pointwise preservation,
row evaluation and the actual diagonal therefore preserve binary products. -/
instance rawRowFunctor_preservesBinaryProducts (k : SimplexCategoryᵒᵖ) :
    PreservesLimitsOfShape (Discrete WalkingPair) (rawRowFunctor.{u} k) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair)
      (internalHom (C := SimplicialSpace.{u})).flip := by
    apply preservesLimitsOfShape_of_evaluation
    intro A
    change PreservesLimitsOfShape (Discrete WalkingPair) (ihom A.unop)
    infer_instance
  unfold rawRowFunctor
  infer_instance

/-- The interval is the SAME full raw(E) outer-zero row, not a vertex set. -/
def originalRawEInterval : SSet.{u} :=
  (rawRowFunctor (op ⦋0⦌)).obj coherentSpace

/-- The whole raw zero row is the original full E, through its single actual coordinate. -/
def originalRawEIntervalIso : originalRawEInterval.{u} ≅ SSet.coherentIso.{u} :=
  RezkRawEClassifyingRows.rawRowIso (op ⦋0⦌) ≪≫
    CategoryTheory.Codiscrete.functorToSSet.mapIso
      (Equiv.toIso (Equiv.funUnique (Fin 1) (ULift.{u} Bool)))

/-- Weakness of the actual interval's terminal map is supplied by the proved classifying row. -/
theorem originalRawEInterval_terminal_weak :
    SSet.realizationWeakEquivalences (terminal.from originalRawEInterval.{u}) :=
  RezkRawEClassifyingRows.rawE_zero_row_weak

/-- Its terminal map is a fibration through the internally constructed whole
classifying-row Iso and the genuine codiscrete nerve Kan structure. -/
theorem originalRawEInterval_terminal_fibration :
    Fibration (terminal.from originalRawEInterval.{u}) := by
  let e := RezkRawEClassifyingRows.rawRowIso.{u} (op ⦋0⦌)
  let _ : SSet.KanComplex (SSet.RezkRawEFiniteRows.rowNerve.{u} 0) :=
    SSet.RezkRawEFiniteRows.rowNerve_kan 0
  have hf : Fibration (e.hom ≫
      terminal.from (SSet.RezkRawEFiniteRows.rowNerve.{u} 0)) := by
    infer_instance
  have heq : e.hom ≫ terminal.from (SSet.RezkRawEFiniteRows.rowNerve.{u} 0) =
      terminal.from originalRawEInterval.{u} := Subsingleton.elim _ _
  rw [heq] at hf
  exact hf

/-- The actual raw(E) interval has a trivial terminal fibration. -/
theorem originalRawEInterval_terminal_trivialFibration :
    trivialFibrations SSet.{u} (terminal.from originalRawEInterval.{u}) :=
  ⟨(HomotopicalAlgebra.fibration_iff _).mp originalRawEInterval_terminal_fibration,
    originalRawEInterval_terminal_weak⟩

/-- Every projection raw(E)_0 × B → B is genuinely weak by pullback stability
of the actual trivial terminal fibration. B need not be Kan. -/
theorem originalRawEInterval_projection_weak (B : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (CartesianMonoidalCategory.snd originalRawEInterval.{u} B) := by
  let _ : Fibration (terminal.from originalRawEInterval.{u}) :=
    originalRawEInterval_terminal_fibration
  let _ : WeakEquivalence (terminal.from originalRawEInterval.{u}) := by
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact RezkRawEClassifyingRows.rawE_zero_row_weak
  have hpb : IsPullback
      (CartesianMonoidalCategory.fst originalRawEInterval.{u} B)
      (CartesianMonoidalCategory.snd originalRawEInterval.{u} B)
      (terminal.from originalRawEInterval.{u}) (terminal.from B) :=
    IsPullback.of_is_product'
      (tensorProductIsBinaryProduct originalRawEInterval.{u} B) terminalIsTerminal
  exact (MorphismProperty.of_isPullback hpb
    (mem_trivialFibrations (terminal.from originalRawEInterval.{u}))).2

/-- Apply the original raw functor to either original whole E endpoint and
retain the native binary-product comparison, with E as the first factor. -/
def rawTensorEndpoint (B : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    (rawRowFunctor (op ⦋0⦌)).obj B ⟶
      originalRawEInterval ⊗ (rawRowFunctor (op ⦋0⦌)).obj B :=
  (rawRowFunctor (op ⦋0⦌)).map (spaceEndpoint B e) ≫
    (prodComparisonIso (rawRowFunctor (op ⦋0⦌)) coherentSpace B).hom

set_option backward.isDefEq.respectTransparency false in
/-- Each actual endpoint remains a strict section of the original projection. -/
theorem rawTensorEndpoint_snd (B : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    rawTensorEndpoint B e ≫
        CartesianMonoidalCategory.snd originalRawEInterval
          ((rawRowFunctor (op ⦋0⦌)).obj B) =
      𝟙 ((rawRowFunctor (op ⦋0⦌)).obj B) := by
  change ((rawRowFunctor (op ⦋0⦌)).map (spaceEndpoint B e) ≫
      (prodComparisonIso (rawRowFunctor (op ⦋0⦌)) coherentSpace B).hom) ≫
    CartesianMonoidalCategory.snd ((rawRowFunctor (op ⦋0⦌)).obj coherentSpace)
      ((rawRowFunctor (op ⦋0⦌)).obj B) = _
  rw [Category.assoc, prodComparisonIso_hom,
    CartesianMonoidalCategory.prodComparison_snd, ← CategoryTheory.Functor.map_comp,
        (spaceEndpoint_laws B e).2.1,
    CategoryTheory.Functor.map_id]

/-- BOTH original endpoint insertions are weak, without a weak raw-unit premise. -/
theorem rawTensorEndpoint_weak (B : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    SSet.realizationWeakEquivalences (rawTensorEndpoint B e) := by
  apply (SSet.realizationWeakEquivalences.postcomp_iff _ _
    (originalRawEInterval_projection_weak
      ((rawRowFunctor (op ⦋0⦌)).obj B))).mp
  rw [rawTensorEndpoint_snd]
  exact SSet.realizationWeakEquivalences.id_mem _

/-- The existing categorical contraction is kept as its actual whole map. -/
def originalPowerHomotopy (W : SimplicialSpace.{u}) :
    coherentSpace ⊗ powerSpace W ⟶ powerSpace W :=
  ofSimplicialObject.map (powerCategoricalHomotopy W)

/-- Its endpoints are the original evaluation-constant composite and identity. -/
theorem originalPowerHomotopy_endpoints (W : SimplicialSpace.{u}) :
    spaceEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫ originalPowerHomotopy W =
        zeroEvaluation W ≫ constantPower W ∧
      spaceEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫ originalPowerHomotopy W =
        𝟙 (powerSpace W) := by
  constructor
  · apply SimplicialSpace.homEquiv.injective
    change (spaceEndpoint (powerSpace W) SSet.coherentIso.x₀).hom ≫
      powerCategoricalHomotopy W = (zeroEvaluation W ≫ constantPower W).hom
    rw [(spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₀).2.2]
    exact (powerCategoricalHomotopy_endpoints W).1
  · apply SimplicialSpace.homEquiv.injective
    change (spaceEndpoint (powerSpace W) SSet.coherentIso.x₁).hom ≫
      powerCategoricalHomotopy W = (𝟙 (powerSpace W) : powerSpace W ⟶ powerSpace W).hom
    rw [(spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₁).2.2]
    exact (powerCategoricalHomotopy_endpoints W).2

/-- The actual scalar raw(E)_0 homotopy, transported through the proved native
product comparison, acts on raw(W raised to the whole E)_0. -/
def rawPowerHomotopy (W : SimplicialSpace.{u}) :
    originalRawEInterval ⊗ (rawRowFunctor (op ⦋0⦌)).obj (powerSpace W) ⟶
      (rawRowFunctor (op ⦋0⦌)).obj (powerSpace W) :=
  (prodComparisonIso (rawRowFunctor (op ⦋0⦌)) coherentSpace (powerSpace W)).inv ≫
    (rawRowFunctor (op ⦋0⦌)).map (originalPowerHomotopy W)

set_option backward.isDefEq.respectTransparency false in
/-- Both raw endpoint composites are the exact original two whole maps. -/
theorem rawPowerHomotopy_endpoints (W : SimplicialSpace.{u}) :
    rawTensorEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫ rawPowerHomotopy W =
        (rawRowFunctor (op ⦋0⦌)).map (zeroEvaluation W) ≫
          (rawRowFunctor (op ⦋0⦌)).map (constantPower W) ∧
      rawTensorEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫ rawPowerHomotopy W =
        𝟙 ((rawRowFunctor (op ⦋0⦌)).obj (powerSpace W)) := by
  constructor
  · dsimp only [rawTensorEndpoint, rawPowerHomotopy]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp,
      (originalPowerHomotopy_endpoints W).1, CategoryTheory.Functor.map_comp]
  · dsimp only [rawTensorEndpoint, rawPowerHomotopy]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp,
      (originalPowerHomotopy_endpoints W).2, CategoryTheory.Functor.map_id]

/-- The SAME original raw constant full-E power map is weak. This is derived
from the actual raw interval, both native endpoints and a strict Arrow retract;
neither rawCompletionUnit nor the desired core comparison is assumed weak. -/
theorem originalRaw_constantPower_weak (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences
      ((rawCompletionMap (constantPower W)).hom.app (op ⦋0⦌)) := by
  let F := rawRowFunctor.{u} (op ⦋0⦌)
  let p := F.map (constantPower W)
  let q := F.map (zeroEvaluation W)
  have hpq : p ≫ q = 𝟙 (F.obj W) := by
    dsimp only [p, q]
    rw [← F.map_comp, constantPower_zeroEvaluation, F.map_id]
  have hH : SSet.realizationWeakEquivalences (rawPowerHomotopy W) := by
    apply (SSet.realizationWeakEquivalences.precomp_iff _ _
      (rawTensorEndpoint_weak (powerSpace W) SSet.coherentIso.x₁)).mp
    rw [(rawPowerHomotopy_endpoints W).2]
    exact SSet.realizationWeakEquivalences.id_mem _
  have hqp : SSet.realizationWeakEquivalences (q ≫ p) := by
    have h := SSet.realizationWeakEquivalences.comp_mem _ _
      (rawTensorEndpoint_weak (powerSpace W) SSet.coherentIso.x₀) hH
    rw [(rawPowerHomotopy_endpoints W).1] at h
    exact h
  let retract : RetractArrow p (q ≫ p) :=
    { i := Arrow.homMk p (𝟙 _) (by
        change p ≫ (q ≫ p) = p ≫ (𝟙 _)
        rw [← Category.assoc, hpq, Category.id_comp, Category.comp_id])
      r := Arrow.homMk q (𝟙 _) (by
        change q ≫ p = (q ≫ p) ≫ (𝟙 _)
        rw [Category.comp_id])
      retract := by
        apply Arrow.hom_ext
        · change p ≫ q = 𝟙 _
          exact hpq
        · change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
          rw [Category.id_comp] }
  exact MorphismProperty.of_retract
    (P := SSet.realizationWeakEquivalences) retract hqp

/-- The corresponding original raw zero-evaluation is weak by its strict section equation. -/
theorem originalRaw_zeroEvaluation_weak (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences
      ((rawCompletionMap (zeroEvaluation W)).hom.app (op ⦋0⦌)) := by
  let F := rawRowFunctor.{u} (op ⦋0⦌)
  have hp : SSet.realizationWeakEquivalences (F.map (constantPower W)) :=
    originalRaw_constantPower_weak W
  apply (SSet.realizationWeakEquivalences.precomp_iff _ _ hp).mp
  change SSet.realizationWeakEquivalences
    (F.map (constantPower W) ≫ F.map (zeroEvaluation W))
  rw [← F.map_comp, constantPower_zeroEvaluation, F.map_id]
  exact SSet.realizationWeakEquivalences.id_mem _

end SimplicialSpace.OriginalRawZeroConstantPowerWeak

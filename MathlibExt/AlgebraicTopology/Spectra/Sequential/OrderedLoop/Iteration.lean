/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Full original ordered loop iteration and its level model properties

The actual ordered loop-successor uses the original right-Quillen
sphere-one internal Hom. It preserves the original level weak and
fibration classes and actual Omega objects. Its original natural unit
is level weak exactly on Omega objects. The SAME functor and unit give
the full iteration diagram, including every stage, all transitions and
all original input Arrow maps with identity/composition/naturality.
The genuine free function-spectrum identity and telescope pi* calculation
remain separate pre-model source obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

private theorem fullTransition_app
    {C : Type u₁} [Category.{v₁} C] (F R : C ⥤ C) (t : 𝟭 C ⟶ R) (X : C) :
    (F.rightUnitor.inv ≫ CategoryTheory.Functor.whiskerLeft F t).app X = t.app (F.obj X) := by
  change 𝟙 (F.obj X) ≫ t.app (F.obj X) = _
  exact Category.id_comp _

namespace PointedCGWH.SequentialSpectrum.OrderedLoop
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private theorem pointedWeak_iff {A C : PointedCGWH.{u, v}} (f : A ⟶ C) :
    weakEquivalences PointedCGWH.{u, v} f ↔ CGWH.weakHomotopyEquivalences f.right :=
  (HomotopicalAlgebra.weakEquivalence_iff f).symm.trans
    ((PointedCGWH.weakEquivalence_iff f).trans (CGWH.modelCategory.weakEquivalence_iff f.right))

/--
The actual original sphere-one internal Hom preserves pointed weak maps on all original
spaces.
-/
private theorem loop_map_weak {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : weakEquivalences PointedCGWH.{u, v} f) :
    weakEquivalences PointedCGWH.{u, v} ((ihom PointedCGWH.sphereOne).map f) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : IsFibrant A := PointedCGWH.modelCategory.allObjectsFibrant A
  let _ : IsFibrant C := PointedCGWH.modelCategory.allObjectsFibrant C
  let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant
    PointedCGWH.sphereOne.{u, v}
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).mpr hf
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := ihom.adjunction PointedCGWH.sphereOne.{u, v}) f)

/-- The actual original sphere-one internal Hom preserves the original pointed fibration class. -/
private theorem loop_map_fibration {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : fibrations PointedCGWH.{u, v} f) :
    fibrations PointedCGWH.{u, v} ((ihom PointedCGWH.sphereOne).map f) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant
    PointedCGWH.sphereOne.{u, v}
  exact Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := ihom.adjunction PointedCGWH.sphereOne) f hf

/-- Every actual original Omega object remains Omega under the SAME full ordered loop functor. -/
theorem functor_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) (hX : X.IsOmega) :
    (functor.obj X).IsOmega := by
  intro n
  change CGWH.weakHomotopyEquivalences
    (PointedCGWH.SequentialSpectrum.adjointStructureMap (functor.obj X) n).right
  rw [functor_adjointStructureMap]
  exact (pointedWeak_iff _).mp
    (loop_map_weak _ ((pointedWeak_iff _).mpr (hX (n + 1))))

/-- The SAME native functor and unit commute as full original spectrum Arrows. -/
theorem functor_map_unit (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    functor.map (unit.app X) = unit.app (functor.obj X) := by
  apply PointedCGWH.SequentialSpectrum.hom_ext
  intro n
  rw [functor_map_levelMap, unit_levelMap, unit_levelMap, functor_adjointStructureMap]
  rfl

/-- Every iteration is the SAME whole native functor, with all its original input maps and laws. -/
def iterate : ℕ → (PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v})
  | 0 => 𝟭 _
  | n + 1 => iterate n ⋙ functor

/-- Each complete iteration transition is the original unit at the original preceding stage. -/
def iterateUnit (n : ℕ) : iterate.{u, v} n ⟶ iterate (n + 1) :=
  (iterate n).rightUnitor.inv ≫ CategoryTheory.Functor.whiskerLeft (iterate n) unit

/-- The complete original transition component retains the actual original unit map. -/
theorem iterateUnit_app (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (iterateUnit n).app X = unit.app ((iterate n).obj X) :=
  fullTransition_app (iterate n) functor unit X

/-- Every complete original input Arrow square commutes through the iteration transition. -/
theorem iterateUnit_naturality (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (iterate n).map f ≫ (iterateUnit n).app Y =
      (iterateUnit n).app X ≫ (iterate (n + 1)).map f :=
  (iterateUnit n).naturality f

/-- ALL original actual Omega objects have Omega objects at EVERY original iteration stage. -/
theorem iterate_isOmega (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (hX : X.IsOmega) :
    ((iterate n).obj X).IsOmega := by
  induction n with
  | zero => exact hX
  | succ n hn => exact functor_isOmega _ hn

/-- The entire ordered iteration diagram uses the SAME original stages and unit transitions. -/
def iterationDiagram (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  Functor.ofSequence (fun n => (iterateUnit n).app X)

/-- Every original stage of the complete iteration diagram is the SAME actual full iterate. -/
theorem iterationDiagram_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (iterationDiagram X).obj n = (iterate n).obj X := rfl

/-- Every original successive transition is the SAME original full unit transition. -/
theorem iterationDiagram_map_succ (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (iterationDiagram X).map (homOfLE (Nat.le_add_right n 1)) = (iterateUnit n).app X :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- All original input spectrum maps give whole natural transformations of the full diagrams. -/
def iterationDiagramMap {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    iterationDiagram X ⟶ iterationDiagram Y :=
  NatTrans.ofSequence (fun n => (iterate n).map f) (fun n => by
    rw [iterationDiagram_map_succ, iterationDiagram_map_succ]
    exact (iterateUnit_naturality n f).symm)

/--
The complete original iteration preserves input identities and compositions as a full functor.
-/
def iterationDiagramFunctor : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ PointedCGWH.SequentialSpectrum.{u, v}) where
  obj := iterationDiagram
  map := iterationDiagramMap
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (iterate n).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (iterate n).map_comp f g

/-- Every complete original input map has the same actual full component at every stage. -/
theorem iterationDiagramFunctor_map_app
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    (iterationDiagramFunctor.map f).app n = (iterate n).map f := rfl

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual whole ordered loop functor preserves the SAME original native level weak class. -/
theorem functor_map_levelWeak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (functor.map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hf ⊢
  have h := (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} => EnrichedFunctorCat.evaluation a)
    (weakEquivalences PointedCGWH.{u, v}) f).mp hf
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} => EnrichedFunctorCat.evaluation a)
    (weakEquivalences PointedCGWH.{u, v}) _).mpr
  intro a
  rcases a with ⟨n⟩
  change weakEquivalences PointedCGWH.{u, v}
    (PointedCGWH.SequentialSpectrum.levelMap (functor.map f) n)
  rw [functor_map_levelMap]
  exact loop_map_weak _
    (h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (n + 1)))

/-- The SAME native level fibration class is retained by the actual full ordered loop functor. -/
theorem functor_map_levelFibration
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : fibrations PointedCGWH.SequentialSpectrum.{u, v} f) :
    fibrations PointedCGWH.SequentialSpectrum.{u, v} (functor.map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq] at hf ⊢
  have h := (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} => EnrichedFunctorCat.evaluation a)
    (fibrations PointedCGWH.{u, v}) f).mp hf
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun a : PointedCGWH.Spectra.Sequential.Index.{u, v} => EnrichedFunctorCat.evaluation a)
    (fibrations PointedCGWH.{u, v}) _).mpr
  intro a
  rcases a with ⟨n⟩
  change fibrations PointedCGWH.{u, v}
    (PointedCGWH.SequentialSpectrum.levelMap (functor.map f) n)
  rw [functor_map_levelMap]
  exact loop_map_fibration _
    (h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (n + 1)))

/-- The SAME full level trivial-fibration class is preserved on arbitrary native endpoints. -/
theorem functor_map_levelTF
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} f) :
    trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} (functor.map f) :=
  ⟨functor_map_levelFibration f hf.1, functor_map_levelWeak f hf.2⟩

/-- The entire original native unit is level weak EXACTLY on the original Omega objects. -/
theorem unit_levelWeak_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (unit.app X) ↔ X.IsOmega := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  rw [EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    have ht := h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
    change weakEquivalences PointedCGWH.{u, v}
      (PointedCGWH.SequentialSpectrum.levelMap (unit.app X) n) at ht
    rw [unit_levelMap] at ht
    exact (pointedWeak_iff _).mp ht
  · intro h a
    rcases a with ⟨n⟩
    change weakEquivalences PointedCGWH.{u, v}
      (PointedCGWH.SequentialSpectrum.levelMap (unit.app X) n)
    rw [unit_levelMap]
    exact (pointedWeak_iff _).mpr (h n)

/-- Every actual iteration stage preserves the SAME original native level weak class. -/
theorem iterate_map_levelWeak (n : ℕ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((iterate n).map f) := by
  induction n with
  | zero => exact hf
  | succ n hn => exact functor_map_levelWeak _ hn

/-- Every actual original unit transition at every original Omega stage is level weak. -/
theorem iterateUnit_levelWeak (n : ℕ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (hX : X.IsOmega) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} ((iterateUnit n).app X) := by
  rw [iterateUnit_app]
  exact (unit_levelWeak_iff _).mpr (iterate_isOmega n X hX)

end PointedCGWH.SequentialSpectrum.OrderedLoop

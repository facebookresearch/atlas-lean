/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneCoordinateData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyInjectiveComparison
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Global fibrations at one simplex coordinate

Global injective fibrations on the one-coordinate presheaf site correspond to scalar injective
fibrations and to Reedy fibrations of the designated simplicial spaces. The same class is
characterized by the right lifting property of every relative matching map, and its
terminal-map specialization identifies the corresponding fibrant objects.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite
namespace SimplicialPresheaf.OrderedJFS

private theorem oneOriginalTuple_covered (a : (FinitePowerSite.Source 1)ᵒᵖ) :
    oneSiteEquivalence.inverse.op.obj (op (a.unop 0)) = a := by
  apply Opposite.unop_injective
  change (fun _ : Fin 1 => a.unop 0) = a.unop
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem oneOriginal_baseWeak_iff {A B : Original.{u} 1} (f : A ⟶ B) :
    SimplicialPresheaf.objectwiseKanWeakEquivalences (FinitePowerSite.Source 1) f ↔
      SimplicialPresheaf.objectwiseKanWeakEquivalences SimplexCategory
        (oneOriginalEquivalence.{u}.functor.map f) := by
  change (∀ a, SSet.realizationWeakEquivalences (f.app a)) ↔
    ∀ n, SSet.realizationWeakEquivalences
      (((oneOriginalEquivalence.{u}).functor.map f).app n)
  constructor
  · intro h n
    change SSet.realizationWeakEquivalences (f.app (oneSiteEquivalence.inverse.op.obj n))
    exact h _
  · intro h a
    have hn := h (op (a.unop 0))
    change SSet.realizationWeakEquivalences
      (f.app (oneSiteEquivalence.inverse.op.obj (op (a.unop 0)))) at hn
    exact Eq.mp (congrArg (fun b => SSet.realizationWeakEquivalences (f.app b))
      (oneOriginalTuple_covered a)) hn

set_option backward.isDefEq.respectTransparency false in
private theorem oneOriginal_trivial_forward {A B : Original.{u} 1} (f : A ⟶ B)
    (hf : InjectiveKan.trivialMonomorphisms (FinitePowerSite.Source 1) f) :
    InjectiveKan.trivialMonomorphisms SimplexCategory
      (oneOriginalEquivalence.{u}.functor.map f) := by
  let : Mono f := hf.1
  exact ⟨monomorphisms.infer_property _, (oneOriginal_baseWeak_iff f).mp hf.2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem oneOriginal_trivial_inverse
    {A B : SimplicialPresheaf.{u} SimplexCategory} (i : A ⟶ B)
    (hi : InjectiveKan.trivialMonomorphisms SimplexCategory i) :
    InjectiveKan.trivialMonomorphisms (FinitePowerSite.Source 1)
      (oneOriginalEquivalence.{u}.inverse.map i) := by
  let : Mono i := hi.1
  refine ⟨monomorphisms.infer_property _, ?_⟩
  intro a
  change SSet.realizationWeakEquivalences (i.app (oneSiteEquivalence.functor.op.obj a))
  exact hi.2 _

private theorem oneOriginal_globalFib_iff_raw
    {A B : Original.{u} 1} (p : A ⟶ B) :
    InjectiveKan.injectiveFibrations (FinitePowerSite.Source 1) p ↔
      InjectiveKan.injectiveFibrations SimplexCategory
        (oneOriginalEquivalence.{u}.functor.map p) := by
  constructor
  · intro hp U V i hi
    have hLift : HasLiftingProperty (oneOriginalEquivalence.{u}.inverse.map i) p :=
      hp _ (oneOriginal_trivial_inverse i hi)
    exact (oneOriginalEquivalence.{u}.symm.toAdjunction.hasLiftingProperty_iff i p).mp hLift
  · intro hp U V i hi
    exact (oneOriginalEquivalence.{u}.functor.hasLiftingProperty_iff_of_isEquivalence i p).mp
      (hp _ (oneOriginal_trivial_forward i hi))

set_option backward.isDefEq.respectTransparency false in
private theorem oneRaw_trivial_forward
    {A B : SimplicialPresheaf.{u} SimplexCategory} (f : A ⟶ B)
    (hf : InjectiveKan.trivialMonomorphisms SimplexCategory f) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    trivialCofibrations SimplicialSpace.{u}
      (SimplicialSpace.ofSimplicialObject.map f) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let : Mono f := hf.1
  change (cofibrations SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map f) ∧
    weakEquivalences SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map f))
  rw [SimplicialSpace.ReedyModel.selectedReedy_injective_classes.1,
    SimplicialSpace.ReedyModel.selectedReedy_injective_classes.2.1]
  exact ⟨monomorphisms.infer_property _, hf.2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem oneRaw_trivial_inverse {A B : SimplicialSpace.{u}} (i : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    trivialCofibrations SimplicialSpace.{u} i →
      InjectiveKan.trivialMonomorphisms SimplexCategory (SimplicialSpace.forget.map i) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  intro hi
  change (cofibrations SimplicialSpace.{u} i ∧ weakEquivalences SimplicialSpace.{u} i) at hi
  rw [SimplicialSpace.ReedyModel.selectedReedy_injective_classes.1,
    SimplicialSpace.ReedyModel.selectedReedy_injective_classes.2.1] at hi
  let : Mono i := hi.1
  exact ⟨monomorphisms.infer_property _, hi.2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem oneRaw_globalFib_iff_reedy
    {A B : SimplicialPresheaf.{u} SimplexCategory} (p : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    InjectiveKan.injectiveFibrations SimplexCategory p ↔
      fibrations SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map p) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let E := SimplicialSpace.equivalenceSimplicialObject.{u}.symm
  rw [← trivialCofibrations_rlp SimplicialSpace.{u}]
  constructor
  · intro hp U V i hi
    have hLift : HasLiftingProperty (E.inverse.map i) p :=
      hp _ (oneRaw_trivial_inverse i hi)
    exact (E.symm.toAdjunction.hasLiftingProperty_iff i p).mp hLift
  · intro hp U V i hi
    exact (E.functor.hasLiftingProperty_iff_of_isEquivalence i p).mp
      (hp _ (oneRaw_trivial_forward i hi))

/-- The original Fin1 GLOBAL injective class agrees with raw scalar injective,
named Reedy and every native relative matching condition, preserving the same arrow.
Both equivalences and test-class transports are internally constructed. -/
theorem one_globalInjectiveFibration_iff {A B : Original.{u} 1} (p : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    (InjectiveKan.injectiveFibrations (FinitePowerSite.Source 1) p ↔
      InjectiveKan.injectiveFibrations SimplexCategory
        (oneOriginalEquivalence.{u}.functor.map p)) ∧
    (InjectiveKan.injectiveFibrations (FinitePowerSite.Source 1) p ↔
      fibrations SimplicialSpace.{u} (oneDesignatedEquivalence.{u}.functor.map p)) ∧
    (InjectiveKan.injectiveFibrations (FinitePowerSite.Source 1) p ↔
      ∀ n : ℕ, SSet.modelCategoryQuillen.J.rlp
        (SimplicialObject.relativeMatchingMap
          (oneOriginalEquivalence.{u}.functor.map p) n)) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have hr := oneOriginal_globalFib_iff_raw p
  have hd := hr.trans (oneRaw_globalFib_iff_reedy (oneOriginalEquivalence.{u}.functor.map p))
  have hm := (HomotopicalAlgebra.fibration_iff
    (oneDesignatedEquivalence.{u}.functor.map p)).symm.trans
      (SimplicialSpace.ReedyModel.fibration_iff (oneDesignatedEquivalence.{u}.functor.map p))
  change (fibrations SimplicialSpace.{u} (oneDesignatedEquivalence.{u}.functor.map p) ↔
    ∀ n : ℕ, SSet.modelCategoryQuillen.J.rlp
      (SimplicialObject.relativeMatchingMap (oneOriginalEquivalence.{u}.functor.map p) n)) at hm
  exact ⟨hr, hd, hd.trans hm⟩

/-- The actual original terminal RLP yields the named scalar Reedy fibrancy and
all raw matching degrees, using the preserved terminal object and both native lift directions. -/
theorem one_globalInjectiveFibrant_iff (X : Original.{u} 1) :
    (letI : ModelCategory (Original.{u} 1) :=
        (InjectiveKan.data.{u} (FinitePowerSite.Source 1)).model
     IsFibrant X) ↔
      (letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
       IsFibrant (oneDesignatedEquivalence.{u}.functor.obj X)) := by
  let _ : ModelCategory (Original.{u} 1) :=
    (InjectiveKan.data.{u} (FinitePowerSite.Source 1)).model
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have hOriginal : IsFibrant X ↔
      InjectiveKan.injectiveFibrations (FinitePowerSite.Source 1) (terminal.from X) := by
    rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff]
    change
        (InjectiveKan.data.{u} (FinitePowerSite.Source 1)).model.categoryWithFibrations.fibrations
      (terminal.from X) ↔ _
    rw [(InjectiveKan.data.{u} (FinitePowerSite.Source 1)).fibrations_eq]
  have ht : IsTerminal (oneDesignatedEquivalence.{u}.functor.obj (⊤_ Original.{u} 1)) :=
    terminalIsTerminal.isTerminalObj oneDesignatedEquivalence.{u}.functor _
  let _ : (fibrations SimplicialSpace.{u}).RespectsIso := by
    rw [SimplicialSpace.ReedyModel.selectedReedy_injective_classes.2.2]
    infer_instance
  have hTarget : IsFibrant (oneDesignatedEquivalence.{u}.functor.obj X) ↔
      fibrations SimplicialSpace.{u}
        (oneDesignatedEquivalence.{u}.functor.map (terminal.from X)) := by
    rw [isFibrant_iff_of_isTerminal
      (oneDesignatedEquivalence.{u}.functor.map (terminal.from X)) ht,
      HomotopicalAlgebra.fibration_iff]
  exact hOriginal.trans (((one_globalInjectiveFibration_iff (terminal.from X)).2.1).trans
    hTarget.symm)

end SimplicialPresheaf.OrderedJFS

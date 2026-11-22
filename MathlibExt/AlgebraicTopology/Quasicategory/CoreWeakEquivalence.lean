/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown
import MathlibExt.AlgebraicTopology.Quasicategory.CoreFunctor
import MathlibExt.AlgebraicTopology.Quasicategory.CoreTrivialFibration
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence

/-!
# Core weak equivalences

Cisinski's Theorem 3.6.8 proof uses the all-simplicial-set core functor and
Brown's lemma. The target class here is the global realization weak-equivalence
class, identified with structural Kan weak equivalences at quasicategory cores.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped JoyalSSet.ModelCategory

namespace JoyalSSet

private theorem copied_isFibrant_iff_quasicategory (X : JoyalSSet.{u}) :
    IsFibrant X ↔ SSet.Quasicategory X.toSSet := by
  let T := ofSSet.obj (terminal SSet.{u})
  let p : X ⟶ T := InducedCategory.homMk (terminal.from X.toSSet)
  have hT : IsTerminal T :=
    IsTerminal.isTerminalObj ofSSet (terminal SSet.{u}) terminalIsTerminal
  rw [isFibrant_iff_of_isTerminal p hT, fibration_iff]
  change modelCategory.categoryWithFibrations.fibrations p ↔ _
  rw [modelCategory_fibrations]
  change SSet.categoricalFibrations (terminal.from X.toSSet) ↔ _
  exact SSet.categoricalFibrations.terminalFrom_iff_quasicategory X.toSSet

private theorem copied_trivialFibrations_iff {X Y : JoyalSSet.{u}} (p : X ⟶ Y) :
    trivialFibrations JoyalSSet.{u} p ↔
      SSet.modelCategoryQuillen.I.rlp (forget.map p) := by
  change
    modelCategory.categoryWithFibrations.fibrations p ∧
      modelCategory.categoryWithWeakEquivalences.weakEquivalences p ↔ _
  rw [modelCategory_fibrations, modelCategory_weakEquivalences]
  exact SSet.categoricalFibrations_and_categoricalEquivalences_iff (forget.map p)

end JoyalSSet

namespace SSet

/-- Core carries categorical equivalences between quasicategories to
structural Kan–Quillen weak equivalences. The result includes that both
literal cores are Kan complexes. -/
theorem core_map_mem_W_of_categoricalEquivalence
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : categoricalEquivalences f) :
    KanComplex.W (core.map f) := by
  let F := JoyalSSet.forget.{u} ⋙ coreFunctor.{u}
  let V := realizationWeakEquivalences.{u}
  have hTF : ∀ {A B : JoyalSSet.{u}} (p : A ⟶ B)
      [IsFibrant A] [IsFibrant B], trivialFibrations JoyalSSet.{u} p →
        V (F.map p) := by
    intro A B p _ _ hp
    have hpI := (JoyalSSet.copied_trivialFibrations_iff p).mp hp
    have hpRLP : (monomorphisms SSet.{u}).rlp (JoyalSSet.forget.map p) := by
      rwa [rlp_monomorphisms]
    have hc := core_map_mem_rlp_monomorphisms hpRLP
    rw [rlp_monomorphisms] at hc
    change realizationWeakEquivalences (core.map (JoyalSSet.forget.map p))
    exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ hc
  let _ : IsFibrant (JoyalSSet.ofSSet.obj X) :=
    (JoyalSSet.copied_isFibrant_iff_quasicategory _).mpr (by
      change Quasicategory X
      infer_instance)
  let _ : IsFibrant (JoyalSSet.ofSSet.obj Y) :=
    (JoyalSSet.copied_isFibrant_iff_quasicategory _).mpr (by
      change Quasicategory Y
      infer_instance)
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map f) := by
    rw [weakEquivalence_iff]
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (JoyalSSet.ofSSet.map f)
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hf
  have hV := Functor.map_mem_of_weakEquivalence_of_fibrant F V
    (isomorphisms_le_of_containsIdentities V) hTF (JoyalSSet.ofSSet.map f)
  change realizationWeakEquivalences (core.map f) at hV
  exact (KanComplex.W_iff_realizationWeakEquivalence (core.map f)).mpr hV

end SSet

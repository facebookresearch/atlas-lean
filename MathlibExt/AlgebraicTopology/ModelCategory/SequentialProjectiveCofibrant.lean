/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Cofibrant sequences in the projective model

First construct a whole natural transformation through an objectwise
trivial fibration, retaining the chosen degree-zero map. Each successor
uses the original source transition cofibration and the original
target transition. This is a diagram-valued lifting construction.
Consequently, a sequence with cofibrant degree zero and cofibration
transitions is cofibrant in any model with the projective right class.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.SequentialProjectiveLifting

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The original degree-zero lift extends to a compatible whole diagram lift through an objectwise
trivial fibration. -/
theorem exists_natTrans_of_fixed_zero
    {F E B : ℕ ⥤ C} (q : E ⟶ B) (b : F ⟶ B)
    (hstep : ∀ n : ℕ, Cofibration (F.map (homOfLE (n.le_add_right 1))))
    (hq : ∀ n, trivialFibrations C (q.app n))
    (l₀ : F.obj 0 ⟶ E.obj 0) (hl₀ : l₀ ≫ q.app 0 = b.app 0) :
    ∃ l : F ⟶ E, l ≫ q = b ∧ l.app 0 = l₀ := by
  let L (n : ℕ) := {l : F.obj n ⟶ E.obj n // l ≫ q.app n = b.app n}
  let step (n : ℕ) (l : L n) :
      {l' : L (n + 1) // F.map (homOfLE (n.le_add_right 1)) ≫ l'.val =
        l.val ≫ E.map (homOfLE (n.le_add_right 1))} := by
    let _ : Cofibration (F.map (homOfLE (n.le_add_right 1))) := hstep n
    let _ : Fibration (q.app (n + 1)) := (mem_trivialFibrations_iff _ |>.mp (hq (n + 1))).1
    let _ : WeakEquivalence (q.app (n + 1)) := (mem_trivialFibrations_iff _ |>.mp (hq (n + 1))).2
    let sq : CommSq (l.val ≫ E.map (homOfLE (n.le_add_right 1)))
        (F.map (homOfLE (n.le_add_right 1))) (q.app (n + 1)) (b.app (n + 1)) :=
      ⟨by
        rw [Category.assoc, q.naturality, ← Category.assoc, l.property]
        exact (b.naturality _).symm⟩
    exact ⟨⟨sq.lift, sq.fac_right⟩, sq.fac_left⟩
  let lifts : ∀ n, L n := Nat.rec ⟨l₀, hl₀⟩ (fun n l => (step n l).val)
  have compatibility (n : ℕ) :
      F.map (homOfLE (n.le_add_right 1)) ≫ (lifts (n + 1)).val =
        (lifts n).val ≫ E.map (homOfLE (n.le_add_right 1)) :=
    (step n (lifts n)).property
  let l : F ⟶ E := NatTrans.ofSequence (fun n => (lifts n).val) compatibility
  refine ⟨l, ?_, rfl⟩
  ext n
  exact (lifts n).property

variable [ModelCategory (ℕ ⥤ C)]

/-- Initial cofibrancy and the actual transition cofibrations imply projective cofibrancy of the
whole original sequence. -/
theorem isCofibrant_of_cofibration_transitions
    (hT : trivialFibrations (ℕ ⥤ C) = (trivialFibrations C).functorCategory ℕ)
    (F : ℕ ⥤ C) [IsCofibrant (F.obj 0)]
    (hstep : ∀ n : ℕ, Cofibration (F.map (homOfLE (n.le_add_right 1)))) :
    IsCofibrant F := by
  rw [isCofibrant_iff, cofibration_iff,
    ← llp_eq_of_wfs (cofibrations (ℕ ⥤ C)) (trivialFibrations (ℕ ⥤ C))]
  intro E B q hq
  have hcomponents : ∀ n, trivialFibrations C (q.app n) := by
    rw [hT] at hq
    exact hq
  constructor
  intro a b sq
  let _ : Fibration (q.app 0) := (mem_trivialFibrations_iff _ |>.mp (hcomponents 0)).1
  let _ : WeakEquivalence (q.app 0) := (mem_trivialFibrations_iff _ |>.mp (hcomponents 0)).2
  let initialSquare : CommSq (initial.to (E.obj 0)) (initial.to (F.obj 0))
      (q.app 0) (b.app 0) := ⟨Subsingleton.elim _ _⟩
  obtain ⟨l, hl, _⟩ := exists_natTrans_of_fixed_zero q b hstep hcomponents
    initialSquare.lift initialSquare.fac_right
  exact CommSq.HasLift.mk' ⟨l, initialIsInitial.hom_ext _ _, hl⟩

end HomotopicalAlgebra.SequentialProjectiveLifting

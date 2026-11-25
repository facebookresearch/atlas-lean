/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.SectionHomotopyExtension
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Compatible maps obtained from actual successive fiberwise homotopies

Each original map lies over its original base map. The actual successor
homotopy is in the slice category, not only pointwise in its fibers.
The stock homotopy-extension theorem retunes the next map strictly on the
old source and returns its whole global comparison. Induction therefore
keeps every earlier restriction and every original fixed-base equation.
-/

noncomputable section

open CategoryTheory Limits

universe u v

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private structure FibrationStageMap (F : ℕ ⥤ C) {E T : C} (p : E ⟶ T)
    (b : (n : ℕ) → F.obj n ⟶ T) (s : (n : ℕ) → F.obj n ⟶ E)
    (hs : ∀ n, s n ≫ p = b n) (n : ℕ) where
  /-- The actual current map, on the original stage carrier. -/
  map : F.obj n ⟶ E
  /-- Its complete original fixed-base equation. -/
  over : map ≫ p = b n
  /-- Its whole global comparison in the actual slice model category. -/
  homotopy : RightHomotopyRel
    (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))
    (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) map over)

private def nextFibrationStageMap
    (F : ℕ ⥤ C) {E T : C} (p : E ⟶ T) [Fibration p]
    (b : (n : ℕ) → F.obj n ⟶ T) (s : (n : ℕ) → F.obj n ⟶ E)
    (hs : ∀ n, s n ≫ p = b n)
    (hobjects : ∀ n, IsCofibrant (F.obj n))
    (hcof : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hb : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n)
    (hstep : ∀ n, LeftHomotopyRel
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p)
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1))
        (by
          change (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ p = b n
          rw [Category.assoc, hs, hb]))
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n)))
    (n : ℕ) (a : FibrationStageMap F p b s hs n) :
    { a' : FibrationStageMap F p b s hs (n + 1) //
      F.map (homOfLE (Nat.le_succ n)) ≫ a'.map = a.map } := by
  letI : IsCofibrant (F.obj n) := hobjects n
  letI : Cofibration (F.map (homOfLE (Nat.le_succ n))) := hcof n
  letI : IsCofibrant (Over.mk (b n)) := overMk_isCofibrant (b n)
  letI : IsFibrant (Over.mk p) := overMk_isFibrant p
  have ha : LeftHomotopyRel
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) a.map a.over) :=
    a.homotopy.leftHomotopyRel
  have hex := exists_fibration_extension_with_over_homotopy
    (F.map (homOfLE (Nat.le_succ n))) p (b n) (b (n + 1)) (hb n)
    (s (n + 1)) (hs (n + 1)) a.map a.over ((hstep n).trans ha)
  let r := Classical.choose hex
  let hr := Classical.choose (Classical.choose_spec hex)
  have hspec := Classical.choose_spec (Classical.choose_spec hex)
  exact ⟨{ map := r, over := hr, homotopy := hspec.2 }, hspec.1⟩

/-- Actual successor cofibrations and whole original slice homotopies
derive a compatible sequence. Every map retains its original base and
whole comparison class; no compatible family or extension is assumed. -/
public theorem exists_compatible_fibration_maps
    (F : ℕ ⥤ C) {E T : C} (p : E ⟶ T) [Fibration p]
    (b : (n : ℕ) → F.obj n ⟶ T) (s : (n : ℕ) → F.obj n ⟶ E)
    (hs : ∀ n, s n ≫ p = b n)
    (hobjects : ∀ n, IsCofibrant (F.obj n))
    (hcof : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hb : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n)
    (hstep : ∀ n, LeftHomotopyRel
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p)
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1))
        (by
          change (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ p = b n
          rw [Category.assoc, hs, hb]))
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))) :
    ∃ s' : (n : ℕ) → F.obj n ⟶ E,
      s' 0 = s 0 ∧
      (∀ n, ∃ h : s' n ≫ p = b n,
        RightHomotopyRel
          (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))
          (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s' n) h)) ∧
      ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ s' (n + 1) = s' n := by
  let : IsFibrant (Over.mk p) := overMk_isFibrant p
  let a₀ : FibrationStageMap F p b s hs 0 :=
    { map := s 0, over := hs 0, homotopy := RightHomotopyRel.refl _ }
  let a : (n : ℕ) → FibrationStageMap F p b s hs n :=
    Nat.rec a₀ (fun n r => (nextFibrationStageMap F p b s hs
      hobjects hcof hb hstep n r).val)
  refine ⟨fun n => (a n).map, rfl, ?_, ?_⟩
  · intro n
    exact ⟨(a n).over, (a n).homotopy⟩
  · intro n
    change F.map (homOfLE (Nat.le_succ n)) ≫
      (nextFibrationStageMap F p b s hs hobjects hcof hb hstep n (a n)).val.map = (a n).map
    exact (nextFibrationStageMap F p b s hs hobjects hcof hb hstep n (a n)).property

/-- The derived successor-compatible maps form a genuine natural
transformation on the ENTIRE original natural-number diagram. All-arrow
naturality is supplied by the existing stock `NatTrans.ofSequence`. -/
public theorem exists_fibration_cocone_of_successor_homotopies
    (F : ℕ ⥤ C) {E T : C} (p : E ⟶ T) [Fibration p]
    (b : (n : ℕ) → F.obj n ⟶ T) (s : (n : ℕ) → F.obj n ⟶ E)
    (hs : ∀ n, s n ≫ p = b n)
    (hobjects : ∀ n, IsCofibrant (F.obj n))
    (hcof : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hb : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ b (n + 1) = b n)
    (hstep : ∀ n, LeftHomotopyRel
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p)
        (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1))
        (by
          change (F.map (homOfLE (Nat.le_succ n)) ≫ s (n + 1)) ≫ p = b n
          rw [Category.assoc, hs, hb]))
      (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))) :
    ∃ s' : F ⟶ (Functor.const ℕ).obj E,
      s'.app 0 = s 0 ∧
      ∀ n, ∃ h : s'.app n ≫ p = b n,
        RightHomotopyRel
          (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s n) (hs n))
          (Over.homMk (U := Over.mk (b n)) (V := Over.mk p) (s'.app n) h) := by
  obtain ⟨s', hs₀, hsbase, hcompat⟩ :=
    exists_compatible_fibration_maps F p b s hs hobjects hcof hb hstep
  let c : F ⟶ (Functor.const ℕ).obj E := NatTrans.ofSequence s' (by
    intro n
    change F.map (homOfLE (Nat.le_succ n)) ≫ s' (n + 1) =
      s' n ≫ ((Functor.const ℕ).obj E).map (homOfLE (Nat.le_succ n))
    rw [Functor.const_obj_map]
    exact (hcompat n).trans ((Category.comp_id (s' n)).symm))
  exact ⟨c, hs₀, hsbase⟩

end HomotopicalAlgebra

end

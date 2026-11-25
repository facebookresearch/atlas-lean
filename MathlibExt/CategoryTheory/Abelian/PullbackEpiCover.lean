/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback squares descend through an epi cover

In an abelian category, a square is a pullback if its base change along an
epimorphism onto the lower left object is a pullback. Commutativity and joint
monicity of the original projections follow from the covered pullback square.
The descended lift retains both original projections.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullbackEpiCoverJointZero {A X Y Z T W : C}
    (a : A ⟶ X) (b : A ⟶ Y) (i : X ⟶ Z) (d : Y ⟶ Z) (q : T ⟶ Y)
    (h : IsPullback (pullback.fst b q ≫ a) (pullback.snd b q) i (q ≫ d))
    (u : W ⟶ A) (huA : u ≫ a = 0) (huB : u ≫ b = 0) : u = 0 := by
  have huq : u ≫ b = (0 : W ⟶ T) ≫ q :=
    huB.trans (show (0 : W ⟶ T) ≫ q = 0 from zero_comp).symm
  let v := pullback.lift u (0 : W ⟶ T) huq
  have hv : v = 0 := h.hom_ext
    (by
      calc
        v ≫ (pullback.fst b q ≫ a) = (v ≫ pullback.fst b q) ≫ a :=
          (Category.assoc _ _ _).symm
        _ = u ≫ a := congrArg (fun f => f ≫ a) (pullback.lift_fst u 0 huq)
        _ = 0 := huA
        _ = (0 : W ⟶ pullback b q) ≫ (pullback.fst b q ≫ a) := zero_comp.symm)
    ((pullback.lift_snd u (0 : W ⟶ T) huq).trans
      (show (0 : W ⟶ pullback b q) ≫ pullback.snd b q = 0 from zero_comp).symm)
  calc
    u = v ≫ pullback.fst b q := (pullback.lift_fst u 0 huq).symm
    _ = (0 : W ⟶ pullback b q) ≫ pullback.fst b q :=
      congrArg (fun f => f ≫ pullback.fst b q) hv
    _ = 0 := zero_comp

private def pullbackEpiCoverLift {A X Y Z T : C}
    (a : A ⟶ X) (b : A ⟶ Y) (i : X ⟶ Z) (d : Y ⟶ Z) (q : T ⟶ Y)
    [Epi q]
    (h : IsPullback (pullback.fst b q ≫ a) (pullback.snd b q) i (q ≫ d))
    (s : PullbackCone i d) :
    { m : s.pt ⟶ A // m ≫ a = s.fst ∧ m ≫ b = s.snd } := by
  let V := pullback s.snd q
  let l : V ⟶ s.pt := pullback.fst s.snd q
  let c : V ⟶ X := l ≫ s.fst
  let t : V ⟶ T := pullback.snd s.snd q
  have hw : c ≫ i = t ≫ (q ≫ d) := by
    calc
      (l ≫ s.fst) ≫ i = l ≫ (s.fst ≫ i) := Category.assoc _ _ _
      _ = l ≫ (s.snd ≫ d) := congrArg (fun f => l ≫ f) s.condition
      _ = (t ≫ q) ≫ d := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ d) pullback.condition)
      _ = t ≫ (q ≫ d) := Category.assoc _ _ _
  let z := h.lift c t hw
  let m := z ≫ pullback.fst b q
  have hmA : m ≫ a = l ≫ s.fst := by
    exact (Category.assoc _ _ _).trans (h.lift_fst c t hw)
  have hmB : m ≫ b = l ≫ s.snd := by
    calc
      (z ≫ pullback.fst b q) ≫ b = z ≫ (pullback.snd b q ≫ q) :=
        (Category.assoc _ _ _).trans (congrArg (fun f => z ≫ f) pullback.condition)
      _ = t ≫ q := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ q) (h.lift_snd c t hw))
      _ = l ≫ s.snd := pullback.condition.symm
  letI : Epi l := inferInstance
  have hKill : kernel.ι l ≫ m = 0 := by
    apply pullbackEpiCoverJointZero a b i d q h
    · calc
        (kernel.ι l ≫ m) ≫ a = kernel.ι l ≫ (m ≫ a) := Category.assoc _ _ _
        _ = kernel.ι l ≫ (l ≫ s.fst) := congrArg (fun f => kernel.ι l ≫ f) hmA
        _ = (kernel.ι l ≫ l) ≫ s.fst := (Category.assoc _ _ _).symm
        _ = (0 : kernel l ⟶ s.pt) ≫ s.fst :=
          congrArg (fun f => f ≫ s.fst) (kernel.condition l)
        _ = 0 := zero_comp
    · calc
        (kernel.ι l ≫ m) ≫ b = kernel.ι l ≫ (m ≫ b) := Category.assoc _ _ _
        _ = kernel.ι l ≫ (l ≫ s.snd) := congrArg (fun f => kernel.ι l ≫ f) hmB
        _ = (kernel.ι l ≫ l) ≫ s.snd := (Category.assoc _ _ _).symm
        _ = (0 : kernel l ⟶ s.pt) ≫ s.snd :=
          congrArg (fun f => f ≫ s.snd) (kernel.condition l)
        _ = 0 := zero_comp
  let f := Abelian.epiDesc l m hKill
  have hlf : l ≫ f = m := Abelian.comp_epiDesc l m hKill
  have hfA : f ≫ a = s.fst := by
    apply (cancel_epi l).1
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ a) hlf).trans hmA))
  have hfB : f ≫ b = s.snd := by
    apply (cancel_epi l).1
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ b) hlf).trans hmB))
  exact ⟨f, hfA, hfB⟩

/-- An epi cover of the lower left object detects a pullback square in an
abelian category. The covered square also forces the commutativity. -/
theorem isPullback_of_epi_cover {A X Y Z T : C}
    (a : A ⟶ X) (b : A ⟶ Y) (i : X ⟶ Z) (d : Y ⟶ Z) (q : T ⟶ Y)
    [Epi q]
    (h : IsPullback (pullback.fst b q ≫ a) (pullback.snd b q) i (q ≫ d)) :
    IsPullback a b i d := by
  have w : a ≫ i = b ≫ d := by
    apply (cancel_epi (pullback.fst b q)).1
    calc
      pullback.fst b q ≫ (a ≫ i) = (pullback.fst b q ≫ a) ≫ i :=
        (Category.assoc _ _ _).symm
      _ = pullback.snd b q ≫ (q ≫ d) := h.w
      _ = (pullback.snd b q ≫ q) ≫ d := (Category.assoc _ _ _).symm
      _ = (pullback.fst b q ≫ b) ≫ d :=
        congrArg (fun f => f ≫ d) pullback.condition.symm
      _ = pullback.fst b q ≫ (b ≫ d) := Category.assoc _ _ _
  exact ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w
    (fun s => (pullbackEpiCoverLift a b i d q h s).1)
    (fun s => (pullbackEpiCoverLift a b i d q h s).2.1)
    (fun s => (pullbackEpiCoverLift a b i d q h s).2.2) (by
      intro s f hf hg
      apply sub_eq_zero.mp
      apply pullbackEpiCoverJointZero a b i d q h
      · simp only [Preadditive.sub_comp, hf,
          (pullbackEpiCoverLift a b i d q h s).2.1, sub_self]
      · simp only [Preadditive.sub_comp, hg,
          (pullbackEpiCoverLift a b i d q h s).2.2, sub_self])⟩⟩

end CategoryTheory.Limits

end

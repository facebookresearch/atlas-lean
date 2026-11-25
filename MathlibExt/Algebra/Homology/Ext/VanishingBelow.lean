/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Bounded Ext vanishing

This file packages the statement that low-degree Ext groups vanish below a
natural-number bound.  It also proves the kernel direction of the depth lemma
for a short exact sequence, directly from the covariant Ext long exact
sequence.

No numerical depth or ring-theoretic assumptions are introduced here.

## Main declarations

* `CategoryTheory.Abelian.Ext.VanishesBelow`
* `CategoryTheory.Abelian.Ext.VanishesBelow.mono`
* `CategoryTheory.Abelian.Ext.vanishesBelow_zero`
* `CategoryTheory.Abelian.Ext.VanishesBelow.of_shortExact_X₁`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian

universe u v t

namespace CategoryTheory.Abelian.Ext

/-- The Ext groups from `X` to `Y` vanish in every natural degree strictly
below `n`. -/
def VanishesBelow
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    (X Y : C) (n : ℕ) : Prop :=
  ∀ i : ℕ, i < n → Subsingleton (Ext.{t} X Y i)

/-- Vanishing below a bound implies vanishing below every smaller bound. -/
theorem VanishesBelow.mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    {X Y : C} {m n : ℕ}
    (h : VanishesBelow X Y n) (hmn : m ≤ n) :
    VanishesBelow X Y m :=
  fun i hi ↦ h i (hi.trans_le hmn)

/-- Ext vanishing below degree zero is vacuous. -/
@[simp]
theorem vanishesBelow_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    (X Y : C) :
    VanishesBelow X Y 0 := by
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

/-- The kernel direction of the depth lemma, expressed as bounded Ext
vanishing.

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, vanishing of
`Ext A X₂` below `n + 1` and of `Ext A X₃` below `n` implies vanishing of
`Ext A X₁` below `n + 1`. -/
theorem VanishesBelow.of_shortExact_X₁
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (A : C) (n : ℕ)
    (h₂ : VanishesBelow A S.X₂ (n + 1))
    (h₃ : VanishesBelow A S.X₃ n) :
    VanishesBelow A S.X₁ (n + 1) := by
  intro i hi
  obtain rfl | i := i
  · let _ : Mono S.f := hS.mono_f
    let _ : Subsingleton (Ext.{t} A S.X₂ 0) :=
      h₂ 0 (Nat.zero_lt_succ n)
    exact (Ext.postcomp_mk₀_injective_of_mono A S.f).subsingleton
  · apply subsingleton_of_forall_eq 0
    intro x
    let _ : Subsingleton (Ext.{t} A S.X₂ (i + 1)) :=
      h₂ (i + 1) hi
    let _ : Subsingleton (Ext.{t} A S.X₃ i) :=
      h₃ i (Nat.lt_of_succ_lt_succ hi)
    have hx : x.comp (Ext.mk₀ S.f) (add_zero (i + 1)) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x₃, hx₃⟩ :=
      Ext.covariant_sequence_exact₁ A hS x hx (n₀ := i) rfl
    rw [← hx₃, Subsingleton.elim x₃ 0, Ext.zero_comp]

end CategoryTheory.Abelian.Ext

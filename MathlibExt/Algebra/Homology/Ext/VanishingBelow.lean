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
# Low-degree Ext vanishing and the kernel depth lemma

In an abelian category with Ext groups in a chosen universe, `Ext.VanishesBelow X Y n` means
`Ext^i(X,Y) = 0` for every natural `i < n`. The condition includes degree zero and weakens
when the bound decreases.

For a short exact sequence `0 → S₁ → S₂ → S₃ → 0`, vanishing of `Ext(A,S₂)` below `n + 1` and
`Ext(A,S₃)` below `n` implies vanishing of `Ext(A,S₁)` below `n + 1`. This is the kernel
direction of the covariant Ext depth lemma.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian

universe u v t

namespace CategoryTheory.Abelian.Ext

/-- Ext vanishing below a natural-degree bound.

For objects `X`, `Y` in an abelian category with `HasExt.{t}`, require `Subsingleton (Ext.{t}
X Y i)` for every natural `i < n`. Thus every such Ext group is zero. -/
def VanishesBelow
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    (X Y : C) (n : ℕ) : Prop :=
  ∀ i : ℕ, i < n → Subsingleton (Ext.{t} X Y i)

/-- Ext vanishing persists when the bound decreases.

If `Ext(X,Y)` vanishes below `n` and `m ≤ n`, then it vanishes below `m`. -/
theorem VanishesBelow.mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    {X Y : C} {m n : ℕ}
    (h : VanishesBelow X Y n) (hmn : m ≤ n) :
    VanishesBelow X Y m :=
  fun i hi ↦ h i (hi.trans_le hmn)

/-- Ext vanishing below zero is vacuous.

Every pair of objects satisfies `VanishesBelow X Y 0`, since no natural degree is less than
zero. -/
@[simp]
theorem vanishesBelow_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]
    (X Y : C) :
    VanishesBelow X Y 0 := by
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

/-- Kernel Ext vanishing from adjacent bounds in a short exact sequence.

For a short exact sequence and fixed probe `A`, if `Ext(A,S.X₂)` vanishes below `n + 1` and
`Ext(A,S.X₃)` below `n`, then `Ext(A,S.X₁)` vanishes below `n + 1`. -/
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

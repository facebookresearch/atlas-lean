/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Factorization and lifting classes

An equality with a left lifting class supplies coproduct and transfinite
composition closure at an independent size universe. An explicit weak
factorization system supplies that equality through its left-class field.

Factorization and cancellation also identify the intersection of an auxiliary
class with a derived right lifting class.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Suppose every morphism factors through `L` and then `R`, and `R = L.rlp`.
If `R ≤ W` and `W` admits cancellation of a following `R`-morphism, the
intersection of `(L ⊓ W).rlp` with `W` is `R`.

This abstracts the argument of Joyal, *The Theory of Quasi-Categories and its
Applications* (2008), Theorem 6.4. -/
theorem rlp_inf_inf_eq_of_hasFactorization
    (L R W : MorphismProperty C) [HasFactorization L R]
    [W.HasOfPostcompProperty R] (hR : L.rlp = R) (hRW : R ≤ W) :
    (L ⊓ W).rlp ⊓ W = R := by
  apply le_antisymm
  · intro X Y f hf
    obtain ⟨hf, hW⟩ := hf
    let d := factorizationData L R f
    have hiW : W d.i := W.of_postcomp d.i d.p d.hp (d.fac.symm ▸ hW)
    have : HasLiftingProperty d.i f := hf d.i ⟨d.hi, hiW⟩
    rw [← hR]
    exact of_retract (P := L.rlp) (RetractArrow.ofRightLiftingProperty d.fac)
      (hR.symm ▸ d.hp)
  · intro X Y f hf
    exact ⟨(antitone_rlp (inf_le_left : L ⊓ W ≤ L)) f (hR.symm ▸ hf), hRW f hf⟩

/-- The weak part of the derived right lifting class for an explicit weak
factorization system, with cancellation relative to its right class. -/
theorem IsWeakFactorizationSystem.rlp_inf_inf_eq
    (L R W : MorphismProperty C) (h : IsWeakFactorizationSystem L R)
    [W.HasOfPostcompProperty R] (hRW : R ≤ W) :
    (L ⊓ W).rlp ⊓ W = R := by
  have : HasFactorization L R := h.hasFactorization
  exact rlp_inf_inf_eq_of_hasFactorization L R W h.rlp hRW

/-- A class equal to a left lifting class is closed under coproducts at an
independent size universe. -/
theorem IsStableUnderCoproducts.of_llp_eq
    (L R : MorphismProperty C) (h : R.llp = L) :
    L.IsStableUnderCoproducts.{w} := by
  rw [← h]
  infer_instance

/-- A class equal to a left lifting class is closed under transfinite
compositions at an independent size universe. -/
theorem IsStableUnderTransfiniteComposition.of_llp_eq
    (L R : MorphismProperty C) (h : R.llp = L) :
    L.IsStableUnderTransfiniteComposition.{w} := by
  rw [← h]
  infer_instance

/-- The left class of an explicit weak factorization system has global
coproduct closure at an independent size universe. -/
theorem IsWeakFactorizationSystem.isStableUnderCoproducts
    (L R : MorphismProperty C) (h : IsWeakFactorizationSystem L R) :
    L.IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq L R h.llp

/-- The left class of an explicit weak factorization system has global
transfinite composition closure at an independent size universe. -/
theorem IsWeakFactorizationSystem.isStableUnderTransfiniteComposition
    (L R : MorphismProperty C) (h : IsWeakFactorizationSystem L R) :
    L.IsStableUnderTransfiniteComposition.{w} :=
  IsStableUnderTransfiniteComposition.of_llp_eq L R h.llp

end CategoryTheory.MorphismProperty

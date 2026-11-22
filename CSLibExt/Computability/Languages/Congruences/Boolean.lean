/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Recognition
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Prod

/-!
# Syntactic monoids and Boolean operations

Complement does not change syntactic indistinguishability.  Intersections and unions are
recognized by the product of recognizers, so their syntactic monoids are quotients of a submonoid
of the product.  These facts give the algebraic closure of finite syntactic monoids under the
Boolean language operations.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v w

variable {Symbol : Type u}

/-- Complementing a language preserves its syntactic relation. -/
theorem syntacticRel_compl_iff (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticRel Lᶜ x y ↔ syntacticRel L x y := by
  classical
  constructor <;> intro h u v
  · constructor
    · intro hx
      by_contra hy
      exact (h u v).mpr hy hx
    · intro hy
      by_contra hx
      exact (h u v).mp hx hy
  · exact not_congr (h u v)

theorem syntacticRel_compl (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticRel Lᶜ x y = syntacticRel L x y :=
  propext (syntacticRel_compl_iff L x y)

/-- Complementing a language leaves its syntactic congruence unchanged. -/
theorem syntacticCon_compl (L : Language Symbol) : syntacticCon Lᶜ = syntacticCon L := by
  apply Con.ext
  exact syntacticRel_compl_iff L

/-- The syntactic monoids of a language and its complement are canonically equivalent. -/
def syntacticMonoidComplEquiv (L : Language Symbol) : SyntacticMonoid Lᶜ ≃* SyntacticMonoid L :=
  Con.congr (MulEquiv.refl _) <| by
    simpa using syntacticCon_compl L

@[simp]
theorem syntacticMonoidComplEquiv_morphism (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMonoidComplEquiv L (syntacticMorphism Lᶜ x) = syntacticMorphism L x :=
  rfl

/-- Finite syntactic monoids are closed under language complement. -/
theorem finite_syntacticMonoid_compl_iff (L : Language Symbol) :
    Finite (SyntacticMonoid Lᶜ) ↔ Finite (SyntacticMonoid L) := by
  constructor
  · intro _
    exact Finite.of_injective (syntacticMonoidComplEquiv L).symm
      (syntacticMonoidComplEquiv L).symm.injective
  · intro _
    exact Finite.of_injective (syntacticMonoidComplEquiv L)
      (syntacticMonoidComplEquiv L).injective

/-- Syntactic equivalence for each operand implies syntactic equivalence for their intersection. -/
theorem syntacticRel_inter {L K : Language Symbol} {x y : FreeMonoid Symbol}
    (hL : syntacticRel L x y) (hK : syntacticRel K x y) : syntacticRel (L ⊓ K) x y := by
  intro u v
  rw [Language.mem_inf, Language.mem_inf]
  exact and_congr (hL u v) (hK u v)

/-- Syntactic equivalence for each operand implies syntactic equivalence for their union. -/
theorem syntacticRel_union {L K : Language Symbol} {x y : FreeMonoid Symbol}
    (hL : syntacticRel L x y) (hK : syntacticRel K x y) : syntacticRel (L ⊔ K) x y := by
  intro u v
  change (_ ∈ L ∨ _ ∈ K) ↔ (_ ∈ L ∨ _ ∈ K)
  exact or_congr (hL u v) (hK u v)

/-- Syntactic equivalence for each operand implies syntactic equivalence for their difference. -/
theorem syntacticRel_diff {L K : Language Symbol} {x y : FreeMonoid Symbol}
    (hL : syntacticRel L x y) (hK : syntacticRel K x y) : syntacticRel (L - K) x y := by
  intro u v
  rw [Language.mem_sub, Language.mem_sub]
  exact and_congr (hL u v) (not_congr (hK u v))

/-- The common refinement of two syntactic congruences refines the congruence of the
intersection. -/
theorem syntacticCon_inf_le_inter (L K : Language Symbol) :
    syntacticCon L ⊓ syntacticCon K ≤ syntacticCon (L ⊓ K) := by
  intro x y h
  exact syntacticRel_inter h.1 h.2

/-- The common refinement of two syntactic congruences refines the congruence of the union. -/
theorem syntacticCon_inf_le_union (L K : Language Symbol) :
    syntacticCon L ⊓ syntacticCon K ≤ syntacticCon (L ⊔ K) := by
  intro x y h
  exact syntacticRel_union h.1 h.2

/-- The common refinement of two syntactic congruences refines the congruence of the
difference. -/
theorem syntacticCon_inf_le_diff (L K : Language Symbol) :
    syntacticCon L ⊓ syntacticCon K ≤ syntacticCon (L - K) := by
  intro x y h
  exact syntacticRel_diff h.1 h.2

/-- The product of recognizers recognizes the intersection using the product accepting set. -/
theorem Recognizes.inter {Carrier₁ : Type v} {Carrier₂ : Type w}
    [Monoid Carrier₁] [Monoid Carrier₂]
    {L K : Language Symbol} {left : FreeMonoid Symbol →* Carrier₁}
    {right : FreeMonoid Symbol →* Carrier₂} {acceptL : Set Carrier₁}
    {acceptK : Set Carrier₂} (hL : Recognizes L left acceptL)
    (hK : Recognizes K right acceptK) :
    Recognizes (L ⊓ K) (left.prod right)
      {p | p.1 ∈ acceptL ∧ p.2 ∈ acceptK} := by
  intro x
  rw [Language.mem_inf]
  change (_ ∈ L ∧ _ ∈ K) ↔ left x ∈ acceptL ∧ right x ∈ acceptK
  exact and_congr (hL x) (hK x)

/-- The product of recognizers recognizes the union. -/
theorem Recognizes.union {Carrier₁ : Type v} {Carrier₂ : Type w}
    [Monoid Carrier₁] [Monoid Carrier₂]
    {L K : Language Symbol} {left : FreeMonoid Symbol →* Carrier₁}
    {right : FreeMonoid Symbol →* Carrier₂} {acceptL : Set Carrier₁}
    {acceptK : Set Carrier₂} (hL : Recognizes L left acceptL)
    (hK : Recognizes K right acceptK) :
    Recognizes (L ⊔ K) (left.prod right)
      {p | p.1 ∈ acceptL ∨ p.2 ∈ acceptK} := by
  intro x
  change (_ ∈ L ∨ _ ∈ K) ↔ left x ∈ acceptL ∨ right x ∈ acceptK
  exact or_congr (hL x) (hK x)

/-- The product of recognizers recognizes language difference. -/
theorem Recognizes.diff {Carrier₁ : Type v} {Carrier₂ : Type w}
    [Monoid Carrier₁] [Monoid Carrier₂]
    {L K : Language Symbol} {left : FreeMonoid Symbol →* Carrier₁}
    {right : FreeMonoid Symbol →* Carrier₂} {acceptL : Set Carrier₁}
    {acceptK : Set Carrier₂} (hL : Recognizes L left acceptL)
    (hK : Recognizes K right acceptK) :
    Recognizes (L - K) (left.prod right)
      {p | p.1 ∈ acceptL ∧ p.2 ∉ acceptK} := by
  intro x
  rw [Language.mem_sub]
  change (_ ∈ L ∧ _ ∉ K) ↔ left x ∈ acceptL ∧ right x ∉ acceptK
  exact and_congr (hL x) (not_congr (hK x))

/-- If both operand syntactic monoids are finite, the intersection's syntactic monoid is
finite. -/
theorem finite_syntacticMonoid_inter (L K : Language Symbol)
    [Finite (SyntacticMonoid L)] [Finite (SyntacticMonoid K)] :
    Finite (SyntacticMonoid (L ⊓ K)) :=
  finite_syntacticMonoid_of_recognizer
    ((syntacticMorphism L).prod (syntacticMorphism K))
    {p | p.1 ∈ syntacticAccept L ∧ p.2 ∈ syntacticAccept K}
    ((recognizes_syntacticMorphism L).inter (recognizes_syntacticMorphism K))

/-- If both operand syntactic monoids are finite, the union's syntactic monoid is finite. -/
theorem finite_syntacticMonoid_union (L K : Language Symbol)
    [Finite (SyntacticMonoid L)] [Finite (SyntacticMonoid K)] :
    Finite (SyntacticMonoid (L ⊔ K)) :=
  finite_syntacticMonoid_of_recognizer
    ((syntacticMorphism L).prod (syntacticMorphism K))
    {p | p.1 ∈ syntacticAccept L ∨ p.2 ∈ syntacticAccept K}
    ((recognizes_syntacticMorphism L).union (recognizes_syntacticMorphism K))

/-- If both operand syntactic monoids are finite, the difference's syntactic monoid is finite. -/
theorem finite_syntacticMonoid_diff (L K : Language Symbol)
    [Finite (SyntacticMonoid L)] [Finite (SyntacticMonoid K)] :
    Finite (SyntacticMonoid (L - K)) :=
  finite_syntacticMonoid_of_recognizer
    ((syntacticMorphism L).prod (syntacticMorphism K))
    {p | p.1 ∈ syntacticAccept L ∧ p.2 ∉ syntacticAccept K}
    ((recognizes_syntacticMorphism L).diff (recognizes_syntacticMorphism K))

end Cslib.Language

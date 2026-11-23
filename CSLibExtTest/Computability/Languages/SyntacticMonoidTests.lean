/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `1184e99236ece3db95d28d07b55998ccaebeec53`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Boolean
public import CSLibExt.Computability.Languages.Congruences.CslibBridge

/-! # Tests for syntactic congruences, monoids, and algebraic recognition -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.SyntacticMonoidTests

/-- The two-state automaton that records whether the most recently read bit is true. -/
def lastBitDFA : DFA Bool Bool where
  step _ a := a
  start := false
  accept := {true}

theorem lastBitDFA_accessible : Accessible lastBitDFA := by
  intro q
  cases q with
  | false => exact ⟨[], rfl⟩
  | true => exact ⟨[true], rfl⟩

theorem lastBitDFA_stateSeparated : StateSeparated lastBitDFA := by
  intro p q hpq
  cases p <;> cases q
  · rfl
  · exfalso
    have h := Set.ext_iff.mp hpq []
    change (false ∈ ({true} : Set Bool) ↔ true ∈ ({true} : Set Bool)) at h
    simp at h
  · exfalso
    have h := Set.ext_iff.mp hpq []
    change (true ∈ ({true} : Set Bool) ↔ false ∈ ({true} : Set Bool)) at h
    simp at h
  · rfl

example (x y : FreeMonoid Bool) :
    syntacticRel lastBitDFA.accepts x y ↔
      transitionAction lastBitDFA x = transitionAction lastBitDFA y :=
  syntacticRel_iff_transitionAction_eq lastBitDFA lastBitDFA_accessible
    lastBitDFA_stateSeparated x y

example : syntacticCon lastBitDFA.accepts = Con.ker (transitionMorphism lastBitDFA) :=
  syntacticCon_eq_transitionMorphism_ker lastBitDFA lastBitDFA_accessible
    lastBitDFA_stateSeparated

example : Function.Injective
    (syntacticActionHom lastBitDFA lastBitDFA_accessible lastBitDFA_stateSeparated) :=
  syntacticActionHom_injective lastBitDFA lastBitDFA_accessible lastBitDFA_stateSeparated

example : Finite (SyntacticMonoid lastBitDFA.accepts) :=
  finite_syntacticMonoid_of_finite_dfa lastBitDFA

example (x : List Bool) :
    (syntacticDFA lastBitDFA.accepts).eval x =
      syntacticMorphism lastBitDFA.accepts (FreeMonoid.ofList x) :=
  syntacticDFA_eval lastBitDFA.accepts x

example : (syntacticDFA lastBitDFA.accepts).accepts = lastBitDFA.accepts :=
  syntacticDFA_accepts lastBitDFA.accepts

example : Accessible (syntacticDFA lastBitDFA.accepts) :=
  syntacticDFA_accessible lastBitDFA.accepts

example (L : Language Bool) (x y : FreeMonoid Bool) :
    syntacticRel Lᶜ x y ↔ syntacticRel L x y :=
  syntacticRel_compl_iff L x y

example (L K : Language Bool) [Finite (SyntacticMonoid L)]
    [Finite (SyntacticMonoid K)] : Finite (SyntacticMonoid (L ⊓ K)) :=
  finite_syntacticMonoid_inter L K

example (L K : Language Bool) [Finite (SyntacticMonoid L)]
    [Finite (SyntacticMonoid K)] : Finite (SyntacticMonoid (L ⊔ K)) :=
  finite_syntacticMonoid_union L K

example (L K : Language Bool) [Finite (SyntacticMonoid L)]
    [Finite (SyntacticMonoid K)] : Finite (SyntacticMonoid (L - K)) :=
  finite_syntacticMonoid_diff L K

example (L : Language Bool) [Finite (SyntacticMonoid L)] : L.IsRegular :=
  isRegular_of_finite_syntacticMonoid L

example (L : Language Bool) (x : FreeMonoid Bool) :
    FreeMonoid.toList x ∈ L ↔ syntacticMorphism L x ∈ syntacticAccept L :=
  mem_iff_syntacticMorphism_mem L x

example (L : Language Bool) (w : FreeMonoid Bool) :
    SyntacticMonoid.toCslib L (syntacticMorphism L w) =
      _root_.Language.homSyntacticMonoid L w := by
  simp

example (L : Language Bool) (x y : SyntacticMonoid L) :
    SyntacticMonoid.toCslib L (x * y) =
      SyntacticMonoid.toCslib L x * SyntacticMonoid.toCslib L y :=
  map_mul (SyntacticMonoid.toCslib L) x y

example : syntacticMorphism lastBitDFA.accepts (FreeMonoid.ofList []) ≠
    syntacticMorphism lastBitDFA.accepts (FreeMonoid.ofList [false]) := by
  intro heq
  have hctx := (syntacticMorphism_eq_iff lastBitDFA.accepts _ _).mp heq
  have h := hctx (FreeMonoid.ofList [true]) 1
  change (true ∈ ({true} : Set Bool) ↔ false ∈ ({true} : Set Bool)) at h
  simp at h

example (L : Language Bool) : L.IsRegular ↔ Finite (SyntacticMonoid L) :=
  (_root_.Language.IsRegular.iff_finite_syntacticMonoid L).trans
    (SyntacticMonoid.toCslib L).toEquiv.finite_iff.symm

example (L : Language Bool) (w : FreeMonoid Bool) :
    (SyntacticMonoid.toCslib L).symm (_root_.Language.homSyntacticMonoid L w) =
      syntacticMorphism L w := by
  simp

#print axioms syntacticCon_eq_cslib
#print axioms SyntacticMonoid.toCslib

end Cslib.Language.SyntacticMonoidTests

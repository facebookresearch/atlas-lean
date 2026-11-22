/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.SyntacticMinimal
public import CSLibExt.Computability.Languages.Congruences.TransitionMinimal

/-! # Client tests for syntactic transition monoids of minimal DFAs -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.SyntacticMinimalTests

/-- Mathlib's residual DFA for a concrete language is accessible and
state-separated. -/
example : Accessible (({[true]} : Language Bool).toDFA) :=
  toDFA_accessible _

example : StateSeparated (({[true]} : Language Bool).toDFA) :=
  toDFA_stateSeparated _

/-- The minimized presentation of a concrete DFA is state-separated. -/
example : StateSeparated (minimizedDFA (({[true]} : Language Bool).toDFA)) :=
  minimizedDFA_stateSeparated _

/-- The upstream canonical automaton for a concrete language is accessible and
state-separated. -/
example : Accessible (Cslib.Automata.DA.FinAcc.toDFA (({[true]} : Language Bool).NerodeCongruenceDA)) :=
  nerodeCongruenceDA_accessible _

example : StateSeparated (Cslib.Automata.DA.FinAcc.toDFA (({[true]} : Language Bool).NerodeCongruenceDA)) :=
  nerodeCongruenceDA_stateSeparated _

/-- The direct transition homomorphism sends the syntactic class of a word to its
transition monoid element. -/
example (x : FreeMonoid Bool) :
    syntacticToTransitionMonoid (({[true]} : Language Bool).toDFA) (toDFA_accessible _)
        (toDFA_stateSeparated _)
        (syntacticMorphism (({[true]} : Language Bool).toDFA).accepts x) =
      toTransitionMonoid (({[true]} : Language Bool).toDFA) x :=
  syntacticToTransitionMonoid_morphism _ _ _ x

/-- The direct transition equivalence sends the syntactic class of a word to its
transition monoid element. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidEquivTransitionMonoid (({[true]} : Language Bool).toDFA)
        (toDFA_accessible _) (toDFA_stateSeparated _)
        (syntacticMorphism (({[true]} : Language Bool).toDFA).accepts x) =
      toTransitionMonoid (({[true]} : Language Bool).toDFA) x :=
  syntacticMonoidEquivTransitionMonoid_morphism _ _ _ x

/-- The direct transition equivalence agrees with the transition homomorphism,
by `rfl`. -/
example (q : SyntacticMonoid (({[true]} : Language Bool).toDFA).accepts) :
    syntacticMonoidEquivTransitionMonoid (({[true]} : Language Bool).toDFA)
        (toDFA_accessible _) (toDFA_stateSeparated _) q =
      syntacticToTransitionMonoid (({[true]} : Language Bool).toDFA)
        (toDFA_accessible _) (toDFA_stateSeparated _) q :=
  rfl

/-- The direct transition homomorphism is injective on syntactic classes. -/
example : Function.Injective
    (syntacticToTransitionMonoid (({[true]} : Language Bool).toDFA)
      (toDFA_accessible _) (toDFA_stateSeparated _)) :=
  syntacticToTransitionMonoid_injective _ _ _

/-- Transporting the direct equivalence along the `accepts` equality sends the
syntactic class of a word to the same transition monoid element, directly. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidEquivTransport (Language.accepts_toDFA (L := ({[true]} : Language Bool)))
        (syntacticMonoidEquivTransitionMonoid (({[true]} : Language Bool).toDFA)
          (toDFA_accessible _) (toDFA_stateSeparated _))
        (x : SyntacticMonoid (({[true]} : Language Bool))) =
      syntacticMonoidEquivTransitionMonoid (({[true]} : Language Bool).toDFA)
        (toDFA_accessible _) (toDFA_stateSeparated _)
        (x : SyntacticMonoid (({[true]} : Language Bool).toDFA).accepts) :=
  syntacticMonoidEquivTransport_morphism _ _ _

/-- The canonical isomorphism for `L.toDFA` sends the syntactic class of a word
to the transition monoid element of that word, through the `simp` morphism rule. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidEquivTransitionMonoidToDFA ({[true]} : Language Bool)
        (x : SyntacticMonoid ({[true]} : Language Bool)) =
      toTransitionMonoid (({[true]} : Language Bool).toDFA) x := by
  simp

/-- The canonical isomorphism for the minimized presentation sends the syntactic
class of a word to the transition monoid element of that word, through the
`simp` morphism rule. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidEquivTransitionMonoidMinimizedDFA (({[true]} : Language Bool).toDFA)
        (x : SyntacticMonoid (({[true]} : Language Bool).toDFA).accepts) =
      toTransitionMonoid (minimizedDFA (({[true]} : Language Bool).toDFA)) x := by
  simp

/-- The canonical isomorphism for the upstream canonical automaton sends the
syntactic class of a word to the transition monoid element of that word,
through the `simp` morphism rule. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA ({[true]} : Language Bool)
        (x : SyntacticMonoid ({[true]} : Language Bool)) =
      toTransitionMonoid
        (Cslib.Automata.DA.FinAcc.toDFA (({[true]} : Language Bool).NerodeCongruenceDA)) x := by
  simp

#print axioms syntacticToTransitionMonoid
#print axioms syntacticMonoidEquivTransport_morphism
#print axioms syntacticMonoidEquivTransitionMonoidToDFA_morphism
#print axioms syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism
#print axioms syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA_morphism

end Cslib.Language.SyntacticMinimalTests

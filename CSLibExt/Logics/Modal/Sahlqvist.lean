/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sahlqvist formulas
-/
module

public import CSLibExt.Logics.Modal.Kripke
public import Mathlib.Data.Set.Insert

/-!
# Sahlqvist formulas

The Sahlqvist class of modal formulas: a Sahlqvist implication is an implication
`α → β` whose antecedent `α` is a Sahlqvist antecedent and whose consequent `β` is
positive, and a Sahlqvist formula is built from Sahlqvist implications using `∧`,
`□`, and `∨` with disjoint propositional vocabularies. `◇` belongs to the antecedent
grammar, not to the outer closure: arbitrary outer `◇` or arbitrary `∨` would leave
the correspondence class. Sahlqvist antecedents are built from boxed atoms
(`□^k p`, allowing `k = 0`) and negative formulas using `∧`, `∨`, and `◇`;
positive and negative formulas are defined by simultaneous recursion on the
primitive constructors (`atom`, `bot`, `imp`, `box`), with the derived
connectives (`neg`, `and`, `or`, `dia`) unfolding to primitive form. Every
Sahlqvist formula has a first-order frame correspondent; that correspondence
theorem is stated as `WantedExt` in
`WantedExt/TheoryOfComputation/SahlqvistCorrespondenceWanted.lean`.

## References

- H. Sahlqvist, *Completeness and Correspondence in the First and Second Order Semantics
  for Modal Logic*, in *Proceedings of the Third Scandinavian Logic Symposium*, North-Holland,
  1975, 110-143.
- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001, §3.6
  (Sahlqvist formulas and correspondence).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Modal

variable {Atom : Type u}

mutual

/-- **Positive modal formulas.** Positive and negative modal formulas are defined by simultaneous
recursion: every atom is positive, $\bot$ is positive, $\varphi \to \psi$ is positive if
$\varphi$ is negative and $\psi$ is positive, and $\Box\varphi$ is positive if $\varphi$ is
positive.

Positive formulas are closed under $\wedge$, $\vee$, $\Box$ and $\Diamond$, which are encoded
through $\to$, $\bot$ and $\Box$. -/
def IsPositive : Formula Atom → Prop
  | .atom _ => True
  | .bot => True
  | .imp φ ψ => IsNegative φ ∧ IsPositive ψ
  | .box φ => IsPositive φ

/-- **Negative modal formulas.** Negative and positive modal formulas are defined by simultaneous
recursion: no atom is negative, $\bot$ is negative, $\varphi \to \psi$ is negative if $\varphi$
is positive and $\psi$ is negative, and $\Box\varphi$ is negative if $\varphi$ is negative.

Negative formulas are closed under $\wedge$, $\vee$, $\Box$ and $\Diamond$, which are encoded
through $\to$, $\bot$ and $\Box$. -/
def IsNegative : Formula Atom → Prop
  | .atom _ => False
  | .bot => True
  | .imp φ ψ => IsPositive φ ∧ IsNegative ψ
  | .box φ => IsNegative φ

end

/-- **Iterated box.** For a natural number $k$ and a modal formula $\varphi$, the iterated box
$\Box^k \varphi$ is defined by $\Box^0 \varphi = \varphi$ and
$\Box^{k+1} \varphi = \Box\,\Box^k \varphi$. -/
def boxPow : Nat → Formula Atom → Formula Atom
  | 0, φ => φ
  | k + 1, φ => .box (boxPow k φ)

/-- **Sahlqvist antecedents.** The Sahlqvist antecedents form the smallest class of modal
formulas that contains every boxed atom $\Box^k p$ (an atom $p$ under $k \ge 0$ boxes) and every
negative formula, and is closed under $\wedge$, $\vee$ and $\Diamond$. -/
inductive IsSahlqvistAntecedent : Formula Atom → Prop
  /-- A boxed atom is a Sahlqvist antecedent. -/
  | boxedAtom (a : Atom) (k : Nat) :
      IsSahlqvistAntecedent (boxPow k (.atom a))
  /-- A negative formula is a Sahlqvist antecedent. -/
  | ofNegative (φ : Formula Atom) : IsNegative φ → IsSahlqvistAntecedent φ
  /-- Sahlqvist antecedents are closed under conjunction. -/
  | and (φ ψ : Formula Atom) :
      IsSahlqvistAntecedent φ → IsSahlqvistAntecedent ψ →
        IsSahlqvistAntecedent (φ.and ψ)
  /-- Sahlqvist antecedents are closed under disjunction. -/
  | or (φ ψ : Formula Atom) :
      IsSahlqvistAntecedent φ → IsSahlqvistAntecedent ψ →
        IsSahlqvistAntecedent (φ.or ψ)
  /-- Sahlqvist antecedents are closed under possibility. -/
  | dia (φ : Formula Atom) :
      IsSahlqvistAntecedent φ → IsSahlqvistAntecedent φ.dia

/-- The set of atoms (propositional variables) occurring in a modal formula. -/
def Formula.atoms : Formula Atom → Set Atom
  | .atom a => {a}
  | .bot => ∅
  | .imp φ ψ => φ.atoms ∪ ψ.atoms
  | .box φ => φ.atoms

/-- **Sahlqvist implications.** A modal formula is a Sahlqvist implication if it is an implication
$\alpha \to \beta$ whose antecedent $\alpha$ is a Sahlqvist antecedent and whose consequent
$\beta$ is a positive formula. -/
def IsSahlqvistImplication (φ : Formula Atom) : Prop :=
  ∃ α β : Formula Atom, IsSahlqvistAntecedent α ∧ IsPositive β ∧ φ = α.imp β

/-- **Sahlqvist formulas.** The Sahlqvist formulas form the smallest class of modal formulas that
contains every Sahlqvist implication, is closed under $\wedge$ and $\Box$, and contains
$\varphi \vee \psi$ whenever $\varphi$ and $\psi$ are Sahlqvist formulas with no atom in common.

The side condition on disjunction is essential: arbitrary disjunction leaves the correspondence
class. $\Diamond$ is not part of this outer closure; it belongs to the grammar of Sahlqvist
antecedents. For example, the boxed Sahlqvist implication $\Box(p \to \Box\Diamond p)$ is a
Sahlqvist formula. -/
inductive IsSahlqvist : Formula Atom → Prop
  /-- A Sahlqvist implication is Sahlqvist. -/
  | impl {φ : Formula Atom} : IsSahlqvistImplication φ → IsSahlqvist φ
  /-- Sahlqvist formulas are closed under conjunction. -/
  | and {φ ψ : Formula Atom} :
      IsSahlqvist φ → IsSahlqvist ψ → IsSahlqvist (φ.and ψ)
  /-- Sahlqvist formulas are closed under disjunction with disjoint atoms. -/
  | or {φ ψ : Formula Atom} :
      IsSahlqvist φ → IsSahlqvist ψ → Disjoint φ.atoms ψ.atoms →
        IsSahlqvist (φ.or ψ)
  /-- Sahlqvist formulas are closed under boxing. -/
  | box {φ : Formula Atom} : IsSahlqvist φ → IsSahlqvist (.box φ)

/-- **The B axiom is a Sahlqvist formula.** For every atom $p$, the instance $p \to \Box\Diamond p$
of the B axiom is a Sahlqvist formula: its antecedent $p$ is a boxed atom with zero boxes and its
consequent $\Box\Diamond p$ is positive. -/
theorem isSahlqvist_axiomB (a : Atom) : IsSahlqvist (Formula.axiomB (.atom a)) :=
  .impl ⟨.atom a, .box (Formula.dia (.atom a)), .boxedAtom a 0,
    ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩

/-- A boxed Sahlqvist implication is Sahlqvist: `□(p → □◇p)`. This is a regression
example for the closure: the bare-implication definition would reject it, since its
top-level constructor is `□`, not `⟹`. -/
example (a : Atom) : IsSahlqvist (.box (Formula.axiomB (.atom a))) :=
  .box (isSahlqvist_axiomB a)

/-- A conjunction of Sahlqvist formulas is Sahlqvist. -/
example (a b : Atom) :
    IsSahlqvist ((Formula.axiomB (.atom a)).and (Formula.axiomB (.atom b))) :=
  .and (isSahlqvist_axiomB a) (isSahlqvist_axiomB b)

/-- A disjunction of Sahlqvist formulas with disjoint atoms is Sahlqvist:
`(p → □◇p) ∨ (q → □◇q)` with `p ≠ q`. This is a regression example for the `or`
side condition: the disjunction is admitted only because the disjuncts share no
atom; arbitrary disjunction is not in the class. -/
example (a b : Atom) (hab : a ≠ b) :
    IsSahlqvist ((Formula.axiomB (.atom a)).or (Formula.axiomB (.atom b))) :=
  .or (isSahlqvist_axiomB a) (isSahlqvist_axiomB b) (by
    show Disjoint (Formula.atoms (Formula.axiomB (.atom a)))
      (Formula.atoms (Formula.axiomB (.atom b)))
    simp only [Formula.axiomB, Formula.dia, Formula.neg, Formula.atoms,
      Set.union_self, Set.union_empty]
    exact Set.disjoint_singleton.mpr hab)

/-- A genuinely negative antecedent: `¬p` is a Sahlqvist antecedent. This is a
regression example for the `ofNegative` constructor: `¬p` is negative, so it is an
antecedent itself; the old constructor instead admitted `¬¬p` from negativity of `p`,
which is impossible since an atom is not negative. -/
example (a : Atom) : IsSahlqvistAntecedent ((Formula.atom a).neg) :=
  .ofNegative (Formula.atom a).neg ⟨trivial, trivial⟩

/-- A Sahlqvist formula with a genuinely negative antecedent: `¬p → q`. -/
example (a b : Atom) : IsSahlqvist (((Formula.atom a).neg).imp (Formula.atom b)) :=
  .impl ⟨(Formula.atom a).neg, Formula.atom b,
    .ofNegative (Formula.atom a).neg ⟨trivial, trivial⟩, trivial, rfl⟩

end Cslib.Modal

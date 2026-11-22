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

/-- A modal formula is positive if it is built from atoms and `⊥` using `∧`, `∨`, `□`,
`◇`, and `⟹` with a negative antecedent. -/
def IsPositive : Formula Atom → Prop
  | .atom _ => True
  | .bot => True
  | .imp φ ψ => IsNegative φ ∧ IsPositive ψ
  | .box φ => IsPositive φ

/-- A modal formula is negative if it is built from `⊥` using `∧`, `∨`, `□`, `◇`, and `⟹`
with a positive antecedent and a negative consequent. -/
def IsNegative : Formula Atom → Prop
  | .atom _ => False
  | .bot => True
  | .imp φ ψ => IsPositive φ ∧ IsNegative ψ
  | .box φ => IsNegative φ

end

/-- Iterated box: `boxPow 0 φ = φ`, `boxPow (k + 1) φ = □ (boxPow k φ)`. -/
def boxPow : Nat → Formula Atom → Formula Atom
  | 0, φ => φ
  | k + 1, φ => .box (boxPow k φ)

/-- A Sahlqvist antecedent is built from boxed atoms (`□^k p`) and negative formulas
using `∧`, `∨`, and `◇`. -/
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

/-- A modal formula is a Sahlqvist implication if it is an implication from a
Sahlqvist antecedent to a positive formula. -/
def IsSahlqvistImplication (φ : Formula Atom) : Prop :=
  ∃ α β : Formula Atom, IsSahlqvistAntecedent α ∧ IsPositive β ∧ φ = α.imp β

/-- A modal formula is Sahlqvist if it is built from Sahlqvist implications using `∧`,
`□`, and `∨` with disjoint propositional vocabularies. The disjunction side condition
is essential: arbitrary disjunction leaves the correspondence class. `◇` at the outer
level is not part of the closure (it belongs to the antecedent grammar). The
bare-implication definition alone would reject e.g. a boxed Sahlqvist implication
`□(p → □◇p)`, which is Sahlqvist. -/
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

/-- The B axiom `p → □◇p` is Sahlqvist: its antecedent is a boxed atom (`k = 0`) and its
consequent is positive. -/
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

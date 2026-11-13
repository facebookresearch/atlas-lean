/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quantifier elimination for Presburger arithmetic
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.TheoryOfComputation.PresburgerDecidabilityWanted
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.PresburgerQEWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL
open Cslib.Logic.PresburgerWanted

/-- The standard structure on `ℕ` for the Presburger language. -/
instance presburgerNat : PresburgerLanguage.Structure ℕ where
  funMap f xs := match f with
    | .zero => 0
    | .succ => xs 0 + 1
    | .add => xs 0 + xs 1
  RelMap R xs := match R with
    | .lt => xs 0 < xs 1

/-- Quantifier-free Presburger normal forms with `n` bound variables: Boolean
combinations of equalities, inequalities, and congruence atoms `t ≡ r (mod m + 1)`
over Presburger terms. -/
inductive PresburgerQF (n : ℕ) where
  /-- Falsity. -/
  | falsum : PresburgerQF n
  /-- Equality of two Presburger terms. -/
  | eq : PresburgerLanguage.Term (Empty ⊕ Fin n) →
      PresburgerLanguage.Term (Empty ⊕ Fin n) → PresburgerQF n
  /-- Less-than of two Presburger terms. -/
  | lt : PresburgerLanguage.Term (Empty ⊕ Fin n) →
      PresburgerLanguage.Term (Empty ⊕ Fin n) → PresburgerQF n
  /-- Congruence atom `t ≡ r (mod m + 1)`. -/
  | cong : (m r : ℕ) → PresburgerLanguage.Term (Empty ⊕ Fin n) → PresburgerQF n
  /-- Implication. -/
  | imp : PresburgerQF n → PresburgerQF n → PresburgerQF n

/-- Satisfaction of a quantifier-free Presburger normal form in the standard model `ℕ`. -/
def PresburgerQF.Holds {n : ℕ} (v : Empty → ℕ) (xs : Fin n → ℕ) : PresburgerQF n → Prop
  | .falsum => False
  | .eq s t => s.realize (Sum.elim v xs) = t.realize (Sum.elim v xs)
  | .lt s t => @Structure.RelMap PresburgerLanguage ℕ _ _ PresburgerRelations.lt
      ![s.realize (Sum.elim v xs), t.realize (Sum.elim v xs)]
  | .cong m r t => t.realize (Sum.elim v xs) % (m + 1) = r % (m + 1)
  | .imp ψ χ => ψ.Holds v xs → χ.Holds v xs

/-- Quantifier elimination for Presburger arithmetic: every formula is equivalent, in
the standard model `ℕ`, to a quantifier-free normal form with the same bound
variables, where the normal form is a Boolean combination of equalities,
inequalities, and congruence atoms. The congruence atoms are essential: the
base-language quantifier-free fragment does not suffice even over `ℕ`, since e.g.
parity `∃y. x = y + y` is not equivalent in `ℕ` to any quantifier-free formula in the
language `{0, S, +, <}`. Together with completeness of the Presburger axioms, this
yields the usual provable equivalence, hence decidability of Presburger arithmetic
(see `PresburgerDecidabilityWanted.lean`).
Source: M. Presburger, "Über die Vollständigkeit eines gewissen Systems der Arithmetik
ganzer Zahlen in welchem die Addition die einzige Operation ist", in Comptes Rendus du
I Congrès des Mathématiciens des Pays Slaves, Warsaw, 1929, 92-101; see also H. Enderton,
A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §3.2, and G. Boolos,
J. Burgess, R. Jeffrey, Computability and Logic, 5th ed., Cambridge University Press,
2007, Chapter 28. -/
public theorem_wanted presburger_quantifier_elimination {n : ℕ}
    (φ : PresburgerLanguage.BoundedFormula Empty n) :
    ∃ ψ : PresburgerQF n,
      ∀ (v : Empty → ℕ) (xs : Fin n → ℕ),
        ψ.Holds v xs ↔ φ.Realize v xs

end Cslib.Logic.PresburgerQEWanted

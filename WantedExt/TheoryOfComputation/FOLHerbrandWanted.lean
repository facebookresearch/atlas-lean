/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Herbrand's theorem for first-order logic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.FOLHerbrandWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

variable {L : FirstOrder.Language} {α : Type*}

/-- A bounded formula is quantifier-free if it contains no `∀`. -/
def IsQuantifierFree : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => True
  | _, .rel _ _ => True
  | _, .imp φ ψ => IsQuantifierFree φ ∧ IsQuantifierFree ψ
  | _, .all _ => False

/-- Herbrand's theorem (existential form): if `∃x φ(x)` is valid over nonempty models,
with `φ` quantifier-free, then some finite disjunction of ground instances
`φ(t₁) ∨ … ∨ φ(tₖ)` is valid over nonempty models, where the `tᵢ` are closed terms.
Validity is over nonempty models (`[Nonempty M]`): for a language with no constants,
the empty structure satisfies no existential sentence, so the premise would be
impossible exactly in the case where Herbrand's theorem normally adjoins a fresh
constant. The hypothesis `(hground : Nonempty (L.Term Empty))` rules that case out by
requiring a ground term of the language; with it, the disjunction is over genuine
ground instances, and it is non-vacuous (the empty disjunction `⊥` is not valid over
nonempty models). The dual universal form (a set of universal sentences is
unsatisfiable iff some finite set of its ground instances is propositionally
unsatisfiable) follows by negation.
Source: J. Herbrand, "Recherches sur la théorie de la démonstration", Travaux de la
Société des Sciences et des Lettres de Varsovie, Classe III, Sciences Mathématiques et
Physiques 33, 1930, 1-128; see also H. Enderton, A Mathematical Introduction to Logic,
2nd ed., Academic Press, 2001, §2.5, and S. Buss, "An Introduction to Proof Theory",
in Handbook of Proof Theory, Elsevier, 1998, §2. -/
public theorem_wanted fol_herbrand {L : FirstOrder.Language}
    {φ : L.BoundedFormula Empty 1} (hqf : IsQuantifierFree φ)
    (hground : Nonempty (L.Term Empty))
    (hvalid : ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ φ.ex) :
    ∃ ts : List (L.Term Empty),
      ∀ (M : Type) [L.Structure M] [Nonempty M],
        M ⊨ ts.foldr (fun t acc => (instantiate t φ) ⊔ acc) ⊥

end Cslib.Logic.FOLHerbrandWanted

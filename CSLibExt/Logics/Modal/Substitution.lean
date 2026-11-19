/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Sahlqvist

@[expose] public section

/-!
# Substitution and locality of Kripke semantics

Uniform substitution of a formula for an atom in the basic modal language of `Kripke.lean`, and
two facts about the Kripke semantics of substituted formulas.

* `Formula.iff`: the biconditional, `(φ → ψ) ∧ (ψ → φ)`.
* `Formula.subst`: `φ.subst p ψ` replaces the atom `p` by `ψ` in `φ`.
* `KripkeModel.updateAtom`: the model with the atom `p` reinterpreted as a given set of worlds.
* `KripkeModel.satisfies_subst` (**substitution lemma**): `φ(ψ)` holds at `w` iff `φ` holds at
  `w` once `p` is reinterpreted as the truth set of `ψ`.
* `KripkeModel.satisfies_congr` (**locality**): truth at a world depends only on the valuation,
  on the atoms of the formula (`Formula.atoms`, from `Sahlqvist.lean`), at the worlds reachable
  from it.

These are the semantic tools used for the fixed point theorems of the provability logic GL
(`ProvabilityLogic/FixedPoint.lean`).

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001
  (uniform substitution; invariance of truth under generated submodels).
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

namespace Formula

/-- **Biconditional.** `φ ↔ ψ`, encoded as `(φ → ψ) ∧ (ψ → φ)` in the `⊥`, `→`, `□` basis. -/
def iff (phi psi : Formula Atom) : Formula Atom := (Formula.imp phi psi).and (.imp psi phi)

variable [DecidableEq Atom]

/-- **Substitution of a formula for an atom.** `φ.subst p ψ` replaces every occurrence of the
atom `p` in `φ` by `ψ`; written `φ(ψ)` when `φ = φ(p)`. -/
def subst : Formula Atom → Atom → Formula Atom → Formula Atom
  | .atom q, p, psi => if q = p then psi else .atom q
  | .bot, _, _ => .bot
  | .imp phi chi, p, psi => .imp (subst phi p psi) (subst chi p psi)
  | .box phi, p, psi => .box (subst phi p psi)

end Formula

namespace KripkeModel

variable {World : Type v}

@[simp] theorem satisfies_iff (M : KripkeModel World Atom) (w : World) (phi psi : Formula Atom) :
    M.Satisfies w (phi.iff psi) ↔ (M.Satisfies w phi ↔ M.Satisfies w psi) := by
  simp [Formula.iff, iff_iff_implies_and_implies]

/-- **Kripke model with one atom reinterpreted.** `M.updateAtom p S` has the frame of `M`, the atom
`p` true exactly at the worlds satisfying `S`, and every other atom as in `M`. -/
def updateAtom [DecidableEq Atom] (M : KripkeModel World Atom) (p : Atom) (S : World → Prop) :
    KripkeModel World Atom where
  nonempty_world := M.nonempty_world
  rel := M.rel
  valuation w q := if q = p then S w else M.valuation w q

@[simp] theorem updateAtom_valuation_self [DecidableEq Atom] (M : KripkeModel World Atom) (p : Atom)
    (S : World → Prop) (w : World) : (M.updateAtom p S).valuation w p = S w := by
  simp [updateAtom]

theorem updateAtom_valuation_ne [DecidableEq Atom] {M : KripkeModel World Atom} {p q : Atom}
    (h : q ≠ p) (S : World → Prop) (w : World) :
    (M.updateAtom p S).valuation w q = M.valuation w q := by
  simp [updateAtom, h]

/-- **Semantic substitution lemma.** `φ(ψ)` holds at `w` iff `φ` holds at `w` once `p` is
reinterpreted as the set of worlds satisfying `ψ`. -/
theorem satisfies_subst [DecidableEq Atom] (M : KripkeModel World Atom) (p : Atom)
    (psi phi : Formula Atom) (w : World) :
    M.Satisfies w (phi.subst p psi) ↔ (M.updateAtom p (M.Satisfies · psi)).Satisfies w phi := by
  induction phi generalizing w with
  | atom q =>
    by_cases h : q = p
    · simp [Formula.subst, updateAtom, h]
    · simp [Formula.subst, updateAtom, h]
  | bot => exact Iff.rfl
  | imp phi chi ih₁ ih₂ => simp only [Formula.subst, satisfies_imp, ih₁, ih₂]
  | box phi ih =>
    simp only [Formula.subst, satisfies_box, ih]
    exact Iff.rfl

/-- **Truth depends only on the visible part of the valuation.** If two Kripke models have the
same relation and their valuations agree, on the atoms occurring in `φ`, at every world of a set
`U` closed under the relation, then `φ` has the same truth value in both at every world of `U`. -/
theorem satisfies_congr (M N : KripkeModel World Atom) (hrel : M.rel = N.rel) (U : Set World)
    (hU : ∀ v ∈ U, ∀ u, M.rel v u → u ∈ U) (phi : Formula Atom)
    (hval : ∀ v ∈ U, ∀ q ∈ phi.atoms, (M.valuation v q ↔ N.valuation v q)) :
    ∀ v ∈ U, (M.Satisfies v phi ↔ N.Satisfies v phi) := by
  induction phi with
  | atom q => exact fun v hv ↦ hval v hv q rfl
  | bot => exact fun _ _ ↦ Iff.rfl
  | imp phi chi ih₁ ih₂ =>
    intro v hv
    simp only [satisfies_imp]
    exact imp_congr (ih₁ (fun v hv q hq ↦ hval v hv q (Or.inl hq)) v hv)
      (ih₂ (fun v hv q hq ↦ hval v hv q (Or.inr hq)) v hv)
  | box phi ih =>
    intro v hv
    simp only [satisfies_box, ← hrel]
    exact forall_congr' fun u ↦ imp_congr_right fun hvu ↦ ih hval u (hU v hv u hvu)

end KripkeModel

end Modal
end Cslib

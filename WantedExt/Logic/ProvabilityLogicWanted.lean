/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.ProvabilityLogic.FixedPoint

/-!
# Provability logic GL: wanted results

Established results about GL over the Hilbert system `Derivable Axioms.GL` of
`CSLibExt.Logics.Modal.ProvabilityLogic.Basic`, recorded without proof.

* `derivable_GL_iff_finite`: Segerberg's completeness theorem for finite strict partial orders.
* `frame_valid_axiomLob_iff`: frame correspondence for Löb's axiom.
* `fixedPoint_GL`: the de Jongh–Sambin fixed point theorem (existence), in general.
-/

@[expose] public section

namespace Cslib
namespace Modal

universe u

variable {Atom : Type u}

/-- **Completeness of GL for finite strict partial orders** (Segerberg 1971; also de Jongh and
Kripke). A formula is a theorem of GL iff it is valid in every Kripke model on a finite set of
worlds whose relation is transitive and irreflexive (Verbrugge, "Provability logic", *Stanford
Encyclopedia of Philosophy*, current edition, §3.2, which also records completeness for finite
transitive irreflexive trees). The direction from left to right is the proved
`Derivable.valid_GL_of_finite`. -/
theorem_wanted derivable_GL_iff_finite (phi : Formula Atom) :
    Derivable Axioms.GL phi ↔
      ∀ (W : Type u) [Finite W] (M : KripkeModel W Atom),
        (∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) → (∀ w, ¬M.rel w w) → M.Valid phi

/-- **Frame correspondence for Löb's axiom.** On a nonempty set of worlds `W`, with at least one
atom, Löb's axiom `□(□φ → φ) → □φ` is valid for every formula `φ` and every valuation on the frame
`(W, R)` iff `R` is transitive and conversely well-founded, i.e. has no infinite chain
`w₀ R w₁ R w₂ R ⋯` (Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*,
current edition, §3.1). The direction from right to left is the proved
`KripkeModel.valid_axiomLob`. -/
theorem_wanted frame_valid_axiomLob_iff {W : Type u} [Nonempty W] [Nonempty Atom]
    (R : W → W → Prop) :
    (∀ (V : W → Atom → Prop) (phi : Formula Atom),
        (KripkeModel.mk inferInstance R V).Valid (Formula.axiomLob phi)) ↔
      (∀ {a b c}, R a b → R b c → R a c) ∧ WellFounded (flip R)

/-- **The de Jongh–Sambin fixed point theorem.** If every occurrence of the atom `p` in `A` lies
under a box, there is a formula `H` in which `p` does not occur, all of whose atoms occur in `A`,
such that `GL ⊢ H ↔ A(H)` (de Jongh and Sambin, 1975; Verbrugge, "Provability logic", *Stanford
Encyclopedia of Philosophy*, current edition, §2.2). The fixed point is unique up to GL-provable
equivalence by the proved `Derivable.fixedPoint_unique_GL`; the case of one boxed occurrence is
the proved `Derivable.fixedPoint_GL_of_box`. -/
theorem_wanted fixedPoint_GL [DecidableEq Atom] {A : Formula Atom} {p : Atom}
    (hA : A.Modalised p) :
    ∃ H : Formula Atom, p ∉ H.atoms ∧ H.atoms ⊆ A.atoms ∧
      Derivable Axioms.GL (H.iff (A.subst p H))

end Modal
end Cslib

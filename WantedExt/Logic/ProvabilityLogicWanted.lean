/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.ProvabilityLogic.FixedPointExistence
public import CSLibExt.Logics.Modal.ProvabilityLogic.FrameCorrespondence

/-!
# Provability logic GL: wanted results

Established results about GL over the Hilbert system `Derivable Axioms.GL` of
`CSLibExt.Logics.Modal.ProvabilityLogic.Basic`, recorded without proof.

* `derivable_GL_iff_finite`: Segerberg's completeness theorem for finite strict partial orders.
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

end Modal
end Cslib

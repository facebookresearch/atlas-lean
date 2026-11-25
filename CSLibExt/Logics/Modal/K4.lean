/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Canonical

@[expose] public section

/-!
# The modal logic K4

K4 is the normal modal logic `K ⊕ 4` with the transitivity axiom `4 : □φ → □□φ`. It is sound and
strongly complete for transitive Kripke models; the completeness proof is the canonical model
argument of `Canonical.lean`, whose relation is transitive when `4` is a theorem.

* `Axioms.K4`: the extra axioms of K4.
* `Derivable.valid_K4` (**soundness**), `not_derivable_bot_K4` (**consistency**).
* `completeness_K4`, `derivable_K4_iff` (**strong completeness** for transitive models).

K4 is the base over which the provability logic GL is built (`ProvabilityLogic/Basic.lean`):
every K4 theorem is a GL theorem, and GL adds Löb's axiom.

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001, §4.2.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

namespace Axioms

/-- **Extra axioms of K4.** The transitivity axioms `□φ → □□φ` (Blackburn, de Rijke and
Venema, *Modal Logic*, 2001, §4.2). -/
def K4 : Set (Formula Atom) := Set.range Formula.axiomFour

theorem axiomFour_mem_K4 (phi : Formula Atom) :
    Formula.axiomFour phi ∈ (K4 : Set (Formula Atom)) :=
  ⟨phi, rfl⟩

end Axioms

/-! ### K4 -/

section K4

variable {World : Type v} {M : KripkeModel World Atom}

/-- **Soundness of K4 for transitive Kripke models.** Every theorem of K4 is valid in every
Kripke model whose accessibility relation is transitive (Blackburn, de Rijke and Venema, *Modal
Logic*, 2001, §4.2). -/
theorem Derivable.valid_K4
    (trans : ∀ {first second third}, M.rel first second → M.rel second third →
      M.rel first third)
    {phi : Formula Atom} (h : Derivable Axioms.K4 phi) : M.Valid phi :=
  h.valid fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact M.valid_axiomFour trans psi

/-- **Consistency of K4.** `⊥` is not a theorem of K4. -/
theorem not_derivable_bot_K4 : ¬Derivable (Axioms.K4 : Set (Formula Atom)) .bot :=
  not_derivable_bot fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact KripkeModel.unit.valid_axiomFour (fun _ _ ↦ trivial) psi

variable {Γ : Set (Formula Atom)} {phi : Formula Atom}

/-- **Strong completeness of K4** for transitive Kripke models: if `φ` holds at every world of
every transitive model at which all of `Γ` hold, then `Γ` deduces `φ` in K4 (Blackburn, de Rijke
and Venema, *Modal Logic*, 2001, §4.2, canonical model argument). -/
theorem completeness_K4
    (hsem : LocallyEntails (fun M ↦ ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) Γ phi) :
    Deduces Axioms.K4 Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_K4
    (fun {_ _ _} hab hbc ↦
      CanonicalWorld.rel_trans (fun phi ↦ .extra (Axioms.axiomFour_mem_K4 phi)) hab hbc)
    hsem

/-- **K4-theorems are the formulas valid in every transitive Kripke model.** For models whose
worlds live in the universe of the atoms (no restriction, since soundness holds in every
universe). -/
theorem derivable_K4_iff :
    Derivable Axioms.K4 phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom),
        (∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) → M.Valid phi := by
  refine ⟨fun h _ _ htrans ↦ h.valid_K4 htrans,
    fun h ↦ deduces_empty_iff.mp (completeness_K4 ?_)⟩
  exact fun W M w htrans _ ↦ h W M htrans w

end K4

end Modal
end Cslib

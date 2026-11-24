/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.K4
public import CSLibExt.Logics.Modal.CslibTranslation

@[expose] public section

/-!
# The provability logic GL

The provability logic `GL` (after Gödel and Löb) is the normal modal logic `K ⊕ Löb`, where
Löb's axiom is `□(□φ → φ) → □φ`. Read `□` as "is provable in Peano arithmetic"; by Solovay's
theorem (1976) the theorems of `GL` are exactly the modal formulas all of whose arithmetical
realizations are provable in PA. This file develops the modal side over the Hilbert systems of
`Hilbert.lean`.

* `Axioms.GL`: the extra axioms of GL (Löb's axiom). K4 and its completeness for transitive
  models are in `CSLibExt.Logics.Modal.K4`.
* `KripkeModel.valid_axiomLob`, `Derivable.valid_GL` (**soundness**): Löb's axiom, hence each
  GL-theorem, is valid in every Kripke model whose relation is transitive and conversely
  well-founded (no infinite chain `w₀ R w₁ R w₂ R ⋯`).
* `Derivable.axiomFour_GL`: GL proves `□φ → □□φ`, by one instance of Löb's axiom (for
  `φ ∧ □φ`) and a theorem of K; hence every theorem of K4 is a theorem of GL
  (`Derivable.GL_of_K4`).
* `Derivable.godel_second_GL`: GL proves `¬□⊥ → ¬□¬□⊥`, the modal form of Gödel's second
  incompleteness theorem.
* `not_derivable_axiomT_bot_GL`, `not_derivable_axiomLob_K4`: GL does not prove `□⊥ → ⊥`, and K4
  does not prove Löb's axiom, so GL is consistent and strictly extends K4.

## References

* G. Boolos, *The Logic of Provability*, Cambridge University Press, 1993.
* R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy* (current edition),
  §2.1 (axioms of GL and the derivation of axiom 4) and §3.1 (frame correspondence and soundness).
* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001, §4.2.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

namespace Formula

/-- **Löb's axiom.** The formula `□(□φ → φ) → □φ`, the extra axiom of the provability logic GL;
it is the modal form of the formalized Löb theorem `PA ⊢ Prov(⌜Prov(⌜φ⌝) → φ⌝) → Prov(⌜φ⌝)`
(Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §1 and §2.1). -/
def axiomLob (phi : Formula Atom) : Formula Atom := .imp (.box (.imp (.box phi) phi)) (.box phi)

end Formula

namespace Axioms

/-- **Extra axioms of the provability logic GL.** The instances of Löb's axiom
`□(□φ → φ) → □φ`; `Derivable Axioms.GL` is the logic GL of Gödel and Löb, also written `L`,
`KW` or `PrL` (Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §2.1). -/
def GL : Set (Formula Atom) := Set.range Formula.axiomLob

theorem axiomLob_mem_GL (phi : Formula Atom) : Formula.axiomLob phi ∈ (GL : Set (Formula Atom)) :=
  ⟨phi, rfl⟩

end Axioms

/-! ### Soundness of GL -/

section Soundness

variable {World : Type v}

/-- **Löb's axiom is valid on transitive conversely well-founded frames.** If the accessibility
relation is transitive and has no infinite ascending chain `w₀ R w₁ R w₂ R ⋯`
(`WellFounded (flip M.rel)`), then `□(□φ → φ) → □φ` holds at every world (Verbrugge,
"Provability logic", *Stanford Encyclopedia of Philosophy*, §3.1). The proof bridges to CSLib's
`Cslib.Logic.Modal.Satisfies.l` through the translation `Formula.toProposition`. -/
theorem KripkeModel.valid_axiomLob (M : KripkeModel World Atom)
    (trans : ∀ {first second third}, M.rel first second → M.rel second third →
      M.rel first third)
    (cwf : WellFounded (flip M.rel)) (phi : Formula Atom) :
    M.Valid (Formula.axiomLob phi) := by
  have : IsTrans World M.rel := ⟨fun _ _ _ ↦ trans⟩
  intro w
  have hl := Logic.Modal.Satisfies.l (Frame.ofRelation (τ := Logic.Modal.τUnimodal Atom) M.rel)
    cwf (Formula.toProposition phi) M.valuation w
  simp only [Logic.Modal.Satisfies.imp_iff_imp, Logic.Modal.Satisfies.box_iff_forall] at hl
  simp only [Formula.axiomLob, KripkeModel.satisfies_imp, KripkeModel.satisfies_box]
  intro h v hwv
  refine (satisfies_toProposition M v phi).mpr (hl (fun v' hv' hbox ↦ ?_) v hwv)
  exact (satisfies_toProposition M v' phi).mp
    (h v' hv' fun u hu ↦ (satisfies_toProposition M u phi).mpr (hbox u hu))

variable {M : KripkeModel World Atom}

/-- **Soundness of GL** for transitive, conversely well-founded Kripke models: every theorem of GL
is valid in every Kripke model whose relation is transitive and has no infinite ascending chain
(Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §3.1). -/
theorem Derivable.valid_GL
    (trans : ∀ {first second third}, M.rel first second → M.rel second third →
      M.rel first third)
    (cwf : WellFounded (flip M.rel)) {phi : Formula Atom} (h : Derivable Axioms.GL phi) :
    M.Valid phi :=
  h.valid fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact M.valid_axiomLob trans cwf psi

/-- **Soundness of GL for finite strict partial orders.** Every theorem of GL is valid in every
Kripke model on a finite set of worlds whose relation is transitive and irreflexive; on a finite
set such a relation is conversely well-founded. -/
theorem Derivable.valid_GL_of_finite [Finite World]
    (trans : ∀ {first second third}, M.rel first second → M.rel second third →
      M.rel first third)
    (irrefl : ∀ w, ¬M.rel w w) {phi : Formula Atom} (h : Derivable Axioms.GL phi) :
    M.Valid phi := by
  have : IsTrans World (flip M.rel) := ⟨fun _ _ _ h₁ h₂ ↦ trans h₂ h₁⟩
  have : Std.Irrefl (flip M.rel) := ⟨irrefl⟩
  exact h.valid_GL trans (Finite.wellFounded_of_trans_of_irrefl _)

end Soundness

/-! ### GL extends K4 -/

namespace Derivable

variable {phi psi : Formula Atom}

/-- **Modus ponens with a K theorem.** A theorem `φ → ψ` of K and a proof of `φ` in any normal
modal logic `K ⊕ Λ` give a proof of `ψ` in `K ⊕ Λ`, since every theorem of K is a theorem of
`K ⊕ Λ`. -/
theorem mp_of_K {Λ : Set (Formula Atom)} (hK : Derivable Axioms.K (.imp phi psi))
    (h : Derivable Λ phi) : Derivable Λ psi :=
  .mp (hK.mono fun _ h ↦ absurd h (Set.notMem_empty _)) h

/-- **GL proves axiom 4.** For every `φ`, `□φ → □□φ` is a theorem of GL: apply Löb's axiom to
`φ ∧ □φ`, whose hypothesis `□(□(φ ∧ □φ) → φ ∧ □φ)` follows from `□φ` in K, and whose conclusion
`□(φ ∧ □φ)` gives `□□φ` in K (Verbrugge, "Provability logic", *Stanford Encyclopedia of
Philosophy*, §2.1). The two K steps are obtained from the completeness of K
(`derivable_K_iff`). -/
theorem axiomFour_GL (phi : Formula Atom) :
    Derivable Axioms.GL (Formula.axiomFour phi) := by
  refine mp_of_K ?_ (.extra (Axioms.axiomLob_mem_GL (phi.and (.box phi))))
  refine derivable_K_iff.mpr fun W M w hl hbox ↦ ?_
  simp only [Formula.axiomLob, KripkeModel.satisfies_imp, KripkeModel.satisfies_box,
    KripkeModel.satisfies_and] at hl ⊢
  intro v hv
  refine (hl (fun v' hv' hb ↦ ⟨hbox v' hv', fun u hu ↦ (hb u hu).1⟩) v hv).2

/-- **Every theorem of K4 is a theorem of GL.** -/
theorem GL_of_K4 (h : Derivable Axioms.K4 phi) : Derivable Axioms.GL phi := by
  induction h with
  | ax1 => exact .ax1 _ _
  | ax2 => exact .ax2 _ _ _
  | dne => exact .dne _
  | distrib => exact .distrib _ _
  | extra h =>
    obtain ⟨psi, rfl⟩ := h
    exact axiomFour_GL psi
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | nec _ ih => exact .nec ih

/-- **Modal Gödel's second incompleteness theorem.** GL proves `¬□⊥ → ¬□¬□⊥`: if `⊥` is not
provable, then the consistency statement `¬□⊥` is not provable. It follows from the instance
`□(□⊥ → ⊥) → □⊥` of Löb's axiom by contraposition (Verbrugge, "Provability logic", *Stanford
Encyclopedia of Philosophy*, §2.2 and §4.1). -/
theorem godel_second_GL :
    Derivable Axioms.GL
      (.imp (Formula.box (.bot : Formula Atom)).neg
        (Formula.box (Formula.box (.bot : Formula Atom)).neg).neg) := by
  refine mp_of_K ?_ (.extra (Axioms.axiomLob_mem_GL .bot))
  refine derivable_K_iff.mpr fun W M w hl hcon hprov ↦ hcon ?_
  exact hl hprov

/-- **The Gödel sentence of GL.** The consistency statement `¬□⊥` is a fixed point of `¬□p`: GL
proves `¬□⊥ → ¬□¬□⊥` and `¬□¬□⊥ → ¬□⊥` (Verbrugge, "Provability logic", *Stanford Encyclopedia
of Philosophy*, §2.2, where `¬□⊥` is the fixed point that the de Jongh–Sambin algorithm produces
for `¬□p`). -/
theorem godel_sentence_GL :
    Derivable Axioms.GL
        (.imp (Formula.box (.bot : Formula Atom)).neg
          (Formula.box (Formula.box (.bot : Formula Atom)).neg).neg) ∧
      Derivable Axioms.GL
        (.imp (Formula.box (Formula.box (.bot : Formula Atom)).neg).neg
          (Formula.box (.bot : Formula Atom)).neg) := by
  refine ⟨godel_second_GL, mp_of_K ?_ (Derivable.imp_self (.bot : Formula Atom))⟩
  refine derivable_K_iff.mpr fun W M w _ hcon hprov ↦ hcon fun v hv ↦ ?_
  exact absurd (hprov v hv) (M.not_satisfies_bot v)

end Derivable

/-! ### GL is consistent and strictly extends K4 -/

/-- **The one-world irreflexive Kripke model.** One world, which sees no world, with every atom
false. Its relation is empty, hence transitive and conversely well-founded. -/
def KripkeModel.irreflexivePoint : KripkeModel PUnit.{1} Atom where
  nonempty_world := ⟨PUnit.unit⟩
  rel _ _ := False
  valuation _ _ := False

/-- **GL does not prove reflection for `⊥`.** `□⊥ → ⊥` is not a theorem of GL: it fails in the
one-world irreflexive model, where `□⊥` holds vacuously. In particular GL is consistent and does
not contain the logic T. -/
theorem not_derivable_axiomT_bot_GL :
    ¬Derivable (Axioms.GL : Set (Formula Atom)) (Formula.axiomT .bot) := fun h ↦
  (h.valid_GL (M := KripkeModel.irreflexivePoint) (fun h _ ↦ h.elim)
    ⟨fun a ↦ ⟨a, fun _ h ↦ h.elim⟩⟩)
    PUnit.unit (fun _ h ↦ h.elim)

/-- **Consistency of GL.** `⊥` is not a theorem of GL. -/
theorem not_derivable_bot_GL : ¬Derivable (Axioms.GL : Set (Formula Atom)) .bot := fun h ↦
  not_derivable_axiomT_bot_GL (.mp (.ax1 _ _) h)

/-- **K4 does not prove Löb's axiom.** The instance `□(□⊥ → ⊥) → □⊥` fails in the one-world
reflexive model, which is transitive; hence GL strictly extends K4. -/
theorem not_derivable_axiomLob_K4 :
    ¬Derivable (Axioms.K4 : Set (Formula Atom)) (Formula.axiomLob .bot) := fun h ↦ by
  have := (h.valid_K4 (M := KripkeModel.unit) (fun _ _ ↦ trivial)) PUnit.unit
  simp only [Formula.axiomLob, KripkeModel.satisfies_imp, KripkeModel.satisfies_box] at this
  exact this (fun _ _ hbox ↦ hbox PUnit.unit trivial) PUnit.unit trivial

end Modal
end Cslib

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Hilbert
public import Cslib.Logics.Modal.Unimodal.Cube

@[expose] public section

/-!
# Translating CSLib's modal syntax into the Hilbert basis

CSLib's modal logic is parameterised by a signature of modal operators. Its `Unimodal` aliases
instantiate one unary operator; propositions have constructors for atoms, `false`, `¬`, `∨` and
`triangle`. The Hilbert systems of `Hilbert.lean` work over the `⊥`, `→`, `□` basis of
`Kripke.lean`.
The binary accessibility relation is `m.rel`, and the atom valuation is `m.v`.

* `Formula.ofProposition`: the translation (`false ↦ ⊥`, `¬φ ↦ φ → ⊥`,
  `φ ∨ ψ ↦ ¬φ → ψ`, and a unimodal `triangle` `↦ ◇φ = ¬□¬φ`).
* `KripkeModel.ofModel`: a CSLib model on a nonempty type of worlds as a Kripke model.
* `satisfies_ofProposition`: the translation preserves satisfaction at every world.
* `Derivable.mem_K`, `mem_T`, `mem_S4`, `mem_S5`: **soundness for CSLib's own modal cube**. A
  proposition whose translation is a theorem of K (respectively T, S4, S5) belongs to CSLib's
  semantic logic `Cslib.Logic.Modal.Unimodal.K World Atom` (respectively `T`, `S4`, `S5`) for
  every type of worlds. These model classes retain the same reflexivity, transitivity and
  right-Euclidean conditions on the binary relation.

The translation is completed to a bidirectional equivalence below
(`KripkeModel.toModel`, `KripkeModel.ofModel_toModel`,
`KripkeModel.toModel_ofModel`, `Formula.toProposition`,
`satisfies_toProposition`).  The local `Formula`/`KripkeModel` of
`Kripke.lean` are retained because the Hilbert-system development
(derivations in the `⊥`/`→`/`□` basis, canonical models, filtration in
`Hilbert.lean`, `Canonical.lean`, `Filtration.lean`) is built over that
concrete syntax and uses a bundled `Nonempty World` invariant, whereas
CSLib's `Proposition`/`Model` are generic over a `PFunctor` signature
with an `or`/`not`/`triangle` basis and possibly empty world types; the
equivalence here shows the two presentations define the same unimodal
semantics, so results transfer in both directions.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u} {World : Type v}

/-- **Translation of CSLib's modal propositions.** CSLib's unimodal propositions are translated into
modal formulas in the $\bot$, $\to$, $\Box$ basis by recursion, writing $\varphi'$ for the
translation of $\varphi$: an atom $p$ goes to $p$, falsehood to $\bot$, $\neg\varphi$ to
$\varphi' \to \bot$, $\varphi \lor \psi$ to $(\varphi' \to \bot) \to \psi'$, and the diamond
(the unimodal triangle) applied to $\varphi$ goes to $\Diamond\varphi'$, that is, to
$\Box(\varphi' \to \bot) \to \bot$. -/
def Formula.ofProposition : Logic.Modal.Unimodal.Proposition Atom → Formula Atom
  | .atom p => .atom p
  | .false => .bot
  | .not phi => (ofProposition phi).neg
  | .or phi psi => (ofProposition phi).or (ofProposition psi)
  | .triangle _ phis => (ofProposition (phis default)).dia
termination_by structural phi => phi

/-- **Kripke model of a CSLib model.** For a CSLib unimodal model $m$ on a nonempty type of worlds,
the associated Kripke model has the same worlds, the binary accessibility relation of $m$ as its
accessibility relation, and the valuation of $m$ as its valuation. -/
def KripkeModel.ofModel [Nonempty World] (m : Logic.Modal.Unimodal.Model World Atom) :
    KripkeModel World Atom where
  nonempty_world := inferInstance
  rel := m.rel
  valuation := m.v

/-- **The translation preserves satisfaction.** Let $m$ be a CSLib unimodal model on a nonempty type
of worlds, $w$ a world and $\varphi$ a CSLib unimodal proposition. Then the translation of $\varphi$
into the $\bot$, $\to$, $\Box$ basis holds at $w$ in the Kripke model of $m$ if and only if
$\varphi$ holds at $w$ in $m$. -/
theorem satisfies_ofProposition [Nonempty World]
    (m : Logic.Modal.Unimodal.Model World Atom) (w : World)
    (phi : Logic.Modal.Unimodal.Proposition Atom) :
    (KripkeModel.ofModel m).Satisfies w (Formula.ofProposition phi) ↔
      Logic.Modal.Satisfies m w phi := by
  induction phi generalizing w with
  | atom p => rfl
  | false => rfl
  | not phi ih =>
    rw [Formula.ofProposition, KripkeModel.satisfies_neg, ih]
    rfl
  | or phi psi ih₁ ih₂ =>
    rw [Formula.ofProposition, KripkeModel.satisfies_or, ih₁, ih₂]
    rfl
  | triangle op phis ih =>
    rw [Formula.ofProposition, KripkeModel.satisfies_dia]
    simp only [ih]
    have hsem : Logic.Modal.Satisfies m w (.triangle op phis) ↔
        ∃ next, m.toFrame.diagonal op w next ∧
          Logic.Modal.Satisfies m next (phis default) := by
      rw [Logic.Modal.Proposition.triangle_def,
        Logic.Modal.Proposition.unary_triangle_eq_dynDiamond]
      exact Logic.Modal.Satisfies.dynDiamond_iff_exists
    have hrel : m.toFrame.diagonal op = m.rel := by
      change m.toFrame.diagonal op = m.toFrame.diagonal default
      exact congrArg m.toFrame.diagonal (Subsingleton.elim op default)
    simpa only [hrel, KripkeModel.ofModel] using hsem.symm

/-- **The CSLib unimodal model of a Kripke model.** A Kripke model $k$ on worlds $W$ gives the
CSLib unimodal model on $W$ whose frame is the unimodal frame built from the accessibility
relation of $k$ and whose valuation is the valuation of $k$. -/
def KripkeModel.toModel (k : KripkeModel World Atom) :
    Logic.Modal.Unimodal.Model World Atom where
  toFrame := Frame.ofRelation k.rel
  v := k.valuation

/-- **Kripke to CSLib and back is the identity.** Let $k$ be a Kripke model on a nonempty type of
worlds. Converting $k$ to a CSLib unimodal model and converting that model back to a Kripke model
gives $k$. -/
theorem KripkeModel.ofModel_toModel [Nonempty World] (k : KripkeModel World Atom) :
    KripkeModel.ofModel (KripkeModel.toModel k) = k := by
  cases k with
  | mk hne rel val => rfl

/-- **Round trip from CSLib models through Kripke models.** For a nonempty type of worlds $W$,
converting a CSLib unimodal model $m$ on $W$ into a Kripke model and then back into a CSLib
unimodal model returns $m$: a unimodal frame is determined by its binary accessibility relation. -/
theorem KripkeModel.toModel_ofModel [Nonempty World]
    (m : Logic.Modal.Unimodal.Model World Atom) :
    (KripkeModel.ofModel m).toModel = m := by
  obtain ⟨f, v⟩ := m
  have hframe : Frame.ofRelation (Frame.rel f) = f := by
    cases f with
    | mk r =>
      congr 1
  change (⟨Frame.ofRelation (Frame.rel f), v⟩ :
    Logic.Modal.Unimodal.Model World Atom) = ⟨f, v⟩
  rw [hframe]

/-- **Translation of modal formulas into CSLib propositions.** Each modal formula built from
atoms, $\bot$, $\to$ and $\Box$ is translated into a CSLib unimodal proposition by recursion:
an atom $p$ goes to the atom $p$, $\bot$ goes to false, $\varphi \to \psi$ goes to
$\neg\varphi' \lor \psi'$, and $\Box\varphi$ goes to $\neg\Diamond\neg\varphi'$, where
$\varphi'$ and $\psi'$ are the translations of $\varphi$ and $\psi$ and $\Diamond$ is the
possibility operator of CSLib's unimodal language. -/
def Formula.toProposition : Formula Atom → Logic.Modal.Unimodal.Proposition Atom
  | .atom p => .atom p
  | .bot => .false
  | .imp phi psi => .or (.not (toProposition phi)) (toProposition psi)
  | .box phi => .not (.triangle default (fun _ => .not (toProposition phi)))

/-- **The reverse translation preserves satisfaction.** Let $k$ be a Kripke model, $w$ a world
and $\varphi$ a modal formula in the $\bot$, $\to$, $\Box$ basis. Then $\varphi$ holds at $w$ in $k$
if and only if its translation into a CSLib unimodal proposition holds at $w$ in the CSLib model
associated with $k$.

Together with the preservation of satisfaction by the forward translation and the two model round
trips, this shows that the two presentations have the same unimodal semantics. -/
theorem satisfies_toProposition (k : KripkeModel World Atom) (w : World)
    (phi : Formula Atom) :
    k.Satisfies w phi ↔ Logic.Modal.Satisfies k.toModel w (Formula.toProposition phi) := by
  induction phi generalizing w with
  | atom p => rfl
  | bot => rfl
  | imp phi psi ih₁ ih₂ =>
    simp only [KripkeModel.satisfies_imp, Formula.toProposition,
      Logic.Modal.Satisfies, ih₁, ih₂]
    constructor
    · intro h
      exact Classical.byCases (fun hphi => Or.inr (h hphi)) (fun hphi => Or.inl hphi)
    · rintro (hphi | hpsi) hphi'
      · exact False.elim (hphi hphi')
      · exact hpsi
  | box phi ih =>
    have hsem : Logic.Modal.Satisfies k.toModel w
        (.triangle default (fun _ => .not (Formula.toProposition phi))) ↔
        ∃ next, k.toModel.toFrame.diagonal default w next ∧
          Logic.Modal.Satisfies k.toModel next
            (.not (Formula.toProposition phi)) := by
      rw [Logic.Modal.Proposition.triangle_def,
        Logic.Modal.Proposition.unary_triangle_eq_dynDiamond]
      exact Logic.Modal.Satisfies.dynDiamond_iff_exists
    have hdiag : ∀ a b, k.toModel.toFrame.diagonal default a b ↔ k.rel a b := by
      intro a b
      rw [← Frame.rel_iff_diagonal]
      show (Frame.ofRelation k.rel).rel a b ↔ k.rel a b
      rw [Frame.ofRelation_rel]
    rw [Formula.toProposition]
    constructor
    · intro hbox hcon
      obtain ⟨next, hnext, hnot⟩ := hsem.mp hcon
      exact hnot ((ih next).mp (hbox next ((hdiag w next).mp hnext)))
    · intro h next hnext
      exact Classical.byContradiction fun hnot =>
        h (hsem.mpr ⟨next, (hdiag w next).mpr hnext,
          fun hsat => hnot ((ih next).mpr hsat)⟩)

/-- **Validity agrees with its CSLib translation.** A modal formula $\varphi$ is
valid in a Kripke model $k$ (true at every world of $k$) if and only if its translation into a
CSLib unimodal proposition is satisfied at every world of the CSLib unimodal model associated
with $k$. -/
theorem KripkeModel.valid_toProposition (k : KripkeModel World Atom)
    (phi : Formula Atom) :
    k.Valid phi ↔
      ∀ w, Logic.Modal.Satisfies k.toModel w (Formula.toProposition phi) :=
  forall_congr' fun w => satisfies_toProposition k w phi

/-- **Validity of the translation gives membership in CSLib's logic.** Let $S$ be a class of CSLib
unimodal models on a type of worlds and $\varphi$ a CSLib unimodal proposition. Suppose that, if
the type of worlds is nonempty, the translation of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is
valid in the Kripke model of every model in $S$. Then $\varphi$ belongs to CSLib's semantic logic
of $S$: it holds at every world of every model in $S$. -/
theorem mem_logic_of_valid {S : Set (Logic.Modal.Unimodal.Model World Atom)}
    {phi : Logic.Modal.Unimodal.Proposition Atom}
    (h : ∀ m ∈ S, ∀ _ : Nonempty World, (KripkeModel.ofModel m).Valid (Formula.ofProposition phi)) :
    phi ∈ Logic.Modal.logic S := by
  intro m hm w
  have hne : Nonempty World := ⟨w⟩
  exact (satisfies_ofProposition m w phi).mp (h m hm hne w)

namespace Derivable

variable {phi : Logic.Modal.Unimodal.Proposition Atom}

/-- **Soundness for CSLib's K.** Let $\varphi$ be a CSLib unimodal proposition. If the translation
of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of the Hilbert system K, then, for
every type of worlds, $\varphi$ belongs to CSLib's modal logic K: it holds at every world of every
CSLib unimodal model on that type. -/
theorem mem_K (h : Derivable Axioms.K (Formula.ofProposition phi)) :
    phi ∈ Logic.Modal.Unimodal.K World Atom :=
  mem_logic_of_valid fun _ _ _ ↦ h.valid_K

/-- **Soundness for CSLib's T.** Let $\varphi$ be a CSLib unimodal proposition. If the translation
of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of the Hilbert system T, then, for
every type of worlds, $\varphi$ belongs to CSLib's modal logic T: it holds at every world of every
CSLib unimodal model on that type whose accessibility relation is reflexive. -/
theorem mem_T (h : Derivable Axioms.T (Formula.ofProposition phi)) :
    phi ∈ Logic.Modal.Unimodal.T World Atom :=
  mem_logic_of_valid fun _ hm _ ↦ h.valid_T (fun w ↦ hm.refl w)

/-- **Soundness for CSLib's S4.** Let $\varphi$ be a CSLib unimodal proposition. If the translation
of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of the Hilbert system S4, then, for
every type of worlds, $\varphi$ belongs to CSLib's modal logic S4: it holds at every world of every
CSLib unimodal model on that type whose accessibility relation is reflexive and transitive. -/
theorem mem_S4 (h : Derivable Axioms.S4 (Formula.ofProposition phi)) :
    phi ∈ Logic.Modal.Unimodal.S4 World Atom :=
  mem_logic_of_valid fun _ hm _ ↦
    h.valid_S4 (fun w ↦ hm.1.refl w) (fun h₁ h₂ ↦ hm.2.trans _ _ _ h₁ h₂)

/-- **Soundness for CSLib's S5.** Let $\varphi$ be a CSLib unimodal proposition. If the translation
of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of the Hilbert system S5, then, for
every type of worlds, $\varphi$ belongs to CSLib's modal logic S5: it holds at every world of every
CSLib unimodal model on that type whose accessibility relation $R$ is reflexive, transitive and
Euclidean ($R(w, u)$ and $R(w, v)$ imply $R(u, v)$). -/
theorem mem_S5 (h : Derivable Axioms.S5 (Formula.ofProposition phi)) :
    phi ∈ Logic.Modal.Unimodal.S5 World Atom := by
  refine mem_logic_of_valid fun m hm _ ↦ h.valid_S5 ?_
  obtain ⟨hRefl, hTrans, hEucl⟩ := hm
  have symm : ∀ {a b}, m.rel a b → m.rel b a := fun hab ↦ hEucl.rightEuclidean hab (hRefl.refl _)
  exact ⟨fun w ↦ hRefl.refl w, symm, fun h₁ h₂ ↦ hTrans.trans _ _ _ h₁ h₂⟩

end Derivable

end Modal
end Cslib

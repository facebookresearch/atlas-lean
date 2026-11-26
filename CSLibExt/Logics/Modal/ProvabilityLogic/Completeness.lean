/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.Basic
import CSLibExt.Logics.Modal.FiniteModelProperty

/-!
# Provability logic GL on finite strict partial orders

Established results about GL over the Hilbert system `Derivable Axioms.GL` of
`CSLibExt.Logics.Modal.ProvabilityLogic.Basic`.

* `derivable_GL_iff_finite`: Segerberg's completeness theorem for finite strict partial orders.
-/

public section

namespace Cslib.Modal

universe u

variable {Atom : Type u}

namespace derivable_GL_iff_finite

variable {W : Type*} (M : KripkeModel W Atom) [DecidableEq Atom] (phi : Formula Atom)

/-- Take the strict part of the Lemmon relation on the realized subformula types. -/
private noncomputable def strictModel : KripkeModel {s // s ∈ filtrationWorlds M phi} Atom where
  nonempty_world := (filtration M phi).nonempty_world
  valuation s p := Formula.atom p ∈ s.val
  rel s t := (s.val, t.val) ∈ lemmonRel M phi ∧ (t.val, s.val) ∉ lemmonRel M phi

private theorem strictModel_trans {s t r} (hst : (strictModel M phi).rel s t)
    (htr : (strictModel M phi).rel t r) : (strictModel M phi).rel s r :=
  ⟨finTrans_lemmonRel M phi _ s.2 _ t.2 _ r.2 hst.1 htr.1,
    fun hrs ↦ htr.2 (finTrans_lemmonRel M phi _ r.2 _ s.2 _ t.2 hrs hst.1)⟩

/-- If Löb's axiom holds, the strict part still has enough successors to test every box. -/
private theorem satisfies_strictModel_iff
    (trans : ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c)
    (lob : ∀ a, M.Valid (Formula.axiomLob a))
    {psi : Formula Atom} (hpsi : psi ∈ phi.sub) (w : W) :
    (strictModel M phi).Satisfies ⟨_, subType_mem_filtrationWorlds M phi w⟩ psi ↔
      M.Satisfies w psi := by
  induction psi generalizing w with
  | atom p =>
    exact (mem_subType M phi).trans (and_iff_right hpsi)
  | bot => rfl
  | imp a b iha ihb =>
    rw [KripkeModel.satisfies_imp, KripkeModel.satisfies_imp,
      iha (Formula.mem_sub_of_imp_mem_left hpsi), ihb (Formula.mem_sub_of_imp_mem_right hpsi)]
  | box a ih =>
    have ha := Formula.mem_sub_of_box_mem hpsi
    have hR := isFiltration_lemmonRel M phi trans
    constructor
    · intro hall
      -- Löb reduces the goal to checking a at successors where □a already holds.
      apply lob a w
      intro v hwv hvbox
      by_cases hback : (subType M phi v, subType M phi w) ∈ lemmonRel M phi
      · -- A reverse Lemmon edge carries □a back to w, forcing a at v.
        have hboxes := (mem_lemmonRel M phi (subType_mem_filtrationWorlds M phi v)
          (subType_mem_filtrationWorlds M phi w)).mp hback a hpsi
        have hwbox := (hboxes ((mem_subType M phi).mpr ⟨hpsi, hvbox⟩)).1
        exact ((mem_subType M phi).mp hwbox).2 v hwv
      · exact (ih ha v).mp (hall ⟨_, subType_mem_filtrationWorlds M phi v⟩ ⟨hR.min hwv, hback⟩)
    · intro hbox t hwt
      obtain ⟨v, hv⟩ := exists_subType_eq M phi t.2
      have ht : t = ⟨_, subType_mem_filtrationWorlds M phi v⟩ := Subtype.ext hv.symm
      subst t
      exact (ih ha v).mpr (hR.max hwt.1 hpsi hbox)

end derivable_GL_iff_finite

open derivable_GL_iff_finite in
/-- **Completeness of GL for finite strict partial orders** (Segerberg 1971; also de Jongh and
Kripke). A formula is a theorem of GL iff it is valid in every Kripke model on a finite set of
worlds whose relation is transitive and irreflexive (Verbrugge, "Provability logic", *Stanford
Encyclopedia of Philosophy*, current edition, §3.2, which also records completeness for finite
transitive irreflexive trees). The direction from left to right is the proved
`Derivable.valid_GL_of_finite`. -/
theorem derivable_GL_iff_finite (phi : Formula Atom) :
    Derivable Axioms.GL phi ↔
      ∀ (W : Type u) [Finite W] (M : KripkeModel W Atom),
        (∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) → (∀ w, ¬M.rel w w) → M.Valid phi := by
  classical
  refine ⟨fun h _ _ _ trans irrefl ↦ h.valid_GL_of_finite trans irrefl, fun h ↦ ?_⟩
  let M := canonicalModel (not_derivable_bot_GL (Atom := Atom))
  have trans : ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c :=
    fun hab hbc ↦ CanonicalWorld.rel_trans Derivable.axiomFour_GL hab hbc
  have lob (a : Formula Atom) : M.Valid (Formula.axiomLob a) := fun w ↦
    (satisfies_canonical_iff _ w _).mpr
      (MaximalConsistent.mem_of_derivable w.2 (.extra (Axioms.axiomLob_mem_GL a)))
  apply deduces_empty_iff.mp (Deduces.of_canonicalModel not_derivable_bot_GL ?_)
  intro w _
  apply (satisfies_strictModel_iff M phi trans lob (Formula.mem_sub_self phi) w).mp
  exact h _ (strictModel M phi) (strictModel_trans M phi) (fun _ hself ↦ hself.2 hself.1) _

end Cslib.Modal

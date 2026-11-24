/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.Basic
public import CSLibExt.Logics.Modal.Substitution

@[expose] public section

/-!
# Fixed points in the provability logic GL

The de Jongh–Sambin fixed point theorem says that self-reference is eliminable in GL: if every
occurrence of the atom `p` in `A(p)` lies under a box, then there is a formula `H` without `p`,
whose atoms occur in `A`, with `GL ⊢ H ↔ A(H)`; and any two such fixed points are GL-provably
equivalent. This file proves

* `Derivable.fixedPoint_unique_GL` (**uniqueness of fixed points**): for `A` modalised in `p` and
  arbitrary formulas `ψ`, `χ`, GL proves `⊡(ψ ↔ A(ψ)) → ⊡(χ ↔ A(χ)) → (ψ ↔ χ)`, where `⊡θ` is
  `θ ∧ □θ` (written as curried hypotheses); this internal form implies the uniqueness rule stated
  in the reference below;
* `Derivable.fixedPoint_GL_of_box` (**existence, one boxed occurrence**): if `A(p) = B(□C(p))`,
  that is `A = B[r := □C]` with `p` not occurring in `B`, then `H = B(□C(B(⊤)))` satisfies
  `GL ⊢ H ↔ A(H)`. This covers `¬□p` (fixed point `¬□¬⊤`, equivalent to `¬□⊥`), `□p`,
  `□(p → q)` and `□¬p`. The explicit formula is derived here.

The general existence theorem is proved in `ProvabilityLogic/FixedPointExistence.lean`.

Both proofs are GL-derivations obtained from finitely many instances of Löb's axiom and the
completeness of K4 (`derivable_K4_iff`): the K4 part is checked on transitive Kripke models, where
truth of a formula at a world depends only on the valuation on the worlds it can see
(`KripkeModel.satisfies_congr` in `CSLibExt.Logics.Modal.Substitution`).

## References

* R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy* (current edition),
  §2.2 (statement of the fixed point theorem; uniqueness as a rule). It attributes the theorem to
  de Jongh and Sambin (1975) and lists proofs by Smoryński (1985), Boolos (1993), Sambin and
  Valentini (1982), Lindström (2006) and Reidhaar-Olson (1990); none of these was read here.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

namespace Formula

/-- **Atom occurring only under a box.** `φ.Modalised p` holds when every occurrence of the atom
`p` in `φ` lies in the scope of some `□`; this is the hypothesis of the de Jongh–Sambin fixed
point theorem (Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §2.2). -/
def Modalised (p : Atom) : Formula Atom → Prop
  | .atom q => q ≠ p
  | .bot => True
  | .imp phi psi => Modalised p phi ∧ Modalised p psi
  | .box _ => True

end Formula

namespace KripkeModel

variable {World : Type v}

/-- **A modalised atom is read only at visible worlds.** If `p` occurs in `φ` only under boxes,
and `S` and `S'` agree on a relation-closed set `U` containing every world seen from `w`, then
reinterpreting `p` as `S` or as `S'` gives `φ` the same truth value at `w`. -/
theorem satisfies_updateAtom_congr_of_modalised [DecidableEq Atom] (M : KripkeModel World Atom)
    {p : Atom} {phi : Formula Atom} (hphi : phi.Modalised p) {S S' : World → Prop}
    (U : Set World) (hU : ∀ v ∈ U, ∀ u, M.rel v u → u ∈ U) (w : World)
    (hw : ∀ u, M.rel w u → u ∈ U) (hS : ∀ v ∈ U, (S v ↔ S' v)) :
    (M.updateAtom p S).Satisfies w phi ↔ (M.updateAtom p S').Satisfies w phi := by
  have hval : ∀ (theta : Formula Atom), ∀ v ∈ U, ∀ q ∈ theta.atoms,
      ((M.updateAtom p S).valuation v q ↔ (M.updateAtom p S').valuation v q) := by
    intro _ v hv q _
    by_cases h : q = p
    · simp only [updateAtom, h, ↓reduceIte]
      exact hS v hv
    · simp only [updateAtom, h, ↓reduceIte]
  induction phi with
  | atom q =>
    simp only [Formula.Modalised] at hphi
    simp [updateAtom, hphi]
  | bot => exact Iff.rfl
  | imp phi chi ih₁ ih₂ =>
    simp only [satisfies_imp]
    exact imp_congr (ih₁ hphi.1) (ih₂ hphi.2)
  | box phi _ =>
    simp only [satisfies_box]
    exact forall_congr' fun u ↦ imp_congr_right fun hwu ↦
      satisfies_congr (M.updateAtom p S) (M.updateAtom p S') rfl U hU phi (hval phi) u (hw u hwu)

end KripkeModel

namespace Derivable

open KripkeModel

/-- **Modus ponens with a K4 theorem in GL.** A K4-theorem `φ → ψ` and a GL-proof of `φ` give a
GL-proof of `ψ`, since every K4 theorem is a GL theorem. -/
theorem mp_of_K4 {phi psi : Formula Atom} (hK : Derivable Axioms.K4 (.imp phi psi))
    (h : Derivable Axioms.GL phi) : Derivable Axioms.GL psi :=
  .mp (GL_of_K4 hK) h

variable [DecidableEq Atom]

/-- In a transitive model, if `ψ ↔ χ` holds at every world seen from `v`, then `A(ψ) ↔ A(χ)`
holds at `v` for every `A` in which `p` is modalised. -/
private theorem subst_iff_of_box_iff {World : Type v} (M : KripkeModel World Atom)
    (trans : ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) {A : Formula Atom} {p : Atom}
    (hA : A.Modalised p) (psi chi : Formula Atom) (v : World)
    (h : ∀ u, M.rel v u → (M.Satisfies u psi ↔ M.Satisfies u chi)) :
    M.Satisfies v (A.subst p psi) ↔ M.Satisfies v (A.subst p chi) := by
  rw [satisfies_subst, satisfies_subst]
  exact satisfies_updateAtom_congr_of_modalised M hA {u | M.rel v u}
    (fun _ hu _ h ↦ trans hu h) v (fun _ h ↦ h) h

/-- **Uniqueness of fixed points in GL.** If every occurrence of `p` in `A` is under a box, then
for all formulas `ψ` and `χ`, GL proves
`(ψ ↔ A(ψ)) → □(ψ ↔ A(ψ)) → (χ ↔ A(χ)) → □(χ ↔ A(χ)) → (ψ ↔ χ)`, i.e. any two fixed points of
`A` are equivalent under `⊡`-hypotheses. Verbrugge, "Provability logic", *Stanford Encyclopedia of
Philosophy*, §2.2, states uniqueness as a rule: if `GL ⊢ B ↔ A(B)` and `GL ⊢ C ↔ A(C)`, then
`GL ⊢ B ↔ C`. The internal form proved here is stronger and gives the rule by necessitation; it
is derived here, not quoted from a source read in this work. The derivation uses one instance of
Löb's axiom, for `ψ ↔ χ`. -/
theorem fixedPoint_unique_GL {A : Formula Atom} {p : Atom} (hA : A.Modalised p)
    (psi chi : Formula Atom) :
    Derivable Axioms.GL
      (.imp (psi.iff (A.subst p psi)) (.imp (.box (psi.iff (A.subst p psi)))
        (.imp (chi.iff (A.subst p chi)) (.imp (.box (chi.iff (A.subst p chi)))
          (psi.iff chi))))) := by
  refine mp_of_K4 ?_ (.extra (Axioms.axiomLob_mem_GL (psi.iff chi)))
  refine derivable_K4_iff.mpr fun W M trans w hl hEp hbEp hEc hbEc ↦ ?_
  simp only [Formula.axiomLob, satisfies_imp, satisfies_box, satisfies_iff] at hl hEp hbEp hEc hbEc
  simp only [satisfies_iff]
  have hstep : ∀ v, M.rel w v → (∀ u, M.rel v u → (M.Satisfies u psi ↔ M.Satisfies u chi)) →
      (M.Satisfies v psi ↔ M.Satisfies v chi) := fun v hv hb ↦ by
    rw [hbEp v hv, hbEc v hv]
    exact subst_iff_of_box_iff M trans hA psi chi v hb
  have hall := hl hstep
  rw [hEp, hEc]
  exact subst_iff_of_box_iff M trans hA psi chi w hall

/-- Semantic core of `fixedPoint_GL_of_box`: in a transitive model, if Löb's axiom for `C(B(⊤))`
holds at `w` and at every world seen from `w`, then `H ↔ A(H)` holds at `w`. -/
private theorem fixedPoint_semantic {World : Type v} (M : KripkeModel World Atom)
    (trans : ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) {B C : Formula Atom} {p r : Atom}
    (hB : p ∉ B.atoms) (w : World)
    (hL : ∀ u, (u = w ∨ M.rel w u) →
      M.Satisfies u (Formula.axiomLob (C.subst p (B.subst r .top)))) :
    M.Satisfies w ((B.subst r (.box (C.subst p (B.subst r .top)))).iff
        ((B.subst r (.box C)).subst p (B.subst r (.box (C.subst p (B.subst r .top)))))) := by
  have cone_closed : ∀ t : World, ∀ v ∈ {s | s = t ∨ M.rel t s}, ∀ u, M.rel v u →
      u ∈ {s | s = t ∨ M.rel t s} := by
    rintro t v (rfl | hv) u hvu
    · exact Or.inr hvu
    · exact Or.inr (trans hv hvu)
  -- Where `□C(B(⊤))` holds, `H` agrees with `B(⊤)` on the whole cone.
  have ha : ∀ t, M.Satisfies t (.box (C.subst p (B.subst r .top))) → ∀ s, (s = t ∨ M.rel t s) →
      (M.Satisfies s (B.subst r (.box (C.subst p (B.subst r .top)))) ↔
        M.Satisfies s (B.subst r .top)) := by
    intro t ht s hs
    rw [satisfies_subst, satisfies_subst]
    refine satisfies_congr (M.updateAtom r _) (M.updateAtom r _) (by rfl) _ (cone_closed t) B
      (fun v hv q _ ↦ ?_) s hs
    by_cases hq : q = r
    · simp only [updateAtom, hq, ↓reduceIte, satisfies_top, iff_true]
      rcases hv with rfl | hv
      · exact ht
      · exact fun x hx ↦ ht x (trans hv hx)
    · simp only [updateAtom, hq, ↓reduceIte]
  -- Hence `C(H)` agrees with `C(B(⊤))` there.
  have ha' : ∀ t, M.Satisfies t (.box (C.subst p (B.subst r .top))) →
      (M.Satisfies t (C.subst p (B.subst r (.box (C.subst p (B.subst r .top))))) ↔
        M.Satisfies t (C.subst p (B.subst r .top))) := by
    intro t ht
    rw [satisfies_subst, satisfies_subst]
    refine satisfies_congr (M.updateAtom p _) (M.updateAtom p _) (by rfl) _ (cone_closed t) C
      (fun v hv q _ ↦ ?_) t (Or.inl rfl)
    by_cases hq : q = p
    · simp only [updateAtom, hq, ↓reduceIte]
      exact ha t ht v hv
    · simp only [updateAtom, hq, ↓reduceIte]
  -- Key claim: `□C(H) ↔ □C(B(⊤))` on the cone of `w` (Löb's axiom gives `→`).
  have hK : ∀ u, (u = w ∨ M.rel w u) →
      (M.Satisfies u (.box (C.subst p (B.subst r (.box (C.subst p (B.subst r .top)))))) ↔
        M.Satisfies u (.box (C.subst p (B.subst r .top)))) := by
    intro u hu
    have hLu := hL u hu
    simp only [Formula.axiomLob, satisfies_imp, satisfies_box] at hLu
    simp only [satisfies_box]
    constructor
    · intro hb
      exact hLu fun t hut hbt ↦ (ha' t hbt).mp (hb t hut)
    · intro hD t hut
      have hDt : M.Satisfies t (.box (C.subst p (B.subst r .top))) :=
        fun x hx ↦ hD x (trans hut hx)
      exact (ha' t hDt).mpr (hD t hut)
  rw [satisfies_iff, satisfies_subst M r, satisfies_subst M p, satisfies_subst (M.updateAtom p _) r]
  refine satisfies_congr (M.updateAtom r _) ((M.updateAtom p _).updateAtom r _) (by rfl) _
    (cone_closed w) B
    (fun v hv q hq ↦ ?_) w (Or.inl rfl)
  have hqp : q ≠ p := fun h ↦ hB (h ▸ hq)
  by_cases hqr : q = r
  · subst hqr
    rw [updateAtom_valuation_self, updateAtom_valuation_self, ← satisfies_subst M p]
    exact (hK v hv).symm
  · rw [updateAtom_valuation_ne hqr, updateAtom_valuation_ne hqr, updateAtom_valuation_ne hqp]

/-- **The de Jongh–Sambin fixed point for one boxed occurrence.** Let `A(p) = B(□C(p))`, i.e.
`A = B[r := □C]`, where the atom `p` does not occur in `B`. Then `H = B(□C(B(⊤)))`, i.e.
`H = B[r := □(C[p := B[r := ⊤]])]`, is a fixed point of `A` in GL: `GL ⊢ H ↔ A(H)`. Every
occurrence of `p` in `A` lies inside the one boxed subformula `□C`, so `A` is modalised in `p`.
Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §2.2, states the
de Jongh–Sambin theorem (existence of a fixed point for every modalised `A`) and the example
`¬□p ↦ ¬□⊥`, but not this explicit formula; the formula and its proof are derived here. The
derivation uses Löb's axiom for `C(B(⊤))` and its necessitation. -/
theorem fixedPoint_GL_of_box {B C : Formula Atom} {p r : Atom} (hB : p ∉ B.atoms) :
    Derivable Axioms.GL
      ((B.subst r (.box (C.subst p (B.subst r .top)))).iff
        ((B.subst r (.box C)).subst p (B.subst r (.box (C.subst p (B.subst r .top)))))) := by
  have hL : Derivable Axioms.GL (Formula.axiomLob (C.subst p (B.subst r .top))) :=
    .extra (Axioms.axiomLob_mem_GL _)
  have hK : Derivable Axioms.K4
      (.imp (.box (Formula.axiomLob (C.subst p (B.subst r .top))))
        (.imp (Formula.axiomLob (C.subst p (B.subst r .top)))
          ((B.subst r (.box (C.subst p (B.subst r .top)))).iff
            ((B.subst r (.box C)).subst p
              (B.subst r (.box (C.subst p (B.subst r .top)))))))) := by
    refine derivable_K4_iff.mpr fun W M trans w hbl hl ↦ ?_
    refine fixedPoint_semantic M trans hB w ?_
    rintro u (rfl | hu)
    · exact hl
    · exact hbl u hu
  exact .mp (mp_of_K4 hK (.nec hL)) hL

end Derivable

end Modal
end Cslib

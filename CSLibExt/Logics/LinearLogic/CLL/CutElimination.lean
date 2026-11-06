/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-
Compatibility source port from leanprover/cslib PR944, commit
a69a43dca61ead87b6a631854de017ddaa310e08.
Original authorship and algorithm: Fabrizio Montesi, Apache 2.0.
Only imports, explicit binders, module splitting and pinned-API bridges
are adapted here. The locked CLL Proposition and Proof are reused.
-/

module

public import CSLibExt.Logics.LinearLogic.CLL.Multicut

/-! # Source cut elimination for the locked CLL calculus -/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem
open scoped CF.Proof

universe u

variable {Atom : Type u} {a b : Proposition Atom} {Γ Δ Θ : Sequent Atom}

/-- **List presentations of two summands from a supplied list.**
Present both summands using only the supplied list. -/
def Sequent.presentSumForCut [DecidableEq Atom]
    (Γ : List (Proposition Atom)) {Θ T : Sequent Atom}
    (h : (Γ : Sequent Atom) = Θ + T) :
    Σ Λ : List (Proposition Atom),
      {R : List (Proposition Atom) //
        (Λ : Sequent Atom) = Θ ∧ (R : Sequent Atom) = T} :=
  let l := Multiset.scanToList Γ Θ (by
    rw [h]
    exact Multiset.le_add_right Θ T)
  let r := Multiset.scanToList Γ T (by
    rw [h]
    exact Multiset.le_add_left T Θ)
  ⟨l.val, r.val, l.property, r.property⟩

/-- **List presentation of a tail without choosing a representative.**
Present a tail without choosing a multiset representative. -/
def Sequent.presentTailForCut [DecidableEq Atom]
    (Γ : List (Proposition Atom)) {b : Proposition Atom} {Θ : Sequent Atom}
    (h : b ::ₘ Θ = (Γ : Sequent Atom)) :
    {Λ : List (Proposition Atom) // (Λ : Sequent Atom) = Θ} :=
  Multiset.scanToList Γ Θ (by
    rw [← h]
    exact Multiset.le_cons_self Θ b)

/-- **Splitting a selected occurrence against a rule head.**
Split a selected occurrence against a rule head; the rule tail can be a multiset. -/
def Sequent.splitCutHead [DecidableEq Atom]
    {a b : Proposition Atom} {Γ : List (Proposition Atom)} {Θ : Sequent Atom}
    (h : a ::ₘ Γ = b ::ₘ Θ) :
    (a = b ∧ (Γ : Sequent Atom) = Θ) ⊕'
      {Λ : List (Proposition Atom) //
        (Γ : Sequent Atom) = b ::ₘ Λ ∧ Θ = a ::ₘ Λ} := by
  rcases Sequent.splitCons h with hp | hn
  · exact .inl hp
  · exact .inr ⟨hn.val, hn.property.2⟩

/-- **Principal shapes of a cut-free proof at the cut proposition.**
The shape of a cut-free proof when the cut proposition is in principal position.
Each constructor corresponds to a rule whose conclusion matches the cut proposition.
Axioms are handled separately in `cutStep`. Tensor carries explicit presentations
of both premises' residual contexts. -/
inductive Proof.CutPrincipal (Γ : List (Proposition Atom)) :
    Proposition Atom → Type u where
  | one (hG : (Γ : Sequent Atom) = 0) : Proof.CutPrincipal Γ 1
  | bot (p : CF⇓(Γ : Sequent Atom)) : Proof.CutPrincipal Γ ⊥
  | top : Proof.CutPrincipal Γ ⊤
  | parr {c d : Proposition Atom} (p : CF⇓(c ::ₘ d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⅋ d)
  | tensor {c d : Proposition Atom} {Λ R : List (Proposition Atom)}
      (hG : (Γ : Sequent Atom) = (Λ : Sequent Atom) + R)
      (p : CF⇓(c ::ₘ Λ)) (q : CF⇓(d ::ₘ R)) :
      Proof.CutPrincipal Γ (c ⊗ d)
  | oplus1 {c d : Proposition Atom} (p : CF⇓(c ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⊕ d)
  | oplus2 {c d : Proposition Atom} (p : CF⇓(d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⊕ d)
  | with {c d : Proposition Atom}
      (p : CF⇓(c ::ₘ Γ)) (q : CF⇓(d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c & d)
  | bang {c : Proposition Atom} (hG : Γ.allQuest) (p : CF⇓(c ::ₘ Γ)) :
      Proof.CutPrincipal Γ (!c)

/-- **Cut step exposing a principal rule or commuting the cut.**
Decompose a cut against a cut-free proof: either expose a principal rule matching
the cut proposition, or commute the cut through one inference (non-principal case).
Every recursive call is on a strictly shorter supplying derivation. -/
def Proof.cutStep [DecidableEq Atom]
    {a : Proposition Atom} (notQuest : ∀ b, a ≠ ʔb)
    {Θ : Sequent Atom} {Γ Δ : List (Proposition Atom)} (r : Proof Θ) (hr : r.IsCutFree) :
      Θ = a ::ₘ Γ →
      (q : CF⇓(a⫠ ::ₘ Δ)) →
      (∀ {Γ' : List (Proposition Atom)} (p' : CF⇓(a ::ₘ Γ')),
        p'.val.height < r.height → CF⇓((Γ' : Sequent Atom) + Δ)) →
      Proof.CutPrincipal Γ a ⊕' CF⇓((Γ : Sequent Atom) + Δ) :=
  match r, hr with
  | .ax (a := c), _ => by
      intro h q recur
      have ha : a = c ∨ a = c⫠ := by
        have ha : a ∈ ({c, c⫠} : Sequent Atom) := by
          rw [h]
          simp
        simpa using ha
      have hG : (Γ : Sequent Atom) = {a⫠} := by
        rcases ha with ha | ha
        · subst a
          apply (Multiset.cons_inj_right c).mp
          simpa using h.symm
        · subst a
          apply (Multiset.cons_inj_right c⫠).mp
          simpa only [Proposition.dual_involution, Multiset.insert_eq_cons] using
            h.symm.trans (Multiset.pair_comm c c⫠)
      exact .inr (q.rwConclusion (by
        rw [hG]
        exact (Multiset.singleton_add _ _).symm))
  | .one, _ => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        exact .inl (.one hG)
      · rcases hn with ⟨Λ, hG, hS⟩
        exact (Multiset.zero_ne_cons hS).elim
  | .top (Γ := Θ), _ => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        exact .inl .top
      · rcases hn with ⟨Λ, hG, hS⟩
        let t : CF⇓((⊤ : Proposition Atom) ::ₘ ((Λ : Sequent Atom) + Δ)) := CF.Proof.top
        exact .inr (t.rwConclusion)
  | .bot (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(Γ : Sequent Atom) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hG.symm
        exact .inl (.bot s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ Λ) := CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hS
        have hlt : s'.val.height < (Proof.bot s).height := by grind [Proof.height]
        exact .inr ((CF.Proof.bot (recur s' hlt)).rwConclusion)
  | .parr (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.parr s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ d ::ₘ Θ)))
        have hlt : s'.val.height < (Proof.parr s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ d ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
        exact .inr ((CF.Proof.parr t).rwConclusion)
  | .tensor (a := c) (b := d) (Γ := Θ) (Δ := T) s t, hst => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        rcases Sequent.presentSumForCut Γ hG with ⟨Λ, R, hL, hR⟩
        let s' : CF⇓(c ::ₘ Λ) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hL])
        let t' : CF⇓(d ::ₘ R) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ T))) (by rw [← hR])
        exact .inl (.tensor (by rw [hL, hR]; exact hG) s' t')
      · rcases hn with ⟨Κ, hG, hST⟩
        rcases Sequent.presentSumForCut (a :: Κ) hST.symm with ⟨Λ, R, hL, hR⟩
        have hsplit : a ::ₘ Κ = (Λ : Sequent Atom) + R := by
          rw [hL, hR]; exact hST.symm
        rcases Sequent.splitConsAdd hsplit with hl | hr
        · rcases hl with ⟨Λ', hLL, hK⟩
          let s' : CF⇓(a ::ₘ (c :: Λ' : List (Proposition Atom))) :=
            CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)))
          have hlt : s'.val.height < (Proof.tensor s t).height := by grind [Proof.height]
          let s'' : CF⇓(c ::ₘ ((Λ' : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
          exact .inr
            ((CF.Proof.tensor s'' (⟨t, hst.2⟩ : CF⇓(d ::ₘ T))).rwConclusion)
        · rcases hr with ⟨R', hRR, hK⟩
          let t' : CF⇓(a ::ₘ (d :: R' : List (Proposition Atom))) :=
            CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ T)))
          have hlt : t'.val.height < (Proof.tensor s t).height := by grind [Proof.height]
          let t'' : CF⇓(d ::ₘ ((R' : Sequent Atom) + Δ)) := (recur t' hlt).rwConclusion
          exact .inr
            ((CF.Proof.tensor (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)) t'').rwConclusion)
  | .oplus₁ (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        exact .inl (.oplus1 s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ)))
        have hlt : s'.val.height < (Proof.oplus₁ (b := d) s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
        exact .inr ((CF.Proof.oplus₁ (b := d) t).rwConclusion)
  | .oplus₂ (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.oplus2 s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(d ::ₘ Θ)))
        have hlt : s'.val.height < (Proof.oplus₂ (a := c) s).height := by grind [Proof.height]
        let t : CF⇓(d ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
        exact .inr ((CF.Proof.oplus₂ (a := c) t).rwConclusion)
  | .with (a := c) (b := d) (Γ := Θ) s t, hst => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        let t' : CF⇓(d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.with s' t')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)))
        let t' : CF⇓(a ::ₘ (d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ Θ)))
        have hslt : s'.val.height < (Proof.with s t).height := by grind [Proof.height]
        have htlt : t'.val.height < (Proof.with s t).height := by grind [Proof.height]
        let s'' : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hslt).rwConclusion
        let t'' : CF⇓(d ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur t' htlt).rwConclusion
        exact .inr ((CF.Proof.with s'' t'').rwConclusion)
  | .quest (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ)))
        have hlt : s'.val.height < (Proof.quest s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
        exact .inr ((CF.Proof.quest t).rwConclusion)
  | .weaken (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ Λ) := CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hS
        have hlt : s'.val.height < (Proof.weaken (a := c) s).height := by grind [Proof.height]
        exact .inr
          ((CF.Proof.weaken (a := c) (recur s' hlt)).rwConclusion)
  | .contract (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (ʔc :: ʔc :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(ʔc ::ₘ ʔc ::ₘ Θ)))
        have hlt : s'.val.height < (Proof.contract s).height := by grind [Proof.height]
        let t : CF⇓(ʔc ::ₘ ʔc ::ₘ ((Λ : Sequent Atom) + Δ)) := (recur s' hlt).rwConclusion
        exact .inr ((CF.Proof.contract t).rwConclusion)
  | .bang (a := c) (Γ := Θ) hS s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        have hGm : Sequent.allQuest (Γ : Sequent Atom) := by
          rw [hG]
          exact hS
        have hGl : Γ.allQuest := by
          simpa only [Sequent.allQuest_coe] using hGm
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        exact .inl (.bang hGl s')
      · rcases hn with ⟨Λ, hG, htail⟩
        have hf : False := by
          have ha : a ∈ Θ := by rw [htail]; simp
          obtain ⟨b, hb⟩ := Sequent.exists_quest_of_mem_allQuest hS ha
          exact notQuest b hb
        exact hf.elim
  | .cut _ _, h => nomatch h


/-- **Cut admissibility for a bang proposition.**
Cut a bang proposition by commuting through its supplying proof to an axiom or promotion.
At promotion, delegates to `questMulticut` with one selected occurrence. -/
def Proof.bangCutAdm [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf (!a)))
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓((!a) ::ₘ Γ)) (q : CF⇓(ʔ(a⫠) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  let recur {Γ' : List (Proposition Atom)}
      (p' : CF⇓((!a) ::ₘ Γ')) (hlt : p'.val.height < p.val.height) :
      CF⇓((Γ' : Sequent Atom) + Δ) :=
    Proof.bangCutAdm cutSmaller p' q
  rcases Proof.cutStep (a := !a) (by intro b hb; cases hb)
      p.val p.property rfl q recur with v | r
  · match v with
    | .bang hG p0 =>
        exact Proof.questMulticut (a := a) (n := 1) cutSmaller hG p0
          (q.rwConclusion rfl)
  · exact r
termination_by p.val.height
decreasing_by assumption

/-- **Question-mark cut via the bang case, duality and exchange.**
Reverse the exponential cut orientation using `bangCutAdm`, duality, and exchange.
This is a wrapper, not a recursive call that swaps premises at the same measure. -/
def Proof.questCutAdm [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf (ʔa)))
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(ʔa ::ₘ Γ)) (q : CF⇓((!(a⫠)) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  have hsize : sizeOf (!(a⫠)) = sizeOf (ʔa) := by
    simp
  let cutSmaller' : CutAdmissibleBelow Atom (sizeOf (!(a⫠))) :=
    fun {b} hb => cutSmaller (a := b) (by simpa only [hsize] using hb)
  let p' : CF⇓(ʔ((a⫠)⫠) ::ₘ Γ) := p.rwConclusion (by simp [Proposition.dual_involution a])
  exact (Proof.bangCutAdm (a := a⫠) cutSmaller' q p').rwConclusion

open scoped Proposition

/-- **Reduction of a cut between matching principal rules.**
Reduce a pair of principal rules whose conclusions match the cut proposition.
Every recursive call is on a proper subproposition of the original cut proposition,
so termination is guaranteed by proposition size. -/
def Proof.cutPrincipal {a : Proposition Atom} (cutSmaller : CutAdmissibleBelow Atom (sizeOf a))
    {Γ Δ : List (Proposition Atom)}
  (vp : Proof.CutPrincipal Γ a) (vq : Proof.CutPrincipal Δ a⫠) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  match (generalizing := true) vp, vq with
  | .one hG, .bot q0 => q0.rwConclusion (by simp [hG])
  | .bot p0, .one hD => p0.rwConclusion (by simp [hD])
  | .top, vq => nomatch vq
  | .bang _ _, vq => nomatch vq
  | .tensor (c := c) (d := d) (Λ := Λ) (R := R) hG p1 p2, .parr q0 => by
      have hc : sizeOf c < sizeOf (c ⊗ d) := by grind
      have hd : sizeOf d < sizeOf (c ⊗ d) := by grind
      let t := cutSmaller (a := c) hc (Γ := Λ) (Δ := d⫠ :: Δ) p1 q0
      let t' : CF⇓(d⫠ ::ₘ (Λ ++ Δ : List (Proposition Atom))) := t.rwConclusion
      let u := cutSmaller (a := d) hd (Γ := R) (Δ := Λ ++ Δ) p2 t'
      exact u.rwConclusion
  | .parr (c := c) (d := d) p0,
      .tensor (Λ := Λ) (R := R) hD q1 q2 => by
      have hc : sizeOf c < sizeOf (c ⅋ d) := by grind
      have hd : sizeOf d < sizeOf (c ⅋ d) := by grind
      let t := cutSmaller (a := c) hc (Γ := d :: Γ) (Δ := Λ) p0 q1
      let t' : CF⇓(d ::ₘ (Γ ++ Λ : List (Proposition Atom))) := t.rwConclusion
      let u := cutSmaller (a := d) hd (Γ := Γ ++ Λ) (Δ := R) t' q2
      exact u.rwConclusion
  | .oplus1 (c := c) (d := d) p0, .with q1 _ =>
      cutSmaller (a := c) (by grind) p0 q1
  | .oplus2 (c := c) (d := d) p0, .with _ q2 =>
      cutSmaller (a := d) (by grind) p0 q2
  | .with (c := c) (d := d) p1 _, .oplus1 q0 =>
      cutSmaller (a := c) (by grind) p1 q0
  | .with (c := c) (d := d) _ p2, .oplus2 q0 =>
      cutSmaller (a := d) (by grind) p2 q0

/-- **Cut admissibility for non-exponential propositions.**
Cut admissibility for non-exponential propositions: uses height induction on the
sum of premise heights, with commuting cases for non-principal rules.
Only callable when neither `a` nor `a⫠` is a question mark. -/
def Proof.cutAdmNonExponential [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf a))
    (notQuest : ∀ b, a ≠ ʔb)
    (dualNotQuest : ∀ b, a⫠ ≠ ʔb) : CutAdmissibleAt a := by
  intro Γ Δ p q
  let recurLeft {Γ' : List (Proposition Atom)}
      (p' : CF⇓(a ::ₘ Γ')) (hlt : p'.val.height < p.val.height) :
      CF⇓((Γ' : Sequent Atom) + Δ) :=
    Proof.cutAdmNonExponential cutSmaller notQuest dualNotQuest p' q
  rcases Proof.cutStep notQuest p.val p.property rfl q recurLeft with vp | r
  · let p' : CF⇓((a⫠)⫠ ::ₘ Γ) :=
      p.rwConclusion (by simp [Proposition.dual_involution a])
    let recurRight {Δ' : List (Proposition Atom)}
      (q' : CF⇓(a⫠ ::ₘ Δ')) (hlt : q'.val.height < q.val.height) :
        CF⇓((Δ' : Sequent Atom) + Γ) :=
      (Proof.cutAdmNonExponential cutSmaller notQuest dualNotQuest p q').rwConclusion
    rcases Proof.cutStep dualNotQuest q.val q.property rfl p' recurRight with vq | r
    · exact Proof.cutPrincipal cutSmaller vp vq
    · exact r.rwConclusion
  · exact r
termination_by Γ Δ p q => p.val.height + q.val.height
decreasing_by all_goals lia

/-- **Proposition-size induction step for cut admissibility.**
The proposition-size induction step for cut admissibility.
Dispatches to `bangCutAdm`, `questCutAdm`, or `cutAdmNonExponential` depending on
the top-level connective. -/
def Proof.cutAdmOfSmaller [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf a)) : CutAdmissibleAt a := by
  cases a <;> first
    | exact Proof.bangCutAdm cutSmaller
    | exact Proof.questCutAdm cutSmaller
    | exact Proof.cutAdmNonExponential cutSmaller
        (by intro b hb; cases hb)
        (by intro b hb; cases hb)

/-- **Core cut admissibility procedure on list sequents.**
The core cut admissibility implementation: given decidable atom equality and explicit
list sequents, combine cut-free proofs of dual distinguished propositions into a cut-free
proof of the sum of their residual sequents. Recurses on proposition size. -/
def Proof.cutAdmImpl {a : Proposition Atom} [DecidableEq Atom]
    {Γ Δ : List (Proposition Atom)}
  (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  Proof.cutAdmOfSmaller (fun {c} _hc {Γ Δ} p' q' => Proof.cutAdmImpl (a := c) p' q') p q
termination_by sizeOf a
decreasing_by exact _hc

/-- **Cut admissibility for cut-free classical linear logic proofs.**
Public entry point for cut admissibility: given cut-free proofs of `a ::ₘ Γ` and
`a⫠ ::ₘ Δ`, produce a cut-free proof of `(Γ : Sequent) + Δ`. -/
def Proof.cutAdm [DecidableEq Atom] {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) : CF⇓((Γ : Sequent Atom) + Δ) := cutAdmImpl p q

/-- **Cut elimination by structural recursion on the proof.**
Compute cut-free proofs by structural recursion on the original (possibly
non-cut-free) proof. Each case recursively normalises the premises, then uses
`cutAdm` at each cut. The list `Γ` is the explicit sequent for the current subgoal. -/
def Proof.cutElimAux [DecidableEq Atom] {Θ : Sequent Atom} (r : Proof Θ) :
    ∀ (Γ : List (Proposition Atom)), Θ = (Γ : Sequent Atom) → CF⇓(Γ : Sequent Atom) :=
  match r with
  | .ax (a := c) => fun Γ h =>
      (CF.Proof.ax (a := c)).rwConclusion h
  | .one => fun Γ h =>
      (CF.Proof.one (Atom := Atom)).rwConclusion h
  | .top (Γ := Θ) => fun Γ h =>
      (CF.Proof.top (Γ := Θ)).rwConclusion h
  | .bot (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s Λ hL.symm
      exact (CF.Proof.bot s').rwConclusion (by rw [hL, h])
  | .parr (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: d :: Λ) (by grind only [multiset])
      exact (CF.Proof.parr (a := c) (b := d) (Γ := Λ) s').rwConclusion
  | .tensor (a := c) (b := d) (Γ := Θ) (Δ := T) s t => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Κ, hK⟩
      rcases Sequent.presentSumForCut Κ hK with ⟨Λ, R, hL, hR⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (d :: R) (by grind only [multiset])
      exact (CF.Proof.tensor (a := c) (b := d) (Γ := Λ) (Δ := R) s' t').rwConclusion
  | .oplus₁ (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      exact (CF.Proof.oplus₁ (a := c) (b := d) (Γ := Λ) s').rwConclusion
  | .oplus₂ (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (d :: Λ) (by grind only [multiset])
      exact (CF.Proof.oplus₂ (a := c) (b := d) (Γ := Λ) s').rwConclusion
  | .with (a := c) (b := d) (Γ := Θ) s t => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (d :: Λ) (by grind only [multiset])
      exact (CF.Proof.with (a := c) (b := d) (Γ := Λ) s' t').rwConclusion
  | .quest (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      exact (CF.Proof.quest (a := c) (Γ := Λ) s').rwConclusion
  | .weaken (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s Λ hL.symm
      exact (CF.Proof.weaken (a := c) s').rwConclusion
  | .contract (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (ʔc :: ʔc :: Λ) (by grind only [multiset])
      exact (CF.Proof.contract (a := c) (Γ := Λ) s').rwConclusion
  | .bang (a := c) (Γ := Θ) hS s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      have hLq : Sequent.allQuest (Λ : Sequent Atom) := by
        rw [hL]
        exact hS
      exact (CF.Proof.bang (a := c) (Γ := Λ) hLq s').rwConclusion
  | .cut (a := c) (Γ := Θ) (Δ := T) s t => by
      intro Γ h
      rcases Sequent.presentSumForCut Γ h.symm with ⟨Λ, R, hL, hR⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (c⫠ :: R) (by grind only [multiset])
      exact (Proof.cutAdm (a := c) (Γ := Λ) (Δ := R) s' t').rwConclusion

/-- **List-based cut elimination in the source calculus.**
List-based cut elimination with the concrete list presentation explicit. -/
def Proof.cutElimList [DecidableEq Atom] {Γ : List (Proposition Atom)}
    (p : ⇓(Γ : Sequent Atom)) : CF⇓(Γ : Sequent Atom) := cutElimAux p Γ rfl

/-- **Cut elimination with a noncomputable list presentation.**
Cut elimination, using a noncomputable list presentation. -/
noncomputable def Proof.cutElim [DecidableEq Atom] {Γ : Sequent Atom} (p : ⇓Γ) : CF⇓Γ :=
  (cutElimAux p Γ.toList (Multiset.coe_toList Γ).symm).rwConclusion (Multiset.coe_toList Γ)

end Cslib.Logic.CLL

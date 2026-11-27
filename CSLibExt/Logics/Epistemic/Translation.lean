/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Announcement elimination
-/
module

public import CSLibExt.Logics.Epistemic.PublicAnnouncement

/-!
# Announcement elimination

Every formula of the announcement language without common knowledge is
equivalent to an announcement-free formula. The translation eliminates
announcements recursively: atoms and falsity become guarded by the
ambient announcement, implication distributes, knowledge keeps the
announcement guard, and successive announcements compose their
conditions with an implication-encoded conjunction. The translated
formula is itself free of announcements and common knowledge.
Background: H. P. van Ditmarsch, W. van der Hoek and B. Kooi,
*Dynamic Epistemic Logic*, Springer, 2008.
-/

@[expose] public section

namespace Cslib
namespace Epistemic

universe v w

variable {World Atom Agent : Type*} (M : Model World Atom Agent)
  {φ ψ χ : Formula Atom Agent} {w : World}

private theorem sat_announce_congr {World Atom Agent : Type*} (M : Model World Atom Agent)
    {α β : Formula Atom Agent} (h : ∀ v, Sat M α v ↔ Sat M β v)
    (θ : Formula Atom Agent) (w : World) :
    Sat M (.announce α θ) w ↔ Sat M (.announce β θ) w := by
  have hc := SatAt.congr (M := M) (fun v => h v) θ w
  constructor
  · intro ha hb
    exact hc.mp (ha ((h w).mpr hb))
  · intro hb ha
    exact hc.mpr (hb ((h w).mp ha))

private theorem sat_announce_true {World Atom Agent : Type*} (M : Model World Atom Agent)
    (θ : Formula Atom Agent) (w : World) :
    Sat M (.announce (.imp .bot .bot) θ) w ↔ Sat M θ w := by
  have htop : ∀ v, Sat M (.imp .bot .bot) v := fun v h => h
  have hPQ : ∀ v, Sat M (.imp .bot .bot) v ↔ True :=
    fun v => ⟨fun _ => True.intro, fun _ => htop v⟩
  have hc := (SatAt.congr (M := M) hPQ θ w).trans ((satAt_true (M := M) (ψ := θ) (w := w)))
  constructor
  · intro h
    exact hc.mp (h (htop w))
  · intro h _
    exact hc.mpr h

/-- The announcement language without common knowledge: atoms, falsity,
implication, knowledge, and announcements. -/
inductive AnnFormula (Atom : Type v) (Agent : Type w) where
  | atom (a : Atom) : AnnFormula Atom Agent
  | bot : AnnFormula Atom Agent
  | imp (φ ψ : AnnFormula Atom Agent) : AnnFormula Atom Agent
  | know (i : Agent) (φ : AnnFormula Atom Agent) : AnnFormula Atom Agent
  | announce (φ ψ : AnnFormula Atom Agent) : AnnFormula Atom Agent

/-- The embedding of the announcement language into the full formula
language. -/
def AnnFormula.toFormula : AnnFormula Atom Agent → Formula Atom Agent
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp φ.toFormula ψ.toFormula
  | .know i φ => .know i φ.toFormula
  | .announce φ ψ => .announce φ.toFormula ψ.toFormula

/-- The announcement-eliminating translation: `translate φ ψ` expresses
"after announcing `φ`, `ψ`", defined by recursion on `ψ`. Successive
announcements compose their conditions with the encoded conjunction.
When the ambient formula `φ` is free of both announcements and common
knowledge, so is the result (`translate_annCommonFree`); at the top level
the ambient formula is a tautology, which satisfies that premise, so
`translateTop` is always free of both. -/
def translate (φ : Formula Atom Agent) : AnnFormula Atom Agent → Formula Atom Agent
  | .atom a => .imp φ (.atom a)
  | .bot => .imp φ .bot
  | .imp ψ χ => .imp (translate φ ψ) (translate φ χ)
  | .know i ψ => .imp φ (.know i (translate φ ψ))
  | .announce χ ψ => translate (Formula.and φ (translate φ χ)) ψ

/-- The translation of a standalone announcement-language formula, under
the vacuous announcement `⊤`. -/
def translateTop (ψ : AnnFormula Atom Agent) : Formula Atom Agent :=
  translate (.imp .bot .bot) ψ

/-- Composition of announcements: announcing `φ` and then `χ` is
announcing `φ` together with "`χ` after `φ`". -/
theorem sat_announce_announce :
    Sat M (.announce φ (.announce χ ψ)) w ↔
      Sat M (.announce (Formula.and φ (.announce φ χ)) ψ) w := by
  have hand : ∀ v, Sat M (Formula.and φ (.announce φ χ)) v ↔
      (Sat M φ v ∧ SatAt M (fun u => Sat M φ u) χ v) := by
    intro v
    exact (sat_and (M := M) (φ := φ) (ψ := .announce φ χ) (w := v)).trans
      ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  have hc := SatAt.congr (M := M) hand ψ w
  constructor
  · intro h hθ
    obtain ⟨hφ, hχ⟩ := (hand w).mp hθ
    exact hc.mpr (h hφ hχ)
  · intro h hφ hχ
    exact hc.mp (h ((hand w).mpr ⟨hφ, hχ⟩))

private theorem sat_translate_at {World Atom Agent : Type*} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (ψ : AnnFormula Atom Agent) (w : World) :
    Sat M (translate φ ψ) w ↔ Sat M (.announce φ ψ.toFormula) w := by
  revert φ w
  induction ψ with
  | atom a =>
    intro φ w
    exact (sat_announce_atom (M := M) (a := a) (φ := φ) (w := w)).symm
  | bot =>
    intro φ w
    rfl
  | imp ψ χ ih1 ih2 =>
    intro φ w
    exact (⟨fun h ha => (ih2 φ w).mp (h ((ih1 φ w).mpr ha)),
      fun h ha => (ih2 φ w).mpr (h ((ih1 φ w).mp ha))⟩ :
      (Sat M (translate φ ψ) w → Sat M (translate φ χ) w) ↔
        (Sat M (.announce φ ψ.toFormula) w →
          Sat M (.announce φ χ.toFormula) w)).trans
      (sat_announce_imp (M := M) (φ := φ) (ψ := ψ.toFormula)
        (χ := χ.toFormula) (w := w)).symm
  | know i ψ ih =>
    intro φ w
    have hknow : Sat M (.know i (translate φ ψ)) w ↔
        Sat M (.know i (.announce φ ψ.toFormula)) w := by
      constructor
      · intro h v hr
        exact (ih φ v).mp (h v hr)
      · intro h v hr
        exact (ih φ v).mpr (h v hr)
    exact (⟨fun h => hknow.mp ∘ h, fun h => hknow.mpr ∘ h⟩ :
      (Sat M φ w → Sat M (.know i (translate φ ψ)) w) ↔
        (Sat M φ w → Sat M (.know i (.announce φ ψ.toFormula)) w)).trans
      (sat_announce_know (M := M) (φ := φ) (ψ := ψ.toFormula)
        (i := i) (w := w)).symm
  | announce χ ψ ihχ ihψ =>
    intro φ w
    have h1 : Sat M (translate φ (.announce χ ψ)) w ↔
        Sat M (.announce (Formula.and φ (translate φ χ)) ψ.toFormula) w :=
      ihψ (Formula.and φ (translate φ χ)) w
    have hcond : ∀ v, Sat M (Formula.and φ (translate φ χ)) v ↔
        Sat M (Formula.and φ (.announce φ χ.toFormula)) v := by
      intro v
      exact (sat_and (M := M) (φ := φ) (ψ := translate φ χ) (w := v)).trans
        ((and_congr Iff.rfl (ihχ φ v)).trans
          (sat_and (M := M) (φ := φ) (ψ := .announce φ χ.toFormula) (w := v)).symm)
    have h2 := sat_announce_congr M hcond ψ.toFormula w
    have h3 := (sat_announce_announce (M := M) (φ := φ) (χ := χ.toFormula)
      (ψ := ψ.toFormula) (w := w)).symm
    exact h1.trans (h2.trans h3)

/-- The translation is correct under any ambient announcement: the
translated formula holds exactly when the body holds after announcing
the condition. -/
theorem sat_translate (φ : Formula Atom Agent) (ψ : AnnFormula Atom Agent) :
    Sat M (translate φ ψ) w ↔ Sat M (.announce φ ψ.toFormula) w := by
  exact sat_translate_at M φ ψ w

/-- Every announcement-language formula is equivalent to its
translation; `translateTop_annCommonFree` shows the translation is
announcement-free. -/
theorem sat_translateTop (ψ : AnnFormula Atom Agent) :
    Sat M (translateTop ψ) w ↔ Sat M ψ.toFormula w := by
  exact (sat_translate_at M (.imp .bot .bot) ψ w).trans
    (sat_announce_true M ψ.toFormula w)

/-- Announcement- and common-knowledge-freedom of formulas. -/
def Formula.AnnCommonFree : Formula Atom Agent → Prop
  | .atom _ => True
  | .bot => True
  | .imp φ ψ => AnnCommonFree φ ∧ AnnCommonFree ψ
  | .know _ φ => AnnCommonFree φ
  | .common _ _ => False
  | .announce _ _ => False

theorem translate_annCommonFree {Atom Agent : Type*} (φ : Formula Atom Agent)
    (hφ : φ.AnnCommonFree) (ψ : AnnFormula Atom Agent) :
    (translate φ ψ).AnnCommonFree := by
  revert φ hφ
  induction ψ with
  | atom a => intro φ hφ; exact ⟨hφ, True.intro⟩
  | bot => intro φ hφ; exact ⟨hφ, True.intro⟩
  | imp ψ χ ih1 ih2 =>
    intro φ hφ
    exact ⟨ih1 φ hφ, ih2 φ hφ⟩
  | know i ψ ih =>
    intro φ hφ
    exact ⟨hφ, ih φ hφ⟩
  | announce χ ψ ih1 ih2 =>
    intro φ hφ
    exact ih2 (Formula.and φ (translate φ χ)) ⟨⟨hφ, ⟨ih1 φ hφ, True.intro⟩⟩, True.intro⟩

/-- The translated formula is itself free of announcements and common
knowledge. -/
theorem translateTop_annCommonFree (ψ : AnnFormula Atom Agent) :
    (translateTop ψ).AnnCommonFree := by
  exact translate_annCommonFree (.imp .bot .bot) ⟨True.intro, True.intro⟩ ψ


end Epistemic
end Cslib

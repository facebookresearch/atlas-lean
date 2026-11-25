/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Public announcements
-/
module

public import CSLibExt.Logics.Epistemic.Basic

/-!
# Public announcements

A public announcement of `φ` restricts attention to the `φ`-worlds,
expressed by the relativized satisfaction relation `SatAt`: knowledge steps
and common-knowledge paths stay inside the announced worlds. This file
proves the transport between relativized and ordinary satisfaction, the
reduction laws for atoms, implication, and knowledge (with the
announcement guard), and the relativized characterization of common
knowledge after an announcement (which is not a reduction law in the
formula language). Background: H. P. van Ditmarsch, W. van der Hoek and
B. Kooi, *Dynamic Epistemic Logic*, Springer, 2008; J. van Benthem,
J. van Eijck and B. Kooi, *Logics of communication and change*,
Information and Computation, 2006.
-/

@[expose] public section

namespace Cslib
namespace Epistemic

variable {World Atom Agent : Type*} (M : Model World Atom Agent)
  {φ ψ χ : Formula Atom Agent} {w : World}

/-- Worlds reachable by announced-steps are the start world or satisfy the announcement. -/
private theorem announce_reach {World Atom Agent : Type*} (M : Model World Atom Agent)
    (φ : Formula Atom Agent) (G : Set Agent) (w v : World)
    (h : Relation.ReflTransGen
      (fun a b => ∃ i ∈ G, Sat M φ b ∧ M.rel i a b) w v) :
    v = w ∨ Sat M φ v := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hStep _ =>
      obtain ⟨_, _, hPv, _⟩ := hStep
      exact Or.inr hPv

namespace SatAt

/-- Pointwise-equivalent world predicates give the same relativized
satisfaction, for every formula and world. -/
theorem congr {World Atom Agent : Type*} {M : Model World Atom Agent}
    {P Q : World → Prop} (hPQ : ∀ v, P v ↔ Q v)
    (ψ : Formula Atom Agent) (w : World) :
    SatAt M P ψ w ↔ SatAt M Q ψ w := by
  induction ψ generalizing P Q w with
  | atom _ => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hQ
        exact (ihψ hPQ w).mp (h ((ihφ hPQ w).mpr hQ))
      · intro h hP
        exact (ihψ hPQ w).mpr (h ((ihφ hPQ w).mp hP))
  | know i φ ih =>
      constructor
      · intro h v hQv hrel
        exact (ih hPQ v).mp (h v ((hPQ v).mpr hQv) hrel)
      · intro h v hPv hrel
        exact (ih hPQ v).mpr (h v ((hPQ v).mp hPv) hrel)
  | common G φ ih =>
      have hrel : (fun a b => ∃ i ∈ G, P b ∧ M.rel i a b) =
          (fun a b => ∃ i ∈ G, Q b ∧ M.rel i a b) := by
        funext a b
        apply propext
        constructor
        · rintro ⟨i, hi, hPb, hr⟩
          exact ⟨i, hi, (hPQ b).mp hPb, hr⟩
        · rintro ⟨i, hi, hQb, hr⟩
          exact ⟨i, hi, (hPQ b).mpr hQb, hr⟩
      change (∀ v, Relation.ReflTransGen
          (fun a b => ∃ i ∈ G, P b ∧ M.rel i a b) w v →
            SatAt M P φ v) ↔
        (∀ v, Relation.ReflTransGen
          (fun a b => ∃ i ∈ G, Q b ∧ M.rel i a b) w v →
            SatAt M Q φ v)
      rw [hrel]
      constructor
      · intro h v hrtc
        exact (ih hPQ v).mp (h v hrtc)
      · intro h v hrtc
        exact (ih hPQ v).mpr (h v hrtc)
  | announce φ ψ ihφ ihψ =>
      have hPred : ∀ v, (P v ∧ SatAt M P φ v) ↔ (Q v ∧ SatAt M Q φ v) :=
        fun v => by
          constructor
          · rintro ⟨hPv, hφv⟩
            exact ⟨(hPQ v).mp hPv, (ihφ hPQ v).mp hφv⟩
          · rintro ⟨hQv, hφv⟩
            exact ⟨(hPQ v).mpr hQv, (ihφ hPQ v).mpr hφv⟩
      have hC := ihψ hPred w
      constructor
      · intro h hQw
        exact hC.mp (h ((ihφ hPQ w).mpr hQw))
      · intro h hPw
        exact hC.mpr (h ((ihφ hPQ w).mp hPw))

end SatAt

/-- Unrestricted relativized satisfaction is ordinary satisfaction. -/
theorem satAt_true :
    SatAt M (fun _ => True) ψ w ↔ Sat M ψ w := by
  induction ψ generalizing w with
  | atom _ => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hs
        exact (ihψ (w := w)).mp (h ((ihφ (w := w)).mpr hs))
      · intro h hs
        exact (ihψ (w := w)).mpr (h ((ihφ (w := w)).mp hs))
  | know i φ ih =>
      constructor
      · intro h v hrel
        exact (ih (w := v)).mp (h v trivial hrel)
      · intro h v _ hrel
        exact (ih (w := v)).mpr (h v hrel)
  | common G φ ih =>
      have hrel : (fun a b => ∃ i ∈ G, True ∧ M.rel i a b) = groupRel M G := by
        funext a b
        apply propext
        constructor
        · rintro ⟨i, hi, _, hr⟩
          exact ⟨i, hi, hr⟩
        · rintro ⟨i, hi, hr⟩
          exact ⟨i, hi, trivial, hr⟩
      change (∀ v, Relation.ReflTransGen
          (fun a b => ∃ i ∈ G, True ∧ M.rel i a b) w v →
            SatAt M (fun _ => True) φ v) ↔
        (∀ v, Relation.ReflTransGen (groupRel M G) w v → Sat M φ v)
      rw [hrel]
      constructor
      · intro h v hrtc
        exact (ih (w := v)).mp (h v hrtc)
      · intro h v hrtc
        exact (ih (w := v)).mpr (h v hrtc)
  | announce φ ψ ihφ ihψ =>
      have hPred : ∀ v, (True ∧ SatAt M (fun _ => True) φ v) ↔ Sat M φ v :=
        fun v => by
          constructor
          · rintro ⟨_, h⟩
            exact (ihφ (w := v)).mp h
          · intro h
            exact ⟨trivial, (ihφ (w := v)).mpr h⟩
      have hC := SatAt.congr (M := M)
        (P := fun v => True ∧ SatAt M (fun _ => True) φ v)
        (Q := fun v => Sat M φ v) hPred ψ w
      constructor
      · intro h hs
        exact hC.mp (h ((ihφ (w := w)).mpr hs))
      · intro h hs
        exact hC.mpr (h ((ihφ (w := w)).mp hs))

/-- Announcements at atoms are implications in the original model. -/
theorem sat_announce_atom {a : Atom} :
    Sat M (.announce φ (.atom a)) w ↔ (Sat M φ w → Sat M (.atom a) w) := by
  constructor
  · intro h hh
    exact h hh
  · intro h hh
    exact h hh

/-- Announcements distribute over implication. -/
theorem sat_announce_imp :
    Sat M (.announce φ (.imp ψ χ)) w ↔
      Sat M (.imp (.announce φ ψ) (.announce φ χ)) w := by
  constructor
  · intro h hann hφ
    exact h hφ (hann hφ)
  · intro h hφ hψ
    exact h (fun _ => hψ) hφ

/-- Knowledge after an announcement: after announcing `φ`, agent `i`
knows `ψ` exactly when, if the announcement can be made, `i` knew that
`ψ` holds after the announcement. -/
theorem sat_announce_know {i : Agent} :
    Sat M (.announce φ (.know i ψ)) w ↔
      Sat M (.imp φ (.know i (.announce φ ψ))) w := by
  constructor
  · intro h hφw v hrel hφv
    exact h hφw v hφv hrel
  · intro h hφw v hφv hrel
    exact h hφw v hrel hφv

/-- After an announcement, common knowledge ranges over exactly the group
paths whose steps land in announced worlds, with the announced body
required, via the announcement, at every reached world. -/
theorem sat_announce_common {G : Set Agent} :
    Sat M (.announce φ (.common G ψ)) w ↔
      (Sat M φ w → ∀ v, Relation.ReflTransGen
        (fun a b => ∃ i ∈ G, Sat M φ b ∧ M.rel i a b) w v →
          Sat M (.announce φ ψ) v) := by
  constructor
  · intro h hφw v hrtc _
    exact h hφw v hrtc
  · intro h hφw v hrtc
    have hφv : Sat M φ v := by
      rcases announce_reach M φ G w v hrtc with rfl | hφv
      · exact hφw
      · exact hφv
    exact (h hφw v hrtc) hφv

end Epistemic
end Cslib

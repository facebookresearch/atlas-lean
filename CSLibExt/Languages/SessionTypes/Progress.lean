/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Communication
public import Mathlib.Logic.Relation

/-!
# Progress and completion for isolated finite binary sessions

The progress hypothesis is structural: both dual-typed sequential threads own
at most the same one active session channel. It excludes cross-channel waits.
No typing constructor contains a transition, progress proof or liveness oracle.
`finite_completion` constructs a finite path of actual communication steps;
`represent_steps` transports the path to the existing π reduction relation.
These are not deadlock-freedom claims for arbitrary well-typed π processes.
-/

@[expose] public section

namespace Cslib.SessionTypes

open PiCalculus

/-- All active obligations of this thread belong to one physical channel. -/
def SingleChannel (Γ : Context) (a : Nat) : Prop :=
  ∀ c, c ≠ a → Γ c = .end

/-- Opposite roles have the same active-channel support. -/
theorem SingleChannel.dual {Γ : Context} {a : Nat}
    (h : SingleChannel Γ a) : SingleChannel (dualContext Γ) a := by
  intro c hc
  simp [dualContext, h c hc, SessionType.dual]

/-- Communication on the sole session cannot create another dependency. -/
theorem SingleChannel.advance {Γ : Context} {a : Nat}
    (h : SingleChannel Γ a) (s : SessionType) :
    SingleChannel (advance Γ a s) a := by
  intro c hc
  simp [Cslib.SessionTypes.advance, hc, h c hc]

/-- A typed thread whose endpoint obligations are completed is inert. -/
theorem HasType.eq_nil_of_completed {n : Nat} {Γ : Context} {p : Proc}
    (h : HasType n Γ p) (hΓ : ∀ c, Γ c = .end) : p = .nil := by
  cases h with
  | nil => rfl
  | out ha => simp [hΓ] at ha
  | inp ha => simp [hΓ] at ha

/-- Every active endpoint of a single-channel thread is the designated one. -/
theorem SingleChannel.active_eq {Γ : Context} {a c : Nat}
    (h : SingleChannel Γ a) (hc : Γ c ≠ .end) : c = a := by
  by_cases hca : c = a
  · exact hca
  · exact False.elim (hc (h c hca))

/-- A send obligation forces a send guard on the sole active channel. -/
theorem HasType.send_shape {n a : Nat} {Γ : Context} {p : Proc}
    {s : SessionType} (h : HasType n Γ p) (hΓ : SingleChannel Γ a)
    (ha : Γ a = .send s) :
    ∃ b q, p = .out (.const a) b q ∧ b.ClosedAt n ∧
      HasType n (advance Γ a s) q := by
  cases h with
  | nil hnil => simp [hnil] at ha
  | @out _ c _ b u q hc hb hq =>
    have hca : c = a := hΓ.active_eq (by simp [hc])
    subst c
    have hsu : s = u := SessionType.send.inj (ha.symm.trans hc)
    subst u
    exact ⟨b, q, rfl, hb, hq⟩
  | @inp _ c _ u q hc hq =>
    have hca : c = a := hΓ.active_eq (by simp [hc])
    subst c
    rw [ha] at hc
    cases hc

/-- A receive obligation forces an input guard on the sole active channel. -/
theorem HasType.recv_shape {n a : Nat} {Γ : Context} {p : Proc}
    {s : SessionType} (h : HasType n Γ p) (hΓ : SingleChannel Γ a)
    (ha : Γ a = .recv s) :
    ∃ q, p = .inp (.const a) q ∧ HasType (n + 1) (advance Γ a s) q := by
  cases h with
  | nil hnil => simp [hnil] at ha
  | @out _ c _ b u q hc hb hq =>
    have hca : c = a := hΓ.active_eq (by simp [hc])
    subst c
    rw [ha] at hc
    cases hc
  | @inp _ c _ u q hc hq =>
    have hca : c = a := hΓ.active_eq (by simp [hc])
    subst c
    have hsu : s = u := SessionType.recv.inj (ha.symm.trans hc)
    subst u
    exact ⟨q, rfl, hq⟩

/-- Dual single-channel threads have either completed or can synchronize.
The single-channel hypothesis excludes cross-session dependency cycles. -/
theorem progress {Γ : Context} {a : Nat} {r : Proc × Proc}
    (hr : BinaryTyped Γ r) (hΓ : SingleChannel Γ a) :
    r = (.nil, .nil) ∨ ∃ t, CommStep r t := by
  rcases r with ⟨p, q⟩
  cases ha : Γ a with
  | «end» =>
    have he : ∀ c, Γ c = .end := by
      intro c
      by_cases hc : c = a
      · simpa [hc] using ha
      · exact hΓ c hc
    have hp := hr.1.eq_nil_of_completed he
    have hq := hr.2.eq_nil_of_completed
      (by intro c; simp [dualContext, he, SessionType.dual])
    exact Or.inl (Prod.ext hp hq)
  | send s =>
    obtain ⟨b, p', rfl, _, _⟩ := hr.1.send_shape hΓ ha
    obtain ⟨q', rfl, _⟩ := hr.2.recv_shape (s := s.dual) hΓ.dual
      (by simp [dualContext, ha, SessionType.dual])
    exact Or.inr ⟨_, .send a b p' q'⟩
  | recv s =>
    obtain ⟨p', rfl, _⟩ := hr.1.recv_shape hΓ ha
    obtain ⟨b, q', rfl, _, _⟩ := hr.2.send_shape (s := s.dual) hΓ.dual
      (by simp [dualContext, ha, SessionType.dual])
    exact Or.inr ⟨_, .recv a b p' q'⟩

/-- A completed sole protocol means both threads have reached `nil`. -/
theorem BinaryTyped.completed {Γ : Context} {a : Nat} {r : Proc × Proc}
    (hr : BinaryTyped Γ r) (hΓ : SingleChannel Γ a) (ha : Γ a = .end) :
    r = (.nil, .nil) := by
  have he : ∀ c, Γ c = .end := by
    intro c
    by_cases hc : c = a
    · simpa [hc] using ha
    · exact hΓ c hc
  exact Prod.ext (hr.1.eq_nil_of_completed he)
    (hr.2.eq_nil_of_completed
      (by intro c; simp [dualContext, he, SessionType.dual]))

/-- Paths of session communication are paths of existing π reductions. -/
theorem represent_steps {r t : Proc × Proc}
    (h : Relation.ReflTransGen CommStep r t) :
    Relation.ReflTransGen PiCalculus.Step (represent r) (represent t) := by
  induction h with
  | refl => exact .refl
  | tail h ht ih => exact .tail ih (represent_step ht)

/-- Every isolated finite dual session admits a finite communication path to
completion. This excludes recursion and is not global π normalization. -/
theorem finite_completion (s : SessionType) {Γ : Context} {a : Nat}
    {r : Proc × Proc} (hr : BinaryTyped Γ r) (hΓ : SingleChannel Γ a)
    (ha : Γ a = s) : Relation.ReflTransGen CommStep r (.nil, .nil) := by
  induction s generalizing Γ r with
  | «end» => rw [hr.completed hΓ ha]
  | send s ih =>
    rcases r with ⟨p, q⟩
    obtain ⟨b, p', rfl, hb, hp⟩ := hr.1.send_shape hΓ ha
    obtain ⟨q', rfl, hq⟩ := hr.2.recv_shape (s := s.dual) hΓ.dual
      (by simp [dualContext, ha, SessionType.dual])
    have ht : BinaryTyped (advance Γ a s) (p', subst q' b) := by
      refine ⟨hp, ?_⟩
      rw [dualContext_advance]
      exact hq.subst hb
    exact (Relation.ReflTransGen.single (.send a b p' q')).trans
      (ih ht (hΓ.advance s) (by simp [advance]))
  | recv s ih =>
    rcases r with ⟨p, q⟩
    obtain ⟨p', rfl, hp⟩ := hr.1.recv_shape hΓ ha
    obtain ⟨b, q', rfl, hb, hq⟩ := hr.2.send_shape (s := s.dual) hΓ.dual
      (by simp [dualContext, ha, SessionType.dual])
    have ht : BinaryTyped (advance Γ a s) (subst p' b, q') := by
      refine ⟨hp.subst hb, ?_⟩
      rw [dualContext_advance]
      exact hq
    exact (Relation.ReflTransGen.single (.recv a b p' q')).trans
      (ih ht (hΓ.advance s) (by simp [advance]))

end Cslib.SessionTypes

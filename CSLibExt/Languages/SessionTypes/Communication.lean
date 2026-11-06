/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Basic

/-!
# Binary communication in the existing π-calculus

The state is a pair of existing π threads. `CommStep` contracts their opposite
head guards, using precisely π substitution. `represent_step` proves this is
an existing π reduction, including the reversed output/input orientation.
Preservation is for these communication contractions, not all reductions
modulo arbitrary π structural congruence.

The data synchronization/substitution shape corresponds to §2.3 `[Com]` of
Honda, Vasconcelos and Kubo (ESOP 1998; DOI 10.1007/BFb0053567). Here the
payload is one already available passive name; there is no expression
sort/evaluation judgment or delegation rule. This is not the source's
translation into asynchronous π or its full subject-reduction theorem.
The directory `README.md` documents the precise restricted projection.
-/

@[expose] public section

namespace Cslib.SessionTypes

open PiCalculus

/-- **Binary configuration as a parallel composition.**
Embed a binary configuration without changing either process. -/
def represent (r : Proc × Proc) : Proc := .par r.1 r.2

/-- **Injectivity of the binary configuration embedding.**
The representation does not identify distinct configurations. -/
theorem represent_injective : Function.Injective represent := by
  intro r t h
  cases r
  cases t
  cases h
  rfl

/-- **Communication step of a binary configuration.**
Opposite head guards synchronize, in either endpoint orientation. -/
inductive CommStep : Proc × Proc → Proc × Proc → Prop where
  | send (a : Nat) (b : Name) (p q : Proc) :
      CommStep (.out (.const a) b p, .inp (.const a) q) (p, subst q b)
  | recv (a : Nat) (b : Name) (p q : Proc) :
      CommStep (.inp (.const a) p, .out (.const a) b q) (subst p b, q)

/-- **Session communication steps are π-calculus reductions.**
Every session communication is a reduction in the unchanged π semantics. -/
theorem represent_step {r t : Proc × Proc} (h : CommStep r t) :
    PiCalculus.Step (represent r) (represent t) := by
  cases h with
  | send a b p q => exact .commSelect (.refl _) (.refl _)
  | recv a b p q =>
    exact .cong (.par_comm _ _)
      (.commSelect (.refl _) (.refl _)) (.par_comm _ _)

/-- **Dual session typing of a binary configuration.**
Locally linear threads owning opposite roles on every channel.
Dual compatibility permits cyclic waits; it does not assert progress. -/
def BinaryTyped (Γ : Context) (r : Proc × Proc) : Prop :=
  HasType 0 Γ r.1 ∧ HasType 0 (dualContext Γ) r.2

/-- **Communication preserves binary session typing.**
Communication consumes dual heads and preserves linear residual typing;
payload substitution never changes the session context. -/
theorem CommStep.preservation {Γ : Context} {r t : Proc × Proc}
    (h : CommStep r t) (hr : BinaryTyped Γ r) :
    ∃ a s, (Γ a = .send s ∨ Γ a = .recv s) ∧
      BinaryTyped (advance Γ a s) t := by
  cases h with
  | send a b p q =>
    cases hr.1 with
    | @out _ _ _ _ s _ ha hb hp =>
      cases hr.2 with
      | @inp _ _ _ u _ hu hq =>
        have hs : s.dual = u := by
          simpa [dualContext, ha, SessionType.dual] using hu
        subst u
        refine ⟨a, s, Or.inl ha, hp, ?_⟩
        rw [dualContext_advance]
        exact hq.subst hb
  | recv a b p q =>
    cases hr.1 with
    | @inp _ _ _ s _ ha hp =>
      cases hr.2 with
      | @out _ _ _ _ u _ hu hb hq =>
        have hs : s.dual = u := by
          simpa [dualContext, ha, SessionType.dual] using hu
        subst u
        refine ⟨a, s, Or.inr ha, hp.subst hb, ?_⟩
        rw [dualContext_advance]
        exact hq

end Cslib.SessionTypes

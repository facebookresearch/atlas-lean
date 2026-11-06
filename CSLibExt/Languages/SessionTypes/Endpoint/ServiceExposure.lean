/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ServiceTemplates

/-!
# Actual canonical communication from a syntactic shared input offer

No readiness/Step field is added to the offer. Replicas are unfolded into real
copies and private wrappers use canonical constant-preserving scope extrusion.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Unguarded shared input communicates with a matching output.**
Actual input syntax supplies an ACTUAL canonical Step with any matching
shared-constant output. Payload and continuation are not finite-unrolled, and
nested private/parallel/replica wrappers are handled by existing Cong/Step. -/
theorem accept_invocation_step {s : Nat} {p : Proc} (h : AcceptIn s p) (b : Name) (c : Proc) :
    ∃ q, PiCalculus.Step (.par (.out (.const s) b c) p) q := by
  induction p generalizing b c with
  | nil => exact False.elim h
  | out => exact False.elim h
  | inp a p ih =>
    change a = .const s at h
    subst a
    exact ⟨_, PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)⟩
  | par p q ihp ihq =>
    rcases h with h | h
    · obtain ⟨r, hs⟩ := ihp h b c
      exact ⟨.par r q, PiCalculus.Step.cong (Cong.par_assoc _ _ _).symm
        (PiCalculus.Step.parL hs) (Cong.refl _)⟩
    · obtain ⟨r, hs⟩ := ihq h b c
      exact ⟨.par r p, PiCalculus.Step.cong
        (Cong.trans (Cong.par_cong (Cong.refl _) (Cong.par_comm p q))
          (Cong.par_assoc _ _ _).symm) (PiCalculus.Step.parL hs) (Cong.refl _)⟩
  | nu p ih =>
    obtain ⟨r, hs⟩ := ih h (liftName 0 b) (liftProc 0 c)
    exact ⟨.nu r, PiCalculus.Step.cong
      (Cong.trans (Cong.par_comm _ _)
        (Cong.trans (Cong.scope _ _) (Cong.nu_cong (Cong.par_comm _ _))))
      (PiCalculus.Step.nu hs) (Cong.refl _)⟩
  | repl p ih =>
    obtain ⟨r, hs⟩ := ih h b c
    exact ⟨.par r (.repl p), PiCalculus.Step.cong
      (Cong.trans (Cong.par_cong (Cong.refl _) (Cong.repl_unfold p))
        (Cong.par_assoc _ _ _).symm) (PiCalculus.Step.parL hs) (Cong.refl _)⟩
  | sum => exact False.elim h

/-- **Offered service communicates with a matching shared output.**
A persistent offered input exposes real canonical communication, including
nested templates and DONE endpoint payloads; no typing or active-key premise. -/
theorem offered_invocation_step {s : Nat} {p : Proc} (h : OfferedIn s p) (b : Name) (c : Proc) :
    ∃ q, PiCalculus.Step (.par (.out (.const s) b c) p) q :=
  accept_invocation_step (offered_accept h) b c

end Cslib.SessionTypes.Endpoint.Runtime

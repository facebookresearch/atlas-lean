/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCong

/-!
# Internally derived guarded-runtime frontier syntax

Only syntax and existing template/declaration facts occur in these predicates.
No typing, congruence, Step, readiness or progress field is stored.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Guarded frontier of guards and idle service templates.**
Unguarded frontier atoms are actual guards or existing guarded idle templates. -/
inductive GuardedFrontier (Γ : ServiceEnv) : Proc → Prop where
  | template {p : Proc} : ServiceTemplate Γ p → GuardedFrontier Γ p
  | out (a b : Name) (p : Proc) : GuardedFrontier Γ (.out a b p)
  | inp (a : Name) (p : Proc) : GuardedFrontier Γ (.inp a p)
  | par {p q : Proc} : GuardedFrontier Γ p → GuardedFrontier Γ q → GuardedFrontier Γ (.par p q)

/-- **Guarded normal form: restrictions over a guarded frontier.**
Actual private restriction towers around a guarded runtime frontier. -/
inductive GuardedNormal (Γ : ServiceEnv) : Proc → Prop where
  | frontier {p : Proc} : GuardedFrontier Γ p → GuardedNormal Γ p
  | nu {p : Proc} : GuardedNormal Γ p → GuardedNormal Γ (.nu p)

/-- **Process with no exposed output on a declared shared name.**
No exposed output is addressed to an actually declared shared constant.
Prefix bodies are not inspected. This is syntax only, not a GLOBAL premise. -/
def RequestFree (Γ : ServiceEnv) : Proc → Prop
  | .nil | .inp .. => True
  | .out a _ _ => ∀ s sig, Γ.lookup s = some sig → a ≠ .const s
  | .par p q | .sum p q => RequestFree Γ p ∧ RequestFree Γ q
  | .nu p | .repl p => RequestFree Γ p

private theorem free_lift (Γ : ServiceEnv) (k : Nat) (a : Name) :
    (∀ s sig, Γ.lookup s = some sig → liftName k a ≠ .const s) ↔
      (∀ s sig, Γ.lookup s = some sig → a ≠ .const s) := by
  constructor
  · intro h s sig hs he
    subst a
    exact h s sig hs rfl
  · intro h s sig hs he
    exact h s sig hs (liftName_injective k he)

private theorem free_swap (Γ : ServiceEnv) (k : Nat) (a : Name) :
    (∀ s sig, Γ.lookup s = some sig → swapNameAt k a ≠ .const s) ↔
      (∀ s sig, Γ.lookup s = some sig → a ≠ .const s) := by
  constructor
  · intro h s sig hs he
    subst a
    exact h s sig hs rfl
  · intro h s sig hs he
    exact h s sig hs (swapNameAt_injective k he)

/-- **Request-freeness is invariant under lifting.**
Literal shared constants are unaffected by canonical lifting. -/
theorem RequestFree.lift_iff (Γ : ServiceEnv) (k : Nat) (p : Proc) :
    RequestFree Γ (liftProc k p) ↔ RequestFree Γ p := by
  induction p generalizing k <;> simp_all [RequestFree, liftProc, free_lift]

/-- **Request-freeness is invariant under binder swapping.**
Canonical binder swap does not turn a nonshared output into a shared one. -/
theorem RequestFree.swap_iff (Γ : ServiceEnv) (k : Nat) (p : Proc) :
    RequestFree Γ (swapProc k p) ↔ RequestFree Γ p := by
  induction p generalizing k <;> simp_all [RequestFree, swapProc, free_swap]

/-- **Request-freeness is invariant under structural congruence.**
All canonical structural laws preserve absence of an exposed shared request. -/
theorem RequestFree.cong_iff {Γ : ServiceEnv} {p q : Proc} (h : Cong p q) :
    RequestFree Γ p ↔ RequestFree Γ q := by
  induction h <;> simp_all [RequestFree, RequestFree.lift_iff,
    RequestFree.swap_iff, and_assoc, and_comm]

/-- **Service templates are request-free.**
Existing guarded templates have no exposed output/request. -/
theorem ServiceTemplate.request_free {Γ : ServiceEnv} {p : Proc} (h : ServiceTemplate Γ p) :
    RequestFree Γ p := by
  induction p with
  | nil => trivial
  | out => exact False.elim h
  | inp => trivial
  | par p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | nu p ih => exact ih h
  | repl p ih => exact ih h
  | sum => exact False.elim h

/-- **Lifting preserves guarded frontiers.**
Canonical lifting maps guards and existing idle templates literally. -/
theorem GuardedFrontier.lift {Γ : ServiceEnv} {p : Proc} (h : GuardedFrontier Γ p) (k : Nat) :
    GuardedFrontier Γ (liftProc k p) := by
  induction h with
  | template ht => exact .template ((ServiceTemplate.lift_iff _ _ _).mpr ht)
  | out => exact .out _ _ _
  | inp => exact .inp _ _
  | par hp hq ihp ihq => exact .par ihp ihq

/-- **Lifting preserves guarded normal forms.**
Lifting preserves the actual unguarded private restriction tower. -/
theorem GuardedNormal.lift {Γ : ServiceEnv} {p : Proc} (h : GuardedNormal Γ p) (k : Nat) :
    GuardedNormal Γ (liftProc k p) := by
  induction h generalizing k with
  | frontier hf => exact .frontier (hf.lift k)
  | nu hp ih => exact .nu (ih (k + 1))

private theorem normalize_left {Γ : ServiceEnv} {p q : Proc} (hp : GuardedFrontier Γ p)
    (hq : GuardedNormal Γ q) : ∃ r, Cong (.par p q) r ∧ GuardedNormal Γ r := by
  induction hq generalizing p with
  | frontier hq => exact ⟨_, Cong.refl _, .frontier (.par hp hq)⟩
  | @nu q hq ih =>
    obtain ⟨r, hc, hr⟩ := ih (hp.lift 0)
    exact ⟨.nu r, Cong.trans (Cong.par_comm p (.nu q))
      (Cong.trans (Cong.scope q p)
        (Cong.nu_cong (Cong.trans (Cong.par_comm q (liftProc 0 p)) hc))), .nu hr⟩

/-- **Parallel composition preserves guarded normal forms up to congruence.**
All private restrictions on either component are extruded canonically;
no process execution or ready pair is stored in the normal form. -/
theorem GuardedNormal.parallel {Γ : ServiceEnv} {p q : Proc} (hp : GuardedNormal Γ p)
    (hq : GuardedNormal Γ q) : ∃ r, Cong (.par p q) r ∧ GuardedNormal Γ r := by
  induction hp generalizing q with
  | frontier hp => exact normalize_left hp hq
  | @nu p hp ih =>
    obtain ⟨r, hc, hr⟩ := ih (hq.lift 0)
    exact ⟨.nu r, Cong.trans (Cong.scope p q) (Cong.nu_cong hc), .nu hr⟩

/-- **Runtime-typed processes are congruent to a guarded normal form.**
ALL10 runtime rules derive a syntactic normal form internally. Replicas
remain actual guarded templates; no recursive process is erased to finite typing. -/
theorem HasType.syntax_normal {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : ∃ q, Cong p q ∧ GuardedNormal Γ q := by
  induction h with
  | nil => exact ⟨_, Cong.refl _, .frontier (.template trivial)⟩
  | outName => exact ⟨_, Cong.refl _, .frontier (.out _ _ _)⟩
  | inpName => exact ⟨_, Cong.refl _, .frontier (.inp _ _)⟩
  | outEndpoint => exact ⟨_, Cong.refl _, .frontier (.out _ _ _)⟩
  | inpEndpoint => exact ⟨_, Cong.refl _, .frontier (.inp _ _)⟩
  | invoke => exact ⟨_, Cong.refl _, .frontier (.out _ _ _)⟩
  | accept => exact ⟨_, Cong.refl _, .frontier (.inp _ _)⟩
  | serve ht => exact ⟨_, Cong.refl _, .frontier (.template ht)⟩
  | par hd hp hq ihp ihq =>
    obtain ⟨p', hc, hnp⟩ := ihp
    obtain ⟨q', hd, hnq⟩ := ihq
    obtain ⟨r, hr, hnr⟩ := hnp.parallel hnq
    exact ⟨r, Cong.trans (Cong.par_cong hc hd) hr, hnr⟩
  | nu hs hp ih =>
    obtain ⟨q, hc, hn⟩ := ih
    exact ⟨.nu q, Cong.nu_cong hc, .nu hn⟩

/-- **Guarded normal form of a typed process keeps its typing.**
Actual runtime normalization retains SAME Γ/n/Δ through the proved Cong
invariance; this theorem supplies the frontier, never the GLOBAL caller. -/
theorem HasType.frontier_normal {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : ∃ q, Cong p q ∧ HasType n Γ Δ q ∧ GuardedNormal Γ q := by
  obtain ⟨q, hc, hn⟩ := h.syntax_normal
  exact ⟨q, hc, (HasType.cong_iff hc).mp h, hn⟩

end Cslib.SessionTypes.Endpoint.Runtime

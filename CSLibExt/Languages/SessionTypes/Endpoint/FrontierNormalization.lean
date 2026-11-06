/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedCong

/-!
# Derived finite-network frontier normalization

All unguarded restrictions can be extruded around a parallel frontier. Prefix
continuations are left untouched. These predicates record syntax only; they
contain no typing, congruence, reduction or enabled-pair witness.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Parallel guard frontier.** A parallel frontier consists of nil and actual input/output guards.
No restriction is hidden under parallel; guarded continuations are unrestricted. -/
inductive GuardFrontier : Proc → Prop where
  | nil : GuardFrontier .nil
  | out (a b : Name) (p : Proc) : GuardFrontier (.out a b p)
  | inp (a : Name) (p : Proc) : GuardFrontier (.inp a p)
  | par {p q : Proc} : GuardFrontier p → GuardFrontier q → GuardFrontier (.par p q)

/-- **Frontier normal form of finite networks.**
A finite network normal form has all unguarded restrictions outside its
parallel frontier. The binder tower can have any finite depth. -/
inductive FrontierNormal : Proc → Prop where
  | frontier {p : Proc} : GuardFrontier p → FrontierNormal p
  | nu {p : Proc} : FrontierNormal p → FrontierNormal (.nu p)

/-- **Lifting preserves guard frontiers.**
Lifting maps every frontier subject, payload and guarded continuation. -/
theorem GuardFrontier.lift {p : Proc} (h : GuardFrontier p) (k : Nat) :
    GuardFrontier (liftProc k p) := by
  induction h with
  | nil => exact GuardFrontier.nil
  | out => exact GuardFrontier.out _ _ _
  | inp => exact GuardFrontier.inp _ _
  | par hp hq ihp ihq => exact GuardFrontier.par ihp ihq

/-- **Lifting preserves frontier normal form.**
Lifting preserves the restriction tower and increments cutoff under binders. -/
theorem FrontierNormal.lift {p : Proc} (h : FrontierNormal p) (k : Nat) :
    FrontierNormal (liftProc k p) := by
  induction h generalizing k with
  | frontier hf => exact FrontierNormal.frontier (hf.lift k)
  | nu hp ih => exact FrontierNormal.nu (ih (k + 1))

private theorem normalize_frontier_left {p q : Proc} (hp : GuardFrontier p)
    (hq : FrontierNormal q) : ∃ r, Cong (.par p q) r ∧ FrontierNormal r := by
  induction hq generalizing p with
  | frontier hq => exact ⟨_, Cong.refl _, FrontierNormal.frontier (GuardFrontier.par hp hq)⟩
  | @nu q hq ih =>
    obtain ⟨r, hc, hr⟩ := ih (hp.lift 0)
    exact ⟨.nu r,
      Cong.trans (Cong.par_comm p (.nu q))
        (Cong.trans (Cong.scope q p)
          (Cong.nu_cong (Cong.trans (Cong.par_comm q (liftProc 0 p)) hc))),
      FrontierNormal.nu hr⟩

/-- **Parallel composition of frontier normal forms normalizes.**
Two normalized components combine by actual canonical scope extrusion.
Every private restriction, on either side, is retained in the resulting tower. -/
theorem FrontierNormal.parallel {p q : Proc} (hp : FrontierNormal p)
    (hq : FrontierNormal q) : ∃ r, Cong (.par p q) r ∧ FrontierNormal r := by
  induction hp generalizing q with
  | frontier hp => exact normalize_frontier_left hp hq
  | @nu p hp ih =>
    obtain ⟨r, hc, hr⟩ := ih (hq.lift 0)
    exact ⟨.nu r, Cong.trans (Cong.scope p q) (Cong.nu_cong hc), FrontierNormal.nu hr⟩

/-- **Every finite linear π term has a frontier normal form.**
GENERAL normalization of every finite-linear existing π term. Prefix
bodies are not evaluated or replaced, and no complementary ready pair is assumed. -/
theorem finiteLinear_frontier_normal {p : Proc} (h : FiniteLinear p) :
    ∃ q, Cong p q ∧ FrontierNormal q := by
  induction p with
  | nil => exact ⟨_, Cong.refl _, FrontierNormal.frontier GuardFrontier.nil⟩
  | out a b p ih => exact ⟨_, Cong.refl _, FrontierNormal.frontier (GuardFrontier.out a b p)⟩
  | inp a p ih => exact ⟨_, Cong.refl _, FrontierNormal.frontier (GuardFrontier.inp a p)⟩
  | par p q ihp ihq =>
    obtain ⟨p', hp, hnp⟩ := ihp h.1
    obtain ⟨q', hq, hnq⟩ := ihq h.2
    obtain ⟨r, hr, hnr⟩ := hnp.parallel hnq
    exact ⟨r, Cong.trans (Cong.par_cong hp hq) hr, hnr⟩
  | nu p ih =>
    obtain ⟨q, hc, hn⟩ := ih h
    exact ⟨.nu q, Cong.nu_cong hc, FrontierNormal.nu hn⟩
  | repl => exact False.elim h
  | sum => exact False.elim h

/-- **Ranked-typed processes have a typed frontier normal form.**
Ranked normalization is DERIVED from typing, preserving every guard and
all external ownership while exposing all unguarded private restrictions. -/
theorem RankedType.frontier_normal {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) : ∃ q, Cong p q ∧ RankedType n Δ q ∧ FrontierNormal q := by
  obtain ⟨q, hc, hn⟩ := finiteLinear_frontier_normal h.hasType.finiteLinear
  exact ⟨q, hc, (RankedType.cong_iff hc).mp h, hn⟩

end Cslib.SessionTypes.Endpoint

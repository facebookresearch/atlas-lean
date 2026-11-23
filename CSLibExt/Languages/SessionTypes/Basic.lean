/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.PiCalculus.Scoping

/-!
# Finite sessions with unrestricted name data

This is a project-authored restricted, sort-erased model of binary sessions on
the existing π syntax, not a formalization of the complete session calculus.
It carries forward an earlier revision of this same module, development
revision `a578d21dd840e286f88b1799fee9403c902b6f24`, preserved verbatim at
`docs/provenance/pi-scoping/finite-session-basic.lean.txt`.
The directory `README.md` maps the reused and adapted declarations to that
source snapshot and identifies the later additions.
Its send/receive/end sequencing and duality are grounded in Honda, Vasconcelos
and Kubo, *Language primitives and type discipline for structured
communication-based programming*, ESOP 1998, LNCS 1381, pp. 122–138:
https://doi.org/10.1007/BFb0053567.

The primary manuscript inspected is linked in this directory's `README.md`.
Its §5, Definitions 5.1–5.3 and Figure 1 (manuscript pp. 11–13) distinguish
shared-name/data sorting from linear channel typing. The local rule mapping is:

* `HasType.nil` retains `[Inact]`'s completed `1` case as `end`, omitting the
  source's composed-channel `⊥` case.
* `HasType.out` retains `[Send]`'s channel-head advancement, but fixes one
  passive-name payload and replaces the source's sort judgment by scoping.
  Only constant subjects are admitted; this is not `[Thr]` delegation.
* `HasType.inp` retains `[Rcv]`'s continuation advancement and received-variable
  binding. Here binding increases de Bruijn depth, not a typed sorting, and
  it introduces no linear endpoint capability.

`Context` is total per-thread bookkeeping, not the source's finite partial
sorting or channel map; absence and completion are conflated as `end`, and
`HasType.finite_support` establishes finite active support for derivations.
There is no source `[Conc]` context-composition algebra. The pair judgment
uses pointwise duality rather than composing channel maps with `⊥`.

Session subjects are constant channels; received names are unrestricted
passive data that can be forwarded, not delegated linear capabilities.
Threads are sequential and protocols have no recursion or choice. Initiation,
restriction, branching, delegation, parallel typing and recursive typing rules
from the source are omitted. Equivalence to its full typing derivations is
not proved. `README.md` records each rule and representation difference.
Dual typing alone does not imply progress for threads owning several channels.
-/

@[expose] public section

namespace Cslib.SessionTypes

open PiCalculus

/-- Finite binary protocols carrying unrestricted, passive names. -/
inductive SessionType where
  | end : SessionType
  | send (next : SessionType) : SessionType
  | recv (next : SessionType) : SessionType
  deriving DecidableEq, Repr

/-- Exchange the endpoint's send and receive obligations. -/
def SessionType.dual : SessionType → SessionType
  | .end => .end
  | .send s => .recv s.dual
  | .recv s => .send s.dual

/-- Duality is an involution, including at completion. -/
@[simp] theorem SessionType.dual_dual (s : SessionType) :
    s.dual.dual = s := by
  induction s <;> simp [dual, *]

/-- Number of communication actions remaining in a finite protocol. -/
def SessionType.length : SessionType → Nat
  | .end => 0
  | .send s => s.length + 1
  | .recv s => s.length + 1

/-- Opposite endpoint roles have the same number of actions. -/
@[simp] theorem SessionType.length_dual (s : SessionType) :
    s.dual.length = s.length := by
  induction s <;> simp [dual, length, *]

/-- One linear endpoint obligation per physical channel in a thread. -/
abbrev Context := Nat → SessionType

/-- Advance just the communicating endpoint; other obligations are unchanged. -/
def advance (Γ : Context) (a : Nat) (s : SessionType) : Context :=
  fun c => if c = a then s else Γ c

/-- The opposite endpoint roles, pointwise. -/
def dualContext (Γ : Context) : Context := fun c => (Γ c).dual

/-- Advancing dual endpoints preserves pointwise compatibility. -/
theorem dualContext_advance (Γ : Context) (a : Nat) (s : SessionType) :
    dualContext (advance Γ a s) = advance (dualContext Γ) a s.dual := by
  funext c
  simp only [dualContext, advance]
  split <;> rfl

/-- Linear typing of finite sequential threads in the existing π syntax.
`nil` consumes only completed obligations. Input-bound names are unrestricted
payloads, never session subjects; there is no parallel duplication rule. -/
inductive HasType : Nat → Context → Proc → Prop where
  | nil {n : Nat} {Γ : Context} : (∀ c, Γ c = .end) → HasType n Γ .nil
  | out {n a : Nat} {Γ : Context} {b : Name} {s : SessionType} {p : Proc} :
      Γ a = .send s → b.ClosedAt n → HasType n (advance Γ a s) p →
      HasType n Γ (.out (.const a) b p)
  | inp {n a : Nat} {Γ : Context} {s : SessionType} {p : Proc} :
      Γ a = .recv s → HasType (n + 1) (advance Γ a s) p →
      HasType n Γ (.inp (.const a) p)

/-- Capture-avoiding payload substitution preserves every linear obligation,
including through nested input binders and at nonzero cutoffs. -/
theorem HasType.substProc {n k : Nat} {Γ : Context} {p : Proc} {b : Name}
    (h : HasType (n + 1) Γ p) (hb : b.ClosedAt n) (hk : k ≤ n) :
    HasType n Γ (PiCalculus.substProc b k p) := by
  induction p generalizing n k Γ b with
  | nil =>
    cases h with
    | nil hΓ => exact HasType.nil hΓ
  | out a x p ih =>
    cases h with
    | out ha hx hp =>
      exact HasType.out ha (hb.subst hx hk) (ih hp hb hk)
  | inp a p ih =>
    cases h with
    | inp ha hp =>
      exact HasType.inp ha (ih hp hb.lift (Nat.add_le_add_right hk 1))
  | par => cases h
  | nu => cases h
  | repl => cases h
  | sum => cases h

/-- Receiving a closed name preserves the residual thread's typing. -/
theorem HasType.subst {Γ : Context} {p : Proc} {b : Name}
    (h : HasType 1 Γ p) (hb : b.ClosedAt 0) :
    HasType 0 Γ (PiCalculus.subst p b) :=
  h.substProc hb (Nat.zero_le 0)

/-- A derivation has only finitely many active channel obligations: above
some bound every channel is completed. Contexts are total functions. -/
theorem HasType.finite_support {n : Nat} {Γ : Context} {p : Proc}
    (h : HasType n Γ p) : ∃ bound, ∀ c, bound ≤ c → Γ c = .end := by
  induction h with
  | nil hΓ => exact ⟨0, fun c _ => hΓ c⟩
  | @out n a Γ b s p ha hb hp ih =>
    obtain ⟨bound, hbound⟩ := ih
    refine ⟨max bound (a + 1), ?_⟩
    intro c hc
    have hca : c ≠ a := by omega
    simpa [advance, hca] using hbound c (by omega)
  | @inp n a Γ s p ha hp ih =>
    obtain ⟨bound, hbound⟩ := ih
    refine ⟨max bound (a + 1), ?_⟩
    intro c hc
    have hca : c ≠ a := by omega
    simpa [advance, hca] using hbound c (by omega)

/-- Every typed thread satisfies the shared π name/process scoping predicate.
Free session constants remain permitted; this is not ν-closedness. -/
theorem HasType.closedAt {n : Nat} {Γ : Context} {p : Proc}
    (h : HasType n Γ p) : p.ClosedAt n := by
  induction h with
  | nil => trivial
  | out _ hb _ ih => exact ⟨trivial, hb, ih⟩
  | inp _ _ ih => exact ⟨trivial, ih⟩

end Cslib.SessionTypes

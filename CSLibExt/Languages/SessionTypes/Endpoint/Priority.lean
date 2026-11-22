/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Context

/-!
# Endpoint-key dependency priorities

Only repeated use of the same endpoint key is exempt. Its opposite role is
a distinct dependency even when both roles have the same physical name.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- A guard precedes every other active owned endpoint. Transferred payloads
are included in ownership until transfer; no enabled edge is assumed. -/
def GuardMin (Δ : Context) (e : Key) (rank : Nat) : Prop :=
  ∀ d c, Δ.lookup d = some c → c.protocol.unfold ≠ .done →
    d ≠ e → rank < c.rank

/-- Owning an active peer of the guard at the same rank violates the discipline. -/
theorem guardMin_rejects_peer {Δ : Context} {e : Key} {c : Capability}
    (hc : Δ.lookup e.opposite = some c) (ha : c.protocol.unfold ≠ .done) :
    ¬ GuardMin Δ e c.rank := by
  intro h
  exact (Nat.lt_irrefl c.rank) (h e.opposite c hc ha e.opposite_ne)

/-- Collision-free rekeying preserves guard inequalities and the exact
same-endpoint exemption; it cannot silently identify the peer role. -/
theorem GuardMin.rekey {f : Key → Key} {Δ : Context} {e : Key} {k : Nat}
    (hf : Set.InjOn f {d | d ∈ Δ}) (h : GuardMin Δ e k) :
    GuardMin (Context.rekey f Δ hf) (f e) k := by
  intro d c hd ha hde
  obtain ⟨a, hac, had⟩ := Context.lookup_rekey.mp hd
  apply h a c hac ha
  intro he
  exact hde (had.symm.trans (congrArg f he))

/-- A guard with only its own endpoint is permitted to keep using that
endpoint sequentially at the same rank. Only DIFFERENT keys must rank later. -/
theorem guardMin_singleton (e : Key) (c : Capability) :
    GuardMin (Finmap.singleton e c) e c.rank := by
  intro d t hd _ hne
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hd)
  exact False.elim (hne he)

/-- Adding a genuinely completed role introduces no guard dependency.
Completion is checked by the actual unfolded protocol, not a key exemption. -/
theorem GuardMin.insert_completed {Δ : Context} {e z : Key} {k : Nat} {c : Capability}
    (h : GuardMin Δ e k) (hc : c.protocol.unfold = .done) :
    GuardMin (Δ.insert z c) e k := by
  intro d u hd ha hde
  by_cases hz : d = z
  · subst d
    rw [Finmap.lookup_insert] at hd
    cases hd
    exact False.elim (ha hc)
  · rw [Finmap.lookup_insert_of_ne _ hz] at hd
    exact h d u hd ha hde

end Cslib.SessionTypes.Endpoint

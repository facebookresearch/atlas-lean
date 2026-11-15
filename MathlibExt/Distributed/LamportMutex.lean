/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

/-!
# Lamport timestamps and mutual exclusion

Requests carry Lamport timestamps `(timestamp, pid)`, ordered
lexicographically. This module proves the core of the
Lamport/Ricart-Agrawala mutual exclusion argument: at most one
request in a set is the minimum (granted), and the Lamport
clock rules strictly increase the clock. The message protocol
producing the request set is not formalized here.
-/

@[expose] public section

/-- Lamport timestamp order on requests `(timestamp, pid)`:
lexicographic, so concurrent requests are totally ordered. A
request is granted when it is the minimum of the request set
(core of DPA-07 mutual exclusion). -/
def IsGranted (reqs : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Prop :=
  r ∈ reqs ∧ ∀ q ∈ reqs, r.1 < q.1 ∨ (r.1 = q.1 ∧ r.2 ≤ q.2)

/-- At most one request is granted: mutual exclusion. -/
theorem granted_unique (reqs : Finset (ℕ × ℕ)) (r q : ℕ × ℕ)
    (hr : IsGranted reqs r) (hq : IsGranted reqs q) : r = q := by
  have h1 := hr.2 q hq.1
  have h2 := hq.2 r hr.1
  rcases h1 with h1 | ⟨e1, l1⟩ <;> rcases h2 with h2 | ⟨e2, l2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · have hfst : r.1 = q.1 := by omega
    have hsnd : r.2 = q.2 := by omega
    exact Prod.ext hfst hsnd

/-- Lamport receive rule: the new clock exceeds both the local
clock and the message timestamp. -/
theorem lamport_receive_gt (c msg : ℕ) :
    c < max c msg + 1 ∧ msg < max c msg + 1 := by
  constructor <;> omega

/-- Lamport send/local rule: ticking strictly increases the clock. -/
theorem lamport_tick_gt (c : ℕ) : c < c + 1 := by
  exact Nat.lt_succ_self c

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK EXPOSURE IN PACKET SWITCHING NETWORKS: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(4)
(1984), 595-609, doi:10.1016/0196-6774(84)90010-5, problem DEADLOCK EXPOSURE IN PACKET
SWITCHING NETWORKS;
S. Toueg and K. Steiglitz, "Some complexity results in the design of deadlock-free packet
switching networks", SIAM Journal on Computing 10(4) (1981), 702-712, doi:10.1137/0210053.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockExposurePacketSwitching

/-- An instance: vertex count `n`, edge list, buffer counts `[b(0), …, b(n-1)]`, routes (vertex
lists), and windows `(u, v, w(u, v))`. -/
abbrev DeadlockExposurePacketSwitchingInstance :=
  ℕ × List (ℕ × ℕ) × List ℕ × List (List ℕ) × List (ℕ × ℕ × ℕ)

/-- The number `b(v)` of buffers at vertex `v`. -/
def buffers (i : DeadlockExposurePacketSwitchingInstance) (v : ℕ) : ℕ := i.2.2.1.getD v 0

/-- Route `ρ` as a list of vertices. -/
def route (i : DeadlockExposurePacketSwitchingInstance) (ρ : ℕ) : List ℕ := i.2.2.2.1.getD ρ []

/-- The source `s(r)` of route `ρ` (its first vertex). -/
def source (i : DeadlockExposurePacketSwitchingInstance) (ρ : ℕ) : ℕ := (route i ρ).headD 0

/-- The destination `d(r)` of route `ρ` (its last vertex). -/
def dest (i : DeadlockExposurePacketSwitchingInstance) (ρ : ℕ) : ℕ := (route i ρ).getLastD 0

/-- The window size `w(u, v)` (from the window list; `0` if the pair has no entry). -/
def window (i : DeadlockExposurePacketSwitchingInstance) (u v : ℕ) : ℕ :=
  ((i.2.2.2.2.find? fun e => e.1 = u ∧ e.2.1 = v).map fun e => e.2.2).getD 0

/-- Well-formedness of an instance: a simple edge list on `0, …, n - 1`; `n` positive buffer
counts; the routes are pairwise distinct (`R` is a set) and each is a simple path (nonempty,
vertices in range and pairwise distinct, consecutive vertices adjacent); the window list has
exactly one entry for each source-destination pair of a route and no other entries (window sizes
are natural numbers; the source requires positivity only of the buffer counts). -/
def WellFormed (i : DeadlockExposurePacketSwitchingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ c ∈ i.2.2.1, 0 < c) ∧
    i.2.2.2.1.Nodup ∧ (∀ r ∈ i.2.2.2.1, r ≠ [] ∧ r.Nodup ∧ (∀ v ∈ r, v < i.1) ∧
      r.IsChain fun u v => (u, v) ∈ i.2.1 ∨ (v, u) ∈ i.2.1) ∧
    (i.2.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.2.2, ∃ ρ < i.2.2.2.1.length, source i ρ = e.1 ∧ dest i ρ = e.2.1) ∧
    ∀ ρ < i.2.2.2.1.length, ∃ e ∈ i.2.2.2.2, e.1 = source i ρ ∧ e.2.1 = dest i ρ

/-- The vertex where packet `q = (ρ, k)` sits: position `k` of route `ρ`. -/
def location (i : DeadlockExposurePacketSwitchingInstance) (q : ℕ × ℕ) : ℕ :=
  (route i q.1).getD q.2 0

/-- The number of packets of `P` at vertex `v`. -/
def occupancy (i : DeadlockExposurePacketSwitchingInstance) (P : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  P.countP fun q => location i q = v

/-- The number of packets of `P` in transit from `u` to `v` (route source `u`, destination
`v`). -/
def inTransit (i : DeadlockExposurePacketSwitchingInstance) (P : List (ℕ × ℕ)) (u v : ℕ) : ℕ :=
  P.countP fun q => source i q.1 = u ∧ dest i q.1 = v

/-- `P` is a deadlock state: every packet has a route and a position on it; no vertex holds more
packets than buffers; the window bounds are obeyed; and no legal move is possible: (i) no route
can start a new packet, (ii) no packet is at its destination, (iii) no packet can advance to the
next vertex of its route. -/
def IsDeadlockState (i : DeadlockExposurePacketSwitchingInstance) (P : List (ℕ × ℕ)) : Prop :=
  (∀ q ∈ P, q.1 < i.2.2.2.1.length ∧ q.2 < (route i q.1).length) ∧
    (∀ v < i.1, occupancy i P v ≤ buffers i v) ∧
    (∀ ρ < i.2.2.2.1.length,
      inTransit i P (source i ρ) (dest i ρ) ≤ window i (source i ρ) (dest i ρ)) ∧
    (∀ ρ < i.2.2.2.1.length,
      window i (source i ρ) (dest i ρ) ≤ inTransit i P (source i ρ) (dest i ρ) ∨
        buffers i (source i ρ) ≤ occupancy i P (source i ρ)) ∧
    (∀ q ∈ P, q.2 + 1 ≠ (route i q.1).length) ∧
    ∀ q ∈ P, buffers i ((route i q.1).getD (q.2 + 1) 0) ≤
      occupancy i P ((route i q.1).getD (q.2 + 1) 0)

/-- There is a deadlock state. -/
def DeadlockExposurePacketSwitchingFeasible (i : DeadlockExposurePacketSwitchingInstance) :
    Prop :=
  ∃ P : List (ℕ × ℕ), IsDeadlockState i P

open Classical in
/-- DEADLOCK EXPOSURE IN PACKET SWITCHING NETWORKS as a decision problem over bitstrings. -/
noncomputable def deadlockExposurePacketSwitchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DeadlockExposurePacketSwitchingInstance) x with
  | some i => decide (WellFormed i ∧ DeadlockExposurePacketSwitchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeadlockExposurePacketSwitching

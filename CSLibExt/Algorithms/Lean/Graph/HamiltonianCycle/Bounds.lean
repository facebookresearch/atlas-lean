/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Correctness
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Time
import Mathlib.Data.Nat.Log

/-!
# Hamiltonian-cycle certificate size and selected-event time

This implementation represents CLRS4's ordered vertex certificate with one
fixed-width binary word per vertex. CLRS does not prescribe this codec.
These bounds concern encoded bit length, not the verifier's physical memory usage.
-/

namespace Cslib.Algorithms.Lean.Graph

/-- **Size of an accepted Hamiltonian-cycle certificate.** If the Hamiltonian-cycle verifier
accepts the bit strings $x$ and $y$, then $|y| = mw$, where $m = \lfloor \sqrt{|x|} \rfloor$ and
$w$ is the least natural number with $m \le 2^w$, and moreover $|y| \le |x|$. -/
public theorem verifyHamiltonianCycle_certificate_size (x y : Array Bool)
    (h : (verifyHamiltonianCycle x y).ret = true) :
    y.size = Nat.sqrt x.size * Nat.clog 2 (Nat.sqrt x.size) ∧ y.size ≤ x.size := by
  have hc := (verifyHamiltonianCycle_iff x y).mp h
  dsimp only at hc
  obtain ⟨hs, _, hy, _⟩ := hc
  have hw : Nat.clog 2 (Nat.sqrt x.size) ≤ Nat.sqrt x.size :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  refine ⟨hy, ?_⟩
  calc
    y.size = Nat.sqrt x.size * Nat.clog 2 (Nat.sqrt x.size) := hy
    _ ≤ Nat.sqrt x.size * Nat.sqrt x.size := Nat.mul_le_mul_left _ hw
    _ = x.size := hs

/-- **Quadratic step bound for the Hamiltonian-cycle verifier.** There is a constant $c > 0$ such
that for all bit strings $x$ and $y$, the step count of the Hamiltonian-cycle verifier on $x$ and
$y$ is at most $c\,(|x| + |y| + 1)^2$. -/
public theorem verifyHamiltonianCycle_time_le :
    ∃ c : Nat, 0 < c ∧ ∀ x y : Array Bool,
      (verifyHamiltonianCycle x y).time ≤ c * (x.size + y.size + 1) ^ 2 := by
  refine ⟨16, by decide, ?_⟩
  intro x y
  have h := verify_time_le_input x y
  have hp : x.size + y.size + 1 ≤ (x.size + y.size + 1) ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self (x.size + y.size + 1)
  have hb := Nat.mul_le_mul_left 16 hp
  omega

/-- **Step bound for accepted Hamiltonian-cycle certificates.** There is a constant $c > 0$ such
that for all bit strings $x$ and $y$ that the Hamiltonian-cycle verifier accepts, its step count
on $x$ and $y$ is at most $c\,(|x| + 1)^2$. -/
public theorem verifyHamiltonianCycle_time_le_of_accept :
    ∃ c : Nat, 0 < c ∧ ∀ x y : Array Bool,
      (verifyHamiltonianCycle x y).ret = true →
        (verifyHamiltonianCycle x y).time ≤ c * (x.size + 1) ^ 2 := by
  refine ⟨16, by decide, ?_⟩
  intro x y _h
  have h := verify_time_le_input x y
  have hp : x.size + 1 ≤ (x.size + 1) ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self (x.size + 1)
  have hb := Nat.mul_le_mul_left 16 hp
  omega

end Cslib.Algorithms.Lean.Graph

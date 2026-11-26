/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Protocols.OneExchange

/-!
# Tests for one-exchange emulation

All the interacting programs here consist of finite tables, fair bits, or bounded scans.
In the separating example the environment keeps one bit off the intermediary's wire.
-/

namespace Cslib.Crypto.OneExchange.Tests

open Cslib.Crypto.Framework
open scoped Cslib.Probability.PMF

private def api : Protocol := .table fun (x, _) => (x, false)
private def peer : Protocol := .table fun (_, u) => (u, false)
private def reversePeer : Protocol := .table fun (_, u) => (!u, false)
private def force (b : Bool) : Intermediary := .table fun _ => (b, id)
private def probe (b : Bool) : Environment := .table fun _ => ⟨b, false, fun y _ => y⟩

-- Same command to the intermediary in both cases. A simulator chosen *after* learning which
-- environment is used could just write that environment's private input to the backdoor.
example (b : Bool) : ∃ S : Intermediary, ∀ k z,
    exec api (probe b) dummy k z = exec peer (probe b) S k z := by
  exact ⟨force b, fun k z => by simp [exec, api, peer, probe, dummy, force, Program.eval]⟩

private theorem probe_gap (S : Intermediary) (k : ℕ) (z : List Bool) :
    1 ≤ advantage (exec api (probe false) dummy k z) (exec peer (probe false) S k z) +
      advantage (exec api (probe true) dummy k z) (exec peer (probe true) S k z) := by
  simp only [exec, api, peer, probe, dummy, Program.eval, PMF.pure_bind, PMF.pure_map]
  calc
    1 = advantage (PMF.pure false) (PMF.pure true) := by norm_num [advantage]
    _ ≤ _ := by rw [advantage_comm (PMF.pure true)]; exact advantage_triangle _ _ _

-- But not one fixed, even randomized, simulator for both environments. Choose the parameter
-- after taking both eventual thresholds; the two inverse-linear errors cannot add up to one.
example : ¬ Emulates api peer := by
  intro h
  obtain ⟨S, hS⟩ := h dummy
  obtain ⟨K₀, h₀⟩ := close_iff.mp (hS (probe false)) 1
  obtain ⟨K₁, h₁⟩ := close_iff.mp (hS (probe true)) 1
  let k := max K₀ K₁ + 3
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast (by dsimp [k]; omega : 3 ≤ k)
  have hb : 1 / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk
  have h₀' := h₀ k (by dsimp [k]; omega) []
  have h₁' := h₁ k (by dsimp [k]; omega) []
  have hg := probe_gap S k []
  simp only [pow_one] at h₀' h₁'
  linarith

-- Distinct protocols with different backdoor semantics: flip the bit in the simulator. The
-- dummy theorem lifts this perfect bit-law equality to *every* real intermediary.
example : Emulates reversePeer peer := by
  apply (emulates_iff_dummy _ _).2
  refine ⟨.table fun b => (!b, id), fun E => ?_⟩
  simpa [Close, exec, reversePeer, peer, dummy, Program.eval] using negligibleAdv_zero

-- A fair private coin, not a deterministic output. The output has positive distance from the
-- constant-false law even though its distinguisher is just the identity on the API bit.
private def toss : Protocol := ((Program.table fun _ => ()).seq .coin).seq <|
  .table fun y => (y, false)

example (k : ℕ) (z : List Bool) :
    dist (exec toss (probe false) dummy k z) (exec api (probe false) dummy k z) = 1 / 2 := by
  rw [← advantage_eq_dist]
  norm_num [exec, toss, api, probe, dummy, Program.eval, PMF.map_bind, PMF.pure_map,
    PMF.bind_pure, advantage]

-- Equality at a positive slack is not enough either. Some probe has distance at least 1/2,
-- no matter how much time the simulator gets or which distribution it puts on that wire.
example (δ : ℕ → ℕ) : ¬ EmulatesWithin δ (fun _ => 1 / 2) api peer := by
  intro h
  obtain ⟨S, _, hS⟩ := h dummy _ (fun _ => le_rfl)
  have h₀ := hS (probe false) 1 _ le_rfl []
  have h₁ := hS (probe true) 1 _ le_rfl []
  rw [← advantage_eq_dist] at h₀ h₁
  linarith [probe_gap S 1 []]

-- Equal output distributions do not imply equal views: two point masses on pairs with the same
-- first coordinate are as far apart as possible before the projection, identical after it.
example : let p := PMF.pure (false, false); let q := PMF.pure (false, true)
    dist p q = 1 ∧ dist (p.map Prod.fst) (q.map Prod.fst) = 0 := by
  dsimp only
  constructor
  · apply Cslib.Probability.PMF.dist_eq_one_of_disjoint_support
    simp
  · simp [PMF.pure_map]

-- Strict slack matters even for identical laws. Zero overhead cannot pay for the report either.
example (π : Protocol) {ε : ℕ → ℝ} (hε : ∀ t, 0 < ε t) : EmulatesWithin id ε π π := by
  intro A t h
  exact ⟨A, h, fun E k tE _ z => by simpa using hε tE⟩

example (π : Protocol) : ¬ EmulatesWithin id (fun _ => 0) π π := by
  intro h
  obtain ⟨S, _, hS⟩ := h dummy _ (fun _ => le_rfl)
  exact (not_lt_of_ge dist_nonneg) (hS (probe false) 0 _ le_rfl [])

example (π : Protocol) : ¬ EmulatesWithin (fun _ => 0) (fun _ => 2) π π := by
  intro h
  obtain ⟨S, hS, _⟩ := h dummy _ (fun _ => le_rfl)
  exact Nat.not_succ_le_zero _ (hS 0)

-- A bounded auxiliary scan; the same code reads only the head, and the empty tape pads false.
private noncomputable def peek : Environment :=
  ((Program.table fun _ => false).seq (.scan 1 fun _ cell => cell.getD false)).seq
    (.table fun b => ⟨b, false, fun y _ => y⟩)

example (k : ℕ) (z : List Bool) :
    exec api peek dummy k z = PMF.pure (z.head?.getD false) := by
  simp [exec, api, peek, dummy, Program.eval, scanPrefix, PMF.pure_map]

-- Cost includes all iterations even when the data path is the identity.
example (k : ℕ) : ((Program.loop Polynomial.X (.table id) : Program false Bool Bool).clock).eval k
    = k := by simp [Program.clock]

-- For each *fixed* z this discrepancy eventually disappears; the uniform comparison still fails
-- because a string of length exactly k witnesses advantage one at k. This tests the ensemble
-- comparison itself, without asserting these length tests represent all efficient observers.
private noncomputable def moving (k : ℕ) (z : List Bool) : PMF Bool := PMF.pure (decide (z.length = k))

example (z : List Bool) : NegligibleAdv (fun k => advantage (moving k z) (PMF.pure false)) := by
  apply NegligibleAdv.of_eventually_le
  intro c
  refine ⟨z.length + 1, fun k hk => ?_⟩
  have hn : z.length ≠ k := by omega
  simp [moving, hn]

example : ¬ Close moving (fun _ _ => PMF.pure false) := by
  intro h
  obtain ⟨K, hK⟩ := close_iff.mp h 1
  let k := K + 2
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (by dsimp [k]; omega : 2 ≤ k)
  have h' := hK k (by dsimp [k]; omega) (List.replicate k false)
  simp [moving, advantage] at h'
  rw [← one_div] at h'
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk
  linarith

end Cslib.Crypto.OneExchange.Tests

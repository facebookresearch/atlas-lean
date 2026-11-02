/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABForwardCharacteristic

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABForwardCharacteristic`

* `abfc_forward_characteristic_physical_envelope` on the constant data `M_n = M = 1`, `C_n = 0`,
  `J = 0`: all its hypotheses are satisfiable;
* `abfc_abig_forward_characteristic_of_exhaustion` applied under its exhaustion hypotheses.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABForwardCharacteristic

open _root_.StatMech _root_.StatMech.Sharpness

-- The characteristic bound for constant magnetizations.
example : ∃ d > 0, ∀ t ∈ Set.Icc 0 d,
    (fun _ _ : ℝ => (1 : ℝ)) (0 + t) 1 ≤
      (fun _ _ : ℝ => (1 : ℝ)) 0 (1 + 0 * ((fun _ _ : ℝ => (1 : ℝ)) 0 1 + 1) * t) :=
  abfc_forward_characteristic_physical_envelope (fun _ _ _ => 1) (fun _ _ _ => 0)
    (fun _ _ => 1) 0 0 1 le_rfl le_rfl one_pos zero_le_one
    (fun _ _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp)
    (fun _ _ _ => monotoneOn_const) (fun _ _ _ => monotoneOn_const)
    (fun _ _ _ _ _ => zero_le_one) (fun _ _ _ _ => tendsto_const_nhds)
    continuousAt_const (fun _ _ _ => differentiableAt_const _) 1 one_pos

-- The bound for the infinite-graph magnetization along an exhaustion.
example {V : Type*} [Countable V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (o : V) (J0 β h : ℝ) (hJ0 : 0 ≤ J0) (hβ : 0 ≤ β) (hh : 0 < h)
    (hJ : ∀ e, 0 ≤ J e) (hJG : ∀ x y, ¬ G.Adj x y → J s(x, y) = 0) (S : ℕ → Finset V)
    (ho : ∀ n, o ∈ S n)
    (hrow : ∀ n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n)) (abigWindowCoupling J (S n)) x ≤ J0)
    (htarget : ∀ b t : ℝ, 0 ≤ b → 0 ≤ t → ∀ n (x : S n), abigMag G J x b t ≤ abigMag G J o b t)
    (hmono : Monotone fun n => abigGhostWindow (S n))
    (hcover : ∀ F : Finset (Option V), ∃ n, F ⊆ abigGhostWindow (S n)) :
    ∃ d > 0, ∀ t ∈ Set.Icc 0 d,
      abigMag G J o (β + t) h ≤ abigMag G J o β (h + J0 * (abigMag G J o β h + 1) * t) :=
  abfc_abig_forward_characteristic_of_exhaustion G J o J0 β h hJ0 hβ hh hJ hJG S ho hrow htarget
    hmono hcover 1 one_pos

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABForwardCharacteristic

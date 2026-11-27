/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceError
import MathlibExt.NumberTheory.GobelSequenceRoots
import Mathlib.Topology.Instances.Real.Lemmas

namespace MetaMathlibExt

open Filter Topology Asymptotics

-- The original Göbel sequence has a root limit, and the error estimate applies at a
-- nonintegral exponent.
example : ∃ C : ℝ,
    Tendsto (fun n : ℕ => (gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n))
      atTop (𝓝 C) ∧
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (2 : ℝ) ^ (m + 1))
        - ((gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n) / C) ^ ((2 : ℕ) ^ n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let root (n : ℕ) := (gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)
  have hstep (n : ℕ) (hn : 1 ≤ n) :
      root (n + 1) < root n ∧ 1 < root (n + 1) :=
    gobelSequence_root_strictAnti 2 2 n le_rfl le_rfl hn
  have hanti : AntitoneOn root (Set.Ici 1) :=
    antitoneOn_nat_Ici_of_succ_le fun n hn => (hstep n hn).1.le
  have hbdd : BddBelow (root '' Set.Ici 1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact ((hstep n hn).2.trans (hstep n hn).1).le
  have hC := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici hanti hbdd
  exact ⟨_, hC, gobelSequence_error_isBigO 2 2 le_rfl le_rfl _ hC (1 / 2) (by norm_num)⟩

end MetaMathlibExt

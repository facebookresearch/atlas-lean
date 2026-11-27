/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.InnerProductSpace.MatchingPursuitConvergence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open Filter Topology
open MathlibExt.Analysis.InnerProductSpace.MatchingPursuit
open MathlibExt.Analysis.InnerProductSpace.MatchingPursuitWanted
open scoped InnerProductSpace

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private noncomputable def atom : Plane := EuclideanSpace.single 0 1

-- The first step removes a nonzero coordinate, but the orthogonal component survives.
example : (Submodule.span ℝ (Set.range fun _ : Unit => atom))ᗮ.starProjection
    (!₂[3, 4] : Plane) = !₂[0, 4] := by
  let r := residue (𝕜 := ℝ) (fun _ => atom) (!₂[3, 4] : Plane)
  have ht : Tendsto r atTop
      (𝓝 ((Submodule.span ℝ (Set.range fun _ : Unit => atom))ᗮ.starProjection
        (!₂[3, 4] : Plane))) := by
    apply tendsto_residue_starProjection_orthogonal (𝕜 := ℝ) (fun _ : Unit => atom)
      (fun _ => by simp [atom]) (α := 1) zero_lt_one le_rfl (fun _ => ())
    intro n
    simp
  have horth : ⟪atom, (!₂[0, 4] : Plane)⟫_ℝ = 0 := by
    simp [atom, EuclideanSpace.inner_single_left]
  have htail (n : ℕ) : r (n + 1) = !₂[0, 4] := by
    induction n with
    | zero =>
      change residue (𝕜 := ℝ) (fun _ => atom) (!₂[3, 4] : Plane) 1 = !₂[0, 4]
      ext i
      fin_cases i <;> simp [residue_succ, atom, EuclideanSpace.inner_single_left]
    | succ n ih =>
      change r (n + 1) - ⟪atom, r (n + 1)⟫_ℝ • atom = !₂[0, 4]
      rw [ih, horth, zero_smul, sub_zero]
  have he : r =ᶠ[atTop] fun _ => (!₂[0, 4] : Plane) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => exact (Nat.not_succ_le_zero 0 hn).elim
    | succ n => exact htail n
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace

/-!
# Delta-generated topology on real standard simplices

The real standard simplex on `Fin (n + 1)` is a continuous retract of its
finite-dimensional coordinate space. The retraction takes positive parts,
divides by their total when it exceeds one, and assigns any remaining mass
to coordinate zero. The simplex is thus delta-generated, including when `n = 0`.

Adapted from the Formal-Math development by Tsutomu Okano and Avocado.
-/

@[expose] public section

open Topology

namespace DeltaGeneratedSpace

variable {n : ℕ}

private def mass (x : Fin (n + 1) → ℝ) : ℝ := ∑ j, max (x j) 0

private noncomputable def normalize (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  max (x j) 0 / max (mass x) 1 + if j = 0 then 1 - mass x / max (mass x) 1 else 0

private theorem normalize_nonneg (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    0 ≤ normalize x j := by
  have hd : 0 < max (mass x) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmass : mass x / max (mass x) 1 ≤ 1 := (div_le_one hd).mpr (le_max_left _ _)
  unfold normalize
  exact add_nonneg (div_nonneg (le_max_right _ _) hd.le)
    (by split <;> simp only [sub_nonneg, hmass, le_rfl])

private theorem normalize_sum (x : Fin (n + 1) → ℝ) : ∑ j, normalize x j = 1 := by
  classical
  simp only [normalize, Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change mass x * (max (mass x) 1)⁻¹ + (1 - mass x * (max (mass x) 1)⁻¹) = 1
  ring

private theorem continuous_normalize : Continuous (normalize (n := n)) := by
  have hcoord (j : Fin (n + 1)) : Continuous (fun x : Fin (n + 1) → ℝ ↦ max (x j) 0) :=
    (continuous_apply j).max continuous_const
  have hmass : Continuous (mass (n := n)) :=
    continuous_finsetSum _ fun j _ ↦ hcoord j
  have hd : Continuous (fun x : Fin (n + 1) → ℝ ↦ max (mass x) 1) :=
    hmass.max continuous_const
  have hne (x : Fin (n + 1) → ℝ) : max (mass x) 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hnorm (j : Fin (n + 1)) :
      Continuous (fun x : Fin (n + 1) → ℝ ↦ max (x j) 0 / max (mass x) 1) :=
    (hcoord j).div hd hne
  have hslack : Continuous (fun x : Fin (n + 1) → ℝ ↦ 1 - mass x / max (mass x) 1) :=
    continuous_const.sub (hmass.div hd hne)
  apply continuous_pi
  intro j
  by_cases hj : j = 0
  · simp only [normalize, hj, ite_true]
    exact (hnorm 0).add hslack
  · simp only [normalize, hj, ite_false, add_zero]
    exact hnorm j

/-- The real finite standard simplex is delta-generated in its native topology. -/
instance convexStdSimplex_finSucc :
    DeltaGeneratedSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := by
  let incl (t : Convexity.StdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ := t.weights
  let retr (x : Fin (n + 1) → ℝ) : Convexity.StdSimplex ℝ (Fin (n + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm (normalize x)
      nonneg j := normalize_nonneg x j
      total := by rw [Finsupp.equivFunOnFinite_symm_sum]; exact normalize_sum x }
  have hEmb : IsEmbedding incl :=
    Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  have hCont : Continuous retr := hEmb.continuous_iff.mpr continuous_normalize
  have hFix : Function.LeftInverse retr incl := by
    intro t
    have hmass : mass (incl t) = 1 := by
      simpa only [mass, incl, max_eq_left (t.weights_nonneg _)] using t.total_of_fintype
    apply Convexity.StdSimplex.ext
    ext j
    change normalize (incl t) j = t.weights j
    simp [normalize, incl, hmass]
  exact (IsQuotientMap.of_inverse hEmb.continuous hCont hFix).isGeneratedBy

end DeltaGeneratedSpace

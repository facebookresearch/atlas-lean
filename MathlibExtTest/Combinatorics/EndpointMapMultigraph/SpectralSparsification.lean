/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EndpointMapMultigraph.SpectralSparsification
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for twice-Ramanujan multigraph sparsifiers -/

open EndpointMapMultigraph Matrix MathlibExt.GraphTheory.SpectralSparsificationWanted

namespace MathlibExtTest.EndpointMapMultigraph.SpectralSparsification

-- Five unit-weight parallel edges and one zero-weight edge join the same two vertices.
-- At d = 4 at least one positive edge must be discarded, while the total new weight is in [5, 45].
example : ∃ w' : Fin 6 → ℝ, 0 ≤ w' ∧ w' 0 = 0 ∧
    (Finset.univ.filter fun e => w' e ≠ 0).card ≤ 4 ∧ 5 ≤ ∑ e, w' e ∧ (∑ e, w' e) ≤ 45 := by
  let w (e : Fin 6) : ℝ := if e = 0 then 0 else 1
  have hw : 0 ≤ w := by intro e; dsimp [w]; split <;> norm_num
  obtain ⟨w', hw', hzero, hcard, hlo, hhi⟩ :=
    exists_twice_ramanujan_sparsifier (fun _ => (0 : Fin 2)) (fun _ => 1) hw (d := 4) (by norm_num)
  refine ⟨w', hw', hzero 0 (by simp [w]), ?_, ?_⟩
  · norm_num at hcard
    exact hcard
  · let x : Fin 2 → ℝ := ![0, 1]
    have eval (u : Fin 6 → ℝ) :
        x ⬝ᵥ (laplacian (fun _ => (0 : Fin 2)) (fun _ => 1) u *ᵥ x) = ∑ e, u e := by
      simp [dotProduct_mulVec_laplacian, x]
    have weight : ∑ e, w e = 5 := by norm_num [w, Fin.sum_univ_succ]
    have lo := hlo.dotProduct_mulVec_nonneg x
    have hi := hhi.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, eval, weight, sub_nonneg] at lo hi
    norm_num at hi
    exact ⟨lo, hi⟩

-- On one vertex every edge is a loop and the edge bound forces all reweighted edges to vanish.
example {E : Type*} [Fintype E] [DecidableEq E] {w : E → ℝ} (hw : 0 ≤ w)
    {d : ℝ} (hd : 1 < d) :
    ∃ w' : E → ℝ, w' = 0 ∧
      (laplacian (fun _ => ()) (fun _ => ()) w' -
        laplacian (fun _ => ()) (fun _ => ()) w).PosSemidef := by
  obtain ⟨w', _, _, hcard, hlo, _⟩ :=
    exists_twice_ramanujan_sparsifier (fun _ => ()) (fun _ => ()) hw hd
  refine ⟨w', ?_, hlo⟩
  simpa [Finset.filter_eq_empty_iff, funext_iff] using hcard

end MathlibExtTest.EndpointMapMultigraph.SpectralSparsification

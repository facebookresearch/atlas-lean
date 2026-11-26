/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.MirrorProx

open Finset MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.MirrorProx

/-- The linear monotone operator `F z = z` on `ℝ`, the gradient of `z² / 2`. -/
noncomputable def Fid : ℝ → ℝ →L[ℝ] ℝ := fun z => z • ContinuousLinearMap.id ℝ ℝ

-- Extragradient (Euclidean mirror-prox) on `F z = z` with `γ = 1/2` from `z_0 = 1`:
-- `w_t = z_t / 2` and `z_{t+1} = 3 z_t / 4`. The averaged leading points certify
-- `F(u) (w̄_N - u) ≤ (u - 1)² / 2 / (N / 2)` for every `u`.
example (N : ℕ) (hN : 0 < N) (u : ℝ) :
    Fid u ((N : ℝ)⁻¹ • ∑ t ∈ range N, (1 / 2 : ℝ) * (3 / 4) ^ t - u) ≤
      bregman (fun x : ℝ => x ^ 2 / 2) (fun x => x • ContinuousLinearMap.id ℝ ℝ) ((3 / 4) ^ 0) u /
        ((1 / 2) * N) := by
  refine mirror_prox_average_le (fun x : ℝ => x ^ 2 / 2) (fun x => x • ContinuousLinearMap.id ℝ ℝ)
    (L := 1) one_pos (by norm_num) (by norm_num) (Z := Set.univ) (fun x _ u _ => ?_) Fid
    (fun a _ b _ => ?_) (fun a _ b _ => ?_) (z := fun t => (3 / 4) ^ t)
    (w := fun t => (1 / 2) * (3 / 4) ^ t) (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _)
    (fun t u _ => ?_) (fun t u _ => ?_) hN (Set.mem_univ u)
  · simp [bregman, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (u - x)]
  · simp [Fid]; nlinarith [sq_nonneg (a - b)]
  · simp only [Fid, ← sub_smul, norm_smul, ContinuousLinearMap.norm_id, mul_one, one_mul,
      le_refl]
  · simp [Fid]; ring_nf; exact le_rfl
  · simp [Fid, pow_succ]; ring_nf; exact le_rfl

end MathlibExt.Analysis.Convex.MirrorProx

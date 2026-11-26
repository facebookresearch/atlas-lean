/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Shuffle

@[expose] public section

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.Shuffle

/-- `121 ⧢ 23` has `C(5, 2) = 10` entries (Chevyrev–Kormilitzin, arXiv:1603.03788v2,
Example 1.13). -/
example : (shuffle [1, 2, 1] [2, 3]).length = 10 := by decide +kernel

/-- The multiset `121 ⧢ 23` of Example 1.13, with its repeated words. -/
example : (shuffle [1, 2, 1] [2, 3] : Multiset (List ℕ)) =
    {[1, 2, 1, 2, 3], [1, 2, 2, 1, 3], [1, 2, 2, 1, 3], [2, 1, 2, 1, 3], [1, 2, 2, 3, 1],
      [1, 2, 2, 3, 1], [2, 1, 2, 3, 1], [1, 2, 3, 2, 1], [2, 1, 3, 2, 1], [2, 3, 1, 2, 1]} := by
  decide +kernel

/-- `(i) ⧢ (i) = {ii, ii}` is a genuine multiset (remark 2 after Example 1.13). -/
example : shuffle [0] [0] = [[0, 0], [0, 0]] := by decide +kernel

/-- Example 1.15: `S¹ S² = S¹² + S²¹` for a path with continuous velocity. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (s t : ℝ) :
    signature v s t [0] * signature v s t [1] =
      signature v s t [0, 1] + signature v s t [1, 0] := by
  rw [signature_mul_signature hv]
  have : shuffle [(0 : Fin 2)] [1] = [[1, 0], [0, 1]] := by decide +kernel
  rw [this]
  simp [add_comm]

/-- Example 1.15: `S¹² S¹ = 2 S¹¹² + S¹²¹`. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (s t : ℝ) :
    signature v s t [0, 1] * signature v s t [0] =
      2 * signature v s t [0, 0, 1] + signature v s t [0, 1, 0] := by
  rw [signature_mul_signature hv]
  have : shuffle [(0 : Fin 2), 1] [0] = [[0, 0, 1], [0, 0, 1], [0, 1, 0]] := by decide +kernel
  rw [this]
  simp
  ring

/-- For a one-dimensional unit-speed path, `(S¹_{0,t})² = 2 S¹¹_{0,t}`, i.e. `S¹¹_{0,t} = t²/2`
(Example 1.6). -/
example (t : ℝ) :
    signature (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) 0 t [0, 0] = t ^ 2 / 2 := by
  have h := signature_mul_signature (v := fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ))
    (fun _ => continuous_const) 0 t [0] [0]
  have hs : shuffle [(0 : Fin 1)] [0] = [[0, 0], [0, 0]] := by decide +kernel
  rw [hs] at h
  simp [signature_singleton] at h
  linarith

/-- The second level of a one-letter-repeated word has no area: `A^{ii} = 0`. -/
example (v : Fin 2 → ℝ → ℝ) (s t : ℝ) : levyArea v s t 0 0 = 0 := by
  simp [levyArea]

/-- `S^{12} = ½ ΔX¹ ΔX² + A^{12}` for a path with continuous velocity. -/
example (v : Fin 2 → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (s t : ℝ) :
    signature v s t [0, 1] =
      (∫ u in s..t, v 0 u) * (∫ u in s..t, v 1 u) / 2 + levyArea v s t 0 1 :=
  signature_pair_eq hv s t 0 1

end MathlibExtTest.Analysis.PathSignature.Shuffle

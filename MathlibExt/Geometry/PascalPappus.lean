/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/PascalPappus.lean` (leanprover/lean-eval), commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `pascal`:
the definitions `SamePoint`, `OnConic`, `meet` and `Collinear3` and the statement of `pascal`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: ATLAS placed the declarations in the namespace below and documented them
in `WantedExt/Geometry/PascalPappusWanted.lean`. This module moves those declarations and
supplies an original proof of Pascal's theorem.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Pascal's theorem for real projective conics

`pascal` proves collinearity of the three intersections of opposite sides of a hexagon on a
nonsingular conic. All coordinates are homogeneous, including those of the intersections.
-/

@[expose] public section

namespace MathlibExt.Geometry.PascalPappusWanted
namespace Geometry.PascalPappus

open Matrix

set_option linter.dupNamespace false in
/-- **Same projective point.** Two vectors $v, w \in \mathbb{R}^3$ represent the same point of the
real projective plane when $w = c v$ for some real number $c \ne 0$. -/
def SamePoint (v w : Fin 3 → ℝ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ w = c • v

set_option linter.dupNamespace false in
/-- **Points on a conic.** For a real $3 \times 3$ matrix $M$, a vector $v \in \mathbb{R}^3$ lies on
the conic $x^\top M x = 0$ when $v^\top M v = 0$. -/
def OnConic (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : Prop :=
  v ⬝ᵥ (M *ᵥ v) = 0

set_option linter.dupNamespace false in
/-- **Meet of two lines.** Writing $\times$ for the cross product on $\mathbb{R}^3$, the meet of
the line through $a$ and $b$ with the line through $c$ and $d$, for $a, b, c, d \in \mathbb{R}^3$,
is the vector $(a \times b) \times (c \times d)$.

When $a \times b$ and $c \times d$ are nonzero and not proportional, this vector represents the
intersection point of the two projective lines. -/
def meet (a b c d : Fin 3 → ℝ) : Fin 3 → ℝ := (a ⨯₃ b) ⨯₃ (c ⨯₃ d)

set_option linter.dupNamespace false in
/-- **Collinear projective points.** Writing $\cdot$ and $\times$ for the dot and cross products
on $\mathbb{R}^3$, three vectors $p, q, r \in \mathbb{R}^3$ represent collinear points of the
real projective plane when their triple product vanishes: $p \cdot (q \times r) = 0$. -/
def Collinear3 (p q r : Fin 3 → ℝ) : Prop := p ⬝ᵥ (q ⨯₃ r) = 0

private theorem triple_mulVec (T : Matrix (Fin 3) (Fin 3) ℝ) (x y z : Fin 3 → ℝ) :
    (T *ᵥ x) ⬝ᵥ ((T *ᵥ y) ⨯₃ (T *ᵥ z)) = T.det * (x ⬝ᵥ (y ⨯₃ z)) := by
  rw [triple_product_eq_det, triple_product_eq_det]
  have h : of ![T *ᵥ x, T *ᵥ y, T *ᵥ z] = of ![x, y, z] * Tᵀ := by
    ext i j
    fin_cases i <;> simp [vecMul_transpose]
  change (of ![T *ᵥ x, T *ᵥ y, T *ᵥ z]).det = T.det * (of ![x, y, z]).det
  rw [h, det_mul, det_transpose, mul_comm]

private theorem meet_mulVec (T : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3 → ℝ) :
    meet (T *ᵥ a) (T *ᵥ b) (T *ᵥ c) (T *ᵥ d) = T.det • (T *ᵥ meet a b c d) := by
  simp only [meet, cross_cross_eq_smul_sub_smul', triple_mulVec, mulVec_sub, mulVec_smul,
    smul_sub, mul_smul]
  rw [dotProduct_comm (_ ⨯₃ _) (T *ᵥ d), triple_mulVec, dotProduct_comm (_ ⨯₃ _) d, mul_smul]

-- With the first pair of vertices at the first two coordinate points, the conic equation
-- has just four monomials. The remaining four vertices impose four linear conditions.
private def monomials (v : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![v 0 * v 1, v 0 * v 2, v 1 * v 2, v 2 ^ 2]

private theorem pascal_determinant (u v w t : Fin 3 → ℝ) :
    meet ![1, 0, 0] w u ![0, 1, 0] ⬝ᵥ
        (meet ![1, 0, 0] t v ![0, 1, 0] ⨯₃ meet u t v w) =
      (of ![monomials u, monomials v, monomials w, monomials t]).det := by
  rw [det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, meet, monomials, cross_apply,
    submatrix_apply, Fin.succAbove]
  ring

private theorem pascal_coordinates (N : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : N.IsSymm) (hn : N.det ≠ 0) (h₀ : N 0 0 = 0) (h₁ : N 1 1 = 0)
    (u v w t : Fin 3 → ℝ) (hu : OnConic N u) (hv : OnConic N v)
    (hw : OnConic N w) (ht : OnConic N t) :
    Collinear3 (meet ![1, 0, 0] w u ![0, 1, 0]) (meet ![1, 0, 0] t v ![0, 1, 0])
      (meet u t v w) := by
  let k := ![2 * N 0 1, 2 * N 0 2, 2 * N 1 2, N 2 2]
  have hk : k ≠ 0 := by
    intro h
    have h₀₁ : 2 * N 0 1 = 0 := congrFun h 0
    have hz := (mul_eq_zero.mp h₀₁).resolve_left (by norm_num)
    exact hn (by simp [det_fin_three, h₀, h₁, hs.apply 0 1, hz])
  have row (x : Fin 3 → ℝ) (hx : OnConic N x) : monomials x ⬝ᵥ k = 0 := by
    refine Eq.trans ?_ hx
    simp [k, monomials, mulVec, dotProduct, Fin.sum_univ_succ, h₀, h₁,
      hs.apply 0 1, hs.apply 0 2, hs.apply 1 2]
    ring
  unfold Collinear3
  rw [pascal_determinant, ← exists_mulVec_eq_zero_iff]
  refine ⟨k, hk, ?_⟩
  funext i
  fin_cases i
  · exact row u hu
  · exact row v hv
  · exact row w hw
  · exact row t ht

set_option linter.dupNamespace false in
/-- **Pascal's theorem for real projective conics.** Let $M$ be a real symmetric $3 \times 3$
matrix with $\det M \ne 0$, and let $a_1, a_2, a_3, b_1, b_2, b_3 \in \mathbb{R}^3$ be nonzero
vectors on the conic $x^\top M x = 0$, no two of which represent the same projective point.
Writing $\cdot$ and $\times$ for the dot and cross products on $\mathbb{R}^3$, let
$p = (a_1 \times b_2) \times (a_2 \times b_1)$, $q = (a_1 \times b_3) \times (a_3 \times b_1)$ and
$r = (a_2 \times b_3) \times (a_3 \times b_2)$ be the meets of the opposite sides of the hexagon
$a_1 b_2 a_3 b_1 a_2 b_3$. Then $p$, $q$ and $r$ are collinear: $p \cdot (q \times r) = 0$.

Source: B. Pascal, *Essay pour les coniques* (1640). Knill, *Some fundamental theorems in
mathematics*, §146. Via leanprover/lean-eval@38361be, problem `pascal`. -/
public theorem pascal
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hMsymm : M.IsSymm) (hMdet : M.det ≠ 0)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Fin 3 → ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hdist : [a₁, a₂, a₃, b₁, b₂, b₃].Pairwise (fun v w => ¬ SamePoint v w))
    (hA₁ : OnConic M a₁) (hA₂ : OnConic M a₂) (hA₃ : OnConic M a₃)
    (hB₁ : OnConic M b₁) (hB₂ : OnConic M b₂) (hB₃ : OnConic M b₃) :
    Collinear3 (meet a₁ b₂ a₂ b₁) (meet a₁ b₃ a₃ b₁) (meet a₂ b₃ a₃ b₂) := by
  -- Use the first pair as coordinate points and their cross product as the third basis vector.
  have hab : a₁ ⨯₃ b₁ ≠ 0 := by
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    apply (LinearIndependent.pair_iff' ha₁).mpr
    intro c hc
    have hne : c ≠ 0 := by
      rintro rfl
      exact hb₁ (by simpa using hc.symm)
    exact (List.pairwise_cons.mp hdist).1 b₁ (by simp) ⟨c, hne, hc.symm⟩
  let T := (of ![a₁, b₁, a₁ ⨯₃ b₁])ᵀ
  have hT : T.det ≠ 0 := by
    rw [show T.det = det ![a₁, b₁, a₁ ⨯₃ b₁] from det_transpose _,
      ← triple_product_eq_det, ← triple_product_permutation (a₁ ⨯₃ b₁) a₁ b₁]
    exact fun h => hab (dotProduct_self_eq_zero.mp h)
  have hTa : T *ᵥ ![1, 0, 0] = a₁ := by
    ext i
    simp [T, mulVec, dotProduct, Fin.sum_univ_succ]
  have hTb : T *ᵥ ![0, 1, 0] = b₁ := by
    ext i
    simp [T, mulVec, dotProduct, Fin.sum_univ_succ]
  have surj := mulVec_surjective_iff_isUnit.mpr ((isUnit_iff_isUnit_det T).mpr hT.isUnit)
  obtain ⟨u, rfl⟩ := surj a₂
  obtain ⟨v, rfl⟩ := surj a₃
  obtain ⟨w, rfl⟩ := surj b₂
  obtain ⟨t, rfl⟩ := surj b₃
  let N := Tᵀ * M * T
  have hsym : N.IsSymm := by simp [N, IsSymm, transpose_mul, hMsymm.eq, mul_assoc]
  have hdet : N.det ≠ 0 := by simpa [N, det_mul] using mul_ne_zero (mul_ne_zero hT hMdet) hT
  have pull (x : Fin 3 → ℝ) : OnConic N x ↔ OnConic M (T *ᵥ x) := by
    unfold OnConic
    rw [show N = Tᵀ * M * T from rfl, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_transpose_mulVec, dotProduct_comm]
  have h₀ : N 0 0 = 0 := by
    simpa [OnConic, mulVec, dotProduct, Fin.sum_univ_succ] using (pull ![1, 0, 0]).mpr (hTa ▸ hA₁)
  have h₁ : N 1 1 = 0 := by
    simpa [OnConic, mulVec, dotProduct, Fin.sum_univ_succ] using (pull ![0, 1, 0]).mpr (hTb ▸ hB₁)
  have h := pascal_coordinates N hsym hdet h₀ h₁ u v w t
    ((pull u).mpr hA₂) ((pull v).mpr hA₃) ((pull w).mpr hB₂) ((pull t).mpr hB₃)
  rw [← hTa, ← hTb]
  unfold Collinear3 at h ⊢
  simp only [meet_mulVec, LinearMap.map_smul, LinearMap.smul_apply, smul_dotProduct,
    dotProduct_smul, triple_mulVec, h, mul_zero, smul_zero]

end Geometry.PascalPappus
end MathlibExt.Geometry.PascalPappusWanted

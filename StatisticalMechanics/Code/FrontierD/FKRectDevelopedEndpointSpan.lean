/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedEndpointReflectionGlue



open Set

namespace StatMech.FrontierD

noncomputable section


theorem fkRectDevelopedThreeByOneVertex_column_val
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (z : fkRectDevelopedThreeByOneRect n) :
    ((fkRectDevelopedSquareVertex R n z.1).1.val : Int) =
      z.1 1 + n + (z.1 0 - z.1 1 + n) / 2 := by
  have hpoint := fkRectVertexSquarePoint_developedThreeByOneVertex
    R n hwidth hheight z.2
  have hundev := congrArg fkRectSquareUndevelopPoint hpoint
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at hundev
  have hx := congrArg Prod.fst hundev
  change ((fkRectDevelopedSquareVertex R n z.1).1.val : Int) =
    (fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z.1)).1 at hx
  rw [hx]
  simp [fkRectDevelopedSquarePoint, fkRectSquareUndevelopPoint]
  congr 1
  ring



theorem developedEndpoint_physical_span (a b : Int) (n : Nat) :
    (n : Int) ≤ 2 * |b - a - n| ∨
      (n : Int) ≤ 4 *
        |(2 * (n : Int) + b / 2) -
          ((n : Int) + (a + n) / 2)| := by
  by_cases hd : 0 ≤ b - a - n
  · rw [abs_of_nonneg hd]
    by_cases he : 0 ≤
        (2 * (n : Int) + b / 2) - ((n : Int) + (a + n) / 2)
    · rw [abs_of_nonneg he]
      omega
    · rw [abs_of_nonpos (le_of_not_ge he)]
      omega
  · rw [abs_of_nonpos (le_of_not_ge hd)]
    by_cases he : 0 ≤
        (2 * (n : Int) + b / 2) - ((n : Int) + (a + n) / 2)
    · rw [abs_of_nonneg he]
      omega
    · rw [abs_of_nonpos (le_of_not_ge he)]
      omega


theorem fkRectDevelopedThreeByOneEndpoint_physical_span
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hp : p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n) :
    let x := fkRectDevelopedSquareVertex R n p.1
    let y := fkRectDevelopedSquareVertex R n p.2
    (n : Int) ≤ 2 * |(y.2.val : Int) - x.2.val| ∨
      (n : Int) ≤ 4 * |(y.1.val : Int) - x.1.val| := by
  dsimp only
  have hend :=
    (mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n p).mp hp
  rw [fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.1,
    fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.2,
    fkRectDevelopedThreeByOneVertex_column_val R n hwidth hheight p.1,
    fkRectDevelopedThreeByOneVertex_column_val R n hwidth hheight p.2,
    hend.1, hend.2]
  convert developedEndpoint_physical_span (p.1.1 0) (p.2.1 0) n using 1 <;>
    congr 2 <;> ring



theorem fkRectCritical_developedThreeByOne_exists_carrierConnection_span_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      let x := fkRectDevelopedSquareVertex R n p.1
      let y := fkRectDevelopedSquareVertex R n p.2
      1 / (2 * (1 + q)) /
          (((3 * n + 1) ^ 2 : Nat) : Real) ≤
        fkRectCriticalEventMass R q
          (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) ∧
      ((n : Int) ≤ 2 * |(y.2.val : Int) - x.2.val| ∨
        (n : Int) ≤ 4 * |(y.1.val : Int) - x.1.val|) := by
  obtain ⟨p, hp, havg⟩ :=
    fkRectCritical_developedThreeByOne_exists_endpoint_ge
      R n hn (by omega) (by omega) hq
  refine ⟨p, hp, ?_,
    fkRectDevelopedThreeByOneEndpoint_physical_span
      R n hwidth hheight p hp⟩
  let M : Real := (((3 * n + 1) ^ 2 : Nat) : Real)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hplanar : 1 / (2 * (1 + q)) / M ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
    rw [div_le_iff₀ hM]
    simpa [M, mul_comm] using havg
  exact hplanar.trans (fkRectCriticalEventMass_mono R
    (zero_lt_one.trans_le hq)
    (fkRectDevelopedThreeByOneEndpointConnection_subset_carrier
      R n hwidth hheight p))

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKCriticalSurface









open Set

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA

theorem exists_triangularFKCritical_candidate
    {q : Real} (hq : 1 <= q) :
    exists p : Real, p ∈ Ioo (0 : Real) 1 /\
      triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0 := by
  let f : Real -> Real := fun y => triangularFKCriticalPolynomial q y
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hf0 : f 0 = -q := by simp [f, triangularFKCriticalPolynomial]
  have hfq : 0 <= f q := by
    dsimp [f, triangularFKCriticalPolynomial]
    nlinarith [sq_nonneg (q - 1)]
  have hzeroMem : (0 : Real) ∈ Icc (f 0) (f q) := by
    rw [hf0]
    exact ⟨by linarith, hfq⟩
  have hfcont : ContinuousOn f (Icc (0 : Real) q) := by
    dsimp [f, triangularFKCriticalPolynomial]
    fun_prop
  obtain ⟨y, hyMem, hy⟩ :=
    intermediate_value_Icc hq0.le hfcont hzeroMem
  have hyEq : triangularFKCriticalPolynomial q y = 0 := by
    simpa [f] using hy
  have hyPos : 0 < y := by
    refine hyMem.1.lt_of_ne ?_
    intro hy0
    subst y
    simp [triangularFKCriticalPolynomial] at hyEq
    linarith
  let p := y / (1 + y)
  have hp0 : 0 < p := div_pos hyPos (by linarith)
  have hp1 : p < 1 := by
    dsimp [p]
    rw [div_lt_one (by linarith : 0 < 1 + y)]
    linarith
  refine ⟨p, ⟨hp0, hp1⟩, ?_⟩
  have hden : 1 + y ≠ 0 := by linarith
  have hodds : fkEdgeOdds p = y := by
    dsimp [p, fkEdgeOdds]
    field_simp [hden]
    ring
  rwa [hodds]





theorem exists_triangularFKCritical_candidate_weaklyAligned
    {q : Real} (hq : 1 <= q) :
    exists p : Real, p ∈ Ioo (0 : Real) 1 /\
      triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0 /\
      (p < triangular.criticalPoint q ->
        dualParam p q <= hexagonal.criticalPoint q) /\
      (triangular.criticalPoint q < p ->
        hexagonal.criticalPoint q <= dualParam p q) /\
      (dualParam p q < hexagonal.criticalPoint q ->
        p <= triangular.criticalPoint q) /\
      (hexagonal.criticalPoint q < dualParam p q ->
        triangular.criticalPoint q <= p) := by
  obtain ⟨p, hp, hsurface⟩ := exists_triangularFKCritical_candidate hq
  obtain ⟨hbelow, habove, hdualBelow, hdualAbove⟩ :=
    triHexSurfaceCandidate_criticalPoints_weaklyAligned hq hp hsurface
  exact ⟨p, hp, hsurface, hbelow, habove, hdualBelow, hdualAbove⟩

end StatMech.FK.PeriodicPlanar

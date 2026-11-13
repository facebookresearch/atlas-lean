/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFaceCornerGreen









namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def faceMarkedEndpointCode
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : faceMarkedEndpointLayer n radius z) :
    Bool × Fin (radius + 1) × Fin (radius + 1) := by
  cases z with
  | none => exact False.elim hz
  | some c =>
      by_cases hlower : c.1.1 + c.2.1 <= radius
      · exact (false, ⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩)
      · have hupper :=
          (faceMarkedEndpointLayer_coordinate_cases n radius c hz).resolve_left
            hlower
        exact (true, ⟨c.1.1, by omega⟩,
          ⟨2 * n - 1 - c.2.1, by omega⟩)

theorem faceMarkedEndpointCode_injective
    (n radius : Nat)
    {z w : Option (FKIsingSquareFullFaceNode n)}
    (hz : faceMarkedEndpointLayer n radius z)
    (hw : faceMarkedEndpointLayer n radius w)
    (hcode : faceMarkedEndpointCode n radius z hz =
      faceMarkedEndpointCode n radius w hw) :
    z = w := by
  cases z with
  | none => exact False.elim hz
  | some c =>
      cases w with
      | none => exact False.elim hw
      | some d =>
          by_cases hc : c.1.1 + c.2.1 <= radius <;>
            by_cases hd : d.1.1 + d.2.1 <= radius
          · simp [faceMarkedEndpointCode, hc, hd] at hcode
            apply congrArg some
            apply Prod.ext
            · apply Fin.ext
              exact hcode.1
            · apply Fin.ext
              exact hcode.2
          · simp [faceMarkedEndpointCode, hc, hd] at hcode
          · simp [faceMarkedEndpointCode, hc, hd] at hcode
          · simp [faceMarkedEndpointCode, hc, hd] at hcode
            apply congrArg some
            apply Prod.ext
            · apply Fin.ext
              exact hcode.1
            · apply Fin.ext
              have hcBound := c.2.isLt
              have hdBound := d.2.isLt
              omega



theorem faceInteriorExceptionalSources_card_le
    (n radius : Nat) :
    (isingFiniteWeightedInteriorExceptionalSources
      (faceDirichletBoundary n)
      (faceMarkedEndpointLayer n radius)).card <=
        2 * (radius + 1) ^ 2 := by
  classical
  let S := isingFiniteWeightedInteriorExceptionalSources
    (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)
  let encode : {z // z ∈ S} ->
      Bool × Fin (radius + 1) × Fin (radius + 1) := fun z =>
    faceMarkedEndpointCode n radius z.1 (by
      have hzmem : z.1 ∈ isingFiniteWeightedInteriorExceptionalSources
          (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) := by
        simpa only [S] using z.2
      change z.1 ∈ Finset.univ.filter (fun w =>
        Not (faceDirichletBoundary n w) /\
          faceMarkedEndpointLayer n radius w) at hzmem
      exact (Finset.mem_filter.mp hzmem).2.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact faceMarkedEndpointCode_injective n radius _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Bool × Fin (radius + 1) × Fin (radius + 1)) :=
    Fintype.card_le_of_injective encode hinj
  simpa [S, pow_two, mul_assoc] using hcard

theorem faceInteriorExceptionalSources_mul_le
    (n radius : Nat) (B : Real) (hB : 0 <= B) :
    ((isingFiniteWeightedInteriorExceptionalSources
      (faceDirichletBoundary n)
      (faceMarkedEndpointLayer n radius)).card : Real) * B <=
        (2 * (radius + 1) ^ 2 : Nat) * B := by
  apply mul_le_mul_of_nonneg_right _ hB
  exact_mod_cast faceInteriorExceptionalSources_card_le n radius


theorem faceMarkedEndpointBarrier_le_radiusDistance
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullFaceNode n)
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary n source))
    (hleft : 0 < source.1.1)
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real))
    (hupperDistance : distance <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * n - 1 - source.2.1 : Nat)) :
    faceMarkedEndpointBarrier n radius (some source) <=
      (2 * (radius + 1) ^ 2 : Nat) *
        (((radius : Real) + 1 / isingFermionicGhostCoefficient) *
          (radius : Real) / distance) := by
  let B : Real :=
    ((radius : Real) + 1 / isingFermionicGhostCoefficient) *
      (radius : Real) / distance
  have hB : 0 <= B := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg (Nat.cast_nonneg _)
          (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le))
        (Nat.cast_nonneg _)) hdistance.le
  have hbarrier := faceMarkedEndpointBarrier_le_card_mul_reciprocal
    n radius (some source) hfixed B
    (facePointPoissonBarrier_le_exceptionalSourceRadius
      n radius distance source hfixed hleft hdistance
      hlowerDistance hupperDistance)
  exact hbarrier.trans
    (faceInteriorExceptionalSources_mul_le n radius B hB)



noncomputable def faceEndpointPolynomialBound (k : Nat) : Real :=
  (2 * (((k + 1) + 1 : Nat) : Real) ^ 2) *
    ((((k + 1 : Nat) : Real) + 1 / isingFermionicGhostCoefficient) *
      ((k + 1 : Nat) : Real) /
        ((((k + 1) ^ 5 : Nat) : Real) / 2))

theorem tendsto_faceEndpointPolynomialBound :
    Filter.Tendsto faceEndpointPolynomialBound Filter.atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hrhs : Filter.Tendsto
      (fun k => 4 * (1 + u k) ^ 2 *
        (1 + (1 / isingFermionicGhostCoefficient) * u k) * u k)
      Filter.atTop (nhds 0) := by
    convert (((tendsto_const_nhds.mul
      ((tendsto_const_nhds.add hu).pow 2)).mul
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hu))).mul hu) using 1
    norm_num
  convert hrhs using 1
  funext k
  unfold faceEndpointPolynomialBound u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  ring

theorem faceMarkedEndpointBarrier_le_polynomialBound
    (k : Nat)
    (source : FKIsingSquareFullFaceNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
    (hleft : 0 < source.1.1)
    (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real))
    (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * ((k + 1) ^ 5) - 1 - source.2.1 : Nat)) :
    faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      faceEndpointPolynomialBound k := by
  have hdistance : (0 : Real) < (((k + 1) ^ 5 : Nat) : Real) / 2 := by
    positivity
  simpa [faceEndpointPolynomialBound] using
    faceMarkedEndpointBarrier_le_radiusDistance
      ((k + 1) ^ 5) (k + 1)
      ((((k + 1) ^ 5 : Nat) : Real) / 2)
      source hfixed hleft hdistance hlowerDistance hupperDistance



theorem faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
    (k : Nat)
    (source : FKIsingSquareFullFaceNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
    (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= source.1.1) :
    faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      faceEndpointPolynomialBound k := by
  have hleft : 0 < source.1.1 := by
    by_contra h
    have hz : source.1.1 = 0 := Nat.eq_zero_of_not_pos h
    have hN : (0 : Real) < ((k : Real) + 1) ^ 5 / 2 := by
      positivity
    simp [hz] at hhalf
    linarith
  apply faceMarkedEndpointBarrier_le_polynomialBound k source hfixed hleft
  · have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    have hy : 0 <= (source.2.1 : Real) := Nat.cast_nonneg _
    linarith
  · have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    have hy : 0 <= ((2 * ((k + 1) ^ 5) - 1 - source.2.1 : Nat) : Real) :=
      Nat.cast_nonneg _
    linarith

theorem tendsto_four_mul_faceEndpointPolynomialBound :
    Filter.Tendsto (fun k => 4 * faceEndpointPolynomialBound k)
      Filter.atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicVertexCornerGreen









namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexMarkedEndpointCode
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : vertexMarkedEndpointLayer n radius z) :
    Bool × Fin (radius + 1) × Fin (radius + 1) := by
  cases z with
  | none => exact False.elim hz
  | some x =>
      by_cases hlower : fullVertexColumnIndex n x +
          fullVertexRowIndex n x <= radius
      · exact (false, ⟨fullVertexColumnIndex n x, by omega⟩,
          ⟨fullVertexRowIndex n x, by omega⟩)
      · have hupper :=
          (vertexMarkedEndpointLayer_coordinate_cases n radius x hz).resolve_left
            hlower
        exact (true, ⟨fullVertexColumnIndex n x, by omega⟩,
          ⟨2 * n - fullVertexRowIndex n x, by omega⟩)

theorem vertexMarkedEndpointCode_injective
    (n radius : Nat)
    {z w : Option (FKIsingSquareFullVertexNode n)}
    (hz : vertexMarkedEndpointLayer n radius z)
    (hw : vertexMarkedEndpointLayer n radius w)
    (hcode : vertexMarkedEndpointCode n radius z hz =
      vertexMarkedEndpointCode n radius w hw) :
    z = w := by
  cases z with
  | none => exact False.elim hz
  | some x =>
      cases w with
      | none => exact False.elim hw
      | some y =>
          by_cases hx : fullVertexColumnIndex n x +
              fullVertexRowIndex n x <= radius <;>
            by_cases hy : fullVertexColumnIndex n y +
              fullVertexRowIndex n y <= radius
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode.1
            have hrow : fullVertexRowIndex n x =
                fullVertexRowIndex n y := hcode.2
            apply congrArg some
            apply Subtype.ext
            funext i
            fin_cases i
            · have hxc := fullVertexColumnIndex_coe n x
              have hyc := fullVertexColumnIndex_coe n y
              change x.1 0 = y.1 0
              omega
            · have hxr := fullVertexRowIndex_coe n x
              have hyr := fullVertexRowIndex_coe n y
              change x.1 1 = y.1 1
              omega
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode.1
            have htopdist : 2 * n - fullVertexRowIndex n x =
                2 * n - fullVertexRowIndex n y := hcode.2
            apply congrArg some
            apply Subtype.ext
            funext i
            fin_cases i
            · have hxc := fullVertexColumnIndex_coe n x
              have hyc := fullVertexColumnIndex_coe n y
              change x.1 0 = y.1 0
              omega
            · have hxr := fullVertexRowIndex_coe n x
              have hyr := fullVertexRowIndex_coe n y
              have hxb := fullVertexRowIndex_le n x
              have hyb := fullVertexRowIndex_le n y
              change x.1 1 = y.1 1
              omega



theorem vertexInteriorExceptionalSources_card_le
    (n radius : Nat) :
    (isingFiniteWeightedInteriorExceptionalSources
      (vertexDirichletBoundary n)
      (vertexMarkedEndpointLayer n radius)).card <=
        2 * (radius + 1) ^ 2 := by
  classical
  let S := isingFiniteWeightedInteriorExceptionalSources
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
  let encode : {z // z ∈ S} ->
      Bool × Fin (radius + 1) × Fin (radius + 1) := fun z =>
    vertexMarkedEndpointCode n radius z.1 (by
      have hzmem : z.1 ∈ isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) := by
        simpa only [S] using z.2
      change z.1 ∈ Finset.univ.filter (fun w =>
        Not (vertexDirichletBoundary n w) ∧
          vertexMarkedEndpointLayer n radius w) at hzmem
      exact (Finset.mem_filter.mp hzmem).2.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact vertexMarkedEndpointCode_injective n radius _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Bool × Fin (radius + 1) × Fin (radius + 1)) :=
    Fintype.card_le_of_injective encode hinj
  simpa [S, pow_two, mul_assoc] using hcard

theorem vertexInteriorExceptionalSources_mul_le
    (n radius : Nat) (B : Real) (hB : 0 <= B) :
    ((isingFiniteWeightedInteriorExceptionalSources
      (vertexDirichletBoundary n)
      (vertexMarkedEndpointLayer n radius)).card : Real) * B <=
        (2 * (radius + 1) ^ 2 : Nat) * B := by
  apply mul_le_mul_of_nonneg_right _ hB
  exact_mod_cast vertexInteriorExceptionalSources_card_le n radius



theorem vertexMarkedEndpointBarrier_le_radiusDistance
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexMarkedEndpointBarrier n radius (some source) <=
      (2 * (radius + 1) ^ 2 : Nat) *
        ((radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) /
            distance) := by
  let B : Real :=
    (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance
  have hB : 0 <= B := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (Nat.cast_nonneg _)
          (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le)))
      hdistance.le
  have hbarrier := vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    n radius (some source) hfixed B
    (vertexPointPoissonBarrier_le_exceptionalSourceRadius
      n radius distance source hn hfixed hright hbottom htop hdistance
      hlowerDistance hupperDistance)
  exact hbarrier.trans
    (vertexInteriorExceptionalSources_mul_le n radius B hB)



noncomputable def vertexEndpointPolynomialBound (k : Nat) : Real :=
  (2 * (((k + 1) + 1 : Nat) : Real) ^ 2) *
    (((k + 1 : Nat) : Real) *
      (((k + 1 : Nat) : Real) + 1 / isingFermionicGhostCoefficient) /
        ((((k + 1) ^ 5 : Nat) : Real) / 2))

theorem tendsto_vertexEndpointPolynomialBound :
    Filter.Tendsto vertexEndpointPolynomialBound Filter.atTop (nhds 0) := by
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
  unfold vertexEndpointPolynomialBound u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  ring

theorem vertexMarkedEndpointBarrier_le_polynomialBound
    (k : Nat)
    (source : FKIsingSquareFullVertexNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary
      ((k + 1) ^ 5) source))
    (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
    (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
    (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
    (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) +
        (fullVertexRowIndex ((k + 1) ^ 5) source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) +
        (2 * ((k + 1) ^ 5) -
          fullVertexRowIndex ((k + 1) ^ 5) source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      vertexEndpointPolynomialBound k := by
  have hn : 0 < (k + 1) ^ 5 := by positivity
  have hdistance : (0 : Real) < (((k + 1) ^ 5 : Nat) : Real) / 2 := by
    positivity
  simpa [vertexEndpointPolynomialBound] using
    vertexMarkedEndpointBarrier_le_radiusDistance
      ((k + 1) ^ 5) (k + 1)
      ((((k + 1) ^ 5 : Nat) : Real) / 2)
      source hn hfixed hright hbottom htop hdistance
      hlowerDistance hupperDistance




theorem vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
    (k : Nat)
    (source : FKIsingSquareFullVertexNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary
      ((k + 1) ^ 5) source))
    (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
    (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
    (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
    (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      fullVertexColumnIndex ((k + 1) ^ 5) source) :
    vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      vertexEndpointPolynomialBound k := by
  apply vertexMarkedEndpointBarrier_le_polynomialBound k source hfixed
    hright hbottom htop
  · have hrow : 0 <=
        (fullVertexRowIndex ((k + 1) ^ 5) source : Real) := by positivity
    have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    linarith
  · have hrow : 0 <=
        ((2 * ((k + 1) ^ 5) -
          fullVertexRowIndex ((k + 1) ^ 5) source : Nat) : Real) := by
      positivity
    have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    linarith

theorem tendsto_four_mul_vertexEndpointPolynomialBound :
    Filter.Tendsto (fun k => 4 * vertexEndpointPolynomialBound k)
      Filter.atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality

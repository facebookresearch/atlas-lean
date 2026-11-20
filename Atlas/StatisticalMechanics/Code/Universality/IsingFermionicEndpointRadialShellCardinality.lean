/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicRadialResidualSummation
import Code.Universality.IsingFermionicVertexCornerCardinality
import Code.Universality.IsingFermionicFaceCornerCardinality









namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


def vertexEndpointRadialShell
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) -> Nat
  | none => 0
  | some x => fullVertexColumnIndex n x +
      min (fullVertexRowIndex n x)
        (2 * n - fullVertexRowIndex n x)

theorem vertexEndpointRadialShell_lt (n : Nat) :
    forall z, vertexEndpointRadialShell n z < 3 * n + 1 := by
  intro z
  cases z with
  | none => simp [vertexEndpointRadialShell]
  | some x =>
      have hcol := fullVertexColumnIndex_le n x
      have hrow := fullVertexRowIndex_le n x
      simp only [vertexEndpointRadialShell]
      omega



noncomputable def vertexEndpointRadialShellCode
    (n r : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : vertexEndpointRadialShell n z = r) : Fin 3 × Fin (r + 1) := by
  cases z with
  | none => exact (0, 0)
  | some x =>
      by_cases hlower : fullVertexRowIndex n x <=
          2 * n - fullVertexRowIndex n x
      · exact (1, ⟨fullVertexColumnIndex n x, by
          simp only [vertexEndpointRadialShell, min_eq_left hlower] at hz
          omega⟩)
      · exact (2, ⟨fullVertexColumnIndex n x, by
          have hupper : 2 * n - fullVertexRowIndex n x <=
              fullVertexRowIndex n x := by omega
          simp only [vertexEndpointRadialShell, min_eq_right hupper] at hz
          omega⟩)

theorem vertexEndpointRadialShellCode_injective
    (n r : Nat)
    {z w : Option (FKIsingSquareFullVertexNode n)}
    (hz : vertexEndpointRadialShell n z = r)
    (hw : vertexEndpointRadialShell n w = r)
    (hcode : vertexEndpointRadialShellCode n r z hz =
      vertexEndpointRadialShellCode n r w hw) :
    z = w := by
  cases z with
  | none =>
      cases w with
      | none => rfl
      | some y =>
          by_cases hy : fullVertexRowIndex n y <=
              2 * n - fullVertexRowIndex n y <;>
            simp [vertexEndpointRadialShellCode, hy] at hcode
  | some x =>
      cases w with
      | none =>
          by_cases hx : fullVertexRowIndex n x <=
              2 * n - fullVertexRowIndex n x <;>
            simp [vertexEndpointRadialShellCode, hx] at hcode
      | some y =>
          by_cases hx : fullVertexRowIndex n x <=
              2 * n - fullVertexRowIndex n x <;>
            by_cases hy : fullVertexRowIndex n y <=
              2 * n - fullVertexRowIndex n y
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode
            have hxrad : fullVertexColumnIndex n x +
                fullVertexRowIndex n x = r := by
              simpa [vertexEndpointRadialShell, min_eq_left hx] using hz
            have hyrad : fullVertexColumnIndex n y +
                fullVertexRowIndex n y = r := by
              simpa [vertexEndpointRadialShell, min_eq_left hy] using hw
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
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode
            have hxupper : 2 * n - fullVertexRowIndex n x <=
                fullVertexRowIndex n x := by omega
            have hyupper : 2 * n - fullVertexRowIndex n y <=
                fullVertexRowIndex n y := by omega
            have hxrad : fullVertexColumnIndex n x +
                (2 * n - fullVertexRowIndex n x) = r := by
              simpa [vertexEndpointRadialShell, min_eq_right hxupper] using hz
            have hyrad : fullVertexColumnIndex n y +
                (2 * n - fullVertexRowIndex n y) = r := by
              simpa [vertexEndpointRadialShell, min_eq_right hyupper] using hw
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

theorem vertexEndpointRadialShell_card_le (n r : Nat) :
    (Finset.univ.filter (fun z : Option (FKIsingSquareFullVertexNode n) =>
      vertexEndpointRadialShell n z = r)).card <= 3 * (r + 1) := by
  classical
  let S := Finset.univ.filter
    (fun z : Option (FKIsingSquareFullVertexNode n) =>
      vertexEndpointRadialShell n z = r)
  let encode : {z // z ∈ S} -> Fin 3 × Fin (r + 1) := fun z =>
    vertexEndpointRadialShellCode n r z.1 (by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using z.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact vertexEndpointRadialShellCode_injective n r _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Fin 3 × Fin (r + 1)) :=
    Fintype.card_le_of_injective encode hinj
  change S.card <= 3 * (r + 1)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
    hcard


def faceEndpointRadialShell
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) -> Nat
  | none => 0
  | some c => c.1.1 + min c.2.1 (2 * n - 1 - c.2.1)

theorem faceEndpointRadialShell_lt (n : Nat) :
    forall z, faceEndpointRadialShell n z < 3 * n + 1 := by
  intro z
  cases z with
  | none => simp [faceEndpointRadialShell]
  | some c =>
      have hc0 := c.1.2
      have hc1 := c.2.2
      simp only [faceEndpointRadialShell]
      omega


noncomputable def faceEndpointRadialShellCode
    (n r : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : faceEndpointRadialShell n z = r) : Fin 3 × Fin (r + 1) := by
  cases z with
  | none => exact (0, 0)
  | some c =>
      by_cases hlower : c.2.1 <= 2 * n - 1 - c.2.1
      · exact (1, ⟨c.1.1, by
          simp only [faceEndpointRadialShell, min_eq_left hlower] at hz
          omega⟩)
      · exact (2, ⟨c.1.1, by
          have hupper : 2 * n - 1 - c.2.1 <= c.2.1 := by omega
          simp only [faceEndpointRadialShell, min_eq_right hupper] at hz
          omega⟩)

theorem faceEndpointRadialShellCode_injective
    (n r : Nat)
    {z w : Option (FKIsingSquareFullFaceNode n)}
    (hz : faceEndpointRadialShell n z = r)
    (hw : faceEndpointRadialShell n w = r)
    (hcode : faceEndpointRadialShellCode n r z hz =
      faceEndpointRadialShellCode n r w hw) :
    z = w := by
  cases z with
  | none =>
      cases w with
      | none => rfl
      | some d =>
          by_cases hd : d.2.1 <= 2 * n - 1 - d.2.1 <;>
            simp [faceEndpointRadialShellCode, hd] at hcode
  | some c =>
      cases w with
      | none =>
          by_cases hc : c.2.1 <= 2 * n - 1 - c.2.1 <;>
            simp [faceEndpointRadialShellCode, hc] at hcode
      | some d =>
          by_cases hc : c.2.1 <= 2 * n - 1 - c.2.1 <;>
            by_cases hd : d.2.1 <= 2 * n - 1 - d.2.1
          · simp [faceEndpointRadialShellCode, hc, hd] at hcode
            have hcol : c.1.1 = d.1.1 := hcode
            have hcrad : c.1.1 + c.2.1 = r := by
              simpa [faceEndpointRadialShell, min_eq_left hc] using hz
            have hdrad : d.1.1 + d.2.1 = r := by
              simpa [faceEndpointRadialShell, min_eq_left hd] using hw
            apply congrArg some
            apply Prod.ext
            · apply Fin.ext
              exact hcol
            · apply Fin.ext
              omega
          · simp [faceEndpointRadialShellCode, hc, hd] at hcode
          · simp [faceEndpointRadialShellCode, hc, hd] at hcode
          · simp [faceEndpointRadialShellCode, hc, hd] at hcode
            have hcol : c.1.1 = d.1.1 := hcode
            have hcupper : 2 * n - 1 - c.2.1 <= c.2.1 := by omega
            have hdupper : 2 * n - 1 - d.2.1 <= d.2.1 := by omega
            have hcrad : c.1.1 + (2 * n - 1 - c.2.1) = r := by
              simpa [faceEndpointRadialShell, min_eq_right hcupper] using hz
            have hdrad : d.1.1 + (2 * n - 1 - d.2.1) = r := by
              simpa [faceEndpointRadialShell, min_eq_right hdupper] using hw
            apply congrArg some
            apply Prod.ext
            · apply Fin.ext
              exact hcol
            · apply Fin.ext
              have hcb := c.2.2
              have hdb := d.2.2
              omega

theorem faceEndpointRadialShell_card_le (n r : Nat) :
    (Finset.univ.filter (fun z : Option (FKIsingSquareFullFaceNode n) =>
      faceEndpointRadialShell n z = r)).card <= 3 * (r + 1) := by
  classical
  let S := Finset.univ.filter
    (fun z : Option (FKIsingSquareFullFaceNode n) =>
      faceEndpointRadialShell n z = r)
  let encode : {z // z ∈ S} -> Fin 3 × Fin (r + 1) := fun z =>
    faceEndpointRadialShellCode n r z.1 (by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using z.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact faceEndpointRadialShellCode_injective n r _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Fin 3 × Fin (r + 1)) :=
    Fintype.card_le_of_injective encode hinj
  change S.card <= 3 * (r + 1)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
    hcard



theorem vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (x : Option (FKIsingSquareFullVertexNode n))
    (C : Real) (hC : 0 <= C)
    (hpoint : forall z,
      vertexSpatialTargetResidual n target z *
          vertexPointPoissonBarrier n z x <=
        C / ((n : Real) *
          ((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :
    vertexSpatialTargetResidualPotential n target x <=
      C * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
  apply vertexSpatialTargetResidualPotential_le_harmonic_of_radialShellBound
    n hn (3 * n + 1) target x (vertexEndpointRadialShell n) C 3 hC
    (vertexEndpointRadialShell_lt n) hpoint
  intro r _
  exact_mod_cast vertexEndpointRadialShell_card_le n r



theorem faceSpatialTargetResidualPotential_le_endpointRadialHarmonic
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) -> Real)
    (x : Option (FKIsingSquareFullFaceNode n))
    (C : Real) (hC : 0 <= C)
    (hpoint : forall z,
      faceSpatialTargetResidual n target z *
          facePointPoissonBarrier n z x <=
        C / ((n : Real) *
          ((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :
    faceSpatialTargetResidualPotential n target x <=
      C * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
  apply faceSpatialTargetResidualPotential_le_harmonic_of_radialShellBound
    n hn (3 * n + 1) target x (faceEndpointRadialShell n) C 3 hC
    (faceEndpointRadialShell_lt n) hpoint
  intro r _
  exact_mod_cast faceEndpointRadialShell_card_le n r



theorem tendsto_endpointRadialHarmonic_div_natCast_succ :
    Filter.Tendsto (fun n : Nat =>
      (harmonic (3 * (n + 1) + 1) : Real) /
        ((n + 1 : Nat) : Real)) Filter.atTop (nhds 0) := by
  have hone : Filter.Tendsto (fun n : Nat =>
      1 / ((n + 1 : Nat) : Real)) Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : Nat => 1 / ((n : Real) + 1))
          Filter.atTop (nhds 0))
  have hlogBase : Filter.Tendsto (fun n : Nat =>
      Real.log (n : Real) / (n : Real)) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : Nat =>
      Real.log ((n + 1 : Nat) : Real) / ((n + 1 : Nat) : Real))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hlogBase.comp (Filter.tendsto_add_atTop_nat 1)
  have hupper : Filter.Tendsto (fun n : Nat =>
      (1 + Real.log 4 + Real.log ((n + 1 : Nat) : Real)) /
        ((n + 1 : Nat) : Real)) Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : Nat => 1 + Real.log 4)
        Filter.atTop (nhds (1 + Real.log 4)) := tendsto_const_nhds
    convert (hconst.mul hone).add hlog using 1
    · funext n
      field_simp
    · norm_num
  apply squeeze_zero
  · intro n
    exact div_nonneg (by
      rw [harmonic, Rat.cast_sum]
      exact Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
  · exact fun k => div_le_div_of_nonneg_right (by
      calc
        (harmonic (3 * (k + 1) + 1) : Real) <=
            1 + Real.log (3 * (k + 1) + 1) :=
          by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
              Nat.cast_ofNat] using
            harmonic_le_one_add_log (3 * (k + 1) + 1)
        _ <= 1 + Real.log (4 * (k + 1)) := by
          have hlogle : Real.log (3 * ((k : Real) + 1) + 1) <=
              Real.log (4 * ((k : Real) + 1)) := by
            apply Real.log_le_log (by positivity)
            exact_mod_cast
              (show 3 * (k + 1) + 1 <= 4 * (k + 1) by omega)
          linarith
        _ = 1 + Real.log 4 + Real.log ((k + 1 : Nat) : Real) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          push_cast
          ring) (by positivity)
  · exact hupper

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality

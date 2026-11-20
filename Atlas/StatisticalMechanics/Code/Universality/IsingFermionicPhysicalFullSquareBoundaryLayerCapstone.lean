/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian
import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian










namespace StatMech.Universality

open Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayerInwardIncrement_le_one
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k <= 1 := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  have hnorm := D.norm_fermionicObservable_le_one z
  unfold fkIsingSquareBoundaryLayerInwardIncrement
  change Complex.normSq (D.fermionicObservable z) <= 1
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (D.fermionicObservable z)]

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive
open FKIsingSquareBoundaryLayerIntegratedPrimitive

@[simp] theorem markedB_base (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareMarkedB n) = 0 := by
  unfold FKIsingSquareFullCoordinateOneForm.vertexPrimitive
  ring

theorem vertex_eq_of_common_face_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f)
    (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn f) := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn f
  rw [hface] at he
  linarith

theorem face_eq_of_common_vertex_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f)
    (hinc : fkIsingSquareBoundaryLayerRadialIncrement n hn e =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn f
  rw [hvertex] at he
  linarith

private theorem boundaryVertexProjection_algebra
    (F t : Complex)
    (hline : (starRingEnd Complex) F = t * F)
    (ht : Complex.normSq t = 1) :
    isingProj t
        ((isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹))) = F := by
  have hct : (starRingEnd Complex) t * t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ht]
    norm_num
  have hlamConj : (starRingEnd Complex) isingLambda = isingLambda⁻¹ := by
    rw [isingLambda_inv_val, isingLambda_val]
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im]
  unfold isingProj
  rw [map_mul, map_mul, map_add, map_one, map_inv₀, hline,
    hlamConj, inv_inv]
  rw [show (starRingEnd Complex)
      (isingFermionicBoundaryVertexNormalization : Complex) =
        isingFermionicBoundaryVertexNormalization by simp]
  have hcollapse : (starRingEnd Complex) t *
      ((isingFermionicBoundaryVertexNormalization : Complex) *
        (t * F * (1 + isingLambda))) =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        F * (1 + isingLambda) := by
    calc
      _ = (isingFermionicBoundaryVertexNormalization : Complex) *
          (((starRingEnd Complex) t * t) * F) *
            (1 + isingLambda) := by ring
      _ = _ := by rw [hct]; ring
  rw [hcollapse]
  rw [isingLambda_inv]
  have hden : (2 + Real.sqrt 2 : Real) ≠ 0 := by positivity
  have hdenC : ((2 + Real.sqrt 2 : Real) : Complex) ≠ 0 := by
    exact_mod_cast hden
  have hdenC' : (2 + (Real.sqrt 2 : Complex)) ≠ 0 := by
    simpa using hdenC
  unfold isingFermionicBoundaryVertexNormalization
  push_cast
  field_simp [hdenC']
  ring

private theorem boundaryVertexProjection_endpoint_algebra
    (F t : Complex)
    (hline : (starRingEnd Complex) F = t * F)
    (ht : Complex.normSq t = 1) :
    isingProj (t * isingLambda ^ 2)
        ((isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹))) = F * isingLambda⁻¹ := by
  have hct : (starRingEnd Complex) t * t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ht]
    norm_num
  have hlamConj : (starRingEnd Complex) isingLambda = isingLambda⁻¹ := by
    rw [isingLambda_inv_val, isingLambda_val]
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im]
  unfold isingProj
  rw [map_mul, map_pow, map_mul, map_mul, map_add, map_one, map_inv₀,
    hline, hlamConj, inv_inv]
  rw [show (starRingEnd Complex)
      (isingFermionicBoundaryVertexNormalization : Complex) =
        isingFermionicBoundaryVertexNormalization by simp]
  have hcollapse : (starRingEnd Complex) t * (isingLambda⁻¹) ^ 2 *
      ((isingFermionicBoundaryVertexNormalization : Complex) *
        (t * F * (1 + isingLambda))) =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        ((isingLambda⁻¹) ^ 2 * F) * (1 + isingLambda) := by
    calc
      _ = (isingFermionicBoundaryVertexNormalization : Complex) *
          ((isingLambda⁻¹) ^ 2 *
            (((starRingEnd Complex) t * t) * F)) *
              (1 + isingLambda) := by ring
      _ = _ := by rw [hct]; ring
  rw [hcollapse]
  have hden : (2 + Real.sqrt 2 : Real) ≠ 0 := by positivity
  have hdenC : (2 + (Real.sqrt 2 : Complex)) ≠ 0 := by
    exact_mod_cast hden
  have hs : (Real.sqrt 2 : Complex) = isingLambda + isingLambda⁻¹ := by
    rw [isingLambda_inv]
    ring
  have hsum :
      1 + isingLambda⁻¹ + (isingLambda⁻¹) ^ 2 * (1 + isingLambda) =
        (2 + (Real.sqrt 2 : Complex)) * isingLambda⁻¹ := by
    rw [hs]
    field_simp [isingLambda_ne]
    ring
  calc
    _ = ((1 / 2 : Complex) *
          (isingFermionicBoundaryVertexNormalization : Complex) *
            (1 + isingLambda⁻¹ +
              (isingLambda⁻¹) ^ 2 * (1 + isingLambda))) * F := by ring
    _ = ((1 / 2 : Complex) *
          (isingFermionicBoundaryVertexNormalization : Complex) *
            ((2 + (Real.sqrt 2 : Complex)) * isingLambda⁻¹)) * F := by
      rw [hsum]
    _ = F * isingLambda⁻¹ := by
      unfold isingFermionicBoundaryVertexNormalization
      push_cast
      field_simp [hdenC]



private noncomputable def bottomBoundaryProjectionReconstruction
    (west north : Complex) : Complex :=
  (1 - Complex.I) * west + (1 + Complex.I) * north

private theorem bottomBoundaryProjectionReconstruction_projection_west
    (west north : Complex)
    (hwest : (starRingEnd Complex) west = west)
    (hnorth : (starRingEnd Complex) north = -Complex.I * north) :
    isingProj 1 (bottomBoundaryProjectionReconstruction west north) = west := by
  unfold bottomBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_sub, map_add, map_one,
    Complex.conj_I, hwest, hnorth]
  norm_num
  ring_nf
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  rw [hI2]
  ring

private theorem bottomBoundaryProjectionReconstruction_projection_north
    (west north : Complex)
    (hwest : (starRingEnd Complex) west = west)
    (hnorth : (starRingEnd Complex) north = -Complex.I * north) :
    isingProj (-Complex.I)
        (bottomBoundaryProjectionReconstruction west north) = north := by
  unfold bottomBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_sub, map_add, map_one,
    map_neg, Complex.conj_I, hwest, hnorth]
  norm_num
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, hI2]
    ring
  ring_nf
  rw [hI2, hI3]
  ring



private noncomputable def rightBoundaryProjectionReconstruction
    (north west : Complex) : Complex :=
  (1 + Complex.I) * north + (1 - Complex.I) * west

private theorem rightBoundaryProjectionReconstruction_projection_north
    (north west : Complex)
    (hnorth : (starRingEnd Complex) north = -north)
    (hwest : (starRingEnd Complex) west = -Complex.I * west) :
    isingProj (-1) (rightBoundaryProjectionReconstruction north west) =
      north := by
  unfold rightBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, map_neg, hnorth, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

private theorem rightBoundaryProjectionReconstruction_projection_west
    (north west : Complex)
    (hnorth : (starRingEnd Complex) north = -north)
    (hwest : (starRingEnd Complex) west = -Complex.I * west) :
    isingProj (-Complex.I)
        (rightBoundaryProjectionReconstruction north west) = west := by
  unfold rightBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, map_neg, hnorth, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq],
    show Complex.I ^ 3 = -Complex.I by
      rw [show (3 : Nat) = 2 + 1 by omega, pow_succ,
        show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
      ring]
  ring



private noncomputable def bottomMissingSouthProjectionReconstruction
    (east west : Complex) : Complex :=
  (1 + Complex.I) * east + (1 - Complex.I) * west

private theorem bottomMissingSouthProjectionReconstruction_projection_east
    (east west : Complex)
    (heast : (starRingEnd Complex) east = Complex.I * east)
    (hwest : (starRingEnd Complex) west = -west) :
    isingProj Complex.I
        (bottomMissingSouthProjectionReconstruction east west) = east := by
  unfold bottomMissingSouthProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, heast, hwest]
  norm_num
  ring_nf
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, hI2]
    ring
  rw [hI2, hI3]
  ring

private theorem bottomMissingSouthProjectionReconstruction_projection_west
    (east west : Complex)
    (heast : (starRingEnd Complex) east = Complex.I * east)
    (hwest : (starRingEnd Complex) west = -west) :
    isingProj (-1)
        (bottomMissingSouthProjectionReconstruction east west) = west := by
  unfold bottomMissingSouthProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one, map_neg,
    heast, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

private theorem isingProj_I_conj_line (z : Complex) :
    (starRingEnd Complex) (isingProj Complex.I z) =
      Complex.I * isingProj Complex.I z := by
  unfold isingProj
  simp only [map_mul, map_add, map_one, Complex.conj_I, map_neg,
    starRingEnd_apply]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

private theorem isingProj_negOne_conj_line (z : Complex) :
    (starRingEnd Complex) (isingProj (-1) z) =
      -isingProj (-1) z := by
  unfold isingProj
  simp only [map_mul, map_add, map_one, map_neg, starRingEnd_apply]
  norm_num
  ring

theorem boundaryLayerEndpoint_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda ^ 2 := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]



theorem boundaryVertexFermion_projection_inward
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)))
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj t _ = F
  rw [hvertex]
  apply boundaryVertexProjection_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerInward_directedTangent]
  cases side <;> norm_num



theorem boundaryVertexFermion_projection_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerEndpointSide side)))
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  rw [boundaryLayerEndpoint_directedTangent]
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
  change isingProj (t * isingLambda ^ 2) _ = F * isingLambda⁻¹
  rw [hvertex]
  apply boundaryVertexProjection_endpoint_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerInward_directedTangent]
  cases side <;> norm_num



noncomputable def fkIsingSquareBoundaryLayerComplementVertexFermion
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  (isingFermionicBoundaryVertexNormalization : Complex) *
    (D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) +
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)))

theorem fkIsingSquareBoundaryLayerComplementInward_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) =
      match side with
      | .bottom => -1
      | .right => Complex.I
      | .top => 1
      | .left => -Complex.I := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).2.1
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).2.1
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).1
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).1

theorem boundaryLayerComplementEndpoint_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda ^ 2 := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .north)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.2,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_horizontal_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      change fkIsingSquareWiredDirectedTangent n hn (.dart (e, .south)) =
        fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) *
          isingLambda ^ 2
      rw [(fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).2.2.1,
        (fkIsingSquareWiredDirectedTangent_vertical_local
          n hn e haxis).1, isingLambda_sq]
      norm_num [Complex.I_sq]

theorem complementBoundaryVertexFermion_projection_inward
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)))
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj t _ = F
  rw [hvertex]
  apply boundaryVertexProjection_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerComplementInward_directedTangent]
  cases side <;> norm_num

theorem complementBoundaryVertexFermion_projection_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementEndpointSide side)))
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let F := D.fermionicObservable z
  let t := fkIsingSquareWiredDirectedTangent n hn z
  have hsquare : t * F ^ 2 = (Complex.normSq F : Complex) := by
    simpa only [t, F, z, D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hline : (starRingEnd Complex) F = t * F :=
    conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq t F hsquare
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  rw [boundaryLayerComplementEndpoint_directedTangent]
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
  change isingProj (t * isingLambda ^ 2) _ = F * isingLambda⁻¹
  rw [hvertex]
  apply boundaryVertexProjection_endpoint_algebra F t hline
  simp only [t, z,
    fkIsingSquareBoundaryLayerComplementInward_directedTangent]
  cases side <;> norm_num

theorem fkIsingSquareBoundaryLayerComplementVertexFermion_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let F := D.fermionicObservable
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side))
  let c := isingFermionicBoundaryVertexNormalization
  have hvertex : fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  rw [hvertex, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, isingLambda_one_add_inv_normSq]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  change (c * c) * (Complex.normSq F * (2 + Real.sqrt 2)) =
    isingFermionicBoundaryVertexNormSqFactor * Complex.normSq F
  rw [show c * c = c ^ 2 by ring]
  calc
    c ^ 2 * (Complex.normSq F * (2 + Real.sqrt 2)) =
        (c ^ 2 * (2 + Real.sqrt 2)) * Complex.normSq F := by ring
    _ = _ := by
      rw [isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq]

theorem fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerComplementInwardSide side)) := by
  rw [fkIsingSquareBoundaryLayerComplementVertexFermion_normSq,
    <- mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]



noncomputable def fkIsingSquareBottomBoundaryMedialObservable
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom k
  bottomBoundaryProjectionReconstruction
    (D.fermionicObservable (.dart (e, .west)))
    (D.fermionicObservable (.dart (e, .north)))

theorem fkIsingSquareBottomBoundaryMedialObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj 1 (fkIsingSquareBottomBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k, .west)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom k
  let W := D.fermionicObservable (.dart (e, .west))
  let N := D.fermionicObservable (.dart (e, .north))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .bottom k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hW : (starRingEnd Complex) W = W := by
    simpa only [W, htW, one_mul] using hline (.dart (e, .west))
  have hN : (starRingEnd Complex) N = -Complex.I * N := by
    simpa only [N, htN] using hline (.dart (e, .north))
  change isingProj 1 (bottomBoundaryProjectionReconstruction W N) = W
  exact bottomBoundaryProjectionReconstruction_projection_west W N hW hN

theorem fkIsingSquareBottomBoundaryMedialObservable_projection_north
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-Complex.I)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom k
  let W := D.fermionicObservable (.dart (e, .west))
  let N := D.fermionicObservable (.dart (e, .north))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .bottom k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hW : (starRingEnd Complex) W = W := by
    simpa only [W, htW, one_mul] using hline (.dart (e, .west))
  have hN : (starRingEnd Complex) N = -Complex.I * N := by
    simpa only [N, htN] using hline (.dart (e, .north))
  change isingProj (-Complex.I)
      (bottomBoundaryProjectionReconstruction W N) = N
  exact bottomBoundaryProjectionReconstruction_projection_north W N hW hN



noncomputable def fkIsingSquareRightBoundaryMedialObservable
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k
  rightBoundaryProjectionReconstruction
    (D.fermionicObservable (.dart (e, .north)))
    (D.fermionicObservable (.dart (e, .west)))

theorem fkIsingSquareRightBoundaryMedialObservable_projection_north
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-1) (fkIsingSquareRightBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k
  let N := D.fermionicObservable (.dart (e, .north))
  let W := D.fermionicObservable (.dart (e, .west))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
    fkIsingSquarePerimeterEdge_axis n .right k
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hN : (starRingEnd Complex) N = -N := by
    simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
  have hW : (starRingEnd Complex) W = -Complex.I * W := by
    simpa only [W, htW] using hline (.dart (e, .west))
  change isingProj (-1) (rightBoundaryProjectionReconstruction N W) = N
  exact rightBoundaryProjectionReconstruction_projection_north N W hN hW

theorem fkIsingSquareRightBoundaryMedialObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-Complex.I)
        (fkIsingSquareRightBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k, .west)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k
  let N := D.fermionicObservable (.dart (e, .north))
  let W := D.fermionicObservable (.dart (e, .west))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
    fkIsingSquarePerimeterEdge_axis n .right k
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
    ⟨htW, _, _, htN⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hN : (starRingEnd Complex) N = -N := by
    simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
  have hW : (starRingEnd Complex) W = -Complex.I * W := by
    simpa only [W, htW] using hline (.dart (e, .west))
  change isingProj (-Complex.I)
      (rightBoundaryProjectionReconstruction N W) = W
  exact rightBoundaryProjectionReconstruction_projection_west N W hN hW



noncomputable def fkIsingSquareTopBoundaryMedialObservable
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k
  bottomMissingSouthProjectionReconstruction
    (D.fermionicObservable (.dart (e, .south)))
    (D.fermionicObservable (.dart (e, .east)))

theorem fkIsingSquareTopBoundaryMedialObservable_projection_south
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj Complex.I (fkIsingSquareTopBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k, .south)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k
  let S := D.fermionicObservable (.dart (e, .south))
  let E := D.fermionicObservable (.dart (e, .east))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .top k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨_, htE, htS, _⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hS : (starRingEnd Complex) S = Complex.I * S := by
    simpa only [S, htS] using hline (.dart (e, .south))
  have hE : (starRingEnd Complex) E = -E := by
    simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
  change isingProj Complex.I
      (bottomMissingSouthProjectionReconstruction S E) = S
  exact bottomMissingSouthProjectionReconstruction_projection_east S E hS hE

theorem fkIsingSquareTopBoundaryMedialObservable_projection_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    isingProj (-1) (fkIsingSquareTopBoundaryMedialObservable n hn k) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k, .east)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k
  let S := D.fermionicObservable (.dart (e, .south))
  let E := D.fermionicObservable (.dart (e, .east))
  have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
    fkIsingSquarePerimeterEdge_axis n .top k
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
    ⟨_, htE, htS, _⟩
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z *
          D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hS : (starRingEnd Complex) S = Complex.I * S := by
    simpa only [S, htS] using hline (.dart (e, .south))
  have hE : (starRingEnd Complex) E = -E := by
    simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
  change isingProj (-1)
      (bottomMissingSouthProjectionReconstruction S E) = E
  exact bottomMissingSouthProjectionReconstruction_projection_west S E hS hE



noncomputable def fkIsingSquareBottomBoundaryMissingSouthObservable
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) : Complex :=
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let east := isingProj Complex.I
    (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
  let west := isingProj (-1)
    (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
  bottomMissingSouthProjectionReconstruction east west

theorem fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    isingProj Complex.I
        (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) =
      isingProj Complex.I
        (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let east := isingProj Complex.I
    (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
  let west := isingProj (-1)
    (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
  change isingProj Complex.I
      (bottomMissingSouthProjectionReconstruction east west) = east
  exact bottomMissingSouthProjectionReconstruction_projection_east
    east west (isingProj_I_conj_line _) (isingProj_negOne_conj_line _)

theorem fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    isingProj (-1)
        (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) =
      isingProj (-1)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let east := isingProj Complex.I
    (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
  let west := isingProj (-1)
    (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
  change isingProj (-1)
      (bottomMissingSouthProjectionReconstruction east west) = west
  exact bottomMissingSouthProjectionReconstruction_projection_west
    east west (isingProj_I_conj_line _) (isingProj_negOne_conj_line _)

private def bottomBoundaryNorthInteriorRadialCell
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    FKIsingSquareInteriorRadialCell n :=
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  ⟨fullVertexNorthEdge n x hnorth, by
    intro s
    fin_cases s <;>
      simp [fullVertexNorthEdge, x, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, k1] <;>
      omega⟩




theorem fkIsingSquareBottomBoundaryObservable_quad
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k)
      (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (fullVertexNorthEdge n x hnorth))
      (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eW := fullVertexWestEdge n x hwest
  have heE : fkIsingSquarePerimeterEdge n .bottom k1 = eE := rfl
  have heW : fkIsingSquarePerimeterEdge n .bottom k0 = eW := by
    apply Subtype.ext
    simp only [eW, fullVertexWestEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [bottomBoundaryNorthInteriorRadialCell, eN, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (bottomBoundaryNorthInteriorRadialCell n hn k)
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, hNS, _⟩
  have hNEobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n :=
      ⟨(eN, .south), (bottomBoundaryNorthInteriorRadialCell n hn k).2 .south⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .west) := by
      have heast' : x.1 0 < (n : Int) := heast
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      apply fkIsingSquareDart_key_injective n
      simp [d, eN, eE, fullVertexNorthEdge, fullVertexEastEdge,
        fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
        fkIsingSquareDirectionAvailable, heast', fkIsingSquareDirectionDart,
        fkIsingSquareSideCorner, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .south)) [ZMOD 8]
      rw [hcE.1, hcN.2.2.1]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n :=
      ⟨(eW, .north), by
        rw [← heW]
        simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
          fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
          fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
          fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0]
        omega⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      have hnorth' : x.1 1 < (n : Int) := hnorth
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
        simp [fkIsingSquarePreviousDirection,
          fkIsingSquareDirectionAvailable, hnorth']
      calc
        _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eN, .west) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .north)) [ZMOD 8]
      rw [hcN.1, hcW.2.2.2]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let south := fkIsingSquareBottomBoundaryMissingSouthObservable n hn k
  let west := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .south
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj 1 east := by
        rw [← heE]
        simpa [east] using
          (fkIsingSquareBottomBoundaryMedialObservable_projection_west
            n hn k1).symm
  · simpa [south, east] using
      (fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east
        n hn k).symm
  · simpa [south, west] using
      fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west n hn k
  · calc
      isingProj (-Complex.I) west =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .north)) := by
        rw [← heW]
        simpa [west] using
          fkIsingSquareBottomBoundaryMedialObservable_projection_north n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .west
      _ = isingProj (-Complex.I) north := by rw [hNW]

private def bottomBoundaryCrossDart
    (n : Nat) (k : Fin (2 * n - 1)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  (fkIsingSquarePerimeterEdge n .bottom k0, .east)

private theorem bottomBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .bottom k0, .east) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem bottomBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (bottomBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let d := bottomBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (bottomBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .west = .east := by
    simp [fkIsingSquareNextDirection,
      fkIsingSquareDirectionAvailable, x,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .bottom k1, .south) := rfl

private theorem bottomBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem bottomBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem bottomBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .bottom k1, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .bottom k1, .south) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega



theorem bottomBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (bottomBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := bottomBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    simpa [d, k1] using bottomBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact bottomBoundaryCrossDart_ne_source n hn k hd
    · exact bottomBoundaryCrossDart_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k1] at h0
      omega
    · exact bottomBoundaryCrossMate_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, bottomBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring



theorem bottom_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := bottomBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    simpa [d, k1] using bottomBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (bottomBoundaryCrossDart_ne_source n hn k)
      (bottomBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, bottomBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .bottom k1, .south)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .bottom k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .bottom k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) :=
        hcross.symm
      _ = _ := by simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
          fkIsingSquareBoundaryLayerInwardSide] using hstandard
  have hinv3 : (isingLambda⁻¹) ^ 3 = -isingLambda := by
    field_simp [isingLambda_ne]
    rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
      isingLambda_sq]
    norm_num [Complex.I_sq]
  calc
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring

private theorem isingSquareSHolomorphicQuad_bottom_projection_cycle
    (south west north east : Complex)
    (h : IsingSquareSHolomorphicQuad south west north east) :
    isingProj 1 north = isingProj 1 east ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  rcases h with ⟨hSW, hNE, hdiag⟩
  constructor <;>
    apply Complex.ext <;>
    simp [isingProj, Complex.ext_iff] at hSW hNE hdiag ⊢ <;>
    linarith



theorem isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition
    (north east west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj 1 north) =
      -2 * Complex.normSq (isingProj 1 north) -
        Complex.normSq (isingProj (-Complex.I) east) -
        Complex.normSq (isingProj 1 west) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hden : 1 + Real.sqrt 2 ≠ 0 := by positivity
  simp [isingPrimalProjectionDivergenceWithoutSouth, isingProj,
    Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, isingFermionicGhostCoefficient,
    hsqrt_ne] at hNE hWN hphase ⊢
  field_simp [hsqrt_ne, hden] at hphase ⊢
  have hEre : east.re = north.re := by linarith
  have hNim : north.im = -(1 + Real.sqrt 2) * north.re := by
    linarith [hphase.1]
  have hWim : west.im = north.re + north.im - west.re := by
    linarith [hWN.1]
  rw [hEre, hWim, hNim]
  ring_nf
  nlinarith

theorem isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos
    (north east west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj 1 north) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition
    north east west hNE hWN hphase]
  have hN := Complex.normSq_nonneg (isingProj 1 north)
  have hE := Complex.normSq_nonneg (isingProj (-Complex.I) east)
  have hW := Complex.normSq_nonneg (isingProj 1 west)
  linarith


noncomputable def isingPrimalProjectionDivergenceWithoutEast
    (north south west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)



theorem isingPrimalProjectionDivergenceWithoutEast_right_decomposition
    (north south west : Complex)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    isingPrimalProjectionDivergenceWithoutEast north south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-Complex.I) west) =
      -2 * Complex.normSq (isingProj (-Complex.I) west) -
        Complex.normSq (isingProj (-1) north) -
        Complex.normSq (isingProj (-Complex.I) south) := by
  have hsame : Complex.normSq (isingProj (-1) west) =
      Complex.normSq (isingProj (-Complex.I) west) := by
    have hlam : Complex.normSq isingLambda = 1 := by
      rw [isingLambda_val]
      norm_num [Complex.normSq_apply]
    rw [hphase, Complex.normSq_mul, Complex.normSq_neg,
      hlam, one_mul]
  have hfar : Complex.normSq (isingProj Complex.I west) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-Complex.I) west) := by
    rw [isingLambda_val] at hphase
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
    simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
      Complex.div_re, Complex.div_im] at hphase ⊢
    field_simp at hphase ⊢
    have hlinear : Real.sqrt 2 * west.re +
        (Real.sqrt 2 + 2) * west.im = 0 := by
      linarith [hphase.2]
    have hprod : Real.sqrt 2 *
        (west.re + (1 + Real.sqrt 2) * west.im) = 0 := by
      calc
        _ = Real.sqrt 2 * west.re +
            (Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 2) * west.im := by ring
        _ = Real.sqrt 2 * west.re +
            (Real.sqrt 2 + 2) * west.im := by rw [hsqrt]
        _ = 0 := hlinear
    have hWx : west.re = -(1 + Real.sqrt 2) * west.im := by
      have hz := (mul_eq_zero.mp hprod).resolve_left hsqrt_ne
      linarith
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
    have hsq3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = _ := by rw [hsq2]
    rw [hWx]
    ring_nf
    rw [hsq2, hsq3]
    ring
  have hpairS_I := isingProj_normSq_add_neg Complex.I south (by norm_num)
  have hpairS_one := isingProj_normSq_add_neg 1 south (by norm_num)
  have hS : Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south) =
      Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj (-Complex.I) south) := by
    rw [← hSW]
    linarith
  have hWNnorm := congrArg Complex.normSq hWN
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  unfold isingPrimalProjectionDivergenceWithoutEast
  rw [hghost]
  nlinarith [hS, hWNnorm, hsame, hfar]

theorem isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos
    (north south west : Complex)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    isingPrimalProjectionDivergenceWithoutEast north south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-Complex.I) west) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutEast_right_decomposition
    north south west hSW hWN hphase]
  have hW := Complex.normSq_nonneg (isingProj (-Complex.I) west)
  have hN := Complex.normSq_nonneg (isingProj (-1) north)
  have hS := Complex.normSq_nonneg (isingProj (-Complex.I) south)
  linarith


noncomputable def isingPrimalProjectionDivergenceWithoutNorth
    (east south west : Complex) : Real :=
  Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)



theorem isingPrimalProjectionDivergenceWithoutNorth_top_decomposition
    (east south west : Complex)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south) :
    isingPrimalProjectionDivergenceWithoutNorth east south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-1) south) =
      -2 * Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-1) east) -
        Complex.normSq (isingProj Complex.I west) := by
  have hsame : Complex.normSq (isingProj Complex.I south) =
      Complex.normSq (isingProj (-1) south) := by
    have hlam : Complex.normSq isingLambda = 1 := by
      rw [isingLambda_val]
      norm_num [Complex.normSq_apply]
    rw [hphase, Complex.normSq_mul, Complex.normSq_neg,
      hlam, one_mul]
  have hfar : Complex.normSq (isingProj 1 south) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-1) south) := by
    rw [isingLambda_val] at hphase
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
      Complex.div_re, Complex.div_im] at hphase ⊢
    field_simp at hphase ⊢
    have hSx : south.re = (1 + Real.sqrt 2) * south.im := by
      linarith [hphase.1]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
    rw [hSx]
    ring_nf
    rw [hsq2]
    ring
  have hpairE_I := isingProj_normSq_add_neg Complex.I east (by norm_num)
  have hpairE_one := isingProj_normSq_add_neg 1 east (by norm_num)
  have hE : Complex.normSq (isingProj 1 east) -
        Complex.normSq (isingProj (-Complex.I) east) =
      Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj (-1) east) := by
    rw [← hES]
    linarith
  have hSWnorm := congrArg Complex.normSq hSW
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  unfold isingPrimalProjectionDivergenceWithoutNorth
  rw [hghost]
  nlinarith [hE, hSWnorm, hsame, hfar]

theorem isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos
    (east south west : Complex)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south) :
    isingPrimalProjectionDivergenceWithoutNorth east south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-1) south) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutNorth_top_decomposition
    east south west hES hSW hphase]
  have hS := Complex.normSq_nonneg (isingProj (-1) south)
  have hE := Complex.normSq_nonneg (isingProj (-1) east)
  have hW := Complex.normSq_nonneg (isingProj Complex.I west)
  linarith

private theorem isingProj_normSq_negOne_of_bottom_phase
    (z : Complex)
    (hphase : isingProj (-Complex.I) z =
      -isingLambda * isingProj 1 z) :
    Complex.normSq (isingProj (-1) z) =
      (3 + 2 * Real.sqrt 2) * Complex.normSq (isingProj 1 z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hzy : z.im = -(1 + Real.sqrt 2) * z.re := by
    linarith [hphase.1]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  rw [hzy]
  ring_nf
  rw [hsq2]
  ring

private theorem isingProj_normSq_I_of_right_phase
    (z : Complex)
    (hphase : isingProj (-1) z =
      -isingLambda * isingProj (-Complex.I) z) :
    Complex.normSq (isingProj Complex.I z) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-Complex.I) z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hlinear : Real.sqrt 2 * z.re +
      (Real.sqrt 2 + 2) * z.im = 0 := by
    linarith [hphase.2]
  have hprod : Real.sqrt 2 *
      (z.re + (1 + Real.sqrt 2) * z.im) = 0 := by
    calc
      _ = Real.sqrt 2 * z.re +
          (Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 2) * z.im := by ring
      _ = Real.sqrt 2 * z.re +
          (Real.sqrt 2 + 2) * z.im := by rw [hsqrt]
      _ = 0 := hlinear
  have hzx : z.re = -(1 + Real.sqrt 2) * z.im := by
    have hz := (mul_eq_zero.mp hprod).resolve_left hsqrt_ne
    linarith
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  have hsq3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = _ := by rw [hsq2]
  rw [hzx]
  ring_nf
  rw [hsq2, hsq3]
  ring

private theorem isingProj_normSq_one_of_top_phase
    (z : Complex)
    (hphase : isingProj Complex.I z =
      -isingLambda * isingProj (-1) z) :
    Complex.normSq (isingProj 1 z) =
      (3 + 2 * Real.sqrt 2) * Complex.normSq (isingProj (-1) z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hzx : z.re = (1 + Real.sqrt 2) * z.im := by
    linarith [hphase.1]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  rw [hzx]
  ring_nf
  rw [hsq2]
  ring



theorem isingPrimalProjectionDivergence_bottomRightCorner_decomposition
    (north west : Complex)
    (hbottom : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj (-Complex.I) north) -
          Complex.normSq (isingProj (-1) north)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj 1 north) +
            Complex.normSq (isingProj (-Complex.I) west)) =
      -4 * (Complex.normSq (isingProj 1 north) +
        Complex.normSq (isingProj (-Complex.I) west)) := by
  have hNfar := isingProj_normSq_negOne_of_bottom_phase north hbottom
  have hWfar := isingProj_normSq_I_of_right_phase west hright
  have hlam : Complex.normSq isingLambda = 1 := by
    rw [isingLambda_val]
    norm_num [Complex.normSq_apply]
  have hNnear := congrArg Complex.normSq hbottom
  have hWnear := congrArg Complex.normSq hright
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hNnear
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hWnear
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  nlinarith

theorem isingPrimalProjectionDivergence_bottomRightCorner_add_ghost_nonpos
    (north west : Complex)
    (hbottom : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj (-Complex.I) north) -
          Complex.normSq (isingProj (-1) north)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj 1 north) +
            Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
  rw [isingPrimalProjectionDivergence_bottomRightCorner_decomposition
    north west hbottom hright]
  have hN : 0 ≤ Complex.normSq (isingProj 1 north) := Complex.normSq_nonneg _
  have hW : 0 ≤ Complex.normSq (isingProj (-Complex.I) west) :=
    Complex.normSq_nonneg _
  linarith


theorem isingPrimalProjectionDivergence_topRightCorner_decomposition
    (south west : Complex)
    (htop : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj (-1) south) +
            Complex.normSq (isingProj (-Complex.I) west)) =
      -4 * (Complex.normSq (isingProj (-1) south) +
        Complex.normSq (isingProj (-Complex.I) west)) := by
  have hSfar := isingProj_normSq_one_of_top_phase south htop
  have hWfar := isingProj_normSq_I_of_right_phase west hright
  have hlam : Complex.normSq isingLambda = 1 := by
    rw [isingLambda_val]
    norm_num [Complex.normSq_apply]
  have hSnear := congrArg Complex.normSq htop
  have hWnear := congrArg Complex.normSq hright
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hSnear
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hWnear
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  nlinarith

theorem isingPrimalProjectionDivergence_topRightCorner_add_ghost_nonpos
    (south west : Complex)
    (htop : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj (-1) south) +
            Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
  rw [isingPrimalProjectionDivergence_topRightCorner_decomposition
    south west htop hright]
  have hS : 0 ≤ Complex.normSq (isingProj (-1) south) := Complex.normSq_nonneg _
  have hW : 0 ≤ Complex.normSq (isingProj (-Complex.I) west) :=
    Complex.normSq_nonneg _
  linarith



noncomputable def isingPrimalProjectionDivergenceWithoutWest
    (north east south : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south)



theorem isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg
    (north east south : Complex)
    (hNE : isingProj (-1) north = isingProj (-1) east)
    (hES : isingProj (-Complex.I) east =
      isingProj (-Complex.I) south)
    (hphase : isingProj 1 south =
      isingLambda * isingProj Complex.I north) :
    0 ≤ isingPrimalProjectionDivergenceWithoutWest north east south -
      isingFermionicGhostCoefficient *
        Complex.normSq (isingProj Complex.I north) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  have hsqrtCube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrtSq]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hghost : isingFermionicGhostCoefficient = 2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  simp [isingPrimalProjectionDivergenceWithoutWest, isingProj,
    Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, hsqrt_ne] at hNE hES hphase ⊢
  field_simp [hsqrt_ne] at hphase ⊢
  have hei : east.im = north.im := by linarith [hNE]
  have her : east.re = south.re + south.im - north.im := by
    linarith [hES.1]
  have hp := congrArg (fun z : Real => Real.sqrt 2 * z) hphase.1
  have hnr : north.re = north.im + Real.sqrt 2 * south.re := by
    dsimp at hp
    ring_nf at hp
    rw [hsqrtSq] at hp
    linarith
  rw [hei, her, hnr]
  ring_nf
  rw [hsqrtSq, hsqrtCube]
  nlinarith [sq_nonneg (south.im - north.im),
    sq_nonneg (north.im + (Real.sqrt 2 - 1) * south.re)]

private def leftInteriorEastDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .east), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩

private def leftInteriorSouthDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .south), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩




theorem left_boundary_interior_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (Quot.mk _ (leftInteriorEastDart n hn k)) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn
        (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareLeftVerticalEdge n hn k
  let j : Fin (2 * n) := ⟨2 * n - 1 - k.1, by omega⟩
  have hv : fkIsingSquareBoundaryVertex n (.left, j) =
      fkIsingSquareLeftVerticalUpper n hn k := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper] <;> omega
  have hperim : fkIsingSquarePerimeterEdge n .left j = e := by
    apply Subtype.ext
    change s(fkIsingSquareBoundaryVertex n (.left, j),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n (.left, j)) .south _) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn k) .south _)
    rw [Sym2.eq_iff]
    apply Or.inl
    refine ⟨hv, ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hwestNorth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
    let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
    have hw : w = (e, .west) := by
      apply Prod.ext
      · apply Subtype.ext
        change s(fkIsingSquareLeftVerticalLower n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalLower n hn k) .north
              (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
          s(fkIsingSquareLeftVerticalUpper n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalUpper n hn k) .south
              (fkIsingSquareLeftVerticalUpper_south_available n hn k))
        rw [Sym2.eq_iff]
        apply Or.inr
        constructor <;>
          apply Subtype.ext <;>
          funext i <;>
          fin_cases i <;>
          simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
            fkIsingSquareLeftVerticalLower,
            fkIsingSquareLeftVerticalUpper]
      · rfl
    have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
      rw [fkIsingSquareWiredBondMate_west]
      rfl
    have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have h := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
      n hn w hsource hterminal
    rw [hnorth, hw] at h
    exact h.symm
  have heastNorth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
    unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
    change Complex.normSq (D.fermionicObservable (.dart (e, .east))) =
      Complex.normSq (D.fermionicObservable (.dart (e, .north)))
    rw [<- hperim]
    have hobs := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .left j
    have hobs' : D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .north)) =
        D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .east)) *
            isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
        fkIsingSquareBoundaryLayerInwardSide] using hobs
    rw [hobs']
    change Complex.normSq _ = Complex.normSq (_ * isingLambda⁻¹)
    rw [Complex.normSq_mul]
    have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
      rw [isingLambda_inv_val]
      norm_num [Complex.normSq_apply]
    rw [hlam, mul_one]
  have hwestSouth :
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
    unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
    change Complex.normSq (D.fermionicObservable (.dart (e, .west))) =
      Complex.normSq (D.fermionicObservable (.dart (e, .south)))
    rw [<- hperim]
    have hobs :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .left j
    have hobs' : D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .south)) =
        D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .left j, .west)) *
            isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hobs
    rw [hobs']
    change Complex.normSq _ = Complex.normSq (_ * isingLambda⁻¹)
    rw [Complex.normSq_mul]
    have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
      rw [isingLambda_inv_val]
      norm_num [Complex.normSq_apply]
    rw [hlam, mul_one]
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south))
  exact heastNorth.trans (hwestNorth.symm.trans hwestSouth)

private theorem leftWiredBoundaryDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBondPhase n hn
      (fkIsingSquareWiredBoundaryDart n hn (.west k)) = -isingLambda := by
  let d := fkIsingSquareWiredBoundaryDart n hn (.west k)
  have hfwd : fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    right
    refine ⟨k, rfl, ?_⟩
    exact fkIsingSquareWiredBondMate_west n hn k
  unfold fkIsingSquareWiredBondPhase
  rw [fkIsingSquareWiredBondTurn, if_pos hfwd, isingLambda]
  rw [show Complex.I * ((((-6 : Int) : Real) *
      (Real.pi / 8) : Real) : Complex) =
      (Real.pi / 4 : Real) * Complex.I - Real.pi * Complex.I by
        push_cast
        ring]
  rw [Complex.exp_sub, Complex.exp_pi_mul_I]
  ring



theorem left_boundary_endpoint_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    let e := fkIsingSquareLeftVerticalEdge n hn k
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable (.dart (e, .south)) =
      isingLambda * D.fermionicObservable (.dart (e, .east)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareLeftVerticalEdge n hn k
  let j : Fin (2 * n) := ⟨2 * n - 1 - k.1, by omega⟩
  let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
  have hperim : fkIsingSquarePerimeterEdge n .left j = e := by
    apply Subtype.ext
    change s(fkIsingSquareBoundaryVertex n (.left, j),
        fkIsingSquareNeighbor n
          (fkIsingSquareBoundaryVertex n (.left, j)) .south _) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn k) .south _)
    rw [Sym2.eq_iff]
    apply Or.inl
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [j, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hw : w = (e, .west) := by
    apply Prod.ext
    · apply Subtype.ext
      change s(fkIsingSquareLeftVerticalLower n hn k,
          fkIsingSquareNeighbor n
            (fkIsingSquareLeftVerticalLower n hn k) .north _) =
        s(fkIsingSquareLeftVerticalUpper n hn k,
          fkIsingSquareNeighbor n
            (fkIsingSquareLeftVerticalUpper n hn k) .south _)
      rw [Sym2.eq_iff]
      apply Or.inr
      constructor <;>
        apply Subtype.ext <;>
        funext i <;>
        fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper]
    · rfl
  have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
    rw [fkIsingSquareWiredBondMate_west]
    rfl
  have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn w hsource hterminal
  have hnorthWest : D.fermionicObservable (.dart (e, .north)) =
      D.fermionicObservable (.dart (e, .west)) * (-isingLambda) := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn w)) =
      D.fermionicObservable (.bond w) *
        fkIsingSquareWiredBondPhase n hn w at hbond
    rw [hnorth, leftWiredBoundaryDart_bondPhase n hn k] at hbond
    simpa only [D, hw, fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      using hbond
  have hnorthEast : D.fermionicObservable (.dart (e, .north)) =
      D.fermionicObservable (.dart (e, .east)) * isingLambda⁻¹ := by
    rw [← hperim]
    simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
      fkIsingSquareBoundaryLayerInwardSide] using
      fkIsingSquareBoundaryLayer_fermionicObservable_endpoint n hn .left j
  have hwestEast : D.fermionicObservable (.dart (e, .west)) =
      isingLambda ^ 2 * D.fermionicObservable (.dart (e, .east)) := by
    rw [hnorthEast] at hnorthWest
    field_simp [isingLambda_ne] at hnorthWest ⊢
    ring_nf at hnorthWest ⊢
    have hlam4 : isingLambda ^ 4 = -1 := by
      rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
        isingLambda_sq]
      norm_num [Complex.I_sq]
    rw [hnorthWest]
    symm
    calc
      isingLambda ^ 2 *
          -(isingLambda ^ 2 * D.fermionicObservable (.dart (e, .west))) =
        -(isingLambda ^ 4) *
          D.fermionicObservable (.dart (e, .west)) := by ring
      _ = D.fermionicObservable (.dart (e, .west)) := by rw [hlam4]; ring
  have hsouthWest : D.fermionicObservable (.dart (e, .south)) =
      D.fermionicObservable (.dart (e, .west)) * isingLambda⁻¹ := by
    rw [← hperim]
    simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
      fkIsingSquareBoundaryLayerComplementInwardSide] using
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .left j
  change D.fermionicObservable (.dart (e, .south)) =
    isingLambda * D.fermionicObservable (.dart (e, .east))
  rw [hsouthWest, hwestEast]
  field_simp [isingLambda_ne]

private theorem faceSouthWest_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceSouthEdge n c, .west)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceWestEdge n c, .south)) := by
  let d := faceSouthWestDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceWestEdge n c, .south) := by
    simpa [d] using faceSouthWest_bondMate n hn c
  have haxisS : (fkIsingSquareOrientedEdge n (faceSouthEdge n c)).axis =
      .horizontal := by
    dsimp [faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n (faceWestEdge n c)).axis =
      .vertical := by
    dsimp [faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceSouthEdge n c) haxisS
    have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceWestEdge n c) haxisW
    simp [d, faceSouthWestDart, hcS.1, hcW.2.2.1, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceSouthWestDart] using h.symm

private theorem faceWestNorth_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceWestEdge n c, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceNorthEdge n c, .south)) := by
  let d := faceWestEastDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceNorthEdge n c, .south) := by
    simpa [d] using faceWestEast_bondMate n hn c
  have haxisW : (fkIsingSquareOrientedEdge n (faceWestEdge n c)).axis =
      .vertical := by
    dsimp [faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisN : (fkIsingSquareOrientedEdge n (faceNorthEdge n c)).axis =
      .horizontal := by
    dsimp [faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceWestEdge n c) haxisW
    have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceNorthEdge n c) haxisN
    simp [d, faceWestEastDart, hcW.2.1, hcN.2.2.1, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceWestEastDart] using h.symm

private theorem faceNorthEast_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceNorthEdge n c, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceEastEdge n c, .north)) := by
  let d := faceNorthEastDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceEastEdge n c, .north) := by
    simpa [d] using faceNorthEast_bondMate n hn c
  have haxisN : (fkIsingSquareOrientedEdge n (faceNorthEdge n c)).axis =
      .horizontal := by
    dsimp [faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n (faceEastEdge n c)).axis =
      .vertical := by
    dsimp [faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceNorthEdge n c) haxisN
    have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceEastEdge n c) haxisE
    simp [d, faceNorthEastDart, hcN.2.1, hcE.2.2.2, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceNorthEastDart] using h.symm

private theorem faceEastSouth_observable_eq
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceEastEdge n c, .west)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (faceSouthEdge n c, .north)) := by
  let d := faceEastWestDart n c
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (faceSouthEdge n c, .north) := by
    simpa [d] using faceEastWest_bondMate n hn c
  have haxisE : (fkIsingSquareOrientedEdge n (faceEastEdge n c)).axis =
      .vertical := by
    dsimp [faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n (faceSouthEdge n c)).axis =
      .horizontal := by
    dsimp [faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
    change fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
    rw [hmate]
    have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
      n hn (faceEastEdge n c) haxisE
    have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
      n hn (faceSouthEdge n c) haxisS
    simp [d, faceEastWestDart, hcE.1, hcS.2.2.2, Int.ModEq]
  have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    n hn d hcode
  change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart d.1) at h
  rw [hmate] at h
  simpa [d, faceEastWestDart] using h.symm


theorem wiredArc_vertex_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalUpper n hn k) := by
  let east : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorEastDart n hn k)
  let south : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorSouthDart n hn k)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn east =
      fkIsingSquareFullFaceOfRadialIncidence n hn south := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h := vertex_eq_of_common_face_increment_eq n hn south east hface.symm
    (left_boundary_interior_increment_eq n hn k).symm
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)) =
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .east)) at h
  simpa [fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
    fkIsingSquareLeftVerticalUpper] using h

private theorem wiredArc_lower_const
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩) := by
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  let P : Nat -> Prop := fun j => forall hj : j < 2 * n,
    H (fkIsingSquareLeftVerticalLower n hn ⟨j, hj⟩) =
      H (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩)
  have hP : forall j, P j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        have hstep := wiredArc_vertex_step n hn ⟨j, by omega⟩
        have heq : fkIsingSquareLeftVerticalUpper n hn ⟨j, by omega⟩ =
            fkIsingSquareLeftVerticalLower n hn ⟨j + 1, hj⟩ := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [fkIsingSquareLeftVerticalUpper,
              fkIsingSquareLeftVerticalLower] <;> ring
        change H _ = H _ at hstep
        rw [heq] at hstep
        exact hstep.symm.trans (ih (by omega))
  exact hP k.val k.isLt

private theorem wiredArc_lower_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareLeftVerticalLower n hn k) = 0 := by
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hlast := wiredArc_vertex_step n hn last
  have hupper : fkIsingSquareLeftVerticalUpper n hn last =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [last, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hupper, markedB_base] at hlast
  calc
    _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareLeftVerticalLower n hn last) := by
        rw [wiredArc_lower_const n hn k,
          wiredArc_lower_const n hn last]
    _ = 0 := hlast

theorem vertex_fixedBoundary_eq_zero
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x = 0 := by
  have hx0 : x.1 0 = -(n : Int) := hx
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  by_cases htop : x.1 1 = (n : Int)
  · have heq : x = fkIsingSquareMarkedB n := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [fkIsingSquareMarkedB] using hx0
      · simpa [fkIsingSquareMarkedB] using htop
    rw [heq, markedB_base]
  · let j : Nat := (x.1 1 + (n : Int)).toNat
    have hj0 : 0 <= x.1 1 + (n : Int) := by omega
    have hj : j < 2 * n := by
      rw [show j = Int.toNat (x.1 1 + (n : Int)) from rfl,
        Int.toNat_lt] <;> omega
    let k : Fin (2 * n) := ⟨j, hj⟩
    have heq : x = fkIsingSquareLeftVerticalLower n hn k := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [k, j, fkIsingSquareLeftVerticalLower] using hx0
      · simp [k, j, fkIsingSquareLeftVerticalLower,
          Int.toNat_of_nonneg hj0]
    rw [heq, wiredArc_lower_zero]

theorem vertex_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
  rw [vertex_fixedBoundary_eq_zero n hn x hx]



theorem bottom_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hx : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .north hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let hx : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .north hx
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let dW : FKIsingSquareInteriorRadialDart n := ⟨(e, .west), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  let dS : FKIsingSquareInteriorRadialDart n := ⟨(e, .south), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  have hmateW : fkIsingSquareWiredBondMate n hn dW.1 =
      (fkIsingSquarePerimeterEdge n .bottom k0, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dW.1 dW.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .north hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .north = .west := by
      simp [fkIsingSquareNextDirection, hwest]
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k0, .north) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .bottom k0, .north) = x := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [x, fkIsingSquarePerimeterEdge,
              fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
              fkIsingSquareOrientedEdge_directionEdge,
              fkIsingSquareDirectionEdgeOrientation,
              fkIsingSquareSideCorner, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
              fkIsingSquareNeighborSite, k0, k1] <;> ring
        have htargetDirection :
            fkIsingSquareDartDirection n
                (fkIsingSquarePerimeterEdge n .bottom k0, .north) = .west := by
          simp [fkIsingSquarePerimeterEdge,
            fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareSideCorner]
        simp only [fkIsingSquareDirectionDart_endpoint,
          fkIsingSquareDirectionDart_direction]
        rw [htargetEndpoint, htargetDirection]
        simp [fkIsingSquareDirectionDart,
          fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  have hmateS : fkIsingSquareWiredBondMate n hn dS.1 =
      (fkIsingSquarePerimeterEdge n .bottom k1, .west) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dS.1 dS.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .north hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .north = .east := by
      simp [fkIsingSquarePreviousDirection, heast]
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k1, .west) := rfl
  have hW := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dW.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dW)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dW)
  have hS := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dS.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dS)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dS)
  rw [hmateW] at hW
  rw [hmateS] at hS
  have hprev :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .bottom k1
  let dE : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .bottom k0, .east)
  have hdEout : dE ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hwire :=
      fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
    have hend := congrArg (fkIsingSquareDartEndpoint n) hi
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n dE at hend
    rw [hend] at hwire
    simp [dE, fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
    omega
  have hmateE : fkIsingSquareWiredBondMate n hn dE =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
      n hn dE hdEout]
    have hprevEdge : fkIsingSquareDartEndpoint n dE = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [dE, x, fkIsingSquarePerimeterEdge,
          fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
          fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hdirection : fkIsingSquareDartDirection n dE = .west := by
      simp [dE, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hturn : (fkIsingSquareSideCorner dE.2).2 = .counterclockwise := by
      rfl
    have hdErepr : dE =
        fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
      apply fkIsingSquareDart_key_injective n
      simp only [fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction]
      rw [hprevEdge, hdirection]
      simp [dE, fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
    rw [hdErepr]
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .west = .east := by
      simp [fkIsingSquareNextDirection, heast,
        fkIsingSquareDirectionAvailable, x,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .bottom k1, .south) := rfl
  have hdEsource : dE ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dE, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hdEterminal : dE ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dE, fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hE := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dE hdEsource hdEterminal
  rw [hmateE] at hE
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south))
  exact hW.symm.trans
    (hprev.symm.trans (hE.symm.trans (hnext.symm.trans hS)))



theorem bottom_boundary_vertex_difference_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.bottom, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let e := fkIsingSquarePerimeterEdge n .bottom k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.bottom, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let ep := fkIsingSquarePerimeterEdge n .bottom k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] <;> ring_nf
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at h1
  linarith



theorem bottom_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let he : fkIsingSquareDirectionAvailable n x .east := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let hw : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let eE := fullVertexEastEdge n x he
    let eN := fullVertexNorthEdge n x hnorth
    let eW := fullVertexWestEdge n x hw
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let he : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hw : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let xE := fkIsingSquareNeighbor n x .east he
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hw
  let eE := fullVertexEastEdge n x he
  let eN := fullVertexNorthEdge n x hnorth
  let eW := fullVertexWestEdge n x hw
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xE, xN, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right; right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 + 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xE, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
      · right; left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xN, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 + 1
          omega
    · rintro (rfl | rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .east he
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .west hw
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xN - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hEN, hEW, hNW]
    ring
  have hdE := vertex_difference_east n hn x he hnorth
  have hdN := vertex_difference_north n hn x hnorth hw
  have hdW := bottom_boundary_vertex_difference_west n hn k
  change H xE - H x = _ at hdE
  change H xN - H x = _ at hdN
  have hx0 : fkIsingSquareBoundaryVertex n (.bottom, k0) = xW := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xW, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
  have heW : fkIsingSquarePerimeterEdge n .bottom k0 = eW := by
    apply Subtype.ext
    simp only [eW, fullVertexWestEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  change H (fkIsingSquareBoundaryVertex n (.bottom, k0)) - H x = _ at hdW
  rw [hx0, heW] at hdW
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west)))
  rw [hLap, hdE, hdN, hdW]



theorem bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let eN := fullVertexNorthEdge n x hnorth
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutSouth
        (fkIsingSquareBoundaryFullMedialObservable n hn eN)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let he : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hw : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eE := fullVertexEastEdge n x he
  let eN := fullVertexNorthEdge n x hnorth
  let eW := fullVertexWestEdge n x hw
  let FN := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let FE := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let FW := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutSouth FN FE FW
  have heE : fkIsingSquarePerimeterEdge n .bottom k1 = eE := by
    rfl
  have heW : fkIsingSquarePerimeterEdge n .bottom k0 = eW := by
    apply Subtype.ext
    simp only [eW, fullVertexWestEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [x, fkIsingSquarePerimeterDirection,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    have he' := he
    have hw' := hw
    simp [fkIsingSquareDirectionAvailable] at he' hw'
    intro hper
    simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image] at hper
    obtain ⟨side, j, hj⟩ := hper
    have hedge : fkIsingSquarePerimeterEdge n side j = eN :=
      Subtype.ext hj
    cases side with
    | bottom =>
        have haxis := congrArg
          (fun e => (fkIsingSquareOrientedEdge n e).axis) hedge
        change (fkIsingSquareOrientedEdge n
            (fkIsingSquarePerimeterEdge n .bottom j)).axis =
          (fkIsingSquareOrientedEdge n eN).axis at haxis
        rw [fkIsingSquarePerimeterEdge_axis] at haxis
        have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
          dsimp [eN, fullVertexNorthEdge]
          rw [fkIsingSquareOrientedEdge_directionEdge]
          rfl
        rw [haxisN] at haxis
        contradiction
    | top =>
        have haxis := congrArg
          (fun e => (fkIsingSquareOrientedEdge n e).axis) hedge
        change (fkIsingSquareOrientedEdge n
            (fkIsingSquarePerimeterEdge n .top j)).axis =
          (fkIsingSquareOrientedEdge n eN).axis at haxis
        rw [fkIsingSquarePerimeterEdge_axis] at haxis
        have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
          dsimp [eN, fullVertexNorthEdge]
          rw [fkIsingSquareOrientedEdge_directionEdge]
          rfl
        rw [haxisN] at haxis
        contradiction
    | right =>
        simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge,
          eN, fullVertexNorthEdge] at hj
        rw [Sym2.eq_iff] at hj
        rcases hj with ⟨hbase, _⟩ | ⟨_, hnext⟩
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbase
          simp [fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite] at h0
          omega
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnext
          simp [fkIsingSquarePerimeterDirection,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
          omega
    | left =>
        simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge,
          eN, fullVertexNorthEdge] at hj
        rw [Sym2.eq_iff] at hj
        rcases hj with ⟨hbase, _⟩ | ⟨_, hnext⟩
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbase
          simp [fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite] at h0
          omega
        · have h0 := congrArg
            (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnext
          simp [fkIsingSquarePerimeterDirection,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
          omega
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨htNW, _, _, htNN⟩
  have hpairI := isingProj_normSq_add_neg (-Complex.I) FW (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 FW (by norm_num)
  simp only [neg_neg] at hpairI
  have hwestRewrite :
      Complex.normSq (isingProj (-Complex.I) FW) -
          Complex.normSq (isingProj 1 FW) =
        Complex.normSq (isingProj (-1) FW) -
          Complex.normSq (isingProj Complex.I FW) := by
    linarith
  rw [bottom_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) = _
  rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
        n hn eN heN .west,
      fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
        n hn eN heN .north,
      htNW, htNN]
  rw [<- heE, <- heW]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [<- fkIsingSquareBottomBoundaryMedialObservable_projection_west
        n hn k1,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_north
        n hn k1,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_north
        n hn k0,
      <- fkIsingSquareBottomBoundaryMedialObservable_projection_west
        n hn k0]
  change
    (Complex.normSq (isingProj 1 FE) -
        Complex.normSq (isingProj (-Complex.I) FE)) +
      (Complex.normSq (isingProj (-Complex.I) FN) -
        Complex.normSq (isingProj (-1) FN)) +
      (Complex.normSq (isingProj (-Complex.I) FW) -
        Complex.normSq (isingProj 1 FW)) = _
  rw [hwestRewrite]
  unfold isingPrimalProjectionDivergenceWithoutSouth
  ring



theorem right_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hx : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .west hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hx : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .west hx
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let dE : FKIsingSquareInteriorRadialDart n := ⟨(e, .east), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  let dN : FKIsingSquareInteriorRadialDart n := ⟨(e, .north), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  have hmateE : fkIsingSquareWiredBondMate n hn dE.1 =
      (fkIsingSquarePerimeterEdge n .right k0, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dE.1 dE.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .west hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .west = .south := by
      simp [fkIsingSquareNextDirection, hsouth]
    calc
      _ = fkIsingSquareDirectionDart n x .south hsouth .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k0, .north) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .right k0, .north) = x := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [x, fkIsingSquarePerimeterEdge,
              fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
              fkIsingSquareOrientedEdge_directionEdge,
              fkIsingSquareDirectionEdgeOrientation,
              fkIsingSquareSideCorner, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
              fkIsingSquareNeighborSite, k0, k1] <;> ring
        have htargetDirection :
            fkIsingSquareDartDirection n
                (fkIsingSquarePerimeterEdge n .right k0, .north) = .south := by
          simp [fkIsingSquarePerimeterEdge,
            fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareSideCorner]
        simp only [fkIsingSquareDirectionDart_endpoint,
          fkIsingSquareDirectionDart_direction]
        rw [htargetEndpoint, htargetDirection]
        simp [fkIsingSquareDirectionDart,
          fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  have hmateN : fkIsingSquareWiredBondMate n hn dN.1 =
      (fkIsingSquarePerimeterEdge n .right k1, .west) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dN.1 dN.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .west hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
      simp [fkIsingSquarePreviousDirection, hnorth]
    calc
      _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k1, .west) := rfl
  have hE := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dE.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dE)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dE)
  have hN := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dN.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dN)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dN)
  rw [hmateE] at hE
  rw [hmateN] at hN
  have hprev :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k1
  let dC : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .right k0, .east)
  have hdCout : dC ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hwire :=
      fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
    have hend := congrArg (fkIsingSquareDartEndpoint n) hi
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n dC at hend
    rw [hend] at hwire
    simp [dC, fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
    omega
  have hmateC : fkIsingSquareWiredBondMate n hn dC =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
      n hn dC hdCout]
    have hprevEdge : fkIsingSquareDartEndpoint n dC = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [dC, x, fkIsingSquarePerimeterEdge,
          fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
          fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hdirection : fkIsingSquareDartDirection n dC = .south := by
      simp [dC, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hdCrepr : dC =
        fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
      apply fkIsingSquareDart_key_injective n
      simp only [fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction]
      rw [hprevEdge, hdirection]
      simp [dC, fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
    rw [hdCrepr]
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .south = .north := by
      simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
        x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .right k1, .south) := rfl
  have hdCsource : dC ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dC, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hdCterminal : dC ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have he := congrArg
      (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
    simp [dC, fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
      fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
      fkIsingSquareMarkedB, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] at he
    have hk := k.isLt
    omega
  have hC := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dC hdCsource hdCterminal
  rw [hmateC] at hC
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east))
  exact hN.symm.trans (hnext.trans (hC.trans (hprev.trans hE)))

private def rightBoundaryCrossDart
    (n : Nat) (k : Fin (2 * n - 1)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  (fkIsingSquarePerimeterEdge n .right k0, .east)

private theorem rightBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right k0, .east) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem rightBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (rightBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let d := rightBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (rightBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, rightBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, rightBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, rightBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .south = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right k1, .south) := rfl

private theorem rightBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [rightBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem rightBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  simp [rightBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
    fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedB, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, k0] at he
  have hk := k.isLt
  omega

private theorem rightBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .right k1, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .right k1, .south) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right k1, .south) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega



theorem rightBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (rightBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := rightBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
    simpa [d, k1] using rightBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact rightBoundaryCrossDart_ne_source n hn k hd
    · exact rightBoundaryCrossDart_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k1] at h0
      omega
    · exact rightBoundaryCrossMate_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, rightBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring



theorem right_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := rightBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
    simpa [d, k1] using rightBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (rightBoundaryCrossDart_ne_source n hn k)
      (rightBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, rightBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .right k1, .south)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .right k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .right k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) :=
        hcross.symm
      _ = _ := by simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
          fkIsingSquareBoundaryLayerInwardSide] using hstandard
  have hinv3 : (isingLambda⁻¹) ^ 3 = -isingLambda := by
    field_simp [isingLambda_ne]
    rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
      isingLambda_sq]
    norm_num [Complex.I_sq]
  calc
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring



theorem right_boundary_vertex_difference_south
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.right, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.right, k1)
    let e := fkIsingSquarePerimeterEdge n .right k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.right, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.right, k1)
  let ep := fkIsingSquarePerimeterEdge n .right k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] <;> ring_nf
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .north)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hcomp
  linarith

private def rightBoundaryWestInteriorRadialCell
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    FKIsingSquareInteriorRadialCell n :=
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  ⟨fullVertexWestEdge n x hwest, by
    intro s
    fin_cases s <;>
      simp [fullVertexWestEdge, x, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, k1] <;>
      omega⟩



theorem right_boundary_projection_cycle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
    let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
    let west := fkIsingSquareBoundaryFullMedialObservable n hn
      (fullVertexWestEdge n x hwest)
    isingProj (-1) south = isingProj (-1) west ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let eW := fullVertexWestEdge n x hwest
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  have heN : fkIsingSquarePerimeterEdge n .right k1 = eN := rfl
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [rightBoundaryWestInteriorRadialCell, eW, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (rightBoundaryWestInteriorRadialCell n hn k)
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eW, .east),
      (rightBoundaryWestInteriorRadialCell n hn k).2 .east⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .north) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .counterclockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquareNextDirection n x .west = .south := by
        simp [fkIsingSquareNextDirection, hsouth]
      calc
        _ = fkIsingSquareDirectionDart n x .south hsouth .clockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eS, .north) := by
          rw [← heS]
          apply fkIsingSquareDart_key_injective n
          simp [fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
            fkIsingSquareDartDirection, fkIsingSquareSideCorner,
            fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
            fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation, x,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .north)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .east)) [ZMOD 8]
      rw [hcS.2.2.2, hcW.2.1]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eW, .north),
      (rightBoundaryWestInteriorRadialCell n hn k).2 .north⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
        simp [fkIsingSquarePreviousDirection, hnorth]
      calc
        _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eN, .west) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .north)) [ZMOD 8]
      rw [hcN.1, hcW.2.2.2]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  constructor
  · calc
      isingProj (-1) south =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .north)) := by
        rw [← heS]
        simpa [south] using
          fkIsingSquareRightBoundaryMedialObservable_projection_north n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa [west] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eW heW .east
      _ = isingProj (-1) west := by rw [hWE]
  · calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa [west] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eW heW .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj (-Complex.I) north := by
        rw [← heN]
        simpa [north] using
          (fkIsingSquareRightBoundaryMedialObservable_projection_west
            n hn k1).symm



theorem right_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let eN := fullVertexNorthEdge n x hnorth
    let eS := fullVertexSouthEdge n x hsouth
    let eW := fullVertexWestEdge n x hwest
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xN, xS, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right; right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · have hi := congrFun h 0
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        omega
      · right; left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xS, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 - 1
          omega
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xN, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 + 1
          omega
    · rintro (rfl | rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xN - H x) + (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hNS, hNW, hSW]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdW := vertex_difference_west n hn x hwest hsouth
  have hdS := right_boundary_vertex_difference_south n hn k
  change H xN - H x = _ at hdN
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.right, k0) = xS := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xS, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  change H (fkIsingSquareBoundaryVertex n (.right, k0)) - H x = _ at hdS
  rw [hx0, heS] at hdS
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdN, hdS, hdW]



theorem right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutEast
        (fkIsingSquareRightBoundaryMedialObservable n hn k1)
        (fkIsingSquareRightBoundaryMedialObservable n hn k0)
        (fkIsingSquareBoundaryFullMedialObservable n hn
          (fullVertexWestEdge n x hwest)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eN := fullVertexNorthEdge n x hnorth
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  have heN : fkIsingSquarePerimeterEdge n .right k1 = eN := rfl
  have heS : fkIsingSquarePerimeterEdge n .right k0 = eS := by
    apply Subtype.ext
    simp only [eS, fullVertexSouthEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [rightBoundaryWestInteriorRadialCell, eW, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (rightBoundaryWestInteriorRadialCell n hn k)
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutEast north south west
  rw [right_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) = _
  simp only [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] at hstd
  simp only [fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] at hcomp
  rw [heS] at hstd hcomp
  rw [hcomp, ← hstd]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [← heN, ← heS]
  rw [← fkIsingSquareRightBoundaryMedialObservable_projection_west
        n hn k1,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_north
        n hn k1,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_north
        n hn k0,
      ← fkIsingSquareRightBoundaryMedialObservable_projection_west
        n hn k0,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eW heW .east,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eW heW .south,
      hWE, hWS]
  have hpairI := isingProj_normSq_add_neg Complex.I south (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 south (by norm_num)
  change
    (Complex.normSq (isingProj (-Complex.I) north) -
        Complex.normSq (isingProj (-1) north)) +
      (Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-Complex.I) south)) +
      (Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj Complex.I west)) = _
  have hSouth : Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-Complex.I) south) =
      Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south) := by
    linarith
  rw [hSouth]
  unfold isingPrimalProjectionDivergenceWithoutEast
  ring



theorem top_boundary_transverse_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hx : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let e := fkIsingSquareDirectionEdge n x .south hx
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let hx : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .south hx
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let dE : FKIsingSquareInteriorRadialDart n := ⟨(e, .east), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  let dN : FKIsingSquareInteriorRadialDart n := ⟨(e, .north), by
    simp [e, x, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, k1, hn]
    omega⟩
  have hmateE : fkIsingSquareWiredBondMate n hn dE.1 =
      (fkIsingSquarePerimeterEdge n .top k0, .south) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dE.1 dE.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .south hx .counterclockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .south = .east := by
      simp [fkIsingSquareNextDirection, heast]
    calc
      _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k0, .south) := by
        apply fkIsingSquareDart_key_injective n
        have htargetEndpoint :
            fkIsingSquareDartEndpoint n
                (fkIsingSquarePerimeterEdge n .top k0, .south) = x := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [x, fkIsingSquarePerimeterEdge,
              fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
              fkIsingSquareOrientedEdge_directionEdge,
              fkIsingSquareDirectionEdgeOrientation,
              fkIsingSquareSideCorner, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
              fkIsingSquareNeighborSite, k0, k1] <;> ring
        have htargetDirection :
            fkIsingSquareDartDirection n
                (fkIsingSquarePerimeterEdge n .top k0, .south) = .east := by
          simp [fkIsingSquarePerimeterEdge,
            fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareSideCorner]
        simp only [fkIsingSquareDirectionDart_endpoint,
          fkIsingSquareDirectionDart_direction]
        rw [htargetEndpoint, htargetDirection]
        simp [fkIsingSquareDirectionDart,
          fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  have hmateN : fkIsingSquareWiredBondMate n hn dN.1 =
      (fkIsingSquarePerimeterEdge n .top k1, .east) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn dN.1 dN.2]
    change fkIsingSquareBondMate n hn
      (fkIsingSquareDirectionDart n x .south hx .clockwise) = _
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
      simp [fkIsingSquarePreviousDirection, hwest]
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k1, .east) := rfl
  have hE := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dE.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dE)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dE)
  have hN := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dN.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn dN)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn dN)
  rw [hmateE] at hE
  rw [hmateN] at hN
  have hprev :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  have hnext := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k1
  let dC : FKIsingMedialDart (fkSquareBoxPlanar n) :=
    (fkIsingSquarePerimeterEdge n .top k0, .west)
  have hdCout : dC ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hwire :=
      fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
    have hend := congrArg (fkIsingSquareDartEndpoint n) hi
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n dC at hend
    rw [hend] at hwire
    simp [dC, fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
    omega
  have hmateC : fkIsingSquareWiredBondMate n hn dC =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
      n hn dC hdCout]
    have hprevEdge : fkIsingSquareDartEndpoint n dC = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [dC, x, fkIsingSquarePerimeterEdge,
          fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
          fkIsingSquareOrientedEdge_directionEdge,
          fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
          fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hdirection : fkIsingSquareDartDirection n dC = .east := by
      simp [dC, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
    have hdCrepr : dC =
        fkIsingSquareDirectionDart n x .east heast .counterclockwise := by
      apply fkIsingSquareDart_key_injective n
      simp only [fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction]
      rw [hprevEdge, hdirection]
      simp [dC, fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
    rw [hdCrepr]
    simp only [fkIsingSquareBondMate,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir : fkIsingSquareNextDirection n x .east = .west := by
      simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
        x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      omega
    calc
      _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
        fkIsingSquareDirectionDart_congr n x hdir _ _ _
      _ = (fkIsingSquarePerimeterEdge n .top k1, .north) := rfl
  have hdCsource : dC ≠ fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hs := congrArg Prod.snd h
    simp [dC, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs
  have hdCterminal : dC ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have he := congrArg
      (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
    simp [dC, fkIsingSquareWiredTerminalDart,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
      fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
      fkIsingSquareMarkedB, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] at he
    have hk := k.isLt
    omega
  have hC := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn dC hdCsource hdCterminal
  rw [hmateC] at hC
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east))
  exact hN.symm.trans (hnext.trans (hC.trans (hprev.trans hE)))

private def topBoundaryCrossDart
    (n : Nat) (k : Fin (2 * n - 1)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  (fkIsingSquarePerimeterEdge n .top k0, .west)

private theorem topBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top k0, .west) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem topBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (topBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let d := topBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (topBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, topBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .east heast .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .east = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top k1, .north) := rfl

private theorem topBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [topBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem topBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  simp [topBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
    fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedB, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, k0] at he
  have hk := k.isLt
  omega

private theorem topBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .top k1, .north) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .top k1, .north) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top k1, .north) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega



theorem topBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (topBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := topBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    simpa [d, k1] using topBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact topBoundaryCrossDart_ne_source n hn k hd
    · exact topBoundaryCrossDart_not_boundary n hn k ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k1] at h0
      omega
    · exact topBoundaryCrossMate_not_boundary n hn k ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, topBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring



theorem top_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := topBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    simpa [d, k1] using topBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (topBoundaryCrossDart_ne_source n hn k)
      (topBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, topBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .top k1, .north)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .top k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .top k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) := hcross.symm
      _ = _ := by simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
          fkIsingSquareBoundaryLayerInwardSide] using hstandard
  have hinv3 : (isingLambda⁻¹) ^ 3 = -isingLambda := by
    field_simp [isingLambda_ne]
    rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
      isingLambda_sq]
    norm_num [Complex.I_sq]
  calc
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring



theorem top_boundary_vertex_difference_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.top, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.top, k1)
    let e := fkIsingSquarePerimeterEdge n .top k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.top, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.top, k1)
  let ep := fkIsingSquarePerimeterEdge n .top k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .east), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .south), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n (ep, .east) =
      fkIsingSquareWedgeFaceKey n (ep, .south)
    simp [ep, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] <;> ring_nf
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .east)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .south)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hcomp
  linarith

private def topBoundarySouthInteriorRadialCell
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    FKIsingSquareInteriorRadialCell n :=
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  ⟨fullVertexSouthEdge n x hsouth, by
    intro s
    fin_cases s <;>
      simp [fullVertexSouthEdge, x, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, k1] <;>
      omega⟩



theorem top_boundary_projection_cycle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
    let south := fkIsingSquareBoundaryFullMedialObservable n hn
      (fullVertexSouthEdge n x hsouth)
    let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
    isingProj Complex.I east = isingProj Complex.I south ∧
      isingProj (-1) south = isingProj (-1) west := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : fkIsingSquarePerimeterEdge n .top k1 = eW := rfl
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [topBoundarySouthInteriorRadialCell, eS, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (topBoundarySouthInteriorRadialCell n hn k)
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, _, hSN⟩
  have hESobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eS, .east),
      (topBoundarySouthInteriorRadialCell n hn k).2 .east⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .south) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .south hsouth .counterclockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquareNextDirection n x .south = .east := by
        simp [fkIsingSquareNextDirection, heast]
      calc
        _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eE, .south) := by
          rw [← heE]
          apply fkIsingSquareDart_key_injective n
          simp [fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
            fkIsingSquareDartDirection, fkIsingSquareSideCorner,
            fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
            fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation, x,
            fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
            fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .south)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .east)) [ZMOD 8]
      rw [hcE.2.2.1, hcS.2.1]
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d : FKIsingSquareInteriorRadialDart n := ⟨(eS, .north),
      (topBoundarySouthInteriorRadialCell n hn k).2 .north⟩
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .east) := by
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .south hsouth .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
        simp [fkIsingSquarePreviousDirection, hwest]
      calc
        _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eW, .east) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .east)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .north)) [ZMOD 8]
      rw [hcW.2.1, hcS.2.2.2]
      decide
    have h := fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
      n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d] using h.symm
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  constructor
  · calc
      isingProj Complex.I east =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .south)) := by
        rw [← heE]
        simpa [east] using
          fkIsingSquareTopBoundaryMedialObservable_projection_south n hn k0
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa [south] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .east
      _ = isingProj Complex.I south := by rw [hSE]
  · calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa [south] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj (-1) west := by
        rw [← heW]
        simpa [west] using
          (fkIsingSquareTopBoundaryMedialObservable_projection_east
            n hn k1).symm



theorem top_boundary_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let heast : fkIsingSquareDirectionAvailable n x .east := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    let hwest : fkIsingSquareDirectionAvailable n x .west := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
      omega
    let eE := fullVertexEastEdge n x heast
    let eS := fullVertexSouthEdge n x hsouth
    let eW := fullVertexWestEdge n x hwest
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let xE := fkIsingSquareNeighbor n x .east heast
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {xE, xS, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right; right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 + 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xE, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · right; left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xS, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 - 1
          omega
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
    · rintro (rfl | rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .east heast
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hES, hEW, hSW]
    ring
  have hdE := top_boundary_vertex_difference_east n hn k
  have hdS := vertex_difference_south n hn x hsouth heast
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xS - H x = _ at hdS
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.top, k0) = xE := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xE, x, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0, k1] <;> ring
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  change H (fkIsingSquareBoundaryVertex n (.top, k0)) - H x = _ at hdE
  rw [hx0, heE] at hdE
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdE, hdS, hdW]



theorem top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    let hsouth : fkIsingSquareDirectionAvailable n x .south := by
      simp [x, fkIsingSquareDirectionAvailable,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
      exact hn
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      isingPrimalProjectionDivergenceWithoutNorth
        (fkIsingSquareTopBoundaryMedialObservable n hn k0)
        (fkIsingSquareBoundaryFullMedialObservable n hn
          (fullVertexSouthEdge n x hsouth))
        (fkIsingSquareTopBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  have heE : fkIsingSquarePerimeterEdge n .top k0 = eE := by
    apply Subtype.ext
    simp only [eE, fullVertexEastEdge, fkIsingSquarePerimeterEdge,
      fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;>
      apply Subtype.ext <;> funext i <;> fin_cases i <;>
      simp [x, fkIsingSquarePerimeterDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have heW : fkIsingSquarePerimeterEdge n .top k1 = eW := rfl
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [topBoundarySouthInteriorRadialCell, eS, x, k1] using
      fkIsingSquareInteriorRadialCell_not_mem_perimeter n
        (topBoundarySouthInteriorRadialCell n hn k)
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, hSS, _⟩
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
    isingPrimalProjectionDivergenceWithoutNorth east south west
  rw [top_boundary_vertex_laplacian_eq_increment_divergence n hn k]
  change
    (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eE, .north))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) = _
  simp only [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] at hstd
  simp only [fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] at hcomp
  rw [heE] at hstd hcomp
  rw [hcomp, ← hstd]
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [← heE, ← heW]
  rw [← fkIsingSquareTopBoundaryMedialObservable_projection_south
        n hn k0,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_east
        n hn k0,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eS heS .east,
      ← fkIsingSquareBoundaryFullMedialObservable_projection
        n hn eS heS .south,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_east
        n hn k1,
      ← fkIsingSquareTopBoundaryMedialObservable_projection_south
        n hn k1,
      hSE, hSS]
  have hpairI := isingProj_normSq_add_neg Complex.I east (by norm_num)
  have hpairOne := isingProj_normSq_add_neg 1 east (by norm_num)
  change
    (Complex.normSq (isingProj Complex.I east) -
        Complex.normSq (isingProj (-1) east)) +
      (Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south)) +
      (Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj Complex.I west)) = _
  have hEast : Complex.normSq (isingProj Complex.I east) -
        Complex.normSq (isingProj (-1) east) =
      Complex.normSq (isingProj 1 east) -
        Complex.normSq (isingProj (-Complex.I) east) := by
    linarith
  rw [hEast]
  unfold isingPrimalProjectionDivergenceWithoutNorth
  ring



theorem bottom_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let j : Fin (2 * n) := ⟨0, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k1, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (k0, j) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let j : Fin (2 * n) := ⟨0, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (k0, j)
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let hx : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .north hx
  have hedge : faceEastEdge n c = e := by
    have hv : faceSEVertex n c = x := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [faceSEVertex, c, x, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, k0, k1, j] <;> ring
    apply Subtype.ext
    simp only [faceEastEdge, e, fkIsingSquareDirectionEdge]
    let hface : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
      simp [fkIsingSquareDirectionAvailable, faceSEVertex, c,
        fkIsingSquareInteriorCellKey, fkIsingSquareInteriorFaceKey, j]
      exact hn
    have hnbr : fkIsingSquareNeighbor n (faceSEVertex n c) .north hface =
        fkIsingSquareNeighbor n x .north hx := by
      apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [faceSEVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, k0, k1, j] <;> ring
    exact congrArg₂ (fun a b => s(a, b)) hv hnbr
  have hdiff := face_difference_east n hn c (by
    have hk := k.isLt
    change k.1 + 1 < 2 * n
    omega)
  have htrans := bottom_boundary_transverse_increment_eq n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) at htrans
  rw [hedge] at hdiff
  have hcE : faceEastNeighbor n c (by
      have hk := k.isLt
      change k.1 + 1 < 2 * n
      omega) = (k1, j) := by
    apply Prod.ext
    · apply Fin.ext
      simp [faceEastNeighbor, c, k0, k1]
    · rfl
  rw [hcE] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (k1, j) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (k1, j) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (k0, j) = _ at hdiff
  rw [htrans] at hdiff
  linarith



theorem right_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k1) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (i, k0)
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hx : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .west hx
  have hedge : faceNorthEdge n c = e := by
    apply Subtype.ext
    simp only [faceNorthEdge, e, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceNWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i, k0, k1] <;> omega
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceNWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i, k0, k1] <;> omega
  have hdiff := face_difference_north n hn c (by
    have hk := k.isLt
    change k.1 + 1 < 2 * n
    omega)
  have htrans := right_boundary_transverse_increment_eq n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) at htrans
  rw [hedge] at hdiff
  have hcN : faceNorthNeighbor n c (by
      have hk := k.isLt
      change k.1 + 1 < 2 * n
      omega) = (i, k1) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [faceNorthNeighbor, c, k0, k1]
  rw [hcN] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i, k1) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i, k1) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (i, k0) = _ at hdiff
  rw [htrans] at hdiff
  linarith



theorem top_boundary_face_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let i0 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let i1 : Fin (2 * n) := ⟨k.1, by omega⟩
    let j : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i0, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i1, j) := by
  have hk := k.isLt
  let kp : Fin (2 * n - 1) := ⟨2 * n - 2 - k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨kp.1 + 1, by omega⟩
  let i0 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let i1 : Fin (2 * n) := ⟨k.1, by omega⟩
  let j : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  let c : FKIsingSquareFullFaceNode n := (i0, j)
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let hx : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let e := fkIsingSquareDirectionEdge n x .south hx
  have hedge : faceWestEdge n c = e := by
    apply Subtype.ext
    simp only [faceWestEdge, e, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceSWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i0, j, kp, k1] <;> omega
    · apply Subtype.ext
      funext q
      fin_cases q <;>
        simp [faceSWVertex, c, x, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
          fkIsingSquareBoundarySite, fkIsingSquareInteriorCellKey,
          fkIsingSquareInteriorFaceKey, i0, j, kp, k1] <;> omega
  have hi0 : 0 < i0.1 := by
    change 0 < k.1 + 1
    omega
  have hdiff := face_difference_west n hn c hi0
  have htrans := top_boundary_transverse_increment_eq n hn kp
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) at htrans
  rw [hedge] at hdiff
  have hcW : faceWestNeighbor n c hi0 = (i1, j) := by
    apply Prod.ext
    · apply Fin.ext
      simp [faceWestNeighbor, c, i0, i1]
    · rfl
  rw [hcW] at hdiff
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i0, j) = _
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (i1, j) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (i0, j) = _ at hdiff
  rw [htrans] at hdiff
  linarith

private theorem bottom_row_const
    (n : Nat) (hn : 0 < n) (i : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (i, z) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (z, z) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (⟨t, ht⟩, z) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, z) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := bottom_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t + 1, by omega⟩, z) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t, by omega⟩, z) at hs
        exact hs.trans (ih (by omega))
  exact hchain i.1 i.2

private theorem right_column_const
    (n : Nat) (hn : 0 < n) (j : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (last, j) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (last, z) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, ⟨t, ht⟩) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := right_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (last, ⟨t + 1, by omega⟩) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (last, ⟨t, by omega⟩) at hs
        exact hs.trans (ih (by omega))
  exact hchain j.1 j.2

private theorem top_row_const
    (n : Nat) (hn : 0 < n) (i : Fin (2 * n)) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (i, last) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (z, last) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hchain : ∀ t, (ht : t < 2 * n) →
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (⟨t, ht⟩, last) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
        have htstep : t < 2 * n - 1 := by omega
        let k : Fin (2 * n - 1) := ⟨t, htstep⟩
        have hs := top_boundary_face_step n hn k
        change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t + 1, by omega⟩, last) =
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (⟨t, by omega⟩, last) at hs
        exact hs.trans (ih (by omega))
  exact hchain i.1 i.2

private theorem terminalAdjacentFace_eq_topLeft
    (n : Nat) (hn : 0 < n) :
    let z : Fin (2 * n) := ⟨0, by omega⟩
    let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
    FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      (z, last) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  apply fkIsingSquareInteriorCellKey_injective n
  rw [show FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
    fkIsingSquareFullFaceOfRadialIncidence n hn
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence n hn)
    from rfl, fkIsingSquareFullFaceOfRadialIncidence_key]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
    fkIsingSquareInteriorCellKey n (z, last)
  simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
    fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation,
    fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareInteriorCellKey,
    fkIsingSquareInteriorFaceKey, z, last]



theorem boundaryLayer_terminalDart_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  rw [<- D.fermionicObservable_terminal]
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  have hbmem : (.bond (fkIsingSquareWiredTerminalDart n hn) :
      FKIsingSquareWiredCarrier n) ∈ D.exploration omega := by
    exact fkIsingSquareWired_terminalBond_mem_explorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  have htmem : (.terminal : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega := D.terminal_mem omega
  change D.fermionicSummand omega
      (.bond (fkIsingSquareWiredTerminalDart n hn)) =
    D.fermionicSummand omega .terminal
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hbmem, if_pos htmem]
  unfold FKIsingDobrushinDomain.windingPhase
  change (D.criticalMass omega : Complex) *
      Complex.exp (Complex.I *
        (((fkIsingSquareWiredLiftedWinding n hn
          (fkIsingSquareClosePerimeter n omega)
            (.bond (fkIsingSquareWiredTerminalDart n hn))) / 2 : Real) :
              Complex)) = _
  rw [show fkIsingSquareWiredLiftedWinding n hn
      (fkIsingSquareClosePerimeter n omega)
        (.bond (fkIsingSquareWiredTerminalDart n hn)) =
      fkIsingSquareWiredLiftedWinding n hn
        (fkIsingSquareClosePerimeter n omega) .terminal by
    unfold fkIsingSquareWiredLiftedWinding
      fkIsingSquareWiredPhysicalTurnCount
    rw [fkIsingSquareWired_terminalBond_rawTurnCount]]
  rfl

theorem boundaryLayer_terminalDart_increment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [boundaryLayer_terminalDart_observable n hn]
  norm_num

private theorem terminalAdjacent_bondMate_eq_topComplementEndpoint
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩).1 =
      (fkIsingSquarePerimeterEdge n .top
        (fkIsingSquarePerimeterLastIndex n hn), .south) := by
  let d := leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2]
  dsimp [d, leftInteriorEastDart]
  have hdart :
      (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
        fkIsingSquareDirectionDart n
          (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
          .south (fkIsingSquareLeftVerticalUpper_south_available n hn _)
          .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareLeftVerticalEdge, fkIsingSquareDirectionDart,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  rw [hdart]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
      .south _ .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n
      (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩) .south =
      .east := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalUpper, hn]
  calc
    _ = fkIsingSquareDirectionDart n
        (fkIsingSquareLeftVerticalUpper n hn ⟨2 * n - 1, by omega⟩)
        .east (by simp [fkIsingSquareDirectionAvailable,
          fkIsingSquareLeftVerticalUpper]; omega) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = _ := by
      apply fkIsingSquareDart_key_injective n
      simp [fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquarePerimeterLastIndex,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      · apply Subtype.ext
        funext i
        fin_cases i <;> simp <;> omega


theorem terminalAdjacentFace_eq_one (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) = 1 := by
  let last : Fin (2 * n) := fkIsingSquarePerimeterLastIndex n hn
  let d := leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩
  let e : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d
  have hmate : fkIsingSquareWiredBondMate n hn d.1 =
      (fkIsingSquarePerimeterEdge n .top last, .south) := by
    simpa [d, last] using
      terminalAdjacent_bondMate_eq_topComplementEndpoint n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    n hn d.1
      (fkIsingSquareInteriorRadialDart_ne_source n hn d)
      (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)
  rw [hmate] at hbond
  have hcomplement :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top last
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .south)) at hcomplement
  have hterminal := boundaryLayer_terminalDart_increment n hn
  rw [fkIsingSquareWiredTerminalDart_eq_perimeter_top_last n hn] at hterminal
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top last, .west)) = 1 at hterminal
  have hd : fkIsingSquareBoundaryLayerRadialIncrement n hn e = 1 := by
    change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart d.1) = 1
    rw [← hbond, ← hcomplement]
    exact hterminal
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero, hd] at hgap
  simpa [e, d, FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace,
    FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence] using hgap


theorem terminalAdjacentFace_nonneg (n : Nat) (hn : 0 < n) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
  let e := FKIsingSquareFullIntegratedPrimitive.terminalAdjacentIncidence n hn
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero] at hgap
  rw [show FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn e from rfl, hgap]
  exact fkIsingSquareBoundaryLayerRadialIncrement_nonneg n hn e


theorem terminalAdjacentFace_le_one (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
      (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) <= 1 := by
  let k : Fin (2 * n) := ⟨0, by omega⟩
  have hv : fkIsingSquareBoundaryVertex n (.left, k) =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [k, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedB]
  have hface : FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn .left k) := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace,
      fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn ⟨2 * n - 1, by omega⟩, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquarePerimeterInteriorRadialDart n .left k).1
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareLeftVerticalUpper,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k]
    omega
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn .left k
  rw [hv, markedB_base, sub_zero] at hgap
  rw [hface, hgap]
  exact fkIsingSquareBoundaryLayerInwardIncrement_le_one n hn .left k



theorem face_fixedBoundary_eq_terminal
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
  let z : Fin (2 * n) := ⟨0, by omega⟩
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hterminal :
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) =
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) := by
    rw [terminalAdjacentFace_eq_topLeft n hn]
  rcases hc with hbottom | hright | htop
  · have hc2 : c.2 = z := by
      apply Fin.ext
      simpa [z] using hbottom
    have hc' : c = (c.1, z) := by
      apply Prod.ext
      · rfl
      · exact hc2
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, z) := bottom_row_const n hn c.1
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := (bottom_row_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, last) := (right_column_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn last
      _ = _ := hterminal
  · have hc1 : c.1 = last := by
      apply Fin.ext
      simp [last]
      omega
    have hc' : c = (last, c.2) := by
      apply Prod.ext
      · exact hc1
      · rfl
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, z) := right_column_const n hn c.2
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (last, last) := (right_column_const n hn last).symm
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn last
      _ = _ := hterminal
  · have hc2 : c.2 = last := by
      apply Fin.ext
      simp [last]
      omega
    have hc' : c = (c.1, last) := by
      apply Prod.ext
      · rfl
      · exact hc2
    rw [hc']
    calc
      _ = (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (z, last) := top_row_const n hn c.1
      _ = _ := hterminal


theorem face_fixedBoundary_eq_one
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c = 1 := by
  rw [face_fixedBoundary_eq_terminal n hn c hc,
    terminalAdjacentFace_eq_one n hn]


theorem face_fixedBoundary_le_one
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c <= 1 := by
  rw [face_fixedBoundary_eq_terminal n hn c hc]
  exact terminalAdjacentFace_le_one n hn


theorem face_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    0 <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c := by
  rw [face_fixedBoundary_eq_terminal n hn c hc]
  exact terminalAdjacentFace_nonneg n hn



theorem boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k)) := by
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex
      n hn side k
  have hfixed := fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
    n hn side k hfree
  rw [face_fixedBoundary_eq_terminal n hn _ hfixed] at hgap
  linarith



theorem boundaryLayer_inwardIncrement_eq_one_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) := by
  rw [boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
      n hn side k hfree,
    terminalAdjacentFace_eq_one n hn]



theorem freeBoundary_vertex_le_one
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (side, k)) <= 1 := by
  have hgap :=
    boundaryLayer_inwardIncrement_eq_terminal_sub_vertex
      n hn side k hfree
  have hnonneg := fkIsingSquareBoundaryLayerInwardIncrement_nonneg
    n hn side k
  have hterminal := terminalAdjacentFace_le_one n hn
  linarith


theorem boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
            (fkIsingSquareBoundaryVertex n (side, k))) := by
  rw [fkIsingSquareBoundaryLayer_halfDiagonal_normSq,
    boundaryLayer_inwardIncrement_eq_terminal_sub_vertex n hn side k hfree]


theorem boundaryLayer_halfDiagonal_eq_ghost_one_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hfree : side ≠ .left) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (side, k))) := by
  rw [boundaryLayer_halfDiagonal_eq_ghost_terminal_sub_vertex
      n hn side k hfree,
    terminalAdjacentFace_eq_one n hn]

theorem bottom_boundary_complementIncrement_eq_terminal_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0,
          fkIsingSquareBoundaryLayerComplementInwardSide .bottom)) =
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (.bottom, k1)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d : FKIsingSquareInteriorRadialDart n :=
    ⟨(fkIsingSquarePerimeterEdge n .bottom k0, .north), by
      simp [fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
      omega⟩
  let r : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d
  have hend : fkIsingSquareInteriorRadialEndpoint n hn r =
      fkIsingSquareBoundaryVertex n (.bottom, k1) := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r, d, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hfaceeq : fkIsingSquareFullFaceOfRadialIncidence n hn r =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn .bottom k0) := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r, d, fkIsingSquarePerimeterInteriorRadialIncidence,
      fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0]
  have hface : fkIsingSquareFullFaceFixedBoundary n
      (fkIsingSquareFullFaceOfRadialIncidence n hn r) := by
    rw [hfaceeq]
    exact fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
      n hn .bottom k0 (by decide)
  have hgap :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r
  rw [hend, face_fixedBoundary_eq_terminal n hn _ hface] at hgap
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) at hcomp
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) at hgap
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) = _
  linarith

theorem bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion
          n hn .bottom k0) =
      isingFermionicGhostCoefficient *
        ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
            (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
            (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change Real.sqrt 2 / 2 * Complex.normSq
      (fkIsingSquareBoundaryLayerComplementVertexFermion
        n hn .bottom k0) = _
  rw [fkIsingSquareBoundaryLayerComplement_halfDiagonal_normSq]
  change isingFermionicGhostCoefficient *
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) = _
  have hgap :=
    bottom_boundary_complementIncrement_eq_terminal_sub_vertex n hn k
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) =
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (FKIsingSquareFullIntegratedPrimitive.terminalAdjacentFace n hn) -
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (.bottom, k1)) at hgap
  rw [hgap]



theorem bottom_boundary_complement_halfDiagonal_eq_ghost_one_sub_vertex
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerComplementVertexFermion
          n hn .bottom k0) =
      isingFermionicGhostCoefficient *
        (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareBoundaryVertex n (.bottom, k1))) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change Real.sqrt 2 / 2 * Complex.normSq
      (fkIsingSquareBoundaryLayerComplementVertexFermion
        n hn .bottom k0) =
    isingFermionicGhostCoefficient *
      (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareBoundaryVertex n (.bottom, k1)))
  rw [bottom_boundary_complement_halfDiagonal_eq_ghost_terminal_sub_vertex
      n hn k,
    terminalAdjacentFace_eq_one n hn]

private def bottomRightCornerLast (n : Nat) (hn : 0 < n) : Fin (2 * n) :=
  ⟨2 * n - 1, by omega⟩

private def bottomRightCornerZero (n : Nat) (hn : 0 < n) : Fin (2 * n) :=
  ⟨0, by omega⟩

private def bottomRightCornerCrossDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquarePerimeterEdge n .bottom (bottomRightCornerLast n hn), .east)

private theorem bottomRightCornerCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (bottomRightCornerCrossDart n hn) at hend
  rw [hend] at hwire
  simp [bottomRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem bottomRightCornerCrossDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (bottomRightCornerCrossDart n hn) =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) := by
  let x := fkIsingSquareBoundaryVertex n
    (.right, bottomRightCornerZero n hn)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := bottomRightCornerCrossDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (bottomRightCornerCrossDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomRightCornerCrossDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomRightCornerCrossDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomRightCornerCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .west = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := rfl

private def bottomRightCornerOtherDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquarePerimeterEdge n .bottom (bottomRightCornerLast n hn), .north)

private theorem bottomRightCornerOtherDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerOtherDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (bottomRightCornerOtherDart n hn) at hend
  rw [hend] at hwire
  simp [bottomRightCornerOtherDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem bottomRightCornerOtherDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (bottomRightCornerOtherDart n hn) =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .west) := by
  let x := fkIsingSquareBoundaryVertex n
    (.right, bottomRightCornerZero n hn)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := bottomRightCornerOtherDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (bottomRightCornerOtherDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomRightCornerOtherDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomRightCornerOtherDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .clockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomRightCornerOtherDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
    simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) := rfl

private theorem cornerDart_ne_source_terminal_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    d ≠ fkIsingSquareWiredSourceDart n hn ∧
      d ≠ fkIsingSquareWiredTerminalDart n hn := by
  constructor
  · intro h
    apply hd
    refine ⟨.bottom, ?_⟩
    simpa [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredSourceDart] using h.symm
  · intro h
    apply hd
    refine ⟨.top, ?_⟩
    simpa [fkIsingSquareWiredBoundaryEmbedding,
      fkIsingSquareWiredTerminalDart] using h.symm

private theorem bottomRightCornerOtherMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .west) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

private theorem bottomRightCornerCrossDart_ne_source
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomRightCornerCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem bottomRightCornerCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) :
    bottomRightCornerCrossDart n hn ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomRightCornerCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

private theorem bottomRightCornerCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

private theorem bottomRightCornerOtherDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (bottomRightCornerOtherDart n hn) =
      bottomRightCornerCrossDart n hn := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .bottom
      (bottomRightCornerLast n hn), .east)
  have hm : FKIsingMedialDart.localMate
      (fkIsingSquareClosePerimeter n omega)
      (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east) =
      (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .north) := by
    simpa [fkIsingSquareBoundaryLayerComplementInwardSide,
      fkIsingSquareBoundaryLayerComplementEndpointSide] using
      fkIsingSquareBoundaryLayer_complement_localMate n omega .bottom
        (bottomRightCornerLast n hn)
  rw [hm] at hinv
  simpa [bottomRightCornerOtherDart, bottomRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using hinv

private theorem bottomRightCornerCrossDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (bottomRightCornerCrossDart n hn) =
      bottomRightCornerOtherDart n hn := by
  simpa [bottomRightCornerOtherDart, bottomRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using
    fkIsingSquareBoundaryLayer_complement_localMate n omega .bottom
      (bottomRightCornerLast n hn)

private theorem bottomRightCornerCrossMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .south) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west)
  have hm : FKIsingMedialDart.localMate
      (fkIsingSquareClosePerimeter n omega)
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := by
    simpa [fkIsingSquareBoundaryLayerInwardSide,
      fkIsingSquareBoundaryLayerEndpointSide] using
      fkIsingSquareBoundaryLayer_localMate n omega .right
        (bottomRightCornerZero n hn)
  rw [hm] at hinv
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using hinv

private theorem bottomRightCornerOtherMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west) =
      (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south) := by
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using
    fkIsingSquareBoundaryLayer_localMate n omega .right
      (bottomRightCornerZero n hn)

private theorem bottomRightCornerCrossMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .south) =
      bottomRightCornerCrossDart n hn := by
  rw [← bottomRightCornerCrossDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

private theorem bottomRightCornerOtherMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west) =
      bottomRightCornerOtherDart n hn := by
  rw [← bottomRightCornerOtherDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

private def bottomRightCornerCycleCarrier
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Prop :=
  z = .dart (bottomRightCornerOtherDart n hn) ∨
  z = .dart (bottomRightCornerCrossDart n hn) ∨
  z = .bond (bottomRightCornerCrossDart n hn) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .south) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .south) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .west) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .west) ∨
  z = .bond (bottomRightCornerOtherDart n hn)

private theorem bottomRightCornerCycleCarrier_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : bottomRightCornerCycleCarrier n hn x)
    (hxy : (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Adj x y) :
    bottomRightCornerCycleCarrier n hn y := by
  have hother := cornerDart_ne_source_terminal_of_not_boundary n hn
    (bottomRightCornerOtherDart n hn)
    (bottomRightCornerOtherDart_not_boundary n hn)
  have hcross := cornerDart_ne_source_terminal_of_not_boundary n hn
    (bottomRightCornerCrossDart n hn)
    (bottomRightCornerCrossDart_not_boundary n hn)
  have hcrossMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .south)
    (bottomRightCornerCrossMate_not_boundary n hn)
  have hotherMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west)
    (bottomRightCornerOtherMate_not_boundary n hn)
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hxy with ⟨-, -, rfl⟩ | rfl <;>
    simp [bottomRightCornerCycleCarrier,
      fkIsingSquareWiredIncidenceMate, fkIsingSquareWiredTransitionMate,
      bottomRightCornerOtherDart_localMate,
      bottomRightCornerCrossDart_localMate,
      bottomRightCornerCrossMate_localMate,
      bottomRightCornerOtherMate_localMate,
      bottomRightCornerCrossDart_bondMate,
      bottomRightCornerCrossMate_bondMate,
      bottomRightCornerOtherDart_bondMate,
      bottomRightCornerOtherMate_bondMate,
      hother.1, hother.2, hcross.1, hcross.2,
      hcrossMate.1, hcrossMate.2, hotherMate.1, hotherMate.2]

private theorem bottomRightCornerCycleCarrier_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {z : FKIsingSquareWiredCarrier n}
    (hz : bottomRightCornerCycleCarrier n hn z) :
    ¬ (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Reachable .source z := by
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  have htransport : ∀ {a b : FKIsingSquareWiredCarrier n},
      (fkIsingSquareWiredLoopGraph n hn
        (fkIsingSquareClosePerimeter n omega)).Walk a b →
      bottomRightCornerCycleCarrier n hn a →
      bottomRightCornerCycleCarrier n hn b := by
    intro a b q
    induction q with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        exact ih (bottomRightCornerCycleCarrier_of_adj n hn omega ha hadj)
  have hsource := htransport p hz
  simpa [bottomRightCornerCycleCarrier] using hsource

private theorem bottomRightCornerOtherMate_not_mem_exploration
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace
      (Sym2 (fkIsingSquareBoundaryDeletedPlanar n).V)) :
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west) : FKIsingSquareWiredCarrier n) ∉
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
  change (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .west) : FKIsingSquareWiredCarrier n) ∉
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  apply bottomRightCornerCycleCarrier_not_reachable n hn omega
  simp [bottomRightCornerCycleCarrier]



theorem bottomRightCorner_inward_observable_eq_zero
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) = 0 := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_eq_zero
  intro omega _
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg (bottomRightCornerOtherMate_not_mem_exploration n hn omega)]



theorem bottomRightCorner_inward_increment_eq_zero
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) = 0 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [bottomRightCorner_inward_observable_eq_zero n hn]
  exact Complex.normSq_zero

private theorem bottomRightCornerCrossDart_bondTurn
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondTurn n hn (bottomRightCornerCrossDart n hn)
      (fkIsingSquareWiredBondMate n hn (bottomRightCornerCrossDart n hn)) = 4 := by
  let d := bottomRightCornerCrossDart n hn
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right (bottomRightCornerZero n hn),
        .south) := by
    simpa [d] using bottomRightCornerCrossDart_bondMate n hn
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact bottomRightCornerCrossDart_ne_source n hn hd
    · exact bottomRightCornerCrossDart_not_boundary n hn
        ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [bottomRightCornerZero, fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
        fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h0
      omega
    · exact bottomRightCornerCrossMate_not_boundary n hn
        ⟨.west j, hd.symm⟩
  rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
  simp [fkIsingSquareOrientedPrincipalBondTurn,
    fkIsingSquareSignedEighthTurn, fkIsingSquareWiredCarrierTangentCode,
    fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
    d, bottomRightCornerCrossDart, bottomRightCornerLast,
    bottomRightCornerZero, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation]

theorem bottomRightCornerCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondPhase n hn (bottomRightCornerCrossDart n hn) =
      Complex.I := by
  unfold fkIsingSquareWiredBondPhase
  rw [bottomRightCornerCrossDart_bondTurn]
  convert exp_pi_div_two_mul_I using 1 <;> push_cast <;> ring



theorem bottomRightCorner_inward_increment_eq
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom
          (bottomRightCornerLast n hn), .north)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerZero n hn), .west)) := by
  let d := bottomRightCornerCrossDart n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate n hn d
    (bottomRightCornerCrossDart_ne_source n hn)
    (bottomRightCornerCrossDart_ne_terminal n hn)
  rw [bottomRightCornerCrossDart_bondMate n hn] at hbond
  have hbottom :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .bottom (bottomRightCornerLast n hn)
  have hright := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right (bottomRightCornerZero n hn)
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .north)) at hbottom
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south)) at hright
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .south)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .east)) at hbond
  exact hbottom.symm.trans (hbond.symm.trans hright.symm)



theorem bottomRightCorner_vertex_difference_west
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x0 := fkIsingSquareBoundaryVertex n (.bottom, last)
    let x1 := fkIsingSquareBoundaryVertex n (.right, zero)
    let e := fkIsingSquarePerimeterEdge n .bottom last
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x0 := fkIsingSquareBoundaryVertex n (.bottom, last)
  let x1 := fkIsingSquareBoundaryVertex n (.right, zero)
  let ep := fkIsingSquarePerimeterEdge n .bottom last
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, last, bottomRightCornerLast,
        fkIsingSquareInteriorRadialEndpoint, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, last, bottomRightCornerLast,
      fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .north)) at h1
  linarith



theorem bottomRightCorner_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    let eN := fkIsingSquarePerimeterEdge n .right zero
    let eW := fkIsingSquarePerimeterEdge n .bottom last
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .west)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .north))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .north)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .west))) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.right, zero)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eN := fkIsingSquarePerimeterEdge n .right zero
  let eW := fkIsingSquarePerimeterEdge n .bottom last
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x = {xN, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · have hi := congrFun h 0
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        omega
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xN, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 + 1
          omega
    · rintro (rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .north hnorth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hNW : xN ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xN - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hNW]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdW := bottomRightCorner_vertex_difference_west n hn
  change H xN - H x = _ at hdN
  have hx0 : fkIsingSquareBoundaryVertex n (.bottom, last) = xW := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xW, x, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite] <;> omega
  change H (fkIsingSquareBoundaryVertex n (.bottom, last)) - H x = _ at hdW
  rw [hx0] at hdW
  have heN : fullVertexNorthEdge n x hnorth = eN := by rfl
  rw [heN] at hdN
  rw [show fkIsingSquarePerimeterEdge n .bottom last = eW by rfl] at hdW
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdN, hdW]



theorem bottomRightCorner_vertex_laplacian_eq_corner_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (b - d) + (b - a) := by
  dsimp only
  rw [bottomRightCorner_vertex_laplacian_eq_increment_divergence n hn]
  rw [bottomRightCorner_inward_increment_eq n hn]



theorem vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound
    (n : Nat) (hn : 0 < n)
    (hcorner :
      let last := bottomRightCornerLast n hn
      let zero := bottomRightCornerZero n hn
      let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
      let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
      let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
      2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.right, zero)
  let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
  let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
  let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
  have hlap := bottomRightCorner_vertex_laplacian_eq_corner_divergence n hn
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
        (b - d) + (b - a) at hlap
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .right zero (by decide)
  change b = 1 -
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x at hgap
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 2 := by
    simp [fkIsingSquareFullVertexGhostMultiplicity, x, zero,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, ← hgap, isingFermionicGhostRate, hmult]
  dsimp only [Nat.cast_ofNat]
  change (b - d) + (b - a) +
    (isingFermionicGhostCoefficient * 2) * b ≤ 0
  have hc : 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := hcorner
  nlinarith



theorem bottomRightCorner_increment_bound
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .bottom last, .west))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .west))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right zero, .north))
    2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
  dsimp only
  rw [bottomRightCorner_inward_increment_eq_zero n hn]
  have ha := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .bottom
        (bottomRightCornerLast n hn), .west)))
  have hd := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerZero n hn), .north)))
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .bottom
      (bottomRightCornerLast n hn), .west)) at ha
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerZero n hn), .north)) at hd
  nlinarith



theorem vertex_modifiedLaplacian_nonpos_of_bottomRightCorner
    (n : Nat) (hn : 0 < n) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.right, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  apply vertex_modifiedLaplacian_nonpos_of_bottomRightCorner_of_increment_bound
  exact bottomRightCorner_increment_bound n hn



theorem bottomRightCorner_rightComplement_phase
    (n : Nat) (hn : 0 < n) :
    let k0 := bottomRightCornerZero n hn
    isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) =
      -isingLambda * isingProj 1
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) := by
  let k0 := bottomRightCornerZero n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right k0
  let F := D.fermionicObservable (.dart (e, .east))
  have hline : (starRingEnd Complex) F = Complex.I * F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .east))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .east)) =
        Complex.I := by
      simpa only [e] using
        fkIsingSquareBoundaryLayerComplementInward_directedTangent
          n hn .right k0
    rw [ht] at h
    exact conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq Complex.I F
      (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
        isingPrimitiveIncrement] using h)
  have hvertex :
      fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0 =
        (isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .north))) = _
    have hep :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .right k0
    change D.fermionicObservable (.dart (e, .north)) = F * isingLambda⁻¹ at hep
    rw [hep]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj (-Complex.I)
      (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .right k0) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = -F.re := by linarith [hre]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]



theorem bottomRightCorner_bottomStandard_phase
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    isingProj (-1)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) =
      -isingLambda * isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) := by
  let last := bottomRightCornerLast n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .bottom last
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 := by
      simpa only [e] using fkIsingSquareBoundaryLayerInward_directedTangent
        n hn .bottom last
    rw [ht, one_mul] at h
    simpa only [one_mul] using
      (conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq 1 F
        (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
          isingPrimitiveIncrement, one_mul] using h))
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .bottom last
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    change _ * (F + F * isingLambda⁻¹) = _
    ring
  change isingProj (-1)
      (fkIsingSquareBoundaryLayerVertexFermion n hn .bottom last) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = 0 := by linarith [him]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]



theorem topRightCorner_rightStandard_phase
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    isingProj Complex.I
        (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) =
      -isingLambda * isingProj (-1)
        (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) := by
  let last := bottomRightCornerLast n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .right last
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = -Complex.I * F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) =
        -Complex.I := by
      simpa only [e] using fkIsingSquareBoundaryLayerInward_directedTangent
        n hn .right last
    rw [ht] at h
    exact conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq (-Complex.I) F
      (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
        isingPrimitiveIncrement] using h)
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn .right last =
      (isingFermionicBoundaryVertexNormalization : Complex) *
        (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
      n hn .right last
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    ring
  change isingProj Complex.I
      (fkIsingSquareBoundaryLayerVertexFermion n hn .right last) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = F.re := by linarith [hre]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]



theorem topRightCorner_topComplement_phase
    (n : Nat) (hn : 0 < n) :
    let k0 := bottomRightCornerZero n hn
    isingProj (-1)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) =
      -isingLambda * isingProj (-Complex.I)
        (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) := by
  let k0 := bottomRightCornerZero n hn
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquarePerimeterEdge n .top k0
  let F := D.fermionicObservable (.dart (e, .west))
  have hline : (starRingEnd Complex) F = F := by
    have h := fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
      n hn (.dart (e, .west))
    have ht : fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west)) = 1 := by
      simpa only [e] using
        fkIsingSquareBoundaryLayerComplementInward_directedTangent
          n hn .top k0
    rw [ht, one_mul] at h
    simpa only [one_mul] using
      (conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq 1 F
        (by simpa only [D, F, fkIsingSquareBoundaryPrimitiveIncrement,
          isingPrimitiveIncrement, one_mul] using h))
  have hvertex :
      fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0 =
        (isingFermionicBoundaryVertexNormalization : Complex) *
          (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerComplementVertexFermion
    change (isingFermionicBoundaryVertexNormalization : Complex) *
      (F + D.fermionicObservable (.dart (e, .south))) = _
    have hep :=
      fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
        n hn .top k0
    change D.fermionicObservable (.dart (e, .south)) = F * isingLambda⁻¹ at hep
    rw [hep]
    ring
  change isingProj (-1)
      (fkIsingSquareBoundaryLayerComplementVertexFermion n hn .top k0) = _
  rw [hvertex, isingLambda_inv_val, isingLambda_val]
  have hre := congrArg Complex.re hline
  have him := congrArg Complex.im hline
  simp at hre him
  have hy : F.im = 0 := by linarith [him]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
  apply Complex.ext <;>
    simp [isingProj, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im] <;>
    rw [hy] <;> ring_nf <;> nlinarith [hsqrt]

private def topRightCornerCrossDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquarePerimeterEdge n .right (bottomRightCornerLast n hn), .north)

private theorem topRightCornerCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (topRightCornerCrossDart n hn) at hend
  rw [hend] at hwire
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem topRightCornerCrossDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (topRightCornerCrossDart n hn) =
      (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .east) := by
  let x := fkIsingSquareBoundaryVertex n
    (.top, bottomRightCornerZero n hn)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := topRightCornerCrossDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (topRightCornerCrossDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topRightCornerCrossDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, topRightCornerCrossDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .clockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topRightCornerCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquarePreviousDirection n x .south = .west := by
    simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .counterclockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) := rfl

private def topRightCornerOtherDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquarePerimeterEdge n .right (bottomRightCornerLast n hn), .east)

private theorem topRightCornerOtherDart_not_boundary
    (n : Nat) (hn : 0 < n) :
    topRightCornerOtherDart n hn ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n (topRightCornerOtherDart n hn) at hend
  rw [hend] at hwire
  simp [topRightCornerOtherDart, bottomRightCornerLast,
    fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

private theorem topRightCornerOtherDart_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn (topRightCornerOtherDart n hn) =
      (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .north) := by
  let x := fkIsingSquareBoundaryVertex n
    (.top, bottomRightCornerZero n hn)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let d := topRightCornerOtherDart n hn
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d
    (topRightCornerOtherDart_not_boundary n hn)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topRightCornerOtherDart, bottomRightCornerLast,
        bottomRightCornerZero, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite] <;> omega
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, topRightCornerOtherDart, bottomRightCornerLast,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topRightCornerOtherDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .south = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, x,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) := rfl

private theorem topRightCornerCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .east) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

private theorem topRightCornerOtherMate_not_boundary
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquarePerimeterEdge n .top (bottomRightCornerZero n hn),
        .north) ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) at hend
  rw [hend] at hwire
  simp [bottomRightCornerZero, fkIsingSquareWiredArc,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDartEndpoint, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hwire
  omega

private theorem topRightCornerOtherDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (topRightCornerOtherDart n hn) =
      topRightCornerCrossDart n hn := by
  simpa [topRightCornerOtherDart, topRightCornerCrossDart,
    fkIsingSquareBoundaryLayerComplementInwardSide,
    fkIsingSquareBoundaryLayerComplementEndpointSide] using
    fkIsingSquareBoundaryLayer_complement_localMate n omega .right
      (bottomRightCornerLast n hn)

private theorem topRightCornerCrossDart_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (topRightCornerCrossDart n hn) =
      topRightCornerOtherDart n hn := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (topRightCornerOtherDart n hn)
  rw [topRightCornerOtherDart_localMate n hn omega] at hinv
  exact hinv

private theorem topRightCornerCrossMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east) =
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .north) := by
  simpa [fkIsingSquareBoundaryLayerInwardSide,
    fkIsingSquareBoundaryLayerEndpointSide] using
    fkIsingSquareBoundaryLayer_localMate n omega .top
      (bottomRightCornerZero n hn)

private theorem topRightCornerOtherMate_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .north) =
      (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east) := by
  have hinv := FKIsingMedialDart.localMate_involutive
    (fkIsingSquareClosePerimeter n omega)
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east)
  have hm := topRightCornerCrossMate_localMate n hn omega
  rw [hm] at hinv
  exact hinv

private theorem topRightCornerCrossMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east) =
      topRightCornerCrossDart n hn := by
  rw [← topRightCornerCrossDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

private theorem topRightCornerOtherMate_bondMate
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .north) =
      topRightCornerOtherDart n hn := by
  rw [← topRightCornerOtherDart_bondMate n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

private def topRightCornerCycleCarrier
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Prop :=
  z = .dart (topRightCornerOtherDart n hn) ∨
  z = .dart (topRightCornerCrossDart n hn) ∨
  z = .bond (topRightCornerCrossDart n hn) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .east) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .east) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .north) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .north) ∨
  z = .bond (topRightCornerOtherDart n hn)

private theorem topRightCornerCycleCarrier_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : topRightCornerCycleCarrier n hn x)
    (hxy : (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Adj x y) :
    topRightCornerCycleCarrier n hn y := by
  have hother := cornerDart_ne_source_terminal_of_not_boundary n hn
    (topRightCornerOtherDart n hn)
    (topRightCornerOtherDart_not_boundary n hn)
  have hcross := cornerDart_ne_source_terminal_of_not_boundary n hn
    (topRightCornerCrossDart n hn)
    (topRightCornerCrossDart_not_boundary n hn)
  have hcrossMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east)
    (topRightCornerCrossMate_not_boundary n hn)
  have hotherMate := cornerDart_ne_source_terminal_of_not_boundary n hn
    (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .north)
    (topRightCornerOtherMate_not_boundary n hn)
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hxy with ⟨-, -, rfl⟩ | rfl <;>
    simp [topRightCornerCycleCarrier,
      fkIsingSquareWiredIncidenceMate, fkIsingSquareWiredTransitionMate,
      topRightCornerOtherDart_localMate,
      topRightCornerCrossDart_localMate,
      topRightCornerCrossMate_localMate,
      topRightCornerOtherMate_localMate,
      topRightCornerCrossDart_bondMate,
      topRightCornerCrossMate_bondMate,
      topRightCornerOtherDart_bondMate,
      topRightCornerOtherMate_bondMate,
      hother.1, hother.2, hcross.1, hcross.2,
      hcrossMate.1, hcrossMate.2, hotherMate.1, hotherMate.2]

private theorem topRightCornerCycleCarrier_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {z : FKIsingSquareWiredCarrier n}
    (hz : topRightCornerCycleCarrier n hn z) :
    ¬ (fkIsingSquareWiredLoopGraph n hn
      (fkIsingSquareClosePerimeter n omega)).Reachable .source z := by
  intro hreach
  obtain ⟨p⟩ := hreach.symm
  have htransport : ∀ {a b : FKIsingSquareWiredCarrier n},
      (fkIsingSquareWiredLoopGraph n hn
        (fkIsingSquareClosePerimeter n omega)).Walk a b →
      topRightCornerCycleCarrier n hn a →
      topRightCornerCycleCarrier n hn b := by
    intro a b q
    induction q with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        exact ih (topRightCornerCycleCarrier_of_adj n hn omega ha hadj)
  have hsource := htransport p hz
  simpa [topRightCornerCycleCarrier] using hsource

private theorem topRightCornerCrossMate_not_mem_exploration
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace
      (Sym2 (fkIsingSquareBoundaryDeletedPlanar n).V)) :
    (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east) : FKIsingSquareWiredCarrier n) ∉
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration omega := by
  change (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .east) : FKIsingSquareWiredCarrier n) ∉
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  apply topRightCornerCycleCarrier_not_reachable n hn omega
  simp [topRightCornerCycleCarrier]



theorem topRightCorner_inward_observable_eq_zero
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) = 0 := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_eq_zero
  intro omega _
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg (topRightCornerCrossMate_not_mem_exploration n hn omega)]



theorem topRightCorner_inward_increment_eq_zero
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) = 0 := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [topRightCorner_inward_observable_eq_zero n hn]
  exact Complex.normSq_zero

private theorem topRightCornerCrossDart_ne_source
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
    fkIsingSquareCornerSide, fkIsingSquareDartEndpoint,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedA, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite] at he
  omega

private theorem topRightCornerCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) :
    topRightCornerCrossDart n hn ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  simp [topRightCornerCrossDart, bottomRightCornerLast,
    fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
    fkIsingSquareCornerSide, fkIsingSquareDartEndpoint,
    fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedB, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite] at he
  omega



theorem topRightCorner_inward_increment_eq
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right
          (bottomRightCornerLast n hn), .east)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top
          (bottomRightCornerZero n hn), .east)) := by
  let d := topRightCornerCrossDart n hn
  have hbond := fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate n hn d
    (topRightCornerCrossDart_ne_source n hn)
    (topRightCornerCrossDart_ne_terminal n hn)
  rw [topRightCornerCrossDart_bondMate n hn] at hbond
  have hright :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right (bottomRightCornerLast n hn)
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .north)) at hright
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .north)) at hbond
  exact hright.trans hbond.symm



theorem topRightCorner_vertex_difference_south
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x0 := fkIsingSquareBoundaryVertex n (.right, last)
    let x1 := fkIsingSquareBoundaryVertex n (.top, zero)
    let e := fkIsingSquarePerimeterEdge n .right last
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x0 := fkIsingSquareBoundaryVertex n (.right, last)
  let x1 := fkIsingSquareBoundaryVertex n (.top, zero)
  let ep := fkIsingSquarePerimeterEdge n .right last
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
    simp [ep, last, bottomRightCornerLast, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, last, bottomRightCornerLast,
        fkIsingSquareInteriorRadialEndpoint, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;> omega
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r0, r1, d0, d1, ep, last, bottomRightCornerLast,
      fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .north)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right last
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right last
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hcomp
  linarith



theorem topRightCorner_vertex_laplacian_eq_increment_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    let eS := fkIsingSquarePerimeterEdge n .right last
    let eW := fkIsingSquarePerimeterEdge n .top zero
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eS, .south))) +
        (fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) -
          fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .south))) := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.top, zero)
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, zero, bottomRightCornerZero, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let eS := fkIsingSquarePerimeterEdge n .right last
  let eW := fkIsingSquarePerimeterEdge n .top zero
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x = {xS, xW} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hxy
      change (hypercubicLattice 2).Adj x.1 y.1 at hxy
      rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
      · right
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          change y.1 0 = x.1 0 - 1
          omega
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          simpa [xW, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
      · have hi := congrFun h 0
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        omega
      · left
        apply Subtype.ext
        funext i
        fin_cases i
        · have hi := congrFun h 0
          simp [Pi.add_apply] at hi
          simpa [xS, fkIsingSquareNeighbor,
            fkIsingSquareNeighborSite] using hi.symm
        · have hi := congrFun h 1
          simp [Pi.add_apply] at hi
          change y.1 1 = x.1 1 - 1
          omega
      · have hi := congrFun h 1
        simp [Pi.add_apply, x, zero, bottomRightCornerZero,
          fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hi
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        omega
    · rintro (rfl | rfl)
      · exact fkIsingSquare_adj_neighbor n x .south hsouth
      · exact fkIsingSquare_adj_neighbor n x .west hwest
  have hSW : xS ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) h
    simp [xS, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xS - H x) + (H xW - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hSW]
    ring
  have hdS := topRightCorner_vertex_difference_south n hn
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xW - H x = _ at hdW
  have hx0 : fkIsingSquareBoundaryVertex n (.right, last) = xS := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [xS, x, last, zero, bottomRightCornerLast,
        bottomRightCornerZero, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite] <;> omega
  change H (fkIsingSquareBoundaryVertex n (.right, last)) - H x = _ at hdS
  rw [hx0] at hdS
  have heW : fullVertexWestEdge n x hwest = eW := by rfl
  rw [heW] at hdW
  rw [show fkIsingSquarePerimeterEdge n .right last = eS by rfl] at hdS
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x = _
  rw [hLap, hdS, hdW]

theorem topRightCorner_vertex_laplacian_eq_corner_divergence
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      (b - a) + (b - d) := by
  dsimp only
  rw [topRightCorner_vertex_laplacian_eq_increment_divergence n hn]
  rw [topRightCorner_inward_increment_eq n hn]

theorem vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound
    (n : Nat) (hn : 0 < n)
    (hcorner :
      let last := bottomRightCornerLast n hn
      let zero := bottomRightCornerZero n hn
      let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
      let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
      let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
      2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let last := bottomRightCornerLast n hn
  let zero := bottomRightCornerZero n hn
  let x := fkIsingSquareBoundaryVertex n (.top, zero)
  let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
  let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
  let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
  have hlap := topRightCorner_vertex_laplacian_eq_corner_divergence n hn
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
        (b - a) + (b - d) at hlap
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .top zero (by decide)
  change b = 1 -
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x at hgap
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 2 := by
    simp [fkIsingSquareFullVertexGhostMultiplicity, x, zero,
      bottomRightCornerZero, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]
    omega
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, ← hgap, isingFermionicGhostRate, hmult]
  dsimp only [Nat.cast_ofNat]
  change (b - a) + (b - d) +
    (isingFermionicGhostCoefficient * 2) * b ≤ 0
  have hc : 2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := hcorner
  nlinarith



theorem topRightCorner_increment_bound
    (n : Nat) (hn : 0 < n) :
    let last := bottomRightCornerLast n hn
    let zero := bottomRightCornerZero n hn
    let a := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .right last, .south))
    let b := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .east))
    let d := fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n .top zero, .south))
    2 * (1 + isingFermionicGhostCoefficient) * b ≤ a + d := by
  dsimp only
  rw [topRightCorner_inward_increment_eq_zero n hn]
  have ha := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .right
        (bottomRightCornerLast n hn), .south)))
  have hd := isingPrimitiveIncrement_nonneg
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n .top
        (bottomRightCornerZero n hn), .south)))
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .right
      (bottomRightCornerLast n hn), .south)) at ha
  change 0 ≤ fkIsingSquareBoundaryPrimitiveIncrement n hn
    (.dart (fkIsingSquarePerimeterEdge n .top
      (bottomRightCornerZero n hn), .south)) at hd
  nlinarith



theorem vertex_modifiedLaplacian_nonpos_of_topRightCorner
    (n : Nat) (hn : 0 < n) :
    let zero := bottomRightCornerZero n hn
    let x := fkIsingSquareBoundaryVertex n (.top, zero)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  apply vertex_modifiedLaplacian_nonpos_of_topRightCorner_of_increment_bound
  exact topRightCorner_increment_bound n hn

theorem bottomRightCorner_ghostMultiplicity
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullVertexGhostMultiplicity n
        (fkIsingSquareBoundaryVertex n
          (.right, bottomRightCornerZero n hn)) = 2 := by
  simp [fkIsingSquareFullVertexGhostMultiplicity, bottomRightCornerZero,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  omega

theorem topRightCorner_ghostMultiplicity
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullVertexGhostMultiplicity n
        (fkIsingSquareBoundaryVertex n
          (.top, bottomRightCornerZero n hn)) = 2 := by
  simp [fkIsingSquareFullVertexGhostMultiplicity, bottomRightCornerZero,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  omega



theorem cornerIncrementDivergence_add_ghost_nonpos
    (far₁ near far₂ : Real)
    (hcorner : 2 * (1 + isingFermionicGhostCoefficient) * near ≤
      far₁ + far₂) :
    (near - far₁) + (near - far₂) +
        2 * isingFermionicGhostCoefficient * near ≤ 0 := by
  linarith



theorem vertex_modifiedLaplacian_nonpos_of_bottomBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eN := fullVertexNorthEdge n x hnorth
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBottomBoundaryMedialObservable n hn k1
  let south := fkIsingSquareBottomBoundaryMissingSouthObservable n hn k
  let west := fkIsingSquareBottomBoundaryMedialObservable n hn k0
  have hquad : IsingSquareSHolomorphicQuad south west north east := by
    simpa [south, west, north, east, eN, x, k0, k1] using
      fkIsingSquareBottomBoundaryObservable_quad n hn k
  obtain ⟨hNE, hWN⟩ :=
    isingSquareSHolomorphicQuad_bottom_projection_cycle
      south west north east hquad
  have hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north := by
    calc
      isingProj (-Complex.I) north = isingProj (-Complex.I) west := hWN.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) := by
        simpa [west] using
          fkIsingSquareBottomBoundaryMedialObservable_projection_north
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
        simpa [k0, k1] using bottom_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj 1 east := by
        rw [fkIsingSquareBottomBoundaryMedialObservable_projection_west]
      _ = -isingLambda * isingProj 1 north := by rw [← hNE]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos
      north east west hNE hWN hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .bottom k1 (by decide)
  have hproj : Complex.normSq (isingProj 1 north) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hNE]
    rw [fkIsingSquareBottomBoundaryMedialObservable_projection_west]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, east] using hgap
  have hlap :=
    bottom_boundary_vertex_laplacian_eq_projectionDivergenceWithoutSouth n hn k
  have hs : x.1 1 = -(n : Int) := by
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
  have he : x.1 0 ≠ (n : Int) := by
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    omega
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    simp [fkIsingSquareFullVertexGhostMultiplicity, hs, he,
      Nat.ne_of_gt hn]
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv



theorem vertex_modifiedLaplacian_nonpos_of_rightBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.right, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eW := fullVertexWestEdge n x hwest
  let north := fkIsingSquareRightBoundaryMedialObservable n hn k1
  let south := fkIsingSquareRightBoundaryMedialObservable n hn k0
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  obtain ⟨hSW, hWN⟩ := right_boundary_projection_cycle n hn k
  have hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west := by
    calc
      isingProj (-1) west = isingProj (-1) south := hSW.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) := by
        simpa [south] using
          fkIsingSquareRightBoundaryMedialObservable_projection_north
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
        simpa [k0, k1] using right_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj (-Complex.I) north := by
        rw [fkIsingSquareRightBoundaryMedialObservable_projection_west]
      _ = -isingLambda * isingProj (-Complex.I) west := by rw [hWN]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos
      north south west hSW hWN hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .right k1 (by decide)
  have hproj : Complex.normSq (isingProj (-Complex.I) west) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hWN]
    rw [fkIsingSquareRightBoundaryMedialObservable_projection_west]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, north] using hgap
  have hlap :=
    right_boundary_vertex_laplacian_eq_projectionDivergenceWithoutEast n hn k
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    split_ifs <;> omega
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv



theorem vertex_modifiedLaplacian_nonpos_of_topBoundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x := fkIsingSquareBoundaryVertex n (.top, k1)
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  change isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    exact hn
  let eS := fullVertexSouthEdge n x hsouth
  let east := fkIsingSquareTopBoundaryMedialObservable n hn k0
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareTopBoundaryMedialObservable n hn k1
  obtain ⟨hES, hSW⟩ := top_boundary_projection_cycle n hn k
  have hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south := by
    calc
      isingProj Complex.I south = isingProj Complex.I east := hES.symm
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) := by
        simpa [east] using
          fkIsingSquareTopBoundaryMedialObservable_projection_south
            n hn k0
      _ = -isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
        simpa [k0, k1] using top_boundary_inward_observable_phase n hn k
      _ = -isingLambda * isingProj (-1) west := by
        rw [fkIsingSquareTopBoundaryMedialObservable_projection_east]
      _ = -isingLambda * isingProj (-1) south := by rw [hSW]
  have hdiv :=
    isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos
      east south west hES hSW hphase
  have hgap := boundaryLayer_inwardIncrement_eq_one_sub_vertex
    n hn .top k1 (by decide)
  have hproj : Complex.normSq (isingProj (-1) south) =
      1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x := by
    rw [hSW]
    rw [fkIsingSquareTopBoundaryMedialObservable_projection_east]
    simpa [fkIsingSquareBoundaryLayerInwardIncrement, x, west] using hgap
  have hlap :=
    top_boundary_vertex_laplacian_eq_projectionDivergenceWithoutNorth n hn k
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 1 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    have hk := k.isLt
    omega
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x =
        isingFermionicGhostCoefficient := by
    simp [isingFermionicGhostRate, hmult]
  change isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
    ≤ 0
  rw [hlap, hrate, ← hproj]
  exact hdiv




theorem vertex_modifiedLaplacian_nonpos_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      <= 0 := by
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
    split_ifs <;> omega
  rw [show fkIsingSquareFullVertexGraph n = (fkSquareBoxPlanar n).G from rfl]
  simp [isingFermionicGhostRate, hmult]
  exact vertex_laplacian_nonpos_of_interior n hn x
    heast hnorth hwest hsouth




theorem vertex_modifiedLaplacian_nonpos_of_not_wiredArc
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hxFree : ¬ fkIsingSquareWiredArc n x) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x)
      ≤ 0 := by
  have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  have hxLeft : x.1 0 ≠ -(n : Int) := by
    simpa [fkIsingSquareWiredArc] using hxFree
  by_cases hbottom : x.1 1 = -(n : Int)
  · by_cases hright : x.1 0 = (n : Int)
    · have hx : x = fkIsingSquareBoundaryVertex n
          (.right, bottomRightCornerZero n hn) := by
        apply Subtype.ext
        funext i
        fin_cases i <;>
          simp [bottomRightCornerZero, fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite, hbottom, hright]
      rw [hx]
      exact vertex_modifiedLaplacian_nonpos_of_bottomRightCorner n hn
    · let j : Nat := Int.toNat (x.1 0 + (n : Int))
      have hj0 : 0 ≤ x.1 0 + (n : Int) := by omega
      have hj : (j : Int) = x.1 0 + (n : Int) := by
        simpa [j] using Int.toNat_of_nonneg hj0
      have hjLower : 1 ≤ j := by omega
      have hjUpper : j < 2 * n := by omega
      let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
      let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
      have hx : x = fkIsingSquareBoundaryVertex n (.bottom, k1) := by
        apply Subtype.ext
        funext i
        fin_cases i <;>
          simp [k1, k, fkIsingSquareBoundaryVertex,
            fkIsingSquareBoundarySite, hbottom] <;> omega
      rw [hx]
      exact vertex_modifiedLaplacian_nonpos_of_bottomBoundary n hn k
  · by_cases hright : x.1 0 = (n : Int)
    · by_cases htop : x.1 1 = (n : Int)
      · have hx : x = fkIsingSquareBoundaryVertex n
            (.top, bottomRightCornerZero n hn) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [bottomRightCornerZero, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, hright, htop]
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_topRightCorner n hn
      · let j : Nat := Int.toNat (x.1 1 + (n : Int))
        have hj0 : 0 ≤ x.1 1 + (n : Int) := by omega
        have hj : (j : Int) = x.1 1 + (n : Int) := by
          simpa [j] using Int.toNat_of_nonneg hj0
        have hjLower : 1 ≤ j := by omega
        have hjUpper : j < 2 * n := by omega
        let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
        let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
        have hx : x = fkIsingSquareBoundaryVertex n (.right, k1) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [k1, k, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, hright] <;> omega
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_rightBoundary n hn k
    · by_cases htop : x.1 1 = (n : Int)
      · let j : Nat := Int.toNat ((n : Int) - x.1 0)
        have hj0 : 0 ≤ (n : Int) - x.1 0 := by omega
        have hj : (j : Int) = (n : Int) - x.1 0 := by
          simpa [j] using Int.toNat_of_nonneg hj0
        have hjLower : 1 ≤ j := by omega
        have hjUpper : j < 2 * n := by omega
        let k : Fin (2 * n - 1) := ⟨j - 1, by omega⟩
        let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
        have hx : x = fkIsingSquareBoundaryVertex n (.top, k1) := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [k1, k, fkIsingSquareBoundaryVertex,
              fkIsingSquareBoundarySite, htop] <;> omega
        rw [hx]
        exact vertex_modifiedLaplacian_nonpos_of_topBoundary n hn k
      · apply vertex_modifiedLaplacian_nonpos_of_interior n hn x
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega
        · simp [fkIsingSquareDirectionAvailable]
          omega



theorem face_modifiedLaplacian_nonneg_of_interior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 0 := by
    unfold fkIsingSquareFullFaceGhostMultiplicity
    split_ifs <;> omega
  simp [isingFermionicGhostRate, hmult]
  exact face_laplacian_nonneg_of_interior n hn c
    heast hnorth hwest hsouth



theorem face_modifiedLaplacian_nonneg_of_leftBoundary
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hleft : c.1.1 = 0)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hsouth : 0 < c.2.1) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
  let F := fkIsingSquareBoundaryFullMedialObservable n hn
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey, hleft]
    omega
  have hSEnorth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hSEwest : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
    simp [fkIsingSquareInteriorCellKey, hleft]
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNEeast : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey, hleft]
    omega
  have hNEnorth : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hNEwest : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
    simp [fkIsingSquareInteriorCellKey, hleft]
  have hNEsouth : fkIsingSquareDirectionAvailable n (faceNEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
    simp [fkIsingSquareInteriorCellKey]
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [show eN = fkIsingSquareDirectionEdge n (faceNEVertex n c) .west
        hNEwest by
      dsimp [eN]
      exact faceNorthEdge_eq_west n c]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceNEVertex n c) .west hNEwest hNEeast hNEnorth hNEwest hNEsouth
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    dsimp [eE, faceEastEdge]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceSEVertex n c) .north hSEnorth hSEeast hSEnorth hSEwest hSEsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [show eS = fkIsingSquareDirectionEdge n (faceSEVertex n c) .west
        hSEwest by
      dsimp [eS]
      exact faceSouthEdge_eq_west n c]
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
      (faceSEVertex n c) .west hSEwest hSEeast hSEnorth hSEwest hSEsouth
  have hneighbors : (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {cE, cN, cS} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hwest⟩)
      · right; left
        apply Prod.ext
        · exact hcol.symm
        · apply Fin.ext
          simp [cN, faceNorthNeighbor]
          omega
      · right; right
        apply Prod.ext
        · exact hcol.symm
        · apply Fin.ext
          simp [cS, faceSouthNeighbor]
          omega
      · left
        apply Prod.ext
        · apply Fin.ext
          simp [cE, faceEastNeighbor]
          omega
        · exact hrow.symm
      · have hy := y.1.2
        omega
    · rintro (rfl | rfl | rfl)
      · exact Or.inr ⟨rfl, Or.inl (by simp [cE, faceEastNeighbor])⟩
      · exact Or.inl ⟨rfl, Or.inl (by simp [cN, faceNorthNeighbor])⟩
      · exact Or.inl ⟨rfl, Or.inr (by simp [cS, faceSouthNeighbor]; omega)⟩
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hLap : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      (H cE - H c) + (H cN - H c) + (H cS - H c) := by
    unfold isingFiniteGraphLaplacian
    rw [hneighbors]
    simp [hEN, hES, hNS]
    ring
  have hdN := face_difference_north n hn c hnorth
  have hdE := face_difference_east n hn c heast
  have hdS := face_difference_south n hn c hsouth
  change H cN - H c = _ at hdN
  change H cE - H c = _ at hdE
  change H cS - H c = _ at hdS
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    dsimp [eN, faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    dsimp [eE, faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    dsimp [eS, faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    dsimp [eW, faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨_, hNEt, hNSt, hNNt⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEWt, _, hESt, hENt⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSWt, _, hSSt, hSNt⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWEt, hWSt, _⟩
  have hprojNE : isingProj (-1) (F eN) = isingProj (-1) (F eE) := by
    calc
      isingProj (-1) (F eN) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eN, .east)) := by
        rw [← hNEt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eN heN .east
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .north)) := faceNorthEast_observable_eq n hn c
      _ = isingProj (-1) (F eE) := by
        rw [← hENt]
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eE heE .north
  have hprojES : isingProj (-Complex.I) (F eE) =
      isingProj (-Complex.I) (F eS) := by
    calc
      isingProj (-Complex.I) (F eE) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eE, .west)) := by
        rw [← hEWt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eE heE .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .north)) := faceEastSouth_observable_eq n hn c
      _ = isingProj (-Complex.I) (F eS) := by
        rw [← hSNt]
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .north
  have heWleft : eW = fkIsingSquareLeftVerticalEdge n hn c.2 := by
    apply Subtype.ext
    change s(faceSWVertex n c,
        fkIsingSquareNeighbor n (faceSWVertex n c) .north _) =
      s(fkIsingSquareLeftVerticalUpper n hn c.2,
        fkIsingSquareNeighbor n
          (fkIsingSquareLeftVerticalUpper n hn c.2) .south _)
    rw [Sym2.eq_iff]
    apply Or.inr
    constructor <;>
      apply Subtype.ext <;>
      funext i <;>
      fin_cases i <;>
      simp [faceSWVertex, fkIsingSquareInteriorCellKey,
        fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hleft]
  have hphase : isingProj 1 (F eS) =
      isingLambda * isingProj Complex.I (F eN) := by
    calc
      isingProj 1 (F eS) =
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eS, .west)) := by
        rw [← hSWt]
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eS heS .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .south)) := faceSouthWest_observable_eq n hn c
      _ = isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eW, .east)) := by
        rw [heWleft]
        exact left_boundary_endpoint_observable_phase n hn c.2
      _ = isingLambda *
          (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (eN, .south)) := by
        rw [faceWestNorth_observable_eq n hn c]
      _ = isingLambda * isingProj Complex.I (F eN) := by
        rw [← hNSt]
        congr 1
        symm
        simpa [F] using fkIsingSquareBoundaryFullMedialObservable_projection
          n hn eN heN .south
  have hdiv : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      isingPrimalProjectionDivergenceWithoutWest (F eN) (F eE) (F eS) := by
    rw [hLap, hdE, hdN, hdS]
    rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .west]
    unfold isingPrimalProjectionDivergenceWithoutWest
    rw [hNEt, hNNt, hEWt, hESt, hSSt, hSWt]
    ring
  let r : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestEastDart n c)
  have hrface : fkIsingSquareFullFaceOfRadialIncidence n hn r = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [r, faceWestEastDart, eW, faceWestEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hrwired : fkIsingSquareFullVertexFixedBoundary n
      (fkIsingSquareInteriorRadialEndpoint n hn r) := by
    change fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n (eW, .east))
    simp [fkIsingSquareWiredArc, eW, faceWestEdge, faceSWVertex,
      fkIsingSquareInteriorCellKey, fkIsingSquareDartEndpoint,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hleft]
  have hgap := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn r
  rw [hrface, vertex_fixedBoundary_eq_zero n hn _ hrwired, sub_zero] at hgap
  have hH : H c = Complex.normSq (isingProj Complex.I (F eN)) := by
    calc
      H c = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eW, .east)) :=
        hgap
      _ = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (eN, .south)) := by
        unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
        rw [faceWestNorth_observable_eq n hn c]
      _ = Complex.normSq (isingProj Complex.I (F eN)) := by
        rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .south, hNSt]
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 1 := by
    simp [fkIsingSquareFullFaceGhostMultiplicity, hleft]
  change 0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c +
    isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n) c *
      (0 - H c)
  rw [hdiv, isingFermionicGhostRate, hmult, hH]
  simpa [sub_eq_add_neg] using
    isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg
      (F eN) (F eE) (F eS) hprojNE hprojES hphase




theorem face_modifiedLaplacian_nonneg_of_not_fixedBoundary
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (hcFree : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c) := by
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hcFree
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    have hcBound := c.1.isLt
    by_contra h
    apply hcFree
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    have hcBound := c.2.isLt
    by_contra h
    apply hcFree
    right
    right
    omega
  by_cases hleft : c.1.1 = 0
  · exact face_modifiedLaplacian_nonneg_of_leftBoundary
      n hn c hleft heast hnorth hsouth
  · exact face_modifiedLaplacian_nonneg_of_interior
      n hn c heast hnorth (by omega) hsouth



noncomputable def radialPatchPrimalValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    (fkIsingSquareRadialPatchPrimalFullVertex n m hm p)



noncomputable def radialPatchDualValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)



theorem radialPatchPrimal_exists_orderedDual
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    ∃ q : FKIsingSquareRadialPatchDualNode m,
      radialPatchPrimalValue n m hn hm p ≤
        radialPatchDualValue n m hn hm hm2 q := by
  by_cases hi : p.1.1.1 + 1 < m
  · let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 + 1, hi⟩, p.1.2), by
        change ¬ Even ((p.1.1.1 + 1) + p.1.2.1)
        rw [Nat.not_even_iff]
        have hpmod := Nat.even_iff.mp p.2
        omega⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) p.1.1.1 p.1.2.1
    refine ⟨q, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_even
          n m hn hm (by omega) p.1.1.1 p.1.2.1 hi p.1.2.2 p.2,
        fkIsingSquareRadialPatchHorizontal_face_of_even
          n m hn hm (by omega) p.1.1.1 p.1.2.1 hi p.1.2.2 p.2] at h
    simpa [radialPatchPrimalValue, radialPatchDualValue, q, e] using h
  · have hi0 : 0 < p.1.1.1 := by
      have hip := p.1.1.2
      omega
    have hprev : p.1.1.1 - 1 + 1 < m := by
      have hip := p.1.1.2
      omega
    have hodd : ¬ Even (p.1.1.1 - 1 + p.1.2.1) := by
      rw [Nat.not_even_iff]
      have hpmod := Nat.even_iff.mp p.2
      omega
    let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 - 1, by omega⟩, p.1.2), hodd⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1
    refine ⟨q, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
          n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1 hprev p.1.2.2 hodd,
        fkIsingSquareRadialPatchHorizontal_face_of_odd
          n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1 hprev p.1.2.2 hodd] at h
    have heq : p.1.1.1 - 1 + 1 = p.1.1.1 := by omega
    simpa [radialPatchPrimalValue, radialPatchDualValue, q, e, heq] using h



theorem radialPatchDual_exists_orderedPrimal
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    ∃ p : FKIsingSquareRadialPatchPrimalNode m,
      radialPatchPrimalValue n m hn hm p ≤
        radialPatchDualValue n m hn hm hm2 q := by
  by_cases hi : q.1.1.1 + 1 < m
  · have heven : Even (q.1.1.1 + 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 + 1, hi⟩, q.1.2), heven⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) q.1.1.1 q.1.2.1
    refine ⟨p, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
          n m hn hm (by omega) q.1.1.1 q.1.2.1 hi q.1.2.2 q.2,
        fkIsingSquareRadialPatchHorizontal_face_of_odd
          n m hn hm (by omega) q.1.1.1 q.1.2.1 hi q.1.2.2 q.2] at h
    simpa [radialPatchPrimalValue, radialPatchDualValue, p, e] using h
  · have hi0 : 0 < q.1.1.1 := by
      have hiq := q.1.1.2
      omega
    have hprev : q.1.1.1 - 1 + 1 < m := by
      have hiq := q.1.1.2
      omega
    have heven : Even (q.1.1.1 - 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 - 1, by omega⟩, q.1.2), heven⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1
    refine ⟨p, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_even
          n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1 hprev q.1.2.2 heven,
        fkIsingSquareRadialPatchHorizontal_face_of_even
          n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1 hprev q.1.2.2 heven] at h
    have heq : q.1.1.1 - 1 + 1 = q.1.1.1 := by omega
    simpa [radialPatchPrimalValue, radialPatchDualValue, p, e, heq] using h





theorem radialPatch_unitRange_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    (∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
      radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1) := by
  have hprimalLower : ∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p := by
    intro p
    apply fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
      n (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    · intro x hx
      exact vertex_modifiedLaplacian_nonpos_of_not_wiredArc n hn x hx
    · intro x hx
      exact vertex_fixedBoundary_nonneg n hn x hx
  have hdualUpper : ∀ q, radialPatchDualValue n m hn hm hm2 q ≤ 1 := by
    intro q
    apply fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
      n (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    · intro c hc
      exact face_modifiedLaplacian_nonneg_of_not_fixedBoundary n hn c hc
    · intro c hc
      exact face_fixedBoundary_le_one n hn c hc
  constructor
  · intro p
    obtain ⟨q, hpq⟩ := radialPatchPrimal_exists_orderedDual
      n m hn hm hm2 p
    exact ⟨hprimalLower p, hpq.trans (hdualUpper q)⟩
  · intro q
    obtain ⟨p, hpq⟩ := radialPatchDual_exists_orderedPrimal
      n m hn hm hm2 q
    exact ⟨(hprimalLower p).trans hpq, hdualUpper q⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality

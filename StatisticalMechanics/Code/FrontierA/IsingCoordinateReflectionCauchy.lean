/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCoordinateReflectionFactor

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)
variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

abbrev IsingCoordinateCrossBoundaryVertices :=
  {z : IsingCoordinateDomainLower K i m //
    z ∈ isingCoordinateDomainCrossBoundary K i m hK}

noncomputable def isingCoordinateDomainHalfReflectionForm
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) : Real :=
  ∑ lower : ConfigSpace (IsingCoordinateDomainLower K i m),
    ∑ upper : ConfigSpace (IsingCoordinateDomainLower K i m),
      (isingCoordinateDomainHalfWeight K i m hK beta boundary lower * F lower) *
        (isingCoordinateDomainHalfWeight K i m hK beta boundary upper * G upper) *
        Real.exp (beta *
          ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
            spin lower z * spin upper z)

noncomputable def isingCoordinateDomainReflectionForm
    (beta : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) : Real :=
  ∑ boundary : ConfigSpace (IsingCoordinateDomainPlane K i m),
    isingCoordinateDomainHalfReflectionForm K i m hK beta boundary F G

set_option maxHeartbeats 2000000 in


theorem isingCoordinateDomainHalfReflectionForm_nonneg
    (beta : Real) (hbeta : 0 <= beta)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (F : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    0 <= isingCoordinateDomainHalfReflectionForm K i m hK beta boundary F F := by
  have h := exp_dotProduct_kernel_quadratic_nonneg beta hbeta
    (fun sigma z => if z ∈ isingCoordinateDomainCrossBoundary K i m hK then
      spin sigma z else 0)
    (fun sigma =>
      isingCoordinateDomainHalfWeight K i m hK beta boundary sigma * F sigma)
  simpa [isingCoordinateDomainHalfReflectionForm] using h

theorem isingCoordinateDomainReflectionForm_nonneg
    (beta : Real) (hbeta : 0 <= beta)
    (F : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    0 <= isingCoordinateDomainReflectionForm K i m hK beta F F := by
  unfold isingCoordinateDomainReflectionForm
  exact Finset.sum_nonneg fun boundary _ =>
    isingCoordinateDomainHalfReflectionForm_nonneg
      K i m hK beta hbeta boundary F

theorem isingCoordinateDomainReflectionForm_add_left
    (beta : Real)
    (F G H : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta (F + G) H =
      isingCoordinateDomainReflectionForm K i m hK beta F H +
        isingCoordinateDomainReflectionForm K i m hK beta G H := by
  unfold isingCoordinateDomainReflectionForm
    isingCoordinateDomainHalfReflectionForm
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem isingCoordinateDomainReflectionForm_smul_left
    (beta t : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta (t • F) G =
      t * isingCoordinateDomainReflectionForm K i m hK beta F G := by
  unfold isingCoordinateDomainReflectionForm
    isingCoordinateDomainHalfReflectionForm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem isingCoordinateDomainReflectionForm_symm
    (beta : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta F G =
      isingCoordinateDomainReflectionForm K i m hK beta G F := by
  unfold isingCoordinateDomainReflectionForm
    isingCoordinateDomainHalfReflectionForm
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  have hdot :
      (∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          spin u z * spin l z) =
        ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          spin l z * spin u z := by
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hdot]
  ring

theorem isingCoordinateDomainReflectionForm_add_right
    (beta : Real)
    (F G H : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta F (G + H) =
      isingCoordinateDomainReflectionForm K i m hK beta F G +
        isingCoordinateDomainReflectionForm K i m hK beta F H := by
  rw [isingCoordinateDomainReflectionForm_symm,
    isingCoordinateDomainReflectionForm_add_left,
    isingCoordinateDomainReflectionForm_symm K i m hK beta G F,
    isingCoordinateDomainReflectionForm_symm K i m hK beta H F]

theorem isingCoordinateDomainReflectionForm_smul_right
    (beta t : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta F (t • G) =
      t * isingCoordinateDomainReflectionForm K i m hK beta F G := by
  rw [isingCoordinateDomainReflectionForm_symm,
    isingCoordinateDomainReflectionForm_smul_left,
    isingCoordinateDomainReflectionForm_symm K i m hK beta G F]

private theorem coordinate_quadratic_nonneg_cauchy
    (aa ab bb : Real)
    (h : ∀ t : Real, 0 <= aa + 2 * t * ab + t ^ 2 * bb) :
    ab ^ 2 <= aa * bb := by
  have hd : discrim bb (2 * ab) aa <= 0 :=
    discrim_le_zero (a := bb) (b := 2 * ab) (c := aa) (by
      intro t
      have ht := h t
      nlinarith)
  unfold discrim at hd
  nlinarith

theorem isingCoordinateDomainReflectionForm_cauchy
    (beta : Real) (hbeta : 0 <= beta)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    isingCoordinateDomainReflectionForm K i m hK beta F G ^ 2 <=
      isingCoordinateDomainReflectionForm K i m hK beta F F *
        isingCoordinateDomainReflectionForm K i m hK beta G G := by
  apply coordinate_quadratic_nonneg_cauchy
  intro t
  have h := isingCoordinateDomainReflectionForm_nonneg
    K i m hK beta hbeta (F + t • G)
  rw [isingCoordinateDomainReflectionForm_add_left,
    isingCoordinateDomainReflectionForm_add_right,
    isingCoordinateDomainReflectionForm_add_right,
    isingCoordinateDomainReflectionForm_smul_left,
    isingCoordinateDomainReflectionForm_smul_right,
    isingCoordinateDomainReflectionForm_smul_left,
    isingCoordinateDomainReflectionForm_smul_right,
    isingCoordinateDomainReflectionForm_symm K i m hK beta G F] at h
  nlinarith

private theorem crossBoundary_sum_eq_subtype_sum
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    (∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
        spin lower z * spin upper z) =
      ∑ z : IsingCoordinateCrossBoundaryVertices K i m hK,
        spin lower z.1 * spin upper z.1 := by
  exact Finset.sum_subtype
    (isingCoordinateDomainCrossBoundary K i m hK)
    (fun _ => Iff.rfl)
    (fun z => spin lower z * spin upper z)

private theorem isingCoordinateDomain_weightedSum_eq_form
    (beta : Real)
    (F G : ConfigSpace (IsingCoordinateDomainLower K i m) → Real) :
    (∑ sigma : ConfigSpace (freeDomainVertices K),
        isingWeight (freeDomainGraph K) beta 0 sigma *
          F (isingCoordinateDomainSplit K i m hK sigma).2.1 *
          G (isingCoordinateDomainSplit K i m hK sigma).2.2) =
      Real.exp (-beta *
          (isingCoordinateDomainCrossBoundary K i m hK).card) *
        isingCoordinateDomainReflectionForm K i m hK beta F G := by
  rw [← (isingCoordinateDomainSplitEquiv K i m hK).bijective.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold isingCoordinateDomainReflectionForm
    isingCoordinateDomainHalfReflectionForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have heq : isingCoordinateDomainSplitEquiv K i m hK (b, (l, u)) =
      isingCoordinateDomainGlue K i m hK b l u := rfl
  rw [heq, isingCoordinateDomainSplit_glue]
  rw [isingCoordinateDomainWeight_factor]
  ring



theorem isingCoordinateDomain_twoPoint_reflection_cauchy
    (beta : Real) (hbeta : 0 <= beta)
    (x y : IsingCoordinateDomainLower K i m) :
    isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma x.1 * spin sigma
          (isingCoordinateDomainReflectEquiv K i m hK y.1)) ^ 2 <=
      isingExpectation (freeDomainGraph K) beta 0
          (fun sigma => spin sigma x.1 * spin sigma
            (isingCoordinateDomainReflectEquiv K i m hK x.1)) *
        isingExpectation (freeDomainGraph K) beta 0
          (fun sigma => spin sigma y.1 * spin sigma
            (isingCoordinateDomainReflectEquiv K i m hK y.1)) := by
  let fx : ConfigSpace (IsingCoordinateDomainLower K i m) → Real :=
    fun sigma => spin sigma x
  let gy : ConfigSpace (IsingCoordinateDomainLower K i m) → Real :=
    fun sigma => spin sigma y
  have hform := isingCoordinateDomainReflectionForm_cauchy
    K i m hK beta hbeta fx gy
  let C := Real.exp (-beta *
    (isingCoordinateDomainCrossBoundary K i m hK).card)
  have hcross :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK y.1))) =
        C * isingCoordinateDomainReflectionForm K i m hK beta fx gy := by
    have h := isingCoordinateDomain_weightedSum_eq_form
      K i m hK beta fx gy
    calc
      _ = ∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            fx (isingCoordinateDomainSplit K i m hK sigma).2.1 *
            gy (isingCoordinateDomainSplit K i m hK sigma).2.2 := by
        apply Finset.sum_congr rfl
        intro sigma _
        simp [fx, gy, isingCoordinateDomainSplit, spin]
      _ = _ := by simpa [C] using h
  have hxx :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK x.1))) =
        C * isingCoordinateDomainReflectionForm K i m hK beta fx fx := by
    have h := isingCoordinateDomain_weightedSum_eq_form
      K i m hK beta fx fx
    calc
      _ = ∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            fx (isingCoordinateDomainSplit K i m hK sigma).2.1 *
            fx (isingCoordinateDomainSplit K i m hK sigma).2.2 := by
        apply Finset.sum_congr rfl
        intro sigma _
        simp [fx, isingCoordinateDomainSplit, spin]
      _ = _ := by simpa [C] using h
  have hyy :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma y.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK y.1))) =
        C * isingCoordinateDomainReflectionForm K i m hK beta gy gy := by
    have h := isingCoordinateDomain_weightedSum_eq_form
      K i m hK beta gy gy
    calc
      _ = ∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            gy (isingCoordinateDomainSplit K i m hK sigma).2.1 *
            gy (isingCoordinateDomainSplit K i m hK sigma).2.2 := by
        apply Finset.sum_congr rfl
        intro sigma _
        simp [gy, isingCoordinateDomainSplit, spin]
      _ = _ := by simpa [C] using h
  have hnum :
      (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK y.1))) ^ 2 <=
        (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma x.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK x.1))) *
        (∑ sigma : ConfigSpace (freeDomainVertices K),
          isingWeight (freeDomainGraph K) beta 0 sigma *
            (spin sigma y.1 * spin sigma
              (isingCoordinateDomainReflectEquiv K i m hK y.1))) := by
    rw [hcross, hxx, hyy]
    have hC : 0 <= C ^ 2 := sq_nonneg C
    nlinarith
  unfold isingExpectation isingProb
  let Z := isingZ (freeDomainGraph K) beta 0
  have hconvert (f : ConfigSpace (freeDomainVertices K) → Real) :
      (∑ s, isingWeight (freeDomainGraph K) beta 0 s / Z * f s) =
        (∑ s, isingWeight (freeDomainGraph K) beta 0 s * f s) / Z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hconvert, hconvert, hconvert, div_pow, div_mul_div_comm]
  simpa [pow_two] using
    (div_le_div_of_nonneg_right hnum (sq_nonneg Z))

end

end StatMech.FrontierA

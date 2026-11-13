/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExtTest.Geometry.Manifold.Riemannian.JacobiField
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Near-miss controls N1-N3 for Jacobi fields
Bump field that is not a Jacobi field, the unit circle with its
covariant acceleration that is not a geodesic, and distinct times.
-/
open Bundle Manifold
open scoped Manifold ContDiff
namespace JacobiNegativeTests
noncomputable section
/-- The bump field along `lineU` vanishing at `0` and `1`. -/
def bumpB : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (JacobiTests.lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ)
    (JacobiTests.lineU s).proj).symm
    (((s * (1 - s) : ℝ)) • Complex.I)
/-- Pin: the bump vanishes at `0`. -/
theorem bumpB_zero : bumpB 0 = 0 := by
  simp [bumpB]
/-- Pin: the bump vanishes at `1`. -/
theorem bumpB_one : bumpB 1 = 0 := by
  simp [bumpB]
/-- Pin: the bump is nonzero at `1 / 2`. -/
theorem bumpB_half_ne : bumpB (1 / 2) ≠ 0 := by
  intro h
  have hs : ((1 / 2 : ℝ) * (1 - 1 / 2) : ℝ) ≠ 0 := by norm_num
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : ((((1 / 2 : ℝ) * (1 - 1 / 2) : ℝ)) • Complex.I : ℂ) = 0 := by
    have hc := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ)
      (JacobiTests.lineU (1 / 2)).proj) h
    simpa [bumpB, ContinuousLinearEquiv.apply_symm_apply] using hc
  exact hs (smul_eq_zero.mp hC |>.resolve_right hI)
/-- The bump is not a Jacobi field along the line. -/
theorem not_jacobi_bump :
    ¬ IsJacobiField 𝓘(ℝ, ℂ) JacobiTests.lineU bumpB := by
  intro hJ
  have hall := JacobiTests.noConjChar_complex JacobiTests.lineU bumpB
    JacobiTests.line_isGeodesic hJ bumpB_zero bumpB_one
  exact bumpB_half_ne (hall (1 / 2))
/-- The unit circle velocity curve in the plane. -/
def circleC : ℝ → TangentBundle 𝓘(ℝ, ℂ) ℂ := fun t =>
  ⟨Complex.exp ((t : ℂ) * Complex.I),
    Complex.exp ((t : ℂ) * Complex.I) * Complex.I⟩
/-- The circle has the stated covariant acceleration at every time. -/
theorem circle_cov (t : ℝ) : HasCovariantDerivAlong 𝓘(ℝ, ℂ) circleC
    (fun s => (circleC s).snd) (fun s => -(circleC s).proj) t := by
  have hR : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) t := by
    simpa using HasDerivAt.ofReal_comp (hasDerivAt_id t)
  have hMul : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I)
      ((1 : ℂ) * Complex.I) t :=
    hR.mul_const Complex.I
  have hExp : HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * ((1 : ℂ) * Complex.I)) t :=
    HasDerivAt.cexp hMul
  have hprojD : HasDerivAt (fun s => (circleC s).proj)
      ((circleC t).snd) t := by
    simpa [circleC, one_mul] using hExp
  have hV0 : HasDerivAt (fun s => ((circleC s).snd : ℂ))
      (-Complex.exp ((t : ℂ) * Complex.I)) t := by
    have hmc := hExp.mul_const Complex.I
    simpa [circleC, mul_assoc, one_mul, Complex.I_mul_I, mul_neg,
      mul_one] using hmc
  have hLin : HasFDerivAt
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj).toContinuousLinearMap)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj).toContinuousLinearMap)
      ((circleC t).snd) :=
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj).toContinuousLinearMap.hasFDerivAt)
  have hComp := HasFDerivAt.comp_hasDerivAt t hLin hV0
  have hV : HasDerivAt
      (fun s => NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC s).proj
        ((circleC s).snd))
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj
        (-(circleC t).proj)) t := by
    show HasDerivAt
        (fun s => ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj).toContinuousLinearMap)
          (((circleC s).snd : ℂ)))
        (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (circleC t).proj).toContinuousLinearMap)
          (-Complex.exp ((t : ℂ) * Complex.I))) t
    exact hComp
  exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt circleC
    _ _ t hprojD hV
/-- The circle is not a geodesic velocity curve. -/
theorem circle_not_geodesic :
    ¬ IsGeodesicVelocityCurve 𝓘(ℝ, ℂ) circleC := by
  intro hgeo
  have hgeocov := (isGeodesicVelocityCurve_iff_hasCovariantDerivAlong
    𝓘(ℝ, ℂ) circleC).mp hgeo 0
  have hcirc := circle_cov 0
  have hunique := HasCovariantDerivAlong.unique 𝓘(ℝ, ℂ) hgeocov hcirc
  have hproj : (circleC 0).proj = 0 := neg_eq_zero.mp hunique.symm
  have hexp0 : (circleC 0).proj = 1 := by
    simp [circleC]
  rw [hexp0] at hproj
  exact one_ne_zero hproj
/-- The shifted field along `lineU` vanishing at `2`. -/
def shiftK : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (JacobiTests.lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ)
    (JacobiTests.lineU s).proj).symm
    ((((s - 2 : ℝ))) • Complex.I)
/-- Pin: the shifted field vanishes at `2`. -/
theorem shiftK_two : shiftK 2 = 0 := by
  simp [shiftK]
/-- Pin: the shifted field is nonzero at `0`. -/
theorem shiftK_zero_ne : shiftK 0 ≠ 0 := by
  intro h
  have hs : ((0 : ℝ) - 2 : ℝ) ≠ 0 := by norm_num
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : ((((0 : ℝ) - 2 : ℝ)) • Complex.I : ℂ) = 0 := by
    have hc := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ)
      (JacobiTests.lineU 0).proj) h
    simp [shiftK, ContinuousLinearEquiv.apply_symm_apply] at hc
  exact hs (smul_eq_zero.mp hC |>.resolve_right hI)
/-- Equal times are never conjugate along the line. -/
theorem not_conj_same :
    ¬ AreConjugateAlong 𝓘(ℝ, ℂ) JacobiTests.lineU 2 2 :=
  fun h => h.2.1 rfl
end
end JacobiNegativeTests

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Geometry.Manifold.Riemannian.JacobiField.VectorSpace
public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow.VectorSpace
/-!
# Tests for Jacobi fields in flat space

Tests for Jacobi fields in flat space: criterion, line and zero-velocity
fields, no conjugate points, Burns-Matveev form.
-/
open Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal
noncomputable section
namespace JacobiTests
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

public section
/-- Velocity curve of the line geodesic in the plane. -/
def lineU : ℝ → TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  fun t => ⟨(t : ℂ), (NormedSpace.fromTangentSpace (𝕜 := ℝ) (t : ℂ)).symm 1⟩
end

/-- Linear Jacobi field along the line geodesic. -/
def lineJ : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (lineU s).proj).symm
    (((1 + 2 * s : ℝ)) • Complex.I)

/-- Covariant derivative of the linear Jacobi field. -/
def lineJ' : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (lineU s).proj).symm
    (((2 : ℝ)) • Complex.I)

public section
/-- The line curve is a geodesic velocity curve. -/
theorem line_isGeodesic : IsGeodesicVelocityCurve 𝓘(ℝ, ℂ) lineU := by
  rw [Manifold.isGeodesicVelocityCurve_vectorSpace_iff]
  intro t
  have hpt : (lineU t).proj = ((t : ℝ) : ℂ) := rfl
  have hp0 : (lineU 0).proj = ((0 : ℝ) : ℂ) := rfl
  have hvel0 : NormedSpace.fromTangentSpace (lineU 0).proj (lineU 0).snd
      = (1 : ℂ) := ContinuousLinearEquiv.apply_symm_apply _ _
  have hvelt : NormedSpace.fromTangentSpace (lineU t).proj (lineU t).snd
      = (1 : ℂ) := ContinuousLinearEquiv.apply_symm_apply _ _
  have e2 : (NormedSpace.fromTangentSpace (lineU t).proj) (lineU t).snd =
      (NormedSpace.fromTangentSpace (lineU 0).proj) (lineU 0).snd := by
    rw [hvelt, hvel0]
  have e1 : (lineU t).proj = (lineU 0).proj + t •
      (NormedSpace.fromTangentSpace (lineU 0).proj) (lineU 0).snd := by
    rw [hvel0, hpt, hp0]
    simp [Complex.real_smul]
  exact ⟨e1, e2⟩
end

/-- Base-curve derivative of the line geodesic. -/
theorem line_hproj (t : ℝ) : HasDerivAt (fun s => (lineU s).proj)
    ((lineU t).snd) t :=
  (hasDerivAt_iff_hasFDerivAt).mpr
    (hasMFDerivAt_iff_hasFDerivAt.mp (line_isGeodesic.hasMFDerivAt_proj t))

/-- The linear field satisfies the Jacobi equation along the line. -/
theorem line_satisfiesJacobiEquation : SatisfiesJacobiEquation 𝓘(ℝ, ℂ) lineU lineJ := by
  have hV : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace _ (lineJ s))
      (NormedSpace.fromTangentSpace _ (lineJ' t)) t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace (lineU s).proj
        (lineJ s)) = (fun s : ℝ => (1 + 2 * s : ℝ) • Complex.I) := by
      funext s
      simp [lineJ]
    have heq' : NormedSpace.fromTangentSpace (lineU t).proj
        (lineJ' t) = ((2 : ℝ) • Complex.I) := by
      simp [lineJ']
    have hlin : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 t := by
      have h2 := (hasDerivAt_id t).const_mul (2 : ℝ)
      have h1 := h2.const_add (1 : ℝ)
      have hmul : (2 : ℝ) * 1 = 2 := mul_one 2
      simpa [hmul, add_comm] using h1
    rw [heq, heq']
    exact hlin.smul_const Complex.I
  have hV' : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace _ (lineJ' s)) 0 t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace (lineU s).proj
        (lineJ' s)) = (fun _ : ℝ => ((2 : ℝ) • Complex.I)) := by
      funext s
      simp [lineJ']
    rw [heq]
    exact hasDerivAt_const t _
  refine ⟨lineJ', fun t => ⟨?_, ?_⟩⟩
  · exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt lineU
      lineJ lineJ' t (line_hproj t) (hV t)
  · have htarget : HasDerivAt
        (fun s => NormedSpace.fromTangentSpace _ (lineJ' s))
        (NormedSpace.fromTangentSpace _
          (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((lineU t).proj)
            (lineJ t) ((lineU t).snd) ((lineU t).snd))) t := by
      have h0 : (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((lineU t).proj)
          (lineJ t) ((lineU t).snd) ((lineU t).snd)) = 0 := by
        simp [Manifold.riemannCurvature_vectorSpace]
      rw [h0]
      simpa using (hV' t)
    exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt lineU
      lineJ' (fun s => -Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((lineU s).proj)
        (lineJ s) ((lineU s).snd) ((lineU s).snd)) t (line_hproj t) htarget

/-- The linear field is a Jacobi field along the line geodesic. -/
theorem line_isJacobiField : IsJacobiField 𝓘(ℝ, ℂ) lineU lineJ :=
  ⟨line_isGeodesic, line_satisfiesJacobiEquation⟩

/-- Pin for the linear field at time zero. -/
theorem lineJ_zero : lineJ 0 =
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((lineU 0).proj)).symm
      Complex.I := by
  simp [lineJ, one_smul]

/-- Pin for the linear field at time one. -/
theorem lineJ_one : lineJ 1 =
    (3 : ℝ) • (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((lineU 1).proj)).symm
      Complex.I := by
  have h13 : (1 + 2 * (1 : ℝ) : ℝ) = 3 := by norm_num
  simp only [lineJ, h13, map_smul]

/-- Constant zero velocity curve. -/
def zeroU : ℝ → TangentBundle 𝓘(ℝ, ℂ) ℂ :=
  fun _ => ⟨(0 : ℂ), 0⟩

/-- Linear Jacobi field along the zero-velocity curve. -/
def zeroJ : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (zeroU s).proj :=
  fun s => (NormedSpace.fromTangentSpace ((zeroU s).proj)).symm
    (((s : ℝ)) • Complex.I)

/-- Covariant derivative of the zero-velocity Jacobi field. -/
def zeroJ' : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (zeroU s).proj :=
  fun s => (NormedSpace.fromTangentSpace ((zeroU s).proj)).symm Complex.I

/-- The zero curve is a geodesic velocity curve. -/
theorem zero_isGeodesic : IsGeodesicVelocityCurve 𝓘(ℝ, ℂ) zeroU := by
  rw [Manifold.isGeodesicVelocityCurve_vectorSpace_iff]
  intro t
  have hpt : (zeroU t).proj = (0 : ℂ) := rfl
  have hp0 : (zeroU 0).proj = (0 : ℂ) := rfl
  have hvel0 : NormedSpace.fromTangentSpace (zeroU 0).proj (zeroU 0).snd
      = (0 : ℂ) := map_zero _
  have hvelt : NormedSpace.fromTangentSpace (zeroU t).proj (zeroU t).snd
      = (0 : ℂ) := map_zero _
  have e2 : (NormedSpace.fromTangentSpace (zeroU t).proj) (zeroU t).snd =
      (NormedSpace.fromTangentSpace (zeroU 0).proj) (zeroU 0).snd := by
    rw [hvelt, hvel0]
  have e1 : (zeroU t).proj = (zeroU 0).proj + t •
      (NormedSpace.fromTangentSpace (zeroU 0).proj) (zeroU 0).snd := by
    rw [hvel0, hpt, hp0]
    simp
  exact ⟨e1, e2⟩

/-- Base-curve derivative of the zero geodesic. -/
theorem zero_hproj (t : ℝ) : HasDerivAt (fun s => (zeroU s).proj)
    ((zeroU t).snd) t :=
  (hasDerivAt_iff_hasFDerivAt).mpr
    (hasMFDerivAt_iff_hasFDerivAt.mp (zero_isGeodesic.hasMFDerivAt_proj t))

/-- The linear field satisfies the Jacobi equation along the zero curve. -/
theorem zero_satisfiesJacobiEquation : SatisfiesJacobiEquation 𝓘(ℝ, ℂ) zeroU zeroJ := by
  have hV : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace ((zeroU s).proj) (zeroJ s))
      (NormedSpace.fromTangentSpace ((zeroU t).proj) (zeroJ' t)) t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace ((zeroU s).proj)
        (zeroJ s)) = (fun s : ℝ => s • Complex.I) := by
      funext s
      simp [zeroJ, ContinuousLinearEquiv.apply_symm_apply]
    have heq' : NormedSpace.fromTangentSpace ((zeroU t).proj)
        (zeroJ' t) = Complex.I := by
      simp [zeroJ', ContinuousLinearEquiv.apply_symm_apply]
    rw [heq, heq']
    simpa [one_smul] using (hasDerivAt_id t).smul_const Complex.I
  have hV' : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace ((zeroU s).proj)
        (zeroJ' s)) 0 t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace ((zeroU s).proj)
        (zeroJ' s)) = (fun _ : ℝ => Complex.I) := by
      funext s
      simp [zeroJ', ContinuousLinearEquiv.apply_symm_apply]
    rw [heq]
    exact hasDerivAt_const t _
  refine ⟨zeroJ', fun t => ⟨?_, ?_⟩⟩
  · exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt zeroU
      zeroJ zeroJ' t (zero_hproj t) (hV t)
  · have htarget : HasDerivAt
        (fun s => NormedSpace.fromTangentSpace ((zeroU s).proj)
          (zeroJ' s))
        (NormedSpace.fromTangentSpace ((zeroU t).proj)
          (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((zeroU t).proj)
            (zeroJ t) ((zeroU t).snd) ((zeroU t).snd))) t := by
      have h0 : (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((zeroU t).proj)
          (zeroJ t) ((zeroU t).snd) ((zeroU t).snd)) = 0 := by
        simp [Manifold.riemannCurvature_vectorSpace]
      rw [h0, map_zero]
      exact hV' t
    exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt zeroU
      zeroJ' (fun s => -Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((zeroU s).proj)
        (zeroJ s) ((zeroU s).snd) ((zeroU s).snd)) t (zero_hproj t) htarget

/-- The linear field is a Jacobi field along the constant geodesic. -/
theorem zero_isJacobiField : IsJacobiField 𝓘(ℝ, ℂ) zeroU zeroJ :=
  ⟨zero_isGeodesic, zero_satisfiesJacobiEquation⟩

/-- Pin for the zero-velocity field at time zero. -/
theorem zeroJ_zero : zeroJ 0 = 0 := by
  simp [zeroJ]

/-- Pin for the zero-velocity field at time one. -/
theorem zeroJ_one : zeroJ 1 =
    (NormedSpace.fromTangentSpace ((zeroU 1).proj)).symm Complex.I := by
  simp [zeroJ, one_smul]

/-- The line has no conjugate points. -/
theorem hasNoConjugatePoints_real : HasNoConjugatePoints 𝓘(ℝ, ℝ) ℝ :=
  Manifold.hasNoConjugatePoints_vectorSpace

/-- The plane has no conjugate points. -/
theorem hasNoConjugatePoints_complex : HasNoConjugatePoints 𝓘(ℝ, ℂ) ℂ :=
  Manifold.hasNoConjugatePoints_vectorSpace

/-- Zero-dimensional Euclidean space has no conjugate points. -/
theorem hasNoConjugatePoints_finZero : HasNoConjugatePoints
    𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0)) :=
  Manifold.hasNoConjugatePoints_vectorSpace

public section
/-- Burns-Matveev form of no conjugate points on the plane. -/
theorem noConjChar_complex (u : ℝ → TangentBundle 𝓘(ℝ, ℂ) ℂ)
    (J : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (u s).proj) :
    IsGeodesicVelocityCurve 𝓘(ℝ, ℂ) u → SatisfiesJacobiEquation 𝓘(ℝ, ℂ) u J →
    J 0 = 0 → J 1 = 0 → ∀ s : ℝ, J s = 0 :=
  fun hgeo hJ ha hb => (hasNoConjugatePoints_iff 𝓘(ℝ, ℂ) ℂ).mp
    hasNoConjugatePoints_complex u J 0 1 hgeo hJ zero_ne_one ha hb
end

/-- Zero and one are not conjugate along the zero curve. -/
theorem notConj_zero : ¬ AreConjugateAlong 𝓘(ℝ, ℂ) zeroU 0 1 :=
  hasNoConjugatePoints_complex zeroU 0 1

/-- Negative times are not conjugate along the line. -/
theorem notConj_neg : ¬ AreConjugateAlong 𝓘(ℝ, ℂ) lineU (-1) 1 :=
  hasNoConjugatePoints_complex lineU (-1) 1

/-- Swapped times are not conjugate along the line. -/
theorem notConj_swap : ¬ AreConjugateAlong 𝓘(ℝ, ℂ) lineU 1 (-1) :=
  hasNoConjugatePoints_complex lineU 1 (-1)

/-- Shifted linear Jacobi field along the line geodesic. -/
def lineL : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (lineU s).proj).symm
    ((((s + 1 : ℝ))) • Complex.I)

/-- Covariant derivative of the shifted linear field. -/
def lineL' : (s : ℝ) → TangentSpace 𝓘(ℝ, ℂ) (lineU s).proj :=
  fun s => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (lineU s).proj).symm
    Complex.I

/-- The shifted field satisfies the Jacobi equation along the line. -/
theorem lineL_satisfiesJacobiEquation : SatisfiesJacobiEquation 𝓘(ℝ, ℂ) lineU lineL := by
  have hV : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace _ (lineL s)) Complex.I t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace (lineU s).proj
        (lineL s)) = (fun s : ℝ => (s + 1 : ℝ) • Complex.I) := by
      funext s
      simp [lineL]
    rw [heq]
    simpa [one_smul] using ((hasDerivAt_id t).add_const 1).smul_const
      Complex.I
  have hV' : ∀ t : ℝ, HasDerivAt
      (fun s => NormedSpace.fromTangentSpace _ (lineL' s)) 0 t := by
    intro t
    have heq : (fun s => NormedSpace.fromTangentSpace (lineU s).proj
        (lineL' s)) = (fun _ : ℝ => Complex.I) := by
      funext s
      simp [lineL']
    rw [heq]
    exact hasDerivAt_const t _
  refine ⟨lineL', fun t => ⟨?_, ?_⟩⟩
  · exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt lineU
      lineL _ t (line_hproj t) (hV t)
  · have htarget : HasDerivAt
        (fun s => NormedSpace.fromTangentSpace _ (lineL' s))
        (NormedSpace.fromTangentSpace _
          (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((lineU t).proj)
            (lineL t) ((lineU t).snd) ((lineU t).snd))) t := by
      have h0 : (-Manifold.riemannCurvature 𝓘(ℝ, ℂ) ((lineU t).proj)
          (lineL t) ((lineU t).snd) ((lineU t).snd)) = 0 := by
        simp [Manifold.riemannCurvature_vectorSpace]
      rw [h0]
      simpa using (hV' t)
    exact Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt lineU
      _ _ t (line_hproj t) htarget

/-- The shifted field is a Jacobi field along the line geodesic. -/
theorem lineL_isJacobiField : IsJacobiField 𝓘(ℝ, ℂ) lineU lineL :=
  ⟨line_isGeodesic, lineL_satisfiesJacobiEquation⟩

/-- Pin for the shifted field at time minus one. -/
theorem lineL_neg : lineL (-1) = 0 := by
  have h10 : ((-1 : ℝ) + 1 : ℝ) = 0 := by norm_num
  simp [lineL, h10]

/-- Pin for the shifted field at time one. -/
theorem lineL_one : lineL 1 =
    (2 : ℝ) • (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((lineU 1).proj)).symm
      Complex.I := by
  have h12 : ((1 : ℝ) + 1 : ℝ) = 2 := by norm_num
  simp only [lineL, h12, map_smul]

end JacobiTests

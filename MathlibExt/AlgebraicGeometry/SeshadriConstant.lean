/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SeshadriConstant

open Finset MvPolynomial

/-!
# The ten-point Seshadri constant on the plane

For ten distinct points in an affine chart of `ℙ²`, the Seshadri constant is
the infimum of `deg C / ∑ᵢ mult_{xᵢ} C` over nonzero plane curves passing
through at least one of the points. The generic constant is the supremum of
these values over all injective ten-point configurations. Harbourne--Roé
record that this supremum is the value at very general points.

Source: Optimization Problems, record 74a, "10-point multi-point Seshadri
constant on `ℙ²`", frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/74a.md` SHA-256
`4464e63b280f31b354015431cacaa82789baf8879b45bca06cb5caf0c55557ca`.

The Lean model works in one affine chart. The identification with the
projective definition (choice of a line avoiding the ten points,
homogenization and dehomogenization, and projective invariance) is not
formalized here; the catalogue bounds are recorded against this affine-chart
supremum in `WantedExt/AlgebraicGeometry/SeshadriConstantWanted.lean`.
-/

/-- A polynomial in two complex variables, representing an affine plane curve. -/
abbrev PlanePolynomial : Type := MvPolynomial (Fin 2) ℂ

/-- A point of the affine complex plane. -/
abbrev AffinePoint : Type := Fin 2 → ℂ

/-- Translate a polynomial so that the point `a` moves to the origin. -/
noncomputable def shifted (f : PlanePolynomial) (a : AffinePoint) : PlanePolynomial :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) f

theorem eval_shifted (f : PlanePolynomial) (a y : AffinePoint) :
    MvPolynomial.eval y (shifted f a) =
      MvPolynomial.eval (fun i => y i + a i) f := by
  rw [shifted, MvPolynomial.aeval_def, MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval y).comp (algebraMap ℂ PlanePolynomial) =
      RingHom.id ℂ := by
    ext r
    simp [MvPolynomial.algebraMap_eq]
  rw [hC]
  simp

theorem coeff_zero_shifted (f : PlanePolynomial) (a : AffinePoint) :
    (shifted f a).coeff 0 = MvPolynomial.eval a f := by
  rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero', eval_shifted]
  simp

theorem shifted_eq_zero_iff {f : PlanePolynomial} {a : AffinePoint} :
    shifted f a = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply MvPolynomial.funext
    intro y
    have hy := congrArg (MvPolynomial.eval (fun i => y i - a i)) h
    simp only [map_zero] at hy
    rw [eval_shifted] at hy
    simpa using hy
  · rintro rfl
    simp [shifted]

/-- The total degree of one monomial exponent vector. -/
def monomialDegree (m : Fin 2 →₀ ℕ) : ℕ :=
  ∑ i, m i

theorem monomialDegree_eq_zero_iff {m : Fin 2 →₀ ℕ} :
    monomialDegree m = 0 ↔ m = 0 := by
  constructor
  · intro h
    ext i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (m j))
      (Finset.mem_univ i)
    rw [monomialDegree] at h
    simp only [Finsupp.zero_apply]
    omega
  · rintro rfl
    simp [monomialDegree]

/-- The multiplicity of a plane polynomial at a point: the least total degree
occurring after translating the point to the origin. It is totalized to `0`
for the zero polynomial; applications below exclude that case. -/
noncomputable def multiplicity (f : PlanePolynomial) (a : AffinePoint) : ℕ :=
  if h : (shifted f a).support.Nonempty then
    ((shifted f a).support.image monomialDegree).min'
      (Finset.image_nonempty.mpr h)
  else 0

theorem multiplicity_le_of_mem_support {f : PlanePolynomial} {a : AffinePoint}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ (shifted f a).support) :
    multiplicity f a ≤ monomialDegree m := by
  have hne : (shifted f a).support.Nonempty := ⟨m, hm⟩
  rw [multiplicity, dite_eq_left hne]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

theorem multiplicity_eq_zero_of_eval_ne_zero {f : PlanePolynomial}
    {a : AffinePoint} (hf : MvPolynomial.eval a f ≠ 0) :
    multiplicity f a = 0 := by
  have h0 : (0 : Fin 2 →₀ ℕ) ∈ (shifted f a).support := by
    rw [MvPolynomial.mem_support_iff, coeff_zero_shifted]
    exact hf
  exact Nat.eq_zero_of_le_zero
    (by simpa [monomialDegree] using multiplicity_le_of_mem_support h0)

theorem multiplicity_pos_of_eval_eq_zero {f : PlanePolynomial}
    {a : AffinePoint} (hf : f ≠ 0) (ha : MvPolynomial.eval a f = 0) :
    0 < multiplicity f a := by
  have hshift : shifted f a ≠ 0 := by
    rwa [ne_eq, shifted_eq_zero_iff]
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hshift
  have hne : (shifted f a).support.Nonempty := ⟨m, hm⟩
  have hmin_mem := Finset.min'_mem ((shifted f a).support.image monomialDegree)
    (Finset.image_nonempty.mpr hne)
  rw [Finset.mem_image] at hmin_mem
  obtain ⟨m₀, hm₀, hdeg⟩ := hmin_mem
  have hm0ne : m₀ ≠ 0 := by
    intro hm0
    rw [hm0, MvPolynomial.mem_support_iff, coeff_zero_shifted] at hm₀
    exact hm₀ ha
  have hpos : 0 < monomialDegree m₀ :=
    Nat.pos_of_ne_zero (fun h => hm0ne (monomialDegree_eq_zero_iff.mp h))
  rw [multiplicity, dite_eq_left hne]
  omega

theorem shifted_X_sub_C (a : AffinePoint) :
    shifted (MvPolynomial.X 0 - MvPolynomial.C (a 0)) a = MvPolynomial.X 0 := by
  simp [shifted]

/-- A coordinate line through a point has multiplicity one there. -/
theorem multiplicity_X_sub_C (a : AffinePoint) :
    multiplicity (MvPolynomial.X 0 - MvPolynomial.C (a 0)) a = 1 := by
  simp only [multiplicity, shifted_X_sub_C, MvPolynomial.support_X]
  simp [monomialDegree]

/-- The degree-over-multiplicity ratios tested by one ten-point configuration. -/
def seshadriRatios (x : Fin 10 → AffinePoint) : Set ℝ :=
  {r | ∃ f : PlanePolynomial, f ≠ 0 ∧
    0 < ∑ i, multiplicity f (x i) ∧
    r = (f.totalDegree : ℝ) / ((∑ i, multiplicity f (x i) : ℕ) : ℝ)}

/-- The Seshadri constant of one affine ten-point configuration, totalized by
the real infimum. -/
noncomputable def affineSeshadriConstant (x : Fin 10 → AffinePoint) : ℝ :=
  sInf (seshadriRatios x)

theorem seshadriRatios_nonneg {x : Fin 10 → AffinePoint} {r : ℝ}
    (hr : r ∈ seshadriRatios x) : 0 ≤ r := by
  obtain ⟨f, _hf, hsum, rfl⟩ := hr
  positivity

theorem bddBelow_seshadriRatios (x : Fin 10 → AffinePoint) :
    BddBelow (seshadriRatios x) :=
  ⟨0, fun _ hr => seshadriRatios_nonneg hr⟩

theorem affineSeshadriConstant_nonneg (x : Fin 10 → AffinePoint) :
    0 ≤ affineSeshadriConstant x :=
  Real.sInf_nonneg (fun _ hr => seshadriRatios_nonneg hr)

/-- A coordinate line through the first point bounds every affine
configuration's Seshadri constant by one. -/
theorem affineSeshadriConstant_le_one (x : Fin 10 → AffinePoint) :
    affineSeshadriConstant x ≤ 1 := by
  let f : PlanePolynomial := MvPolynomial.X 0 - MvPolynomial.C ((x 0) 0)
  have hfne : f ≠ 0 := by
    intro hf
    have hf' : (MvPolynomial.X 0 - MvPolynomial.C ((x 0) 0) : PlanePolynomial) = 0 := hf
    have h := multiplicity_X_sub_C (x 0)
    rw [hf'] at h
    simp [multiplicity, shifted] at h
  have hmult0 : multiplicity f (x 0) = 1 := multiplicity_X_sub_C (x 0)
  have hsum : 1 ≤ ∑ i, multiplicity f (x i) := by
    have h := Finset.single_le_sum (fun i _ => Nat.zero_le (multiplicity f (x i)))
      (Finset.mem_univ (0 : Fin 10))
    rwa [hmult0] at h
  have hsumpos : 0 < ∑ i, multiplicity f (x i) := hsum
  have hmem : (f.totalDegree : ℝ) /
      ((∑ i, multiplicity f (x i) : ℕ) : ℝ) ∈ seshadriRatios x :=
    ⟨f, hfne, hsumpos, rfl⟩
  have hdeg : f.totalDegree ≤ 1 := by
    calc f.totalDegree ≤ max (MvPolynomial.X (0 : Fin 2)).totalDegree
          (MvPolynomial.C ((x 0) 0)).totalDegree := MvPolynomial.totalDegree_sub _ _
      _ = 1 := by simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  have hratio : (f.totalDegree : ℝ) /
      ((∑ i, multiplicity f (x i) : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hsumpos)]
    exact_mod_cast hdeg.trans hsum
  exact (csInf_le (bddBelow_seshadriRatios x) hmem).trans hratio

/-- The generic ten-point Seshadri constant, modeled in an affine chart as
the supremum over injective ten-point configurations. -/
noncomputable def genericSeshadriConstant : ℝ :=
  sSup {r | ∃ x : Fin 10 → AffinePoint, Function.Injective x ∧
    r = affineSeshadriConstant x}

/-- The ten-point multi-point Seshadri constant `C₇₄` in the affine-chart model. -/
noncomputable def seshadriConstant10 : ℝ :=
  genericSeshadriConstant

/-- Ten distinct points on one coordinate axis, used only to exhibit an
injective configuration. -/
private def standardPoints : Fin 10 → AffinePoint :=
  fun i j => if j = 0 then (i : ℂ) else 0

private theorem standardPoints_injective : Function.Injective standardPoints := by
  intro i k h
  have h0 := congrFun h 0
  simp [standardPoints] at h0
  exact Fin.ext (by exact_mod_cast h0)

theorem bddAbove_genericSeshadriSet :
    BddAbove {r | ∃ x : Fin 10 → AffinePoint, Function.Injective x ∧
      r = affineSeshadriConstant x} := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, _hx, rfl⟩
  exact affineSeshadriConstant_le_one x

theorem genericSeshadriConstant_le_one : genericSeshadriConstant ≤ 1 := by
  apply csSup_le
  · exact ⟨affineSeshadriConstant standardPoints, standardPoints,
      standardPoints_injective, rfl⟩
  · rintro r ⟨x, _hx, rfl⟩
    exact affineSeshadriConstant_le_one x

theorem zero_le_genericSeshadriConstant : 0 ≤ genericSeshadriConstant := by
  have hmem : affineSeshadriConstant standardPoints ∈
      {r | ∃ x : Fin 10 → AffinePoint, Function.Injective x ∧
        r = affineSeshadriConstant x} :=
    ⟨standardPoints, standardPoints_injective, rfl⟩
  exact (affineSeshadriConstant_nonneg standardPoints).trans
    (le_csSup bddAbove_genericSeshadriSet hmem)

theorem seshadriConstant10_nonneg : 0 ≤ seshadriConstant10 :=
  zero_le_genericSeshadriConstant

theorem seshadriConstant10_le_one : seshadriConstant10 ≤ 1 :=
  genericSeshadriConstant_le_one

end MathlibExt.AlgebraicGeometry.SeshadriConstant

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.JacobiField
public import MathlibExt.Geometry.Manifold.Riemannian.LeviCivitaVectorSpace
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Jacobi fields in Euclidean space

Let `F` be a finite-dimensional real inner product space with its standard Riemannian metric.
This file records the flat-space companion facts for covariant derivatives along curves and
Jacobi fields: a sufficient ordinary-derivative criterion for `Manifold.HasCovariantDerivAlong`
and the absence of conjugate points. Textbook sources: Lee, Introduction to Riemannian
Manifolds (2nd ed.), Thm. 4.24, Prop. 5.5, Ch. 10; do Carmo, Riemannian Geometry, Ch. 2
Prop. 2.2, Ch. 5.

## Main results

* `Manifold.hasCovariantDerivAlong_vectorSpace_of_hasDerivAt`: sufficient criterion for the
  covariant derivative along a curve in flat space.
* `Manifold.hasNoConjugatePoints_vectorSpace`: flat space has no conjugate points.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

namespace Manifold

/-- Sufficient criterion for the covariant derivative along a curve in flat space: if the base
curve has derivative the velocity and the field has derivative the candidate, then
`HasCovariantDerivAlong` holds. Sufficient only; no converse is claimed. -/
theorem hasCovariantDerivAlong_vectorSpace_of_hasDerivAt
    (u : ℝ → TangentBundle 𝓘(ℝ, F) F)
    (V V' : (s : ℝ) → TangentSpace 𝓘(ℝ, F) (u s).proj) (t : ℝ)
    (hproj : HasDerivAt (fun s => (u s).proj) ((u t).snd) t)
    (hV : HasDerivAt (fun s => NormedSpace.fromTangentSpace _ (V s))
      (NormedSpace.fromTangentSpace _ (V' t)) t) :
    HasCovariantDerivAlong 𝓘(ℝ, F) u V V' t := by
  have hprojF : HasFDerivAt (fun s => (u s).proj)
      (ContinuousLinearMap.toSpanSingleton ℝ ((u t).snd)) t :=
    (hasDerivAt_iff_hasFDerivAt).mp hproj
  have hMF : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun s => (u s).proj) t
      (ContinuousLinearMap.toSpanSingleton ℝ ((u t).snd)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr hprojF
  refine ⟨hMF, fun W hW => ?_⟩
  have hsecT : MDiffAt
      (fun y : F => (trivializationAt F _ ((u t).proj) ⟨y, W y⟩).2)
      ((u t).proj) :=
    ((mdifferentiableAt_section 𝓘(ℝ, F) W).mp hW)
  have hWdiff : DifferentiableAt ℝ (fun y : F => (W y : F)) ((u t).proj) := by
    have h := mdifferentiableAt_iff_differentiableAt.mp hsecT
    simpa [trivializationAt_model_space_apply] using h
  have hWcomp : HasDerivAt (fun s => W ((u s).proj))
      ((fderiv ℝ (fun y : F => (W y : F)) ((u t).proj)) ((u t).snd)) t :=
    HasFDerivAt.comp_hasDerivAt t hWdiff.hasFDerivAt hproj
  have hprod : HasDerivAt (fun s => inner ℝ
      (NormedSpace.fromTangentSpace _ (V s)) (W ((u s).proj)))
      (inner ℝ (NormedSpace.fromTangentSpace _ (V t))
        ((fderiv ℝ (fun y : F => (W y : F)) ((u t).proj)) ((u t).snd)) +
        inner ℝ (NormedSpace.fromTangentSpace _ (V' t))
        (W ((u t).proj))) t :=
    HasDerivAt.inner ℝ hV hWcomp
  have hconn : (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F) W
      ((u t).proj) ((u t).snd) =
      (fderiv ℝ (fun y : F => (W y : F)) ((u t).proj)) ((u t).snd) := by
    have h := CovariantDerivative.leviCivitaConnection_vectorSpace_apply
      hW ((u t).snd)
    simpa using h
  have hfinal : HasDerivAt (fun s => inner ℝ (V s) (W ((u s).proj)))
      (inner ℝ (V' t) (W ((u t).proj)) + inner ℝ (V t)
        ((CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F) W
          ((u t).proj) ((u t).snd))) t := by
    rw [hconn, add_comm]
    exact hprod
  exact hfinal

/-- A finite-dimensional real inner product space with its standard Riemannian metric has no
conjugate points: curvature vanishes, so a Jacobi field vanishing twice is zero. -/
theorem hasNoConjugatePoints_vectorSpace :
    HasNoConjugatePoints 𝓘(ℝ, F) F := by
  intro u a b hconj
  obtain ⟨hgeo, hab, hex⟩ := hconj
  obtain ⟨J, hJ, ha, hb, hex2⟩ := hex
  obtain ⟨s₀, hs₀⟩ := hex2
  obtain ⟨J', hJ'⟩ := hJ
  have hW : ∀ t : ℝ, MDiffAt
      (T% (FiberBundle.extend F (J s₀))) ((u t).proj) :=
    fun t => FiberBundle.mdifferentiableAt_extend_model_space _ _
  have hconn : ∀ t : ℝ,
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) F)
        (FiberBundle.extend F (J s₀)) ((u t).proj) = 0 :=
    fun t => CovariantDerivative.leviCivitaConnection_extend_vectorSpace
      _ ((u t).proj)
  have hR : ∀ t : ℝ, Manifold.riemannCurvature 𝓘(ℝ, F) ((u t).proj)
      (J t) ((u t).snd) ((u t).snd) = 0 :=
    fun t => Manifold.riemannCurvature_vectorSpace _ _ _ _
  have hf2 : ∀ t : ℝ, HasDerivAt (fun s => inner ℝ (J' s)
      ((FiberBundle.extend F (J s₀)) ((u s).proj))) 0 t := by
    intro t
    simpa [hconn t, hR t, inner_zero_left, inner_zero_right,
      neg_zero, add_zero] using
      (((hJ' t).2).hasDerivAt_inner _ (hW t))
  have hf1 : ∀ t : ℝ, HasDerivAt (fun s => inner ℝ (J s)
      ((FiberBundle.extend F (J s₀)) ((u s).proj)))
      (inner ℝ (J' t) ((FiberBundle.extend F (J s₀)) ((u t).proj))) t := by
    intro t
    simpa [hconn t, inner_zero_right, add_zero] using
      (((hJ' t).1).hasDerivAt_inner _ (hW t))
  have hf2const (x y : ℝ) : inner ℝ (J' x)
      ((FiberBundle.extend F (J s₀)) ((u x).proj)) =
      inner ℝ (J' y) ((FiberBundle.extend F (J s₀)) ((u y).proj)) := by
    have hd : Differentiable ℝ (fun s => inner ℝ (J' s)
        ((FiberBundle.extend F (J s₀)) ((u s).proj))) :=
      fun z => (hf2 z).differentiableAt
    exact is_const_of_deriv_eq_zero hd (fun z => (hf2 z).deriv) x y
  have hf1a : inner ℝ (J a) ((FiberBundle.extend F (J s₀)) ((u a).proj))
      = 0 := by simp [ha]
  have hf1b : inner ℝ (J b) ((FiberBundle.extend F (J s₀)) ((u b).proj))
      = 0 := by simp [hb]
  have hC : inner ℝ (J' a) ((FiberBundle.extend F (J s₀)) ((u a).proj))
      = 0 := by
    have hg (t : ℝ) : HasDerivAt ((fun s => inner ℝ (J s)
        ((FiberBundle.extend F (J s₀)) ((u s).proj))) -
        (fun y => inner ℝ (J' a) ((FiberBundle.extend F (J s₀))
          ((u a).proj)) * y)) 0 t := by
      have hsub := (hf1 t).sub ((hasDerivAt_id t).const_mul
        (inner ℝ (J' a) ((FiberBundle.extend F (J s₀)) ((u a).proj))))
      simpa [hf2const t a, sub_self] using hsub
    have hgd : Differentiable ℝ ((fun s => inner ℝ (J s)
        ((FiberBundle.extend F (J s₀)) ((u s).proj))) -
        (fun y => inner ℝ (J' a) ((FiberBundle.extend F (J s₀))
          ((u a).proj)) * y)) := fun z => (hg z).differentiableAt
    have hba := is_const_of_deriv_eq_zero hgd (fun z => (hg z).deriv) b a
    simp only [Pi.sub_apply] at hba
    rw [hf1a, hf1b] at hba
    have hmul : inner ℝ (J' a) ((FiberBundle.extend F (J s₀))
        ((u a).proj)) * (b - a) = 0 := by linear_combination -hba
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr (Ne.symm hab))
  have hf1zero : ∀ t : ℝ, HasDerivAt (fun s => inner ℝ (J s)
      ((FiberBundle.extend F (J s₀)) ((u s).proj))) 0 t := by
    intro t
    simpa [hf2const t a, hC] using (hf1 t)
  have hfs : inner ℝ (J s₀) ((FiberBundle.extend F (J s₀))
      ((u s₀).proj)) = 0 := by
    have hd : Differentiable ℝ (fun s => inner ℝ (J s)
        ((FiberBundle.extend F (J s₀)) ((u s).proj))) :=
      fun z => (hf1zero z).differentiableAt
    have h := is_const_of_deriv_eq_zero hd (fun z => (hf1zero z).deriv) s₀ a
    simpa [hf1a] using h
  have hext : FiberBundle.extend F (J s₀) ((u s₀).proj) = J s₀ :=
    FiberBundle.extend_model_space _ _ _
  have hself : inner ℝ (J s₀) (J s₀) = 0 := by rw [hext] at hfs; exact hfs
  exact hs₀ (inner_self_eq_zero.mp hself)

end Manifold

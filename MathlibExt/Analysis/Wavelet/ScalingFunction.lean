/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import MathlibExt.Analysis.Wavelet.Multiresolution
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Scaling functions of multiresolution approximations

The integer translates of a scaling function form a Hilbert basis of the space at resolution
zero. We orthonormalize the basis supplied by the coordinate isomorphism using the positive
square root of its Gram operator, which commutes with translations.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace MathlibExt.Analysis.Wavelet.MultiresolutionWanted

open MathlibExt.Analysis.Wavelet.Multiresolution

/-- The modulus of a Hilbert space isomorphism has the same action on norms. It commutes with
surjective isometries that also preserve the inner product pulled back by the isomorphism. -/
private theorem exists_modulus {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (e : E ≃L[ℂ] F) :
    ∃ P : E →L[ℂ] E, (∀ x, ‖P x‖ = ‖e x‖) ∧ Function.Surjective P ∧
      ∀ T : E →ₗᵢ[ℂ] E, Function.Surjective T →
        (∀ x y, ⟪e (T x), e (T y)⟫_ℂ = ⟪e x, e y⟫_ℂ) → Commute P T.toContinuousLinearMap := by
  let A := e.toContinuousLinearMap
  let G := A.adjoint ∘L A
  let P := CFC.sqrt G
  have hG : 0 ≤ G := ContinuousLinearMap.nonneg_iff_isPositive.mpr A.isPositive_adjoint_comp_self
  have hsq : P * P = G := CFC.sqrt_mul_sqrt_self G hG
  have hself : P.adjoint = P := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)).adjoint_eq
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x
    calc
      ‖P x‖ = _ := P.apply_norm_eq_sqrt_inner_adjoint_left x
      _ = ‖A x‖ := by
        rw [hself, A.apply_norm_eq_sqrt_inner_adjoint_left]
        rw [show P ∘L P = G from hsq]
  · have hInv : e.symm.toContinuousLinearMap ∘L A = ContinuousLinearMap.id ℂ E := by
      ext x
      exact e.symm_apply_apply x
    have hRight : A.adjoint ∘L e.symm.toContinuousLinearMap.adjoint = .id ℂ E := by
      rw [← ContinuousLinearMap.adjoint_comp, hInv, ContinuousLinearMap.adjoint_id]
    intro x
    let y := e.symm (e.symm.toContinuousLinearMap.adjoint x)
    refine ⟨P y, ?_⟩
    calc
      P (P y) = G y := DFunLike.congr_fun hsq y
      _ = A.adjoint (e (e.symm (e.symm.toContinuousLinearMap.adjoint x))) := rfl
      _ = x := by rw [e.apply_symm_apply]; exact DFunLike.congr_fun hRight x
  · intro T hT hInner
    have hcomm : Commute G T.toContinuousLinearMap := by
      ext x
      apply ext_inner_right ℂ
      intro y
      obtain ⟨z, rfl⟩ := hT y
      change ⟪A.adjoint (A (T x)), T z⟫_ℂ = ⟪T (A.adjoint (A x)), T z⟫_ℂ
      rw [T.inner_map_map, A.adjoint_inner_left, A.adjoint_inner_left]
      exact hInner x z
    exact hcomm.cfcₙ_nnreal NNReal.sqrt

/-- **Scaling function of a multiresolution approximation** (S. Mallat, *Multiresolution
approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989),
Section 2). If `(V_j)` is a multiresolution approximation of `L²(ℝ)`, there is `φ ∈ L²(ℝ)` whose
integer translates `x ↦ φ(x - k)`, `k ∈ ℤ`, form an orthonormal basis of `V_0`: a Hilbert basis
of `V_0` indexed by `ℤ` whose elements are a.e. equal to these translates. -/
theorem exists_scaling_function {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝ), ∃ b : HilbertBasis ℤ ℂ (V 0),
      ∀ k : ℤ, ⇑((b k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] fun x => φ (x - k) := by
  obtain ⟨hClosed, _, _, _, _, hTranslate, e, he⟩ := hV
  let : CompleteSpace (V 0) := (hClosed 0).completeSpace_coe
  let shift (k : ℤ) := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ
    (· - (k : ℝ)) (measurePreserving_sub_right volume (k : ℝ))
  have hShift (k : ℤ) (f : V 0) : shift k f ∈ V 0 := by
    apply hTranslate 0 k _ _ _ f.property
    simp only [neg_zero, zpow_zero, one_mul]
    exact Lp.coeFn_compMeasurePreserving f.val (measurePreserving_sub_right volume (k : ℝ))
  let T (k : ℤ) : V 0 →ₗᵢ[ℂ] V 0 :=
    { ((shift k).toLinearMap.comp (V 0).subtype).codRestrict (V 0) (hShift k) with
      norm_map' := fun f => (shift k).norm_map f.val }
  have hCoord (k : ℤ) (f : V 0) (n : ℤ) : e (T k f) n = e f (n - k) :=
    he k f (T k f) (Lp.coeFn_compMeasurePreserving _ _) n
  obtain ⟨P, hNorm, hOnto, hComm⟩ := exists_modulus e
  let U : lp (fun _ : ℤ => ℂ) 2 →ₗᵢ[ℂ] V 0 :=
    { P.toLinearMap.comp e.symm.toLinearMap with
      norm_map' := fun c => (hNorm (e.symm c)).trans (by rw [e.apply_symm_apply]) }
  let b : HilbertBasis ℤ ℂ (V 0) :=
    ⟨(LinearIsometryEquiv.ofSurjective U (hOnto.comp e.symm.surjective)).symm⟩
  have hb (k : ℤ) : b k = P (e.symm (lp.single 2 k 1)) := by
    rw [← b.repr_symm_single]
    rfl
  refine ⟨(b 0).val, b, fun k => ?_⟩
  have hSurj : Function.Surjective (T k) := by
    intro f
    refine ⟨T (-k) f, e.injective ?_⟩
    ext n
    simp [hCoord]
  have hInner (f g : V 0) : ⟪e (T k f), e (T k g)⟫_ℂ = ⟪e f, e g⟫_ℂ := by
    simp only [lp.inner_eq_tsum, hCoord]
    exact (Equiv.subRight k).tsum_eq (fun n => ⟪e f n, e g n⟫_ℂ)
  have hSingle : T k (e.symm (lp.single 2 0 1)) = e.symm (lp.single 2 k 1) := by
    apply e.injective
    ext n
    simp [hCoord, lp.single_apply, Pi.single_apply, sub_eq_zero, eq_comm]
  have hbShift : b k = T k (b 0) := by
    rw [hb, hb, ← hSingle]
    exact DFunLike.congr_fun (hComm (T k) hSurj hInner).eq _
  rw [hbShift]
  exact Lp.coeFn_compMeasurePreserving _ _

end MathlibExt.Analysis.Wavelet.MultiresolutionWanted

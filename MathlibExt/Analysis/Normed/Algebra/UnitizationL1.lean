/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import MathlibExt.Algebra.Algebra.Unitization.Unital

/-!
# The L¹ unitization of a unital normed algebra

Let 𝕜 be a normed field and A a unital normed 𝕜-algebra, in independent
universes. The L¹ unitization WithLp 1 (Unitization 𝕜 A) is continuously
algebra-equivalent to 𝕜 × A. In scalar/algebra coordinates the map is
(c,a) ↦ (c,c • 1 + a), with inverse (c,b) ↦ (c,b - c • 1).
-/

@[expose] public section

namespace WithLp

noncomputable section

universe u v

/-- For a normed field 𝕜 and unital normed 𝕜-algebra A, the L¹ unitization
is continuously algebra-equivalent to 𝕜 × A. The forward coordinate map is
(c,a) ↦ (c,c • 1 + a), and its inverse is (c,b) ↦ (c,b - c • 1). -/
noncomputable def unitalUnitizationProdContinuousAlgEquiv
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] :
    WithLp 1 (Unitization 𝕜 A) ≃A[𝕜] 𝕜 × A := by
  let eAlg : WithLp 1 (Unitization 𝕜 A) ≃ₐ[𝕜] 𝕜 × A :=
    (WithLp.unitizationAlgEquiv 𝕜).trans
      (Unitization.unitalProdAlgEquiv 𝕜 A)
  refine ContinuousAlgEquiv.mk eAlg ?_ ?_
  · let e : WithLp 1 (Unitization 𝕜 A) ≃ₜ 𝕜 × A :=
      (WithLp.uniformEquiv_unitization_addEquiv_prod 𝕜 A).toHomeomorph.trans
        (WithLp.homeomorphProd 1 𝕜 A)
    have he : Continuous (fun x : WithLp 1 (Unitization 𝕜 A) ↦ e x) :=
      e.continuous
    have hfst : Continuous (fun x : WithLp 1 (Unitization 𝕜 A) ↦ (e x).1) :=
      continuous_fst.comp he
    have hsnd : Continuous (fun x : WithLp 1 (Unitization 𝕜 A) ↦
        (e x).1 • (1 : A) + (e x).2) :=
      (hfst.smul continuous_const).add (continuous_snd.comp he)
    have he_apply (x : WithLp 1 (Unitization 𝕜 A)) :
        e x = ((WithLp.ofLp x).fst, (WithLp.ofLp x).snd) := rfl
    change Continuous (fun x : WithLp 1 (Unitization 𝕜 A) ↦
      Unitization.unitalProdAlgEquiv 𝕜 A (WithLp.unitizationAlgEquiv 𝕜 x))
    simpa only [WithLp.unitizationAlgEquiv_apply,
      Unitization.unitalProdAlgEquiv_apply, he_apply] using hfst.prodMk hsnd
  · let e : WithLp 1 (Unitization 𝕜 A) ≃ₜ 𝕜 × A :=
      (WithLp.uniformEquiv_unitization_addEquiv_prod 𝕜 A).toHomeomorph.trans
        (WithLp.homeomorphProd 1 𝕜 A)
    have hshear : Continuous (fun p : 𝕜 × A ↦
        (p.1, p.2 - p.1 • (1 : A))) :=
      continuous_fst.prodMk
        (continuous_snd.sub (continuous_fst.smul continuous_const))
    have h := e.symm.continuous.comp hshear
    have he_apply (x : WithLp 1 (Unitization 𝕜 A)) :
        e x = ((WithLp.ofLp x).fst, (WithLp.ofLp x).snd) := rfl
    have hpoint (p : 𝕜 × A) :
        e.symm (p.1, p.2 - p.1 • (1 : A)) =
          WithLp.toLp 1
            (Unitization.inl p.1 + Unitization.inr (p.2 - p.1 • (1 : A))) := by
      apply e.injective
      rw [e.apply_symm_apply, he_apply]
      simp [Unitization.inr, Unitization.inl]
    have htarget : Continuous (fun p : 𝕜 × A ↦ WithLp.toLp 1
        (Unitization.inl p.1 + Unitization.inr (p.2 - p.1 • (1 : A)))) := by
      rw [show (fun p : 𝕜 × A ↦ WithLp.toLp 1
        (Unitization.inl p.1 + Unitization.inr (p.2 - p.1 • (1 : A)))) =
        (fun p : 𝕜 × A ↦ e.symm (p.1, p.2 - p.1 • (1 : A))) by
          funext p
          exact (hpoint p).symm]
      exact h
    change Continuous (fun p : 𝕜 × A ↦
      (WithLp.unitizationAlgEquiv 𝕜).symm
        ((Unitization.unitalProdAlgEquiv 𝕜 A).symm p))
    simpa only [Unitization.unitalProdAlgEquiv_symm_apply,
      WithLp.unitizationAlgEquiv_symm_apply] using htarget

/-- Let 𝕜 be a normed field, A a unital normed 𝕜-algebra, and
x : WithLp 1 (Unitization 𝕜 A). The scalar coordinate of the continuous
product equivalence is the scalar coordinate of x. -/
@[simp]
theorem unitalUnitizationProdContinuousAlgEquiv_apply_fst
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (x : WithLp 1 (Unitization 𝕜 A)) :
    (unitalUnitizationProdContinuousAlgEquiv 𝕜 A x).1 =
      (WithLp.ofLp x).fst := by
  change (Unitization.unitalProdAlgEquiv 𝕜 A
    (WithLp.unitizationAlgEquiv 𝕜 x)).1 = _
  rw [Unitization.unitalProdAlgEquiv_apply_fst]
  rfl

/-- Let 𝕜 be a normed field, A a unital normed 𝕜-algebra, and
x : WithLp 1 (Unitization 𝕜 A). If x has coordinates (c,a), its image
under the continuous product equivalence has algebra coordinate c • 1 + a. -/
@[simp]
theorem unitalUnitizationProdContinuousAlgEquiv_apply_snd
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (x : WithLp 1 (Unitization 𝕜 A)) :
    (unitalUnitizationProdContinuousAlgEquiv 𝕜 A x).2 =
      (WithLp.ofLp x).fst • (1 : A) + (WithLp.ofLp x).snd := by
  change (Unitization.unitalProdAlgEquiv 𝕜 A
    (WithLp.unitizationAlgEquiv 𝕜 x)).2 = _
  rw [Unitization.unitalProdAlgEquiv_apply_snd]
  rfl

/-- For a normed field 𝕜, unital normed 𝕜-algebra A, c : 𝕜 and a : A,
the inverse product equivalence sends (c,a) to the L¹ unitization element
inl(c) + inr(a - c • 1). -/
@[simp]
theorem unitalUnitizationProdContinuousAlgEquiv_symm_apply
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (c : 𝕜) (a : A) :
    (unitalUnitizationProdContinuousAlgEquiv 𝕜 A).symm (c, a) =
      WithLp.toLp 1
        (Unitization.inl c + Unitization.inr (a - c • (1 : A))) := by
  change (WithLp.unitizationAlgEquiv 𝕜).symm
    ((Unitization.unitalProdAlgEquiv 𝕜 A).symm (c, a)) = _
  rw [Unitization.unitalProdAlgEquiv_symm_apply,
    WithLp.unitizationAlgEquiv_symm_apply]

/-- For a normed field 𝕜, unital normed 𝕜-algebra A and c : 𝕜,
the scalar algebra-map element of the L¹ unitization is sent to
(c, algebraMap 𝕜 A c) in 𝕜 × A. -/
@[simp]
theorem unitalUnitizationProdContinuousAlgEquiv_algebraMap
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (c : 𝕜) :
    unitalUnitizationProdContinuousAlgEquiv 𝕜 A
        (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A)) c) =
      (c, algebraMap 𝕜 A c) := by
  exact (unitalUnitizationProdContinuousAlgEquiv 𝕜 A).commutes c

/-- For a normed field 𝕜, unital normed 𝕜-algebra A and a : A,
the embedded unitization element inr(a) is sent to (0,a). -/
@[simp]
theorem unitalUnitizationProdContinuousAlgEquiv_inr
    (𝕜 : Type u) (A : Type v)
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    (a : A) :
    unitalUnitizationProdContinuousAlgEquiv 𝕜 A
        (WithLp.toLp 1 (Unitization.inr a : Unitization 𝕜 A)) =
      (0, a) := by
  change Unitization.unitalProdAlgEquiv 𝕜 A (Unitization.inr a) = (0, a)
  exact Unitization.unitalProdAlgEquiv_inr 𝕜 A a

end

end WithLp

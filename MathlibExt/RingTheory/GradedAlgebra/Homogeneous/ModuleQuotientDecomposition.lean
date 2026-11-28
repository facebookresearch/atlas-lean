/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.ModuleQuotient

/-!
# Internal decompositions of homogeneous submodules and quotients

Let S be a graded commutative A-algebra and M = ⨁ₙM_n an internally decomposed graded
S-module, with compatible A-action. For a homogeneous S-submodule H, the inherited pieces H_n
form an internal direct-sum decomposition of H. The n-th component of x ∈ H, viewed in M, is
its ambient component x_n.

The image pieces Q_n = q(M_n) form an internal direct-sum decomposition of Q = M/H.
Decomposition of a quotient class satisfies q(x)_n = q(x_n), independently of the
representative because H is homogeneous. Each decomposition has finite support. The
coefficient, algebra and module universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped DirectSum

universe u v w

namespace HomogeneousSubmodule

variable {A : Type u} [CommRing A]
variable {S : Type v} [CommRing S] [Algebra A S]
variable {M : Type w} [AddCommGroup M]
  [Module A M] [Module S M] [IsScalarTower A S M]

variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M)
  [SetLike.GradedSMul Sgrade Mgrade]
  [DirectSum.Decomposition Mgrade]

private def gradeDirectSumInclusion
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (⨁ n, N.grade Sgrade Mgrade n) →ₗ[A] (⨁ n, Mgrade n) :=
  DirectSum.lmap fun n ↦ N.gradeInclusion Sgrade Mgrade n

private theorem coeLinearMap_gradeDirectSumInclusion
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (DirectSum.coeLinearMap Mgrade).comp
        (gradeDirectSumInclusion Sgrade Mgrade N) =
      ((N.toSubmodule.subtype).restrictScalars A).comp
        (DirectSum.coeLinearMap (N.grade Sgrade Mgrade)) := by
  apply DirectSum.linearMap_ext A
  intro n
  apply LinearMap.ext
  intro x
  rfl

private theorem grade_isInternal
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    DirectSum.IsInternal (N.grade Sgrade Mgrade) := by
  constructor
  · intro x y hxy
    have hxy' : DirectSum.coeLinearMap (N.grade Sgrade Mgrade) x =
        DirectSum.coeLinearMap (N.grade Sgrade Mgrade) y := hxy
    have hincl :
        Function.Injective (gradeDirectSumInclusion Sgrade Mgrade N) :=
      (DirectSum.lmap_injective _).mpr fun n ↦
        N.gradeInclusion_injective Sgrade Mgrade n
    apply hincl
    apply (DirectSum.Decomposition.isInternal Mgrade).injective
    calc
      DirectSum.coeLinearMap Mgrade
          (gradeDirectSumInclusion Sgrade Mgrade N x) =
        ((N.toSubmodule.subtype).restrictScalars A)
          (DirectSum.coeLinearMap (N.grade Sgrade Mgrade) x) :=
        LinearMap.congr_fun
          (coeLinearMap_gradeDirectSumInclusion Sgrade Mgrade N) x
      _ = ((N.toSubmodule.subtype).restrictScalars A)
          (DirectSum.coeLinearMap (N.grade Sgrade Mgrade) y) := by
        rw [hxy']
      _ = DirectSum.coeLinearMap Mgrade
          (gradeDirectSumInclusion Sgrade Mgrade N y) :=
        (LinearMap.congr_fun
          (coeLinearMap_gradeDirectSumInclusion Sgrade Mgrade N) y).symm
  · intro x
    classical
    let d := DirectSum.decompose Mgrade (x : M)
    let y : ⨁ n, N.grade Sgrade Mgrade n :=
      ∑ n ∈ d.support,
        DirectSum.of (fun n ↦ N.grade Sgrade Mgrade n) n
          ⟨⟨(d n : M), N.isHomogeneous n x.2⟩, (d n).2⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change ((DirectSum.coeLinearMap (N.grade Sgrade Mgrade) y :
      N.toSubmodule) : M) = (x : M)
    dsimp only [y]
    rw [map_sum]
    simp only [DirectSum.coeLinearMap_of]
    change N.toSubmodule.subtype
      (∑ n ∈ d.support,
        (⟨(d n : M), N.isHomogeneous n x.2⟩ : N.toSubmodule)) = (x : M)
    rw [map_sum]
    change (∑ n ∈ d.support, (d n : M)) = (x : M)
    dsimp only [d]
    exact DirectSum.sum_support_decompose Mgrade (x : M)

/-- Internal decomposition of a homogeneous submodule.

For a homogeneous H in an internally decomposed graded S-module M, the inherited grades H_n
form an internal direct sum. Its components are the ambient components of elements of H, which
remain in H by homogeneity. -/
@[no_expose]
noncomputable instance gradeDecomposition
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    DirectSum.Decomposition (N.grade Sgrade Mgrade) := by
  exact (grade_isInternal Sgrade Mgrade N).chooseDecomposition

/-- Ambient value of a homogeneous submodule component.

For x ∈ H and any n, decompose x using the inherited grades H_n and then include its n-th
component in M. The result is the n-th ambient component of x under M = ⨁ₙM_n. -/
@[simp]
theorem coe_decompose_grade
    (N : HomogeneousSubmodule Sgrade Mgrade)
    (x : N.toSubmodule) (n : ℕ) :
    ((DirectSum.decompose (N.grade Sgrade Mgrade) x n :
        N.toSubmodule) : M) =
      (DirectSum.decompose Mgrade (x : M) n : M) := by
  have hds : gradeDirectSumInclusion Sgrade Mgrade N
        (DirectSum.decompose (N.grade Sgrade Mgrade) x) =
      DirectSum.decompose Mgrade (x : M) := by
    apply (DirectSum.Decomposition.isInternal Mgrade).injective
    calc
      DirectSum.coeLinearMap Mgrade
          (gradeDirectSumInclusion Sgrade Mgrade N
            (DirectSum.decompose (N.grade Sgrade Mgrade) x)) =
        ((N.toSubmodule.subtype).restrictScalars A)
          (DirectSum.coeLinearMap (N.grade Sgrade Mgrade)
            (DirectSum.decompose (N.grade Sgrade Mgrade) x)) :=
        LinearMap.congr_fun
          (coeLinearMap_gradeDirectSumInclusion Sgrade Mgrade N) _
      _ = (x : M) := by
        rw [show DirectSum.coeLinearMap (N.grade Sgrade Mgrade)
          (DirectSum.decompose (N.grade Sgrade Mgrade) x) = x by
            exact
              (DirectSum.decompose
                (N.grade Sgrade Mgrade)).symm_apply_apply x]
        rfl
      _ = DirectSum.coeLinearMap Mgrade
          (DirectSum.decompose Mgrade (x : M)) :=
        ((DirectSum.decompose Mgrade).symm_apply_apply (x : M)).symm
  have hn := congrArg (fun z ↦ z n) hds
  change ((N.gradeInclusion Sgrade Mgrade n
    (DirectSum.decompose (N.grade Sgrade Mgrade) x n) : Mgrade n) : M) = _
  exact congrArg (fun z : Mgrade n ↦ (z : M))
    (by simpa [gradeDirectSumInclusion] using hn)

private def quotientDirectSumMap
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (⨁ n, Mgrade n) →ₗ[A]
      (⨁ n, N.quotientGrade Sgrade Mgrade n) :=
  DirectSum.lmap fun n ↦ N.gradeQuotient Sgrade Mgrade n

private def quotientDecomposeAux
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    M →ₗ[A] (⨁ n, N.quotientGrade Sgrade Mgrade n) :=
  (quotientDirectSumMap Sgrade Mgrade N).comp
    (DirectSum.decomposeLinearEquiv Mgrade).toLinearMap

private theorem quotientDecomposeAux_eq_zero_of_mem
    (N : HomogeneousSubmodule Sgrade Mgrade) (x : M)
    (hx : x ∈ N.toSubmodule) :
    quotientDecomposeAux Sgrade Mgrade N x = 0 := by
  apply DFinsupp.ext
  intro n
  change N.gradeQuotient Sgrade Mgrade n
      (DirectSum.decompose Mgrade x n) = 0
  apply Subtype.ext
  rw [N.gradeQuotient_apply]
  exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr
    (N.isHomogeneous n hx)

private noncomputable def quotientDecompose
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (M ⧸ N.toSubmodule) →ₗ[A]
      (⨁ n, N.quotientGrade Sgrade Mgrade n) :=
  { QuotientAddGroup.lift N.toSubmodule.toAddSubgroup
      (quotientDecomposeAux Sgrade Mgrade N).toAddMonoidHom
      (fun x hx ↦
        quotientDecomposeAux_eq_zero_of_mem Sgrade Mgrade N x hx) with
    map_smul' := by
      rintro a ⟨x⟩
      exact (quotientDecomposeAux Sgrade Mgrade N).map_smul a x }

private theorem quotientDecompose_mk
    (N : HomogeneousSubmodule Sgrade Mgrade) (x : M) :
    quotientDecompose Sgrade Mgrade N (N.toSubmodule.mkQ x) =
      quotientDirectSumMap Sgrade Mgrade N
        (DirectSum.decompose Mgrade x) :=
  rfl

private theorem coeLinearMap_quotientDirectSumMap
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (DirectSum.coeLinearMap (N.quotientGrade Sgrade Mgrade)).comp
        (quotientDirectSumMap Sgrade Mgrade N) =
      (N.toSubmodule.mkQ.restrictScalars A).comp
        (DirectSum.coeLinearMap Mgrade) := by
  apply DirectSum.linearMap_ext A
  intro n
  apply LinearMap.ext
  intro x
  rfl

private theorem quotientDecompose_left_inv
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (DirectSum.coeLinearMap (N.quotientGrade Sgrade Mgrade)).comp
        (quotientDecompose Sgrade Mgrade N) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := N.toSubmodule.mkQ_surjective q
  change DirectSum.coeLinearMap (N.quotientGrade Sgrade Mgrade)
      (quotientDecompose Sgrade Mgrade N (N.toSubmodule.mkQ x)) =
    N.toSubmodule.mkQ x
  rw [quotientDecompose_mk]
  calc
    DirectSum.coeLinearMap (N.quotientGrade Sgrade Mgrade)
        (quotientDirectSumMap Sgrade Mgrade N
          (DirectSum.decompose Mgrade x)) =
      (N.toSubmodule.mkQ.restrictScalars A)
        (DirectSum.coeLinearMap Mgrade (DirectSum.decompose Mgrade x)) :=
      LinearMap.congr_fun
        (coeLinearMap_quotientDirectSumMap Sgrade Mgrade N) _
    _ = N.toSubmodule.mkQ x := by
      rw [show DirectSum.coeLinearMap Mgrade
        (DirectSum.decompose Mgrade x) = x by
          exact (DirectSum.decompose Mgrade).symm_apply_apply x]
      rfl

private theorem quotientDecompose_right_inv
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    (quotientDecompose Sgrade Mgrade N).comp
        (DirectSum.coeLinearMap (N.quotientGrade Sgrade Mgrade)) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext A
  intro n
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := N.gradeQuotient_surjective Sgrade Mgrade n q
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    DirectSum.coeLinearMap_lof]
  change quotientDecompose Sgrade Mgrade N
      (N.toSubmodule.mkQ (x : M)) =
    DirectSum.lof A ℕ (fun n ↦ N.quotientGrade Sgrade Mgrade n) n
      (N.gradeQuotient Sgrade Mgrade n x)
  rw [quotientDecompose_mk,
    show DirectSum.decompose Mgrade (x : M) =
      DirectSum.of (fun n ↦ Mgrade n) n x by
        exact DirectSum.decompose_coe Mgrade x]
  rw [show quotientDirectSumMap Sgrade Mgrade N =
      DirectSum.lmap (fun n ↦ N.gradeQuotient Sgrade Mgrade n) by rfl,
    DirectSum.lmap_of]
  rfl

/-- Internal decomposition of a homogeneous quotient.

For homogeneous H ⊆ M with M internally decomposed, the image grades Q_n = q(M_n) give an
internal direct-sum decomposition of M/H. Its decomposition map sends q(x) to the finite
family of classes q(x_n), which is well defined by homogeneity of H. -/
@[no_expose]
noncomputable instance quotientGradeDecomposition
    (N : HomogeneousSubmodule Sgrade Mgrade) :
    DirectSum.Decomposition (N.quotientGrade Sgrade Mgrade) := by
  exact DirectSum.Decomposition.ofLinearMap
    (N.quotientGrade Sgrade Mgrade)
    (quotientDecompose Sgrade Mgrade N)
    (quotientDecompose_left_inv Sgrade Mgrade N)
    (quotientDecompose_right_inv Sgrade Mgrade N)

/-- Component formula for a canonical quotient representative.

For x ∈ M and n : ℕ, the n-th component of q(x) in the image-grade decomposition of M/H,
viewed as a quotient class, equals q(x_n), where x_n is the ambient degree-n component of x. -/
theorem decompose_quotient_mk
    (N : HomogeneousSubmodule Sgrade Mgrade) (x : M) (n : ℕ) :
    ((DirectSum.decompose (N.quotientGrade Sgrade Mgrade)
        (N.toSubmodule.mkQ x) n : N.quotientGrade Sgrade Mgrade n) :
      M ⧸ N.toSubmodule) =
      N.toSubmodule.mkQ (DirectSum.decompose Mgrade x n : M) := by
  change ((quotientDecompose Sgrade Mgrade N
      (N.toSubmodule.mkQ x) n : N.quotientGrade Sgrade Mgrade n) :
    M ⧸ N.toSubmodule) = _
  rw [quotientDecompose_mk]
  rfl

end HomogeneousSubmodule

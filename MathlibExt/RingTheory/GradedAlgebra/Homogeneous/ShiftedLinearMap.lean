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

public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.ModuleQuotientDecomposition

/-!
# Homogeneous linear maps with nonnegative degree shifts

Let A,S be semirings, M,N semimodules with both scalar actions, and M_n,N_n families of
A-submodules. An S-linear map f has degree d : ℕ when f(M_n) ⊆ N_{d+n} for every n.
Composition adds degrees in outer-first order e+d, and the q-th power of a degree-d
endomorphism has degree q·d.

If the component families form internal direct-sum decompositions, (f(x))_{d+n} = f(x_n),
while every component (f(x))_k for k < d is zero. The kernel and range are consequently stable
under their respective homogeneous component projections. For a graded algebra S over a
commutative semiring A, a compatible graded action on the relevant family bundles these as
homogeneous S-submodules.

Multiplication by a scalar s in degree d is also a degree-d linear map whenever the scalar and
module families satisfy the graded-action law. The coefficient, algebra and module universes
remain independent.
-/

@[expose] public section

set_option autoImplicit false

namespace GradedModule

universe uA uS uM uN uP

section Raw

variable {A : Type uA} [Semiring A]
variable {S : Type uS} [Semiring S]
variable {M : Type uM} [AddCommMonoid M] [Module A M] [Module S M]
variable {N : Type uN} [AddCommMonoid N] [Module A N] [Module S N]

/-- Degree-shift condition on a linear map.

For families M_n,N_n of A-submodules, a natural d and an S-linear map f : M → N,
IsHomogeneousOfDegree means f(M_n) ⊆ N_{d+n} for every n. At this level A,S are semirings and
M,N carry both actions; an internal decomposition is not required. -/
def IsHomogeneousOfDegree
    (Mgrade : ℕ → Submodule A M) (Ngrade : ℕ → Submodule A N)
    (d : ℕ) (f : M →ₗ[S] N) : Prop :=
  ∀ n, Set.MapsTo f (Mgrade n) (Ngrade (d + n))

namespace IsHomogeneousOfDegree

variable {Mgrade : ℕ → Submodule A M} {Ngrade : ℕ → Submodule A N}

/-- Homogeneity of the zero map in every degree.

For any A-submodule families M_n,N_n and d : ℕ, the zero S-linear map M → N is homogeneous of
degree d, since zero belongs to every target piece. -/
theorem zero (d : ℕ) :
    IsHomogeneousOfDegree Mgrade Ngrade d (0 : M →ₗ[S] N) := by
  intro n x hx
  change (0 : N) ∈ Ngrade (d + n)
  exact (Ngrade (d + n)).zero_mem

/-- Degree-zero homogeneity of the identity.

For any A-submodule family M_n on an S-semimodule M, the identity S-linear map is homogeneous
of degree zero. -/
theorem id :
    IsHomogeneousOfDegree Mgrade Mgrade 0
      (LinearMap.id (R := S) (M := M)) := by
  intro n x hx
  simpa using hx

variable {P : Type uP} [AddCommMonoid P] [Module A P] [Module S P]
variable {Pgrade : ℕ → Submodule A P}

/-- Outer-first degree formula for composed homogeneous maps.

If f : M → N has degree d and g : N → P has degree e relative to the given A-submodule
families, g ∘ f has degree e+d. A degree-n input is sent first to degree d+n and then to
degree e+(d+n). -/
theorem comp {d e : ℕ} {f : M →ₗ[S] N} {g : N →ₗ[S] P}
    (hg : IsHomogeneousOfDegree Ngrade Pgrade e g)
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    IsHomogeneousOfDegree Mgrade Pgrade (e + d) (g.comp f) := by
  intro n x hx
  simpa [add_assoc] using hg (d + n) (hf n hx)

/-- Degree of a power of a homogeneous endomorphism.

If the S-linear endomorphism f of M has degree d relative to M_n, then f^q has degree q·d for
every natural q, including the identity at q = 0. -/
theorem pow {d : ℕ} {f : Module.End S M}
    (hf : IsHomogeneousOfDegree Mgrade Mgrade d f) (q : ℕ) :
    IsHomogeneousOfDegree Mgrade Mgrade (q * d) (f ^ q) := by
  induction q with
  | zero =>
      rw [pow_zero, zero_mul]
      intro n x hx
      simpa only [Module.End.one_apply, zero_add] using hx
  | succ q ih =>
      simpa only [pow_succ, Module.End.mul_eq_comp, Nat.succ_mul] using
        comp (Mgrade := Mgrade) (Ngrade := Mgrade) (Pgrade := Mgrade) ih hf

section Components

variable [DirectSum.Decomposition Mgrade]
variable [DirectSum.Decomposition Ngrade]

/-- Shifted component formula for a homogeneous map.

Suppose M_n,N_n form internal direct-sum decompositions and f : M →ₗ[S] N has degree d. For
every x and n, the degree-d+n component of f(x), viewed in N, is f(x_n), where x_n is the
degree-n component of x. -/
theorem coe_decompose_apply_add {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) (x : M) (n : ℕ) :
    (DirectSum.decompose Ngrade (f x) (d + n) : N) =
      f (DirectSum.decompose Mgrade x n : M) := by
  induction x using DirectSum.Decomposition.inductionOn Mgrade with
  | zero => simp
  | @homogeneous i x =>
      by_cases hin : i = n
      · subst i
        rw [DirectSum.decompose_of_mem_same Mgrade x.property,
          DirectSum.decompose_of_mem_same Ngrade (hf n x.property)]
      · have hdin : d + i ≠ d + n := fun h ↦ hin (Nat.add_left_cancel h)
        rw [DirectSum.decompose_of_mem_ne Mgrade x.property hin,
          DirectSum.decompose_of_mem_ne Ngrade (hf i x.property) hdin,
          map_zero]
  | add x y hx hy =>
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
        Submodule.coe_add, hx, hy]

/-- Vanishing of image components below the degree shift.

For an S-linear degree-d map between internally decomposed A-submodule families, every
component of f(x) at degree k < d is zero. All homogeneous input components map to degrees
d+n. -/
theorem coe_decompose_apply_eq_zero_of_lt {d k : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) (x : M) (hk : k < d) :
    (DirectSum.decompose Ngrade (f x) k : N) = 0 := by
  induction x using DirectSum.Decomposition.inductionOn Mgrade with
  | zero => simp
  | @homogeneous i x =>
      have hki : d + i ≠ k :=
        (Nat.ne_of_lt (hk.trans_le (Nat.le_add_right d i))).symm
      exact DirectSum.decompose_of_mem_ne Ngrade (hf i x.property) hki
  | add x y hx hy =>
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
        Submodule.coe_add, hx, hy, add_zero]

/-- Homogeneous kernel of a degree-shifting map.

For a degree-d S-linear map f between internally decomposed families, Ker(f) is closed under
each source component projection. The shifted component identity sends a component of an
element of Ker(f) to a component of zero. -/
theorem isHomogeneous_ker {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    (LinearMap.ker f).IsHomogeneous Mgrade := by
  intro n x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hf.coe_decompose_apply_add x n, hx]
  simp

/-- Homogeneous range of a degree-shifting map.

For a degree-d S-linear map between internally decomposed families, Im(f) is closed under
target component projections. Components below d vanish; a component at d+n is f(x_n) for a
preimage x. -/
theorem isHomogeneous_range {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    (LinearMap.range f).IsHomogeneous Ngrade := by
  intro k y hy
  obtain ⟨x, rfl⟩ := hy
  by_cases hk : k < d
  · rw [hf.coe_decompose_apply_eq_zero_of_lt x hk]
    exact (LinearMap.range f).zero_mem
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hk)
    rw [hf.coe_decompose_apply_add x n]
    exact ⟨_, rfl⟩

end Components

end IsHomogeneousOfDegree

end Raw

section Bundles

variable {A : Type uA} [CommSemiring A]
variable {S : Type uS} [Semiring S] [Algebra A S]
variable {M : Type uM} [AddCommMonoid M] [Module A M] [Module S M]
variable {N : Type uN} [AddCommMonoid N] [Module A N] [Module S N]
variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M) [DirectSum.Decomposition Mgrade]
variable (Ngrade : ℕ → Submodule A N) [DirectSum.Decomposition Ngrade]

namespace IsHomogeneousOfDegree

/-- Bundled homogeneous kernel for a graded scalar action.

Let S be a graded algebra over a commutative semiring A and M_n,N_n internally decomposed
families. If M_n is compatible with the graded S-action and f : M →ₗ[S] N has degree d, its
kernel defines a HomogeneousSubmodule of M with underlying S-submodule Ker(f). -/
def kerHomogeneousSubmodule [SetLike.GradedSMul Sgrade Mgrade]
    {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    HomogeneousSubmodule Sgrade Mgrade where
  toSubmodule := LinearMap.ker f
  is_homogeneous' := hf.isHomogeneous_ker

/-- Bundled homogeneous range for a graded scalar action.

Let S be a graded algebra over a commutative semiring A and M_n,N_n internally decomposed
families. If N_n is compatible with the graded S-action and f : M →ₗ[S] N has degree d, its
range defines a HomogeneousSubmodule of N with underlying S-submodule Im(f). -/
def rangeHomogeneousSubmodule [SetLike.GradedSMul Sgrade Ngrade]
    {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    HomogeneousSubmodule Sgrade Ngrade where
  toSubmodule := LinearMap.range f
  is_homogeneous' := hf.isHomogeneous_range

end IsHomogeneousOfDegree

end Bundles

section ScalarMultiplication

variable {A : Type uA} [Semiring A]
variable {S : Type uS} [CommSemiring S] [Module A S]
variable {M : Type uM} [AddCommMonoid M] [Module A M] [Module S M]
variable (Sgrade : ℕ → Submodule A S)
variable (Mgrade : ℕ → Submodule A M) [SetLike.GradedSMul Sgrade Mgrade]

namespace IsHomogeneousOfDegree

/-- Degree of multiplication by a homogeneous scalar.

Let S be a commutative semiring, with scalar and module A-submodule families satisfying S_i •
M_j ⊆ M_{i+j}. For s ∈ S_d, the S-linear scalar multiplication map x ↦ s • x is homogeneous of
degree d. This statement uses the graded-action law without requiring internal decompositions. -/
theorem lsmul {d : ℕ} {s : S} (hs : s ∈ Sgrade d) :
    IsHomogeneousOfDegree Mgrade Mgrade d (LinearMap.lsmul S M s) := by
  intro n x hx
  change s • x ∈ Mgrade (d + n)
  exact SetLike.GradedSMul.smul_mem hs hx

end IsHomogeneousOfDegree

end ScalarMultiplication

end GradedModule

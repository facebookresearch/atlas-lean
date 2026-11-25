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
# Degree-shifting linear maps of graded modules

A linear map is homogeneous of degree `d` when it sends the component of
degree `n` into the component of degree `d + n`.  Such a map commutes with
decomposition after shifting the target coordinate; all target coordinates
below the shift vanish.  Consequently its kernel and range are homogeneous
submodules.

This file is neutral graded-module infrastructure.  It proves no quotient
functoriality, stabilization, Hilbert--Serre polynomiality, or
associated-graded injectivity statement.

## Main declarations

* `GradedModule.IsHomogeneousOfDegree`
* `GradedModule.IsHomogeneousOfDegree.coe_decompose_apply_add`
* `GradedModule.IsHomogeneousOfDegree.coe_decompose_apply_eq_zero_of_lt`
* `GradedModule.IsHomogeneousOfDegree.kerHomogeneousSubmodule`
* `GradedModule.IsHomogeneousOfDegree.rangeHomogeneousSubmodule`
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

/-- A linear map is homogeneous of degree `d` when it maps degree `n` into
degree `d + n`. -/
def IsHomogeneousOfDegree
    (Mgrade : ℕ → Submodule A M) (Ngrade : ℕ → Submodule A N)
    (d : ℕ) (f : M →ₗ[S] N) : Prop :=
  ∀ n, Set.MapsTo f (Mgrade n) (Ngrade (d + n))

namespace IsHomogeneousOfDegree

variable {Mgrade : ℕ → Submodule A M} {Ngrade : ℕ → Submodule A N}

/-- The zero map is homogeneous of every degree. -/
theorem zero (d : ℕ) :
    IsHomogeneousOfDegree Mgrade Ngrade d (0 : M →ₗ[S] N) := by
  intro n x hx
  change (0 : N) ∈ Ngrade (d + n)
  exact (Ngrade (d + n)).zero_mem

/-- The identity map is homogeneous of degree zero. -/
theorem id :
    IsHomogeneousOfDegree Mgrade Mgrade 0
      (LinearMap.id (R := S) (M := M)) := by
  intro n x hx
  simpa using hx

variable {P : Type uP} [AddCommMonoid P] [Module A P] [Module S P]
variable {Pgrade : ℕ → Submodule A P}

/-- Composition adds degrees in outer-first order. -/
theorem comp {d e : ℕ} {f : M →ₗ[S] N} {g : N →ₗ[S] P}
    (hg : IsHomogeneousOfDegree Ngrade Pgrade e g)
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    IsHomogeneousOfDegree Mgrade Pgrade (e + d) (g.comp f) := by
  intro n x hx
  simpa [add_assoc] using hg (d + n) (hf n hx)

/-- The `q`-th power of a degree-`d` endomorphism has degree `q * d`. -/
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

/-- The degree-`d+n` component of the image is the image of the degree-`n`
component. -/
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

/-- Every component of an image strictly below the degree shift is zero. -/
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

/-- The kernel of a homogeneous degree-shifting map is homogeneous. -/
theorem isHomogeneous_ker {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    (LinearMap.ker f).IsHomogeneous Mgrade := by
  intro n x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hf.coe_decompose_apply_add x n, hx]
  simp

/-- The range of a homogeneous degree-shifting map is homogeneous. -/
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

/-- The kernel of a homogeneous degree-shifting map, bundled as a homogeneous
submodule. -/
def kerHomogeneousSubmodule [SetLike.GradedSMul Sgrade Mgrade]
    {d : ℕ} {f : M →ₗ[S] N}
    (hf : IsHomogeneousOfDegree Mgrade Ngrade d f) :
    HomogeneousSubmodule Sgrade Mgrade where
  toSubmodule := LinearMap.ker f
  is_homogeneous' := hf.isHomogeneous_ker

/-- The range of a homogeneous degree-shifting map, bundled as a homogeneous
submodule. -/
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

/-- Multiplication by a homogeneous scalar is a homogeneous linear map of the
same degree. -/
theorem lsmul {d : ℕ} {s : S} (hs : s ∈ Sgrade d) :
    IsHomogeneousOfDegree Mgrade Mgrade d (LinearMap.lsmul S M s) := by
  intro n x hx
  change s • x ∈ Mgrade (d + n)
  exact SetLike.GradedSMul.smul_mem hs hx

end IsHomogeneousOfDegree

end ScalarMultiplication

end GradedModule

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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Filtration
public import Mathlib.Tactic.Abel

/-!
# The augmentation kernel is the span of generator-ended products

Let R be a commutative ring, L an R-Lie algebra and U = U_R(L), with
scalar augmentation ε : U → R. The R-submodule
J = span_R{u ι(x) | u ∈ U, x ∈ L}
is stable under left multiplication by U.

Every u ∈ U satisfies u−algebraMap(ε(u)) ∈ J. Since ε kills
generator-ended products, it follows that ker_R(ε) = J.
This identifies the augmentation kernel inside U as an R-submodule
and applies to arbitrary Lie algebras over R, with independent
scalar and Lie-carrier worlds.
-/

@[expose] public section

universe u v

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- For a commutative ring R, an R-Lie algebra L and
U = U_R(L), the augmentation submodule is
span_R{u ι(x) | u ∈ U, x ∈ L}.
It is an R-submodule of U, with the Lie generator on the right
of each displayed product. -/
def augmentationSubmodule : Submodule R U :=
  Submodule.span R (Set.range (fun ux : U × L => ux.1 * ι R ux.2))

theorem mul_ι_mem_augmentationSubmodule (u : U) (x : L) :
    u * ι R x ∈ augmentationSubmodule R L :=
  Submodule.subset_span (Set.mem_range_self (u, x))

theorem mul_mem_augmentationSubmodule (a : U) {u : U}
    (hu : u ∈ augmentationSubmodule R L) : a * u ∈ augmentationSubmodule R L := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨⟨v, x⟩, rfl⟩ := hu
      rw [← mul_assoc]
      exact mul_ι_mem_augmentationSubmodule R L (a * v) x
  | zero => rw [mul_zero]; exact (augmentationSubmodule R L).zero_mem
  | add u v hu hv ihu ihv =>
      rw [mul_add]
      exact (augmentationSubmodule R L).add_mem ihu ihv
  | smul r u hu ih =>
      rw [mul_smul_comm]
      exact (augmentationSubmodule R L).smul_mem r ih

theorem augmentationSubmodule_le_ker :
    augmentationSubmodule R L ≤ LinearMap.ker (augmentation R L).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro u ⟨⟨v, x⟩, rfl⟩
  change augmentation R L (v * ι R x) = 0
  rw [map_mul, augmentation_ι, mul_zero]

/-- For a commutative ring R, an R-Lie algebra L and u ∈ U_R(L),
the element u−algebraMap(ε_L(u)) belongs to
span_R{v ι(x) | v ∈ U_R(L), x ∈ L}.
Here ε_L is the scalar augmentation annihilating every Lie generator. -/
theorem sub_algebraMap_augmentation_mem (u : U) :
    u - algebraMap R U (augmentation R L u) ∈ augmentationSubmodule R L := by
  induction u using UniversalEnvelopingAlgebra.induction R L with
  | algebraMap r =>
      have hr : augmentation R L (algebraMap R U r) = r := by
        simpa using (augmentation R L).commutes r
      rw [hr, sub_self]
      exact (augmentationSubmodule R L).zero_mem
  | ι x =>
      rw [augmentation_ι, map_zero, sub_zero]
      simpa only [one_mul] using mul_ι_mem_augmentationSubmodule R L 1 x
  | mul u v hu hv =>
      rw [map_mul]
      have hdecomp : u * v - algebraMap R U (augmentation R L u * augmentation R L v) =
          u * (v - algebraMap R U (augmentation R L v)) +
            (u - algebraMap R U (augmentation R L u)) * algebraMap R U (augmentation R L v) := by
        rw [map_mul, mul_sub, sub_mul]
        abel
      rw [hdecomp]
      apply (augmentationSubmodule R L).add_mem
      · exact mul_mem_augmentationSubmodule R L u hv
      · simpa only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] using
          (augmentationSubmodule R L).smul_mem (augmentation R L v) hu
  | add u v hu hv =>
      rw [map_add, map_add, add_sub_add_comm]
      exact (augmentationSubmodule R L).add_mem hu hv

/-- For a commutative ring R and an R-Lie algebra L, the kernel
of ε_L : U_R(L) → R as an R-linear map is
span_R{u ι(x) | u ∈ U_R(L), x ∈ L}.
The statement concerns the enveloping algebra itself and does not
require a basis of L. -/
theorem augmentation_ker_eq_submodule :
    LinearMap.ker (augmentation R L).toLinearMap = augmentationSubmodule R L := by
  apply le_antisymm
  · intro u hu
    change augmentation R L u = 0 at hu
    simpa only [hu, map_zero, sub_zero] using sub_algebraMap_augmentation_mem R L u
  · exact augmentationSubmodule_le_ker R L

end UniversalEnvelopingAlgebra

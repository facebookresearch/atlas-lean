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

public import MathlibExt.Analysis.CStarAlgebra.GNS.UnitizationComparison
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The kernel of the GNS coefficient map

For a positive complex functional on a possibly nonunital C-star algebra,
the actual coefficient map into its GNS completion vanishes exactly on
the quadratic null set. This kernel is closed in the algebra norm and
stable under left multiplication. The zero functional has the whole
algebra as its kernel. No normalization or nonzero assumption is needed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

universe uA
variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
For every `a : A`, its coefficient in `tau`'s actual GNS completion is zero exactly
when `tau (star a * a) = 0`. -/
theorem toGNS_eq_zero_iff (tau : A →ₚ[ℂ] ℂ) (a : A) :
    tau.toGNS a = 0 ↔ tau (star a * a) = 0 := by
  constructor
  · intro h
    have hg := (tau.toGNS_inner a a).symm
    simpa only [h, inner_zero_left] using hg
  · intro h
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [tau.toGNS_inner]
    exact h

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
An element `a : A` belongs to the complex linear kernel of the actual GNS coefficient
map exactly when `tau (star a * a) = 0`. -/
@[simp]
theorem mem_ker_toGNS (tau : A →ₚ[ℂ] ℂ) (a : A) :
    a ∈ tau.toGNS.ker ↔ tau (star a * a) = 0 :=
  toGNS_eq_zero_iff tau a

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
The kernel of its actual GNS coefficient map is closed in the original C*-algebra
norm topology on `A`. -/
theorem isClosed_ker_toGNS (tau : A →ₚ[ℂ] ℂ) :
    IsClosed ((tau.toGNS.ker : Submodule ℂ A) : Set A) := by
  have hcarrier : ((tau.toGNS.ker : Submodule ℂ A) : Set A) =
      {a : A | tau (star a * a) = 0} := by
    ext a
    exact toGNS_eq_zero_iff tau a
  rw [hcarrier]
  exact isClosed_eq ((map_continuous tau).comp (continuous_star.mul continuous_id)) continuous_const

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
If `x : A` belongs to the kernel of the actual GNS coefficient map, then `a * x`
belongs to that kernel for every `a : A`. -/
theorem mul_mem_ker_toGNS (tau : A →ₚ[ℂ] ℂ) (a : A) {x : A}
    (hx : x ∈ tau.toGNS.ker) : a * x ∈ tau.toGNS.ker := by
  change tau.toGNS x = 0 at hx
  change tau.toGNS (a * x) = 0
  rw [← tau.gnsNonUnitalStarAlgHom_toGNS a x, hx, map_zero]

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
For the zero positive complex-linear functional `A → ℂ`, the actual GNS coefficient
kernel is the full complex submodule `A`, represented by `⊤ : Submodule ℂ A`. -/
@[simp]
theorem ker_toGNS_zero :
    (0 : A →ₚ[ℂ] ℂ).toGNS.ker = ⊤ := by
  ext a
  simp only [mem_ker_toGNS, zero_apply, Submodule.mem_top]

end PositiveLinearMap

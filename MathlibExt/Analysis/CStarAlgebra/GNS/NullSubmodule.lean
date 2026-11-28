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

public import MathlibExt.Analysis.CStarAlgebra.GNS.NullKernel
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The actual closed GNS null submodule

The coefficient kernel of an arbitrary positive complex functional is a
closed submodule in the original C-star algebra norm topology. It is stable
under ambient left multiplication. This construction uses the stock
`ClosedSubmodule` carrier and includes the zero functional and zero or
nonunital algebras without a normalization premise.

The quadratic-null set is a closed left ideal. For the GNS construction, see
Gerard J. Murphy, *C*-Algebras and Operator Theory*, Chapter 3,
"Ideals and Positive Functionals".
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
open scoped ComplexOrder InnerProductSpace

namespace PositiveLinearMap

universe uA
variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
Construct its actual GNS coefficient kernel as a stock `ClosedSubmodule ℂ A`, closed
in the original C*-algebra norm topology. -/
def gnsNullSubmodule (tau : A →ₚ[ℂ] ℂ) : ClosedSubmodule ℂ A where
  toSubmodule := tau.toGNS.ker
  isClosed' := isClosed_ker_toGNS tau

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
The underlying complex submodule of its actual closed GNS null submodule is exactly
the linear kernel `tau.toGNS.ker`. -/
@[simp]
theorem gnsNullSubmodule_toSubmodule (tau : A →ₚ[ℂ] ℂ) :
    (gnsNullSubmodule tau).toSubmodule = tau.toGNS.ker := rfl

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
An element `a : A` belongs to its actual closed GNS null submodule exactly when
`tau (star a * a) = 0`. -/
@[simp]
theorem mem_gnsNullSubmodule (tau : A →ₚ[ℂ] ℂ) (a : A) :
    a ∈ gnsNullSubmodule tau ↔ tau (star a * a) = 0 :=
  mem_ker_toGNS tau a

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
Let `tau : A → ℂ` be a positive complex-linear functional, possibly zero.
If `x : A` belongs to its actual closed GNS null submodule, then `a * x` belongs to
the same submodule for every `a : A`. -/
theorem mul_mem_gnsNullSubmodule (tau : A →ₚ[ℂ] ℂ) (a : A) {x : A}
    (hx : x ∈ gnsNullSubmodule tau) : a * x ∈ gnsNullSubmodule tau :=
  mul_mem_ker_toGNS tau a hx

/-- Let `A` be a possibly nonunital complex C*-algebra, including the zero algebra, with a
compatible partial order (`PartialOrder A`, `StarOrderedRing A`).
The actual closed GNS null submodule of the zero positive complex-linear functional
`A → ℂ` is `⊤ : ClosedSubmodule ℂ A`, in the original C*-algebra norm topology. -/
@[simp]
theorem gnsNullSubmodule_zero :
    gnsNullSubmodule (0 : A →ₚ[ℂ] ℂ) = ⊤ := by
  apply ClosedSubmodule.toSubmodule_injective
  change (0 : A →ₚ[ℂ] ℂ).toGNS.ker = (⊤ : Submodule ℂ A)
  exact ker_toGNS_zero

end PositiveLinearMap

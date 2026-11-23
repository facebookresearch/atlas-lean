/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Edgewise
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.CategoryTheory.SegalSubdivision.Basic

/-!
# The Segal subdivision category

The Segal subdivision (also called the twisted-arrow category) of `C` is
Mathlib's category of elements of the hom functor.  Thus an object is an
arrow `a ⟶ b`, while a morphism from `a ⟶ b` to `a' ⟶ b'` consists
of arrows `a' ⟶ a` and `b ⟶ b'` making the evident composite equal to
`a' ⟶ b'`.

Classically, its nerve is the twisted edgewise subdivision of `nerve C`. In
degree `n`, a chain of commuting squares is sent to the composable string

```text
aₙ ⟶ ⋯ ⟶ a₀ ⟶ b₀ ⟶ ⋯ ⟶ bₙ.
```

This file packages the carrier and endpoint functors without reproducing the
category-of-elements laws. It also proves the degree-zero instance of the
edgewise comparison and checks its target orientation: the target functor
selects `b`, exactly as `SSet.esdComparison` selects the target of a
one-simplex.

The all-degree simplicial isomorphism requires a reusable double-ended
join/split construction for `ComposableArrows`; it is deliberately not
asserted by this packet. No realization weak-equivalence theorem for the
target functor is claimed here.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory

namespace SegalSubdivision

variable (C : Type u) [Category.{v} C]

/-- In degree zero, the nerve of the Segal subdivision is the set of arrows
of `C`, which is also degree zero of the edgewise subdivision. -/
noncomputable def nerveZeroEquiv :
    (nerve (SegalSubdivision C)).obj (op ⦋0⦌) ≃
      (SSet.esd.obj (nerve C)).obj (op ⦋0⦌) where
  toFun Z := ComposableArrows.mk₁ Z.left.val
  invFun F := ComposableArrows.mk₀ (mk C F.hom)
  left_inv Z := by
    obtain ⟨z, rfl⟩ := ComposableArrows.mk₀_surjective Z
    obtain ⟨X, Y, f, rfl⟩ := mk_surjective C z
    rfl
  right_inv F := by
    obtain ⟨X, Y, f, rfl⟩ := ComposableArrows.mk₁_surjective F
    rfl

@[simp]
theorem nerveZeroEquiv_mk {X Y : C} (f : X ⟶ Y) :
    (show (nerve (SegalSubdivision C)).obj (op ⦋0⦌) ≃ (nerve C).obj (op ⦋1⦌)
      from nerveZeroEquiv C) (ComposableArrows.mk₀ (mk C f)) =
      ComposableArrows.mk₁ f :=
  rfl

/-- The degree-zero target selected by the Segal-subdivision projection is
the target selected by the edgewise comparison. -/
theorem nerveZeroEquiv_target (Z : (nerve (SegalSubdivision C)).obj (op ⦋0⦌)) :
    (SSet.esdComparison.app (nerve C)).app (op ⦋0⦌)
        (nerveZeroEquiv C Z) =
      (nerveMapCross (target C)).app (op ⦋0⦌) Z := by
  obtain ⟨z, rfl⟩ := ComposableArrows.mk₀_surjective Z
  obtain ⟨X, Y, f, rfl⟩ := mk_surjective C z
  apply ComposableArrows.ext₀
  rfl

end SegalSubdivision

end CategoryTheory

end

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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneMap
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictLowDegree
public import MathlibExt.RepresentationTheory.Rep.ZModRestrictTensor

/-!
# Scalar restriction and the degree-`(1, 1)` cup product

Restriction of coefficients from `ZMod n` to `ℤ` preserves the explicit
degree-one and degree-two cocycles.  The only coefficient adjustment needed
for a cup product is the canonical comparison from the integral tensor
product of the restricted factors to the restriction of their `ZMod n`
tensor product.  This file records that compatibility first for cocycle
representatives and then for the descended `H¹ × H¹ → H²` cup product.

The statements include `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {G : Type} [Group G]
variable (n : ℕ) (A B : Rep (ZMod n) G)

/-- Scalar restriction carries a `ZMod n`-linear cup cocycle to the cup of
the scalar-restricted one-cocycles, after the canonical tensor comparison. -/
theorem cocycles₂ZModRestrictIntEquiv_cupCocycleOneOne
    (x : cocycles₁ A) (y : cocycles₁ B) :
    cocycles₂ZModRestrictIntEquiv n (A ⊗ B)
        (cupCocycleOneOne A B x y) =
      mapCocycles₂ (MonoidHom.id G)
        (Rep.zmodRestrictIntTensorIso n A B).hom
        (cupCocycleOneOne
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n B)
          (cocycles₁ZModRestrictIntEquiv n A x)
          (cocycles₁ZModRestrictIntEquiv n B y)) := by
  apply cocycles₂_ext
  intro g h
  rfl

/-- The degree-`(1, 1)` cup product commutes with scalar restriction from
`ZMod n` to `ℤ`, after the canonical tensor comparison. -/
theorem H2ZModRestrictIntAddEquiv_cupOneOne
    (x : H1 A) (y : H1 B) :
    H2ZModRestrictIntAddEquiv n (A ⊗ B)
        (cupOneOne A B x y) =
      map (MonoidHom.id G)
        (Rep.zmodRestrictIntTensorIso n A B).hom 2
        (cupOneOne
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n B)
          (H1ZModRestrictIntAddEquiv n A x)
          (H1ZModRestrictIntAddEquiv n B y)) := by
  induction x using H1_induction_on with
  | _ x =>
      induction y using H1_induction_on with
      | _ y =>
          rw [cupOneOne_H1π_H1π,
            H2ZModRestrictIntAddEquiv_H2π,
            H1ZModRestrictIntAddEquiv_H1π,
            H1ZModRestrictIntAddEquiv_H1π,
            cupOneOne_H1π_H1π,
            ← ConcreteCategory.comp_apply,
            H2π_comp_map]
          rw [cocycles₂ZModRestrictIntEquiv_cupCocycleOneOne]
          rfl

/-- Scalar restriction commutes with an equivariant coefficient map in
degree one. -/
theorem H1ZModRestrictIntAddEquiv_map
    {C : Rep (ZMod n) G} (f : A ⟶ C) (x : H1 A) :
    H1ZModRestrictIntAddEquiv n C
        (map (MonoidHom.id G) f 1 x) =
      map (MonoidHom.id G) (Rep.zmodRestrictIntMap f) 1
        (H1ZModRestrictIntAddEquiv n A x) := by
  induction x using H1_induction_on with
  | _ x =>
      rw [H1ZModRestrictIntAddEquiv_H1π]
      rw [← ConcreteCategory.comp_apply, H1π_comp_map]
      rw [ConcreteCategory.comp_apply,
        H1ZModRestrictIntAddEquiv_H1π]
      rw [← ConcreteCategory.comp_apply, H1π_comp_map]
      rfl

/-- Scalar restriction commutes with an equivariant coefficient map in
degree two. -/
theorem H2ZModRestrictIntAddEquiv_map
    {C : Rep (ZMod n) G} (f : A ⟶ C) (x : H2 A) :
    H2ZModRestrictIntAddEquiv n C
        (map (MonoidHom.id G) f 2 x) =
      map (MonoidHom.id G) (Rep.zmodRestrictIntMap f) 2
        (H2ZModRestrictIntAddEquiv n A x) := by
  induction x using H2_induction_on with
  | _ x =>
      rw [H2ZModRestrictIntAddEquiv_H2π]
      rw [← ConcreteCategory.comp_apply, H2π_comp_map]
      rw [ConcreteCategory.comp_apply,
        H2ZModRestrictIntAddEquiv_H2π]
      rw [← ConcreteCategory.comp_apply, H2π_comp_map]
      rfl

end groupCohomology

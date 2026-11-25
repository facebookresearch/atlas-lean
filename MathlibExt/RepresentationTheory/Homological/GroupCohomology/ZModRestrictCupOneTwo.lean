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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwoNestedFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictCupOneOne
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictDegreeThreeFunctoriality

/-!
# Scalar restriction and the degree-`(1, 2)` cup product

Restriction of coefficients from `ZMod n` to `ℤ` preserves the explicit
degree-`(1, 2)` cup cocycle and its descended H3 class.  The coefficient is
adjusted by the canonical comparison from the integral tensor product of the
restricted factors to the restriction of their `ZMod n` tensor product.

The statements include `n = 0`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace Rep

variable {G : Type} [Group G]

/-- The right-associated tensor cube of a scalar-restricted representation is
canonically the scalar restriction of its right-associated tensor cube. -/
noncomputable def zmodRestrictIntRightTensorCubeIso
    (n : ℕ) (A : Rep (ZMod n) G) :
    zmodRestrictInt n A ⊗
        (zmodRestrictInt n A ⊗ zmodRestrictInt n A) ≅
      zmodRestrictInt n (A ⊗ (A ⊗ A)) :=
  tensorIso (Iso.refl _) (zmodRestrictIntTensorIso n A A) ≪≫
    zmodRestrictIntTensorIso n A (A ⊗ A)

end Rep

namespace groupCohomology

variable {G : Type} [Group G]
variable (n : ℕ) (A B : Rep (ZMod n) G)

/-- Scalar restriction carries a `ZMod n`-linear degree-`(1, 2)` cup cocycle
to the cup of the scalar-restricted cocycles, after the canonical tensor
comparison. -/
theorem cocycles₃ZModRestrictIntEquiv_cupCocycleOneTwo
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cocycles₃ZModRestrictIntEquiv n (A ⊗ B)
        (cupCocycleOneTwo A B x y) =
      mapCocycles₃ (MonoidHom.id G)
        (Rep.zmodRestrictIntTensorIso n A B).hom
        (cupCocycleOneTwo
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n B)
          (cocycles₁ZModRestrictIntEquiv n A x)
          (cocycles₂ZModRestrictIntEquiv n B y)) := by
  apply cocycles₃_ext
  intro g h i
  rfl

/-- Scalar restriction of an explicit right-associated triple cup is the
integral triple cup followed by the canonical tensor-cube comparison. -/
theorem cocycles₃ZModRestrictIntEquiv_nestedCupOneOne
    (x y z : cocycles₁ A) :
    cocycles₃ZModRestrictIntEquiv n (A ⊗ (A ⊗ A))
        (cupCocycleOneTwo A (A ⊗ A) x (cupCocycleOneOne A A y z)) =
      mapCocycles₃ (MonoidHom.id G)
        (Rep.zmodRestrictIntRightTensorCubeIso n A).hom
        (cupCocycleOneTwo
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n A ⊗ Rep.zmodRestrictInt n A)
          (cocycles₁ZModRestrictIntEquiv n A x)
          (cupCocycleOneOne
            (Rep.zmodRestrictInt n A)
            (Rep.zmodRestrictInt n A)
            (cocycles₁ZModRestrictIntEquiv n A y)
            (cocycles₁ZModRestrictIntEquiv n A z))) := by
  rw [cocycles₃ZModRestrictIntEquiv_cupCocycleOneTwo,
    cocycles₂ZModRestrictIntEquiv_cupCocycleOneOne]
  let R := Rep.zmodRestrictInt n A
  let t := (Rep.zmodRestrictIntTensorIso n A A).hom
  have hcup := mapCocycles₃_cupCocycleOneTwo_of_hom
    (MonoidHom.id G) (𝟙 R) t
    (cocycles₁ZModRestrictIntEquiv n A x)
    (cupCocycleOneOne R R
      (cocycles₁ZModRestrictIntEquiv n A y)
      (cocycles₁ZModRestrictIntEquiv n A z))
  have hid : mapCocycles₁ (MonoidHom.id G) (𝟙 R)
      (cocycles₁ZModRestrictIntEquiv n A x) =
      cocycles₁ZModRestrictIntEquiv n A x := by
    apply cocycles₁_ext
    intro g
    rfl
  rw [hid] at hcup
  rw [← hcup]
  apply cocycles₃_ext
  intro g h i
  rfl

/-- The degree-`(1, 2)` cup product commutes with scalar restriction from
`ZMod n` to `ℤ`, after the canonical tensor comparison. -/
theorem H3ZModRestrictIntAddEquiv_cupOneTwo
    (x : H1 A) (y : H2 B) :
    H3ZModRestrictIntAddEquiv n (A ⊗ B)
        (cupOneTwo A B x y) =
      map (MonoidHom.id G)
        (Rep.zmodRestrictIntTensorIso n A B).hom 3
        (cupOneTwo
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n B)
          (H1ZModRestrictIntAddEquiv n A x)
          (H2ZModRestrictIntAddEquiv n B y)) := by
  induction x using H1_induction_on with
  | _ x =>
      induction y using H2_induction_on with
      | _ y =>
          rw [cupOneTwo_H1π_H2π,
            H3ZModRestrictIntAddEquiv_H3π,
            H1ZModRestrictIntAddEquiv_H1π,
            H2ZModRestrictIntAddEquiv_H2π,
            cupOneTwo_H1π_H2π,
            ← ConcreteCategory.comp_apply,
            H3π_comp_map]
          rw [cocycles₃ZModRestrictIntEquiv_cupCocycleOneTwo]
          rfl

/-- Scalar restriction of a right-associated triple cup is the integral
triple cup followed by the canonical right-associated tensor comparison. -/
theorem H3ZModRestrictIntAddEquiv_nestedCupOneOne
    (x y z : H1 A) :
    H3ZModRestrictIntAddEquiv n (A ⊗ (A ⊗ A))
        (cupOneTwo A (A ⊗ A) x (cupOneOne A A y z)) =
      map (MonoidHom.id G)
        (Rep.zmodRestrictIntRightTensorCubeIso n A).hom 3
        (cupOneTwo
          (Rep.zmodRestrictInt n A)
          (Rep.zmodRestrictInt n A ⊗ Rep.zmodRestrictInt n A)
          (H1ZModRestrictIntAddEquiv n A x)
          (cupOneOne
            (Rep.zmodRestrictInt n A)
            (Rep.zmodRestrictInt n A)
            (H1ZModRestrictIntAddEquiv n A y)
            (H1ZModRestrictIntAddEquiv n A z))) := by
  rw [H3ZModRestrictIntAddEquiv_cupOneTwo,
    H2ZModRestrictIntAddEquiv_cupOneOne]
  let R := Rep.zmodRestrictInt n A
  let t := (Rep.zmodRestrictIntTensorIso n A A).hom
  have hcup := map_cupOneTwo_of_hom
    (MonoidHom.id G) (𝟙 R) t
    (H1ZModRestrictIntAddEquiv n A x)
    (cupOneOne R R
      (H1ZModRestrictIntAddEquiv n A y)
      (H1ZModRestrictIntAddEquiv n A z))
  have hid : map (MonoidHom.id G) (𝟙 R) 1
      (H1ZModRestrictIntAddEquiv n A x) =
      H1ZModRestrictIntAddEquiv n A x := by
    rw [map_id]
    rfl
  rw [hid] at hcup
  rw [← hcup]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rfl

end groupCohomology

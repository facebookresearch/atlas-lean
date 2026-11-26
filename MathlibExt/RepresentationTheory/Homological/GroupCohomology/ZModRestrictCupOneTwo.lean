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
# Integral scalar restriction and the cup in degrees one and two

Let n∈ℕ and A,B be ZMod n-representations of a group G.
The additive scalar-restriction comparisons identify the degree-(1,2)
cup cocycle and H¹×H²→H³ cup with their integral counterparts,
using Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B).

For three degree-one classes in A, the nested product x∪(y∪z)
uses the right-associated tensor cube. Its integral comparison preserves
that order through
Res(A)⊗(Res(A)⊗Res(A))≅Res(A⊗(A⊗A)).
All assertions include n=0.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace Rep

variable {G : Type} [Group G]

/-- For n∈ℕ, a group G and a ZMod n-representation A, the
right-associated coefficient comparison is
Res(A)⊗[ℤ](Res(A)⊗[ℤ]Res(A))≅
Res(A⊗[ZMod n](A⊗[ZMod n]A)).
It sends a⊗(b⊗c) to the corresponding ordered tensor. -/
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

/-- Let n∈ℕ, G be a group and A,B representations over ZMod n.
Write Res for scalar restriction to ℤ and
μ:Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B) for the canonical tensor
comparison. All statements include n=0.
For x∈Z¹(G,A) and y∈Z²(G,B), the degree-three scalar-restricted
cup equals the integral (1,2) cup of the restricted cocycles,
followed by μ on its coefficient. -/
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

/-- For n∈ℕ, a group G and a ZMod n-representation A, let x,y,z
be degree-one cocycles. Scalar restriction of x∪(y∪z) equals the
nested integral cup of their restrictions, followed by the
right-associated tensor-cube comparison. -/
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

/-- Let n∈ℕ, G be a group and A,B representations over ZMod n.
Write Res for scalar restriction to ℤ and
μ:Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B) for the canonical tensor
comparison. All statements include n=0.
For x∈H¹(G,A) and y∈H²(G,B), the additive comparison satisfies
χ₃(x∪y)=H³(μ)(χ₁(x)∪χ₂(y)). -/
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

/-- For n∈ℕ, a group G and a ZMod n-representation A, scalar
restriction sends x∪(y∪z) for x,y,z∈H¹(G,A) to the nested
integral cup, with coefficients identified by the right-associated
tensor-cube comparison. The degree is three. -/
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

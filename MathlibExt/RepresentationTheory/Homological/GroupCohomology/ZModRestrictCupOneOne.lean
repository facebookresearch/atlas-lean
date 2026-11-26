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
# Integral scalar restriction and the cup in degrees one and one

For n∈ℕ and a ZMod n-representation of a group G, scalar restriction
to ℤ retains the coefficient group and action. The degree-one and
degree-two cocycle and cohomology comparisons preserve representatives.

The tensor comparison
Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B)
identifies the scalar restriction of the (1,1) cup with the integral cup.
The equality holds on cocycles and on H¹×H¹→H², and is natural in
coefficient morphisms. The case n=0 is included.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {G : Type} [Group G]
variable (n : ℕ) (A B : Rep (ZMod n) G)

/-- Let n∈ℕ, G be a group and A,B representations over ZMod n.
Write Res for scalar restriction to ℤ and
μ:Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B) for the canonical tensor
comparison. All statements include n=0.
For x∈Z¹(G,A) and y∈Z¹(G,B), their cup cocycle is
(x∪y)(g,h)=x(g)⊗g•y(h).
Its scalar restriction equals the integral cup of the restricted
cocycles followed by the coefficient map μ. -/
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

/-- Let n∈ℕ, G be a group and A,B representations over ZMod n.
Write Res for scalar restriction to ℤ and
μ:Res(A)⊗[ℤ]Res(B)≅Res(A⊗[ZMod n]B) for the canonical tensor
comparison. All statements include n=0.
For x∈H¹(G,A) and y∈H¹(G,B), the additive degree-two comparison
satisfies χ₂(x∪y)=H²(μ)(χ₁(x)∪χ₁(y)).
The integral cup first has coefficient Res(A)⊗[ℤ]Res(B). -/
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

/-- For n∈ℕ, a group G and a morphism t:A→C of ZMod n-
representations, the degree-one additive comparison is natural:
χ_C¹∘H¹(t)=H¹(Res(t))∘χ_A¹.
The coefficient action is restricted to ℤ, including n=0. -/
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

/-- For n∈ℕ, a group G and a morphism t:A→C of ZMod n-
representations, the degree-two additive comparison satisfies
χ_C²∘H²(t)=H²(Res(t))∘χ_A², including n=0. -/
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

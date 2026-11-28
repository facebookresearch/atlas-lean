/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReducedGroupSchemesPerfectField

/-!
# Tests for reduced schemes and reduced group schemes over a perfect field
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

open scoped TensorProduct

namespace MathlibExtTest.AlgebraicGeometry.ReducedGroupSchemesPerfectField

universe u v w

/-- Two reduced algebras over a perfect field have a reduced tensor product. -/
example (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A]
    [IsReduced A] (B : Type w) [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) :=
  Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced k A B

/-- In particular `A ⊗[k] A` is reduced, the affine case of `G ×_k G`. -/
example (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A]
    [IsReduced A] : IsReduced (A ⊗[k] A) :=
  Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced k A A

/-- The fibre product of two reduced schemes over a perfect field is reduced. -/
example {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ Spec (.of k)) [IsReduced X] [IsReduced Y] : IsReduced (pullback f g) :=
  isReduced_pullback_of_perfectField f g

/-- A reduced group scheme locally of finite type over a perfect field is smooth. -/
example {k : Type u} [Field k] [PerfectField k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced G] : Smooth f :=
  smooth_of_grpObj_of_isReduced_of_perfectField f

/-- The reduction of a scheme is reduced, and a morphism from a reduced scheme factors through
it. -/
example {X Y : Scheme.{u}} [IsReduced Y] (g : Y ⟶ X) :
    IsReduced X.nilradical.subscheme ∧ g.liftNilradical ‹_› ≫ X.nilradical.subschemeι = g :=
  ⟨inferInstance, Scheme.Hom.liftNilradical_subschemeι g _⟩

/-- Over a perfect field, the reduction of a group scheme is a group scheme and its closed
immersion into `G` is a homomorphism (both found by instance search). -/
example {k : Type u} [Field k] [PerfectField k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] :
    Nonempty (GrpObj (Over.mk (G.nilradical.subschemeι ≫ f))) ∧
      IsMonHom (nilradicalSubschemeι f) ∧ IsClosedImmersion G.nilradical.subschemeι :=
  ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

/-- The group law of `G_red` is the restriction of that of `G`. -/
example {k : Type u} [Field k] [PerfectField k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] :
    μ[Over.mk (G.nilradical.subschemeι ≫ f)] ≫ nilradicalSubschemeι f =
      (nilradicalSubschemeι f ⊗ₘ nilradicalSubschemeι f) ≫ μ[Over.mk f] :=
  IsMonHom.mul_hom _

end MathlibExtTest.AlgebraicGeometry.ReducedGroupSchemesPerfectField

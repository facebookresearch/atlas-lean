/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CanonicalPolarizationData

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.QMCanonicalPol

universe u v

namespace CanonicalPolarizationDataTest

/-- Consumer with the original binders: canonical polarization data gives
an invertible symmetric sheaf whose Mumford kernel is `2`-torsion and
which is Rosati compatible. -/
theorem exactSource {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L Ldual : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L Ldual) :
    IsLineBundle L ∧ IsSymmetric G L ∧
      KernelIsTwoTorsion G L Ldual ∧
      RosatiCompatible G L Ldual act act_over star :=
  ⟨h.isLineBundle, h.isSymmetric, h.kernelIsTwoTorsion,
    h.rosatiCompatible⟩

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {S : Type 1} [CommRing S] {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {I : Type 1} (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) (L Ldual : A.Modules)
    (h : CanonicalPolarizationData G act act_over star L Ldual) :
    IsLineBundle L ∧ IsSymmetric G L ∧
      KernelIsTwoTorsion G L Ldual ∧
      RosatiCompatible G L Ldual act act_over star :=
  ⟨h.isLineBundle, h.isSymmetric, h.kernelIsTwoTorsion,
    h.rosatiCompatible⟩

/-- Boundary point: the identity point satisfies the `2`-torsion
equation in the kernel condition, and negation is over the base. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    G.mul t (G.one t) (G.one t) = G.one t ∧ negMor G ≫ f = f :=
  ⟨mul_one_one G t, negMor_over G⟩

/-- Local isomorphism is reflexive and symmetric on an actual sheaf. -/
example {X : Scheme.{u}} (M M' : X.Modules) (h : LocIsoOnBase M M') :
    LocIsoOnBase M M ∧ LocIsoOnBase M' M :=
  ⟨locIsoOnBase_refl M, locIsoOnBase_symm h⟩

end CanonicalPolarizationDataTest

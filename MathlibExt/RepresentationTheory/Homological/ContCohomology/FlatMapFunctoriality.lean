/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
# Composition on tuple-form continuous homogeneous cochains

For a topological ring k, profinite groups G,H,K and continuous coefficient
intertwiners f,g, the tuple-form cochain map associated to φ:H→G and f sends
a cochain a to t ↦ f(a(φ(t))). Identity and composition hold on the complete
tuple-form complexes, with independent group universes and a common coefficient
carrier. The laws agree with those of the nested homogeneous complexes through
their canonical tuple comparisons.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u v z y w

namespace ContinuousCohomology

/-- The identity group and coefficient maps induce the identity of the tuple-form
homogeneous cochain complex. -/
theorem nativeFlatGroupCoefficientMap_id
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} (X : TopRep.{max v w, u, v} k G) :
    nativeFlatGroupCoefficientMap.{u, v, v, w}
      (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (flatHomogeneousComplex X) := by
  apply (cancel_epi (homogeneousFlatComplexIso.{u, v, w} X).hom).1
  apply (cancel_mono (homogeneousFlatComplexIso.{u, v, w} X).inv).1
  simpa only [nativeGroupCoefficientCochainsMap, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Category.id_comp] using
    nativeGroupCoefficientCochainsMap_id.{u, v, w} X

/-- For three independently sized profinite groups, tuple-form group/coefficient
cochain maps compose by composing the group maps and restricting then composing
the coefficient intertwiners. Coefficients lie in max(v,z,y,w). -/
theorem nativeFlatGroupCoefficientMap_comp
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} {K : ProfiniteGrp.{y}}
    {X : TopRep.{max v (max z (max y w)), u, v} k G}
    {Y : TopRep.{max z (max v (max y w)), u, z} k H}
    {Z : TopRep.{max y (max v (max z w)), u, y} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ Y ⟶ Z) :
    nativeFlatGroupCoefficientMap.{u, v, y, max z w} (φ.comp ψ)
        ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) =
      nativeFlatGroupCoefficientMap.{u, v, z, max y w} φ f ≫
        nativeFlatGroupCoefficientMap.{u, z, y, max v w} ψ g := by
  apply (cancel_epi (homogeneousFlatComplexIso.{u, v, max z (max y w)} X).hom).1
  apply (cancel_mono (homogeneousFlatComplexIso.{u, y, max v (max z w)} Z).inv).1
  simpa only [nativeGroupCoefficientCochainsMap, Category.assoc,
    Iso.inv_hom_id_assoc] using
    nativeGroupCoefficientCochainsMap_comp.{u, v, z, y, w} φ ψ f g

/-- The same composition law holds for every tuple-form homogeneous degree map. -/
theorem nativeFlatGroupCoefficientTerm_comp
    {k : Type u} [Ring k] [TopologicalSpace k]
    {G : ProfiniteGrp.{v}} {H : ProfiniteGrp.{z}} {K : ProfiniteGrp.{y}}
    {X : TopRep.{max v (max z (max y w)), u, v} k G}
    {Y : TopRep.{max z (max v (max y w)), u, z} k H}
    {Z : TopRep.{max y (max v (max z w)), u, y} k K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ Y ⟶ Z) (n : ℕ) :
    nativeFlatGroupCoefficientTerm.{u, v, y, max z w} (φ.comp ψ)
        ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) n =
      nativeFlatGroupCoefficientTerm.{u, v, z, max y w} φ f n ≫
        nativeFlatGroupCoefficientTerm.{u, z, y, max v w} ψ g n := by
  simpa only [nativeFlatGroupCoefficientMap, HomologicalComplex.comp_f] using
    congrArg (fun m => m.f n)
      (nativeFlatGroupCoefficientMap_comp.{u, v, z, y, w} φ ψ f g)

end ContinuousCohomology

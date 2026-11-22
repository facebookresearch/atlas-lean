/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.DiscreteFunctor
public import MathlibExt.CategoryTheory.Action.Coinvariants
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.End

/-!
# Actual permutation actions on native freely based discrete spaces
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v wH w

open CategoryTheory

namespace PointedCGWH

/-- The type-permutation bridge retains the existing categorical product order. -/
private def typePermutationAut (I : Type w) : Equiv.Perm I →* Aut I where
  toFun e := Aut.of e.toIso
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply ConcreteCategory.hom_ext
    intro i
    rfl
  map_mul' e d := by
    apply Aut.ext
    apply Iso.ext
    apply ConcreteCategory.hom_ext
    intro i
    rfl

/-- Actual index permutations act by automorphisms of the native G-plus space. -/
def permutationAut (I : Type w) :
    Equiv.Perm I →* Aut (basedDiscreteObj.{u, v, w} I) := by
  let bridge : Equiv.Perm I →* Aut I :=
    { toFun e := Aut.of e.toIso
      map_one' := by
        apply Aut.ext
        apply Iso.ext
        apply ConcreteCategory.hom_ext
        intro i
        rfl
      map_mul' e d := by
        apply Aut.ext
        apply Iso.ext
        apply ConcreteCategory.hom_ext
        intro i
        rfl }
  exact (Functor.mapAut I basedDiscreteFunctor.{u, v, w}).comp bridge

@[reassoc (attr := simp)]
theorem permutationAut_generator (I : Type w) (e : Equiv.Perm I) (i : I) :
    basedDiscreteIncl.{u, v, w} I i ≫ (permutationAut I e).asIso.hom =
      basedDiscreteIncl I (e i) :=
  basedDiscreteIncl_naturality (fun x => e x) i

/-- Actual left group multiplication as a chosen index-permutation homomorphism. -/
private def leftPermutationHom (G : Type w) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := Equiv.mulLeft_one
  map_mul' := Equiv.mulLeft_mul

/-- Full left multiplication acts on the actual native G-plus carrier. -/
def leftTranslationAut (G : Type w) [Group G] :
    G →* Aut (basedDiscreteObj.{u, v, w} G) := by
  let bridge : G →* Equiv.Perm G :=
    { toFun := Equiv.mulLeft
      map_one' := Equiv.mulLeft_one
      map_mul' := Equiv.mulLeft_mul }
  exact (permutationAut G).comp bridge

@[reassoc (attr := simp)]
theorem leftTranslationAut_generator (G : Type w) [Group G] (k g : G) :
    basedDiscreteIncl.{u, v, w} G g ≫ (leftTranslationAut G k).asIso.hom =
      basedDiscreteIncl G (k * g) :=
  permutationAut_generator G (Equiv.mulLeft k) g

/-- Inverse right multiplication uses only the target-group inverse. -/
private def inverseRightPermutationHom (H : Type wH) (G : Type w)
    [Monoid H] [Group G] (iota : H →* G) : H →* Equiv.Perm G where
  toFun a := Equiv.mulRight ((iota a)⁻¹)
  map_one' := by
    rw [iota.map_one, inv_one, Equiv.mulRight_one]
  map_mul' a b := by
    rw [iota.map_mul, mul_inv_rev, Equiv.mulRight_mul]

/-- The actual inverse-right index action on native G-plus. -/
def inverseRightTranslationAut (H : Type wH) (G : Type w)
    [Monoid H] [Group G] (iota : H →* G) :
    H →* Aut (basedDiscreteObj.{u, v, w} G) := by
  let bridge : H →* Equiv.Perm G :=
    { toFun a := Equiv.mulRight ((iota a)⁻¹)
      map_one' := by
        rw [iota.map_one, inv_one, Equiv.mulRight_one]
      map_mul' a b := by
        rw [iota.map_mul, mul_inv_rev, Equiv.mulRight_mul] }
  exact (permutationAut G).comp bridge

@[reassoc (attr := simp)]
theorem inverseRightTranslationAut_generator (H : Type wH) (G : Type w)
    [Monoid H] [Group G] (iota : H →* G) (a : H) (g : G) :
    basedDiscreteIncl.{u, v, w} G g ≫ (inverseRightTranslationAut H G iota a).asIso.hom =
      basedDiscreteIncl G (g * (iota a)⁻¹) :=
  permutationAut_generator G (Equiv.mulRight ((iota a)⁻¹)) g

/-- The native generator action is the actual chosen generic inverse-right dictionary. -/
theorem inverseRightTranslationAut_action (H : Type wH) (G : Type w)
    [Monoid H] [Group G] (iota : H →* G) (a : H) (g : G) :
    letI := ActionCategory.inverseRightMulAction H G iota
    basedDiscreteIncl.{u, v, w} G g ≫ (inverseRightTranslationAut H G iota a).asIso.hom =
      basedDiscreteIncl G (a • g) := by
  let _ := ActionCategory.inverseRightMulAction H G iota
  exact inverseRightTranslationAut_generator H G iota a g

/-- Full left and inverse-right index multiplication commute on the actual native carrier. -/
theorem leftTranslationAut_inverseRight_commute (H : Type wH) (G : Type w)
    [Monoid H] [Group G] (iota : H →* G) (k : G) (a : H) :
    (leftTranslationAut.{u, v, w} G k).asIso.hom ≫
        (inverseRightTranslationAut H G iota a).asIso.hom =
      (inverseRightTranslationAut H G iota a).asIso.hom ≫
        (leftTranslationAut G k).asIso.hom := by
  let L : G ⟶ G := ↾fun g => k * g
  let R : G ⟶ G := ↾fun g => g * (iota a)⁻¹
  have h : L ≫ R = R ≫ L := by
    apply ConcreteCategory.hom_ext
    intro g
    exact mul_assoc k g (iota a)⁻¹
  change basedDiscreteFunctor.{u, v, w}.map L ≫ basedDiscreteFunctor.map R =
    basedDiscreteFunctor.map R ≫ basedDiscreteFunctor.map L
  rw [← Functor.map_comp, ← Functor.map_comp, h]

end PointedCGWH

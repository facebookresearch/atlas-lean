/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.Basic

/-! # Functoriality of `K₂`

Concrete `K₂` functoriality via the categorical kernel.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

/-- `K₂` on ring homomorphisms via the categorical functor. -/
noncomputable def K2.mapRingHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    K2 R →* K2 S :=
  (K2.functor.map (RingCat.ofHom f)).hom

@[simp]
lemma K2.functor_map_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    K2.functor.map (RingCat.ofHom f) = GrpCat.ofHom (K2.mapRingHom f) :=
  rfl

@[simp]
theorem K2.mapRingHom_id {R : Type u} [Ring R] :
    K2.mapRingHom (RingHom.id R) = MonoidHom.id (K2 R) := by
  ext x
  have h_eq : RingCat.ofHom (RingHom.id R) = 𝟙 (RingCat.of R) := rfl
  have h_map : K2.functor.map (RingCat.ofHom (RingHom.id R)) =
      𝟙 (K2.functor.obj (RingCat.of R)) := by
    rw [h_eq, K2.functor.map_id]
  have h_congr : (K2.functor.map (RingCat.ofHom (RingHom.id R))) x =
      (𝟙 (K2.functor.obj (RingCat.of R))) x :=
    ConcreteCategory.congr_hom h_map x
  exact h_congr

@[simp]
theorem K2.mapRingHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    K2.mapRingHom (g.comp f) = (K2.mapRingHom g).comp (K2.mapRingHom f) := by
  ext x
  have h_eq : RingCat.ofHom (g.comp f) = RingCat.ofHom f ≫ RingCat.ofHom g := rfl
  have h_map : K2.functor.map (RingCat.ofHom (g.comp f)) =
      K2.functor.map (RingCat.ofHom f) ≫ K2.functor.map (RingCat.ofHom g) := by
    rw [h_eq, K2.functor.map_comp]
  have h_congr : (K2.functor.map (RingCat.ofHom (g.comp f))) x =
      (K2.functor.map (RingCat.ofHom f) ≫ K2.functor.map (RingCat.ofHom g)) x :=
    ConcreteCategory.congr_hom h_map x
  have h_left : (K2.functor.map (RingCat.ofHom (g.comp f))) x =
      K2.mapRingHom (g.comp f) x := rfl
  have h_right : (K2.functor.map (RingCat.ofHom f) ≫
      K2.functor.map (RingCat.ofHom g)) x =
      K2.mapRingHom g (K2.mapRingHom f x) := rfl
  rw [h_left, h_right] at h_congr
  exact h_congr

@[simp]
theorem K2.inclusion_mapRingHom_apply {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (x : K2 R) :
    K2.inclusion.app (RingCat.of S) (K2.mapRingHom f x) =
      StableSteinberg.mapRingHom f (K2.inclusion.app (RingCat.of R) x) := by
  have h_nat := K2.inclusion.naturality (RingCat.ofHom f)
  have h_congr : (K2.functor.map (RingCat.ofHom f) ≫ K2.inclusion.app (RingCat.of S)) x =
      (K2.inclusion.app (RingCat.of R) ≫ StableSteinberg.functor.map (RingCat.ofHom f)) x :=
    ConcreteCategory.congr_hom h_nat x
  have h_left : (K2.functor.map (RingCat.ofHom f) ≫
      K2.inclusion.app (RingCat.of S)) x =
      K2.inclusion.app (RingCat.of S) (K2.mapRingHom f x) := rfl
  have h_right : (K2.inclusion.app (RingCat.of R) ≫
      StableSteinberg.functor.map (RingCat.ofHom f)) x =
      StableSteinberg.mapRingHom f (K2.inclusion.app (RingCat.of R) x) := by
    rw [StableSteinberg.functor_map_ofHom]
    rfl
  rw [h_left, h_right] at h_congr
  exact h_congr

end AlgebraicKTheory

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Continuous homogeneous cochains as a coefficient functor

We bundle homogeneous continuous cochains as an additive functor in the
coefficient representation, for a fixed topological group.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def coefficientHom
    {X Y : TopRep.{max v w, u, v} k G} (f : X ⟶ Y) :
    TopRep.res (ContinuousMonoidHom.id G) X ⟶ Y :=
  TopRep.ofHom f.hom

private theorem cochainsMap_congr
    {X Y : TopRep.{max v w, u, v} k G}
    {φ ψ : G →ₜ* G}
    (hφψ : φ = ψ)
    (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ X ⟶ Y)
    (hfg : f.hom.toContinuousLinearMap = g.hom.toContinuousLinearMap) :
    cochainsMap φ f = cochainsMap ψ g := by
  subst ψ
  congr 1
  ext
  simp [hfg]

private theorem resolutionMap_add
    {X Y : TopRep.{max v w, u, v} k G}
    (f g : X ⟶ Y) (n : ℕ) :
    resolutionMap (ContinuousMonoidHom.id G) (coefficientHom (f + g)) n =
      resolutionMap (ContinuousMonoidHom.id G) (coefficientHom f) n +
        resolutionMap (ContinuousMonoidHom.id G) (coefficientHom g) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
      ext F x
      rfl

/-- Homogeneous continuous cochains as a functor in the coefficient
representation. -/
noncomputable def homogeneousCochainsFunctor :
    TopRep.{max v w, u, v} k G ⥤
      CochainComplex (TopModuleCat.{max v w} k) ℕ where
  obj X := TopRep.homogeneousCochains X
  map f := cochainsMap (ContinuousMonoidHom.id G) (TopRep.ofHom f.hom)
  map_id X := by
    exact (cochainsMap_congr rfl (coefficientHom (𝟙 X)) (𝟙 X) rfl).trans
      (cochainsMap_id X)
  map_comp f g := by
    have hid : ContinuousMonoidHom.id G =
        (ContinuousMonoidHom.id G).comp (ContinuousMonoidHom.id G) := by
      ext x
      rfl
    exact (cochainsMap_congr hid (coefficientHom (f ≫ g))
      ((TopRep.resFunctor (ContinuousMonoidHom.id G : G →* G)).map
        (coefficientHom f) ≫ coefficientHom g) rfl).trans
      (cochainsMap_comp (ContinuousMonoidHom.id G)
        (ContinuousMonoidHom.id G) (coefficientHom f) (coefficientHom g))

instance homogeneousCochainsFunctor_additive :
    (homogeneousCochainsFunctor.{u, v, w} (k := k) (G := G)).Additive where
  map_add {X Y} {f g} := by
    change cochainsMap (ContinuousMonoidHom.id G) (coefficientHom (f + g)) =
      cochainsMap (ContinuousMonoidHom.id G) (coefficientHom f) +
        cochainsMap (ContinuousMonoidHom.id G) (coefficientHom g)
    ext n : 1
    rw [HomologicalComplex.add_f_apply, cochainsMap_f, cochainsMap_f,
      cochainsMap_f, resolutionMap_add]
    ext z
    rfl

end ContinuousCohomology

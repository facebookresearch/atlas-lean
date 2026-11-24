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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFunctor
public import MathlibExt.Algebra.Category.Grp.Kernel
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Categorical `K₂`

The stable Steinberg-to-elementary arrow and its categorical kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicKTheory

noncomputable section

/-! ## Arrow `St → E∞` -/

/-- Arrow functor `R ↦ (St(R) ⟶ E∞(R))` induced by `toStableENat`. -/
noncomputable def StableSteinberg.toStableEArrow : RingCat.{u} ⥤ Arrow GrpCat.{u} where
  obj R := Arrow.mk (StableSteinberg.toStableENat.app R)
  map {R S} f :=
    Arrow.homMk (StableSteinberg.functor.map f) (StableE.functor.map f)
      (StableSteinberg.toStableENat.naturality f)
  map_id R := by
    apply Arrow.hom_ext
    · exact StableSteinberg.functor.map_id R
    · exact StableE.functor.map_id R
  map_comp {R S T} f g := by
    apply Arrow.hom_ext
    · exact StableSteinberg.functor.map_comp f g
    · exact StableE.functor.map_comp f g

/-! ## Functorial `K₂` as categorical kernel -/

/-- Functorial `K₂` as the categorical kernel of `St → E∞`. -/
noncomputable def K2.functor : RingCat.{u} ⥤ GrpCat.{u} :=
  StableSteinberg.toStableEArrow ⋙ Limits.ker (C := GrpCat.{u})

@[simp]
lemma K2.functor_obj (R : RingCat.{u}) :
    K2.functor.obj R = Limits.kernel (StableSteinberg.toStableENat.app R) :=
  rfl

@[simp]
lemma K2.functor_obj_of (R : Type u) [Ring R] :
    K2.functor.obj (RingCat.of R) =
      Limits.kernel (GrpCat.ofHom (StableSteinberg.toStableE (R := R))) :=
  rfl

/-- Underlying type of `K₂(R)`. -/
abbrev K2 (R : Type u) [Ring R] : Type u :=
  ↥(K2.functor.obj (RingCat.of R))

/-! ## Kernel inclusion `K₂ → St` -/

/-- Natural kernel inclusion `K₂ → St`. -/
noncomputable def K2.inclusion : K2.functor.{u} ⟶ StableSteinberg.functor.{u} where
  app R := Limits.kernel.ι (StableSteinberg.toStableENat.app R)
  naturality {R S} f := by
    have h := (Limits.ker.ι (C := GrpCat.{u})).naturality
      (StableSteinberg.toStableEArrow.map f)
    dsimp [K2.functor] at h ⊢
    exact h

@[simp]
lemma K2.inclusion_app (R : RingCat.{u}) :
    K2.inclusion.app R = Limits.kernel.ι (StableSteinberg.toStableENat.app R) :=
  rfl

/-! ## Concrete kernel isomorphisms -/

/-- Concrete description of `K₂(R)` as subgroup kernel. -/
noncomputable def K2.kernelIsoKer (R : RingCat.{u}) :
    K2.functor.obj R ≅ GrpCat.of (StableSteinberg.toStableENat.app R).hom.ker :=
  GrpCat.kernelIsoKer (StableSteinberg.toStableENat.app R)

/-- Concrete description for `RingCat.of R`. -/
noncomputable def K2.kernelIsoKerOf (R : Type u) [Ring R] :
    K2.functor.obj (RingCat.of R) ≅ GrpCat.of (StableSteinberg.toStableE (R := R)).ker :=
  GrpCat.kernelIsoKer (GrpCat.ofHom (StableSteinberg.toStableE (R := R)))

@[simp]
lemma K2.kernelIsoKer_hom_comp_subtype {R : RingCat.{u}} :
    (K2.kernelIsoKer R).hom ≫
      GrpCat.ofHom (Subgroup.subtype (StableSteinberg.toStableENat.app R).hom.ker) =
      K2.inclusion.app R :=
  GrpCat.kernelIsoKer_hom_comp_subtype (StableSteinberg.toStableENat.app R)

@[simp]
lemma K2.kernelIsoKer_inv_comp_ι {R : RingCat.{u}} :
    (K2.kernelIsoKer R).inv ≫ K2.inclusion.app R =
      GrpCat.ofHom (Subgroup.subtype (StableSteinberg.toStableENat.app R).hom.ker) :=
  GrpCat.kernelIsoKer_inv_comp_ι (StableSteinberg.toStableENat.app R)

@[simp]
lemma K2.kernelIsoKerOf_hom_comp_subtype {R : Type u} [Ring R] :
    (K2.kernelIsoKerOf (R := R)).hom ≫
      GrpCat.ofHom (Subgroup.subtype (StableSteinberg.toStableE (R := R)).ker) =
      K2.inclusion.app (RingCat.of R) :=
  GrpCat.kernelIsoKer_hom_comp_subtype (GrpCat.ofHom (StableSteinberg.toStableE (R := R)))

@[simp]
lemma K2.kernelIsoKerOf_inv_comp_ι {R : Type u} [Ring R] :
    (K2.kernelIsoKerOf (R := R)).inv ≫ K2.inclusion.app (RingCat.of R) =
      GrpCat.ofHom (Subgroup.subtype (StableSteinberg.toStableE (R := R)).ker) :=
  GrpCat.kernelIsoKer_inv_comp_ι (GrpCat.ofHom (StableSteinberg.toStableE (R := R)))

/-! ## Kernel vanishes under `toStableE` -/

theorem K2.inclusion_comp_toStableE :
    K2.inclusion.{u} ≫ StableSteinberg.toStableENat.{u} = 0 := by
  ext R x
  exact ConcreteCategory.congr_hom
    (Limits.kernel.condition (StableSteinberg.toStableENat.app R)) x

@[simp]
theorem K2.toStableE_inclusion_apply {R : Type u} [Ring R] (x : K2 R) :
    StableSteinberg.toStableE (K2.inclusion.app (RingCat.of R) x) = 1 := by
  have hApp : K2.inclusion.app (RingCat.of R) ≫
      StableSteinberg.toStableENat.app (RingCat.of R) =
      (0 : K2.functor.obj (RingCat.of R) ⟶ StableE.functor.obj (RingCat.of R)) := by
    have := congrArg (fun t : K2.functor ⟶ StableE.functor => t.app (RingCat.of R))
      K2.inclusion_comp_toStableE
    simpa using this
  have h := ConcreteCategory.congr_hom hApp x
  have h_comp : ((K2.inclusion.app (RingCat.of R) ≫
      StableSteinberg.toStableENat.app (RingCat.of R)) x) =
      StableSteinberg.toStableE ((K2.inclusion.app (RingCat.of R)) x) := rfl
  have h_zero : ((0 : K2.functor.obj (RingCat.of R) ⟶
      StableE.functor.obj (RingCat.of R)) x) = (1 : StableE R) := rfl
  rw [h_comp, h_zero] at h
  exact h

theorem K2.inclusion_apply_mem_ker {R : Type u} [Ring R] (x : K2 R) :
    (K2.inclusion.app (RingCat.of R) x : StableSteinberg R) ∈
      MonoidHom.ker (StableSteinberg.toStableE (R := R)) := by
  exact MonoidHom.mem_ker.mpr (K2.toStableE_inclusion_apply x)

end

end AlgebraicKTheory

end

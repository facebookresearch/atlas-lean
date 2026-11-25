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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
public import MathlibExt.Analysis.CStarAlgebra.Unitization
public import Mathlib.Algebra.Group.Monoid

/-!
# Equivariant unitization of point-norm actions

A point-norm action on a nonunital complex C-star algebra induces an action
on its canonical unitization by fixing the scalar coordinate and acting on
the ideal coordinate. The ideal inclusion and scalar character are
equivariant, and equivariant homomorphisms induce coordinatewise maps of
unitizations.
-/

@[expose] public section

open Filter
open scoped CStarAlgebra

universe uG uA uB uC

noncomputable section

namespace PointNormCStarAction

variable {G : Type uG} {A : Type uA} {B : Type uB}
variable [Monoid G] [TopologicalSpace G]
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Let `G` be a monoid equipped with a topology, and let `A` be possibly nonunital complex
C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient orbits in
the norm topology.

The point-norm action induced on the canonical unitization. -/
noncomputable def unitizationAction (α : PointNormCStarAction G A) :
    PointNormCStarAction G (Unitization ℂ A) := by
  let actionAut (g : G) : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A :=
    StarAlgEquiv.ofBijective
      (Unitization.starMap (α.aut g).toNonUnitalStarAlgHom)
      ⟨Unitization.starMap_injective (α.aut g).injective,
        Unitization.starMap_surjective (α.aut g).surjective⟩
  have actionAut_apply (g : G) (x : Unitization ℂ A) :
      actionAut g x =
        Unitization.inl x.fst + Unitization.inr (α g x.snd) := by
    change Unitization.starMap (α.aut g).toNonUnitalStarAlgHom x = _
    induction x using Unitization.ind with
    | inl_add_inr z a => simp [Unitization.algebraMap_eq_inl]
  exact
    { toMonoidHom :=
      { toFun := actionAut
        map_one' := by
          apply StarAlgEquiv.ext
          intro x
          rw [actionAut_apply, α.apply_one]
          exact Unitization.inl_fst_add_inr_snd_eq x
        map_mul' := by
          intro g h
          apply StarAlgEquiv.ext
          intro x
          change actionAut (g * h) x = actionAut g (actionAut h x)
          simp [actionAut_apply] }
      continuous_orbit := by
        intro x
        rw [continuous_iff_continuousAt]
        intro g₀
        rw [ContinuousAt, Metric.tendsto_nhds]
        intro ε hε
        filter_upwards
            [(Metric.tendsto_nhds.mp (α.continuous_orbit x.snd).continuousAt)
              ε hε] with g hg
        calc
          dist (actionAut g x) (actionAut g₀ x) =
              dist (α g x.snd) (α g₀ x.snd) := by
            rw [actionAut_apply, actionAut_apply, dist_eq_norm,
              dist_eq_norm, add_sub_add_left_eq_sub, ← Unitization.inr_sub,
              Unitization.norm_inr]
          _ < ε := hg }

@[simp]
theorem unitizationAction_apply
    (α : PointNormCStarAction G A) (g : G) (x : Unitization ℂ A) :
    α.unitizationAction g x =
      Unitization.inl x.fst + Unitization.inr (α g x.snd) := by
  change Unitization.starMap (α.aut g).toNonUnitalStarAlgHom x = _
  induction x using Unitization.ind with
  | inl_add_inr z a =>
      simp only [Unitization.fst_add, Unitization.fst_inl,
        Unitization.fst_inr, add_zero, Unitization.snd_add,
        Unitization.snd_inl, Unitization.snd_inr, zero_add]
      rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr,
        Unitization.algebraMap_eq_inl]
      rfl

@[simp]
theorem unitizationAction_inl
    (α : PointNormCStarAction G A) (g : G) (z : ℂ) :
    α.unitizationAction g (Unitization.inl z) = Unitization.inl z := by
  simp [unitizationAction_apply]

@[simp]
theorem unitizationAction_inr
    (α : PointNormCStarAction G A) (g : G) (a : A) :
    α.unitizationAction g (Unitization.inr a) =
      Unitization.inr (α g a) := by
  simp [unitizationAction_apply]

/-- Let `G` be a monoid equipped with a topology, and let `A` be possibly nonunital complex
C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient orbits in
the norm topology.

The canonical ideal inclusion as an equivariant homomorphism. -/
def unitizationInclusion (α : PointNormCStarAction G A) :
    PointNormCStarAction.Hom α α.unitizationAction where
  toNonUnitalStarAlgHom := Unitization.inrNonUnitalStarAlgHom ℂ A
  equivariant' := by
    intro g a
    simp

@[simp]
theorem unitizationInclusion_apply
    (α : PointNormCStarAction G A) (a : A) :
    α.unitizationInclusion a = Unitization.inr a :=
  rfl

/-- Let `G` be a monoid equipped with a topology, and let `A` be possibly nonunital complex
C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient orbits in
the norm topology.

The scalar character is equivariant from the unitization action to the trivial action on the
scalars. -/
def unitizationCharacter (α : PointNormCStarAction G A) :
    PointNormCStarAction.Hom α.unitizationAction
      (PointNormCStarAction.trivial G ℂ) where
  toNonUnitalStarAlgHom :=
    (Unitization.fstStarAlgHom A).toNonUnitalStarAlgHom
  equivariant' := by
    intro g x
    change (α.unitizationAction g x).fst = x.fst
    rw [unitizationAction_apply]
    simp

@[simp]
theorem unitizationCharacter_apply
    (α : PointNormCStarAction G A) (x : Unitization ℂ A) :
    α.unitizationCharacter x = x.fst :=
  rfl

@[simp]
theorem unitizationCharacter_inclusion_apply
    (α : PointNormCStarAction G A) (a : A) :
    α.unitizationCharacter (α.unitizationInclusion a) = 0 :=
  rfl

namespace Hom

variable {α : PointNormCStarAction G A} {β : PointNormCStarAction G B}

/-- Let `G` be a monoid equipped with a topology, and let `A` and `B` be possibly nonunital complex
C*-algebras. Specify actions by star-algebra automorphisms with continuous coefficient orbits in
the norm topology.

Coordinatewise unitization of an equivariant homomorphism. -/
def unitizationMap (φ : PointNormCStarAction.Hom α β) :
    PointNormCStarAction.Hom α.unitizationAction β.unitizationAction where
  toNonUnitalStarAlgHom :=
    (Unitization.starMap φ.toNonUnitalStarAlgHom).toNonUnitalStarAlgHom
  equivariant' := by
    intro g x
    change Unitization.starMap φ.toNonUnitalStarAlgHom
      (α.unitizationAction g x) =
        β.unitizationAction g
          (Unitization.starMap φ.toNonUnitalStarAlgHom x)
    induction x using Unitization.ind with
    | inl_add_inr z a =>
        calc
          Unitization.starMap φ.toNonUnitalStarAlgHom
              (α.unitizationAction g
                (Unitization.inl z + Unitization.inr a)) =
              Unitization.inl z + Unitization.inr
                (φ.toNonUnitalStarAlgHom (α g a)) := by
            simp [unitizationAction_apply, Unitization.algebraMap_eq_inl]
          _ = Unitization.inl z + Unitization.inr
              (β g (φ.toNonUnitalStarAlgHom a)) :=
            congrArg (fun b : B => Unitization.inl z + Unitization.inr b)
              (φ.equivariant' g a)
          _ = β.unitizationAction g
              (Unitization.starMap φ.toNonUnitalStarAlgHom
                (Unitization.inl z + Unitization.inr a)) := by
            simp [unitizationAction_apply, Unitization.algebraMap_eq_inl]

@[simp]
theorem unitizationMap_apply
    (φ : PointNormCStarAction.Hom α β) (x : Unitization ℂ A) :
    φ.unitizationMap x =
      Unitization.inl x.fst + Unitization.inr (φ x.snd) := by
  change Unitization.starMap φ.toNonUnitalStarAlgHom x = _
  induction x using Unitization.ind with
  | inl_add_inr z a =>
      simp only [Unitization.fst_add, Unitization.fst_inl,
        Unitization.fst_inr, add_zero, Unitization.snd_add,
        Unitization.snd_inl, Unitization.snd_inr, zero_add]
      rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr,
        Unitization.algebraMap_eq_inl]
      rfl

@[simp]
theorem unitizationMap_id (α : PointNormCStarAction G A) :
    (PointNormCStarAction.Hom.id α).unitizationMap =
      PointNormCStarAction.Hom.id α.unitizationAction := by
  apply PointNormCStarAction.Hom.ext
  intro x
  rw [unitizationMap_apply]
  exact Unitization.inl_fst_add_inr_snd_eq x

@[simp]
theorem unitizationMap_comp
    {C : Type uC} [NonUnitalCStarAlgebra C]
    {γ : PointNormCStarAction G C}
    (ψ : PointNormCStarAction.Hom β γ)
    (φ : PointNormCStarAction.Hom α β) :
    (PointNormCStarAction.Hom.comp ψ φ).unitizationMap =
      PointNormCStarAction.Hom.comp ψ.unitizationMap φ.unitizationMap := by
  apply PointNormCStarAction.Hom.ext
  intro x
  simp [unitizationMap_apply]

@[simp]
theorem unitizationMap_comp_inclusion
    (φ : PointNormCStarAction.Hom α β) :
    PointNormCStarAction.Hom.comp φ.unitizationMap α.unitizationInclusion =
      PointNormCStarAction.Hom.comp β.unitizationInclusion φ := by
  apply PointNormCStarAction.Hom.ext
  intro a
  simp

@[simp]
theorem character_comp_unitizationMap
    (φ : PointNormCStarAction.Hom α β) :
    PointNormCStarAction.Hom.comp β.unitizationCharacter φ.unitizationMap =
      α.unitizationCharacter := by
  apply PointNormCStarAction.Hom.ext
  intro x
  simp [unitizationMap_apply]

end Hom

end PointNormCStarAction

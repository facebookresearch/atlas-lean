/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PointQuotient
public import MathlibExt.Topology.Compactification.OnePoint.QuotientComplement

/-!
# Point quotients as one-point compactifications

If an arrow has nonempty closed range in a compact Hausdorff target and the
complement of that range is homeomorphic to a space `Y`, then its point
quotient is the one-point compactification of `Y`.  This packages the generic
bridge from the existing point-quotient complement API.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Set
open scoped OnePoint

universe u v

namespace TopCat

set_option backward.isDefEq.respectTransparency false in
/-- A chosen model for the complement of a closed collapsed range also
models the complement of the point in the point quotient. -/
noncomputable def pointQuotientTargetComplementHomeomorph
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right)) :
    Y ≃ₜ
      (({pointQuotientPoint f PUnit.unit}ᶜ :
        Set (pointQuotient f))) := by
  have hset : (Set.range f.hom)ᶜ =
      (pointQuotientProjection.app f).hom ⁻¹'
        ({pointQuotientPoint f PUnit.unit}ᶜ :
          Set (pointQuotient f)) := by
    rw [Set.preimage_compl]
    exact congrArg (fun s : Set f.right ↦ sᶜ)
      (pointQuotientProjection_preimage_singleton f).symm
  let h := pointQuotientProjection_isHomeomorph_compl_of_isClosed_range
    f hf
  exact sourceComplement.trans
    ((Homeomorph.setCongr hset).trans (h.homeomorph _))

@[simp]
theorem pointQuotientTargetComplementHomeomorph_apply
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right))
    (y : Y) :
    (pointQuotientTargetComplementHomeomorph hf sourceComplement y).1 =
      pointQuotientProjection.app f (sourceComplement y).1 :=
  rfl

/-- A one-point compactification model for a closed-range point quotient. -/
noncomputable def onePointHomeomorphPointQuotient
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right)) :
    OnePoint Y ≃ₜ pointQuotient f :=
  OnePoint.homeomorphOfQuotientComplement
    (Set.range f.hom) (pointQuotientProjection.app f).hom
    (pointQuotientPoint f PUnit.unit) hf
    (pointQuotientProjection_isQuotientMap f)
    (pointQuotientProjection_preimage_singleton f)
    sourceComplement
    (pointQuotientTargetComplementHomeomorph hf sourceComplement)
    (pointQuotientTargetComplementHomeomorph_apply hf sourceComplement)

@[simp]
theorem onePointHomeomorphPointQuotient_apply_infty
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right)) :
    onePointHomeomorphPointQuotient hf sourceComplement ∞ =
      pointQuotientPoint f PUnit.unit :=
  rfl

@[simp]
theorem onePointHomeomorphPointQuotient_apply_coe
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right))
    (y : Y) :
    onePointHomeomorphPointQuotient hf sourceComplement (y : OnePoint Y) =
      pointQuotientProjection.app f (sourceComplement y).1 :=
  rfl

/-- The closed-range point quotient, oriented toward its one-point
compactification model. -/
noncomputable def pointQuotientHomeomorphOnePoint
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right)) :
    pointQuotient f ≃ₜ OnePoint Y :=
  (onePointHomeomorphPointQuotient hf sourceComplement).symm

@[simp]
theorem pointQuotientHomeomorphOnePoint_point
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right)) :
    pointQuotientHomeomorphOnePoint hf sourceComplement
        (pointQuotientPoint f PUnit.unit) =
      ∞ := by
  apply (onePointHomeomorphPointQuotient hf sourceComplement).symm_apply_eq.mpr
  rfl

@[simp]
theorem pointQuotientHomeomorphOnePoint_projection
    {f : Arrow TopCat.{u}} [Nonempty f.left]
    [CompactSpace f.right] [T2Space f.right]
    (hf : IsClosed (Set.range f.hom))
    {Y : Type v} [TopologicalSpace Y]
    (sourceComplement :
      Y ≃ₜ ((Set.range f.hom)ᶜ : Set f.right))
    (y : Y) :
    pointQuotientHomeomorphOnePoint hf sourceComplement
        (pointQuotientProjection.app f (sourceComplement y).1) =
      (y : OnePoint Y) := by
  apply (onePointHomeomorphPointQuotient hf sourceComplement).symm_apply_eq.mpr
  rfl

end TopCat

end

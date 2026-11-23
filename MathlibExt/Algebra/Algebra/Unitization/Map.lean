/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Unitization

/-!
# Canonical maps between algebraic unitizations

A nonunital algebra map extends by the native unitization universal property,
leaving the scalar coordinate unchanged and applying the original map to the
algebra coordinate. Scalar and algebra carrier universes remain independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v w

namespace Unitization

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original nonunital algebra map lifts through the genuine unitization property. -/
def mapAlgHom {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) :
    Unitization k A →ₐ[k] Unitization k B :=
  Unitization.lift ((Unitization.inrNonUnitalAlgHom k B).comp f)

@[simp]
theorem mapAlgHom_inr {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (a : A) :
    mapAlgHom k A f (Unitization.inr a) = Unitization.inr (f a) := by
  simp [mapAlgHom, Unitization.lift]

@[simp]
theorem mapAlgHom_inl {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (r : k) :
    mapAlgHom k A f (Unitization.inl r) = Unitization.inl r := by
  simpa only [Unitization.algebraMap_eq_inl] using (mapAlgHom k A f).commutes r

/-- Independent original algebra carriers keep both native unitization coordinates. -/
theorem mapAlgHom_apply {B : Type w} [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B] (f : A →ₙₐ[k] B) (x : Unitization k A) :
    mapAlgHom k A f x = Unitization.mk (x.fst, f x.snd) := by
  conv_lhs =>
    rw [← Unitization.inl_fst_add_inr_snd_eq x, map_add,
      mapAlgHom_inl, mapAlgHom_inr]
  apply Unitization.ext
  · simp only [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]
  · simp only [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

end Unitization

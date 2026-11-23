/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/Valuation/ValuativeRel/Comap.lean;
TauCeti/AlgebraicGeometry/AdicSpace/ValuationSpectrum/Basic.lean;
TauCeti/AlgebraicGeometry/AdicSpace/Cont/Basic.lean;
TauCeti/AlgebraicGeometry/AdicSpace/Spa/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: Chris Birkbeck. Apache 2.0.
Modification: retain the all-rank valuative-relation construction and its
exact comparison/continuity rules, in one narrow standalone ATLAS module.
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Actual all-rank affine adic point spectra

A point is an actual valuative relation, independent of a chosen value
group. Basic opens compare two ring elements. Continuity tests the open
attained-value balls; under the topological-ring hypotheses of Huber pairs
this is the usual value-group continuity criterion. No rank-one or real
seminorm substitute is used.

Reference: Wedhorn, *Adic Spaces*, arXiv:1910.05934v1,
Definitions 4.1, 7.7 and 7.23; Scholze, arXiv:1111.4914v1, §2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineAdicSpectra

open CategoryTheory TopologicalSpace

universe u

/-- Pullback of the actual valuation relation along a ring map. -/
@[instance_reducible]
def comapRelation {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (v : ValuativeRel B) : ValuativeRel A where
  vle a b := v.vle (f a) (f b)
  vle_total a b := v.vle_total (f a) (f b)
  vle_trans h j := v.vle_trans h j
  vle_add h j := by simpa [map_add] using v.vle_add h j
  mul_vle_mul_left h a := by simpa [map_mul] using v.mul_vle_mul_left h (f a)
  vle_mul_cancel h j := by
    rw [map_zero] at h
    simpa [map_mul] using v.vle_mul_cancel h (by simpa [map_mul] using j)
  not_vle_one_zero := by simp [v.not_vle_one_zero]
  vle_mul_comm := by simp only [map_mul]; exact v.vle_mul_comm

/-- All-rank valuation points, with no chosen representative value group. -/
@[ext] structure Spectrum (A : Type u) [CommRing A] where
  relation : ValuativeRel A

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The actual basic comparison open in the valuation spectrum. -/
def basicOpen (a b : A) : Set (Spectrum A) :=
  {v | v.relation.vle a b ∧ ¬ v.relation.vle b 0}

instance : TopologicalSpace (Spectrum A) :=
  TopologicalSpace.generateFrom {U | ∃ a b : A, U = basicOpen a b}

/-- The actual point map induced by a ring map. -/
def comap (f : A →+* B) (v : Spectrum B) : Spectrum A :=
  ⟨comapRelation f v.relation⟩

@[simp] theorem comap_basicOpen (f : A →+* B) (a b : A) :
    comap f ⁻¹' basicOpen a b = basicOpen (f a) (f b) := by
  ext v
  change (v.relation.vle (f a) (f b) ∧ ¬ v.relation.vle (f b) (f 0)) ↔
    (v.relation.vle (f a) (f b) ∧ ¬ v.relation.vle (f b) 0)
  rw [map_zero]

theorem continuous_comap (f : A →+* B) : Continuous (comap f) := by
  rw [continuous_generateFrom_iff]
  rintro U ⟨a, b, rfl⟩
  rw [comap_basicOpen]
  exact isOpen_generateFrom_of_mem ⟨f a, f b, rfl⟩

@[simp] theorem comap_id (v : Spectrum A) : comap (RingHom.id A) v = v := by
  apply Spectrum.ext
  apply ValuativeRel.ext
  funext a b
  rfl

@[simp] theorem comap_comp (f : A →+* B) (g : B →+* C)
    (v : Spectrum C) : comap (g.comp f) v = comap f (comap g v) := by
  apply Spectrum.ext
  apply ValuativeRel.ext
  funext a b
  rfl

/-- Continuity is imposed on the comparison relation itself. -/
def IsContinuous [TopologicalSpace A] (v : Spectrum A) : Prop :=
  ∀ b : A, IsOpen {a : A | v.relation.vlt a b}

theorem IsContinuous.comap [TopologicalSpace A] [TopologicalSpace B]
    {v : Spectrum B} (hv : IsContinuous v) (f : A →+* B)
    (hf : Continuous f) : IsContinuous (comap f v) := by
  intro b
  exact (hv (f b)).preimage hf

/-- The actual adic spectrum of the prescribed plus subring. -/
def Spa [TopologicalSpace A] (Aplus : Subring A) : Set (Spectrum A) :=
  {v | IsContinuous v ∧ ∀ a ∈ Aplus, v.relation.vle a 1}

/-- A continuous plus-preserving ring map gives its actual Spa point map. -/
def spaComap [TopologicalSpace A] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {Aplus : Subring A}
    {Bplus : Subring B} (hp : ∀ a ∈ Aplus, f a ∈ Bplus) :
    Spa Bplus → Spa Aplus :=
  fun v ↦ ⟨comap f v.1, v.2.1.comap f hf,
    fun a ha ↦ by
      change v.1.relation.vle (f a) (f 1)
      rw [map_one]
      exact v.2.2 (f a) (hp a ha)⟩

theorem continuous_spaComap [TopologicalSpace A] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {Aplus : Subring A}
    {Bplus : Subring B} (hp : ∀ a ∈ Aplus, f a ∈ Bplus) :
    Continuous (spaComap f hf hp) :=
  ((continuous_comap f).comp continuous_subtype_val).subtype_mk _

end MathlibExt.AlgebraicGeometry.AffineAdicSpectra

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeMapTypeModels
public import Mathlib.Data.Fintype.Perm

/-!
# Actual root-permutation groups and contact multiplicities

Eligible root permutations preserve the full relative type through an
actual vertex permutation: genus, actual degree labels, leg incidence,
root incidence and contact orders. The group Eq(eta) is the intersection
for the two sides, as a native subgroup of the finite root-permutation
group. Its order is that group's actual cardinal, not a supplied scalar.
Source: Jun Li arXiv:math/0110113v1, Section3.1, p30 and introduction p4.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups

open RelativeMapTypeModels
open scoped BigOperators

variable {n r : ℕ} (G : RelativeType n r) {A : Type*} (beta : Fin G.vertices → A)

def eligible (s : Equiv.Perm (Fin r)) : Prop :=
  ∃ v : Equiv.Perm (Fin G.vertices),
    (∀ i, G.genus (v i) = G.genus i) ∧ (∀ i, beta (v i) = beta i) ∧
    (∀ i : Fin n, v (G.legLabels i).1 = (G.legLabels i).1) ∧
    (∀ i : Fin r, (G.rootLabels (s i)).1 = v (G.rootLabels i).1) ∧
    (∀ i : Fin r, G.order (s i) = G.order i)

def rootGroup : Subgroup (Equiv.Perm (Fin r)) where
  carrier := {s | eligible G beta s}
  one_mem' := show eligible G beta 1 from ⟨1, by simp, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro s t ⟨v, hg, hb, hl, hr, ho⟩ ⟨w, kg, kb, kl, kr, ko⟩
    show eligible G beta (s * t)
    refine ⟨v * w, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact (hg (w i)).trans (kg i)
    · intro i; exact (hb (w i)).trans (kb i)
    · intro i; change v (w (G.legLabels i).1) = _; rw [kl, hl]
    · intro i; change (G.rootLabels (s (t i))).1 = v (w (G.rootLabels i).1); rw [hr, kr]
    · intro i; exact (ho (t i)).trans (ko i)
  inv_mem' := by
    rintro s ⟨v, hg, hb, hl, hr, ho⟩
    show eligible G beta s⁻¹
    refine ⟨v⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simpa using (hg (v⁻¹ i)).symm
    · intro i; simpa using (hb (v⁻¹ i)).symm
    · intro i; change v.symm (G.legLabels i).1 = _; exact v.symm_apply_eq.mpr (hl i).symm
    · intro i
      change (G.rootLabels (s.symm i)).1 = v.symm (G.rootLabels i).1
      apply v.injective
      simpa using (hr (s.symm i)).symm
    · intro i; simpa using (ho (s⁻¹ i)).symm

variable {n' : ℕ} (H : RelativeType n' r) {B : Type*} (gamma : Fin H.vertices → B)

def equivalenceGroup : Subgroup (Equiv.Perm (Fin r)) := rootGroup G beta ⊓ rootGroup H gamma

instance equivalenceGroupFintype : Fintype (equivalenceGroup G beta H gamma) := Fintype.ofFinite _

def equivalenceOrder : ℕ := Fintype.card (equivalenceGroup G beta H gamma)

def contactMultiplicity : ℕ := ∏ i : Fin r, G.order i

theorem equivalenceOrder_pos : 0 < equivalenceOrder G beta H gamma := Fintype.card_pos

theorem contactMultiplicity_pos : 0 < contactMultiplicity G :=
  Finset.prod_pos (fun i _ => G.positive i)

end MathlibExt.AlgebraicGeometry.RelativeRootEquivalenceGroups

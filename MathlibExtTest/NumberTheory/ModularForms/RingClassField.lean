/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.RingClassField
import MathlibExt.Analysis.SpecialFunctions.Elliptic.HomothetyClasses

open PeriodPair

-- The `j`-invariant of a lattice contained in `K` lies in the ring class field of its own
-- endomorphism ring.
example (K : Subfield ℂ) (L : PeriodPair) (hLK : (L.lattice : Set ℂ) ⊆ K) :
    L.jInvariant ∈ ringClassField K L.endomorphismRing :=
  jInvariant_mem_ringClassField (isProperIdeal_endomorphismRing L) hLK

-- Homothetic lattices give the same generator: `j(αL) = j(L)`, by the homothety lemma.
example (L : PeriodPair) (α : ℂˣ) : (L.scale α).jInvariant = L.jInvariant :=
  jInvariant_eq_of_lattice_eq_smul α.ne_zero (lattice_scale L α)

-- A lattice contained in `K` and its multiple by `α ∈ K` give the same generator.
example (K : Subfield ℂ) (L : PeriodPair) (α : ℂˣ) (hLK : (L.lattice : Set ℂ) ⊆ K) :
    (L.scale α).jInvariant ∈ ringClassField K L.endomorphismRing := by
  rw [jInvariant_eq_of_lattice_eq_smul α.ne_zero (lattice_scale L α)]
  exact jInvariant_mem_ringClassField (isProperIdeal_endomorphismRing L) hLK

-- Outside the case of an order: no lattice has endomorphism ring `ℂ`, since `ω₁ / 2` is not a
-- lattice point, so the generating set is empty and `ringClassField K ⊤ = ⊥`.
example (K : Subfield ℂ) : ringClassField K ⊤ = ⊥ := by
  have h : {x | ∃ L : PeriodPair, L.IsProperIdeal ⊤ ∧ (L.lattice : Set ℂ) ⊆ K ∧
      x = L.jInvariant} = (∅ : Set ℂ) := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨L, hL, -, -⟩
    have h2 : (2⁻¹ : ℂ) ∈ L.endomorphismRing := hL ▸ Subring.mem_top _
    apply L.ω₁_div_two_notMem_lattice
    simpa [div_eq_inv_mul] using h2 L.ω₁ L.ω₁_mem_lattice
  rw [ringClassField, h, IntermediateField.adjoin_empty]

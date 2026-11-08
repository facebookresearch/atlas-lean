/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Finiteness.Quotient

public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.PurelyInseparable.Basic

@[expose] public section

open scoped Pointwise

namespace Ideal

attribute [local instance] Ideal.Quotient.field

/-- Inertia cardinality equals ramification index times inseparable degree. -/
theorem card_inertia_eq_ramificationIdxIn_mul_finInsepDegree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B] {p : Ideal A} [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (P.inertia G) =
      ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
  have h_exact := Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P
  have h_index : ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).index =
      Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr h_exact.toEquiv
  have h_lagrange := ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index
  rw [h_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv] at h_lagrange
  let _ : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal G p P
  have h_aut_sep : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) =
      Field.finSepDegree (A ⧸ p) (B ⧸ P) :=
    Nat.card_congr
      (Normal.algHomEquivAut (A ⧸ p) (AlgebraicClosure (B ⧸ P)) (B ⧸ P)).symm
  rw [h_aut_sep] at h_lagrange
  have h_gef := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G
  have h_orbit := Algebra.IsInvariant.orbit_eq_primesOver A B G p P
  have h_gD : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P) =
      Nat.card G := by
    rw [← h_orbit]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hg_pos : 0 < (primesOver p B).ncard := by
    by_contra hg
    simp only [not_lt, Nat.le_zero] at hg
    rw [hg, zero_mul] at h_gef
    linarith [Nat.card_pos (α := G)]
  have h_D_eq : Nat.card (MulAction.stabilizer G P) =
      ramificationIdxIn p B * inertiaDegIn p B :=
    Nat.eq_of_mul_eq_mul_left hg_pos (h_gD.trans h_gef.symm)
  rw [h_D_eq, inertiaDegIn_eq_inertiaDeg p P G, Ideal.inertiaDeg_eq_of_isMaximal p P,
    ← Field.finSepDegree_mul_finInsepDegree (A ⧸ p) (B ⧸ P)] at h_lagrange
  have h_rw : ramificationIdxIn p B * (Field.finSepDegree (A ⧸ p) (B ⧸ P) *
      Field.finInsepDegree (A ⧸ p) (B ⧸ P)) =
      (ramificationIdxIn p B * Field.finInsepDegree (A ⧸ p) (B ⧸ P)) *
        Field.finSepDegree (A ⧸ p) (B ⧸ P) := by
    ring
  rw [h_rw] at h_lagrange
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne _)) h_lagrange

end Ideal

end

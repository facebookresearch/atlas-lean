/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`Definitions/Def_MvFormalGroup_BasicV2.lean`,
`Definitions/Def_MvFormalGroup_EndRingV2.lean`,
`P2M/Sol/S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`P2M/Sol/S_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric.lean`, and
`P2M/Sol/S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Basic

/-!
# Homomorphisms of multivariate formal group laws

A homomorphism `MvFormalGroup.Hom F G` of formal group laws is a family of power series with zero
constant terms that intertwines the two laws. This file defines the identity, composition, zero
and sum of homomorphisms; the homomorphisms into a commutative formal group law form an additive
commutative monoid.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

/-- A homomorphism of formal group laws `F → G`: power series with zero constant terms that
intertwine the two group laws. -/
@[ext]
structure Hom (F : MvFormalGroup g R) (G : MvFormalGroup h R) where

  toPowerSeries : Fin h → MvPowerSeries (Fin g) R

  constantCoeff_eq_zero : ∀ i, (toPowerSeries i).constantCoeff = 0

  subst_eq : ∀ i,
    subst F.toPowerSeries (toPowerSeries i)
      =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (toPowerSeries j))
        fun j => subst
          (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (toPowerSeries j))
      (G.toPowerSeries i)

namespace Hom

theorem hasSubst_toPowerSeries {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    (φ : Hom F G) : HasSubst φ.toPowerSeries :=
  hasSubst_of_constantCoeff_zero φ.constantCoeff_eq_zero

/-- The identity homomorphism of a formal group law. -/
def id (F : MvFormalGroup g R) : Hom F F where
  toPowerSeries := fun i => X i
  constantCoeff_eq_zero := fun i => constantCoeff_X i
  subst_eq := by
    intro i
    change subst F.toPowerSeries (X i)
        = subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (X j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (X j))
          (F.toPowerSeries i)
    have h2 : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have h3 : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hl : (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (X j : MvPowerSeries (Fin g) R))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (X j : MvPowerSeries (Fin g) R))
        = fun s => (X s : MvPowerSeries (Fin g ⊕ Fin g) R) := by
      funext s
      rcases s with j | j
      · simp [subst_X h2]
      · simp [subst_X h3]
    rw [subst_X F.hasSubst_toPowerSeries, hl, subst_self]
    rfl

/-- Composition of homomorphisms of formal group laws. -/
def comp {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
    (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  toPowerSeries := fun i => subst φ.toPowerSeries (ψ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero φ.hasSubst_toPowerSeries φ.constantCoeff_eq_zero
      (ψ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    change subst F.toPowerSeries (subst φ.toPowerSeries (ψ.toPowerSeries i))
        = subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
          (H.toPowerSeries i)
    have hAφ : HasSubst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;>
        exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
          (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
    have hAψ : HasSubst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
          (ψ.toPowerSeries j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
          (ψ.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;>
        exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
          (fun l => constantCoeff_X _) (ψ.constantCoeff_eq_zero j)
    rw [subst_comp_subst_apply φ.hasSubst_toPowerSeries F.hasSubst_toPowerSeries]
    have heq1 : (fun s => subst F.toPowerSeries (φ.toPowerSeries s))
        = fun s => subst (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j)) (G.toPowerSeries s) :=
      funext fun s => φ.subst_eq s
    rw [heq1, ← subst_comp_subst_apply G.hasSubst_toPowerSeries hAφ, ψ.subst_eq i,
      subst_comp_subst_apply hAψ hAφ]
    have heq2 : (fun s => subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j)) s))
        = Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · change subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j))
        rw [subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) hAφ,
          subst_comp_subst_apply φ.hasSubst_toPowerSeries
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)]
        have hfam : (fun s : Fin h => subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (X (Sum.inl s) : MvPowerSeries (Fin h ⊕ Fin h) R))
            = fun s => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries s) := by
          funext l
          simp only [subst_X hAφ, Sum.elim_inl]
        rw [hfam]
      · change subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j))
        rw [subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) hAφ,
          subst_comp_subst_apply φ.hasSubst_toPowerSeries
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)]
        have hfam : (fun s : Fin h => subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (X (Sum.inr s) : MvPowerSeries (Fin h ⊕ Fin h) R))
            = fun s => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries s) := by
          funext l
          simp only [subst_X hAφ, Sum.elim_inr]
        rw [hfam]
    rw [heq2]

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

/-- The zero homomorphism of formal group laws. -/
def zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) : Hom F G where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    change subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R)
      = subst (Sum.elim
          (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
          fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
        (G.toPowerSeries i)
    have hL : subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R) = 0 := by
      rw [← coe_substAlgHom F.hasSubst_toPowerSeries, map_zero]
    have hfam : (Sum.elim
        (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        = fun _ : Fin h ⊕ Fin h => (0 : MvPowerSeries (Fin g ⊕ Fin g) R) := by
      funext s
      rcases s with j | j
      · change subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXl, map_zero]
      · change subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXr, map_zero]
    rw [hL, hfam,
      subst_zero_of_constantCoeff_eq_zero (G.constantCoeff_eq_zero i)]

@[simp]
theorem toPowerSeries_zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) :
    (Hom.zero F G).toPowerSeries = fun _ => 0 := rfl

/-- The sum of two homomorphisms into a commutative formal group law. -/
def add [IsComm G] (φ ψ : Hom F G) : Hom F G where
  toPowerSeries := fun i =>
    subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_elim G φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero i
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hφψ : HasSubst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) :=
      hasSubst_elim φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hψL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    have hψR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    change subst F.toPowerSeries
        (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i))
      = subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
        (G.toPowerSeries i)
    rw [subst_comp_subst_apply hφψ F.hasSubst_toPowerSeries]
    have hLfam : (fun s => subst F.toPowerSeries
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s))
        = Sum.elim (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
          fun j => subst F.toPowerSeries (ψ.toPowerSeries j) := by
      funext s
      rcases s with j | j <;> rfl
    rw [hLfam]
    have hφeq : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => φ.subst_eq j
    have hψeq : (fun j => subst F.toPowerSeries (ψ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => ψ.subst_eq j
    rw [hφeq, hψeq, subst_elim_exchange G hφL hφR hψL hψR i]
    have hfinL : (fun s' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinR : (fun s' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinal : (Sum.elim
        (fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        = Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · change subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXl, hfinL]
      · change subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXr, hfinR]
    rw [hfinal]

@[simp]
theorem toPowerSeries_add [IsComm G] (φ ψ : Hom F G) :
    (Hom.add φ ψ).toPowerSeries
      = fun i => subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i) :=
  rfl

instance instZero : Zero (Hom F G) := ⟨Hom.zero F G⟩

@[simp]
theorem toPowerSeries_zero' : (0 : Hom F G).toPowerSeries = fun _ => 0 := rfl

instance instAdd [IsComm G] : Add (Hom F G) := ⟨Hom.add⟩

instance instAddCommMonoid [IsComm G] : AddCommMonoid (Hom F G) where
  add := (· + ·)
  zero := 0
  nsmul := nsmulRec
  add_assoc a b c := by
    apply Hom.ext
    funext i
    change subst (Sum.elim
        (fun j => subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries j))
        c.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim a.toPowerSeries
        fun j => subst (Sum.elim b.toPowerSeries c.toPowerSeries) (G.toPowerSeries j))
        (G.toPowerSeries i)
    exact subst_elim_assoc G a.constantCoeff_eq_zero b.constantCoeff_eq_zero
      c.constantCoeff_eq_zero i
  zero_add a := by
    apply Hom.ext
    funext i
    change subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have h0X : HasSubst (Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
        fun j => (X j : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
          fun j => (X j : MvPowerSeries (Fin h) R)) s))
        = Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) a.toPowerSeries := by
      funext s
      rcases s with j | j
      · change subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
      · change subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
    have h1 : subst a.toPowerSeries (subst (Sum.elim (fun _ => 0)
        fun j => (X j : MvPowerSeries (Fin h) R)) (G.toPowerSeries i))
        = subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply h0X hsa, hfam]
    rw [← h1, subst_elim_zero_X G i, subst_X hsa]
  add_zero a := by
    apply Hom.ext
    funext i
    change subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have hX0 : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
        fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun j => constantCoeff_X j) fun _ => map_zero _
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
          fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) s))
        = Sum.elim a.toPowerSeries fun _ : Fin h => (0 : MvPowerSeries (Fin g) R) := by
      funext s
      rcases s with j | j
      · change subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
      · change subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
    have h1 : subst a.toPowerSeries (subst (Sum.elim
        (fun j => (X j : MvPowerSeries (Fin h) R)) fun _ => 0) (G.toPowerSeries i))
        = subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply hX0 hsa, hfam]
    rw [← h1, subst_elim_X_zero G i, subst_X hsa]
  add_comm a b := by
    apply Hom.ext
    funext i
    change subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim b.toPowerSeries a.toPowerSeries) (G.toPowerSeries i)
    exact subst_elim_comm G a.constantCoeff_eq_zero b.constantCoeff_eq_zero i

end Hom

end MvFormalGroup

end

end

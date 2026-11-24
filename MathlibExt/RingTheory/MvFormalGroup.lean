/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_MvFormalGroup_BasicV2.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Multivariate formal groups

A multivariate formal group law over a commutative ring, given by
power series with vanishing constant coefficient, linear part the
identity, and the associativity identity. Homomorphisms, endomorphisms,
base change and the `n`-series are defined, together with evaluation at
nilpotent points.
-/

@[expose] public noncomputable section

open MvPowerSeries

@[ext]
structure MvFormalGroup (g : ℕ) (R : Type*) [CommRing R] where

  toPowerSeries : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R

  constantCoeff_eq_zero : ∀ i, (toPowerSeries i).constantCoeff = 0

  coeff_single_inl : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0

  coeff_single_inr : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0

  assoc : ∀ i,
    subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j)))
      (toPowerSeries i)
      =
    subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (toPowerSeries j))
      (toPowerSeries i)

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommRing S]

class IsComm (F : MvFormalGroup g R) : Prop where
  comm : ∀ i,
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
      (F.toPowerSeries i)
      = F.toPowerSeries i

theorem hasSubst_toPowerSeries (F : MvFormalGroup g R) : HasSubst F.toPowerSeries :=
  hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero

theorem subst_X_add_X {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) (s t : σ) :
    subst a (X s + X t : MvPowerSeries σ R) = a s + a t := by
  have h := hasSubst_of_constantCoeff_zero ha
  rw [subst_add h, subst_X h, subst_X h]

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

def id (F : MvFormalGroup g R) : Hom F F where
  toPowerSeries := fun i => X i
  constantCoeff_eq_zero := fun i => constantCoeff_X i
  subst_eq := by
    intro i
    show subst F.toPowerSeries (X i)
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

def comp {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
    (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  toPowerSeries := fun i => subst φ.toPowerSeries (ψ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero φ.hasSubst_toPowerSeries φ.constantCoeff_eq_zero
      (ψ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    show subst F.toPowerSeries (subst φ.toPowerSeries (ψ.toPowerSeries i))
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
      · show subst
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
      · show subst
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

end Hom

def End (F : MvFormalGroup g R) := Hom F F

def map (f : R →+* S) (F : MvFormalGroup g R) : MvFormalGroup g S where
  toPowerSeries := fun i => MvPowerSeries.map f (F.toPowerSeries i)
  constantCoeff_eq_zero := by
    intro i
    rw [constantCoeff_map, F.constantCoeff_eq_zero, map_zero]
  coeff_single_inl := by
    intro i j
    rw [coeff_map, F.coeff_single_inl]
    split <;> simp
  coeff_single_inr := by
    intro i j
    rw [coeff_map, F.coeff_single_inr]
    split <;> simp
  assoc := by
    intro i
    have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hB := hasSubst_of_constantCoeff_zero hzB
    have hC := hasSubst_of_constantCoeff_zero hzC
    have hA : HasSubst (Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
      · exact constantCoeff_X _
    have hA' : HasSubst (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
    have key := congrArg (MvPowerSeries.map f) (F.assoc i)
    rw [map_subst hA, map_subst hA'] at key
    have hBmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s))
        = Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inl l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hCmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s))
        = Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inr l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hAmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) s))
        = Sum.elim
          (fun j => subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inl l))) (MvPowerSeries.map f (F.toPowerSeries j)))
          fun j => X (Sum.inr (Sum.inr j)) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map f (subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
            = subst (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inl l))) (MvPowerSeries.map f (F.toPowerSeries j))
        rw [map_subst hB, hBmap]
      · simp [map_X]
    have hA'map : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
        = Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun j => subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inr l))) (MvPowerSeries.map f (F.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · simp [map_X]
      · show MvPowerSeries.map f (subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
            = subst (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inr l))) (MvPowerSeries.map f (F.toPowerSeries j))
        rw [map_subst hC, hCmap]
    rw [hAmap, hA'map] at key
    exact key

def nthSeries (F : MvFormalGroup g R) : ℕ → Fin g → MvPowerSeries (Fin g) R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      subst (Sum.elim (nthSeries F n) fun j => X j) (F.toPowerSeries i)

@[simp]
theorem nthSeries_zero (F : MvFormalGroup g R) : F.nthSeries 0 = fun _ => 0 := rfl

theorem nthSeries_succ (F : MvFormalGroup g R) (n : ℕ) : F.nthSeries (n + 1) = fun i =>
    subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i) := rfl

def linearPart (φ : Fin h → MvPowerSeries (Fin g) R) : Matrix (Fin h) (Fin g) R :=
  Matrix.of fun i j => (φ i).coeff (Finsupp.single j 1)

def FiniteHeight (p : ℕ) {K : Type*} [Field K] [CharP K p] (F : MvFormalGroup g K) : Prop :=
  FiniteDimensional K (MvPowerSeries (Fin g) K ⧸ Ideal.span (Set.range (F.nthSeries p)))

def addMv (g : ℕ) (R : Type*) [CommRing R] : MvFormalGroup g R where
  toPowerSeries := fun i => X (Sum.inl i) + X (Sum.inr i)
  constantCoeff_eq_zero := by
    intro i
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0
    rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]
  coeff_single_inl := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  coeff_single_inr := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  assoc := by
    intro i
    have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    simp only [subst_X_add_X hzB, subst_X_add_X hzC, Sum.elim_inl, Sum.elim_inr]
    have hzA : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
          + X (Sum.inr (Sum.inl j)))
        fun j => X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    have hzA' : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => X (Sum.inr (Sum.inl j)) + X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    rw [subst_X_add_X hzA, subst_X_add_X hzA']
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_assoc _ _ _

instance (g : ℕ) (R : Type*) [CommRing R] : IsComm (addMv g R) where
  comm := by
    intro i
    have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    show subst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
        (X (Sum.inl i) + X (Sum.inr i)) = X (Sum.inl i) + X (Sum.inr i)
    rw [subst_X_add_X hz]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_comm _ _

end MvFormalGroup

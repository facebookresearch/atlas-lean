/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_MvFormalGroup_BasicV2.lean`,
`Definitions/Def_MvFormalGroup_EndRingV2.lean`,
`Definitions/Def_MvFormalGroup_NegV2.lean`,
`Definitions/Def_CerednikDrinfeld_SpecialFormalModule.lean`,
`Definitions/Def_CerednikDrinfeld_LubinTateModule.lean`,
`Definitions/Def_CerednikDrinfeld_StandardFormalODModule.lean`,
`Definitions/Def_CerednikDrinfeld_SpecialFormalFunctorG.lean`
and the `AlgFunctor` and `frobTwist` definitions from
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean` and
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum.lean`
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
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.InitTail
public import Mathlib.RingTheory.WittVector.MulCoeff
public import Mathlib.RingTheory.WittVector.StructurePolynomial
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Truncated

@[expose] public noncomputable section


set_option autoImplicit false

noncomputable section

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

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section Subst

variable {σ τ : Type*}

theorem subst_zero_of_constantCoeff_eq_zero {f : MvPowerSeries σ R}
    (hf : f.constantCoeff = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = 0 := by
  classical
  ext d
  rw [map_zero, coeff_subst HasSubst.zero, finsum_eq_zero_of_forall_eq_zero]
  intro e
  by_cases he : e = 0
  · subst he
    simp [coeff_zero_eq_constantCoeff_apply, hf]
  · obtain ⟨i, hi⟩ : ∃ i : σ, e i ≠ 0 := by
      by_contra hc
      exact he (Finsupp.ext fun a => not_ne_iff.mp fun hne => hc ⟨a, hne⟩)
    have hz : (e.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi) (by simp [zero_pow hi])
    rw [hz, map_zero, smul_zero]

theorem le_order_finsuppProd_pow {c : σ → MvPowerSeries τ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0) (e : σ →₀ ℕ) :
    (e.degree : ℕ∞) ≤ (e.prod fun j n => (c j) ^ n).order := by
  classical
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (e j) (hc0 j)

theorem homogeneousComponent_finsuppProd_pow [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    (e : σ →₀ ℕ) :
    homogeneousComponent e.degree (e.prod fun j n => (c j) ^ n) =
      monomial e (1 : R) := by
  classical
  suffices H : ∀ n : ℕ, ∀ e : σ →₀ ℕ, e.degree = n →
      homogeneousComponent n (e.prod fun j m => (c j) ^ m) = monomial e (1 : R) by
    exact H e.degree e rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro e hen
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have he : e = 0 := (Finsupp.degree_eq_zero_iff e).mp hen
      subst he
      rw [Finsupp.prod_zero_index]
      ext d
      rw [coeff_homogeneousComponent, coeff_monomial]
      by_cases hd : d = 0
      · subst hd
        simp
      · rw [if_neg (fun hcon => hd ((Finsupp.degree_eq_zero_iff d).mp hcon)), if_neg hd]
    · have he0 : e ≠ 0 := by
        intro hcon
        subst hcon
        rw [map_zero] at hen
        omega
      obtain ⟨j, hj⟩ : ∃ j : σ, e j ≠ 0 := by
        by_contra hc
        exact he0 (Finsupp.ext fun a => not_ne_iff.mp fun hne => hc ⟨a, hne⟩)
      set e' : σ →₀ ℕ := e - Finsupp.single j 1 with he'def
      have hsplit : Finsupp.single j 1 + e' = e :=
        add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj))
      have hdeg' : e'.degree = n - 1 := by
        have hcongr := congrArg Finsupp.degree hsplit
        rw [map_add, Finsupp.degree_single] at hcongr
        omega
      have hP : (e.prod fun j' m => (c j') ^ m)
          = c j * (e'.prod fun j' m => (c j') ^ m) := by
        rw [← hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _)
          (fun a b₁ b₂ => pow_add _ b₁ b₂),
          Finsupp.prod_single_index (h := fun s' n' => (c s') ^ n') (pow_zero (c j)),
          pow_one]
      have hone : (1 : ℕ∞) ≤ (c j).order :=
        one_le_order_iff_constCoeff_eq_zero.mpr (hc0 j)
      have hord' : ((n - 1 : ℕ) : ℕ∞) ≤ (e'.prod fun j' m => (c j') ^ m).order := by
        rw [← hdeg']
        exact le_order_finsuppProd_pow hc0 e'
      have hcomp : homogeneousComponent n (c j * e'.prod fun j' m => (c j') ^ m)
          = homogeneousComponent 1 (c j)
            * homogeneousComponent (n - 1) (e'.prod fun j' m => (c j') ^ m) := by
        have hmul := homogeneousComponent_mul_of_le_order (f := c j)
          (g := e'.prod fun j' m => (c j') ^ m) hone hord'
        rwa [show 1 + (n - 1) = n by omega] at hmul
      have hXj : homogeneousComponent 1 (c j) = monomial (Finsupp.single j 1) (1 : R) := by
        ext d
        rw [coeff_homogeneousComponent, coeff_monomial]
        by_cases hd : d.degree = 1
        · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
            have hmem : d ∈ {d' : σ →₀ ℕ | d'.degree = 1} := hd
            rw [← Finsupp.range_single_one] at hmem
            exact hmem
          rw [if_pos hd, hc1 j a]
          by_cases hja : j = a
          · subst hja
            simp
          · rw [if_neg hja, if_neg]
            intro hcon
            exact hja (Finsupp.single_left_injective one_ne_zero hcon).symm
        · rw [if_neg hd, if_neg]
          intro hcon
          subst hcon
          exact hd (Finsupp.degree_single j 1)
      rw [hP, hcomp, hXj, IH (n - 1) (by omega) e' hdeg', monomial_mul_monomial, one_mul,
        hsplit]

theorem coeff_finsuppProd_pow_of_degree_eq [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    {d e : σ →₀ ℕ} (hde : d.degree = e.degree) :
    coeff d (e.prod fun j n => (c j) ^ n) = if d = e then 1 else 0 := by
  classical
  have h1 := congrArg (coeff d) (homogeneousComponent_finsuppProd_pow hc0 hc1 e)
  rwa [coeff_homogeneousComponent, if_pos hde, coeff_monomial] at h1

theorem eq_zero_of_subst_eq_zero [Finite σ] [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    {p : MvPowerSeries σ R} (hp : subst c p = 0) : p = 0 := by
  classical
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  have key : ∀ n : ℕ, ∀ d : σ →₀ ℕ, d.degree = n → coeff d p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro d hd
      have h0 : coeff d (subst c p) = 0 := by rw [hp, map_zero]
      rw [coeff_subst hsc] at h0
      rw [finsum_eq_single _ d (fun e hne => ?_)] at h0
      · rwa [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 rfl, if_pos rfl, smul_eq_mul,
          mul_one] at h0
      · rcases lt_trichotomy e.degree n with hlt | heq | hgt
        · rw [IH e.degree hlt e rfl, zero_smul]
        · rw [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 (by rw [hd, heq]),
            if_neg (fun hcon => hne hcon.symm), smul_zero]
        · have horder : ((Finsupp.degree d : ℕ) : ℕ∞)
              < (e.prod fun s' n' => (c s') ^ n').order := by
            refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hc0 e)
            rw [hd]
            exact_mod_cast hgt
          have hcz : coeff d (e.prod fun s' n' => (c s') ^ n') = 0 :=
            coeff_of_lt_order horder
          rw [hcz, smul_zero]
  ext d
  rw [map_zero]
  exact key d.degree d rfl

theorem subst_injective [Finite σ] [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0) :
    Function.Injective (subst (R := R) c) := by
  intro p q hpq
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  have hz : subst c (p - q) = 0 := by
    rw [← coe_substAlgHom hsc, map_sub, coe_substAlgHom hsc, hpq, sub_self]
  have := eq_zero_of_subst_eq_zero hc0 hc1 hz
  exact sub_eq_zero.mp this

theorem coeff_single_subst {σ' : Type*} [Fintype σ'] {c : σ' → MvPowerSeries τ R}
    (hc0 : ∀ s, (c s).constantCoeff = 0) (q : MvPowerSeries σ' R) (t : τ) :
    coeff (Finsupp.single t 1) (subst c q)
      = ∑ s : σ', coeff (Finsupp.single s 1) q * coeff (Finsupp.single t 1) (c s) := by
  classical
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : σ' => Finsupp.single s 1) (fun e he => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    show coeff (Finsupp.single s 1) q
        • coeff (Finsupp.single t 1) ((Finsupp.single s 1).prod fun s' n => (c s') ^ n)
      = coeff (Finsupp.single s 1) q * coeff (Finsupp.single t 1) (c s)
    rw [Finsupp.prod_single_index (h := fun s' n' => (c s') ^ n') (pow_zero (c s)),
      pow_one, smul_eq_mul]
  · by_contra hmem
    apply he
    rcases Nat.lt_trichotomy e.degree 1 with hlt | heq | hgt
    · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst he0
      rw [Finsupp.prod_zero_index, coeff_one,
        if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), smul_zero]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = e := by
        have hmem' : e ∈ {d' : σ' →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have horder : (((Finsupp.single t 1).degree : ℕ) : ℕ∞)
          < (e.prod fun s' n' => (c s') ^ n').order := by
        refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hc0 e)
        rw [Finsupp.degree_single]
        exact_mod_cast hgt
      have hcz : coeff (Finsupp.single t 1) (e.prod fun s' n' => (c s') ^ n') = 0 :=
        coeff_of_lt_order horder
      rw [hcz, smul_zero]

end Subst

section LinearPart

@[simp]
theorem linearPart_zero :
    linearPart (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) = 0 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.zero_apply]
  exact map_zero _

@[simp]
theorem linearPart_X :
    linearPart (fun i : Fin g => (X i : MvPowerSeries (Fin g) R)) = 1 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.one_apply]
  rw [coeff_X]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg (fun hcon => hij (Finsupp.single_left_injective one_ne_zero hcon).symm),
      if_neg hij]

theorem linearPart_subst {m n : ℕ} {b : Fin m → MvPowerSeries (Fin n) R}
    (hb : ∀ s, (b s).constantCoeff = 0) (a : Fin h → MvPowerSeries (Fin m) R) :
    linearPart (fun i => subst b (a i)) = linearPart a * linearPart b := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.mul_apply]
  exact coeff_single_subst hb (a i) j

theorem linearPart_subst_elim {m : ℕ} (F : MvFormalGroup g R)
    {a b : Fin g → MvPowerSeries (Fin m) R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    linearPart (fun i => subst (Sum.elim a b) (F.toPowerSeries i))
      = linearPart a + linearPart b := by
  classical
  have hab : ∀ s : Fin g ⊕ Fin g, ((Sum.elim a b) s).constantCoeff = 0 := by
    rintro (s | s)
    exacts [ha s, hb s]
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.add_apply]
  rw [coeff_single_subst hab (F.toPowerSeries i) j, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

end LinearPart

section Transport

variable {τ : Type*} (F : MvFormalGroup g R)

theorem hasSubst_elim {n : ℕ} {τ' : Type*} {a b : Fin n → MvPowerSeries τ' R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    HasSubst (Sum.elim a b) :=
  hasSubst_of_constantCoeff_zero (by rintro (s | s); exacts [ha s, hb s])

theorem constantCoeff_subst_elim {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) (i : Fin g) :
    (subst (Sum.elim a b) (F.toPowerSeries i)).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim ha hb)
    (by rintro (s | s); exacts [ha s, hb s]) (F.constantCoeff_eq_zero i)

theorem subst_elim_assoc {a b c : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c)
        (F.toPowerSeries i)
      = subst (Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j))
        (F.toPowerSeries i) := by
  have hT0 : ∀ s : Fin g ⊕ (Fin g ⊕ Fin g),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
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
  have key := congrArg (subst (R := R) (Sum.elim a (Sum.elim b c))) (F.assoc i)
  rw [subst_comp_subst_apply hA hT, subst_comp_subst_apply hA' hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hA'fam] at key
  exact key

theorem subst_elim_comm [IsComm F] {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a b) (F.toPowerSeries i)
      = subst (Sum.elim b a) (F.toPowerSeries i) := by
  have hT : HasSubst (Sum.elim b a) := hasSubst_elim hb ha
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := R) (Sum.elim b a)) (IsComm.comm (F := F) i)
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim b a) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) = Sum.elim a b := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  exact key

theorem subst_elim_exchange [IsComm F] {a b c d : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j))
        fun j => subst (Sum.elim c d) (F.toPowerSeries j)) (F.toPowerSeries i)
      = subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j))
        fun j => subst (Sum.elim b d) (F.toPowerSeries j)) (F.toPowerSeries i) := by
  have hcd : ∀ j, (subst (Sum.elim c d) (F.toPowerSeries j)).constantCoeff = 0 :=
    constantCoeff_subst_elim F hc hd
  have hbd : ∀ j, (subst (Sum.elim b d) (F.toPowerSeries j)).constantCoeff = 0 :=
    constantCoeff_subst_elim F hb hd
  rw [subst_elim_assoc F ha hb hcd i]
  have hinner : ∀ j, subst (Sum.elim b fun j' => subst (Sum.elim c d) (F.toPowerSeries j'))
      (F.toPowerSeries j)
      = subst (Sum.elim c fun j' => subst (Sum.elim b d) (F.toPowerSeries j'))
        (F.toPowerSeries j) := by
    intro j
    rw [← subst_elim_assoc F hb hc hd j]
    have hswap : (fun j' => subst (Sum.elim b c) (F.toPowerSeries j'))
        = fun j' => subst (Sum.elim c b) (F.toPowerSeries j') :=
      funext fun j' => subst_elim_comm F hb hc j'
    rw [hswap]
    exact subst_elim_assoc F hc hb hd j
  have houter : (fun j => subst (Sum.elim b fun j' => subst (Sum.elim c d)
      (F.toPowerSeries j')) (F.toPowerSeries j))
      = fun j => subst (Sum.elim c fun j' => subst (Sum.elim b d) (F.toPowerSeries j'))
        (F.toPowerSeries j) :=
    funext hinner
  rw [houter]
  exact (subst_elim_assoc F ha hc hbd i).symm

end Transport

section Unit

variable (F : MvFormalGroup g R)

theorem eq_X_of_subst_self {σ : Type*} [Finite σ] [DecidableEq σ]
    {u : σ → MvPowerSeries σ R}
    (hu0 : ∀ j, (u j).constantCoeff = 0)
    (hu1 : ∀ j j', coeff (Finsupp.single j' 1) (u j) = if j = j' then 1 else 0)
    (hidem : ∀ j, subst u (u j) = u j) (i : σ) : u i = X i := by
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hv : subst u (u i - X i) = 0 := by
    rw [← coe_substAlgHom hsu, map_sub, coe_substAlgHom hsu, hidem i, subst_X hsu,
      sub_self]
  exact sub_eq_zero.mp (eq_zero_of_subst_eq_zero hu0 hu1 hv)

theorem subst_elim_X_zero (i : Fin g) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R)) fun _ => 0)
      (F.toPowerSeries i) = X i := by
  have hXz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
      fun _ => (0 : MvPowerSeries (Fin g) R)) s).constantCoeff = 0 := by
    rintro (j | j)
    · simp [constantCoeff_X]
    · simp
  have hzero : ∀ j : Fin g,
      ((fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have hu0 : ∀ j, (subst (Sum.elim (fun j' => (X j' : MvPowerSeries (Fin g) R)) fun _ => 0)
      (F.toPowerSeries j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXz) hXz
      (F.constantCoeff_eq_zero j)
  have hu1 : ∀ j j', coeff (Finsupp.single j' 1)
      (subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j)) = if j = j' then 1 else 0 := by
    have hlin := linearPart_subst_elim F (a := fun j => (X j : MvPowerSeries (Fin g) R))
      (b := fun _ => 0) (fun j => constantCoeff_X j) (fun _ => map_zero _)
    rw [linearPart_X, linearPart_zero, add_zero] at hlin
    intro j j'
    simpa [linearPart, Matrix.of_apply, Matrix.one_apply]
      using congrFun (congrFun hlin j) j'
  have hz2 : (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      = fun _ : Fin g ⊕ Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext s
    rcases s with s | s <;> rfl
  have hFzz : (fun j => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ => 0) (F.toPowerSeries j)) = fun _ : Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext j
    rw [hz2]
    exact subst_zero_of_constantCoeff_eq_zero (F.constantCoeff_eq_zero j)
  have hsu2 : HasSubst (Sum.elim (fun j' => (X j' : MvPowerSeries (Fin g) R)) fun _ => 0) :=
    hasSubst_of_constantCoeff_zero hXz
  have hsut : HasSubst (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j')) :=
    hasSubst_of_constantCoeff_zero hu0
  have hassoc' : ∀ j, subst (Sum.elim (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
      fun _ => 0) (F.toPowerSeries j)
      = subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j) := by
    intro j
    have h1 := subst_elim_assoc F (a := fun j'' => (X j'' : MvPowerSeries (Fin g) R))
      (b := fun _ => 0) (c := fun _ => 0) (fun j'' => constantCoeff_X j'') hzero hzero j
    rwa [hFzz] at h1
  have hidem : ∀ j, subst (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
      (subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j))
      = subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j) := by
    intro j
    rw [subst_comp_subst_apply hsu2 hsut]
    have hfam : (fun s => subst (fun j' => subst (Sum.elim
        (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
        ((Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R))
          (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))) s))
        = Sum.elim (fun j' => subst (Sum.elim
            (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
            (F.toPowerSeries j')) (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) := by
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl]
        exact subst_X hsut j'
      · simp only [Sum.elim_inr]
        rw [← coe_substAlgHom hsut, map_zero]
    rw [hfam]
    exact hassoc' j
  exact eq_X_of_subst_self hu0 hu1 hidem i

theorem subst_elim_zero_X (i : Fin g) :
    subst (Sum.elim (fun _ => 0) fun j => (X j : MvPowerSeries (Fin g) R))
      (F.toPowerSeries i) = X i := by
  have hzX : ∀ s : Fin g ⊕ Fin g, ((Sum.elim (fun _ => (0 : MvPowerSeries (Fin g) R))
      fun j => (X j : MvPowerSeries (Fin g) R)) s).constantCoeff = 0 := by
    rintro (j | j)
    · simp
    · simp [constantCoeff_X]
  have hzero : ∀ j : Fin g,
      ((fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have hu0 : ∀ j, (subst (Sum.elim (fun _ => 0) fun j' => (X j' : MvPowerSeries (Fin g) R))
      (F.toPowerSeries j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzX) hzX
      (F.constantCoeff_eq_zero j)
  have hu1 : ∀ j j', coeff (Finsupp.single j' 1)
      (subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j)) = if j = j' then 1 else 0 := by
    have hlin := linearPart_subst_elim F (a := fun _ => 0)
      (b := fun j => (X j : MvPowerSeries (Fin g) R)) (fun _ => map_zero _)
      (fun j => constantCoeff_X j)
    rw [linearPart_X, linearPart_zero, zero_add] at hlin
    intro j j'
    simpa [linearPart, Matrix.of_apply, Matrix.one_apply]
      using congrFun (congrFun hlin j) j'
  have hz2 : (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      = fun _ : Fin g ⊕ Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext s
    rcases s with s | s <;> rfl
  have hFzz : (fun j => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ => 0) (F.toPowerSeries j)) = fun _ : Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext j
    rw [hz2]
    exact subst_zero_of_constantCoeff_eq_zero (F.constantCoeff_eq_zero j)
  have hsu2 : HasSubst (Sum.elim (fun _ => (0 : MvPowerSeries (Fin g) R))
      fun j' => (X j' : MvPowerSeries (Fin g) R)) :=
    hasSubst_of_constantCoeff_zero hzX
  have hsut : HasSubst (fun j' => subst (Sum.elim (fun _ => 0)
      fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j')) :=
    hasSubst_of_constantCoeff_zero hu0
  have hassoc' : ∀ j, subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun j' => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
        fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j')) (F.toPowerSeries j)
      = subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
        fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j) := by
    intro j
    have h1 := subst_elim_assoc F (a := fun _ => 0) (b := fun _ => 0)
      (c := fun j'' => (X j'' : MvPowerSeries (Fin g) R)) hzero hzero
      (fun j'' => constantCoeff_X j'') j
    rw [hFzz] at h1
    exact h1.symm
  have hidem : ∀ j, subst (fun j' => subst (Sum.elim (fun _ => 0)
      fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j'))
      (subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j))
      = subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j) := by
    intro j
    rw [subst_comp_subst_apply hsu2 hsut]
    have hfam : (fun s => subst (fun j' => subst (Sum.elim (fun _ => 0)
        fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j'))
        ((Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          fun j'' => (X j'' : MvPowerSeries (Fin g) R)) s))
        = Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
            fun j' => subst (Sum.elim (fun _ => 0)
              fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j') := by
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl]
        rw [← coe_substAlgHom hsut, map_zero]
      · simp only [Sum.elim_inr]
        exact subst_X hsut j'
    rw [hfam]
    exact hassoc' j
  exact eq_X_of_subst_self hu0 hu1 hidem i

end Unit

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) : Hom F G where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    show subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R)
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
      · show subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXl, map_zero]
      · show subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXr, map_zero]
    rw [hL, hfam,
      subst_zero_of_constantCoeff_eq_zero (G.constantCoeff_eq_zero i)]

@[simp]
theorem toPowerSeries_zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) :
    (Hom.zero F G).toPowerSeries = fun _ => 0 := rfl

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
    show subst F.toPowerSeries
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
      · show subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXl, hfinL]
      · show subst (Sum.elim
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
    show subst (Sum.elim
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
    show subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i)
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
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
    have h1 : subst a.toPowerSeries (subst (Sum.elim (fun _ => 0)
        fun j => (X j : MvPowerSeries (Fin h) R)) (G.toPowerSeries i))
        = subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply h0X hsa, hfam]
    rw [← h1, subst_elim_zero_X G i, subst_X hsa]
  add_zero a := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i)
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
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
    have h1 : subst a.toPowerSeries (subst (Sum.elim
        (fun j => (X j : MvPowerSeries (Fin h) R)) fun _ => 0) (G.toPowerSeries i))
        = subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply hX0 hsa, hfam]
    rw [← h1, subst_elim_X_zero G i, subst_X hsa]
  add_comm a b := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim b.toPowerSeries a.toPowerSeries) (G.toPowerSeries i)
    exact subst_elim_comm G a.constantCoeff_eq_zero b.constantCoeff_eq_zero i

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instMonoid : Monoid (End F) where
  mul φ ψ := Hom.comp φ ψ
  one := Hom.id F
  mul_assoc φ ψ χ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries χ) (subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i))
      = subst (fun j => subst (Hom.toPowerSeries χ) (Hom.toPowerSeries ψ j))
        (Hom.toPowerSeries φ i)
    rw [subst_comp_subst_apply (Hom.hasSubst_toPowerSeries ψ)
      (Hom.hasSubst_toPowerSeries χ)]
  one_mul φ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries φ) (X i) = Hom.toPowerSeries φ i
    exact subst_X (Hom.hasSubst_toPowerSeries φ) i
  mul_one φ := by
    apply Hom.ext
    funext i
    show subst (fun j => (X j : MvPowerSeries (Fin g) R)) (Hom.toPowerSeries φ i)
      = Hom.toPowerSeries φ i
    exact congrFun subst_self (Hom.toPowerSeries φ i)

@[simp]
theorem toPowerSeries_one :
    Hom.toPowerSeries (1 : End F) = fun i => (X i : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_mul (φ ψ : End F) :
    Hom.toPowerSeries (φ * ψ)
      = fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i) := rfl

instance instAddCommMonoid [IsComm F] : AddCommMonoid (End F) :=
  inferInstanceAs (AddCommMonoid (Hom F F))

instance instSemiring [IsComm F] : Semiring (End F) :=
  { End.instAddCommMonoid F, End.instMonoid F with
    left_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (fun j => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          (F.toPowerSeries j)) (Hom.toPowerSeries a i)
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
          (F.toPowerSeries i)
      have hbc : HasSubst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero b) (Hom.constantCoeff_eq_zero c)
      have hXl : HasSubst (fun l : Fin g =>
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hXr : HasSubst (fun l : Fin g =>
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have haLR : HasSubst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j)) :=
        hasSubst_elim
          (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j))
          fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j)
      rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries hbc, Hom.subst_eq a i,
        subst_comp_subst_apply haLR hbc]
      have hbfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inl l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries b := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inl l)) = Hom.toPowerSeries b l
        rw [subst_X hbc]
        rfl
      have hcfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inr l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries c := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inr l)) = Hom.toPowerSeries c l
        rw [subst_X hbc]
        rfl
      have hfam : (fun s => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j) := by
        funext s
        rcases s with j | j
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXl hbc, hbfam]
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXr hbc, hcfam]
      rw [hfam]
    right_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries c)
          (subst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b))
            (F.toPowerSeries i))
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j))
          (F.toPowerSeries i)
      have hab : HasSubst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero a) (Hom.constantCoeff_eq_zero b)
      rw [subst_comp_subst_apply hab (Hom.hasSubst_toPowerSeries c)]
      have hfam : (fun s => subst (Hom.toPowerSeries c)
          ((Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [hfam]
    zero_mul := fun a => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries a) (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom (Hom.hasSubst_toPowerSeries a), map_zero]
    mul_zero := fun a => by
      apply Hom.ext
      funext i
      show subst (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          (Hom.toPowerSeries a i) = 0
      exact subst_zero_of_constantCoeff_eq_zero (Hom.constantCoeff_eq_zero a i) }

@[simp]
theorem toPowerSeries_natCast [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((n : End F)) = F.nthSeries n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, nthSeries_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ]
    funext i
    show subst (Sum.elim (Hom.toPowerSeries ((n : End F)))
        (Hom.toPowerSeries (1 : End F))) (F.toPowerSeries i)
      = F.nthSeries (n + 1) i
    rw [ih, nthSeries_succ]
    rfl

@[simp]
theorem toPowerSeries_zero [IsComm F] :
    Hom.toPowerSeries (0 : End F) = fun _ => (0 : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_add [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ + ψ)
      = fun i => subst (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ))
        (F.toPowerSeries i) := rfl

end End

theorem constantCoeff_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    ∀ i, (F.nthSeries n i).constantCoeff = 0 := by
  induction n with
  | zero =>
    intro i
    rw [nthSeries_zero]
    exact map_zero _
  | succ n ih =>
    intro i
    rw [nthSeries_succ]
    exact constantCoeff_subst_elim F ih (fun j => constantCoeff_X j) i

theorem linearPart_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    linearPart (F.nthSeries n) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  induction n with
  | zero =>
    rw [nthSeries_zero, zero_smul]
    exact linearPart_zero
  | succ n ih =>
    rw [nthSeries_succ,
      linearPart_subst_elim F (constantCoeff_nthSeries F n) (fun j => constantCoeff_X j),
      ih, linearPart_X, succ_nsmul]

def linearPartHom (F : MvFormalGroup g R) [IsComm F] :
    End F →+* Matrix (Fin g) (Fin g) R where
  toFun φ := linearPart (Hom.toPowerSeries φ)
  map_one' := by
    show linearPart (fun i => (X i : MvPowerSeries (Fin g) R)) = 1
    exact linearPart_X
  map_mul' φ ψ := by
    show linearPart (fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i)) = _
    exact linearPart_subst (Hom.constantCoeff_eq_zero ψ) (Hom.toPowerSeries φ)
  map_zero' := by
    show linearPart (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) = 0
    exact linearPart_zero
  map_add' φ ψ := by
    show linearPart (fun i => subst
        (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ)) (F.toPowerSeries i)) = _
    exact linearPart_subst_elim F (Hom.constantCoeff_eq_zero φ)
      (Hom.constantCoeff_eq_zero ψ)

@[simp]
theorem linearPartHom_apply (F : MvFormalGroup g R) [IsComm F] (φ : End F) :
    linearPartHom F φ = linearPart (Hom.toPowerSeries φ) := rfl

@[simp]
theorem linearPartHom_natCast (F : MvFormalGroup g R) [IsComm F] (n : ℕ) :
    linearPartHom F ((n : End F)) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [linearPartHom_apply, End.toPowerSeries_natCast, linearPart_nthSeries]

end MvFormalGroup

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section Congr

variable {τ : Type*}

theorem coeff_pow_congr {c c' : MvPowerSeries τ R} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e c = coeff e c') {k : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (c ^ k) = coeff d (c' ^ k) := by
  classical
  induction k generalizing d with
  | zero => rfl
  | succ k IH =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_right _ _
    have h2 : p.2.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_left _ _
    rw [IH h1, h p.2 h2]

theorem coeff_finsuppProd_pow_congr {σ' : Type*} {c c' : σ' → MvPowerSeries τ R} {n : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (c j) = coeff e (c' j))
    (m : σ' →₀ ℕ) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => simp
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _),
      coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : p.1.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_right _ _
    have h2 : p.2.degree ≤ n := by
      refine le_trans ?_ hd
      rw [← hp, map_add]
      exact Nat.le_add_left _ _
    rw [coeff_pow_congr (h j) h1, IH h2]

theorem coeff_subst_congr {σ' : Type*} [Finite σ'] {c c' : σ' → MvPowerSeries τ R}
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0) {n : ℕ}
    (h : ∀ j, ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (c j) = coeff e (c' j))
    (f : MvPowerSeries σ' R) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (subst c f) = coeff d (subst c' f) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hc),
    coeff_subst (hasSubst_of_constantCoeff_zero hc')]
  exact finsum_congr fun m => by
    rw [coeff_finsuppProd_pow_congr h m hd]

end Congr

section Vanish

variable {τ : Type*}

theorem coeff_pow_eq_zero_of_degree_lt {c : MvPowerSeries τ R}
    (hc : c.constantCoeff = 0) {l : ℕ} {d : τ →₀ ℕ} (hd : d.degree < l) :
    coeff d (c ^ l) = 0 := by
  classical
  induction l generalizing d with
  | zero => omega
  | succ l IH =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1.degree < l
    · rw [IH h1, zero_mul]
    · have h2 : p.2 = 0 := by
        by_contra h2
        have : 1 ≤ p.2.degree := by
          rcases Nat.eq_zero_or_pos p.2.degree with hz | hpos
          · exact absurd ((Finsupp.degree_eq_zero_iff p.2).mp hz) h2
          · exact hpos
        have hdd : p.1.degree + p.2.degree = d.degree := by
          rw [← hp, map_add]
        omega
      rw [h2, coeff_zero_eq_constantCoeff_apply, hc, mul_zero]

theorem coeff_finsuppProd_pow_eq_zero_of_degree_lt {σ' : Type*}
    {c : σ' → MvPowerSeries τ R} (hc : ∀ j, (c j).constantCoeff = 0)
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree < m.degree) :
    coeff d (m.prod fun j l => c j ^ l) = 0 := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero =>
    rw [(Finsupp.degree_eq_zero_iff (0 : σ' →₀ ℕ)).mpr rfl] at hd
    omega
  | single_add j l m hjm hl IH =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _), coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdd : p.1.degree + p.2.degree = d.degree := by
      rw [← hp, map_add]
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    by_cases h1 : p.1.degree < l
    · rw [coeff_pow_eq_zero_of_degree_lt (hc j) h1, zero_mul]
    · have h2 : p.2.degree < m.degree := by omega
      rw [IH h2, mul_zero]

end Vanish

section SubCongr

variable {τ : Type*}

theorem coeff_mul_congr_right {u c c' : MvPowerSeries τ R} {K r : ℕ}
    (hu : ∀ e : τ →₀ ℕ, e.degree < r → coeff e u = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree ≤ K → coeff e c = coeff e c')
    {d : τ →₀ ℕ} (hd : d.degree ≤ K + r) :
    coeff d (u * c) = coeff d (u * c') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdd : p.1.degree + p.2.degree = d.degree := by
    rw [← hp, map_add]
  by_cases h1 : p.1.degree < r
  · rw [hu p.1 h1, zero_mul, zero_mul]
  · rw [hcc p.2 (by omega)]

theorem coeff_pow_sub_congr {c c' : MvPowerSeries τ R} {N : ℕ} (hN : 1 ≤ N)
    (hc : c.constantCoeff = 0) (hc' : c'.constantCoeff = 0)
    (hcc : ∀ e : τ →₀ ℕ, e.degree < N → coeff e c = coeff e c') {l : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ N + l - 2) :
    coeff d (c ^ l) = coeff d (c' ^ l) := by
  classical
  induction l generalizing d with
  | zero => rw [pow_zero, pow_zero]
  | succ l IH =>
    rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · subst hl0
      rw [pow_one, pow_one]
      exact hcc d (by omega)
    · have step1 : coeff d (c ^ (l + 1)) = coeff d (c ^ l * c') := by
        rw [pow_succ]
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e (c ^ l) = 0 :=
          fun e he => coeff_pow_eq_zero_of_degree_lt hc he
        exact coeff_mul_congr_right (K := N - 1) (r := l) hvanish
          (fun e he => hcc e (by omega)) (by omega)
      have step2 : coeff d (c ^ l * c') = coeff d (c' ^ l * c') := by
        rw [mul_comm (c ^ l) c', mul_comm (c' ^ l) c']
        have hvanish : ∀ e : τ →₀ ℕ, e.degree < 1 → coeff e c' = 0 := by
          intro e he
          have he0 : e = 0 := by
            rcases Nat.eq_zero_or_pos e.degree with hz | hpos
            · exact (Finsupp.degree_eq_zero_iff e).mp hz
            · omega
          subst he0
          rw [coeff_zero_eq_constantCoeff_apply, hc']
        exact coeff_mul_congr_right (K := N + l - 2) (r := 1) hvanish
          (fun e he => IH he) (by omega)
      rw [step1, step2, ← pow_succ]

theorem coeff_finsuppProd_pow_sub_congr {σ' : Type*} {c c' : σ' → MvPowerSeries τ R}
    {N : ℕ} (hN : 1 ≤ N)
    (hc : ∀ j, (c j).constantCoeff = 0) (hc' : ∀ j, (c' j).constantCoeff = 0)
    (hcc : ∀ j, ∀ e : τ →₀ ℕ, e.degree < N → coeff e (c j) = coeff e (c' j))
    {m : σ' →₀ ℕ} {d : τ →₀ ℕ} (hd : d.degree ≤ N + m.degree - 2) :
    coeff d (m.prod fun j l => c j ^ l) = coeff d (m.prod fun j l => c' j ^ l) := by
  classical
  induction m using Finsupp.induction generalizing d with
  | zero => rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index]
  | single_add j l m hjm hl IH =>
    have hsum : (Finsupp.single j l + m).degree = l + m.degree := by
      rw [map_add, Finsupp.degree_single]
    rw [hsum] at hd
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _)]
    have step1 : coeff d ((c j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l') := by
      rw [mul_comm ((c j) ^ l) _, mul_comm ((c' j) ^ l) _]
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < m.degree →
          coeff e (m.prod fun j' l' => c j' ^ l') = 0 :=
        fun e he => coeff_finsuppProd_pow_eq_zero_of_degree_lt hc he
      exact coeff_mul_congr_right (K := N + l - 2) (r := m.degree) hvanish
        (fun e he => coeff_pow_sub_congr hN (hc j) (hc' j) (hcc j) he) (by omega)
    have step2 : coeff d ((c' j) ^ l * m.prod fun j' l' => c j' ^ l')
        = coeff d ((c' j) ^ l * m.prod fun j' l' => c' j' ^ l') := by
      have hvanish : ∀ e : τ →₀ ℕ, e.degree < l → coeff e ((c' j) ^ l) = 0 :=
        fun e he => coeff_pow_eq_zero_of_degree_lt (hc' j) he
      exact coeff_mul_congr_right (K := N + m.degree - 2) (r := l) hvanish
        (fun e he => IH he) (by omega)
    rw [step1, step2]

end SubCongr

section UnitGeneral

variable {τ : Type*} (F : MvFormalGroup g R)

theorem subst_elim_zero_right {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a fun _ => 0) (F.toPowerSeries i) = a i := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hX0 : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
      (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) :=
    hasSubst_elim (fun j => constantCoeff_X j) fun _ => map_zero _
  have hfam : (fun s : Fin g ⊕ Fin g => subst a
      ((Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
        (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) s))
      = (Sum.elim a (fun _ => 0) : Fin g ⊕ Fin g → MvPowerSeries τ R) := by
    funext s
    rcases s with j | j
    · show subst a (X j) = a j
      exact subst_X hsa j
    · show subst a (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom hsa, map_zero]
  rw [← hfam, ← subst_comp_subst_apply hX0 hsa, subst_elim_X_zero F i, subst_X hsa]

theorem subst_elim_zero_left {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun _ => 0) a) (F.toPowerSeries i) = a i := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h0X : HasSubst (Sum.elim (fun _ => 0)
      (fun j => (X j : MvPowerSeries (Fin g) R)) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) :=
    hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
  have hfam : (fun s : Fin g ⊕ Fin g => subst a
      ((Sum.elim (fun _ => 0)
        (fun j => (X j : MvPowerSeries (Fin g) R)) : Fin g ⊕ Fin g → MvPowerSeries (Fin g) R) s))
      = (Sum.elim (fun _ => 0) a : Fin g ⊕ Fin g → MvPowerSeries τ R) := by
    funext s
    rcases s with j | j
    · show subst a (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom hsa, map_zero]
    · show subst a (X j) = a j
      exact subst_X hsa j
  rw [← hfam, ← subst_comp_subst_apply h0X hsa, subst_elim_zero_X F i, subst_X hsa]

end UnitGeneral

section Perturb

variable {τ : Type*} (F : MvFormalGroup g R)

theorem coeff_subst_elim_sub_homogeneous {a y E : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    {N : ℕ} (hN : 1 ≤ N) (hE : ∀ j, ∀ e : τ →₀ ℕ, coeff e (E j) ≠ 0 → e.degree = N)
    {d : τ →₀ ℕ} (hd : d.degree ≤ N) (i : Fin g) :
    coeff d (subst (Sum.elim a fun j => y j - E j) (F.toPowerSeries i))
      = coeff d (subst (Sum.elim a y) (F.toPowerSeries i)) - coeff d (E i) := by
  classical
  have hE0 : ∀ j, (E j).constantCoeff = 0 := by
    intro j
    by_contra hcon
    have h1 : coeff (0 : τ →₀ ℕ) (E j) ≠ 0 := by
      rwa [coeff_zero_eq_constantCoeff_apply]
    have h2 := hE j 0 h1
    rw [(Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl] at h2
    omega
  have hfam : ∀ s : Fin g ⊕ Fin g,
      ((Sum.elim a fun j => y j - E j) s).constantCoeff = 0 := by
    rintro (j | j)
    · exact ha j
    · show (y j - E j).constantCoeff = 0
      rw [map_sub, hy j, hE0 j, sub_zero]
  have hfam' : ∀ s : Fin g ⊕ Fin g, ((Sum.elim a y) s).constantCoeff = 0 := by
    rintro (j | j)
    exacts [ha j, hy j]

  have key : ∀ m : (Fin g ⊕ Fin g) →₀ ℕ,
      coeff d (m.prod fun s l => (Sum.elim a fun j => y j - E j) s ^ l)
        = coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)
          - ∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0 := by
    intro m
    by_cases hm : ∃ j : Fin g, m = Finsupp.single (Sum.inr j) 1
    · obtain ⟨j, rfl⟩ := hm
      rw [Finsupp.prod_single_index
          (h := fun s l => (Sum.elim a fun j' => y j' - E j') s ^ l) (pow_zero _),
        Finsupp.prod_single_index (h := fun s l => (Sum.elim a y) s ^ l) (pow_zero _),
        pow_one, pow_one, Finset.sum_eq_single j
          (fun j' _ hj' => if_neg fun hcon =>
            hj' (Sum.inr_injective (Finsupp.single_left_injective one_ne_zero hcon.symm)))
          (fun hcon => absurd (Finset.mem_univ j) hcon), if_pos rfl]
      show coeff d (y j - E j) = coeff d (y j) - coeff d (E j)
      rw [map_sub]
    · rw [Finset.sum_eq_zero (fun j _ => if_neg fun hcon => hm ⟨j, hcon⟩), sub_zero]
      rcases Nat.lt_or_ge m.degree 2 with hm2 | hm2
      · rcases Nat.lt_or_ge m.degree 1 with hm1 | hm1
        · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
          subst hm0
          rw [Finsupp.prod_zero_index, Finsupp.prod_zero_index]
        · have hmem : m ∈ {d' : (Fin g ⊕ Fin g) →₀ ℕ | d'.degree = 1} := by
            show m.degree = 1
            omega
          rw [← Finsupp.range_single_one] at hmem
          obtain ⟨s, hs⟩ := hmem
          have hs' : Finsupp.single s 1 = m := hs
          rcases s with j | j
          · rw [← hs', Finsupp.prod_single_index
                (h := fun s' l => (Sum.elim a fun j' => y j' - E j') s' ^ l) (pow_zero _),
              Finsupp.prod_single_index (h := fun s' l => (Sum.elim a y) s' ^ l)
                (pow_zero _), pow_one, pow_one]
            rfl
          · exact absurd ⟨j, hs'.symm⟩ hm
      · have hcc : ∀ s : Fin g ⊕ Fin g, ∀ e : τ →₀ ℕ, e.degree < N →
            coeff e ((Sum.elim a fun j => y j - E j) s) = coeff e ((Sum.elim a y) s) := by
          rintro (j | j) e he
          · rfl
          · show coeff e (y j - E j) = coeff e (y j)
            have hEe : coeff e (E j) = 0 := by
              by_contra hcon
              have := hE j e hcon
              omega
            rw [map_sub, hEe, sub_zero]
        exact coeff_finsuppProd_pow_sub_congr hN hfam hfam' hcc (by omega)

  have hsplit : (fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • coeff d (m.prod fun s l => (Sum.elim a fun j => y j - E j) s ^ l))
      = fun m =>
        coeff m (F.toPowerSeries i) • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)
          - coeff m (F.toPowerSeries i)
            • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) := by
    funext m
    rw [key m, smul_sub]
  have hfin1 : (Function.support fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l)).Finite := by
    refine Set.Finite.subset (Finsupp.finite_of_degree_le (σ := Fin g ⊕ Fin g) d.degree) ?_
    intro m hm
    show m.degree ≤ d.degree
    by_contra hcon
    apply hm
    show coeff m (F.toPowerSeries i)
      • coeff d (m.prod fun s l => (Sum.elim a y) s ^ l) = 0
    rw [coeff_finsuppProd_pow_eq_zero_of_degree_lt hfam' (by omega), smul_zero]
  have hfin2 : (Function.support fun m : (Fin g ⊕ Fin g) →₀ ℕ =>
      coeff m (F.toPowerSeries i)
        • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
            then coeff d (E j) else 0)).Finite := by
    refine Set.Finite.subset
      (Set.finite_range fun j : Fin g => Finsupp.single (Sum.inr j) 1) ?_
    intro m hm
    by_contra hmem
    apply hm
    show coeff m (F.toPowerSeries i)
      • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) = 0
    have hz : (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
        then coeff d (E j) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg fun hcon => hmem ⟨j, hcon.symm⟩
    rw [hz, smul_zero]
  have hδ : (∑ᶠ m : (Fin g ⊕ Fin g) →₀ ℕ, coeff m (F.toPowerSeries i)
      • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0))
      = coeff d (E i) := by
    rw [finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun j : Fin g => Finsupp.single (Sum.inr j) 1)
      (fun m hm => ?_),
      Finset.sum_image (fun j _ j' _ hjj =>
        Sum.inr_injective (Finsupp.single_left_injective one_ne_zero hjj))]
    · have hterm : ∀ j : Fin g,
          coeff (Finsupp.single (Sum.inr j) 1) (F.toPowerSeries i)
            • (∑ j' : Fin g, if (Finsupp.single (Sum.inr j) 1 : (Fin g ⊕ Fin g) →₀ ℕ)
                = Finsupp.single (Sum.inr j') 1 then coeff d (E j') else 0)
          = (if i = j then 1 else 0) * coeff d (E j) := by
        intro j
        rw [F.coeff_single_inr i j, Finset.sum_eq_single j
          (fun j' _ hj' => if_neg fun hcon =>
            hj' (Sum.inr_injective
              (Finsupp.single_left_injective one_ne_zero hcon)).symm)
          (fun hcon => absurd (Finset.mem_univ j) hcon), if_pos rfl, smul_eq_mul]
      rw [Finset.sum_congr rfl fun j _ => hterm j,
        Finset.sum_eq_single i
          (fun j _ hj => by rw [if_neg fun hcon => hj hcon.symm, zero_mul])
          (fun hcon => absurd (Finset.mem_univ i) hcon), if_pos rfl, one_mul]
    · by_contra hmem
      apply hm
      show coeff m (F.toPowerSeries i)
        • (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1 then coeff d (E j) else 0) = 0
      have hz : (∑ j : Fin g, if m = Finsupp.single (Sum.inr j) 1
          then coeff d (E j) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg fun hcon => hmem (by
          rw [hcon]
          exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      rw [hz, smul_zero]
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hfam),
    coeff_subst (hasSubst_of_constantCoeff_zero hfam'), hsplit,
    finsum_sub_distrib hfin1 hfin2, hδ]

end Perturb

section NegSeries

variable {τ : Type*} (F : MvFormalGroup g R)

def negApprox (a : Fin g → MvPowerSeries τ R) : ℕ → Fin g → MvPowerSeries τ R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      negApprox a n i
        - homogeneousComponent (n + 1)
            (subst (Sum.elim a (negApprox a n)) (F.toPowerSeries i))

@[simp]
theorem negApprox_zero (a : Fin g → MvPowerSeries τ R) :
    negApprox F a 0 = fun _ => 0 := rfl

theorem negApprox_succ (a : Fin g → MvPowerSeries τ R) (n : ℕ) :
    negApprox F a (n + 1) = fun i =>
      negApprox F a n i
        - homogeneousComponent (n + 1)
            (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) := rfl

theorem constantCoeff_negApprox (a : Fin g → MvPowerSeries τ R) (n : ℕ) (i : Fin g) :
    (negApprox F a n i).constantCoeff = 0 := by
  induction n with
  | zero =>
    show (0 : MvPowerSeries τ R).constantCoeff = 0
    exact map_zero _
  | succ n IH =>
    show (negApprox F a n i - homogeneousComponent (n + 1)
        (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i))).constantCoeff = 0
    have h0 : ((0 : τ →₀ ℕ)).degree = 0 :=
      (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl
    have hne : ((0 : τ →₀ ℕ)).degree ≠ n + 1 := by omega
    rw [map_sub, IH, ← coeff_zero_eq_constantCoeff_apply, coeff_homogeneousComponent,
      if_neg hne, sub_zero]

theorem coeff_subst_elim_negApprox {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) {n : ℕ} {d : τ →₀ ℕ}
    (hdn : d.degree ≤ n) (hd0 : d ≠ 0) (i : Fin g) :
    coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) = 0 := by
  induction n generalizing d with
  | zero =>
    exact absurd ((Finsupp.degree_eq_zero_iff d).mp (Nat.le_zero.mp hdn)) hd0
  | succ n IH =>
    have hy : ∀ j, (negApprox F a n j).constantCoeff = 0 :=
      fun j => constantCoeff_negApprox F a n j
    have hE : ∀ j, ∀ e : τ →₀ ℕ,
        coeff e (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries j))) ≠ 0 →
        e.degree = n + 1 := by
      intro j e hne
      by_contra hcon
      rw [coeff_homogeneousComponent, if_neg hcon] at hne
      exact hne rfl
    rw [negApprox_succ,
      coeff_subst_elim_sub_homogeneous F ha hy (Nat.succ_le_succ (Nat.zero_le n)) hE hdn i]
    rcases Nat.lt_or_ge d.degree (n + 1) with hlt | hge
    · have h1 : coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) = 0 :=
        IH (by omega) hd0
      have h2 : coeff d (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i))) = 0 := by
        rw [coeff_homogeneousComponent, if_neg (by omega)]
      rw [h1, h2, sub_zero]
    · have hdeq : d.degree = n + 1 := by omega
      have h2 : coeff d (homogeneousComponent (n + 1)
          (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)))
          = coeff d (subst (Sum.elim a (negApprox F a n)) (F.toPowerSeries i)) := by
        rw [coeff_homogeneousComponent, if_pos hdeq]
      rw [h2, sub_self]

theorem coeff_negApprox_stable (a : Fin g → MvPowerSeries τ R) {n m : ℕ}
    (hnm : n ≤ m) {d : τ →₀ ℕ} (hd : d.degree ≤ n) (i : Fin g) :
    coeff d (negApprox F a m i) = coeff d (negApprox F a n i) := by
  revert hnm
  induction m with
  | zero =>
    intro hnm
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ m IH =>
    intro hnm
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hstep : coeff d (negApprox F a (m + 1) i) = coeff d (negApprox F a m i) := by
        rw [negApprox_succ]
        show coeff d (negApprox F a m i - homogeneousComponent (m + 1)
            (subst (Sum.elim a (negApprox F a m)) (F.toPowerSeries i)))
          = coeff d (negApprox F a m i)
        rw [map_sub, coeff_homogeneousComponent, if_neg (by omega), sub_zero]
      rw [hstep]
      exact IH (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      rfl

def negSeries (a : Fin g → MvPowerSeries τ R) : Fin g → MvPowerSeries τ R :=
  fun i => (fun d => coeff d (negApprox F a d.degree i) : (τ →₀ ℕ) → R)

theorem coeff_negSeries (a : Fin g → MvPowerSeries τ R) (d : τ →₀ ℕ) (i : Fin g) :
    coeff d (negSeries F a i) = coeff d (negApprox F a d.degree i) := rfl

theorem coeff_negSeries_eq_negApprox (a : Fin g → MvPowerSeries τ R) {n : ℕ}
    {d : τ →₀ ℕ} (hd : d.degree ≤ n) (i : Fin g) :
    coeff d (negSeries F a i) = coeff d (negApprox F a n i) := by
  rw [coeff_negSeries]
  exact (coeff_negApprox_stable F a hd (le_refl d.degree) i).symm

@[simp]
theorem constantCoeff_negSeries (a : Fin g → MvPowerSeries τ R) (i : Fin g) :
    (negSeries F a i).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_negSeries,
    (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl]
  show coeff (0 : τ →₀ ℕ) (0 : MvPowerSeries τ R) = 0
  exact map_zero _

theorem hasSubst_negSeries (a : Fin g → MvPowerSeries τ R) :
    HasSubst (negSeries F a) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_negSeries F a)

theorem subst_elim_negSeries {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a (negSeries F a)) (F.toPowerSeries i) = 0 := by
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  ext d
  rw [map_zero]
  by_cases hd0 : d = 0
  · subst hd0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_subst_elim F ha hneg i
  · have hagree : ∀ s : Fin g ⊕ Fin g, ∀ e : τ →₀ ℕ, e.degree ≤ d.degree →
        coeff e ((Sum.elim a (negSeries F a)) s)
          = coeff e ((Sum.elim a (negApprox F a d.degree)) s) := by
      rintro (j | j) e he
      · rfl
      · exact coeff_negSeries_eq_negApprox F a he j
    have hfam1 : ∀ s : Fin g ⊕ Fin g,
        ((Sum.elim a (negSeries F a)) s).constantCoeff = 0 := by
      rintro (j | j)
      exacts [ha j, hneg j]
    have hfam2 : ∀ s : Fin g ⊕ Fin g,
        ((Sum.elim a (negApprox F a d.degree)) s).constantCoeff = 0 := by
      rintro (j | j)
      exacts [ha j, constantCoeff_negApprox F a _ j]
    rw [coeff_subst_congr hfam1 hfam2 hagree (F.toPowerSeries i) (le_refl d.degree)]
    exact coeff_subst_elim_negApprox F ha (le_refl d.degree) hd0 i

theorem coeff_single_negSeries {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (t : τ) (i : Fin g) :
    coeff (Finsupp.single t 1) (negSeries F a i)
      = - coeff (Finsupp.single t 1) (a i) := by
  have hdeg : (Finsupp.single t 1).degree = 1 := Finsupp.degree_single t 1
  rw [coeff_negSeries, hdeg]
  show coeff (Finsupp.single t 1) (negApprox F a (0 + 1) i)
    = - coeff (Finsupp.single t 1) (a i)
  rw [negApprox_succ]
  show coeff (Finsupp.single t 1) (negApprox F a 0 i - homogeneousComponent (0 + 1)
      (subst (Sum.elim a (negApprox F a 0)) (F.toPowerSeries i)))
    = - coeff (Finsupp.single t 1) (a i)
  simp only [negApprox_zero]
  rw [map_sub, map_zero, zero_sub, coeff_homogeneousComponent, if_pos (by omega),
    subst_elim_zero_right F ha i]

end NegSeries

section Group

variable {τ τ' : Type*} (F : MvFormalGroup g R)

theorem subst_subst_elim {u v : Fin g → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0)
    {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (i : Fin g) :
    subst b (subst (Sum.elim u v) (F.toPowerSeries i))
      = subst (Sum.elim (fun j => subst b (u j)) fun j => subst b (v j))
        (F.toPowerSeries i) := by
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hb]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem subst_elim_negSeries_left {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (negSeries F a) a) (F.toPowerSeries i) = 0 := by
  have hy : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  have hz : ∀ j, (negSeries F (negSeries F a) j).constantCoeff = 0 :=
    constantCoeff_negSeries F _
  have tup1 : ∀ j, subst (Sum.elim (negSeries F a) (negSeries F (negSeries F a)))
      (F.toPowerSeries j) = 0 := subst_elim_negSeries F hy
  have haz : a = negSeries F (negSeries F a) := by
    funext j
    have s1 : a j = subst (Sum.elim a fun _ => 0) (F.toPowerSeries j) :=
      (subst_elim_zero_right F ha j).symm
    have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
        = fun j' => subst (Sum.elim (negSeries F a) (negSeries F (negSeries F a)))
            (F.toPowerSeries j') := by
      funext j'
      exact (tup1 j').symm
    have s3 : subst (Sum.elim a fun j' => subst (Sum.elim (negSeries F a)
          (negSeries F (negSeries F a))) (F.toPowerSeries j')) (F.toPowerSeries j)
        = subst (Sum.elim (fun j' => subst (Sum.elim a (negSeries F a))
            (F.toPowerSeries j')) (negSeries F (negSeries F a))) (F.toPowerSeries j) :=
      (subst_elim_assoc F ha hy hz j).symm
    have s4 : (fun j' => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j'))
        = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
      funext j'
      exact subst_elim_negSeries F ha j'
    rw [s1, s2, s3, s4, subst_elim_zero_left F hz j]
  nth_rewrite 2 [haz]
  exact tup1 i

theorem negSeries_unique {a y : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    (h : ∀ i, subst (Sum.elim a y) (F.toPowerSeries i) = 0) :
    y = negSeries F a := by
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  funext j
  have s1 : y j = subst (Sum.elim (fun _ => 0) y) (F.toPowerSeries j) :=
    (subst_elim_zero_left F hy j).symm
  have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
      = fun j' => subst (Sum.elim (negSeries F a) a) (F.toPowerSeries j') := by
    funext j'
    exact (subst_elim_negSeries_left F ha j').symm
  have s3 : subst (Sum.elim (fun j' => subst (Sum.elim (negSeries F a) a)
        (F.toPowerSeries j')) y) (F.toPowerSeries j)
      = subst (Sum.elim (negSeries F a) fun j' => subst (Sum.elim a y)
          (F.toPowerSeries j')) (F.toPowerSeries j) :=
    subst_elim_assoc F hneg ha hy j
  have s4 : (fun j' => subst (Sum.elim a y) (F.toPowerSeries j'))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j'
    exact h j'
  rw [s1, s2, s3, s4, subst_elim_zero_right F hneg j]

theorem negSeries_unique_left {a y : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hy : ∀ j, (y j).constantCoeff = 0)
    (h : ∀ i, subst (Sum.elim y a) (F.toPowerSeries i) = 0) :
    y = negSeries F a := by

  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  funext j
  have s1 : y j = subst (Sum.elim y fun _ => 0) (F.toPowerSeries j) :=
    (subst_elim_zero_right F hy j).symm
  have s2 : (fun _ : Fin g => (0 : MvPowerSeries τ R))
      = fun j' => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j') := by
    funext j'
    exact (subst_elim_negSeries F ha j').symm
  have s3 : subst (Sum.elim y fun j' => subst (Sum.elim a (negSeries F a))
        (F.toPowerSeries j')) (F.toPowerSeries j)
      = subst (Sum.elim (fun j' => subst (Sum.elim y a) (F.toPowerSeries j'))
          (negSeries F a)) (F.toPowerSeries j) :=
    (subst_elim_assoc F hy ha hneg j).symm
  have s4 : (fun j' => subst (Sum.elim y a) (F.toPowerSeries j'))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j'
    exact h j'
  rw [s1, s2, s3, s4, subst_elim_zero_left F hneg j]

end Group

section InvSeries

variable (F : MvFormalGroup g R)

def invSeries : Fin g → MvPowerSeries (Fin g) R :=
  negSeries F fun j => X j

@[simp]
theorem constantCoeff_invSeries (i : Fin g) : (invSeries F i).constantCoeff = 0 :=
  constantCoeff_negSeries F _ i

theorem hasSubst_invSeries : HasSubst (invSeries F) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_invSeries F)

theorem subst_elim_X_invSeries (i : Fin g) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R)) (invSeries F))
      (F.toPowerSeries i) = 0 :=
  subst_elim_negSeries F (fun j => constantCoeff_X j) i

theorem subst_elim_invSeries_X (i : Fin g) :
    subst (Sum.elim (invSeries F) fun j => (X j : MvPowerSeries (Fin g) R))
      (F.toPowerSeries i) = 0 :=
  subst_elim_negSeries_left F (fun j => constantCoeff_X j) i

end InvSeries

section NegSeriesMore

variable {τ τ' : Type*} (F : MvFormalGroup g R)

theorem subst_negSeries [Finite τ] {a : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) {b : τ → MvPowerSeries τ' R}
    (hb0 : ∀ s, (b s).constantCoeff = 0) :
    (fun i => subst b (negSeries F a i)) = negSeries F fun i => subst b (a i) := by
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero hb0
  have hneg : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  refine negSeries_unique F (fun j => constantCoeff_subst_eq_zero hb hb0 (ha j))
    (fun j => constantCoeff_subst_eq_zero hb hb0 (hneg j)) fun i => ?_
  rw [← subst_subst_elim F ha hneg hb i, subst_elim_negSeries F ha i,
    ← coe_substAlgHom hb, map_zero]

theorem negSeries_elim_add [IsComm F] {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    negSeries F (fun i => subst (Sum.elim a b) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (negSeries F a) (negSeries F b))
          (F.toPowerSeries i) := by
  have hna : ∀ j, (negSeries F a j).constantCoeff = 0 := constantCoeff_negSeries F a
  have hnb : ∀ j, (negSeries F b j).constantCoeff = 0 := constantCoeff_negSeries F b
  refine (negSeries_unique F (fun j => constantCoeff_subst_elim F ha hb j)
    (fun j => constantCoeff_subst_elim F hna hnb j) fun i => ?_).symm
  rw [subst_elim_exchange F ha hb hna hnb i]
  have hzl : (fun j => subst (Sum.elim a (negSeries F a)) (F.toPowerSeries j))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j
    exact subst_elim_negSeries F ha j
  have hzr : (fun j => subst (Sum.elim b (negSeries F b)) (F.toPowerSeries j))
      = fun _ : Fin g => (0 : MvPowerSeries τ R) := by
    funext j
    exact subst_elim_negSeries F hb j
  rw [hzl, hzr]
  exact subst_elim_zero_right F (fun _ => map_zero _) i

end NegSeriesMore

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def neg [IsComm G] (φ : Hom F G) : Hom F G where
  toPowerSeries := negSeries G φ.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries G φ.toPowerSeries
  subst_eq := by
    intro i
    have hφ : ∀ j, (φ.toPowerSeries j).constantCoeff = 0 := φ.constantCoeff_eq_zero
    have hbF : ∀ s, ((F.toPowerSeries) s).constantCoeff = 0 := F.constantCoeff_eq_zero
    have hXl0 : ∀ l : Fin g,
        ((X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hXr0 : ∀ l : Fin g,
        ((X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXl0) hXl0 (hφ j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero hXr0) hXr0 (hφ j)
    calc subst F.toPowerSeries (negSeries G φ.toPowerSeries i)
        = negSeries G (fun j => subst F.toPowerSeries (φ.toPowerSeries j)) i :=
          congrFun (subst_negSeries G hφ hbF) i
      _ = negSeries G (fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j)) i := by
          have hc : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
              = fun j => subst (Sum.elim
                (fun j' => subst
                  (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j'))
                fun j' => subst
                  (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                  (φ.toPowerSeries j')) (G.toPowerSeries j) := by
            funext j
            exact φ.subst_eq j
          rw [hc]
      _ = subst (Sum.elim
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            (negSeries G fun j' => subst
              (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))) (G.toPowerSeries i) :=
          congrFun (negSeries_elim_add G hφL hφR) i
      _ = subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (negSeries G φ.toPowerSeries j') ) (G.toPowerSeries i) := by
          rw [← subst_negSeries G hφ hXl0, ← subst_negSeries G hφ hXr0]

@[simp]
theorem toPowerSeries_neg [IsComm G] (φ : Hom F G) :
    (Hom.neg φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl

instance instNeg [IsComm G] : Neg (Hom F G) := ⟨Hom.neg⟩

instance instAddCommGroup [IsComm G] : AddCommGroup (Hom F G) :=
  { Hom.instAddCommMonoid with
    neg := Hom.neg
    zsmul := zsmulRec
    neg_add_cancel := fun φ => by
      apply Hom.ext
      funext i
      show subst (Sum.elim (negSeries G φ.toPowerSeries) φ.toPowerSeries)
          (G.toPowerSeries i) = 0
      exact subst_elim_negSeries_left G φ.constantCoeff_eq_zero i }

@[simp]
theorem toPowerSeries_neg' [IsComm G] (φ : Hom F G) :
    (-φ).toPowerSeries = negSeries G φ.toPowerSeries := rfl

@[simp]
theorem toPowerSeries_sub [IsComm G] (φ ψ : Hom F G) :
    (φ - ψ).toPowerSeries = fun i =>
      subst (Sum.elim φ.toPowerSeries (negSeries G ψ.toPowerSeries))
        (G.toPowerSeries i) := rfl

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instAddCommGroup [IsComm F] : AddCommGroup (End F) :=
  inferInstanceAs (AddCommGroup (Hom F F))

instance instRing [IsComm F] : Ring (End F) :=
  { End.instSemiring F, End.instAddCommGroup F with }

@[simp]
theorem toPowerSeries_neg [IsComm F] (φ : End F) :
    Hom.toPowerSeries (-φ) = negSeries F (Hom.toPowerSeries φ) := rfl

@[simp]
theorem toPowerSeries_sub [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ - ψ) = fun i =>
      subst (Sum.elim (Hom.toPowerSeries φ) (negSeries F (Hom.toPowerSeries ψ)))
        (F.toPowerSeries i) := rfl

theorem toPowerSeries_neg_one [IsComm F] :
    Hom.toPowerSeries (-1 : End F) = invSeries F := by
  rw [toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (1 : End F)) = invSeries F
  rw [toPowerSeries_one]
  rfl

theorem toPowerSeries_intCast_ofNat [IsComm F] (n : ℕ) :
    Hom.toPowerSeries (((n : ℕ) : ℤ) : End F) = F.nthSeries n := by
  rw [Int.cast_natCast]
  exact toPowerSeries_natCast F n

theorem toPowerSeries_intCast_negSucc [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((Int.negSucc n : ℤ) : End F)
      = negSeries F (F.nthSeries (n + 1)) := by
  rw [Int.cast_negSucc, toPowerSeries_neg]
  show negSeries F (Hom.toPowerSeries (((n + 1 : ℕ) : End F))) = _
  rw [toPowerSeries_natCast]

end End

section InvHom

variable (F : MvFormalGroup g R)

def invHom [IsComm F] : End F := -(1 : End F)

@[simp]
theorem toPowerSeries_invHom [IsComm F] :
    Hom.toPowerSeries (invHom F) = invSeries F :=
  End.toPowerSeries_neg_one F

end InvHom

section LinearPartNeg

variable (F : MvFormalGroup g R)

theorem linearPart_negSeries {k : ℕ} {a : Fin g → MvPowerSeries (Fin k) R}
    (ha : ∀ j, (a j).constantCoeff = 0) :
    linearPart (negSeries F a) = - linearPart a := by
  ext i j
  show coeff (Finsupp.single j 1) (negSeries F a i)
    = (- linearPart a) i j
  rw [coeff_single_negSeries F ha j i, Matrix.neg_apply]
  rfl

theorem coeff_single_invSeries (t i : Fin g) :
    coeff (Finsupp.single t 1) (invSeries F i)
      = - coeff (Finsupp.single t 1) (X i : MvPowerSeries (Fin g) R) :=
  coeff_single_negSeries F (fun l => constantCoeff_X l) t i

theorem linearPart_invSeries : linearPart (invSeries F) = -1 := by
  classical
  ext i j
  show coeff (Finsupp.single j 1) (invSeries F i)
    = (-1 : Matrix (Fin g) (Fin g) R) i j
  rw [coeff_single_invSeries F j i, coeff_index_single_X, Matrix.neg_apply,
    Matrix.one_apply]
  by_cases hij : j = i
  · subst hij
    rfl
  · rw [if_neg hij, if_neg fun hcon => hij hcon.symm, neg_zero]

@[simp]
theorem linearPartHom_neg [IsComm F] (φ : End F) :
    linearPartHom F (-φ) = - linearPartHom F φ :=
  map_neg (linearPartHom F) φ

theorem linearPartHom_neg_one [IsComm F] :
    linearPartHom F (-1 : End F) = -1 := by
  rw [map_neg, map_one]

@[simp]
theorem linearPartHom_intCast [IsComm F] (n : ℤ) :
    linearPartHom F ((n : ℤ) : End F) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [map_intCast, zsmul_eq_mul, mul_one]

end LinearPartNeg

end MvFormalGroup


set_option autoImplicit false

noncomputable section

universe u v


namespace CerednikDrinfeld

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable (p : ℕ) [Fact p.Prime]

abbrev Zp2 : Type := WittVector p (GaloisField p 2)

namespace SpecialFormal

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

abbrev Series (B : Type u) [CommRing B] : Type u := Fin 2 → MvPowerSeries (Fin 2) B

def Series.id (B : Type u) [CommRing B] : Series B := fun i => MvPowerSeries.X i

def Series.comp (ψ φ : Series B) : Series B := fun i => subst φ (ψ i)

def Series.addVia (F : MvFormalGroup 2 B) (φ ψ : Series B) : Series B :=
  fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i)

def Series.map (f : B →+* B') (φ : Series B) : Series B' := fun i => MvPowerSeries.map f (φ i)

def IsLawHom (F G : MvFormalGroup 2 B) (φ : Series B) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧
  ∀ i, subst F.toPowerSeries (φ i) =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      (G.toPowerSeries i)

namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}

def toHom (h : IsLawHom F G φ) : MvFormalGroup.Hom F G := ⟨φ, h.1, h.2⟩

@[simp] theorem toHom_toPowerSeries (h : IsLawHom F G φ) : h.toHom.toPowerSeries = φ := rfl

theorem of_hom (f : MvFormalGroup.Hom F G) : IsLawHom F G f.toPowerSeries :=
  ⟨f.constantCoeff_eq_zero, f.subst_eq⟩

theorem hasSubst (h : IsLawHom F G φ) : HasSubst φ := hasSubst_of_constantCoeff_zero h.1

theorem id (F : MvFormalGroup 2 B) : IsLawHom F F (Series.id B) := of_hom (MvFormalGroup.Hom.id F)

theorem comp (hψ : IsLawHom G H ψ) (hφ : IsLawHom F G φ) : IsLawHom F H (ψ.comp φ) :=
  of_hom (hψ.toHom.comp hφ.toHom)

theorem map (h : IsLawHom F G φ) (f : B →+* B') :
    IsLawHom (F.map f) (G.map f) (φ.map f) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show constantCoeff (MvPowerSeries.map f (φ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h.1 i, map_zero]
  · have hXl : ∀ l : Fin 2, constantCoeff
        ((MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
      fun l => constantCoeff_X _
    have hXr : ∀ l : Fin 2, constantCoeff
        ((MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) = 0 :=
      fun l => constantCoeff_X _
    have hA : HasSubst (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl (h.1 j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr (h.1 j)
    have key := congrArg (MvPowerSeries.map f) (h.2 i)
    rw [map_subst F.hasSubst_toPowerSeries, map_subst hA] at key
    have hAmap : (fun s => MvPowerSeries.map f (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j)) s))
        = Sum.elim
          (fun j => subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
              (MvPowerSeries.map f (φ j)))
          (fun j => subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
              (MvPowerSeries.map f (φ j))) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map f (subst _ (φ j)) = _
        rw [map_subst (hasSubst_of_constantCoeff_zero hXl)]
        simp only [MvPowerSeries.map_X, Sum.elim_inl]
      · show MvPowerSeries.map f (subst _ (φ j)) = _
        rw [map_subst (hasSubst_of_constantCoeff_zero hXr)]
        simp only [MvPowerSeries.map_X, Sum.elim_inr]
    rw [hAmap] at key
    exact key

end IsLawHom

theorem Series.map_comp (f : B →+* B') (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (ψ.comp φ).map f = (ψ.map f).comp (φ.map f) := by
  funext i
  show MvPowerSeries.map f (subst φ (ψ i)) = subst _ (MvPowerSeries.map f (ψ i))
  rw [map_subst (hasSubst_of_constantCoeff_zero hφ)]
  rfl

theorem Series.map_addVia (f : B →+* B') (F : MvFormalGroup 2 B) (φ ψ : Series B)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (Series.addVia F φ ψ).map f = Series.addVia (F.map f) (φ.map f) (ψ.map f) := by
  funext i
  show MvPowerSeries.map f (subst (Sum.elim φ ψ) (F.toPowerSeries i)) =
    subst (Sum.elim (φ.map f) (ψ.map f)) (MvPowerSeries.map f (F.toPowerSeries i))
  have hS : HasSubst (Sum.elim φ ψ) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact hφ j
    · exact hψ j
  rw [map_subst hS]
  congr 1
  funext s
  rcases s with j | j <;> rfl

@[simp] theorem Series.map_id (f : B →+* B') : (Series.id B).map f = Series.id B' := by
  funext i
  exact MvPowerSeries.map_X f i

@[simp] theorem Series.map_ringHom_id (φ : Series B) : φ.map (RingHom.id B) = φ := by
  funext i
  exact congrFun (congrArg DFunLike.coe (MvPowerSeries.map_id (σ := Fin 2) (R := B))) (φ i)

theorem Series.map_map {B'' : Type*} [CommRing B''] (f : B →+* B') (g : B' →+* B'') (φ : Series B) :
    (φ.map f).map g = φ.map (g.comp f) := by
  funext i
  exact MvPowerSeries.map_map f g (φ i)

theorem Series.comp_assoc (χ ψ φ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  funext i
  exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ)
    (hasSubst_of_constantCoeff_zero hφ) (χ i)

theorem Series.id_comp (φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (Series.id B).comp φ = φ := by
  funext i
  exact subst_X (hasSubst_of_constantCoeff_zero hφ) i

theorem Series.comp_id (φ : Series B) : φ.comp (Series.id B) = φ := by
  funext i
  exact congrFun MvPowerSeries.subst_self (φ i)

theorem Series.constantCoeff_comp {ψ φ : Series B} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) : constantCoeff ((ψ.comp φ) i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hφ) hφ (hψ i)

end SpecialFormal

open SpecialFormal

structure FormalODModule (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] where

  F : MvFormalGroup 2 B

  isComm : F.IsComm

  act : Zp2 p → Series B

  varpi : Series B

  isLawHom_act : ∀ a, IsLawHom F F (act a)

  isLawHom_varpi : IsLawHom F F varpi

  act_one : act 1 = Series.id B

  act_mul : ∀ a b, act (a * b) = (act a).comp (act b)

  act_add : ∀ a b, act (a + b) = Series.addVia F (act a) (act b)

  varpi_comp_varpi : varpi.comp varpi = act (p : Zp2 p)

  varpi_comp_act : ∀ a, varpi.comp (act a) = (act (WittVector.frobenius a)).comp varpi

namespace FormalODModule

attribute [instance] FormalODModule.isComm

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

def map (f : B →+* B') (X : FormalODModule p B) : FormalODModule p B' where
  F := X.F.map f
  isComm := by
    constructor
    intro i
    have key := congrArg (MvPowerSeries.map f) (X.isComm.comm i)
    have hS : HasSubst (Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
        fun j => MvPowerSeries.X (Sum.inl j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;> exact constantCoeff_X _
    rw [map_subst hS] at key
    have hfam : (fun s => MvPowerSeries.map f (Sum.elim
        (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
        (fun j => MvPowerSeries.X (Sum.inl j)) s))
        = Sum.elim
          (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))
          fun j => MvPowerSeries.X (Sum.inl j) := by
      funext s
      rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
    rw [hfam] at key
    exact key
  act a := (X.act a).map f
  varpi := X.varpi.map f
  isLawHom_act a := (X.isLawHom_act a).map f
  isLawHom_varpi := X.isLawHom_varpi.map f
  act_one := by rw [X.act_one, Series.map_id]
  act_mul a b := by
    rw [X.act_mul, Series.map_comp f _ _ (X.isLawHom_act b).1]
  act_add a b := by
    rw [X.act_add, Series.map_addVia f X.F _ _ (X.isLawHom_act a).1 (X.isLawHom_act b).1]
  varpi_comp_varpi := by
    rw [← Series.map_comp f _ _ X.isLawHom_varpi.1, X.varpi_comp_varpi]
  varpi_comp_act a := by
    rw [← Series.map_comp f _ _ (X.isLawHom_act a).1, X.varpi_comp_act,
      Series.map_comp f _ _ X.isLawHom_varpi.1]

@[simp] theorem map_F (f : B →+* B') (X : FormalODModule p B) : (X.map f).F = X.F.map f := rfl
@[simp] theorem map_act (f : B →+* B') (X : FormalODModule p B) (a : Zp2 p) :
    (X.map f).act a = (X.act a).map f := rfl
@[simp] theorem map_varpi (f : B →+* B') (X : FormalODModule p B) :
    (X.map f).varpi = X.varpi.map f := rfl

theorem ext' {X Y : FormalODModule p B} (hF : X.F = Y.F) (ha : X.act = Y.act)
    (hv : X.varpi = Y.varpi) : X = Y := by
  cases X; cases Y; cases hF; cases ha; cases hv; rfl

theorem _root_.MvFormalGroup.map_map' {g : ℕ} {B'' : Type*} [CommRing B''] (f : B →+* B')
    (f' : B' →+* B'') (F : MvFormalGroup g B) : (F.map f).map f' = F.map (f'.comp f) :=
  MvFormalGroup.ext (funext fun i => MvPowerSeries.map_map f f' (F.toPowerSeries i))

theorem _root_.MvFormalGroup.map_ringHom_id {g : ℕ} (F : MvFormalGroup g B) : F.map (RingHom.id B) = F :=
  MvFormalGroup.ext (funext fun i => by
    show MvPowerSeries.map (RingHom.id B) (F.toPowerSeries i) = F.toPowerSeries i
    rw [MvPowerSeries.map_id]; rfl)

@[simp] theorem map_id (X : FormalODModule p B) : X.map (RingHom.id B) = X :=
  ext' (MvFormalGroup.map_ringHom_id X.F) (funext fun a => Series.map_ringHom_id (X.act a))
    (Series.map_ringHom_id _)

theorem map_map {B'' : Type*} [CommRing B''] (f : B →+* B') (g : B' →+* B'')
    (X : FormalODModule p B) : (X.map f).map g = X.map (g.comp f) :=
  ext' (MvFormalGroup.map_map' f g X.F) (funext fun a => Series.map_map f g (X.act a))
    (Series.map_map f g _)

def actEnd (X : FormalODModule p B) (a : Zp2 p) : MvFormalGroup.End X.F := (X.isLawHom_act a).toHom

def varpiEnd (X : FormalODModule p B) : MvFormalGroup.End X.F := X.isLawHom_varpi.toHom

def actRingHom (X : FormalODModule p B) : Zp2 p →+* MvFormalGroup.End X.F where
  toFun := X.actEnd
  map_one' := MvFormalGroup.Hom.ext (X.act_one)
  map_mul' a b := MvFormalGroup.Hom.ext (X.act_mul a b)
  map_zero' := by
    have h : X.actEnd 0 + X.actEnd 0 = X.actEnd 0 :=
      MvFormalGroup.Hom.ext (by have h := (X.act_add 0 0).symm; rw [add_zero] at h; exact h)
    exact add_eq_left.mp h
  map_add' a b := MvFormalGroup.Hom.ext (X.act_add a b)

@[simp] theorem actRingHom_apply (X : FormalODModule p B) (a : Zp2 p) :
    X.actRingHom a = X.actEnd a := rfl

@[simp] theorem actEnd_toPowerSeries (X : FormalODModule p B) (a : Zp2 p) :
    (X.actEnd a).toPowerSeries = X.act a := rfl

@[simp] theorem varpiEnd_toPowerSeries (X : FormalODModule p B) :
    X.varpiEnd.toPowerSeries = X.varpi := rfl

theorem varpiEnd_mul_varpiEnd (X : FormalODModule p B) :
    X.varpiEnd * X.varpiEnd = X.actRingHom (p : Zp2 p) :=
  MvFormalGroup.Hom.ext X.varpi_comp_varpi

theorem varpiEnd_mul_actEnd (X : FormalODModule p B) (a : Zp2 p) :
    X.varpiEnd * X.actEnd a = X.actEnd (WittVector.frobenius a) * X.varpiEnd :=
  MvFormalGroup.Hom.ext (X.varpi_comp_act a)

theorem act_natCast (X : FormalODModule p B) (n : ℕ) : X.act (n : Zp2 p) = X.F.nthSeries n := by
  have h : X.actRingHom (n : Zp2 p) = (n : MvFormalGroup.End X.F) := map_natCast X.actRingHom n
  have h2 := congrArg MvFormalGroup.Hom.toPowerSeries h
  rw [MvFormalGroup.End.toPowerSeries_natCast] at h2
  exact h2

theorem act_pow_add (X : FormalODModule p B) (a b : ℕ) :
    X.act ((p : Zp2 p) ^ (a + b)) = (X.act ((p : Zp2 p) ^ a)).comp (X.act ((p : Zp2 p) ^ b)) := by
  rw [pow_add, X.act_mul]

abbrev Lie (_X : FormalODModule p B) : Type u := Fin 2 → B

def lieAct (X : FormalODModule p B) (a : Zp2 p) : X.Lie →ₗ[B] X.Lie :=
  Matrix.mulVecLin (MvFormalGroup.linearPart (X.act a))

def lieZero (j : Zp2 p →+* B) (X : FormalODModule p B) : Submodule B X.Lie :=
  ⨅ a : Zp2 p, LinearMap.ker (X.lieAct a - j a • LinearMap.id)

def lieOne (j : Zp2 p →+* B) (X : FormalODModule p B) : Submodule B X.Lie :=
  ⨅ a : Zp2 p, LinearMap.ker (X.lieAct a - j (WittVector.frobenius a) • LinearMap.id)

def IsSpecial (j : Zp2 p →+* B) (X : FormalODModule p B) : Prop :=
  IsCompl (X.lieZero j) (X.lieOne j) ∧
    Module.Invertible B ↥(X.lieZero j) ∧ Module.Invertible B ↥(X.lieOne j)

def IsODHom (X Y : FormalODModule p B) (φ : Series B) : Prop :=
  IsLawHom X.F Y.F φ ∧ (∀ a, φ.comp (X.act a) = (Y.act a).comp φ) ∧
    φ.comp X.varpi = Y.varpi.comp φ

structure Hom (X Y : FormalODModule p B) where

  toSeries : Series B

  isODHom : IsODHom X Y toSeries

namespace IsODHom

variable {X Y Z : FormalODModule p B} {φ ψ : Series B}

theorem constantCoeff (h : IsODHom X Y φ) (i : Fin 2) : constantCoeff (φ i) = 0 := h.1.1 i

protected theorem id (X : FormalODModule p B) : IsODHom X X (Series.id B) := by
  refine ⟨IsLawHom.id X.F, fun a => ?_, ?_⟩
  · rw [Series.id_comp _ (X.isLawHom_act a).1, Series.comp_id]
  · rw [Series.id_comp _ X.isLawHom_varpi.1, Series.comp_id]

protected theorem comp (hψ : IsODHom Y Z ψ) (hφ : IsODHom X Y φ) : IsODHom X Z (ψ.comp φ) := by
  refine ⟨hψ.1.comp hφ.1, fun a => ?_, ?_⟩
  · rw [Series.comp_assoc _ _ _ hφ.constantCoeff (X.isLawHom_act a).1, hφ.2.1 a,
      ← Series.comp_assoc _ _ _ (Y.isLawHom_act a).1 hφ.constantCoeff, hψ.2.1 a,
      Series.comp_assoc _ _ _ hψ.constantCoeff hφ.constantCoeff]
  · rw [Series.comp_assoc _ _ _ hφ.constantCoeff X.isLawHom_varpi.1, hφ.2.2,
      ← Series.comp_assoc _ _ _ Y.isLawHom_varpi.1 hφ.constantCoeff, hψ.2.2,
      Series.comp_assoc _ _ _ hψ.constantCoeff hφ.constantCoeff]

protected theorem map (h : IsODHom X Y φ) (f : B →+* B') :
    IsODHom (X.map f) (Y.map f) (φ.map f) := by
  refine ⟨h.1.map f, fun a => ?_, ?_⟩
  · show (φ.map f).comp ((X.act a).map f) = ((Y.act a).map f).comp (φ.map f)
    rw [← Series.map_comp f _ _ (X.isLawHom_act a).1, h.2.1 a, Series.map_comp f _ _ h.constantCoeff]
  · show (φ.map f).comp (X.varpi.map f) = (Y.varpi.map f).comp (φ.map f)
    rw [← Series.map_comp f _ _ X.isLawHom_varpi.1, h.2.2, Series.map_comp f _ _ h.constantCoeff]

theorem act_natCast_pow (X : FormalODModule p B) (n : ℕ) :
    IsODHom X X (X.act ((p : Zp2 p) ^ n)) := by
  refine ⟨X.isLawHom_act _, fun a => ?_, ?_⟩
  · rw [← X.act_mul, ← X.act_mul, mul_comm]
  · rw [X.varpi_comp_act, map_pow, map_natCast]

end IsODHom

namespace Hom

variable {X Y Z : FormalODModule p B}

@[ext] theorem ext {f g : Hom X Y} (h : f.toSeries = g.toSeries) : f = g := by
  cases f; cases g; cases h; rfl

protected def id (X : FormalODModule p B) : Hom X X := ⟨Series.id B, IsODHom.id X⟩

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z := ⟨g.toSeries.comp f.toSeries, g.isODHom.comp f.isODHom⟩

def map (f' : B →+* B') (f : Hom X Y) : Hom (X.map f') (Y.map f') :=
  ⟨f.toSeries.map f', f.isODHom.map f'⟩

def toLawHom (f : Hom X Y) : MvFormalGroup.Hom X.F Y.F := f.isODHom.1.toHom

def IsIso (f : Hom X Y) : Prop := ∃ g : Hom Y X, g.comp f = Hom.id X ∧ f.comp g = Hom.id Y

end Hom

abbrev KerAlgebra (φ : Series B) : Type u :=
  MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range φ)

def HasKernelOfDegree (φ : Series B) (d : ℕ) : Prop :=
  Module.Finite B (KerAlgebra φ) ∧ Module.Projective B (KerAlgebra φ) ∧
    ∀ (κ : Type u) [Field κ] (f : B →+* κ), Module.finrank κ (KerAlgebra (φ.map f)) = d

def IsIsogenyOfHeight (X Y : FormalODModule p B) (φ : Series B) (h : ℕ) : Prop :=
  IsODHom X Y φ ∧ HasKernelOfDegree φ (p ^ h)

def HasHeight (X : FormalODModule p B) (h : ℕ) : Prop :=
  HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h)

end FormalODModule

structure SpecialFormalODModule (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : Zp2 p →+* B)
    extends FormalODModule p B where

  isSpecial : toFormalODModule.IsSpecial j

  hasHeight : toFormalODModule.HasHeight 4

namespace SpecialFormal

abbrev pIdeal (B : Type u) [CommRing B] : Ideal B := Ideal.span {(p : B)}

variable {p}

def residueMap {O : Type v} [CommRing O] {B : Type u} [CommRing B] (ψ : O →+* B) :
    O ⧸ pIdeal p O →+* B ⧸ pIdeal p B :=
  Ideal.quotientMap (pIdeal p B) ψ (by
    rw [pIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      map_natCast]
    exact Ideal.subset_span rfl)

def reduceMap {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') :
    B ⧸ pIdeal p B →+* B' ⧸ pIdeal p B' :=
  residueMap f

abbrev structureMap {O : Type v} [CommRing O] {B : Type u} [CommRing B] (ι : Zp2 p →+* O)
    (ψ : O →+* B) : Zp2 p →+* B :=
  ψ.comp ι

structure Rigidified (p : ℕ) [Fact p.Prime] {O : Type v} [CommRing O]
    (Φ : FormalODModule p (O ⧸ pIdeal p O)) (B : Type u) [CommRing B] where

  X : FormalODModule p B

  n : ℕ

  ρ : Series (B ⧸ pIdeal p B)

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']

abbrev Xbar (t : Rigidified p Φ B) : FormalODModule p (B ⧸ pIdeal p B) :=
  t.X.map (Ideal.Quotient.mk (pIdeal p B))

abbrev Φbar (ψ : O →+* B) (_t : Rigidified p Φ B) : FormalODModule p (B ⧸ pIdeal p B) :=
  Φ.map (residueMap ψ)

def IsAdmissible (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) : Prop :=
  t.X.IsSpecial (structureMap ι ψ) ∧ t.X.HasHeight 4 ∧
    FormalODModule.IsIsogenyOfHeight (t.Φbar ψ) t.Xbar t.ρ (4 * t.n)

def IsIsomorphic (t t' : Rigidified p Φ B) : Prop :=
  ∃ (u v : Series B) (m : ℕ), FormalODModule.IsODHom t.X t'.X u ∧ FormalODModule.IsODHom t'.X t.X v ∧
    v.comp u = Series.id B ∧ u.comp v = Series.id B ∧
    (t'.Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((u.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ)
      = (t'.Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp t'.ρ

theorem IsIsomorphic.refl (t : Rigidified p Φ B) (hρ : ∀ i, constantCoeff (t.ρ i) = 0) :
    t.IsIsomorphic t := by
  refine ⟨Series.id B, Series.id B, 0, FormalODModule.IsODHom.id t.X, FormalODModule.IsODHom.id t.X,
    Series.comp_id _, Series.comp_id _, ?_⟩
  rw [Series.map_id, Series.id_comp _ hρ]

theorem IsAdmissible.constantCoeff_ρ {ι : Zp2 p →+* O} {ψ : O →+* B} {t : Rigidified p Φ B}
    (ht : t.IsAdmissible ι ψ) (i : Fin 2) : constantCoeff (t.ρ i) = 0 :=
  ht.2.2.1.constantCoeff i

theorem IsIsomorphic.symm {t t' : Rigidified p Φ B} (h : t.IsIsomorphic t')
    (hρ : ∀ i, constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0) :
    t'.IsIsomorphic t := by
  obtain ⟨u, v, m, hu, hv, hvu, huv, h⟩ := h
  refine ⟨v, u, m, hv, hu, huv, hvu, ?_⟩
  set mk := Ideal.Quotient.mk (pIdeal p B)
  have hub : FormalODModule.IsODHom t.Xbar t'.Xbar (u.map mk) := hu.map mk
  have hvb : FormalODModule.IsODHom t'.Xbar t.Xbar (v.map mk) := hv.map mk
  have hA' : ∀ k i, constantCoeff (t'.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t'.Xbar.isLawHom_act _).1
  have huρ : ∀ i, constantCoeff (((u.map mk).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hub.constantCoeff hρ
  have hvu' : (v.map mk).comp (u.map mk) = Series.id _ := by
    rw [← Series.map_comp mk _ _ hu.constantCoeff, hvu, Series.map_id]
  rw [← Series.comp_assoc _ _ _ hvb.constantCoeff hρ', ← hvb.2.1, Series.comp_assoc _ _ _ (hA' _) hρ',
    ← h, ← Series.comp_assoc _ _ _ (hA' _) huρ, hvb.2.1, Series.comp_assoc _ _ _ hvb.constantCoeff huρ,
    ← Series.comp_assoc _ _ _ hub.constantCoeff hρ, hvu', Series.id_comp _ hρ]

theorem IsIsomorphic.trans {t t' t'' : Rigidified p Φ B} (h₁ : t.IsIsomorphic t') (h₂ : t'.IsIsomorphic t'')
    (hρ : ∀ i, constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0)
    (hρ'' : ∀ i, constantCoeff (t''.ρ i) = 0) :
    t.IsIsomorphic t'' := by
  obtain ⟨u₁, v₁, m₁, hu₁, hv₁, hvu₁, huv₁, h₁⟩ := h₁
  obtain ⟨u₂, v₂, m₂, hu₂, hv₂, hvu₂, huv₂, h₂⟩ := h₂
  refine ⟨u₂.comp u₁, v₁.comp v₂, m₁ + m₂ + t'.n, hu₂.comp hu₁, hv₁.comp hv₂, ?_, ?_, ?_⟩
  · rw [Series.comp_assoc _ _ _ hv₂.constantCoeff (hu₂.comp hu₁).constantCoeff,
      ← Series.comp_assoc _ _ _ hu₂.constantCoeff hu₁.constantCoeff, hvu₂,
      Series.id_comp _ hu₁.constantCoeff, hvu₁]
  · rw [Series.comp_assoc _ _ _ hu₁.constantCoeff (hv₁.comp hv₂).constantCoeff,
      ← Series.comp_assoc _ _ _ hv₁.constantCoeff hv₂.constantCoeff, huv₁,
      Series.id_comp _ hv₂.constantCoeff, huv₂]
  set mk := Ideal.Quotient.mk (pIdeal p B)
  have hub₁ : FormalODModule.IsODHom t.Xbar t'.Xbar (u₁.map mk) := hu₁.map mk
  have hub₂ : FormalODModule.IsODHom t'.Xbar t''.Xbar (u₂.map mk) := hu₂.map mk
  have hA' : ∀ k i, constantCoeff (t'.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t'.Xbar.isLawHom_act _).1
  have hA'' : ∀ k i, constantCoeff (t''.Xbar.act ((p : Zp2 p) ^ k) i) = 0 :=
    fun k => (t''.Xbar.isLawHom_act _).1
  have hu₁ρ : ∀ i, constantCoeff (((u₁.map mk).comp t.ρ) i) = 0 :=
    Series.constantCoeff_comp hub₁.constantCoeff hρ
  have hu₂ρ' : ∀ i, constantCoeff (((u₂.map mk).comp t'.ρ) i) = 0 :=
    Series.constantCoeff_comp hub₂.constantCoeff hρ'
  have e₁ : m₁ + m₂ + t'.n + t''.n = (m₂ + t''.n) + (m₁ + t'.n) := by omega
  have e₂ : m₁ + m₂ + t'.n + t.n = (m₁ + t.n) + (m₂ + t'.n) := by omega
  rw [Series.map_comp mk _ _ hu₁.constantCoeff, e₁, e₂, FormalODModule.act_pow_add t''.Xbar (m₂ + t''.n) (m₁ + t'.n),
    Series.comp_assoc _ _ _ hub₁.constantCoeff hρ,
    Series.comp_assoc _ _ _ (hA'' _) (Series.constantCoeff_comp hub₂.constantCoeff hu₁ρ),
    ← Series.comp_assoc _ _ _ hub₂.constantCoeff hu₁ρ, ← hub₂.2.1,
    Series.comp_assoc _ _ _ (hA' _) hu₁ρ, h₁,
    ← Series.comp_assoc _ _ _ (hA' _) hρ', hub₂.2.1,
    Series.comp_assoc _ _ _ hub₂.constantCoeff hρ',
    ← Series.comp_assoc _ _ _ (hA'' _) hu₂ρ', ← FormalODModule.act_pow_add t''.Xbar (m₂ + t''.n) (m₁ + t.n),
    add_comm (m₂ + t''.n) (m₁ + t.n), FormalODModule.act_pow_add t''.Xbar (m₁ + t.n) (m₂ + t''.n),
    Series.comp_assoc _ _ _ (hA'' _) hu₂ρ', h₂,
    ← Series.comp_assoc _ _ _ (hA'' _) hρ'', ← FormalODModule.act_pow_add]

def map (f : B →+* B') (t : Rigidified p Φ B) : Rigidified p Φ B' where
  X := t.X.map f
  n := t.n
  ρ := t.ρ.map (reduceMap f)

@[simp] theorem map_X (f : B →+* B') (t : Rigidified p Φ B) : (t.map f).X = t.X.map f := rfl
@[simp] theorem map_n (f : B →+* B') (t : Rigidified p Φ B) : (t.map f).n = t.n := rfl
@[simp] theorem map_ρ (f : B →+* B') (t : Rigidified p Φ B) :
    (t.map f).ρ = t.ρ.map (reduceMap f) := rfl

theorem ext' {t t' : Rigidified p Φ B} (hX : t.X = t'.X) (hn : t.n = t'.n) (hρ : t.ρ = t'.ρ) :
    t = t' := by
  cases t; cases t'; cases hX; cases hn; cases hρ; rfl

omit [Fact p.Prime] in
theorem reduceMap_id : reduceMap (p := p) (RingHom.id B) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext rfl

omit [Fact p.Prime] in
theorem reduceMap_comp (g : B' →+* B'') (f : B →+* B') :
    reduceMap (p := p) (g.comp f) = (reduceMap g).comp (reduceMap f) :=
  Ideal.Quotient.ringHom_ext rfl

omit [Fact p.Prime] in

theorem _root_.CerednikDrinfeld.SpecialFormal.residueMap_comp (f : B →+* B') (ψ : O →+* B) :
    residueMap (p := p) (f.comp ψ) = (reduceMap f).comp (residueMap ψ) :=
  Ideal.Quotient.ringHom_ext rfl

theorem map_id (t : Rigidified p Φ B) : t.map (RingHom.id B) = t :=
  ext' (by rw [map_X]; exact t.X.map_id) rfl (by rw [map_ρ, reduceMap_id, Series.map_ringHom_id])

theorem map_comp (g : B' →+* B'') (f : B →+* B') (t : Rigidified p Φ B) :
    t.map (g.comp f) = (t.map f).map g :=
  ext' (by rw [map_X, map_X, map_X, FormalODModule.map_map]) rfl
    (by rw [map_ρ, map_ρ, map_ρ, reduceMap_comp, Series.map_map])

theorem Φbar_map (ψ : O →+* B) (f : B →+* B') (t : Rigidified p Φ B) :
    (t.map f).Φbar (f.comp ψ) = (t.Φbar ψ).map (reduceMap f) := by
  rw [Φbar, Φbar, FormalODModule.map_map, residueMap_comp]

end Rigidified

structure ModuliPackage (p : ℕ) [Fact p.Prime] (O : Type v) [CommRing O] : Type (max (u + 1) v) where

  obj : ∀ (B : Type u) [CommRing B] (_ψ : O →+* B), IsNilpotent (p : B) → Type u

  map : ∀ {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
    f.comp ψ = ψ' → obj B ψ hB → obj B' ψ' hB'

  map_id : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : obj B ψ hB),
    map hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x

  map_comp : ∀ {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']
    {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : obj B ψ hB),
    map hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x =
      map hB' hB'' g hg (map hB hB' f hf x)

namespace ModuliPackage

variable {O : Type v} [CommRing O]

def twist (τ : O →+* O) (M : ModuliPackage.{u, v} p O) : ModuliPackage.{u, v} p O where
  obj B _ ψ hB := M.obj B (ψ.comp τ) hB
  map hB hB' f hf := M.map hB hB' f (by rw [← RingHom.comp_assoc, hf])
  map_id hB x := M.map_id hB x
  map_comp hB hB' hB'' g f hf hg x := M.map_comp hB hB' hB'' g f _ _ x

@[simp] theorem twist_obj (τ : O →+* O) (M : ModuliPackage.{u, v} p O) (B : Type u) [CommRing B]
    (ψ : O →+* B) (hB : IsNilpotent (p : B)) : (M.twist τ).obj B ψ hB = M.obj B (ψ.comp τ) hB := rfl

theorem twist_map (τ : O →+* O) (M : ModuliPackage.{u, v} p O) {B B' : Type u} [CommRing B]
    [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'} (hB : IsNilpotent (p : B))
    (hB' : IsNilpotent (p : B')) (f : B →+* B') (hf : f.comp ψ = ψ') (x : (M.twist τ).obj B ψ hB) :
    (M.twist τ).map hB hB' f hf x =
      M.map (ψ := ψ.comp τ) (ψ' := ψ'.comp τ) hB hB' f (by rw [← RingHom.comp_assoc, hf]) x := rfl

def IsZariskiSheaf (M : ModuliPackage.{u, v} p O) : Prop :=
  ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (n : ℕ) (f : Fin n → B) (_hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)]
    [∀ i, IsLocalization.Away (f i) (L i)]
    (hL : ∀ i, IsNilpotent (p : L i))
    (L₂ : Fin n → Fin n → Type u) [∀ i j, CommRing (L₂ i j)] [∀ i j, Algebra B (L₂ i j)]
    [∀ i j, IsLocalization.Away (f i * f j) (L₂ i j)]
    (hL₂ : ∀ i j, IsNilpotent (p : L₂ i j))
    (l : ∀ i j, L i →+* L₂ i j) (r : ∀ i j, L j →+* L₂ i j)
    (hl : ∀ i j (b : B), l i j (algebraMap B (L i) b) = algebraMap B (L₂ i j) b)
    (hr : ∀ i j (b : B), r i j (algebraMap B (L j) b) = algebraMap B (L₂ i j) b),
    (∀ m m' : M.obj B ψ hB,
      (∀ i, M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m =
        M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m') →
      m = m') ∧
    (∀ x : ∀ i, M.obj (L i) ((algebraMap B (L i)).comp ψ) (hL i),
      (∀ i j, M.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL i) (hL₂ i j) (l i j)
            (RingHom.ext fun b => hl i j (ψ b)) (x i) =
          M.map (ψ' := (algebraMap B (L₂ i j)).comp ψ) (hL j) (hL₂ i j) (r i j)
            (RingHom.ext fun b => hr i j (ψ b)) (x j)) →
      ∃ m : M.obj B ψ hB, ∀ i,
        M.map (ψ' := (algebraMap B (L i)).comp ψ) hB (hL i) (algebraMap B (L i)) rfl m = x i)

def IsModuli (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{u, v} p O) : Prop :=
  M.IsZariskiSheaf ∧
  ∃ η : ∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB,
    (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
        (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
        (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
    (∀ (B B' : Type u) [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
        (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
        η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
    (∀ (B : Type u) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
        ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
          ∀ (i : Fin n) (L : Type u) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
            (hL : IsNilpotent (p : L)),
            ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
              η L ((algebraMap B L).comp ψ) hL t =
                M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld

end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.LubinTateLemma

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [CharP k p]

theorem two_le_card : 2 ≤ Fintype.card k := Fintype.one_lt_card

theorem card_ne_zero : Fintype.card k ≠ 0 := by
  have := two_le_card (k := k); omega

theorem constantCoeff_natCast_p : WittVector.constantCoeff (p : WittVector p k) = 0 := by
  rw [WittVector.constantCoeff_apply, WittVector.coeff_p_zero]

theorem p_ne_zero' : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k

theorem isUnit_one_sub_pow (r : ℕ) : IsUnit (1 - (p : WittVector p k) ^ (r + 1)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_pow, constantCoeff_natCast_p,
    zero_pow (Nat.succ_ne_zero r), sub_zero]
  exact one_ne_zero

theorem one_sub_pow_ne_zero (r : ℕ) : (1 - (p : WittVector p k) ^ (r + 1)) ≠ 0 :=
  (isUnit_one_sub_pow r).ne_zero

theorem exists_eq_p_mul_of_coeff_zero (x : WittVector p k) (hx : x.coeff 0 = 0) :
    ∃ y : WittVector p k, x = (p : WittVector p k) * y := by
  have h1 : x = WittVector.verschiebung (x.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := x) (n := 1) (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact hx)
    simpa using this
  obtain ⟨y, hy⟩ := (WittVector.frobenius_bijective p k).2 (x.shift 1)
  refine ⟨y, ?_⟩
  rw [h1, ← hy, WittVector.verschiebung_frobenius, mul_comm]

variable (p k)

def fvec (τ : Type*) : τ → MvPowerSeries τ (WittVector p k) :=
  fun s => C (p : WittVector p k) * X s + X s ^ Fintype.card k

def Comm {τ : Type*} (φ : MvPowerSeries τ (WittVector p k)) : Prop :=
  C (p : WittVector p k) * φ + φ ^ Fintype.card k = subst (fvec p k τ) φ

def defect {τ : Type*} (θ : MvPowerSeries τ (WittVector p k)) : MvPowerSeries τ (WittVector p k) :=
  C (p : WittVector p k) * θ + θ ^ Fintype.card k - subst (fvec p k τ) θ

variable {p k}

section Family

variable {τ : Type*}

theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p k τ s) = 0 := by
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow (card_ne_zero (k := k)), add_zero]

theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p k τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

theorem coeff_single_X_pow_card [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) ((X s : MvPowerSeries τ (WittVector p k)) ^ Fintype.card k) = 0 := by
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d t) h
  simp only [Finsupp.single_eq_same] at this
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same] at this
    have := two_le_card (k := k)
    omega
  · rw [Finsupp.single_eq_of_ne hts] at this
    exact one_ne_zero this

theorem coeff_single_fvec [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) (fvec p k τ s) = if t = s then (p : WittVector p k) else 0 := by
  rw [fvec, map_add, coeff_C_mul, coeff_index_single_X, coeff_single_X_pow_card, add_zero]
  split_ifs <;> simp

theorem comm_X [Finite τ] (s : τ) : Comm p k (X s : MvPowerSeries τ (WittVector p k)) := by
  unfold Comm
  rw [subst_X hasSubst_fvec]
  rfl

theorem constantCoeff_C_mul_X (s : τ) :
    constantCoeff (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) = 0 := by
  rw [map_mul, constantCoeff_X, mul_zero]

theorem comm_subst {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ (WittVector p k)}
    (hφ : Comm p k φ) {a : σ → MvPowerSeries τ (WittVector p k)}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, Comm p k (a s)) :
    Comm p k (subst a φ) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  unfold Comm at *
  calc C (p : WittVector p k) * subst a φ + subst a φ ^ Fintype.card k
      = subst a (C (p : WittVector p k) * φ + φ ^ Fintype.card k) := by
        rw [subst_add hsa, subst_mul hsa, subst_pow hsa, subst_C]
    _ = subst a (subst (fvec p k σ) φ) := by rw [hφ]
    _ = subst (fun s => subst a (fvec p k σ s)) φ :=
        subst_comp_subst_apply hasSubst_fvec hsa φ
    _ = subst (fun s => subst (fvec p k τ) (a s)) φ := by
        congr 1
        funext s
        show subst a (C (p : WittVector p k) * X s + X s ^ Fintype.card k) = _
        rw [subst_add hsa, subst_mul hsa, subst_C, subst_pow hsa, subst_X hsa]
        exact ha s
    _ = subst (fvec p k τ) (subst a φ) := (subst_comp_subst_apply hsa hasSubst_fvec φ).symm

end Family

section Leading

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem finsuppProd_C_mul_X_pow (m : τ →₀ ℕ) :
    (m.prod fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = C ((p : WittVector p k) ^ m.degree) * monomial m 1 := by
  have h : (fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = fun s e => C ((p : WittVector p k) ^ e) * X s ^ e := by
    funext s e
    rw [mul_pow, map_pow]
  rw [h, Finsupp.prod_mul, ← monomial_one_eq, ← map_finsuppProd]
  congr 2
  rw [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

theorem coeff_finsuppProd_fvec_pow {d m : τ →₀ ℕ} (hdm : d.degree = m.degree) :
    coeff d (m.prod fun s e => (fvec p k τ s) ^ e)
      = if d = m then (p : WittVector p k) ^ m.degree else 0 := by
  have hcc : ∀ s, ∀ e : τ →₀ ℕ, e.degree < 2 →
      coeff e (fvec p k τ s) = coeff e (C (p : WittVector p k) * X s) := by
    intro s e he
    rw [fvec, map_add, add_eq_left, coeff_X_pow, if_neg]
    intro h
    subst h
    rw [Finsupp.degree_single] at he
    have := two_le_card (k := k)
    omega
  have key := MvFormalGroup.coeff_finsuppProd_pow_sub_congr (N := 2) (by norm_num)
    (c := fvec p k τ) (c' := fun s => C (p : WittVector p k) * X s)
    constantCoeff_fvec constantCoeff_C_mul_X hcc (m := m) (d := d) (by omega)
  rw [key, finsuppProd_C_mul_X_pow, coeff_C_mul, coeff_monomial]
  split_ifs <;> simp

theorem coeff_subst_fvec {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (hθ : ∀ e : τ →₀ ℕ, e.degree < n → coeff e θ = 0) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (subst (fvec p k τ) θ) = (p : WittVector p k) ^ d.degree * coeff d θ := by
  rw [coeff_subst hasSubst_fvec, finsum_eq_single _ d]
  · rw [coeff_finsuppProd_fvec_pow rfl, if_pos rfl, smul_eq_mul, mul_comm]
  · intro m hm
    rcases lt_trichotomy m.degree d.degree with hlt | heq | hgt
    · rw [hθ m (by omega), zero_smul]
    · rw [coeff_finsuppProd_fvec_pow heq.symm, if_neg (Ne.symm hm), smul_zero]
    · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hgt,
        smul_zero]

end Leading

section Divisible

variable {τ : Type*}

include p in

theorem pow_card_eq_subst_X_pow (g : MvPowerSeries τ k) :
    g ^ Fintype.card k = subst (fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k) g := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card k p
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [hn, ← map_iterateFrobenius_expand p hp0 g n, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id, RingHom.id_apply]
  unfold MvPowerSeries.expand
  rw [substAlgHom_apply]

theorem map_defect_eq_zero [Finite τ] (θ : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k) (defect p k θ) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  rw [defect, map_sub, map_add, map_mul, map_pow, map_C, constantCoeff_natCast_p, map_zero,
    zero_mul, zero_add, map_subst hf, sub_eq_zero]
  have hfam : (fun s => MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k)
      (fvec p k τ s)) = fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k := by
    funext s
    simp only [fvec, map_add, map_mul, map_C, constantCoeff_natCast_p, map_zero, zero_mul,
      zero_add, map_pow, map_X]
  rw [hfam]
  exact pow_card_eq_subst_X_pow _

theorem exists_coeff_defect_eq_mul [Finite τ] (θ : MvPowerSeries τ (WittVector p k))
    (e : τ →₀ ℕ) : ∃ y : WittVector p k, coeff e (defect p k θ) = (p : WittVector p k) * y := by
  apply exists_eq_p_mul_of_coeff_zero
  rw [← WittVector.constantCoeff_apply, ← MvPowerSeries.coeff_map, map_defect_eq_zero, map_zero]

end Divisible

section Unique

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem eq_zero_or_single_of_degree_le_one {d : τ →₀ ℕ} (hd : d.degree ≤ 1) :
    d = 0 ∨ ∃ s, d = Finsupp.single s 1 := by
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · left
    exact (Finsupp.degree_eq_zero_iff d).mp (by omega)
  · right
    have hdeg : d.degree = 1 := le_antisymm hd h1
    have hmem : d ∈ {d' : τ →₀ ℕ | d'.degree = 1} := hdeg
    rw [← Finsupp.range_single_one] at hmem
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.symm⟩

theorem eq_of_comm {φ ψ : MvPowerSeries τ (WittVector p k)}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ)
    (hφ : Comm p k φ) (hψ : Comm p k ψ) : φ = ψ := by
  suffices key : ∀ n : ℕ, ∀ d : τ →₀ ℕ, d.degree ≤ n + 1 → coeff d φ = coeff d ψ from
    MvPowerSeries.ext fun d => key d.degree d (Nat.le_succ _)
  intro n
  induction n with
  | zero =>
    intro d hd
    rcases eq_zero_or_single_of_degree_le_one hd with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hφ0, hψ0]
    · exact h1 s
  | succ n IH =>
    intro d hd
    by_cases hlt : d.degree ≤ n + 1
    · exact IH d hlt
    have hdeg : d.degree = n + 2 := by omega
    have hf : HasSubst (fvec p k τ) := hasSubst_fvec
    have hδ : ∀ e : τ →₀ ℕ, e.degree < n + 2 → coeff e (φ - ψ) = 0 := by
      intro e he
      rw [map_sub, IH e (by omega), sub_self]
    have hpow : coeff d (φ ^ Fintype.card k) = coeff d (ψ ^ Fintype.card k) :=
      MvFormalGroup.coeff_pow_sub_congr (N := n + 2) (by omega) hφ0 hψ0
        (fun e he => IH e (by omega)) (by have := two_le_card (k := k); omega)
    have hsub : coeff d (subst (fvec p k τ) φ) - coeff d (subst (fvec p k τ) ψ)
        = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
      rw [← map_sub, ← subst_sub hf, coeff_subst_fvec hδ (le_of_eq hdeg), hdeg]
    have eφ := congrArg (coeff d) hφ
    have eψ := congrArg (coeff d) hψ
    simp only [map_add, coeff_C_mul] at eφ eψ
    have hc : (p : WittVector p k) * (1 - (p : WittVector p k) ^ (n + 1)) * coeff d (φ - ψ) = 0 := by
      have : (p : WittVector p k) * coeff d (φ - ψ)
          = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
        rw [← hsub, ← eφ, ← eψ, hpow, map_sub]
        ring
      linear_combination this
    rcases mul_eq_zero.mp hc with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' p_ne_zero'
      · exact absurd h' (one_sub_pow_ne_zero n)
    · rwa [map_sub, sub_eq_zero] at h

end Unique

section Exists

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

open scoped Classical in

def pdiv (x : WittVector p k) : WittVector p k :=
  if h : ∃ y : WittVector p k, x = (p : WittVector p k) * y then h.choose else 0

theorem pdiv_spec {x : WittVector p k} (h : ∃ y : WittVector p k, x = (p : WittVector p k) * y) :
    x = (p : WittVector p k) * pdiv x := by
  rw [pdiv, dif_pos h]
  exact h.choose_spec

def corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) : MvPowerSeries τ (WittVector p k) :=
  fun d => if d.degree = n + 2 then
    -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
      * pdiv (coeff d (defect p k θ)) else 0

theorem coeff_corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) (d : τ →₀ ℕ) :
    coeff d (corr θ n) = if d.degree = n + 2 then
      -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
        * pdiv (coeff d (defect p k θ)) else 0 := rfl

theorem coeff_corr_of_ne {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ} {d : τ →₀ ℕ}
    (hd : d.degree ≠ n + 2) : coeff d (corr θ n) = 0 := by
  rw [coeff_corr, if_neg hd]

def approx (c : τ → WittVector p k) : ℕ → MvPowerSeries τ (WittVector p k)
  | 0 => ∑ s, C (c s) * X s
  | n + 1 => approx c n + corr (approx c n) n

theorem approx_succ (c : τ → WittVector p k) (n : ℕ) :
    approx c (n + 1) = approx c n + corr (approx c n) n := rfl

theorem coeff_approx_zero (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (approx c 0) = ∑ s, if d = Finsupp.single s 1 then c s else 0 := by
  show coeff d (∑ s, C (c s) * X s) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

theorem coeff_approx_zero_of_degree_ne_one (c : τ → WittVector p k) {d : τ →₀ ℕ}
    (hd : d.degree ≠ 1) : coeff d (approx c 0) = 0 := by
  rw [coeff_approx_zero]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [if_neg]
  rintro rfl
  exact hd (Finsupp.degree_single s 1)

theorem coeff_single_approx_zero (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (approx c 0) = c t := by
  rw [coeff_approx_zero, Finset.sum_eq_single t]
  · rw [if_pos rfl]
  · intro s _ hst
    rw [if_neg]
    intro h
    exact hst (Finsupp.single_left_injective one_ne_zero h).symm
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem coeff_approx_of_le (c : τ → WittVector p k) {n m : ℕ} (hnm : n ≤ m) {d : τ →₀ ℕ}
    (hd : d.degree ≤ n + 1) : coeff d (approx c m) = coeff d (approx c n) := by
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ m IH =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [approx_succ, map_add, coeff_corr_of_ne (by omega), add_zero]
      exact IH (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      rfl

theorem constantCoeff_approx (c : τ → WittVector p k) (n : ℕ) : constantCoeff (approx c n) = 0 := by
  have h0 : ((0 : τ →₀ ℕ)).degree = 0 := (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_approx_of_le c (Nat.zero_le n) (by omega),
    coeff_approx_zero_of_degree_ne_one c (by omega)]

theorem coeff_single_approx (c : τ → WittVector p k) (n : ℕ) (t : τ) :
    coeff (Finsupp.single t 1) (approx c n) = c t := by
  rw [coeff_approx_of_le c (Nat.zero_le n) (by rw [Finsupp.degree_single]),
    coeff_single_approx_zero]

theorem coeff_defect_approx (c : τ → WittVector p k) (n : ℕ) {e : τ →₀ ℕ}
    (he : e.degree ≤ n + 1) : coeff e (defect p k (approx c n)) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  induction n generalizing e with
  | zero =>

    have hlin0 : ∀ e' : τ →₀ ℕ, e'.degree < 1 → coeff e' (approx c 0) = 0 :=
      fun e' he' => coeff_approx_zero_of_degree_ne_one c (by omega)
    rw [defect, map_sub, map_add, coeff_C_mul, coeff_subst_fvec hlin0 he,
      MvFormalGroup.coeff_pow_eq_zero_of_degree_lt (constantCoeff_approx c 0)
        (by have := two_le_card (k := k); omega), add_zero]
    rcases eq_zero_or_single_of_degree_le_one he with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_approx, mul_zero, mul_zero, sub_self]
    · rw [Finsupp.degree_single, pow_one, sub_self]
  | succ n IH =>

    set θ := approx c n with hθ
    have hθ0 : constantCoeff θ = 0 := constantCoeff_approx c n
    have hκ : ∀ e' : τ →₀ ℕ, e'.degree < n + 2 → coeff e' (corr θ n) = 0 :=
      fun e' he' => coeff_corr_of_ne (by omega)
    have hκ0 : constantCoeff (corr θ n) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hκ 0 (by rw [map_zero]; omega)
    have hθ'0 : constantCoeff (θ + corr θ n) = 0 := by rw [map_add, hθ0, hκ0, add_zero]

    have hpow : coeff e ((θ + corr θ n) ^ Fintype.card k) = coeff e (θ ^ Fintype.card k) :=
      MvFormalGroup.coeff_pow_sub_congr (N := n + 2) (by omega) hθ'0 hθ0
        (fun e' he' => by rw [map_add, hκ e' he', add_zero])
        (by have := two_le_card (k := k); omega)
    have hexp : coeff e (defect p k (θ + corr θ n))
        = coeff e (defect p k θ) + ((p : WittVector p k) * coeff e (corr θ n)
            - coeff e (subst (fvec p k τ) (corr θ n))) := by
      simp only [defect, map_sub, map_add, coeff_C_mul, mul_add, subst_add hf, hpow]
      ring
    rw [approx_succ, hexp]
    rcases Nat.lt_or_ge e.degree (n + 2) with hlt | hge
    · rw [IH (by omega), coeff_subst_fvec hκ (le_of_lt hlt), hκ e hlt, mul_zero, mul_zero,
        sub_self, add_zero]
    · have hedeg : e.degree = n + 2 := by omega
      rw [coeff_subst_fvec hκ (le_of_eq hedeg), hedeg, coeff_corr, if_pos hedeg]
      set u : (WittVector p k)ˣ := (isUnit_one_sub_pow (p := p) (k := k) n).unit with hu
      have hu' : (u : WittVector p k) = 1 - (p : WittVector p k) ^ (n + 1) := rfl
      have hdiv := pdiv_spec (exists_coeff_defect_eq_mul θ e)
      set y := pdiv (coeff e (defect p k θ)) with hy
      rw [hdiv]
      have hinv : (u : WittVector p k) * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) = 1 :=
        Units.mul_inv u
      linear_combination (-((p : WittVector p k) * y)) * hinv
        + ((p : WittVector p k) * y * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hu'

def ltSeries (c : τ → WittVector p k) : MvPowerSeries τ (WittVector p k) :=
  fun d => coeff d (approx c d.degree)

theorem coeff_ltSeries (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (ltSeries c) = coeff d (approx c d.degree) := rfl

theorem coeff_ltSeries_of_le (c : τ → WittVector p k) {n : ℕ} {d : τ →₀ ℕ} (hd : d.degree ≤ n + 1) :
    coeff d (ltSeries c) = coeff d (approx c n) := by
  rw [coeff_ltSeries]
  rcases Nat.lt_or_ge d.degree (n + 1) with h | h
  · rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · rw [h0]
      exact (coeff_approx_of_le c (Nat.zero_le n) (by omega)).symm
    · rw [coeff_approx_of_le c (show d.degree - 1 ≤ d.degree by omega) (by omega)]
      exact (coeff_approx_of_le c (show d.degree - 1 ≤ n by omega) (by omega)).symm
  · exact coeff_approx_of_le c (by omega) (by omega)

theorem constantCoeff_ltSeries (c : τ → WittVector p k) : constantCoeff (ltSeries c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ltSeries_of_le c (n := 0) (by rw [map_zero]; omega),
    coeff_zero_eq_constantCoeff_apply, constantCoeff_approx]

theorem coeff_single_ltSeries (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (ltSeries c) = c t := by
  rw [coeff_ltSeries_of_le c (n := 0) (by rw [Finsupp.degree_single]), coeff_single_approx]

theorem coeff_defect_congr {θ θ' : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e θ = coeff e θ') {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (defect p k θ) = coeff d (defect p k θ') := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  have hpow : coeff d (θ ^ Fintype.card k) = coeff d (θ' ^ Fintype.card k) :=
    MvFormalGroup.coeff_pow_congr h hd
  have hsub : coeff d (subst (fvec p k τ) θ) = coeff d (subst (fvec p k τ) θ') := by
    rw [← sub_eq_zero, ← map_sub, ← subst_sub hf, coeff_subst hf,
      finsum_eq_zero_of_forall_eq_zero]
    intro m
    rcases Nat.lt_or_ge d.degree m.degree with hlt | hge
    · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hlt,
        smul_zero]
    · rw [map_sub, h m (by omega), sub_self, zero_smul]
  rw [defect, defect, map_sub, map_sub, map_add, map_add, coeff_C_mul, coeff_C_mul, h d hd, hpow,
    hsub]

theorem comm_ltSeries (c : τ → WittVector p k) : Comm p k (ltSeries c) := by
  unfold Comm
  rw [← sub_eq_zero]
  change defect p k (ltSeries c) = 0
  refine MvPowerSeries.ext fun d => ?_
  rw [map_zero, coeff_defect_congr (θ' := approx c d.degree) (n := d.degree)
    (fun e he => coeff_ltSeries_of_le c (by omega)) le_rfl]
  exact coeff_defect_approx c d.degree (Nat.le_succ _)

end Exists

end CerednikDrinfeld.LubinTateLemma

end

universe u v in
open CerednikDrinfeld.LubinTateLemma in
theorem CerednikDrinfeld.LubinTateLemma.existsUnique_series
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
    (τ : Type v) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ := by
  classical
  haveI : Fintype τ := Fintype.ofFinite τ
  refine ⟨ltSeries c, ⟨constantCoeff_ltSeries c, coeff_single_ltSeries c, comm_ltSeries c⟩, ?_⟩
  rintro ψ ⟨hψ0, hψ1, hψ⟩
  exact eq_of_comm hψ0 (constantCoeff_ltSeries c) (fun s => by rw [hψ1, coeff_single_ltSeries])
    hψ (comm_ltSeries c)

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.LubinTate

universe u v

variable {p : ℕ} [Fact p.Prime]

instance instFintypeGaloisFieldTwo : Fintype (GaloisField p 2) := Fintype.ofFinite _

theorem card_GF : Fintype.card (GaloisField p 2) = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 two_ne_zero]

theorem two_le_card : 2 ≤ Fintype.card (GaloisField p 2) := Fintype.one_lt_card

local notation "𝕆" => Zp2 p
local notation "𝔮" => Fintype.card (GaloisField p 2)

theorem frobenius_frobenius (a : 𝕆) : WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← sq,
    ← card_GF, FiniteField.pow_card]

theorem exists_pow_ne : ∃ ω : GaloisField p 2, ω ^ p ≠ ω := by
  classical
  by_contra h
  push Not at h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P : Polynomial (GaloisField p 2) := Polynomial.X ^ p - Polynomial.X with hP
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hp1
  have hdeg : P.natDegree = p := Polynomial.natDegree_X_pow_sub_X hp1
  have hroots : ∀ ω : GaloisField p 2, ω ∈ P.roots := by
    intro ω
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h ω, sub_self]
  have hcard : Fintype.card (GaloisField p 2) ≤ p := by
    calc Fintype.card (GaloisField p 2) = (Finset.univ : Finset (GaloisField p 2)).card :=
          Finset.card_univ.symm
      _ ≤ P.roots.toFinset.card :=
          Finset.card_le_card fun ω _ => Multiset.mem_toFinset.mpr (hroots ω)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hdeg
  rw [card_GF, sq] at hcard
  have : p * p ≤ p * 1 := by simpa using hcard
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem exists_isUnit_frobenius_sub : ∃ a : 𝕆, IsUnit (WittVector.frobenius a - a) := by
  obtain ⟨ω, hω⟩ := exists_pow_ne (p := p)
  refine ⟨WittVector.teichmuller p ω, WittVector.isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr hω

variable (p)

def fvec (τ : Type*) : τ → MvPowerSeries τ 𝕆 :=
  fun s => C (p : 𝕆) * X s + X s ^ 𝔮

def Comm {τ : Type*} (φ : MvPowerSeries τ 𝕆) : Prop :=
  C (p : 𝕆) * φ + φ ^ 𝔮 = subst (fvec p τ) φ

theorem lt_existsUnique (τ : Type*) [Finite τ] (c : τ → 𝕆) :
    ∃! φ : MvPowerSeries τ 𝕆, constantCoeff φ = 0 ∧
      (∀ s, coeff (Finsupp.single s 1) φ = c s) ∧ Comm p φ :=
  CerednikDrinfeld.LubinTateLemma.existsUnique_series p (GaloisField p 2) τ c

def lt (τ : Type*) [Finite τ] (c : τ → 𝕆) : MvPowerSeries τ 𝕆 :=
  (lt_existsUnique p τ c).exists.choose

variable {p}

section LT

variable {τ : Type*}

theorem lt_spec [Finite τ] (c : τ → 𝕆) :
    constantCoeff (lt p τ c) = 0 ∧ (∀ s, coeff (Finsupp.single s 1) (lt p τ c) = c s) ∧
      Comm p (lt p τ c) :=
  (lt_existsUnique p τ c).exists.choose_spec

theorem constantCoeff_lt [Finite τ] (c : τ → 𝕆) : constantCoeff (lt p τ c) = 0 := (lt_spec c).1

theorem coeff_single_lt [Finite τ] (c : τ → 𝕆) (s : τ) :
    coeff (Finsupp.single s 1) (lt p τ c) = c s := (lt_spec c).2.1 s

theorem comm_lt [Finite τ] (c : τ → 𝕆) : Comm p (lt p τ c) := (lt_spec c).2.2

theorem eq_of_comm [Finite τ] {φ ψ : MvPowerSeries τ 𝕆}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0) (hφ : Comm p φ) (hψ : Comm p ψ)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ) : φ = ψ :=
  (lt_existsUnique p τ fun s => coeff (Finsupp.single s 1) ψ).unique ⟨hφ0, h1, hφ⟩
    ⟨hψ0, fun _ => rfl, hψ⟩

theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p τ s) = 0 := by
  have h0 : 𝔮 ≠ 0 := by have := two_le_card (p := p); omega
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow h0, add_zero]

theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

theorem coeff_single_X_pow_card [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) ((X s : MvPowerSeries τ 𝕆) ^ 𝔮) = 0 := by
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d t) h
  simp only [Finsupp.single_eq_same] at this
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same] at this
    have := two_le_card (p := p)
    omega
  · rw [Finsupp.single_eq_of_ne hts] at this
    exact one_ne_zero this

theorem coeff_single_fvec [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) (fvec p τ s) = if t = s then (p : 𝕆) else 0 := by
  rw [fvec, map_add, coeff_C_mul, coeff_index_single_X, coeff_single_X_pow_card, add_zero]
  split_ifs <;> simp

theorem comm_X [Finite τ] (s : τ) : Comm p (X s : MvPowerSeries τ 𝕆) := by
  unfold Comm
  rw [subst_X hasSubst_fvec]
  rfl

theorem comm_fvec [Finite τ] (s : τ) : Comm p (fvec p τ s) := by
  have hf : HasSubst (fvec p τ) := hasSubst_fvec
  unfold Comm
  conv_rhs => rw [fvec]
  rw [subst_add hf, subst_mul hf, subst_C, subst_pow hf, subst_X hf]

theorem comm_subst {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) {a : σ → MvPowerSeries τ 𝕆}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, Comm p (a s)) :
    Comm p (subst a φ) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  unfold Comm at *
  calc C (p : 𝕆) * subst a φ + subst a φ ^ 𝔮
      = subst a (C (p : 𝕆) * φ + φ ^ 𝔮) := by
        rw [subst_add hsa, subst_mul hsa, subst_pow hsa, subst_C]
    _ = subst a (subst (fvec p σ) φ) := by rw [hφ]
    _ = subst (fun s => subst a (fvec p σ s)) φ :=
        subst_comp_subst_apply hasSubst_fvec hsa φ
    _ = subst (fun s => subst (fvec p τ) (a s)) φ := by
        congr 1
        funext s
        show subst a (C (p : 𝕆) * X s + X s ^ 𝔮) = _
        rw [subst_add hsa, subst_mul hsa, subst_C, subst_pow hsa, subst_X hsa]
        exact ha s
    _ = subst (fvec p τ) (subst a φ) := (subst_comp_subst_apply hsa hasSubst_fvec φ).symm

theorem comm_subst_X {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) (e : σ → τ) :
    Comm p (subst (fun s => (X (e s) : MvPowerSeries τ 𝕆)) φ) :=
  comm_subst hφ (fun _ => constantCoeff_X _) fun _ => comm_X _

theorem constantCoeff_subst_of {σ : Type*} [Finite σ] {φ : MvPowerSeries σ 𝕆}
    (hφ : constantCoeff φ = 0) {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) :
    constantCoeff (subst a φ) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha0) ha0 hφ

theorem coeff_single_subst_lt {σ : Type*} [Fintype σ] [Fintype τ] (c : σ → 𝕆)
    {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (lt p σ c)) = ∑ s, c s * coeff (Finsupp.single t 1) (a s) := by
  rw [MvFormalGroup.coeff_single_subst ha0]
  simp only [coeff_single_lt]

end LT

section FrobeniusInvariance

variable {τ : Type*}

local notation "σ" => (WittVector.frobenius : Zp2 p →+* Zp2 p)

theorem map_frobenius_fvec (s : τ) : MvPowerSeries.map σ (fvec p τ s) = fvec p τ s := by
  rw [fvec, map_add, map_mul, map_C, map_natCast, map_X, map_pow, map_X]

theorem comm_map_frobenius [Finite τ] {φ : MvPowerSeries τ 𝕆} (hφ : Comm p φ) :
    Comm p (MvPowerSeries.map σ φ) := by
  unfold Comm at *
  have h := congrArg (MvPowerSeries.map σ) hφ
  rw [map_add, map_mul, map_C, map_natCast, map_pow, map_subst hasSubst_fvec] at h
  rw [h]
  congr 1
  funext s
  exact map_frobenius_fvec s

theorem map_frobenius_lt [Finite τ] (c : τ → 𝕆) :
    MvPowerSeries.map σ (lt p τ c) = lt p τ fun s => σ (c s) := by
  classical
  refine eq_of_comm ?_ (constantCoeff_lt _) (comm_map_frobenius (comm_lt c)) (comm_lt _) fun s => ?_
  · rw [constantCoeff_map, constantCoeff_lt, map_zero]
  · rw [coeff_map, coeff_single_lt, coeff_single_lt]

end FrobeniusInvariance

section Sigma

variable (p)

def sigmaSeries : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆 := lt p (Fin 1 ⊕ Fin 1) fun _ => 1

def act₁ (a : 𝕆) : MvPowerSeries (Fin 1) 𝕆 := lt p (Fin 1) fun _ => a

variable {p}

theorem constantCoeff_sigmaSeries : constantCoeff (sigmaSeries p) = 0 := constantCoeff_lt _

theorem comm_sigmaSeries : Comm p (sigmaSeries p) := comm_lt _

theorem coeff_single_sigmaSeries (v : Fin 1 ⊕ Fin 1) :
    coeff (Finsupp.single v 1) (sigmaSeries p) = 1 := by
  rw [sigmaSeries, coeff_single_lt]

theorem coeff_single_subst_sigmaSeries {τ : Type*} [Fintype τ]
    {a : Fin 1 ⊕ Fin 1 → MvPowerSeries τ 𝕆} (ha0 : ∀ v, constantCoeff (a v) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (sigmaSeries p))
      = coeff (Finsupp.single t 1) (a (Sum.inl 0)) + coeff (Finsupp.single t 1) (a (Sum.inr 0)) := by
  rw [sigmaSeries, coeff_single_subst_lt _ ha0, Fintype.sum_sum_type]
  simp only [one_mul, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]

theorem constantCoeff_act₁ (a : 𝕆) : constantCoeff (act₁ p a) = 0 := constantCoeff_lt _

theorem comm_act₁ (a : 𝕆) : Comm p (act₁ p a) := comm_lt _

theorem coeff_single_act₁ (a : 𝕆) (s : Fin 1) : coeff (Finsupp.single s 1) (act₁ p a) = a := by
  rw [act₁, coeff_single_lt]

theorem coeff_single_subst_act₁ {τ : Type*} [Fintype τ] (a : 𝕆)
    {b : Fin 1 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (act₁ p a)) = a * coeff (Finsupp.single t 1) (b 0) := by
  rw [act₁, coeff_single_subst_lt _ hb0]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]

theorem hasSubst_fin1 {τ : Type*} {x : MvPowerSeries τ 𝕆} (hx : constantCoeff x = 0) :
    HasSubst (fun _ : Fin 1 => x) :=
  hasSubst_of_constantCoeff_zero fun _ => hx

variable (p) in

def sigma : MvFormalGroup 1 𝕆 where
  toPowerSeries := fun _ => sigmaSeries p
  constantCoeff_eq_zero := fun _ => constantCoeff_sigmaSeries
  coeff_single_inl i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  coeff_single_inr i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  assoc i := by
    classical
    have hB : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hC : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hBv : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) = fun s => X (Sum.elim (fun l => Sum.inl l)
          (fun l => Sum.inr (Sum.inl l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hCv : (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) = fun s => X (Sum.elim (fun l => Sum.inr (Sum.inl l))
          (fun l => Sum.inr (Sum.inr l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hA : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun _ : Fin 1 => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
          fun l => X (Sum.inr (Sum.inl l))) (sigmaSeries p))
        fun j => X (Sum.inr (Sum.inr j))) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_subst_of constantCoeff_sigmaSeries hB
      · exact constantCoeff_X _
    have hA' : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun _ : Fin 1 => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
          fun l => X (Sum.inr (Sum.inr l))) (sigmaSeries p)) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_of constantCoeff_sigmaSeries hC
    refine eq_of_comm (constantCoeff_subst_of constantCoeff_sigmaSeries hA)
      (constantCoeff_subst_of constantCoeff_sigmaSeries hA') ?_ ?_ ?_
    · refine comm_subst comm_sigmaSeries hA ?_
      rintro (j | j)
      · show Comm p (subst _ (sigmaSeries p))
        rw [hBv]
        exact comm_subst_X comm_sigmaSeries _
      · exact comm_X _
    · refine comm_subst comm_sigmaSeries hA' ?_
      rintro (j | j)
      · exact comm_X _
      · show Comm p (subst _ (sigmaSeries p))
        rw [hCv]
        exact comm_subst_X comm_sigmaSeries _
    · intro t
      rw [coeff_single_subst_sigmaSeries hA, coeff_single_subst_sigmaSeries hA']
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [coeff_single_subst_sigmaSeries hB, coeff_single_subst_sigmaSeries hC]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact add_assoc _ _ _

@[simp] theorem sigma_toPowerSeries (i : Fin 1) : (sigma p).toPowerSeries i = sigmaSeries p := rfl

instance sigma_isComm : (sigma p).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (sigmaSeries p) = sigmaSeries p
    refine eq_of_comm (constantCoeff_subst_of constantCoeff_sigmaSeries hS)
      constantCoeff_sigmaSeries ?_ comm_sigmaSeries ?_
    · rw [hSv]
      exact comm_subst_X comm_sigmaSeries _
    · intro t
      rw [coeff_single_subst_sigmaSeries hS, coeff_single_sigmaSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      rcases t with l | l <;> rw [Fin.fin_one_eq_zero l] <;> simp

theorem constantCoeff_homFamily₁ {φ : MvPowerSeries (Fin 1) 𝕆} (hφ : constantCoeff φ = 0) :
    ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) s) = 0 := by
  rintro (j | j) <;> exact constantCoeff_subst_of hφ (fun l => constantCoeff_X _)

theorem subst_sigma_eq_of_comm {φ : MvPowerSeries (Fin 1) 𝕆} (h0 : constantCoeff φ = 0)
    (hc : Comm p φ) :
    subst (sigma p).toPowerSeries φ =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        (sigmaSeries p) := by
  classical
  have hF : ∀ j : Fin 1, constantCoeff ((sigma p).toPowerSeries j) = 0 :=
    fun _ => constantCoeff_sigmaSeries
  have hA := constantCoeff_homFamily₁ h0
  refine eq_of_comm (constantCoeff_subst_of h0 hF)
    (constantCoeff_subst_of constantCoeff_sigmaSeries hA)
    (comm_subst hc hF fun _ => comm_sigmaSeries) (comm_subst comm_sigmaSeries hA ?_) ?_
  · rintro (j | j) <;> exact comm_subst_X hc _
  · intro t
    rw [coeff_single_subst_sigmaSeries hA, MvFormalGroup.coeff_single_subst hF]
    simp only [Sum.elim_inl, Sum.elim_inr, sigma_toPowerSeries, coeff_single_sigmaSeries,
      Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
    rw [MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _),
      MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _)]
    simp only [coeff_index_single_X, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, mul_ite, mul_one, mul_zero]
    rcases t with l | l <;> rw [Fin.fin_one_eq_zero l] <;> simp

theorem subst_sigma_act₁ (a : 𝕆) :
    subst (sigma p).toPowerSeries (act₁ p a) =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) (act₁ p a))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) (act₁ p a))
        (sigmaSeries p) :=
  subst_sigma_eq_of_comm (constantCoeff_act₁ a) (comm_act₁ a)

theorem act₁_one : act₁ p 1 = X 0 := by
  classical
  refine eq_of_comm (constantCoeff_act₁ 1) (constantCoeff_X 0) (comm_act₁ 1) (comm_X 0) fun s => ?_
  rw [coeff_single_act₁, coeff_index_single_X, if_pos (Subsingleton.elim s 0)]

theorem act₁_zero : act₁ p 0 = 0 := by
  classical
  have h0 : Comm p (0 : MvPowerSeries (Fin 1) 𝕆) := by
    unfold Comm
    have hq : Fintype.card (GaloisField p 2) ≠ 0 := by have := two_le_card (p := p); omega
    rw [mul_zero, zero_pow hq, add_zero, ← coe_substAlgHom hasSubst_fvec, map_zero]
  refine eq_of_comm (constantCoeff_act₁ 0) (map_zero _) (comm_act₁ 0) h0 fun s => ?_
  rw [coeff_single_act₁, map_zero]

theorem act₁_mul (a b : 𝕆) : act₁ p (a * b) = subst (fun _ : Fin 1 => act₁ p b) (act₁ p a) := by
  classical
  refine eq_of_comm (constantCoeff_act₁ _)
    (constantCoeff_subst_of (constantCoeff_act₁ a) (fun _ => constantCoeff_act₁ b))
    (comm_act₁ _) (comm_subst (comm_act₁ a) (fun _ => constantCoeff_act₁ b) fun _ => comm_act₁ b)
    fun s => ?_
  rw [coeff_single_act₁, coeff_single_subst_act₁ a (fun _ => constantCoeff_act₁ b),
    coeff_single_act₁]

theorem act₁_add (a b : 𝕆) :
    act₁ p (a + b) = subst (Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b)
      (sigmaSeries p) := by
  classical
  have hab : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff
      ((Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b) s) = 0 := by
    rintro (j | j) <;> exact constantCoeff_act₁ _
  refine eq_of_comm (constantCoeff_act₁ _) (constantCoeff_subst_of constantCoeff_sigmaSeries hab)
    (comm_act₁ _) (comm_subst comm_sigmaSeries hab ?_) fun s => ?_
  · rintro (j | j) <;> exact comm_act₁ _
  · rw [coeff_single_act₁, coeff_single_subst_sigmaSeries hab]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_act₁]

theorem act₁_natCast_p :
    act₁ p (p : 𝕆) = C (p : 𝕆) * X 0 + X 0 ^ Fintype.card (GaloisField p 2) := by
  classical
  refine eq_of_comm (constantCoeff_act₁ _) (constantCoeff_fvec 0) (comm_act₁ _) (comm_fvec 0)
    fun s => ?_
  show _ = coeff _ (fvec p (Fin 1) 0)
  rw [coeff_single_act₁, coeff_single_fvec, if_pos (Subsingleton.elim s 0)]

theorem map_frobenius_sigmaSeries :
    MvPowerSeries.map WittVector.frobenius (sigmaSeries p) = sigmaSeries p := by
  rw [sigmaSeries, map_frobenius_lt]
  simp only [map_one]

theorem map_frobenius_act₁ (a : 𝕆) :
    MvPowerSeries.map WittVector.frobenius (act₁ p a) = act₁ p (WittVector.frobenius a) := by
  rw [act₁, map_frobenius_lt]
  rfl

end Sigma

section Reduction

instance instIsCommMap {g : ℕ} {R S : Type*} [CommRing R] [CommRing S] (F : MvFormalGroup g R)
    [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  have hS : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j) <;> exact constantCoeff_X _
  rw [map_subst hS] at key
  have hfam : (fun s => MvPowerSeries.map f (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun j => X (Sum.inl j)) s))
      = Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

variable {B : Type u} [CommRing B]

theorem map_homIdentity₁ (f : 𝕆 →+* B) {F : Fin 1 → MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆}
    (hF : ∀ i, constantCoeff (F i) = 0) {G : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆}
    {φ : MvPowerSeries (Fin 1) 𝕆} (hφ : constantCoeff φ = 0)
    (h : subst F φ = subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) G) :
    subst (fun i => MvPowerSeries.map f (F i)) (MvPowerSeries.map f φ) = subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ)) (MvPowerSeries.map f G) := by
  have hXl : ∀ l : Fin 1, constantCoeff
      ((X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) = 0 := fun l => constantCoeff_X _
  have hXr : ∀ l : Fin 1, constantCoeff
      ((X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) = 0 := fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl hφ
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr hφ
  have key := congrArg (MvPowerSeries.map f) h
  rw [map_subst (hasSubst_of_constantCoeff_zero hF), map_subst hA] at key
  have hAmap : (fun s => MvPowerSeries.map f (Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) s))
      = Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ) := by
    funext s
    rcases s with j | j
    · show MvPowerSeries.map f (subst _ φ) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXl)]
      simp only [MvPowerSeries.map_X, Sum.elim_inl]
    · show MvPowerSeries.map f (subst _ φ) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXr)]
      simp only [MvPowerSeries.map_X, Sum.elim_inr]
  rw [hAmap] at key
  exact key

variable (j : Zp2 p →+* B)

def sigmaBar : MvFormalGroup 1 B := (sigma p).map j

@[simp] theorem sigmaBar_toPowerSeries (i : Fin 1) :
    (sigmaBar j).toPowerSeries i = MvPowerSeries.map j (sigmaSeries p) := rfl

instance sigmaBar_isComm : (sigmaBar j).IsComm := instIsCommMap _ _

def rhoEnd (a : 𝕆) : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => MvPowerSeries.map j (act₁ p a)
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_map, constantCoeff_act₁, map_zero]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i]
    exact map_homIdentity₁ j (fun _ => constantCoeff_sigmaSeries) (constantCoeff_act₁ a)
      (subst_sigma_act₁ a)

@[simp] theorem rhoEnd_toPowerSeries (a : 𝕆) (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (rhoEnd j a) i = MvPowerSeries.map j (act₁ p a) := rfl

theorem toPowerSeries_fin1 {F : MvFormalGroup 1 B} (e : MvFormalGroup.End F) :
    MvFormalGroup.Hom.toPowerSeries e = fun _ => MvFormalGroup.Hom.toPowerSeries e 0 := by
  funext i; rw [Fin.fin_one_eq_zero i]

def rho : 𝕆 →+* MvFormalGroup.End (sigmaBar j) where
  toFun := rhoEnd j
  map_one' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_one, MvPowerSeries.map_X, MvFormalGroup.End.toPowerSeries_one,
      Fin.fin_one_eq_zero i]
  map_mul' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, MvFormalGroup.End.toPowerSeries_mul, act₁_mul,
      map_subst (hasSubst_fin1 (constantCoeff_act₁ b))]
    rfl
  map_zero' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_zero, map_zero, MvFormalGroup.End.toPowerSeries_zero]
  map_add' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    have hab : HasSubst (Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l) <;> exact constantCoeff_act₁ _
    rw [rhoEnd_toPowerSeries, MvFormalGroup.End.toPowerSeries_add, act₁_add, map_subst hab]
    dsimp only
    rw [sigmaBar_toPowerSeries]
    congr 1
    funext s
    rcases s with l | l <;> rfl

theorem rho_toPowerSeries (a : 𝕆) (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (rho j a) i = MvPowerSeries.map j (act₁ p a) := rfl

theorem coeff_single_rho (a : 𝕆) :
    coeff (Finsupp.single 0 1) (MvFormalGroup.Hom.toPowerSeries (rho j a) 0) = j a := by
  rw [rho_toPowerSeries, coeff_map, coeff_single_act₁]

variable [CharP B p]

theorem rho_p_toPowerSeries :
    MvFormalGroup.Hom.toPowerSeries (rho j (p : 𝕆)) 0 = (X 0 : MvPowerSeries (Fin 1) B) ^ p ^ 2 := by
  rw [rho_toPowerSeries, act₁_natCast_p, map_add, map_mul, map_C, map_natCast, CharP.cast_eq_zero,
    map_zero, zero_mul, zero_add, map_pow, MvPowerSeries.map_X, card_GF]

theorem j_eq_teichmuller (x : 𝕆) : j x = j (WittVector.teichmuller p (x.coeff 0)) := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈ Ideal.span {(p : 𝕆)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  have : j (x - WittVector.teichmuller p (x.coeff 0)) = 0 := by
    rw [← hd, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]
  rwa [map_sub, sub_eq_zero] at this

theorem j_frobenius (x : 𝕆) : j (WittVector.frobenius x) = j x ^ p := by
  rw [j_eq_teichmuller j (WittVector.frobenius x), j_eq_teichmuller j x,
    WittVector.coeff_frobenius_charP, map_pow, map_pow]

theorem map_frobenius_map_j {τ : Type*} (y : MvPowerSeries τ 𝕆) :
    MvPowerSeries.map (frobenius B p) (MvPowerSeries.map j y) =
      MvPowerSeries.map j (MvPowerSeries.map WittVector.frobenius y) := by
  ext m
  simp only [coeff_map, frobenius_def, j_frobenius]

theorem hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero

theorem pow_p_eq_expand_map {τ : Type*} (y : MvPowerSeries τ B) :
    y ^ p = expand p hp0 (MvPowerSeries.map (frobenius B p) y) := by
  rw [← map_frobenius_expand p hp0, map_expand]

theorem sigmaBar_pow_p :
    (MvPowerSeries.map j (sigmaSeries p)) ^ p =
      subst (fun s : Fin 1 ⊕ Fin 1 => (X s : MvPowerSeries (Fin 1 ⊕ Fin 1) B) ^ p)
        (MvPowerSeries.map j (sigmaSeries p)) := by
  rw [pow_p_eq_expand_map, map_frobenius_map_j, map_frobenius_sigmaSeries, expand, coe_substAlgHom]

def phi : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => (X 0 : MvPowerSeries (Fin 1) B) ^ p
  constantCoeff_eq_zero := fun _ => by rw [map_pow, constantCoeff_X, zero_pow hp0]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i, sigmaBar_toPowerSeries, subst_pow (sigmaBar j).hasSubst_toPowerSeries,
      subst_X (sigmaBar j).hasSubst_toPowerSeries, sigmaBar_toPowerSeries, sigmaBar_pow_p]
    congr 1
    funext s
    rcases s with l | l
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inl,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inr,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]

@[simp] theorem phi_toPowerSeries (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (phi j) i = (X 0 : MvPowerSeries (Fin 1) B) ^ p := rfl

theorem phi_mul_rho (a : 𝕆) : phi j * rho j a = rho j (WittVector.frobenius a) * phi j := by
  apply MvFormalGroup.Hom.ext
  funext i
  rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul]
  dsimp only
  rw [phi_toPowerSeries,
    subst_pow (rho j a).hasSubst_toPowerSeries, subst_X (rho j a).hasSubst_toPowerSeries,
    rho_toPowerSeries, rho_toPowerSeries, pow_p_eq_expand_map, map_frobenius_map_j, map_frobenius_act₁,
    expand, coe_substAlgHom]
  congr 1
  funext s
  rw [phi_toPowerSeries, Fin.fin_one_eq_zero s]

theorem phi_mul_phi : phi j * phi j = rho j (p : 𝕆) := by
  apply MvFormalGroup.Hom.ext
  funext i
  rw [MvFormalGroup.End.toPowerSeries_mul]
  dsimp only
  rw [phi_toPowerSeries, subst_pow (phi j).hasSubst_toPowerSeries,
    subst_X (phi j).hasSubst_toPowerSeries, phi_toPowerSeries, ← pow_mul, ← sq, Fin.fin_one_eq_zero i,
    rho_p_toPowerSeries]

theorem rho_mul_comm (a b : 𝕆) : rho j a * rho j b = rho j b * rho j a := by
  rw [← map_mul, ← map_mul, mul_comm]

end Reduction

end CerednikDrinfeld.LubinTate

end

section BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.BoxBasisLemma

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

abbrev powIdeal (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) :=
  Ideal.span (Set.range fun i : Fin g => (X i : MvPowerSeries (Fin g) R) ^ N i)

def InBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Prop := ∀ i, d i < N i

instance instDecidableInBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Decidable (InBox N d) := by
  unfold InBox; infer_instance

def boxKer (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) where
  carrier := {θ | ∀ d : Fin g →₀ ℕ, InBox N d → coeff d θ = 0}
  zero_mem' := fun d _ => map_zero _
  add_mem' := by
    intro a b ha hb d hd
    rw [map_add, ha d hd, hb d hd, add_zero]
  smul_mem' := by
    intro c θ hθ d hd
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : InBox N x.2 := fun i => lt_of_le_of_lt (by rw [← hx]; simp) (hd i)
    rw [hθ x.2 hx2, mul_zero]

theorem mem_boxKer {θ : MvPowerSeries (Fin g) R} :
    θ ∈ boxKer R g N ↔ ∀ d : Fin g →₀ ℕ, InBox N d → coeff d θ = 0 := Iff.rfl

theorem X_pow_mem_boxKer (i : Fin g) :
    (X i : MvPowerSeries (Fin g) R) ^ N i ∈ boxKer R g N := by
  classical
  intro d hd
  rw [coeff_X_pow, if_neg]
  rintro rfl
  have := hd i
  rw [Finsupp.single_eq_same] at this
  exact lt_irrefl _ this

theorem powIdeal_le_boxKer : powIdeal R g N ≤ boxKer R g N :=
  Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact X_pow_mem_boxKer i)

def part (N : Fin g → ℕ) (θ : MvPowerSeries (Fin g) R) (i : Fin g) : MvPowerSeries (Fin g) R :=
  fun e => if (∀ j, j < i → e j < N j) then coeff (e + Finsupp.single i (N i)) θ else 0

theorem coeff_part (θ : MvPowerSeries (Fin g) R) (i : Fin g) (e : Fin g →₀ ℕ) :
    coeff e (part N θ i)
      = if (∀ j, j < i → e j < N j) then coeff (e + Finsupp.single i (N i)) θ else 0 :=
  rfl

theorem coeff_X_pow_mul_part (θ : MvPowerSeries (Fin g) R) (i : Fin g) (d : Fin g →₀ ℕ) :
    coeff d ((X i : MvPowerSeries (Fin g) R) ^ N i * part N θ i)
      = if (N i ≤ d i ∧ ∀ j, j < i → d j < N j) then coeff d θ else 0 := by
  classical
  rw [X_pow_eq, coeff_monomial_mul, one_mul]
  by_cases hi : N i ≤ d i
  · have hle : Finsupp.single i (N i) ≤ d := Finsupp.single_le_iff.mpr hi
    rw [if_pos hle, coeff_part]
    have hsub : ∀ j, j < i → (d - Finsupp.single i (N i)) j = d j := by
      intro j hj
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne (ne_of_lt hj), Nat.sub_zero]
    by_cases hj : ∀ j, j < i → d j < N j
    · rw [if_pos (fun j hj' => by rw [hsub j hj']; exact hj j hj'), if_pos ⟨hi, hj⟩,
        tsub_add_cancel_of_le hle]
    · rw [if_neg (fun h => hj fun j hj' => by rw [← hsub j hj']; exact h j hj'), if_neg]
      exact fun h => hj h.2
  · rw [if_neg (fun h => hi (Finsupp.single_le_iff.mp h)), if_neg]
    exact fun h => hi h.1

theorem eq_sum_X_pow_mul_part {θ : MvPowerSeries (Fin g) R} (hθ : θ ∈ boxKer R g N) :
    θ = ∑ i, (X i : MvPowerSeries (Fin g) R) ^ N i * part N θ i := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sum]
  simp_rw [coeff_X_pow_mul_part]
  by_cases hd : InBox N d
  · rw [hθ d hd, Finset.sum_eq_zero]
    intro i _
    rw [if_neg]
    exact fun h => absurd (hd i) (not_lt.mpr h.1)
  ·
    have hne : (Finset.univ.filter fun i : Fin g => N i ≤ d i).Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
      exact hd fun i => not_le.mp (hc (Finset.mem_univ i))
    set i₀ := (Finset.univ.filter fun i : Fin g => N i ≤ d i).min' hne with hi₀
    have hi₀mem : N i₀ ≤ d i₀ := by
      have := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at this
      exact this.2
    have hi₀min : ∀ j, j < i₀ → d j < N j := by
      intro j hj
      by_contra hc
      have hjmem : j ∈ Finset.univ.filter fun i : Fin g => N i ≤ d i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_lt.mp hc⟩
      exact absurd (Finset.min'_le _ j hjmem) (not_le.mpr hj)
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos ⟨hi₀mem, hi₀min⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨hj1, hj2⟩
      rcases lt_trichotomy j i₀ with hlt | heq | hgt
      · exact absurd (hi₀min j hlt) (not_lt.mpr hj1)
      · exact hj heq
      · exact absurd (hj2 i₀ hgt) (not_lt.mpr hi₀mem)
    · intro h
      exact absurd (Finset.mem_univ i₀) h

theorem boxKer_le_powIdeal : boxKer R g N ≤ powIdeal R g N := by
  intro θ hθ
  rw [eq_sum_X_pow_mul_part hθ]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem powIdeal_eq_boxKer : powIdeal R g N = boxKer R g N :=
  le_antisymm powIdeal_le_boxKer boxKer_le_powIdeal

def toFinsupp (u : (i : Fin g) → Fin (N i)) : Fin g →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i : ℕ)

@[simp] theorem toFinsupp_apply (u : (i : Fin g) → Fin (N i)) (i : Fin g) : toFinsupp u i = u i := rfl

theorem inBox_toFinsupp (u : (i : Fin g) → Fin (N i)) : InBox N (toFinsupp u) := fun i => (u i).isLt

def extend (v : ((i : Fin g) → Fin (N i)) → R) : MvPowerSeries (Fin g) R :=
  fun d => if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0

theorem coeff_extend (v : ((i : Fin g) → Fin (N i)) → R) (d : Fin g →₀ ℕ) :
    coeff d (extend v) = if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0 :=
  rfl

theorem coeff_extend_toFinsupp (v : ((i : Fin g) → Fin (N i)) → R) (u : (i : Fin g) → Fin (N i)) :
    coeff (toFinsupp u) (extend v) = v u := by
  rw [coeff_extend, dif_pos (inBox_toFinsupp u)]
  rfl

theorem coeff_extend_of_not (v : ((i : Fin g) → Fin (N i)) → R) {d : Fin g →₀ ℕ}
    (hd : ¬ InBox N d) : coeff d (extend v) = 0 := by
  rw [coeff_extend, dif_neg hd]

theorem toFinsupp_mk {d : Fin g →₀ ℕ} (h : InBox N d) :
    toFinsupp (fun i => (⟨d i, h i⟩ : Fin (N i))) = d := by
  ext i
  rfl

def extendLin (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) →ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  (Ideal.Quotient.mkₐ R (powIdeal R g N)).toLinearMap ∘ₗ
    { toFun := extend
      map_add' := fun v w => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_add, coeff_extend, coeff_extend, coeff_extend]
        split_ifs <;> simp
      map_smul' := fun c v => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_smul, coeff_extend, coeff_extend, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }

theorem extendLin_apply (v : ((i : Fin g) → Fin (N i)) → R) :
    extendLin R g N v = Ideal.Quotient.mk (powIdeal R g N) (extend v) := rfl

theorem extendLin_injective : Function.Injective (extendLin R g N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [extendLin_apply, Ideal.Quotient.eq_zero_iff_mem, powIdeal_eq_boxKer] at hv
  funext u
  rw [← coeff_extend_toFinsupp v u]
  exact hv _ (inBox_toFinsupp u)

theorem extendLin_surjective : Function.Surjective (extendLin R g N) := by
  intro x
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨fun u => coeff (toFinsupp u) θ, ?_⟩
  rw [extendLin_apply, Ideal.Quotient.eq, powIdeal_eq_boxKer]
  intro d hd
  rw [map_sub, coeff_extend, dif_pos hd, toFinsupp_mk hd, sub_self]

def boxEquiv (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) ≃ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  LinearEquiv.ofBijective (extendLin R g N) ⟨extendLin_injective, extendLin_surjective⟩

end CerednikDrinfeld.BoxBasisLemma

end

open CerednikDrinfeld.BoxBasisLemma in
theorem CerednikDrinfeld.BoxBasisLemma.free_and_finite_and_finrank_quotient_span_range_X_pow (R : Type u) [CommRing R] [Nontrivial R] (g : ℕ) (N : Fin g → ℕ) :
    Module.Free R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.Finite R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.finrank R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i))
          = ∏ i, N i := by
  refine ⟨Module.Free.of_equiv (boxEquiv R g N), Module.Finite.equiv (boxEquiv R g N), ?_⟩
  rw [← (boxEquiv R g N).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_pi]
  simp only [Fintype.card_fin]

end BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.LubinTate

namespace CerednikDrinfeld.Standard

universe u v

variable {p : ℕ} [Fact p.Prime]

local notation "𝕆" => Zp2 p
local notation "𝔮" => Fintype.card (GaloisField p 2)

section Standard

def lawLin (i : Fin 2) : Fin 2 ⊕ Fin 2 → 𝕆 :=
  Sum.elim (fun j => if j = i then 1 else 0) (fun j => if j = i then 1 else 0)

theorem sum_lawLin_mul (i : Fin 2) (g : Fin 2 ⊕ Fin 2 → 𝕆) :
    ∑ v, lawLin (p := p) i v * g v = g (Sum.inl i) + g (Sum.inr i) := by
  rw [Fintype.sum_sum_type]
  simp only [lawLin, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lawLin_eq (i : Fin 2) (v : Fin 2 ⊕ Fin 2) :
    lawLin (p := p) i v = (if v = Sum.inl i then 1 else 0) + (if v = Sum.inr i then 1 else 0) := by
  rcases v with j | j <;> by_cases h : j = i <;> simp [lawLin, h]

variable (p)

def lawSeries (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆 := lt p (Fin 2 ⊕ Fin 2) (lawLin i)

variable {p}

theorem constantCoeff_lawSeries (i : Fin 2) : constantCoeff (lawSeries p i) = 0 := constantCoeff_lt _

theorem comm_lawSeries (i : Fin 2) : Comm p (lawSeries p i) := comm_lt _

theorem coeff_single_lawSeries (i : Fin 2) (v : Fin 2 ⊕ Fin 2) :
    coeff (Finsupp.single v 1) (lawSeries p i)
      = (if v = Sum.inl i then 1 else 0) + (if v = Sum.inr i then 1 else 0) := by
  rw [lawSeries, coeff_single_lt, lawLin_eq]

theorem coeff_single_subst_lawSeries {τ : Type*} [Fintype τ] (i : Fin 2)
    {a : Fin 2 ⊕ Fin 2 → MvPowerSeries τ 𝕆} (ha0 : ∀ v, constantCoeff (a v) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (lawSeries p i))
      = coeff (Finsupp.single t 1) (a (Sum.inl i)) + coeff (Finsupp.single t 1) (a (Sum.inr i)) := by
  rw [lawSeries, coeff_single_subst_lt _ ha0, sum_lawLin_mul]

def law : MvFormalGroup 2 𝕆 where
  toPowerSeries := lawSeries p
  constantCoeff_eq_zero := constantCoeff_lawSeries
  coeff_single_inl i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  coeff_single_inr i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  assoc i := by
    classical

    have hB : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hC : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hBv : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) = fun s => X (Sum.elim (fun l => Sum.inl l)
          (fun l => Sum.inr (Sum.inl l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hCv : (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) = fun s => X (Sum.elim (fun l => Sum.inr (Sum.inl l))
          (fun l => Sum.inr (Sum.inr l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hA : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
          fun l => X (Sum.inr (Sum.inl l))) (lawSeries p j))
        fun j => X (Sum.inr (Sum.inr j))) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_subst_of (constantCoeff_lawSeries j) hB
      · exact constantCoeff_X _
    have hA' : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
          fun l => X (Sum.inr (Sum.inr l))) (lawSeries p j)) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_of (constantCoeff_lawSeries j) hC
    refine eq_of_comm (constantCoeff_subst_of (constantCoeff_lawSeries i) hA)
      (constantCoeff_subst_of (constantCoeff_lawSeries i) hA') ?_ ?_ ?_
    · refine comm_subst (comm_lawSeries i) hA ?_
      rintro (j | j)
      · show Comm p (subst _ (lawSeries p j))
        rw [hBv]
        exact comm_subst_X (comm_lawSeries j) _
      · exact comm_X _
    · refine comm_subst (comm_lawSeries i) hA' ?_
      rintro (j | j)
      · exact comm_X _
      · show Comm p (subst _ (lawSeries p j))
        rw [hCv]
        exact comm_subst_X (comm_lawSeries j) _
    · intro t
      rw [coeff_single_subst_lawSeries i hA, coeff_single_subst_lawSeries i hA']
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [coeff_single_subst_lawSeries i hB, coeff_single_subst_lawSeries i hC]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact add_assoc _ _ _

instance law_isComm : (law (p := p)).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (lawSeries p i) = lawSeries p i
    refine eq_of_comm (constantCoeff_subst_of (constantCoeff_lawSeries i) hS)
      (constantCoeff_lawSeries i) ?_ (comm_lawSeries i) ?_
    · rw [hSv]
      exact comm_subst_X (comm_lawSeries i) _
    · intro t
      rw [coeff_single_subst_lawSeries i hS, coeff_single_lawSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      exact add_comm _ _

def chi (i : Fin 2) : 𝕆 →+* 𝕆 := if i = 0 then RingHom.id _ else WittVector.frobenius

@[simp] theorem chi_zero : chi (p := p) 0 = RingHom.id _ := rfl

@[simp] theorem chi_one : chi (p := p) 1 = WittVector.frobenius := rfl

theorem chi_frobenius (i : Fin 2) (a : 𝕆) :
    chi i (WittVector.frobenius a) = WittVector.frobenius (chi i a) := by
  fin_cases i <;> simp

theorem chi_natCast (i : Fin 2) : chi i (p : 𝕆) = p := map_natCast _ _

variable (p)

def actSeries (a : 𝕆) : Series 𝕆 := fun i => lt p (Fin 2) fun s => if s = i then chi i a else 0

def varpiLin (i s : Fin 2) : 𝕆 := if i = 0 then (if s = 1 then p else 0) else (if s = 0 then 1 else 0)

def varpiSeries : Series 𝕆 := fun i => lt p (Fin 2) (varpiLin p i)

variable {p}

theorem constantCoeff_actSeries (a : 𝕆) (i : Fin 2) : constantCoeff (actSeries p a i) = 0 :=
  constantCoeff_lt _

theorem comm_actSeries (a : 𝕆) (i : Fin 2) : Comm p (actSeries p a i) := comm_lt _

theorem coeff_single_actSeries (a : 𝕆) (i s : Fin 2) :
    coeff (Finsupp.single s 1) (actSeries p a i) = if s = i then chi i a else 0 := by
  rw [actSeries, coeff_single_lt]

theorem coeff_single_subst_actSeries {τ : Type*} [Fintype τ] (a : 𝕆) (i : Fin 2)
    {b : Fin 2 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (actSeries p a i))
      = chi i a * coeff (Finsupp.single t 1) (b i) := by
  rw [actSeries, coeff_single_subst_lt _ hb0]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem constantCoeff_varpiSeries (i : Fin 2) : constantCoeff (varpiSeries p i) = 0 :=
  constantCoeff_lt _

theorem comm_varpiSeries (i : Fin 2) : Comm p (varpiSeries p i) := comm_lt _

theorem coeff_single_varpiSeries (i s : Fin 2) :
    coeff (Finsupp.single s 1) (varpiSeries p i) = varpiLin p i s := by
  rw [varpiSeries, coeff_single_lt]

theorem sum_varpiLin_mul (i : Fin 2) (g : Fin 2 → 𝕆) :
    ∑ s, varpiLin p i s * g s = if i = 0 then (p : 𝕆) * g 1 else g 0 := by
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp [varpiLin]

theorem coeff_single_subst_varpiSeries {τ : Type*} [Fintype τ] (i : Fin 2)
    {b : Fin 2 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (varpiSeries p i))
      = if i = 0 then (p : 𝕆) * coeff (Finsupp.single t 1) (b 1)
        else coeff (Finsupp.single t 1) (b 0) := by
  rw [varpiSeries, coeff_single_subst_lt _ hb0, sum_varpiLin_mul]

theorem constantCoeff_homFamily {φ : Series 𝕆} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆)) (φ j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆)) (φ j)) s) = 0 := by
  rintro (j | j) <;> exact constantCoeff_subst_of (hφ j) (fun l => constantCoeff_X _)

theorem isLawHom_of_comm {φ : Series 𝕆} (h0 : ∀ i, constantCoeff (φ i) = 0)
    (hc : ∀ i, Comm p (φ i)) : IsLawHom (law (p := p)) law φ := by
  classical
  refine ⟨h0, fun i => ?_⟩
  have hF : ∀ j, constantCoeff (lawSeries p j) = 0 := constantCoeff_lawSeries
  have hA := constantCoeff_homFamily h0
  refine eq_of_comm (constantCoeff_subst_of (h0 i) hF)
    (constantCoeff_subst_of (constantCoeff_lawSeries i) hA)
    (comm_subst (hc i) hF comm_lawSeries) (comm_subst (comm_lawSeries i) hA ?_) ?_
  · rintro (j | j) <;> exact comm_subst_X (hc j) _
  · intro t
    show coeff _ (subst (lawSeries p) (φ i)) = coeff _ (subst _ (lawSeries p i))
    rw [coeff_single_subst_lawSeries i hA, MvFormalGroup.coeff_single_subst hF]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_lawSeries]
    rw [MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _),
      MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _)]
    simp only [coeff_index_single_X, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]

def standard : FormalODModule p 𝕆 where
  F := law
  isComm := law_isComm
  act := actSeries p
  varpi := varpiSeries p
  isLawHom_act a := isLawHom_of_comm (constantCoeff_actSeries a) (comm_actSeries a)
  isLawHom_varpi := isLawHom_of_comm constantCoeff_varpiSeries comm_varpiSeries
  act_one := by
    classical
    funext i
    refine eq_of_comm (constantCoeff_actSeries 1 i) (constantCoeff_X i) (comm_actSeries 1 i)
      (comm_X i) fun s => ?_
    rw [coeff_single_actSeries, map_one]
    exact (coeff_index_single_X i s).symm
  act_mul a b := by
    classical
    funext i
    refine eq_of_comm (constantCoeff_actSeries _ i)
      (constantCoeff_subst_of (constantCoeff_actSeries a i) (constantCoeff_actSeries b))
      (comm_actSeries _ i) (comm_subst (comm_actSeries a i) (constantCoeff_actSeries b)
        (comm_actSeries b)) fun s => ?_
    show _ = coeff _ (subst (actSeries p b) (actSeries p a i))
    rw [coeff_single_actSeries, coeff_single_subst_actSeries a i (constantCoeff_actSeries b),
      coeff_single_actSeries, map_mul]
    split_ifs <;> ring
  act_add a b := by
    classical
    funext i
    have hab : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim (actSeries p a) (actSeries p b)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_actSeries _ j
    refine eq_of_comm (constantCoeff_actSeries _ i)
      (constantCoeff_subst_of (constantCoeff_lawSeries i) hab)
      (comm_actSeries _ i) (comm_subst (comm_lawSeries i) hab ?_) fun s => ?_
    · rintro (j | j) <;> exact comm_actSeries _ j
    · show _ = coeff _ (subst _ (lawSeries p i))
      rw [coeff_single_actSeries, coeff_single_subst_lawSeries i hab]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_actSeries, map_add]
      split_ifs <;> ring
  varpi_comp_varpi := by
    classical
    funext i
    refine eq_of_comm
      (constantCoeff_subst_of (constantCoeff_varpiSeries i) constantCoeff_varpiSeries)
      (constantCoeff_actSeries _ i)
      (comm_subst (comm_varpiSeries i) constantCoeff_varpiSeries comm_varpiSeries)
      (comm_actSeries _ i) fun s => ?_
    show coeff _ (subst (varpiSeries p) (varpiSeries p i)) = _
    rw [coeff_single_subst_varpiSeries i constantCoeff_varpiSeries, coeff_single_varpiSeries,
      coeff_single_varpiSeries, coeff_single_actSeries, chi_natCast]
    fin_cases i <;> fin_cases s <;> simp [varpiLin]
  varpi_comp_act a := by
    classical
    funext i
    refine eq_of_comm
      (constantCoeff_subst_of (constantCoeff_varpiSeries i) (constantCoeff_actSeries a))
      (constantCoeff_subst_of (constantCoeff_actSeries _ i) constantCoeff_varpiSeries)
      (comm_subst (comm_varpiSeries i) (constantCoeff_actSeries a) (comm_actSeries a))
      (comm_subst (comm_actSeries _ i) constantCoeff_varpiSeries comm_varpiSeries) fun s => ?_
    show coeff _ (subst (actSeries p a) (varpiSeries p i))
      = coeff _ (subst (varpiSeries p) (actSeries p _ i))
    rw [coeff_single_subst_varpiSeries i (constantCoeff_actSeries a), coeff_single_actSeries,
      coeff_single_actSeries, coeff_single_subst_actSeries _ i constantCoeff_varpiSeries,
      coeff_single_varpiSeries]
    fin_cases i <;> fin_cases s <;> simp [varpiLin, frobenius_frobenius, mul_comm]

theorem standard_act_p : (standard (p := p)).act (p : 𝕆) = fvec p (Fin 2) := by
  classical
  funext i
  refine eq_of_comm (constantCoeff_actSeries _ i) (constantCoeff_fvec i) (comm_actSeries _ i)
    (comm_fvec i) fun s => ?_
  show coeff _ (actSeries p _ i) = _
  rw [coeff_single_actSeries, coeff_single_fvec, chi_natCast]

theorem coeff_single_standard_act (a : 𝕆) (i s : Fin 2) :
    coeff (Finsupp.single s 1) ((standard (p := p)).act a i) = if s = i then chi i a else 0 :=
  coeff_single_actSeries a i s

end Standard

section Identities

def emb (i : Fin 2) : Fin 1 ⊕ Fin 1 → Fin 2 ⊕ Fin 2 := Sum.map (fun _ => i) fun _ => i

@[simp] theorem emb_inl (i : Fin 2) (l : Fin 1) : emb i (Sum.inl l) = Sum.inl i := rfl
@[simp] theorem emb_inr (i : Fin 2) (l : Fin 1) : emb i (Sum.inr l) = Sum.inr i := rfl

theorem lawSeries_eq (i : Fin 2) :
    lawSeries p i = subst (fun s => (X (emb i s) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
      (sigmaSeries p) := by
  classical
  have h0 : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((X (emb i s) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆)) = 0 :=
    fun s => constantCoeff_X _
  refine eq_of_comm (constantCoeff_lawSeries i) (constantCoeff_subst_of constantCoeff_sigmaSeries h0)
    (comm_lawSeries i) (comm_subst_X comm_sigmaSeries _) fun v => ?_
  rw [coeff_single_lawSeries, coeff_single_subst_sigmaSeries h0]
  simp only [emb_inl, emb_inr, coeff_index_single_X]

theorem actSeries_eq (a : 𝕆) (i : Fin 2) :
    actSeries p a i = subst (fun _ : Fin 1 => (X i : MvPowerSeries (Fin 2) 𝕆)) (act₁ p (chi i a)) := by
  classical
  refine eq_of_comm (constantCoeff_actSeries a i)
    (constantCoeff_subst_of (constantCoeff_act₁ _) fun _ => constantCoeff_X _)
    (comm_actSeries a i) (comm_subst_X (comm_act₁ _) _) fun s => ?_
  rw [coeff_single_actSeries, coeff_single_subst_act₁ _ (fun _ => constantCoeff_X _),
    coeff_index_single_X, mul_ite, mul_one, mul_zero]

theorem varpiSeries_zero :
    varpiSeries p 0 = subst (fun _ : Fin 1 => (X 1 : MvPowerSeries (Fin 2) 𝕆)) (act₁ p (p : 𝕆)) := by
  classical
  refine eq_of_comm (constantCoeff_varpiSeries 0)
    (constantCoeff_subst_of (constantCoeff_act₁ _) fun _ => constantCoeff_X _)
    (comm_varpiSeries 0) (comm_subst_X (comm_act₁ _) _) fun s => ?_
  rw [coeff_single_varpiSeries, coeff_single_subst_act₁ _ (fun _ => constantCoeff_X _),
    coeff_index_single_X, mul_ite, mul_one, mul_zero]
  simp [varpiLin]

theorem varpiSeries_one : varpiSeries p 1 = X 0 := by
  classical
  refine eq_of_comm (constantCoeff_varpiSeries 1) (constantCoeff_X 0) (comm_varpiSeries 1) (comm_X 0)
    fun s => ?_
  rw [coeff_single_varpiSeries, coeff_index_single_X]
  simp [varpiLin]

end Identities

section OverB

variable {B : Type*} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

def modB : FormalODModule p B := (standard (p := p)).map j

theorem lieAct_apply (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (modB j).lieAct a m i = j (chi i a) * m i := by
  classical
  show (Matrix.mulVecLin (MvFormalGroup.linearPart ((modB j).act a))) m i = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [MvFormalGroup.linearPart, Matrix.of_apply]
  show ∑ s, coeff (Finsupp.single s 1) (MvPowerSeries.map j ((standard (p := p)).act a i)) * m s = _
  simp only [MvPowerSeries.coeff_map, coeff_single_standard_act, apply_ite j, map_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sub_smul_apply (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (((modB j).lieAct a - j a • (LinearMap.id : (modB j).Lie →ₗ[B] (modB j).Lie)) m) i
      = (j (chi i a) - j a) * m i := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply,
    Pi.smul_apply, lieAct_apply, smul_eq_mul, sub_mul]

theorem sub_smul_apply' (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (((modB j).lieAct a - j (WittVector.frobenius a) •
        (LinearMap.id : (modB j).Lie →ₗ[B] (modB j).Lie)) m) i
      = (j (chi i a) - j (WittVector.frobenius a)) * m i := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply,
    Pi.smul_apply, lieAct_apply, smul_eq_mul, sub_mul]

theorem mem_lieZero_iff (m : (modB j).Lie) : m ∈ (modB j).lieZero j ↔ m 1 = 0 := by
  rw [FormalODModule.lieZero, Submodule.mem_iInf]
  constructor
  · intro h
    obtain ⟨a₀, ha₀⟩ := exists_isUnit_frobenius_sub (p := p)
    have h1 := congrFun (LinearMap.mem_ker.mp (h a₀)) 1
    rw [sub_smul_apply, Pi.zero_apply, chi_one, ← map_sub] at h1
    exact (ha₀.map j).mul_right_eq_zero.mp h1
  · intro hm a
    rw [LinearMap.mem_ker]
    funext i
    rw [sub_smul_apply, Pi.zero_apply]
    fin_cases i
    · simp
    · simp [hm]

theorem mem_lieOne_iff (m : (modB j).Lie) : m ∈ (modB j).lieOne j ↔ m 0 = 0 := by
  rw [FormalODModule.lieOne, Submodule.mem_iInf]
  constructor
  · intro h
    obtain ⟨a₀, ha₀⟩ := exists_isUnit_frobenius_sub (p := p)
    have h1 := congrFun (LinearMap.mem_ker.mp (h a₀)) 0
    rw [sub_smul_apply', Pi.zero_apply, chi_zero, RingHom.id_apply, ← map_sub] at h1
    have hu : IsUnit (a₀ - WittVector.frobenius a₀) := by
      rw [← neg_sub]
      exact ha₀.neg
    exact (hu.map j).mul_right_eq_zero.mp h1
  · intro hm a
    rw [LinearMap.mem_ker]
    funext i
    rw [sub_smul_apply', Pi.zero_apply]
    fin_cases i
    · simp [hm]
    · simp

theorem isCompl_lie : IsCompl ((modB j).lieZero j) ((modB j).lieOne j) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    intro m hm
    rw [Submodule.mem_inf, mem_lieZero_iff, mem_lieOne_iff] at hm
    funext i
    fin_cases i
    · exact hm.2
    · exact hm.1
  · rw [Submodule.eq_top_iff']
    intro m
    rw [Submodule.mem_sup]
    refine ⟨Pi.single 0 (m 0), (mem_lieZero_iff j _).mpr (by simp), Pi.single 1 (m 1),
      (mem_lieOne_iff j _).mpr (by simp), ?_⟩
    funext i
    fin_cases i <;> simp

def lieZeroEquiv : ↥((modB j).lieZero j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 0 b, (mem_lieZero_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · simpa using ((mem_lieZero_iff j _).mp m.2).symm
  right_inv b := by simp

def lieOneEquiv : ↥((modB j).lieOne j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 1 b, (mem_lieOne_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simpa using ((mem_lieOne_iff j _).mp m.2).symm
    · simp
  right_inv b := by simp

theorem isSpecial : (modB j).IsSpecial j :=
  ⟨isCompl_lie j, Module.Invertible.congr (lieZeroEquiv j).symm,
    Module.Invertible.congr (lieOneEquiv j).symm⟩

theorem modB_act_p : (modB j).act (p : 𝕆) = fun i => (X i : MvPowerSeries (Fin 2) B) ^ 𝔮 := by
  show ((standard (p := p)).act (p : 𝕆)).map j = _
  rw [standard_act_p]
  funext i
  show MvPowerSeries.map j (C (p : 𝕆) * X i + X i ^ 𝔮) = X i ^ 𝔮
  rw [map_add, map_mul, map_C, map_natCast, CharP.cast_eq_zero, map_zero, zero_mul, zero_add,
    map_pow, map_X]

theorem hasKernelOfDegree_X_pow :
    FormalODModule.HasKernelOfDegree (fun i => (X i : MvPowerSeries (Fin 2) B) ^ 𝔮) (p ^ 4) := by
  haveI : Nontrivial B := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  obtain ⟨hfree, hfin, -⟩ :=
    CerednikDrinfeld.BoxBasisLemma.free_and_finite_and_finrank_quotient_span_range_X_pow B 2 (fun _ => 𝔮)
  refine ⟨hfin, Module.Projective.of_free, fun κ _ f => ?_⟩
  have hφ : (fun i : Fin 2 => MvPowerSeries.map f ((X i : MvPowerSeries (Fin 2) B) ^ 𝔮))
      = fun i => (X i : MvPowerSeries (Fin 2) κ) ^ 𝔮 := by
    funext i
    rw [map_pow, map_X]
  show Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range
    fun i : Fin 2 => MvPowerSeries.map f ((X i : MvPowerSeries (Fin 2) B) ^ 𝔮))) = p ^ 4
  rw [hφ, (CerednikDrinfeld.BoxBasisLemma.free_and_finite_and_finrank_quotient_span_range_X_pow κ 2 fun _ => 𝔮).2.2,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_GF, ← pow_mul]

theorem hasHeight : (modB j).HasHeight 4 := by
  show FormalODModule.HasKernelOfDegree ((modB j).act (p : 𝕆)) (p ^ 4)
  rw [modB_act_p]
  exact hasKernelOfDegree_X_pow

end OverB

def _root_.CerednikDrinfeld.SpecialFormalODModule.standard {B : Type u} [CommRing B] [CharP B p]
    (j : Zp2 p →+* B) : SpecialFormalODModule p j where
  toFormalODModule := modB j
  isSpecial := isSpecial j
  hasHeight := hasHeight j

theorem _root_.CerednikDrinfeld.SpecialFormalODModule.standard_toFormalODModule {B : Type u}
    [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (SpecialFormalODModule.standard j).toFormalODModule = modB j := rfl

section HomAlgebra

variable {R : Type*} [CommRing R] {g h k m : ℕ}

theorem _root_.MvFormalGroup.Hom.comp_assoc {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    {H : MvFormalGroup k R} {K : MvFormalGroup m R} (χ : MvFormalGroup.Hom H K)
    (ψ : MvFormalGroup.Hom G H) (φ : MvFormalGroup.Hom F G) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  apply MvFormalGroup.Hom.ext
  funext i
  exact subst_comp_subst_apply ψ.hasSubst_toPowerSeries φ.hasSubst_toPowerSeries _

theorem _root_.MvFormalGroup.Hom.comp_id' {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    (φ : MvFormalGroup.Hom F G) : φ.comp (MvFormalGroup.Hom.id F) = φ := by
  apply MvFormalGroup.Hom.ext
  funext i
  exact congrFun MvPowerSeries.subst_self _

theorem _root_.MvFormalGroup.Hom.comp_one' {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    (φ : MvFormalGroup.Hom F G) : φ.comp (1 : MvFormalGroup.End F) = φ :=
  MvFormalGroup.Hom.comp_id' φ

theorem _root_.MvFormalGroup.Hom.id_comp' {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    (φ : MvFormalGroup.Hom F G) : (MvFormalGroup.Hom.id G).comp φ = φ := by
  apply MvFormalGroup.Hom.ext
  funext i
  exact subst_X φ.hasSubst_toPowerSeries i

end HomAlgebra

section Biproduct

variable {B : Type u} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

theorem modB_F_toPowerSeries (l : Fin 2) :
    (modB j).F.toPowerSeries l =
      subst (fun s => (X (emb l s) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))
        (MvPowerSeries.map j (sigmaSeries p)) := by
  show MvPowerSeries.map j (lawSeries p l) = _
  rw [lawSeries_eq, map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  congr 1
  funext s
  exact MvPowerSeries.map_X j _

theorem modB_act (a : 𝕆) (i : Fin 2) :
    (modB j).act a i =
      subst (fun _ : Fin 1 => (X i : MvPowerSeries (Fin 2) B)) (MvPowerSeries.map j (act₁ p (chi i a))) := by
  show MvPowerSeries.map j (actSeries p a i) = _
  rw [actSeries_eq, map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  congr 1
  funext s
  exact MvPowerSeries.map_X j _

theorem modB_varpi_zero :
    (modB j).varpi 0 =
      subst (fun _ : Fin 1 => (X 1 : MvPowerSeries (Fin 2) B)) (MvPowerSeries.map j (act₁ p (p : 𝕆))) := by
  show MvPowerSeries.map j (varpiSeries p 0) = _
  rw [varpiSeries_zero, map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  congr 1
  funext s
  exact MvPowerSeries.map_X j _

theorem modB_varpi_one : (modB j).varpi 1 = X 0 := by
  show MvPowerSeries.map j (varpiSeries p 1) = _
  rw [varpiSeries_one, MvPowerSeries.map_X]

theorem subst_elim_modB_F {τ : Type*} {a b : Fin 2 → MvPowerSeries τ B}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (l : Fin 2) :
    subst (Sum.elim a b) ((modB j).F.toPowerSeries l) =
      subst (Sum.elim (fun _ : Fin 1 => a l) fun _ : Fin 1 => b l) (MvPowerSeries.map j (sigmaSeries p)) := by
  have hab : HasSubst (Sum.elim a b) := MvFormalGroup.hasSubst_elim ha hb
  rw [modB_F_toPowerSeries, subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hab]
  congr 1
  funext s
  rcases s with m | m
  · rw [subst_X hab]; rfl
  · rw [subst_X hab]; rfl

theorem constantCoeff_sigmaBarSeries :
    constantCoeff (MvPowerSeries.map j (sigmaSeries p)) = 0 := by
  rw [constantCoeff_map, constantCoeff_sigmaSeries, map_zero]

theorem subst_elim_sigmaBar_zero_right {τ : Type*} {x : MvPowerSeries τ B} (hx : constantCoeff x = 0) :
    subst (Sum.elim (fun _ : Fin 1 => x) fun _ : Fin 1 => (0 : MvPowerSeries τ B))
      (MvPowerSeries.map j (sigmaSeries p)) = x :=
  MvFormalGroup.subst_elim_zero_right (sigmaBar j) (a := fun _ : Fin 1 => x) (fun _ => hx) 0

theorem subst_elim_sigmaBar_zero_left {τ : Type*} {x : MvPowerSeries τ B} (hx : constantCoeff x = 0) :
    subst (Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries τ B)) fun _ : Fin 1 => x)
      (MvPowerSeries.map j (sigmaSeries p)) = x :=
  MvFormalGroup.subst_elim_zero_left (sigmaBar j) (a := fun _ : Fin 1 => x) (fun _ => hx) 0

def single₂ {τ : Type*} (i : Fin 2) (x : MvPowerSeries τ B) : Fin 2 → MvPowerSeries τ B :=
  fun l => if l = i then x else 0

theorem single₂_apply {τ : Type*} (i : Fin 2) (x : MvPowerSeries τ B) (l : Fin 2) :
    single₂ i x l = if l = i then x else 0 := rfl

theorem constantCoeff_single₂ {τ : Type*} (i : Fin 2) {x : MvPowerSeries τ B} (hx : constantCoeff x = 0)
    (l : Fin 2) : constantCoeff (single₂ i x l) = 0 := by
  rw [single₂_apply]; split_ifs; exacts [hx, map_zero _]

theorem subst_single₂ {τ τ' : Type*} (i : Fin 2) {x : MvPowerSeries τ B} {c : τ → MvPowerSeries τ' B}
    (hc : HasSubst c) : (fun l => subst c (single₂ i x l)) = single₂ i (subst c x) := by
  funext l
  rw [single₂_apply, single₂_apply]
  split_ifs
  · rfl
  · rw [← coe_substAlgHom hc, map_zero]

def incl (i : Fin 2) : MvFormalGroup.Hom (sigmaBar j) (modB j).F where
  toPowerSeries := single₂ i (X 0 : MvPowerSeries (Fin 1) B)
  constantCoeff_eq_zero := constantCoeff_single₂ i (constantCoeff_X 0)
  subst_eq l := by
    have hXl : HasSubst (fun l' : Fin 1 => (X (Sum.inl l') : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hXr : HasSubst (fun l' : Fin 1 => (X (Sum.inr l') : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [subst_single₂ i hXl, subst_single₂ i hXr, subst_X hXl, subst_X hXr,
      subst_elim_modB_F j (constantCoeff_single₂ i (constantCoeff_X _))
        (constantCoeff_single₂ i (constantCoeff_X _)), single₂_apply, single₂_apply, single₂_apply]
    split_ifs with h
    · rw [subst_X (sigmaBar j).hasSubst_toPowerSeries, sigmaBar_toPowerSeries]
      have hid : (Sum.elim (fun _ : Fin 1 => (X (Sum.inl 0) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          fun _ : Fin 1 => (X (Sum.inr 0) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          = fun s => X s := by
        funext s; rcases s with m | m <;> rw [Fin.fin_one_eq_zero m] <;> rfl
      rw [hid]
      exact (congrFun MvPowerSeries.subst_self _).symm
    · rw [← coe_substAlgHom (sigmaBar j).hasSubst_toPowerSeries, map_zero]
      have h00 : (Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          fun _ : Fin 1 => (0 : MvPowerSeries (Fin 1 ⊕ Fin 1) B)) = fun _ => 0 := by
        funext s; rcases s with m | m <;> rfl
      rw [h00]
      exact (MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (constantCoeff_sigmaBarSeries j)).symm

theorem incl_toPowerSeries (i : Fin 2) :
    (incl j i).toPowerSeries = single₂ i (X 0 : MvPowerSeries (Fin 1) B) := rfl

def proj (i : Fin 2) : MvFormalGroup.Hom (modB j).F (sigmaBar j) where
  toPowerSeries := fun _ => (X i : MvPowerSeries (Fin 2) B)
  constantCoeff_eq_zero := fun _ => constantCoeff_X i
  subst_eq l := by
    have hXl : HasSubst (fun l' : Fin 2 => (X (Sum.inl l') : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hXr : HasSubst (fun l' : Fin 2 => (X (Sum.inr l') : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [subst_X (modB j).F.hasSubst_toPowerSeries, Fin.fin_one_eq_zero l, sigmaBar_toPowerSeries,
      modB_F_toPowerSeries]
    congr 1
    funext s
    rcases s with m | m
    · rw [Sum.elim_inl, subst_X hXl]; rfl
    · rw [Sum.elim_inr, subst_X hXr]; rfl

theorem proj_toPowerSeries (i : Fin 2) (l : Fin 1) :
    (proj j i).toPowerSeries l = (X i : MvPowerSeries (Fin 2) B) := rfl

theorem proj_comp_incl (i i' : Fin 2) :
    (proj j i).comp (incl j i') =
      if i = i' then (1 : MvFormalGroup.End (sigmaBar j)) else (0 : MvFormalGroup.End (sigmaBar j)) := by
  apply MvFormalGroup.Hom.ext
  funext l
  show subst (incl j i').toPowerSeries (X i) = _
  rw [subst_X (incl j i').hasSubst_toPowerSeries, incl_toPowerSeries, single₂_apply]
  split_ifs
  · rw [Fin.fin_one_eq_zero l]; rfl
  · rfl

def cell (i i' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) : MvFormalGroup.End (modB j).F :=
  ((incl j i).comp e).comp (proj j i')

def entry (i i' : Fin 2) (E : MvFormalGroup.End (modB j).F) : MvFormalGroup.End (sigmaBar j) :=
  ((proj j i).comp E).comp (incl j i')

theorem cell_def (i i' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) :
    cell j i i' e = ((incl j i).comp e).comp (proj j i') := rfl

theorem entry_def (i i' : Fin 2) (E : MvFormalGroup.End (modB j).F) :
    entry j i i' E = ((proj j i).comp E).comp (incl j i') := rfl

theorem toPowerSeries_cell (i i' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) :
    (cell j i i' e).toPowerSeries =
      single₂ i (subst (fun _ : Fin 1 => (X i' : MvPowerSeries (Fin 2) B)) (e.toPowerSeries 0)) := by
  funext l
  show subst (proj j i').toPowerSeries (subst e.toPowerSeries ((incl j i).toPowerSeries l)) = _
  rw [incl_toPowerSeries, single₂_apply, single₂_apply]
  split_ifs
  · rw [subst_X e.hasSubst_toPowerSeries]
    rfl
  · rw [← coe_substAlgHom e.hasSubst_toPowerSeries, map_zero,
      ← coe_substAlgHom (proj j i').hasSubst_toPowerSeries, map_zero]

theorem mul_eq_comp {g : ℕ} {F : MvFormalGroup g B} (φ ψ : MvFormalGroup.End F) : φ * ψ = φ.comp ψ := rfl

theorem hasSubst_fin1' {τ : Type*} {x : MvPowerSeries τ B} (hx : constantCoeff x = 0) :
    HasSubst (fun _ : Fin 1 => x) :=
  hasSubst_of_constantCoeff_zero fun _ => hx

theorem hasSubst_single₂ {τ : Type*} (i : Fin 2) {x : MvPowerSeries τ B} (hx : constantCoeff x = 0) :
    HasSubst (single₂ i x) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_single₂ i hx)

theorem constantCoeff_subst_X_toPowerSeries (i : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) :
    constantCoeff (subst (fun _ : Fin 1 => (X i : MvPowerSeries (Fin 2) B)) (e.toPowerSeries 0)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (e.constantCoeff_eq_zero 0)

theorem toPowerSeries_fin1 (e : MvFormalGroup.End (sigmaBar j)) :
    e.toPowerSeries = fun _ => e.toPowerSeries 0 := by
  funext l; rw [Fin.fin_one_eq_zero l]

theorem subst_fin1_X (f : MvPowerSeries (Fin 1) B) :
    subst (fun _ : Fin 1 => (X 0 : MvPowerSeries (Fin 1) B)) f = f := by
  have h := congrFun (MvPowerSeries.subst_self (σ := Fin 1) (R := B)) f
  have hX : (X : Fin 1 → MvPowerSeries (Fin 1) B) = fun _ => X 0 := by
    funext l; rw [Fin.fin_one_eq_zero l]
  rw [hX] at h
  exact h

theorem subst_single₂_subst_X {τ : Type*} (k i' : Fin 2) {y : MvPowerSeries τ B} (hy : constantCoeff y = 0)
    (e : MvFormalGroup.End (sigmaBar j)) :
    subst (single₂ k y) (subst (fun _ : Fin 1 => (X i' : MvPowerSeries (Fin 2) B)) (e.toPowerSeries 0)) =
      if i' = k then subst (fun _ : Fin 1 => y) (e.toPowerSeries 0) else 0 := by
  rw [subst_comp_subst_apply (hasSubst_fin1' (constantCoeff_X _)) (hasSubst_single₂ k hy)]
  simp only [subst_X (hasSubst_single₂ k hy), single₂_apply]
  split_ifs
  · rfl
  · exact MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (e.constantCoeff_eq_zero 0)

theorem cell_mul_cell (i i' k k' : Fin 2) (e e' : MvFormalGroup.End (sigmaBar j)) :
    cell j i i' e * cell j k k' e' = if i' = k then cell j i k' (e * e') else 0 := by
  apply MvFormalGroup.Hom.ext
  rw [MvFormalGroup.End.toPowerSeries_mul, toPowerSeries_cell, toPowerSeries_cell,
    subst_single₂ i (hasSubst_single₂ k (constantCoeff_subst_X_toPowerSeries j k' e')),
    subst_single₂_subst_X j k i' (constantCoeff_subst_X_toPowerSeries j k' e')]
  split_ifs with h
  · rw [toPowerSeries_cell, MvFormalGroup.End.toPowerSeries_mul, toPowerSeries_fin1 j e',
      subst_comp_subst_apply (hasSubst_fin1' (e'.constantCoeff_eq_zero 0)) (hasSubst_fin1' (constantCoeff_X _))]
  · funext l
    rw [single₂_apply, MvFormalGroup.End.toPowerSeries_zero]
    split_ifs <;> rfl

theorem cell_add (i i' : Fin 2) (e e' : MvFormalGroup.End (sigmaBar j)) :
    cell j i i' (e + e') = cell j i i' e + cell j i i' e' := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [toPowerSeries_cell, MvFormalGroup.End.toPowerSeries_add, MvFormalGroup.End.toPowerSeries_add,
    toPowerSeries_cell, toPowerSeries_cell]
  dsimp only
  rw [subst_elim_modB_F j (constantCoeff_single₂ i (constantCoeff_subst_X_toPowerSeries j i' e))
      (constantCoeff_single₂ i (constantCoeff_subst_X_toPowerSeries j i' e')), single₂_apply, single₂_apply,
    single₂_apply, sigmaBar_toPowerSeries,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim e.constantCoeff_eq_zero e'.constantCoeff_eq_zero)
      (hasSubst_fin1' (constantCoeff_X _))]
  split_ifs
  · congr 1
    funext s
    rcases s with m | m <;> rw [Fin.fin_one_eq_zero m] <;> rfl
  · have h00 : (Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries (Fin 2) B))
        fun _ : Fin 1 => (0 : MvPowerSeries (Fin 2) B)) = fun _ => 0 := by
      funext s; rcases s with m | m <;> rfl
    rw [h00, MvFormalGroup.subst_zero_of_constantCoeff_eq_zero (constantCoeff_sigmaBarSeries j)]

theorem cell_zero (i i' : Fin 2) : cell j i i' 0 = 0 := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [toPowerSeries_cell, MvFormalGroup.End.toPowerSeries_zero, MvFormalGroup.End.toPowerSeries_zero,
    single₂_apply]
  dsimp only
  rw [← coe_substAlgHom (hasSubst_fin1' (constantCoeff_X _)), map_zero]
  split_ifs <;> rfl

theorem cell_neg (i i' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) : cell j i i' (-e) = -cell j i i' e := by
  rw [eq_neg_iff_add_eq_zero, ← cell_add, neg_add_cancel, cell_zero]

theorem cell_sub (i i' : Fin 2) (e e' : MvFormalGroup.End (sigmaBar j)) :
    cell j i i' (e - e') = cell j i i' e - cell j i i' e' := by
  rw [sub_eq_add_neg, cell_add, cell_neg, ← sub_eq_add_neg]

theorem entry_cell (i i' k k' : Fin 2) (e : MvFormalGroup.End (sigmaBar j)) :
    entry j i i' (cell j k k' e) = if i = k then (if k' = i' then e else 0) else 0 := by
  apply MvFormalGroup.Hom.ext
  funext l
  show subst (incl j i').toPowerSeries (subst (cell j k k' e).toPowerSeries (X i)) = _
  rw [toPowerSeries_cell, subst_X (hasSubst_single₂ k (constantCoeff_subst_X_toPowerSeries j k' e)),
    single₂_apply, incl_toPowerSeries]
  split_ifs with h1 h2
  · rw [subst_single₂_subst_X j i' k' (constantCoeff_X _), if_pos h2, Fin.fin_one_eq_zero l, subst_fin1_X]
  · rw [subst_single₂_subst_X j i' k' (constantCoeff_X _), if_neg h2]; rfl
  · rw [← coe_substAlgHom (hasSubst_single₂ i' (constantCoeff_X _)), map_zero]; rfl

theorem entry_add (i i' : Fin 2) (E E' : MvFormalGroup.End (modB j).F) :
    entry j i i' (E + E') = entry j i i' E + entry j i i' E' := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [MvFormalGroup.End.toPowerSeries_add]
  show subst (incl j i').toPowerSeries (subst (E + E').toPowerSeries (X i)) =
    subst (Sum.elim (fun _ => subst (incl j i').toPowerSeries (subst E.toPowerSeries (X i)))
      fun _ => subst (incl j i').toPowerSeries (subst E'.toPowerSeries (X i))) ((sigmaBar j).toPowerSeries l)
  rw [subst_X E.hasSubst_toPowerSeries, subst_X E'.hasSubst_toPowerSeries,
    subst_X (E + E').hasSubst_toPowerSeries, MvFormalGroup.End.toPowerSeries_add]
  dsimp only
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim E.constantCoeff_eq_zero E'.constantCoeff_eq_zero)
      (incl j i').hasSubst_toPowerSeries, Fin.fin_one_eq_zero l, sigmaBar_toPowerSeries]
  have hfam : (fun s => subst (incl j i').toPowerSeries (Sum.elim E.toPowerSeries E'.toPowerSeries s)) =
      Sum.elim (fun m => subst (incl j i').toPowerSeries (E.toPowerSeries m))
        fun m => subst (incl j i').toPowerSeries (E'.toPowerSeries m) := by
    funext s; rcases s with m | m <;> rfl
  rw [hfam, subst_elim_modB_F j]
  · intro m
    exact constantCoeff_subst_eq_zero (incl j i').hasSubst_toPowerSeries (incl j i').constantCoeff_eq_zero
      (E.constantCoeff_eq_zero m)
  · intro m
    exact constantCoeff_subst_eq_zero (incl j i').hasSubst_toPowerSeries (incl j i').constantCoeff_eq_zero
      (E'.constantCoeff_eq_zero m)

theorem one_eq_cell_add_cell : (1 : MvFormalGroup.End (modB j).F) = cell j 0 0 1 + cell j 1 1 1 := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [MvFormalGroup.End.toPowerSeries_one, MvFormalGroup.End.toPowerSeries_add, toPowerSeries_cell,
    toPowerSeries_cell, MvFormalGroup.End.toPowerSeries_one, subst_X (hasSubst_fin1' (B := B) (constantCoeff_X _)),
    subst_X (hasSubst_fin1' (B := B) (constantCoeff_X _))]
  dsimp only
  rw [subst_elim_modB_F j (constantCoeff_single₂ 0 (constantCoeff_X _)) (constantCoeff_single₂ 1 (constantCoeff_X _)),
    single₂_apply, single₂_apply]
  revert l
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [if_pos rfl, if_neg zero_ne_one]
    exact (subst_elim_sigmaBar_zero_right j (constantCoeff_X _)).symm
  · rw [if_neg one_ne_zero, if_pos rfl]
    exact (subst_elim_sigmaBar_zero_left j (constantCoeff_X _)).symm

theorem eq_sum_cell_entry (E : MvFormalGroup.End (modB j).F) :
    E = cell j 0 0 (entry j 0 0 E) + cell j 0 1 (entry j 0 1 E) +
      (cell j 1 0 (entry j 1 0 E) + cell j 1 1 (entry j 1 1 E)) := by
  have key : ∀ i i' : Fin 2, cell j i i 1 * E * cell j i' i' 1 = cell j i i' (entry j i i' E) := by
    intro i i'
    rw [mul_eq_comp, mul_eq_comp, cell_def, cell_def, cell_def, entry_def, MvFormalGroup.Hom.comp_one',
      MvFormalGroup.Hom.comp_one']
    exact (MvFormalGroup.Hom.comp_assoc _ _ _).trans
      ((MvFormalGroup.Hom.comp_assoc _ _ _).trans
        ((congrArg ((incl j i).comp ·) (MvFormalGroup.Hom.comp_assoc _ _ _).symm).trans
          ((congrArg ((incl j i).comp ·) (MvFormalGroup.Hom.comp_assoc _ _ _).symm).trans
            (MvFormalGroup.Hom.comp_assoc _ _ _).symm)))
  calc E = 1 * E * 1 := by rw [one_mul, mul_one]
    _ = (cell j 0 0 1 + cell j 1 1 1) * E * (cell j 0 0 1 + cell j 1 1 1) := by rw [← one_eq_cell_add_cell]
    _ = _ := by rw [add_mul, add_mul, mul_add, mul_add, key, key, key, key]

theorem actEnd_eq (a : 𝕆) :
    (modB j).actEnd a = cell j 0 0 (rho j a) + cell j 1 1 (rho j (WittVector.frobenius a)) := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [MvFormalGroup.End.toPowerSeries_add, FormalODModule.actEnd_toPowerSeries, toPowerSeries_cell,
    toPowerSeries_cell]
  dsimp only
  rw [subst_elim_modB_F j (constantCoeff_single₂ 0 (constantCoeff_subst_X_toPowerSeries j _ _))
      (constantCoeff_single₂ 1 (constantCoeff_subst_X_toPowerSeries j _ _)),
    single₂_apply, single₂_apply, modB_act]
  revert l
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [if_pos rfl, if_neg zero_ne_one, chi_zero, RingHom.id_apply]
    exact (subst_elim_sigmaBar_zero_right j (constantCoeff_subst_X_toPowerSeries j 0 (rho j a))).symm
  · rw [if_neg one_ne_zero, if_pos rfl, chi_one]
    exact (subst_elim_sigmaBar_zero_left j
      (constantCoeff_subst_X_toPowerSeries j 1 (rho j (WittVector.frobenius a)))).symm

theorem varpiEnd_eq : (modB j).varpiEnd = cell j 0 1 (rho j (p : 𝕆)) + cell j 1 0 1 := by
  apply MvFormalGroup.Hom.ext
  funext l
  rw [MvFormalGroup.End.toPowerSeries_add, FormalODModule.varpiEnd_toPowerSeries, toPowerSeries_cell,
    toPowerSeries_cell]
  dsimp only
  rw [subst_elim_modB_F j (constantCoeff_single₂ 0 (constantCoeff_subst_X_toPowerSeries j _ _))
      (constantCoeff_single₂ 1 (constantCoeff_subst_X_toPowerSeries j _ _)),
    single₂_apply, single₂_apply]
  revert l
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [if_pos rfl, if_neg zero_ne_one, modB_varpi_zero]
    exact (subst_elim_sigmaBar_zero_right j (constantCoeff_subst_X_toPowerSeries j 1 (rho j (p : 𝕆)))).symm
  · rw [if_neg one_ne_zero, if_pos rfl, modB_varpi_one, MvFormalGroup.End.toPowerSeries_one,
      subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    exact (subst_elim_sigmaBar_zero_left j (constantCoeff_X _)).symm

end Biproduct

end CerednikDrinfeld.Standard

end


namespace CerednikDrinfeld
namespace FormalOmega

structure AlgFunctor (𝒪 : Type) [CommRing 𝒪] : Type 1 where

  obj : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Type

  map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'],
    (B →ₐ[𝒪] B') → obj B → obj B'

  map_id : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] (x : obj B), map (AlgHom.id 𝒪 B) x = x

  map_comp : ∀ {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂]
    {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃] (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : obj B₁),
    map (g.comp f) x = map g (map f x)

variable {𝒪 : Type} [CommRing 𝒪] (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  (Fr : Onr ≃ₐ[𝒪] Onr)

noncomputable def frobTwist (n : ℤ) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (ψ : Onr →ₐ[𝒪] B) : Onr →ₐ[𝒪] B :=
  ψ.comp ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)

theorem frobTwist_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr 0 ψ = ψ := by
  ext x
  simp [frobTwist]

theorem frobTwist_add {B : Type} [CommRing B] [Algebra 𝒪 B] (m n : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr (m + n) ψ = frobTwist Onr Fr m (frobTwist Onr Fr n ψ) := by
  have hcomm : ∀ x : Onr, (Fr ^ n) ((Fr ^ m) x) = (Fr ^ (m + n)) x := by
    intro x
    rw [add_comm m n, ← AlgEquiv.mul_apply, ← zpow_add]
  ext x
  simp only [frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom, hcomm]

end FormalOmega
end CerednikDrinfeld


set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld
namespace SpecialFormal

open FormalOmega

variable {p : ℕ} [Fact p.Prime]

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B : Type u} [CommRing B]

def frobSeries (B : Type u) [CommRing B] (j : ℕ) : Series B :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ j)

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) (ψ : O →+* B) (t t' : Rigidified p Φ B) :
    Prop :=
  t'.X = t.X ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n + k))).comp (t'.ρ.comp (frobSeries (p := p) _ m')) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
          (t.ρ.comp ((Series.map (residueMap ψ) e).comp (frobSeries (p := p) _ (2 * k))))

def IsPiTranslate (ψ : O →+* B) (t t' : Rigidified p Φ B) : Prop :=
  t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
          (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))

end Rigidified

namespace ModuliPackage

variable (𝒪 : Type) [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]

structure GPoint (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  ψ : O →ₐ[𝒪] B

  nilp : IsNilpotent (p : B)

  pt : M.obj B (ψ : O →+* B) nilp

namespace GPoint

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {x y : GPoint 𝒪 M B} (h₁ : x.ψ = y.ψ) (h₂ : HEq x.pt y.pt) : x = y := by
  obtain ⟨ψ, n, m⟩ := x
  obtain ⟨ψ', n', m'⟩ := y
  cases h₁
  cases h₂
  rfl

def map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    GPoint 𝒪 M B' where
  ψ := φ.comp x.ψ
  nilp := by simpa only [map_natCast] using x.nilp.map (φ : B →+* B')
  pt := M.map x.nilp (by simpa only [map_natCast] using x.nilp.map (φ : B →+* B'))
    (φ : B →+* B') rfl x.pt

@[simp] theorem map_ψ {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).ψ = φ.comp x.ψ := rfl

theorem map_pt {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).pt = M.map x.nilp (x.map φ).nilp (φ : B →+* B') rfl x.pt := rfl

theorem map_id (x : GPoint 𝒪 M B) : x.map (AlgHom.id 𝒪 B) = x :=
  ext' (AlgHom.id_comp _) (heq_of_eq (M.map_id x.nilp x.pt))

theorem map_comp {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂] {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃]
    (f : B →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : GPoint 𝒪 M B) :
    x.map (g.comp f) = (x.map f).map g :=
  ext' (AlgHom.comp_assoc _ _ _)
    (heq_of_eq (M.map_comp x.nilp (x.map f).nilp ((x.map f).map g).nilp (g : B₂ →+* B₃) (f : B →+* B₂)
      rfl rfl x.pt))

end GPoint

def G (M : ModuliPackage.{0, 0} p O) : AlgFunctor 𝒪 where
  obj B _ _ := GPoint 𝒪 M B
  map φ x := x.map φ
  map_id x := x.map_id
  map_comp f g x := x.map_comp f g

@[simp] theorem G_obj (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (G 𝒪 M).obj B = GPoint 𝒪 M B := rfl

@[simp] theorem G_map (M : ModuliPackage.{0, 0} p O) {B : Type} [CommRing B] [Algebra 𝒪 B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (G 𝒪 M).map φ x = x.map φ := rfl

namespace G

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
  (Fr : O ≃ₐ[𝒪] O)

def LocallyLifts {B : Type} [CommRing B] (ψ ψ' : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) (m' : M.obj B ψ' hB)
    (Rel : ∀ (L : Type) [CommRing L], (O →+* L) → Rigidified p Φ L → Rigidified p Φ L → Prop) : Prop :=
  ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
    ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (p : L)),
      ∃ t t' : Rigidified p Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧ t'.IsAdmissible ι ((algebraMap B L).comp ψ') ∧
        η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m ∧
        η L ((algebraMap B L).comp ψ') hL t' = M.map (ψ' := (algebraMap B L).comp ψ') hB hL (algebraMap B L) rfl m' ∧
        Rel L ((algebraMap B L).comp ψ) t t'

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr ((m' : ℤ) - 2 * k) x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsTranslate e k m' χ t t')

def IsPiTranslate {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr 1 x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsPiTranslate χ t t')

def IsActBy {K : Type} [Field K] [Algebra 𝒪 K]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : GPoint 𝒪 M B) : Prop :=
  ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ),
    E₀ e = (p : K) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')) ∧
    IsTranslate ι Φ η Fr (e : MvFormalGroup.End Φ.F).toPowerSeries k m' x x'

end G

end ModuliPackage

end SpecialFormal
end CerednikDrinfeld

end

end

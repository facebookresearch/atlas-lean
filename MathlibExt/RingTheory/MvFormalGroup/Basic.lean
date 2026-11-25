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

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Multivariate formal group laws

A `g`-dimensional formal group law over a commutative ring `R` (`MvFormalGroup g R`) is a family
of `g` power series in two sets of `g` variables with zero constant terms, identity linear part
in each set of variables, and associativity. This file defines commutativity
(`MvFormalGroup.IsComm`), base change (`MvFormalGroup.map`), the `n`-series
(`MvFormalGroup.nthSeries`), the linear part of a family of power series
(`MvFormalGroup.linearPart`) and the additive formal group law (`MvFormalGroup.addMv`).
It proves the unit laws `F(X, 0) = X` and `F(0, X) = X` and transports associativity and
commutativity to arbitrary arguments with zero constant terms.

Homomorphisms are in `MathlibExt.RingTheory.MvFormalGroup.Hom` and endomorphism semirings in
`MathlibExt.RingTheory.MvFormalGroup.End`.
-/

@[expose] public section

noncomputable section

open MvPowerSeries

/-- A `g`-dimensional formal group law over `R`: `g` power series in two sets of `g` variables
with zero constant terms, identity linear part in each set of variables, and associativity. -/
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

section

variable {g h k : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommRing S]

/-- A formal group law is commutative if swapping the two sets of variables fixes it. -/
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

/-- Base change of a formal group law along a ring homomorphism. -/
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
      · change MvPowerSeries.map f (subst (Sum.elim
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
      · change MvPowerSeries.map f (subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
            = subst (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inr l))) (MvPowerSeries.map f (F.toPowerSeries j))
        rw [map_subst hC, hCmap]
    rw [hAmap, hA'map] at key
    exact key

/-- The `n`-series of a formal group law: the `n`-fold formal sum of the variables. -/
def nthSeries (F : MvFormalGroup g R) : ℕ → Fin g → MvPowerSeries (Fin g) R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      subst (Sum.elim (nthSeries F n) fun j => X j) (F.toPowerSeries i)

@[simp]
theorem nthSeries_zero (F : MvFormalGroup g R) : F.nthSeries 0 = fun _ => 0 := rfl

theorem nthSeries_succ (F : MvFormalGroup g R) (n : ℕ) : F.nthSeries (n + 1) = fun i =>
    subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i) := rfl

/-- The linear part of a family of power series, as the matrix of degree-one coefficients. -/
def linearPart (φ : Fin h → MvPowerSeries (Fin g) R) : Matrix (Fin h) (Fin g) R :=
  Matrix.of fun i j => (φ i).coeff (Finsupp.single j 1)

/-- The additive formal group law `X + Y` in dimension `g`. -/
def addMv (g : ℕ) (R : Type*) [CommRing R] : MvFormalGroup g R where
  toPowerSeries := fun i => X (Sum.inl i) + X (Sum.inr i)
  constantCoeff_eq_zero := by
    intro i
    change ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0
    rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]
  coeff_single_inl := by
    intro i j
    change ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  coeff_single_inr := by
    intro i j
    change ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
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
    change subst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
        (X (Sum.inl i) + X (Sum.inr i)) = X (Sum.inl i) + X (Sum.inr i)
    rw [subst_X_add_X hz]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_comm _ _

end

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
      · rw [ite_eq_right (fun hcon => hd ((Finsupp.degree_eq_zero_iff d).mp hcon)), ite_eq_right hd]
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
          rw [ite_eq_left hd, hc1 j a]
          by_cases hja : j = a
          · subst hja
            simp
          · rw [ite_eq_right hja, ite_eq_right]
            intro hcon
            exact hja (Finsupp.single_left_injective one_ne_zero hcon).symm
        · rw [ite_eq_right hd, ite_eq_right]
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
  rwa [coeff_homogeneousComponent, ite_eq_left hde, coeff_monomial] at h1

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
      · rwa [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 rfl, ite_eq_left rfl, smul_eq_mul,
          mul_one] at h0
      · rcases lt_trichotomy e.degree n with hlt | heq | hgt
        · rw [IH e.degree hlt e rfl, zero_smul]
        · rw [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 (by rw [hd, heq]),
            ite_eq_right (fun hcon => hne hcon.symm), smul_zero]
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
    change coeff (Finsupp.single s 1) q
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
        ite_eq_right (Finsupp.single_ne_zero.mpr one_ne_zero), smul_zero]
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
  · rw [ite_eq_right (fun hcon => hij (Finsupp.single_left_injective one_ne_zero hcon).symm),
      ite_eq_right hij]

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
    · change subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
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
    · change subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
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

end MvFormalGroup

end

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_MvFormalGroup_CartierModule.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor

/-!
# Cartier modules of multivariate formal groups

For a prime `p` and a formal group law `Φ : MvFormalGroup d R`, a point of
`MvFormalGroup.CartierModule p Φ` is a family of `d` power series in the variables `ℕ` with zero
constant term that is additive from the Witt-vector addition law to `Φ`: substituting the Witt
addition polynomials (`MvFormalGroup.WittLaw.addFam`) agrees with applying `Φ` to two copies of
the family. For commutative `Φ` these form an additive group (`CartierModule.instAddCommGroup`).

The file also records the weighted homogeneity of the Witt structure polynomials and the
endomorphism families of the Witt law used to build operators: `WittLaw.IsEndo`, the
Verschiebung family `WittLaw.verFam` and, in characteristic `p`, the Frobenius family
`WittLaw.frobFam`.

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

def weight {idx : Type*} (c : idx → ℕ) : idx × ℕ → ℕ := fun im => c im.1 * p ^ im.2

omit hp in
@[simp] theorem weight_apply {idx : Type*} (c : idx → ℕ) (i : idx) (m : ℕ) :
    weight p c (i, m) = c i * p ^ m := rfl

omit hp in
theorem isWeightedHomogeneous_rename_wittPolynomial {idx : Type*} (c : idx → ℕ) (i : idx)
    (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (rename (Prod.mk i) (wittPolynomial p ℤ n))
      (c i * p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
  rw [map_mul, rename_C, map_pow, map_pow, rename_X]
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hX := (isWeightedHomogeneous_X (R := ℤ) (weight p c) (i, j)).pow (p ^ (n - j))
  have hdeg : (p ^ (n - j)) • weight p c (i, j) = c i * p ^ n := by
    rw [weight_apply, smul_eq_mul, ← mul_assoc, mul_comm (p ^ (n - j)), mul_assoc,
      ← pow_add, Nat.sub_add_cancel hj']
  rw [hdeg] at hX
  have := hX.C_mul ((p : ℤ) ^ j)
  rwa [map_pow] at this

theorem isWeightedHomogeneous_wittStructureInt {idx : Type*} (c : idx → ℕ)
    (Φ : MvPolynomial idx ℤ) (k : ℕ)
    (hΦ : ∀ n, IsWeightedHomogeneous (weight p c)
      (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) (k * p ^ n)) (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (wittStructureInt p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := wittStructureInt_prop p Φ n
    rw [← aeval_eq_bind₁, aeval_wittPolynomial, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      pow_one] at key
    have hsum : IsWeightedHomogeneous (weight p c)
        (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) (k * p ^ n) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h1 := (ih i hi').pow (p ^ (n - i))
      have hdeg : (p ^ (n - i)) • (k * p ^ i) = k * p ^ n := by
        rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le]
      rw [hdeg] at h1
      have h2 := h1.C_mul ((p : ℤ) ^ i)
      rwa [map_pow, map_natCast] at h2
    intro d hd
    by_contra hne
    have hcoeff : ((p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n).coeff d = 0 := by
      have := congrArg (fun q => q.coeff d) key
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at this
      have hR : (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ).coeff d = 0 :=
        (hΦ n).coeff_eq_zero d hne
      have hS : (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)).coeff d = 0 := hsum.coeff_eq_zero d hne
      rw [hR, hS, zero_add] at this
      exact this
    have hC : (p : MvPolynomial (idx × ℕ) ℤ) ^ n = C ((p : ℤ) ^ n) := by
      rw [map_pow, map_natCast]
    rw [hC, coeff_C_mul] at hcoeff
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero))
    · exact hd h

theorem isWeightedHomogeneous_wittAdd (n : ℕ) :
    IsWeightedHomogeneous (weight p fun _ : Fin 2 => 1) (WittVector.wittAdd p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 2 => 1) (X 0 + X 1) 1
    (fun m => by
      rw [map_add, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 1 m
      rw [one_mul] at h0 h1
      exact h0.add h1) n
  rwa [one_mul] at h

theorem isWeightedHomogeneous_wittMul (n : ℕ) :
    IsWeightedHomogeneous (weight p ![0, 1]) (WittVector.wittMul p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p ![0, 1] (X 0 * X 1) 1
    (fun m => by
      rw [map_mul, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 1 m
      simp only [Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, one_mul] at h0 h1
      have := h0.mul h1
      rwa [zero_add] at this) n
  rwa [one_mul] at h

variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n))

theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam p R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, WittVector.constantCoeff_wittAdd, map_zero]

theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {d : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff d (addFam p R n) ≠ 0) :
    Finsupp.weight (weight p fun _ : Fin 2 => 1) d = p ^ n := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : (WittVector.wittAdd p n).coeff d ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_wittAdd p n h'

theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam p R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun d => ?_⟩
  · refine (Set.finite_lt_nat (Finsupp.weight (weight p fun _ : Fin 2 => 1) d)).subset ?_
    intro n hn
    have hw := weight_eq_of_coeff_addFam_ne_zero p R hn
    change n < Finsupp.weight (weight p fun _ : Fin 2 => 1) d
    rw [hw]
    exact Nat.lt_pow_self hp.out.one_lt

instance instTendstoCofiniteProdMk (i : Fin 2) :
    Filter.TendstoCofinite (Prod.mk i : ℕ → Fin 2 × ℕ) :=
  Filter.tendstoCofinite_of_injective (Prod.mk_right_injective i)

variable {R}

def blk (i : Fin 2) : ℕ → MvPowerSeries (Fin 2 × ℕ) R := fun m => MvPowerSeries.X (i, m)

omit hp in
@[simp] theorem blk_apply (i : Fin 2) (m : ℕ) : blk (R := R) i m = MvPowerSeries.X (i, m) := rfl

omit hp in
theorem constantCoeff_blk (i : Fin 2) (m : ℕ) :
    MvPowerSeries.constantCoeff (blk (R := R) i m) = 0 :=
  MvPowerSeries.constantCoeff_X _

omit hp in
theorem hasSubst_blk (i : Fin 2) : MvPowerSeries.HasSubst (blk (R := R) i) :=
  MvPowerSeries.HasSubst.X_comp (Prod.mk i)

omit hp in
theorem subst_blk_eq_rename (i : Fin 2) (f : MvPowerSeries ℕ R) :
    MvPowerSeries.subst (blk i) f = MvPowerSeries.rename (Prod.mk i) f :=
  (MvPowerSeries.rename_eq_subst (Prod.mk i) f).symm

end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

/-- **Cartier module of a formal group law.** Let `p` be a prime and `Φ` a `d`-dimensional
formal group law over a commutative ring `R`. A point of `CartierModule p Φ` is a family of `d`
power series `f j` in the variables `X 0, X 1, …`, with zero constant terms, such that
substituting the `p`-typical Witt vector addition polynomials into each `f j` gives `Φ` applied
to two copies of `f` in disjoint blocks of variables: `f` is a homomorphism from the
`p`-typical Witt vector addition law to `Φ`. -/
structure CartierModule (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]
    (Φ : MvFormalGroup d R) where

  toPowerSeries : Fin d → MvPowerSeries ℕ R

  constantCoeff_eq_zero : ∀ j, (toPowerSeries j).constantCoeff = 0

  subst_eq : ∀ j,
    subst (WittLaw.addFam p R) (toPowerSeries j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
        (Φ.toPowerSeries j)

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

@[ext] theorem ext {f g : CartierModule p Φ} (h : f.toPowerSeries = g.toPowerSeries) : f = g := by
  cases f; cases g; cases h; rfl

theorem hasSubst_toPowerSeries (f : CartierModule p Φ) : HasSubst f.toPowerSeries :=
  hasSubst_of_constantCoeff_zero f.constantCoeff_eq_zero

def inBlk (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) : Fin d → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => subst (blk i) (a l)

omit hp in
@[simp] theorem inBlk_apply (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) (l : Fin d) :
    inBlk i a l = subst (blk i) (a l) := rfl

omit hp in
theorem constantCoeff_inBlk (i : Fin 2) {a : Fin d → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (l : Fin d) : (inBlk i a l).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk i) (constantCoeff_blk i) (ha l)

omit hp in
theorem inBlk_zero (i : Fin 2) : inBlk i (fun _ : Fin d => (0 : MvPowerSeries ℕ R)) = fun _ =>
    0 := by
  funext l
  change subst (blk i) (0 : MvPowerSeries ℕ R) = 0
  rw [← coe_substAlgHom (hasSubst_blk i), map_zero]

omit hp in
theorem inBlk_subst_elim (G : MvFormalGroup d' R) (i : Fin 2) {a b : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (hb : ∀ l, (b l).constantCoeff = 0) :
    inBlk i (fun l => subst (Sum.elim a b) (G.toPowerSeries l)) =
      fun l => subst (Sum.elim (inBlk i a) (inBlk i b)) (G.toPowerSeries l) := by
  funext l
  exact subst_subst_elim G ha hb (hasSubst_blk i) l

omit hp in
theorem inBlk_negSeries (G : MvFormalGroup d' R) (i : Fin 2) {a : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) :
    inBlk i (negSeries G a) = negSeries G (inBlk i a) := by
  have hneg : ∀ j, (negSeries G a j).constantCoeff = 0 := constantCoeff_negSeries G a
  refine negSeries_unique G (constantCoeff_inBlk i ha) (constantCoeff_inBlk i hneg) fun l => ?_
  have h := congrFun (inBlk_subst_elim G i ha hneg) l
  rw [← h]
  change subst (blk i) (subst (Sum.elim a (negSeries G a)) (G.toPowerSeries l)) = 0
  rw [subst_elim_negSeries G ha l, ← coe_substAlgHom (hasSubst_blk i), map_zero]

theorem subst_addFam (f : CartierModule p Φ) (j : Fin d) :
    subst (WittLaw.addFam p R) (f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)) (Φ.toPowerSeries j) :=
  f.subst_eq j

protected def zero (Φ : MvFormalGroup d R) : CartierModule p Φ where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro j
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    have h0 : (fun l : Fin d => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 0
    have h1 : (fun l : Fin d => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 1
    rw [h0, h1]
    exact (subst_elim_zero_right Φ (fun _ => map_zero _) j).symm

instance instZero : Zero (CartierModule p Φ) := ⟨CartierModule.zero Φ⟩

@[simp] theorem toPowerSeries_zero : (0 : CartierModule p Φ).toPowerSeries = fun _ => 0 := rfl

protected def add [Φ.IsComm] (f g : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero j
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hg := g.constantCoeff_eq_zero
    change subst (WittLaw.addFam p R)
        (subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim
        (inBlk 0 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l))
        (inBlk 1 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)
    rw [subst_subst_elim Φ hf hg (hasSubst_addFam p R) j, inBlk_subst_elim Φ 0 hf hg,
      inBlk_subst_elim Φ 1 hf hg]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    have hgeq : (fun l => subst (WittLaw.addFam p R) (g.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 g.toPowerSeries) (inBlk 1 g.toPowerSeries))
          (Φ.toPowerSeries l) := funext g.subst_addFam
    rw [hfeq, hgeq]
    exact subst_elim_exchange Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf)
      (constantCoeff_inBlk 0 hg) (constantCoeff_inBlk 1 hg) j

instance instAdd [Φ.IsComm] : Add (CartierModule p Φ) := ⟨CartierModule.add⟩

@[simp] theorem toPowerSeries_add [Φ.IsComm] (f g : CartierModule p Φ) :
    (f + g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j) := rfl

protected def neg [Φ.IsComm] (f : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := negSeries Φ f.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries Φ f.toPowerSeries
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hneg : ∀ j, (negSeries Φ f.toPowerSeries j).constantCoeff = 0 :=
      constantCoeff_negSeries Φ _
    change subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries j) =
      subst
          (Sum.elim (inBlk 0 (negSeries Φ f.toPowerSeries)) (inBlk 1 (negSeries Φ f.toPowerSeries)))
        (Φ.toPowerSeries j)
    have hS : (fun l => subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries l)) =
        negSeries Φ fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l) := by
      have hA := hasSubst_addFam p R
      have hA0 := constantCoeff_addFam p R
      refine negSeries_unique Φ (fun l => constantCoeff_subst_eq_zero hA hA0 (hf l))
        (fun l => constantCoeff_subst_eq_zero hA hA0 (hneg l)) fun i => ?_
      rw [← subst_subst_elim Φ hf hneg hA i, subst_elim_negSeries Φ hf i, ← coe_substAlgHom hA,
        map_zero]
    have h1 := congrFun hS j
    rw [h1]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfeq, negSeries_elim_add Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf),
      ← inBlk_negSeries Φ 0 hf, ← inBlk_negSeries Φ 1 hf]

instance instNeg [Φ.IsComm] : Neg (CartierModule p Φ) := ⟨CartierModule.neg⟩

@[simp] theorem toPowerSeries_neg [Φ.IsComm] (f : CartierModule p Φ) :
    (-f).toPowerSeries = negSeries Φ f.toPowerSeries := rfl

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (CartierModule p Φ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := CartierModule.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := CartierModule.ext (funext fun j =>
    subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := CartierModule.ext (funext fun j =>
    subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  add_comm a b := CartierModule.ext (funext fun j =>
    subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j)
  neg_add_cancel a := CartierModule.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

@[simp] theorem toPowerSeries_sub [Φ.IsComm] (f g : CartierModule p Φ) :
    (f - g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries (negSeries Φ g.toPowerSeries))
          (Φ.toPowerSeries j) := by
  rw [sub_eq_add_neg]; rfl

end CartierModule

namespace WittLaw

variable (p)

def pairFam (u : ℕ → MvPowerSeries ℕ R) : Fin 2 × ℕ → MvPowerSeries (Fin 2 × ℕ) R :=
  fun im => subst (blk im.1) (u im.2)

/-- **Endomorphism of the Witt vector addition law.** Let `p` be a prime and `R` a commutative
ring. A family `u` of power series over `R` in the variables `X 0, X 1, …`, indexed by `ℕ`, is an
endomorphism of the `p`-typical Witt vector addition law when it can be substituted, its members
have zero constant terms, and substituting the Witt vector addition polynomials into each `u n`
agrees with substituting two copies of `u`, in disjoint blocks of variables, into the `n`-th Witt
vector addition polynomial. -/
structure IsEndo (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (addFam p R) (u n) = subst (pairFam u) (addFam p R n)

variable {p}

omit hp in
@[simp] theorem pairFam_apply (u : ℕ → MvPowerSeries ℕ R) (i : Fin 2) (m : ℕ) :
    pairFam u (i, m) = subst (blk i) (u m) := rfl

omit hp in
theorem constantCoeff_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : ∀ n, (u n).constantCoeff = 0)
    (im : Fin 2 × ℕ) : (pairFam u im).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk im.1) (constantCoeff_blk im.1) (hu im.2)

omit hp in
theorem exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero (i : Fin 2) (f : MvPowerSeries ℕ R)
    {e : Fin 2 × ℕ →₀ ℕ} (h : coeff e (subst (blk (R := R) i) f) ≠ 0) :
    ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e ∧ coeff x f ≠ 0 := by
  rw [subst_blk_eq_rename, coeff_rename] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, hne⟩
  simpa using hx

omit hp in
theorem hasSubst_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) : HasSubst (pairFam u) := by
  refine ⟨fun im => by rw [constantCoeff_pairFam hu0]; exact IsNilpotent.zero, fun e => ?_⟩
  have hfin : ∀ i : Fin 2, {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0}.Finite := by
    intro i
    by_cases hx : ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e
    · obtain ⟨x, rfl⟩ := hx
      refine (hu.coeff_zero x).subset fun m hm => ?_
      obtain ⟨y, hy, hne⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      have hyx : y = x := Finsupp.mapDomain_injective (Prod.mk_right_injective i) hy
      rw [hyx] at hne
      exact hne
    · convert Set.finite_empty using 1
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      by_contra hm
      obtain ⟨y, hy, -⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      exact hx ⟨y, hy⟩
  have hsub : {im : Fin 2 × ℕ | coeff e (pairFam u im) ≠ 0} ⊆
      ⋃ i : Fin 2, Prod.mk i '' {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0} := by
    rintro ⟨i, m⟩ him
    exact Set.mem_iUnion.mpr ⟨i, m, him, rfl⟩
  exact (Set.finite_iUnion fun i => (hfin i).image _).subset hsub

omit hp in
theorem subst_pairFam_subst_blk {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) (i : Fin 2) (f : MvPowerSeries ℕ R) :
    subst (pairFam u) (subst (blk (R := R) i) f) = subst (blk (R := R) i) (subst u f) := by
  rw [subst_comp_subst_apply (hasSubst_blk i) (hasSubst_pairFam hu hu0),
    subst_comp_subst_apply hu (hasSubst_blk i)]
  congr 1
  funext m
  change subst (pairFam u) (X (i, m)) = subst (blk i) (u m)
  rw [subst_X (hasSubst_pairFam hu hu0)]
  rfl

variable (R)

def verFam : ℕ → MvPowerSeries ℕ R
  | 0 => 0
  | n + 1 => X n

variable {R}

omit hp in
@[simp] theorem verFam_zero : verFam R 0 = 0 := rfl

omit hp in
@[simp] theorem verFam_succ (n : ℕ) : verFam R (n + 1) = X n := rfl

omit hp in
theorem constantCoeff_verFam (n : ℕ) : (verFam R n).constantCoeff = 0 := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact constantCoeff_X _

omit hp in
theorem hasSubst_verFam : HasSubst (verFam R) := by
  classical
  refine ⟨fun n => by rw [constantCoeff_verFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (e.support.image Nat.succ).finite_toSet.subset fun n hn => ?_
  cases n with
  | zero => exact absurd (by simp) hn
  | succ n =>
    have h : coeff e (X n : MvPowerSeries ℕ R) ≠ 0 := hn
    rw [coeff_X] at h
    split_ifs at h with he
    · subst he
      simp
    · exact absurd rfl h

theorem aeval_verschiebung_wittAdd (n : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ))
      (WittVector.wittAdd p n) =
      Nat.casesOn n 0 fun m => WittVector.wittAdd p m := by
  let A := MvPolynomial (Fin 2 × ℕ) ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  let y : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (1, m)
  have key := congrArg (fun z : WittVector p A => z.coeff n)
    (WittVector.verschiebung.map_add x y).symm
  have hval : (fun im : Fin 2 × ℕ =>
      (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : A)) =
      Function.uncurry ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] := by
    funext ⟨i, m⟩
    fin_cases i <;> cases m <;> rfl
  rw [hval]
  change WittVector.peval (WittVector.wittAdd p n)
      ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] = _
  rw [← WittVector.add_coeff, key]
  cases n with
  | zero => exact WittVector.verschiebung_coeff_zero _
  | succ m =>
    rw [WittVector.verschiebung_coeff_succ, WittVector.add_coeff]
    change MvPolynomial.aeval (Function.uncurry ![x.coeff, y.coeff]) (WittVector.wittAdd p m) = _
    have hid : Function.uncurry ![x.coeff, y.coeff] = (MvPolynomial.X : Fin 2 × ℕ → A) := by
      funext ⟨i, k⟩
      fin_cases i <;> rfl
    rw [hid, MvPolynomial.aeval_X_left_apply]

theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam p R n) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval g (WittVector.wittAdd p n)) :
        MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [addFam, subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · have h1 := RingHom.ext_int (ψ₁.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
      exact RingHom.congr_fun h1 r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (WittVector.wittAdd p n)

theorem isEndo_verFam : IsEndo p (verFam R) := by
  refine ⟨hasSubst_verFam, constantCoeff_verFam, fun n => ?_⟩
  have hpair : pairFam (verFam R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R)
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ) :
          MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    cases m with
    | zero =>
      change subst (blk i) (0 : MvPowerSeries ℕ R) = _
      rw [← coe_substAlgHom (hasSubst_blk i), map_zero]
      simp
    | succ m =>
      change subst (blk i) (X m : MvPowerSeries ℕ R) = _
      rw [subst_X (hasSubst_blk i)]
      simp [blk]
  rw [hpair, subst_coe_addFam (fun im : Fin 2 × ℕ =>
    (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ)) n,
    aeval_verschiebung_wittAdd]
  cases n with
  | zero =>
    change subst (addFam p R) (0 : MvPowerSeries ℕ R) = _
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    simp
  | succ m =>
    change subst (addFam p R) (X m : MvPowerSeries ℕ R) = _
    rw [subst_X (hasSubst_addFam p R)]
    rfl

variable (p R)

def frobFam : ℕ → MvPowerSeries ℕ R := fun n => X n ^ p

variable {p R}

omit hp in
@[simp] theorem frobFam_apply (n : ℕ) : frobFam p R n = X n ^ p := rfl

theorem constantCoeff_frobFam (n : ℕ) : (frobFam p R n).constantCoeff = 0 := by
  rw [frobFam_apply, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]

theorem hasSubst_frobFam : HasSubst (frobFam p R) := HasSubst.X_pow hp.out.ne_zero

theorem subst_frobFam (f : MvPowerSeries ℕ R) :
    subst (frobFam p R) f = MvPowerSeries.expand p hp.out.ne_zero f := by
  rw [MvPowerSeries.expand, substAlgHom_apply]
  rfl

theorem expand_map_wittAdd [CharP R p] (n : ℕ) :
    MvPolynomial.expand p (MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n)) =
      MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n) ^ p := by
  have : ExpChar R p := ExpChar.prime hp.out
  rw [← MvPolynomial.map_frobenius_expand p, MvPolynomial.map_expand, MvPolynomial.map_map,
    show (frobenius R p).comp (Int.castRingHom R) = Int.castRingHom R from RingHom.ext_int _ _]

theorem isEndo_frobFam [CharP R p] : IsEndo p (frobFam p R) := by
  refine ⟨hasSubst_frobFam, constantCoeff_frobFam, fun n => ?_⟩
  have hpair : pairFam (frobFam p R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    change subst (blk i) (X m ^ p : MvPowerSeries ℕ R) = _
    rw [subst_pow (hasSubst_blk i), subst_X (hasSubst_blk i), map_pow, MvPolynomial.map_X,
      MvPolynomial.coe_pow, MvPolynomial.coe_X]
    rfl
  rw [hpair, frobFam_apply, subst_pow (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    subst_coe_addFam (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ)) n]
  have hexp : MvPolynomial.aeval (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p :
      MvPolynomial (Fin 2 × ℕ) ℤ)) (WittVector.wittAdd p n) =
      MvPolynomial.expand p (WittVector.wittAdd p n) := by
    rw [MvPolynomial.expand, ← MvPolynomial.aeval_eq_bind₁]
  rw [hexp, MvPolynomial.map_expand, expand_map_wittAdd, MvPolynomial.coe_pow]
  rfl

end WittLaw

end MvFormalGroup

end

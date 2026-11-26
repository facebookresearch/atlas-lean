/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean`,
`Theorems/Thm_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre.lean`,
`Theorems/Thm_AlgebraicCurve_discr_ne_zero_of_normalForm_split.lean`,
`Theorems/Thm_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed.lean`,
`Theorems/Thm_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.lean`,
`Theorems/Thm_AlgebraicCurve_exists_coboundary_at_infinity_of_smallExtension_of_split.lean`,
`Theorems/Thm_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension.lean`,
`Theorems/Thm_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.lean`,
`Theorems/Thm_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.lean`,
`Theorems/Thm_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.lean`,
`P2M/Sol/S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean`,
`P2M/Sol/S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre.lean`,
`P2M/Sol/S_AlgebraicCurve_discr_ne_zero_of_normalForm_split.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_coboundary_at_infinity_of_smallExtension_of_split.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.lean`,
`P2M/Sol/S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.lean`, and
`P2M/Sol/S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.lean`
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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.WittVector.Basic

import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.Complete

universe u v w w' x


-- The coordinate algebra of a structure-constant table over `Fin (N + 1)`, with the cochain
-- maps and small helpers that the auxiliary developments below share. Upstream, the solution
-- files adapted in `Aux5` to `Aux10` each carry their own copy of these declarations.
namespace CoordTable

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

section TableAlgebra

structure Table (R : Type*) [CommRing R] (N : ℕ) where

  γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R
  unit : ∀ j k, γ 0 j k = if j = k then 1 else 0
  comm : ∀ i j k, γ i j k = γ j i k
  assoc : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m

variable {R : Type*} [CommRing R] {N : ℕ}

def cst (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R) :
    Fin (N + 1) → R :=
  fun m => ∑ i, ∑ j, x i * y j * γ i j m

theorem cst_apply (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R)
    (m : Fin (N + 1)) : cst γ x y m = ∑ i, ∑ j, x i * y j * γ i j m := rfl

theorem sum3_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ t, ∑ q, f q l t := by
  calc ∑ q, ∑ l, ∑ t, f q l t = ∑ l, ∑ q, ∑ t, f q l t := Finset.sum_comm
    _ = ∑ l, ∑ t, ∑ q, f q l t := Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem sum4_rot (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l := by
  calc ∑ q, ∑ t, ∑ k, ∑ l, f q t k l = ∑ q, ∑ k, ∑ t, ∑ l, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ k, ∑ l, ∑ t, f q t k l :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ q, ∑ l, ∑ t, f q t k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ q, ∑ t, f q t k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ t, ∑ q, f q t k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

theorem cst_cst_left (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo (cst γi a b) c s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi k l q * γo q t s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  rw [sum4_rot]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_cst_right (γo γi : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (a b c : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γo a (cst γi b c) s = ∑ k, ∑ l, ∑ t, a k * b l * c t * ∑ q, γi l t q * γo k q s := by
  simp only [cst, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem cst_comm_of (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (hc : ∀ i j k, γ i j k = γ j i k) (a b : Fin (N + 1) → R) : cst γ a b = cst γ b a := by
  funext m
  rw [cst_apply, cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc j i m]; ring

theorem cst_add_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a a' b : Fin (N + 1) → R) :
    cst γ (a + a') b = cst γ a b + cst γ a' b := by
  funext m
  simp only [cst, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cst_add_right (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (a b b' : Fin (N + 1) → R) :
    cst γ a (b + b') = cst γ a b + cst γ a b' := by
  funext m
  simp only [cst, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cst_smul_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (z : R)
    (a b : Fin (N + 1) → R) : cst γ (z • a) b = z • cst γ a b := by
  funext m
  simp only [cst, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem cst_zero_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (b : Fin (N + 1) → R) :
    cst γ 0 b = 0 := by
  funext m; simp [cst]

theorem cst_single_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i : Fin (N + 1))
    (y : Fin (N + 1) → R) (m : Fin (N + 1)) :
    cst γ (Pi.single i 1) y m = ∑ q, y q * γ i q m := by
  rw [cst_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cst_single_single (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    cst γ (Pi.single i 1) (Pi.single j 1) = fun m => γ i j m := by
  funext m
  rw [cst_apply, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem cst_unit_left (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (h1 : ∀ j k, γ 0 j k = if j = k then 1 else 0) (b : Fin (N + 1) → R) :
    cst γ (Pi.single 0 1) b = b := by
  funext m
  rw [cst_apply, Finset.sum_eq_single 0]
  · simp only [Pi.single_eq_same, one_mul, h1]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ m) h
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin (N + 1))) h

structure TAlg (T : Table R N) where

  coord : Fin (N + 1) → R

namespace TAlg

variable (T : Table R N)

@[ext] theorem ext {x y : TAlg T} (h : x.coord = y.coord) : x = y := by
  cases x; cases y; congr

def equiv : TAlg T ≃ (Fin (N + 1) → R) where
  toFun := coord
  invFun := TAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TAlg T) := (equiv T).addCommGroup

instance instModule : Module R (TAlg T) :=
  ({ equiv T with map_add' := fun _ _ => rfl } : TAlg T ≃+ (Fin (N + 1) → R)).module R

@[simp] theorem coord_add (x y : TAlg T) : (x + y).coord = x.coord + y.coord := rfl
@[simp] theorem coord_zero : (0 : TAlg T).coord = 0 := rfl
@[simp] theorem coord_neg (x : TAlg T) : (-x).coord = -x.coord := rfl
@[simp] theorem coord_sub (x y : TAlg T) : (x - y).coord = x.coord - y.coord := rfl
@[simp] theorem coord_smul (z : R) (x : TAlg T) : (z • x).coord = z • x.coord := rfl
@[simp] theorem coord_mk (v : Fin (N + 1) → R) : (TAlg.mk v : TAlg T).coord = v := rfl

def linearEquiv : TAlg T ≃ₗ[R] (Fin (N + 1) → R) :=
  { equiv T with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] theorem linearEquiv_apply (x : TAlg T) : linearEquiv T x = x.coord := rfl
@[simp] theorem linearEquiv_symm_apply (v : Fin (N + 1) → R) : (linearEquiv T).symm v = TAlg.mk v :=
  rfl

theorem coord_sum {ι : Type*} (s : Finset ι) (f : ι → TAlg T) :
    (∑ i ∈ s, f i).coord = ∑ i ∈ s, (f i).coord := by
  change linearEquiv T (∑ i ∈ s, f i) = ∑ i ∈ s, linearEquiv T (f i)
  exact map_sum _ _ _

instance : Mul (TAlg T) := ⟨fun x y => TAlg.mk (cst T.γ x.coord y.coord)⟩

instance : One (TAlg T) := ⟨TAlg.mk (Pi.single 0 1)⟩

@[simp] theorem coord_mul (x y : TAlg T) : (x * y).coord = cst T.γ x.coord y.coord := rfl
@[simp] theorem coord_one : (1 : TAlg T).coord = Pi.single 0 1 := rfl

theorem mul_comm' (x y : TAlg T) : x * y = y * x := by
  ext1; simp only [coord_mul]; exact cst_comm_of T.γ T.comm _ _

theorem mul_assoc' (x y z : TAlg T) : x * y * z = x * (y * z) := by
  ext1
  simp only [coord_mul]
  funext s
  rw [cst_cst_left, cst_cst_right]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun t _ => ?_
  rw [T.assoc k l t s]

theorem one_mul' (x : TAlg T) : 1 * x = x := by
  ext1; simp only [coord_mul, coord_one]; exact cst_unit_left T.γ T.unit _

instance instCommRing : CommRing (TAlg T) where
  __ := (inferInstance : AddCommGroup (TAlg T))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' T
  one_mul := one_mul' T
  mul_one x := by rw [mul_comm']; exact one_mul' T x
  zero_mul x := by ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  mul_zero x := by rw [mul_comm']; ext1; simp only [coord_mul, coord_zero]; exact cst_zero_left _ _
  left_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_right _ _ _ _
  right_distrib x y z := by ext1; simp only [coord_mul, coord_add]; exact cst_add_left _ _ _ _
  mul_comm := mul_comm' T

theorem smul_mul_assoc' (z : R) (x y : TAlg T) : (z • x) * y = z • (x * y) := by
  ext1; simp only [coord_mul, coord_smul]; exact cst_smul_left _ _ _ _

instance instAlgebra : Algebra R (TAlg T) :=
  Algebra.ofModule (smul_mul_assoc' T) fun z x y => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

def basis : Module.Basis (Fin (N + 1)) R (TAlg T) := Module.Basis.ofEquivFun (linearEquiv T)

theorem basis_apply (i : Fin (N + 1)) : basis T i = TAlg.mk (Pi.single i 1) := by
  rw [basis, Module.Basis.coe_ofEquivFun]; rfl

theorem coord_basis (i : Fin (N + 1)) : (basis T i).coord = Pi.single i 1 := by
  rw [basis_apply]

theorem basis_repr_apply (x : TAlg T) (k : Fin (N + 1)) : (basis T).repr x k = x.coord k := by
  rw [basis, Module.Basis.ofEquivFun_repr_apply]; rfl

theorem basis_zero : basis T 0 = 1 := by
  ext1; rw [coord_basis, coord_one]

theorem basis_mul_basis_coord (i j : Fin (N + 1)) :
    (basis T i * basis T j).coord = fun m => T.γ i j m := by
  rw [coord_mul, coord_basis, coord_basis, cst_single_single]

theorem repr_basis_mul_basis (i j k : Fin (N + 1)) :
    (basis T).repr (basis T i * basis T j) k = T.γ i j k := by
  rw [basis_repr_apply, basis_mul_basis_coord]

theorem algebraMap_coord (f : R) : (algebraMap R (TAlg T) f).coord = Pi.single 0 f := by
  rw [Algebra.algebraMap_eq_smul_one, coord_smul, coord_one, ← Pi.single_smul, smul_eq_mul, mul_one]

theorem eq_sum_coord_smul_basis (x : TAlg T) : x = ∑ i, x.coord i • basis T i := by
  conv_lhs => rw [← (basis T).sum_repr x]
  simp only [basis_repr_apply]

end TAlg

section OfBasis

variable {C : Type*} [CommRing C] [Algebra R C] (e : Module.Basis (Fin (N + 1)) R C)

theorem repr_mul_unit (he : e 0 = 1) (j k : Fin (N + 1)) :
    e.repr (e 0 * e j) k = if j = k then 1 else 0 := by
  rw [he, one_mul, e.repr_self, Finsupp.single_apply]

theorem repr_mul_comm (i j k : Fin (N + 1)) : e.repr (e i * e j) k = e.repr (e j * e i) k := by
  rw [mul_comm]

theorem repr_mul_expand_left (i j l m : Fin (N + 1)) :
    e.repr (e i * e j * e l) m = ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m := by
  conv_lhs => rw [← e.sum_repr (e i * e j), Finset.sum_mul, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_expand_right (i j l m : Fin (N + 1)) :
    e.repr (e i * (e j * e l)) m = ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  conv_lhs => rw [← e.sum_repr (e j * e l), Finset.mul_sum, map_sum]
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mul_assoc (i j l m : Fin (N + 1)) :
    ∑ k, e.repr (e i * e j) k * e.repr (e k * e l) m =
      ∑ k, e.repr (e j * e l) k * e.repr (e i * e k) m := by
  rw [← repr_mul_expand_left, ← repr_mul_expand_right, mul_assoc]

def tableOfBasis (he : e 0 = 1) : Table R N where
  γ i j k := e.repr (e i * e j) k
  unit := repr_mul_unit e he
  comm := repr_mul_comm e
  assoc := repr_mul_assoc e

@[simp] theorem tableOfBasis_γ (he : e 0 = 1) (i j k : Fin (N + 1)) :
    (tableOfBasis e he).γ i j k = e.repr (e i * e j) k := rfl

end OfBasis

def Table.map {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R') : Table R' N where
  γ i j k := f (T.γ i j k)
  unit j k := by rw [T.unit]; split_ifs <;> simp
  comm i j k := by rw [T.comm]
  assoc i j l m := by
    have h := congrArg f (T.assoc i j l m)
    simpa only [map_sum, map_mul] using h

@[simp] theorem Table.map_γ {R' : Type*} [CommRing R'] (T : Table R N) (f : R →+* R')
    (i j k : Fin (N + 1)) : (T.map f).γ i j k = f (T.γ i j k) := rfl

end TableAlgebra

section Homs

variable {R : Type*} [CommRing R] {N : ℕ}

theorem cst_map {R₂ : Type*} [CommRing R₂] (f : R →+* R₂)
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : Fin (N + 1) → R) (m : Fin (N + 1)) :
    f (cst γ x y m) = cst (fun i j k => f (γ i j k)) (fun i => f (x i)) (fun j => f (y j)) m := by
  simp only [cst_apply, map_sum, map_mul]

def TAlg.mapHom (T₁ : Table R N) {R₂ : Type*} [CommRing R₂] (T₂ : Table R₂ N) (f : R →+* R₂)
    (hf : ∀ i j k, f (T₁.γ i j k) = T₂.γ i j k) : TAlg T₁ →+* TAlg T₂ where
  toFun x := TAlg.mk fun k => f (x.coord k)
  map_one' := by
    ext1; funext k
    simp only [TAlg.coord_mk, TAlg.coord_one, Pi.single_apply]
    split_ifs <;> simp
  map_mul' x y := by
    ext1; funext m
    simp only [TAlg.coord_mk, TAlg.coord_mul]
    rw [cst_map]
    simp only [hf]
  map_zero' := by ext1; funext k; simp
  map_add' x y := by ext1; funext k; simp

@[simp] theorem TAlg.mapHom_coord (T₁ : Table R N) {R₂ : Type*} [CommRing R₂] (T₂ : Table R₂ N)
    (f : R →+* R₂) (hf : ∀ i j k, f (T₁.γ i j k) = T₂.γ i j k) (x : TAlg T₁) (k : Fin (N + 1)) :
    (TAlg.mapHom T₁ T₂ f hf x).coord k = f (x.coord k) := rfl

variable {C : Type*} [CommRing C] [Algebra R C] (e : Module.Basis (Fin (N + 1)) R C)

theorem repr_sum_smul (c : Fin (N + 1) → R) (m : Fin (N + 1)) :
    e.repr (∑ k, c k • e k) m = c m := by
  rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single m]
  · rw [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
      mul_one]
  · intro k _ hk
    rw [map_smul, Finsupp.smul_apply, e.repr_self, Finsupp.single_apply, if_neg hk, smul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

end Homs

section Cochains

variable {R : Type*} [CommRing R] {N : ℕ}

def D1 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) : R :=
  (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)

def D2 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) : R :=
  (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) + (∑ k, γ j l k * φ i k m) -
    (∑ k, φ i j k * γ k l m)

theorem D1_smul (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (c : R)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (c • lam) i j m = c * D1 γ lam i j m := by
  simp only [D1, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_sub]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact Finset.sum_congr rfl fun k _ => by ring

end Cochains

section DegreeBounds

variable {N : ℕ} (d : Fin (N + 1) → ℕ) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)

include hd0 hd in
theorem d_le_two (m : Fin (N + 1)) : d m ≤ 2 := by
  by_cases hm : m = 0
  · rw [hm, hd0]; exact Nat.zero_le _
  · rcases hd m hm with h | h <;> omega

include hd in
theorem one_le_d (m : Fin (N + 1)) (hm : m ≠ 0) : 1 ≤ d m := by
  rcases hd m hm with h | h <;> omega

end DegreeBounds

section DivEps

variable {S : Type*} [CommRing S]

open Classical in
def divε (ε c : S) : S :=
  if c = 0 then 0 else if h : ε ∣ c then Classical.choose h else 0

open Classical in
theorem divε_zero (ε : S) : divε ε 0 = 0 := by simp [divε]

open Classical in
theorem mul_divε (ε c : S) (h : ε ∣ c) : ε * divε ε c = c := by
  by_cases hc : c = 0
  · simp [divε, hc]
  · rw [divε, if_neg hc, dif_pos h]
    exact (Classical.choose_spec h).symm

end DivEps

end

end CoordTable

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_aeval_sub_mem_smul_of_isMaximal_of_isIntegrallyClosed.lean`.
namespace Aux1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial UniqueFactorizationMonoid


noncomputable section

namespace FibreMonogenicSol

section Local

variable {B : Type v} [CommRing B] [IsDedekindDomain B]

theorem eq_span_sup_sq (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) : Ideal.span {t} ⊔ Q ^ 2 = Q := by
  have hle : Ideal.span {t} ⊔ Q ^ 2 ≤ Q ^ 1 := by
    rw [pow_one]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero)
  have hlt : Q ^ (1 + 1) < Ideal.span {t} ⊔ Q ^ 2 := by
    refine lt_of_le_of_ne le_sup_right fun h => ht2 ?_
    have : t ∈ Ideal.span {t} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)
    rw [← h] at this
    exact this
  have := Ideal.eq_prime_pow_of_succ_lt_of_le hQ0 hlt hle
  rw [this, pow_one]

theorem pow_le_span_pow_sup (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) (k : ℕ) : Q ^ k ≤ Ideal.span {t ^ k} ⊔ Q ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hQ : Q = Ideal.span {t} ⊔ Q ^ 2 := (eq_span_sup_sq Q hQ0 t ht ht2).symm
    calc Q ^ (k + 1) = Q ^ k * Q := pow_succ Q k
      _ ≤ (Ideal.span {t ^ k} ⊔ Q ^ (k + 1)) * Q := Ideal.mul_mono_left ih
      _ = Ideal.span {t ^ k} * Q ⊔ Q ^ (k + 1) * Q := Ideal.sup_mul _ _ _
      _ ≤ Ideal.span {t ^ (k + 1)} ⊔ Q ^ (k + 1 + 1) := by
        refine sup_le ?_ ?_
        · conv_lhs => rw [hQ]
          rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, ← pow_succ]
          refine sup_le le_sup_left (le_sup_right.trans' ?_)
          rw [show k + 1 + 1 = k + 2 by ring, pow_add]
          exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).2
            (Ideal.pow_mem_pow ht k))
        · rw [← pow_succ]; exact le_sup_right

theorem exists_expansion (Q : Ideal B) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (t : B) (ht : t ∈ Q)
    (ht2 : t ∉ Q ^ 2) {K : Type u} [Field K] (φ : K →+* B)
    (hres : ∀ b : B, ∃ a : K, b - φ a ∈ Q) (b : B) (k : ℕ) :
    ∃ a : ℕ → K, b - ∑ i ∈ Finset.range k, φ (a i) * t ^ i ∈ Q ^ k := by
  induction k with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih

    have hmem := pow_le_span_pow_sup Q hQ0 t ht ht2 k ha
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨c, hc⟩ := hres b'
    refine ⟨Function.update a k c, ?_⟩
    rw [Finset.sum_range_succ, Function.update_self]
    have hsum : ∑ i ∈ Finset.range k, φ (Function.update a k c i) * t ^ i =
        ∑ i ∈ Finset.range k, φ (a i) * t ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
    rw [hsum]
    have : b - (∑ i ∈ Finset.range k, φ (a i) * t ^ i + φ c * t ^ k) =
        (b' - φ c) * t ^ k + w := by
      have e : b - ∑ i ∈ Finset.range k, φ (a i) * t ^ i = b' * t ^ k + w := huw.symm
      linear_combination e
    rw [this]
    refine Ideal.add_mem _ ?_ hw
    rw [pow_succ']
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ht k)

end Local

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra K[X] B] [Module.Finite K[X] B] [FaithfulSMul K[X] B]

theorem main (P : Ideal K[X]) (hP : P.IsMaximal) :
    ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X], z - aeval y q ∈ P • (⊤ : Submodule K[X] B) := by
  classical

  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite K[X] B
  haveI : Algebra.IsIntegral K[X] B := inferInstance
  haveI : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral K[X] B
  haveI : IsDedekindRing B := { }
  haveI : IsDedekindDomain B := { }
  have hinj : Function.Injective (algebraMap K[X] B) := FaithfulSMul.algebraMap_injective K[X] B

  have hP0 : P ≠ ⊥ := by
    intro h; rw [h] at hP
    exact Polynomial.not_isField K (Ring.isField_iff_maximal_bot.2 hP)
  obtain ⟨c, hc⟩ : ∃ c : K, X - C c ∈ P := by
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
    have hg0 : g ≠ 0 := by rintro rfl; apply hP0; rw [hg]; simp
    have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
    have hgu : ¬IsUnit g := fun hu => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hgP hu)
    have hdeg : g.degree ≠ 0 := fun h => hgu (isUnit_iff_degree_eq_zero.2 h)
    obtain ⟨c, hcroot⟩ := IsAlgClosed.exists_root g hdeg
    refine ⟨c, ?_⟩
    have hgmem : g ∈ Ideal.span {X - C c} := by
      rw [Ideal.mem_span_singleton]; exact dvd_iff_isRoot.2 hcroot
    have hle : P ≤ Ideal.span {X - C c} := by
      rw [hg]; exact (Ideal.span_singleton_le_iff_mem _).2 hgmem
    have hne : Ideal.span {X - C c} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_X_sub_C c
    rw [hP.eq_of_le hne hle]
    exact Ideal.mem_span_singleton_self _
  let φ : K →+* B := (algebraMap K[X] B).comp C
  have hφ : ∀ a, φ a = algebraMap K[X] B (C a) := fun a => rfl

  have hred : ∀ (Q : Ideal B), Ideal.map (algebraMap K[X] B) P ≤ Q → ∀ g : K[X],
      algebraMap K[X] B g - φ (g.eval c) ∈ Q := by
    intro Q hQ g
    apply hQ
    rw [hφ, ← map_sub]
    apply Ideal.mem_map_of_mem
    have : g - C (g.eval c) ∈ Ideal.span {X - C c} := by
      rw [Ideal.mem_span_singleton, dvd_iff_isRoot]; simp
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 this
    rw [← hh]; exact P.mul_mem_left h hc

  have hres : ∀ (Q : Ideal B), Q.IsMaximal → Ideal.map (algebraMap K[X] B) P ≤ Q →
      ∀ b : B, ∃ a : K, b - φ a ∈ Q := by
    intro Q hQ hPQ b
    letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
    let f : K →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp φ
    have hf : f.IsIntegral := by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, hpm, hp⟩ : IsIntegral K[X] b := Algebra.IsIntegral.isIntegral b
      refine ⟨p.map (evalRingHom c), hpm.map _, ?_⟩
      have hcomp : (Ideal.Quotient.mk Q).comp (algebraMap K[X] B) = f.comp (evalRingHom c) := by
        ext g
        · change Ideal.Quotient.mk Q (algebraMap K[X] B (C g)) = f ((C g).eval c)
          rw [eval_C]
          rfl
        · change Ideal.Quotient.mk Q (algebraMap K[X] B X) = Ideal.Quotient.mk Q (φ (X.eval c))
          rw [eval_X, Ideal.Quotient.eq]
          have := hred Q hPQ X
          rwa [eval_X] at this
      rw [eval₂_map, ← hcomp, ← hom_eval₂, hp, map_zero]
    obtain ⟨a, ha⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral f hf).2 (Ideal.Quotient.mk Q b)
    exact ⟨a, Ideal.Quotient.eq.1 ha.symm⟩

  set I : Ideal B := Ideal.map (algebraMap K[X] B) P with hIdef
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact hP0
  let S : Finset (Ideal B) := (factors I).toFinset
  let e : Ideal B → ℕ := fun Q => (factors I).count Q
  have hSprime : ∀ Q ∈ S, Prime Q := fun Q hQ => prime_of_factor Q (Multiset.mem_toFinset.1 hQ)
  have hSprime' : ∀ Q ∈ S, Q.IsPrime := fun Q hQ => Ideal.isPrime_of_prime (hSprime Q hQ)
  have hS0 : ∀ Q ∈ S, Q ≠ ⊥ := fun Q hQ => (hSprime Q hQ).ne_zero
  have hSmax : ∀ Q ∈ S, Q.IsMaximal := fun Q hQ => (hSprime' Q hQ).isMaximal (hS0 Q hQ)
  have hprod : ∏ Q ∈ S, Q ^ e Q = I := by
    calc ∏ Q ∈ S, Q ^ e Q = ((factors I).map fun Q => Q).prod :=
          (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI0)
  have hinf : (S.inf fun Q => Q ^ e Q) = I := by
    rw [← hprod]
    exact IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun Q => Q) e hSprime
      (fun i _ j _ hij => hij)
  have hIle : ∀ Q ∈ S, I ≤ Q := by
    intro Q hQ
    have h1 : I ≤ Q ^ e Q := by rw [← hinf]; exact Finset.inf_le hQ
    exact h1.trans (Ideal.pow_le_self (Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hQ)))
  have hepos : ∀ Q ∈ S, 0 < e Q := fun Q hQ =>
    Multiset.count_pos.2 (Multiset.mem_toFinset.1 hQ)

  have hunif : ∀ Q ∈ S, ∃ t : B, t ∈ Q ∧ t ∉ Q ^ 2 := by
    intro Q hQ
    obtain ⟨t, ht1, ht2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q (hS0 Q hQ)
      (hSmax Q hQ).ne_top 1
    exact ⟨t, by rwa [pow_one] at ht1, ht2⟩
  choose! t ht ht2 using hunif

  obtain ⟨cS, hcS⟩ : ∃ cS : Ideal B → K, Set.InjOn cS S := by
    let emb : S ↪ K := ((Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding).trans
      (Infinite.natEmbedding K)
    refine ⟨fun Q => if h : Q ∈ S then emb ⟨Q, h⟩ else 0, ?_⟩
    intro Q₁ h₁ Q₂ h₂ h12
    have h₁' : Q₁ ∈ S := Finset.mem_coe.1 h₁
    have h₂' : Q₂ ∈ S := Finset.mem_coe.1 h₂
    simp only [dif_pos h₁', dif_pos h₂'] at h12
    have := emb.injective h12
    exact congrArg Subtype.val this

  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun Q => Q) e hSprime
    (fun i _ j _ hij => hij) (fun Q => φ (cS Q) + t Q)
  refine ⟨y, fun z => ?_⟩

  have hyc : ∀ Q ∈ S, y - φ (cS Q) ∈ Q := by
    intro Q hQ
    have h1 : y - (φ (cS Q) + t Q) ∈ Q := Ideal.pow_le_self (hepos Q hQ).ne' (hy Q hQ)
    have : y - φ (cS Q) = (y - (φ (cS Q) + t Q)) + t Q := by ring
    rw [this]; exact Q.add_mem h1 (ht Q hQ)

  have hloc : ∀ Q ∈ S, ∃ qQ : K[X], z - (qQ.map C).eval₂ (algebraMap K[X] B) y ∈ Q ^ e Q := by
    intro Q hQ
    haveI := hSprime' Q hQ
    obtain ⟨a, ha⟩ := exists_expansion Q (hS0 Q hQ) (t Q) (ht Q hQ) (ht2 Q hQ) φ
      (hres Q (hSmax Q hQ) (hIle Q hQ)) z (e Q)
    refine ⟨∑ i ∈ Finset.range (e Q), C (a i) * (X - C (cS Q)) ^ i, ?_⟩
    have hev : (Polynomial.map C (∑ i ∈ Finset.range (e Q), C (a i) * (X - C (cS Q)) ^ i)).eval₂
        (algebraMap K[X] B) y = ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i := by
      rw [eval₂_map]
      simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_sub, eval₂_X]
      rfl
    rw [hev]

    have hcong : (∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) -
        ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i ∈ Q ^ e Q := by
      rw [← Ideal.Quotient.eq]
      simp only [map_sum, map_mul, map_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      rw [Ideal.Quotient.eq]
      have : t Q - (y - φ (cS Q)) = -(y - (φ (cS Q) + t Q)) := by ring
      rw [this]; exact Submodule.neg_mem _ (hy Q hQ)
    have : z - ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i =
        (z - ∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) +
          ((∑ i ∈ Finset.range (e Q), φ (a i) * t Q ^ i) -
            ∑ i ∈ Finset.range (e Q), φ (a i) * (y - φ (cS Q)) ^ i) := by ring
    rw [this]
    exact Ideal.add_mem _ ha hcong
  choose! qQ hqQ using hloc

  have hTprime : ∀ Q ∈ S, Prime (Ideal.span {X - C (cS Q)} : Ideal K[X]) := fun Q _ =>
    (Ideal.prime_iff_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero _)).2
      ((Ideal.span_singleton_prime (X_sub_C_ne_zero _)).2 (prime_X_sub_C _))
  have hTcop : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, Q₁ ≠ Q₂ →
      (Ideal.span {X - C (cS Q₁)} : Ideal K[X]) ≠ Ideal.span {X - C (cS Q₂)} := by
    intro Q₁ h₁ Q₂ h₂ hne heq
    apply hne
    apply hcS h₁ h₂
    have hmem : X - C (cS Q₁) ∈ Ideal.span {X - C (cS Q₂)} := by
      rw [← heq]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot] at hmem
    simp only [IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero] at hmem
    exact hmem.symm
  obtain ⟨q, hq⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun Q => (Ideal.span {X - C (cS Q)} : Ideal K[X])) e hTprime hTcop (fun Q => qQ Q)
  refine ⟨q.map C, ?_⟩

  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hIdef, ← hinf,
    Submodule.mem_finsetInf]
  intro Q hQ
  have h1 := hqQ Q hQ
  have h2 : (Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y -
      aeval y (Polynomial.map C q) ∈ Q ^ e Q := by
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1
      ((Ideal.span_singleton_pow (X - C (cS Q)) (e Q)) ▸ hq Q hQ)

    have hdiff : Polynomial.map C (qQ Q) - Polynomial.map C q =
        -(Polynomial.map C h * (Polynomial.map C (X - C (cS Q))) ^ e Q) := by
      rw [← Polynomial.map_pow, ← Polynomial.map_mul, hh, Polynomial.map_sub]; ring
    rw [aeval_def, ← eval₂_sub, hdiff, eval₂_neg, eval₂_mul, eval₂_pow]
    refine Submodule.neg_mem _ (Ideal.mul_mem_left _ _ ?_)
    have : (Polynomial.map C (X - C (cS Q))).eval₂ (algebraMap K[X] B) y = y - φ (cS Q) := by
      rw [Polynomial.map_sub, map_X, map_C, eval₂_sub, eval₂_X, eval₂_C]
      rfl
    rw [this]
    exact Ideal.pow_mem_pow (hyc Q hQ) _
  have : z - aeval y (Polynomial.map C q) =
      (z - (Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y) +
        ((Polynomial.map C (qQ Q)).eval₂ (algebraMap K[X] B) y - aeval y (Polynomial.map C q)) := by
    ring
  rw [this]
  exact Ideal.add_mem _ h1 h2

end Main

end FibreMonogenicSol

end

private theorem aeval_sub
    (K : Type u) [Field K] [IsAlgClosed K] (B : Type v) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra K[X] B] [Module.Finite K[X] B] [FaithfulSMul K[X] B]
    (P : Ideal K[X]) (hP : P.IsMaximal) :
    ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X], z - aeval y q ∈ P • (⊤ : Submodule K[X] B) :=
  FibreMonogenicSol.main P hP

end Aux1

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_discr_ne_zero_of_normalForm_split.lean`.
namespace Aux2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial Matrix


noncomputable section

namespace DiscSplitSol

theorem coeff_prod_of_natDegree_le {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R[X]) (N : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ N i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, N i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, N i) = ∏ i ∈ s, (f i).coeff (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h' : ∀ i ∈ s, (f i).natDegree ≤ N i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ih1, ih2⟩ := ih h'
    have hfa := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (Nat.add_le_add hfa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hfa ih1, ih2]

section Main

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]

theorem main (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (τ : Fin (n + 1) → Fin (n + 1) → K) (hτu : IsUnit (Matrix.det (Matrix.of τ)))
    (hτ0 : ∀ j, τ j 0 = 1)
    (hτm : ∀ j i i', i ≠ 0 → i' ≠ 0 →
      τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    Algebra.discr K[X] b ≠ 0 := by
  classical

  set γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγdef
  have hγ0 : ∀ j k, γ 0 j k = if j = k then 1 else 0 := fun j k => by
    simp only [hγdef, hb0, one_mul, b.repr_self, Finsupp.single_apply]
  have hγc : ∀ i j k, γ i j k = γ j i k := fun i j k => by simp only [hγdef, mul_comm]
  have hdle : ∀ m, d m ≤ 2 := fun m => by
    by_cases hm : m = 0
    · rw [hm, hd0]; exact Nat.zero_le _
    · rcases hd m hm with h | h <;> omega
  have hdge : ∀ m, m ≠ 0 → 1 ≤ d m := fun m hm => by rcases hd m hm with h | h <;> omega

  have hdegAll : ∀ x y z, (γ x y z).natDegree ≤ d x + d y - d z := by
    intro x y z
    by_cases hx : x = 0
    · subst hx; rw [hγ0]; split_ifs <;> simp
    by_cases hy : y = 0
    · subst hy; rw [hγc, hγ0]; split_ifs <;> simp
    exact hdeg x y z hx hy

  have hvan : ∀ x y z, d x + d y < d z → γ x y z = 0 := by
    intro x y z hlt
    by_cases hx : x = 0
    · subst hx; rw [hγ0]; split_ifs with h
      · subst h; rw [hd0] at hlt; omega
      · rfl
    by_cases hy : y = 0
    · subst hy; rw [hγc, hγ0]; split_ifs with h
      · subst h; rw [hd0] at hlt; omega
      · rfl
    have := hdle z; have := hdge x hx; have := hdge y hy
    omega

  set c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K :=
    fun x y z => (γ x y z).coeff (d x + d y - d z)
    with hcdef
  have hc0 : ∀ y z, c 0 y z = if y = z then 1 else 0 := by
    intro y z
    simp only [hcdef, hγ0, hd0, zero_add]
    split_ifs with h
    · subst h; simp
    · simp
  have hcc : ∀ x y z, c x y z = c y x z := fun x y z => by
    simp only [hcdef, hγc x y z, Nat.add_comm (d x) (d y)]

  have hτm' : ∀ j i i', τ j i * τ j i' = ∑ k, c i i' k * τ j k := by
    intro j i i'
    by_cases hi : i = 0
    · subst hi
      rw [hτ0, one_mul]
      simp only [hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hi' : i' = 0
    · subst hi'
      rw [hτ0, mul_one]
      simp only [hcc i 0, hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    exact hτm j i i' hi hi'

  have htr : ∀ x : B, Algebra.trace K[X] B x = ∑ m, b.repr (x * b m) m := by
    intro x
    rw [Algebra.trace_eq_matrix_trace b x, Matrix.trace]
    simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  have hM : ∀ i k, Algebra.traceMatrix K[X] b i k = ∑ m, ∑ l, γ i k l * γ l m m := by
    intro i k
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htr]
    refine Finset.sum_congr rfl fun m _ => ?_

    conv_lhs => rw [← b.sum_repr (b i * b k), Finset.sum_mul, map_sum]
    rw [Finset.sum_apply']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

  have hterm : ∀ i k l m, (γ i k l * γ l m m).natDegree ≤ d i + d k ∧
      (γ i k l * γ l m m).coeff (d i + d k) = c i k l * c l m m := by
    intro i k l m
    by_cases hlt : d i + d k < d l
    · rw [hvan i k l hlt]
      simp only [zero_mul, natDegree_zero, coeff_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [hcdef, hvan i k l hlt, coeff_zero, zero_mul]
    · have h1 : (γ i k l).natDegree ≤ d i + d k - d l := hdegAll i k l
      have h2 : (γ l m m).natDegree ≤ d l := by
        have := hdegAll l m m; rwa [Nat.add_sub_cancel] at this
      have hsum : d i + d k - d l + d l = d i + d k := by omega
      refine ⟨natDegree_mul_le.trans (by omega), ?_⟩
      rw [← hsum, coeff_mul_add_eq_of_natDegree_le h1 h2]
      simp only [hcdef, Nat.add_sub_cancel]
  have hMdeg : ∀ i k, (Algebra.traceMatrix K[X] b i k).natDegree ≤ d i + d k := by
    intro i k
    rw [hM]
    exact natDegree_sum_le_of_forall_le _ _ fun m _ =>
      natDegree_sum_le_of_forall_le _ _ fun l _ => (hterm i k l m).1
  have hMtop : ∀ i k, (Algebra.traceMatrix K[X] b i k).coeff (d i + d k) =
      ∑ m, ∑ l, c i k l * c l m m := by
    intro i k
    rw [hM, finsetSum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [finsetSum_coeff]
    exact Finset.sum_congr rfl fun l _ => (hterm i k l m).2

  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of τ with hTdef
  have htrace : ∀ l, ∑ m, c l m m = ∑ j, τ j l := by
    intro l
    let Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun m l' => c l l' m
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.diagonal fun j => τ j l
    have hTL : T * Λ = D * T := by
      ext j l'
      rw [Matrix.mul_apply, Matrix.diagonal_mul]
      change ∑ m, τ j m * c l l' m = τ j l * τ j l'
      rw [hτm' j l l']
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    have hΛ : Λ = T⁻¹ * D * T := by
      rw [Matrix.mul_assoc, ← hTL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul T hτu,
        Matrix.one_mul]
    have h1 : Matrix.trace Λ = ∑ m, c l m m := by
      simp only [Matrix.trace, Matrix.diag, Λ, Matrix.of_apply]
    rw [← h1, hΛ, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv T hτu, Matrix.one_mul,
      Matrix.trace_diagonal]
  have hMtop' : ∀ i k, (Algebra.traceMatrix K[X] b i k).coeff (d i + d k) = (Tᵀ * T) i k := by
    intro i k
    rw [hMtop, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hTdef, Matrix.of_apply]
    calc ∑ m, ∑ l, c i k l * c l m m = ∑ l, c i k l * ∑ m, c l m m := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
      _ = ∑ l, c i k l * ∑ j, τ j l := Finset.sum_congr rfl fun l _ => by rw [htrace]
      _ = ∑ j, ∑ l, c i k l * τ j l := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
      _ = ∑ j, τ j i * τ j k := Finset.sum_congr rfl fun j _ => (hτm' j i k).symm

  set Dtot : ℕ := ∑ i, d i + ∑ i, d i with hDtot
  have hdet : (Algebra.discr K[X] b).coeff Dtot = (Tᵀ * T).det := by
    rw [Algebra.discr_def, Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    rw [← C_eq_intCast, coeff_C_mul]
    congr 1
    have hσsum : ∑ i, (d (σ i) + d i) = Dtot := by
      rw [Finset.sum_add_distrib, hDtot]
      congr 1
      exact Equiv.sum_comp σ d
    have := (coeff_prod_of_natDegree_le Finset.univ
      (fun i => Algebra.traceMatrix K[X] b (σ i) i) (fun i => d (σ i) + d i)
      (fun i _ => hMdeg (σ i) i)).2
    rw [hσsum] at this
    rw [this]
    exact Finset.prod_congr rfl fun i _ => hMtop' (σ i) i
  have hdetne : (Tᵀ * T).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    have hne : T.det ≠ 0 := hτu.ne_zero
    exact mul_ne_zero hne hne
  intro hzero
  apply hdetne
  rw [← hdet, hzero, coeff_zero]

end Main

end DiscSplitSol

end

private theorem discr_ne_zero
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    Algebra.discr K[X] b ≠ 0 := by
  obtain ⟨τ, hτu, hτ0, hτm⟩ := hinf
  exact DiscSplitSol.main b d hb0 hd0 hd hdeg τ hτu hτ0 hτm

end Aux2

-- Adapted from
-- `P2M/Sol/S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre.lean`.
namespace Aux3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial


noncomputable section

namespace MonogenicLiftSol

open Classical in

theorem main
    (R' : Type u) [CommRing R'] [IsLocalRing R'] (R : Type v) [CommRing R] [IsLocalRing R]
    (π : R' →+* R) (hπ : Function.Surjective π)
    (C : Type w) [CommRing C] [Algebra R C] (ι : Type x) [Fintype ι]
    (e : Module.Basis ι R C) (i₀ : ι) (he : e i₀ = 1)
    (y : C) (hy : ∀ z : C, ∃ q : R[X],
      z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C')
      (σ : C' →+* C),
      e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
  haveI : Module.Free R C := Module.Free.of_basis e
  haveI : Module.Finite R C := Module.Finite.of_basis e
  haveI : Nonempty ι := ⟨i₀⟩

  have hspan_all : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro z _
    obtain ⟨q, hq⟩ := hy z
    have h1 : aeval y q ∈ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
      rw [aeval_eq_sum_range]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have h2 : z = aeval y q + (z - aeval y q) := by ring
    rw [h2]
    exact Submodule.add_mem_sup h1 hq

  set χ : R[X] := (Algebra.lmul R C y).charpoly with hχdef
  have hχm : χ.Monic := LinearMap.charpoly_monic _
  have hχdeg : χ.natDegree = Fintype.card ι := by
    rw [hχdef, LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis e]
  have hχy : aeval y χ = 0 := by
    have h0 : Algebra.lmul R C (aeval y χ) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]
      exact LinearMap.aeval_self_charpoly _
    exact Algebra.lmul_injective (R := R) (by rw [h0, map_zero])
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hχ1 : χ ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hχdeg, natDegree_one] at this
    omega

  obtain ⟨χ', hχ'map, hχ'deg, hχ'm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hπ χ) hχm
  set d : ℕ := χ'.natDegree with hddef
  have hd : d = Fintype.card ι := by rw [hχ'deg, hχdeg]
  have hd0 : 0 < d := by rw [hd]; exact hcard

  set v : Fin d → C := fun j => y ^ (j : ℕ) with hvdef
  have hv_span : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range v) := by
    refine hspan_all.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk : y ^ k = aeval y (X ^ k %ₘ χ) := by
      rw [aeval_modByMonic_eq_self_of_root hχy, map_pow, aeval_X]
    have hlt : (X ^ k %ₘ χ).natDegree < d := by
      rw [hd, ← hχdeg]
      exact natDegree_modByMonic_lt _ hχm hχ1
    change y ^ k ∈ Submodule.span R (Set.range v)
    rw [hk, aeval_eq_sum_range' hlt, ← Fin.sum_univ_eq_sum_range]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let ιd : ι ≃ Fin d := (Fintype.equivFinOfCardEq hd.symm)
  have hv_li : LinearIndependent R v := by
    let L : (Fin d →₀ R) →ₗ[R] C := Finsupp.linearCombination R v
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact top_le_iff.mp hv_span
    let inj : (Fin d →₀ R) →ₗ[R] C :=
      e.repr.symm.toLinearMap ∘ₗ (Finsupp.domLCongr ιd.symm).toLinearMap
    have hinj : Function.Injective inj :=
      e.repr.symm.injective.comp (Finsupp.domLCongr ιd.symm).injective
    exact OrzechProperty.injective_of_surjective_of_injective inj L hinj hL
  let vB : Module.Basis (Fin d) R C := Module.Basis.mk hv_li hv_span
  have hvB : ∀ j, vB j = y ^ (j : ℕ) := fun j => by rw [Module.Basis.mk_apply]

  haveI : Module.Free R' (AdjoinRoot χ') := hχ'm.free_adjoinRoot
  haveI : Module.Finite R' (AdjoinRoot χ') := hχ'm.finite_adjoinRoot
  let pb : PowerBasis R' (AdjoinRoot χ') := AdjoinRoot.powerBasis' hχ'm
  have hpbdim : pb.dim = d := rfl
  have hpb : ∀ j : Fin d, pb.basis j = AdjoinRoot.root χ' ^ (j : ℕ) := fun j => by
    rw [PowerBasis.coe_basis]; rfl
  have hev : χ'.eval₂ ((algebraMap R C).comp π) y = 0 := by
    rw [← Polynomial.eval₂_map, hχ'map]
    exact hχy
  let σ : AdjoinRoot χ' →+* C := AdjoinRoot.lift ((algebraMap R C).comp π) y hev
  have hσ_of : ∀ r, σ (algebraMap R' (AdjoinRoot χ') r) = algebraMap R C (π r) := fun r => by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of hev
  have hσ_root : ∀ k : ℕ, σ (AdjoinRoot.root χ' ^ k) = y ^ k := fun k => by
    rw [map_pow, AdjoinRoot.lift_root]
  have hσ_smul : ∀ (r : R') (c : AdjoinRoot χ'), σ (r • c) = π r • σ c := fun r c => by
    rw [Algebra.smul_def, map_mul, hσ_of, ← Algebra.smul_def]
  have hσ_sum : ∀ a : Fin d → R', σ (∑ j, a j • pb.basis j) = ∑ j, π (a j) • v j := fun a => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hσ_smul, hpb, hσ_root]

  have hkerσ : ∀ c : AdjoinRoot χ', σ c = 0 →
      c ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) := by
    intro c hc
    have hc' : c = ∑ j : Fin d, pb.basis.repr c j • pb.basis j := (pb.basis.sum_repr c).symm
    rw [hc'] at hc
    replace hc : (∑ j, π (pb.basis.repr c j) • v j) = 0 :=
      (hσ_sum (fun j => pb.basis.repr c j)).symm.trans hc
    have hzero : ∀ j, π (pb.basis.repr c j) = 0 := fun j =>
      linearIndependent_iff'.mp hv_li Finset.univ (fun j => π (pb.basis.repr c j)) hc j
        (Finset.mem_univ j)
    rw [hc']
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hzero j)) Submodule.mem_top

  let s : R → R' := Function.surjInv hπ
  have hs : ∀ r, π (s r) = r := Function.surjInv_eq hπ
  let j₀ : Fin d := ⟨0, hd0⟩
  have hvB0 : vB j₀ = 1 := by rw [hvB]; simp [j₀]
  have hP0 : ∀ j : Fin d, vB.repr (e i₀) j = if j = j₀ then 1 else 0 := fun j => by
    rw [he, ← hvB0, vB.repr_self, Finsupp.single_apply]
    by_cases h : j = j₀
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  let P' : ι → Fin d → R' := fun i j =>
    if i = i₀ then (if j = j₀ then 1 else 0) else s (vB.repr (e i) j)
  have hP' : ∀ i j, π (P' i j) = vB.repr (e i) j := by
    intro i j
    by_cases hi : i = i₀
    · subst hi
      simp only [P', if_true, hP0]
      split_ifs <;> simp
    · simp only [P', if_neg hi, hs]
  let ev : ι → AdjoinRoot χ' := fun i => ∑ j, P' i j • pb.basis j
  have hσev : ∀ i, σ (ev i) = e i := fun i => by
    change σ (∑ j, P' i j • pb.basis j) = e i
    rw [hσ_sum]
    conv_rhs => rw [← vB.sum_repr (e i)]
    exact Finset.sum_congr rfl fun j _ => by rw [hP', hvB]
  have hev0 : ev i₀ = 1 := by
    change ∑ j, P' i₀ j • pb.basis j = 1
    rw [Finset.sum_eq_single j₀]
    · simp only [P', if_true, one_smul, hpb]
      simp [j₀]
    · intro j _ hj
      simp only [P', if_true, if_neg hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ j₀) h

  have hkerπ : RingHom.ker π ≤ (⊥ : Ideal R').jacobson :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hev_span : (⊤ : Submodule R' (AdjoinRoot χ')) ≤ Submodule.span R' (Set.range ev) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hkerπ
    intro c _
    let c'' : AdjoinRoot χ' := ∑ i, s (e.repr (σ c) i) • ev i
    have hc'' : c'' ∈ Submodule.span R' (Set.range ev) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hσc'' : σ c'' = σ c := by
      change σ (∑ i, s (e.repr (σ c) i) • ev i) = σ c
      rw [map_sum]
      conv_rhs => rw [← e.sum_repr (σ c)]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ_smul, hs, hσev]
    have hdiff : c - c'' ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) :=
      hkerσ _ (by rw [map_sub, hσc'', sub_self])
    have : c = c'' + (c - c'') := by ring
    rw [this]
    exact Submodule.add_mem_sup hc'' hdiff

  have hev_li : LinearIndependent R' ev := by
    let L : (ι →₀ R') →ₗ[R'] AdjoinRoot χ' := Finsupp.linearCombination R' ev
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact top_le_iff.mp hev_span
    let inj : (ι →₀ R') →ₗ[R'] AdjoinRoot χ' :=
      pb.basis.repr.symm.toLinearMap ∘ₗ (Finsupp.domLCongr ιd).toLinearMap
    have hinj : Function.Injective inj :=
      pb.basis.repr.symm.injective.comp (Finsupp.domLCongr ιd).injective
    exact OrzechProperty.injective_of_surjective_of_injective inj L hinj hL
  let e' : Module.Basis ι R' (AdjoinRoot χ') := Module.Basis.mk hev_li hev_span
  refine ⟨AdjoinRoot χ', inferInstance, inferInstance, e', σ, ?_, hσ_of, fun i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact hev0
  · rw [Module.Basis.mk_apply]; exact hσev i

end MonogenicLiftSol

end

private theorem lift_basis
    (R' : Type u) [CommRing R'] [IsLocalRing R'] (R : Type v) [CommRing R] [IsLocalRing R]
    (π : R' →+* R) (hπ : Function.Surjective π)
    (C : Type w) [CommRing C] [Algebra R C] (ι : Type x) [Fintype ι]
    (e : Module.Basis ι R C) (i₀ : ι) (he : e i₀ = 1)
    (hmono : ∃ y : C, ∀ z : C, ∃ q : R[X],
      z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C')
      (σ : C' →+* C),
      e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
  obtain ⟨y, hy⟩ := hmono
  exact MonogenicLiftSol.main R' R π hπ C ι e i₀ he y hy

end Aux3

-- Adapted from
-- `P2M/Sol/S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean`.
namespace Aux4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


noncomputable section

namespace HochschildSplitSol

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

structure Cocycle (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] where

  ψ : S →ₗ[R] S →ₗ[R] M
  symm : ∀ x y, ψ x y = ψ y x
  one : ∀ y, ψ 1 y = 0
  coc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0

structure Ext (c : Cocycle R S M) where

  fst : S

  snd : M

namespace Ext

variable (c : Cocycle R S M)

@[ext] theorem ext {a b : Ext c} (h1 : a.fst = b.fst) (h2 : a.snd = b.snd) : a = b := by
  cases a; cases b; congr

def equiv : Ext c ≃ S × M where
  toFun a := (a.fst, a.snd)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Ext c) := (equiv c).addCommGroup

instance instModule : Module R (Ext c) :=
  ({ equiv c with map_add' := fun _ _ => rfl } : Ext c ≃+ (S × M)).module R

@[simp] theorem fst_add (a b : Ext c) : (a + b).fst = a.fst + b.fst := rfl
@[simp] theorem snd_add (a b : Ext c) : (a + b).snd = a.snd + b.snd := rfl
@[simp] theorem fst_zero : (0 : Ext c).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : Ext c).snd = 0 := rfl
@[simp] theorem fst_neg (a : Ext c) : (-a).fst = -a.fst := rfl
@[simp] theorem snd_neg (a : Ext c) : (-a).snd = -a.snd := rfl
@[simp] theorem fst_smul (r : R) (a : Ext c) : (r • a).fst = r • a.fst := rfl
@[simp] theorem snd_smul (r : R) (a : Ext c) : (r • a).snd = r • a.snd := rfl
@[simp] theorem fst_mk (x : S) (u : M) : (Ext.mk x u : Ext c).fst = x := rfl
@[simp] theorem snd_mk (x : S) (u : M) : (Ext.mk x u : Ext c).snd = u := rfl

instance : Mul (Ext c) :=
  ⟨fun a b => ⟨a.fst * b.fst, a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst⟩⟩

instance : One (Ext c) := ⟨⟨1, 0⟩⟩

@[simp] theorem fst_mul (a b : Ext c) : (a * b).fst = a.fst * b.fst := rfl
@[simp] theorem snd_mul (a b : Ext c) :
    (a * b).snd = a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst := rfl
@[simp] theorem fst_one : (1 : Ext c).fst = 1 := rfl
@[simp] theorem snd_one : (1 : Ext c).snd = 0 := rfl

theorem mul_comm' (a b : Ext c) : a * b = b * a := by
  ext
  · simp only [fst_mul, mul_comm]
  · simp only [snd_mul, c.symm a.fst b.fst]
    abel

theorem mul_assoc' (a b d : Ext c) : a * b * d = a * (b * d) := by
  ext
  · simp only [fst_mul, mul_assoc]
  · simp only [snd_mul, fst_mul, smul_add]
    rw [← sub_eq_zero]
    have h := c.coc a.fst b.fst d.fst
    calc _ = -(a.fst • c.ψ b.fst d.fst - c.ψ (a.fst * b.fst) d.fst +
          c.ψ a.fst (b.fst * d.fst) - d.fst • c.ψ a.fst b.fst) := by
          simp only [smul_smul]
          module
      _ = 0 := by rw [h, neg_zero]

theorem one_mul' (a : Ext c) : 1 * a = a := by
  ext
  · simp only [fst_mul, fst_one, one_mul]
  · simp only [snd_mul, fst_one, snd_one, one_smul, smul_zero, add_zero, c.one]

instance instCommRing : CommRing (Ext c) where
  __ := (inferInstance : AddCommGroup (Ext c))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' c
  one_mul := one_mul' c
  mul_one a := by rw [mul_comm']; exact one_mul' c a
  zero_mul a := by
    ext
    · simp only [fst_mul, fst_zero, zero_mul]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero,
        LinearMap.zero_apply, add_zero]
  mul_zero a := by
    ext
    · simp only [fst_mul, fst_zero, mul_zero]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero, add_zero]
  left_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, mul_add]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add]
      abel
  right_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, add_mul]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add, LinearMap.add_apply]
      abel
  mul_comm := mul_comm' c

theorem smul_mul_assoc' (r : R) (a b : Ext c) : (r • a) * b = r • (a * b) := by
  ext
  · simp only [fst_mul, fst_smul, smul_mul_assoc]
  · simp only [snd_mul, fst_smul, snd_smul, smul_add, LinearMap.map_smul₂, smul_assoc]
    rw [smul_comm b.fst r a.snd]

instance instAlgebra : Algebra R (Ext c) :=
  Algebra.ofModule (smul_mul_assoc' c) fun r a b => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

def fstHom : Ext c →ₐ[R] S where
  toFun := Ext.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, fst_smul, fst_one, Algebra.algebraMap_eq_smul_one]

theorem fstHom_apply (a : Ext c) : fstHom c a = a.fst := rfl

theorem fstHom_surjective : Function.Surjective (fstHom c) := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem fst_eq_zero_of_mem_ker {a : Ext c} (ha : a ∈ RingHom.ker (fstHom c : Ext c →+* S)) :
    a.fst = 0 := ha

theorem ker_sq_eq_bot : RingHom.ker (fstHom c : Ext c →+* S) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha' := fst_eq_zero_of_mem_ker c ha
  have hb' := fst_eq_zero_of_mem_ker c hb
  ext
  · simp only [fst_mul, ha', zero_mul, fst_zero]
  · simp only [snd_mul, ha', hb', zero_smul, map_zero, add_zero, snd_zero]

theorem isNilpotent_ker : IsNilpotent (RingHom.ker (fstHom c : Ext c →+* S)) :=
  ⟨2, ker_sq_eq_bot c⟩

variable [Algebra.FormallySmooth R S]

def sect : S →ₐ[R] Ext c :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) (fstHom c) (fstHom_surjective c)
    (isNilpotent_ker c)

theorem fst_sect (x : S) : (sect c x).fst = x := by
  have h := Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R S) (fstHom c)
    (fstHom_surjective c) (isNilpotent_ker c) x
  exact h

def ell : S →ₗ[R] M where
  toFun x := (sect c x).snd
  map_add' x y := by rw [map_add, snd_add]
  map_smul' r x := by rw [map_smul, snd_smul, RingHom.id_apply]

theorem ell_apply (x : S) : ell c x = (sect c x).snd := rfl

theorem ell_one : ell c 1 = 0 := by rw [ell_apply, map_one, snd_one]

theorem ψ_eq (x y : S) : c.ψ x y = ell c (x * y) - x • ell c y - y • ell c x := by
  have h := congrArg Ext.snd (map_mul (sect c) x y)
  rw [snd_mul, fst_sect, fst_sect] at h
  rw [ell_apply, ell_apply, ell_apply, h]
  abel

end Ext

end HochschildSplitSol

end

open HochschildSplitSol in
private theorem formally_smooth_linear
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (ψ : S →ₗ[R] S →ₗ[R] M)
    (hsymm : ∀ x y, ψ x y = ψ y x)
    (hone : ∀ y, ψ 1 y = 0)
    (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
    ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x :=
  let c : Cocycle R S M := ⟨ψ, hsymm, hone, hcoc⟩
  ⟨Ext.ell c, Ext.ell_one c, Ext.ψ_eq c⟩

end Aux4

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre.lean`.
namespace Aux5

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable


noncomputable section

namespace LocCobSol


section Homs

variable {R : Type*} [CommRing R] {N : ℕ}


variable {C : Type*} [CommRing C] [Algebra R C] (e : Module.Basis (Fin (N + 1)) R C)

theorem repr_mul_eq_cst (x y : C) (m : Fin (N + 1)) :
    e.repr (x * y) m = cst (fun i j k => e.repr (e i * e j) k) (fun i => e.repr x i)
      (fun j => e.repr y j) m := by
  have hx : x = ∑ i, e.repr x i • e i := (e.sum_repr x).symm
  have hy : y = ∑ j, e.repr y j • e j := (e.sum_repr y).symm
  conv_lhs => rw [hx, hy, Finset.sum_mul_sum]
  rw [map_sum, Finsupp.finsetSum_apply, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]


def basedHom (he : e 0 = 1) {R₂ : Type*} [CommRing R₂] (T : Table R₂ N) (f : R →+* R₂)
    (hf : ∀ i j k, f (e.repr (e i * e j) k) = T.γ i j k) : C →+* TAlg T where
  toFun x := TAlg.mk fun k => f (e.repr x k)
  map_one' := by
    ext1; funext k
    simp only [TAlg.coord_mk, TAlg.coord_one, Pi.single_apply, ← he, e.repr_self,
      Finsupp.single_apply]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero]
  map_mul' x y := by
    ext1; funext m
    simp only [TAlg.coord_mk, TAlg.coord_mul]
    rw [repr_mul_eq_cst, cst_map]
    simp only [hf]
  map_zero' := by ext1; funext k; simp
  map_add' x y := by ext1; funext k; simp

@[simp] theorem basedHom_coord (he : e 0 = 1) {R₂ : Type*} [CommRing R₂] (T : Table R₂ N)
    (f : R →+* R₂) (hf : ∀ i j k, f (e.repr (e i * e j) k) = T.γ i j k) (x : C) (k : Fin (N + 1)) :
    (basedHom e he T f hf x).coord k = f (e.repr x k) := rfl

end Homs

section PolyKer

variable {S T : Type*} [CommRing S] [CommRing T]


theorem exists_eq_C_mul_of_map_eq_zero (π : S →+* T) (ε : S) (hker : ∀ a : S, π a = 0 ↔ ε ∣ a)
    (f : S[X]) (hf : f.map π = 0) : ∃ g : S[X], f = C ε * g := by
  refine ⟨∑ t ∈ Finset.range (f.natDegree + 1), C (divε ε (f.coeff t)) * X ^ t, ?_⟩
  ext t
  rw [coeff_C_mul, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  have hdiv : ε ∣ f.coeff t := by
    rw [← hker]
    have := congrArg (fun F : T[X] => F.coeff t) hf
    simpa only [coeff_map, coeff_zero] using this
  by_cases ht : t < f.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, mul_divε ε _ hdiv]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, mul_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

end PolyKer

section Main

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (P : Ideal K[X]) (hP : P.IsMaximal)
    (hmono : ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X],
      z - aeval y q ∈ P • (⊤ : Submodule K[X] B)) :
    ∃ s : K[X], s ∉ P ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        s * (ac i j l m).map (ρ.comp π) := by
  classical

  let θ : A' →+* K := ρ.comp π
  let πX : A'[X] →+* A[X] := mapRingHom π
  let ρX : A[X] →+* K[X] := mapRingHom ρ
  let θX : A'[X] →+* K[X] := mapRingHom θ
  have hθX : ∀ f : A'[X], θX f = ρX (πX f) := fun f => by
    change f.map θ = (f.map π).map ρ
    rw [Polynomial.map_map]
  have hπXs : Function.Surjective πX := Polynomial.map_surjective π hπ
  have hρXs : Function.Surjective ρX := Polynomial.map_surjective ρ hρ
  have hπε : π ε = 0 := (hker ε).2 (dvd_refl ε)
  have hθε : θX (C ε) = 0 := by
    change (C ε).map θ = 0
    rw [map_C]; change C (ρ (π ε)) = 0; rw [hπε, map_zero, C_0]

  have hannX : ∀ W : A'[X], C ε * W = 0 → θX W = 0 := by
    intro W hW
    ext t
    rw [coeff_zero]
    change (W.map θ).coeff t = 0
    rw [coeff_map]
    exact hann _ (by simpa only [coeff_C_mul, coeff_zero] using congrArg (fun F => F.coeff t) hW)
  haveI hPmax : P.IsMaximal := hP
  let Q : Ideal A[X] := P.comap ρX
  haveI hQmax : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective ρX hρXs
  haveI hQprime : Q.IsPrime := hQmax.isPrime
  let Q' : Ideal A'[X] := Q.comap πX
  haveI hQ'max : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective πX hπXs
  haveI hQ'prime : Q'.IsPrime := hQ'max.isPrime
  have hmemQ' : ∀ f : A'[X], f ∈ Q' ↔ θX f ∈ P := fun f => by
    rw [hθX]; rfl
  let Rl := Localization.AtPrime Q
  let R'l := Localization.AtPrime Q'
  let πl : R'l →+* Rl := Localization.localRingHom Q' Q πX rfl
  have hπl_alg : ∀ x : A'[X], πl (algebraMap A'[X] R'l x) = algebraMap A[X] Rl (πX x) :=
    fun x => Localization.localRingHom_to_map Q' Q πX rfl x

  have hπls : Function.Surjective πl := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨a', ha'⟩ := hπXs a
    obtain ⟨s', hs'⟩ := hπXs s
    have hs'Q : s' ∈ Q'.primeCompl := by
      intro h
      apply s.2
      change πX s' ∈ Q at h
      rwa [hs'] at h
    refine ⟨IsLocalization.mk' R'l a' ⟨s', hs'Q⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    change IsLocalization.mk' Rl (πX a') _ = IsLocalization.mk' Rl a s
    congr 1
    exact Subtype.ext hs'

  let εl : R'l := algebraMap A'[X] R'l (C ε)
  have hkerl : ∀ x : R'l, πl x = 0 → ∃ z : R'l, x = εl * z := by
    intro x hx
    obtain ⟨⟨a', s'⟩, rfl⟩ := IsLocalization.mk'_surjective Q'.primeCompl x
    change πl (IsLocalization.mk' R'l a' s') = 0 at hx
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hπXs m
    have hm'Q : m' ∈ Q'.primeCompl := by
      intro h; apply m.2; change πX m' ∈ Q at h; rwa [hm'] at h
    have h0 : πX (m' * a') = 0 := by rw [map_mul, hm']; exact hm
    have h0' : (m' * a').map π = 0 := h0
    obtain ⟨g, hg⟩ := exists_eq_C_mul_of_map_eq_zero π ε hker (m' * a') h0'
    refine ⟨IsLocalization.mk' R'l g (⟨m', hm'Q⟩ * s'), ?_⟩
    change IsLocalization.mk' R'l a' s' = algebraMap A'[X] R'l (C ε) * IsLocalization.mk' R'l g _
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, ← hg, IsLocalization.mk'_mul,
      IsLocalization.mk'_self R'l hm'Q, one_mul]

  have hannl : ∀ W : A'[X], algebraMap A'[X] R'l (C ε * W) = 0 → θX W = 0 := by
    intro W hW
    rw [IsLocalization.map_eq_zero_iff Q'.primeCompl] at hW
    obtain ⟨v, hv⟩ := hW
    have h1 : θX (v * W) = 0 := hannX _ (by rw [← hv]; ring)
    rw [map_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso; apply v.2
      change (v : A'[X]) ∈ Q'
      rw [hmemQ', h]; exact P.zero_mem
    · exact h

  let κ := K[X] ⧸ P
  letI : Field κ := Ideal.Quotient.field P
  let mkP : K[X] →+* κ := Ideal.Quotient.mk P
  have hunit : ∀ s : Q.primeCompl, IsUnit ((mkP.comp ρX) s) := by
    intro s
    rw [isUnit_iff_ne_zero]
    intro h
    apply s.2
    change ρX s ∈ P
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  let lam : Rl →+* κ := IsLocalization.lift (M := Q.primeCompl) (S := Rl) hunit
  have hlam_alg : ∀ x : A[X], lam (algebraMap A[X] Rl x) = mkP (ρX x) := fun x =>
    IsLocalization.lift_eq hunit x
  have hlams : Function.Surjective lam := by
    intro c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨g, rfl⟩ := hρXs f
    exact ⟨algebraMap A[X] Rl g, hlam_alg g⟩
  have hlamker : ∀ x : Rl, lam x = 0 → x ∈ IsLocalRing.maximalIdeal Rl := by
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    change IsLocalization.mk' Rl a s ∈ _
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff Rl Q a s]
    have h1 := IsLocalization.mk'_spec Rl a s
    have h2 := congrArg lam h1
    change lam (IsLocalization.mk' Rl a s) = 0 at hx
    rw [map_mul, hx, zero_mul, hlam_alg] at h2
    change a ∈ P.comap ρX
    rw [Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2.symm

  let TA : Table A[X] n := ⟨γ, hγ1, hγc, hγa⟩
  let Tl : Table Rl n := TA.map (algebraMap A[X] Rl)
  let TB : Table K[X] n := tableOfBasis b hb0
  let Tκ : Table κ n := TB.map mkP
  let Cl := TAlg Tl
  let e : Module.Basis (Fin (n + 1)) Rl Cl := TAlg.basis Tl
  have he0 : e 0 = 1 := TAlg.basis_zero Tl
  have hlamγ : ∀ i j k, lam (Tl.γ i j k) = Tκ.γ i j k := by
    intro i j k
    change lam (algebraMap A[X] Rl (γ i j k)) = mkP (b.repr (b i * b j) k)
    rw [hlam_alg, ← hγB]; rfl
  let redC : Cl →+* TAlg Tκ := TAlg.mapHom Tl Tκ lam hlamγ
  let redB : B →+* TAlg Tκ := basedHom b hb0 Tκ mkP (fun i j k => rfl)

  have hredB_P : ∀ z : B, z ∈ P • (⊤ : Submodule K[X] B) → redB z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp w _ => ?_) (fun x y hx hy => ?_)
    · ext1; funext k
      rw [show (redB (p • w)).coord k = mkP (b.repr (p • w) k) from rfl]
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
      rfl
    · rw [map_add, hx, hy, add_zero]

  have hredB_alg : ∀ f : K[X], redB (algebraMap K[X] B f) = algebraMap κ (TAlg Tκ) (mkP f) := by
    intro f
    ext1; funext k
    rw [show (redB (algebraMap K[X] B f)).coord k =
        mkP (b.repr (algebraMap K[X] B f) k) from rfl]
    rw [TAlg.algebraMap_coord, Algebra.algebraMap_eq_smul_one, ← hb0, map_smul,
      b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Pi.single_apply, smul_eq_mul]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero, map_zero]
  have hredC_alg : ∀ r : Rl, redC (algebraMap Rl Cl r) = algebraMap κ (TAlg Tκ) (lam r) := by
    intro r
    ext1; funext k
    rw [TAlg.mapHom_coord, TAlg.algebraMap_coord, TAlg.algebraMap_coord, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp

  have hlift : ∀ w : Cl, ∃ z : B, redB z = redC w := by
    intro w
    have hc : ∀ k, ∃ f : K[X], mkP f = lam (w.coord k) := fun k =>
      Ideal.Quotient.mk_surjective (lam (w.coord k))
    choose f hf using hc
    refine ⟨∑ k, f k • b k, ?_⟩
    ext1; funext k
    rw [show (redB (∑ i, f i • b i)).coord k =
        mkP (b.repr (∑ i, f i • b i) k) from rfl]
    rw [repr_sum_smul, TAlg.mapHom_coord, hf]

  obtain ⟨yB, hyB⟩ := hmono
  have hyc : ∀ k, ∃ r : Rl, lam r = (redB yB).coord k := fun k => hlams _
  choose ry hry using hyc
  let yC : Cl := TAlg.mk ry
  have hyC : redC yC = redB yB := by
    ext1; funext k; rw [TAlg.mapHom_coord]; exact hry k
  have hmonoC : ∀ w : Cl, ∃ q : Polynomial Rl,
      w - aeval yC q ∈ (IsLocalRing.maximalIdeal Rl) • (⊤ : Submodule Rl Cl) := by
    intro w
    obtain ⟨z, hz⟩ := hlift w
    obtain ⟨q₀, hq₀⟩ := hyB z
    obtain ⟨q, hq⟩ := Polynomial.map_surjective lam hlams (q₀.map mkP)
    refine ⟨q, ?_⟩

    have h1 : redB (aeval yB q₀) = (q₀.map mkP).eval₂ (algebraMap κ (TAlg Tκ)) (redB yB) := by
      rw [aeval_def, hom_eval₂, eval₂_map]
      congr 1
      exact RingHom.ext fun f => hredB_alg f
    have h2 : redC (aeval yC q) = (q₀.map mkP).eval₂ (algebraMap κ (TAlg Tκ)) (redB yB) := by
      rw [aeval_def, hom_eval₂, ← hq, eval₂_map, hyC]
      congr 1
      exact RingHom.ext fun r => hredC_alg r
    have h3 : redB (z - aeval yB q₀) = 0 := hredB_P _ hq₀
    have h4 : redC (w - aeval yC q) = 0 := by
      rw [map_sub, ← hz, h2, ← h1, ← map_sub, h3]

    have h5 : ∀ k, (w - aeval yC q).coord k ∈ IsLocalRing.maximalIdeal Rl := by
      intro k
      apply hlamker
      have := congrArg (fun x : TAlg Tκ => x.coord k) h4
      simp only [TAlg.mapHom_coord, TAlg.coord_zero, Pi.zero_apply] at this
      exact this
    rw [TAlg.eq_sum_coord_smul_basis Tl (w - aeval yC q)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (h5 k) Submodule.mem_top

  obtain ⟨C', instC', instAlg, e', σ, he'0, hσalg, hσe⟩ :=
    Aux3.lift_basis R'l Rl πl hπls Cl
      (Fin (n + 1)) e 0 he0 ⟨yC, hmonoC⟩

  let T'' : Table R'l n := tableOfBasis e' he'0
  have hT''γ : ∀ i j k, T''.γ i j k = e'.repr (e' i * e' j) k := fun i j k => rfl
  have hσ_smul : ∀ (r : R'l) (x : C'), σ (r • x) = πl r • σ x := fun r x => by
    rw [Algebra.smul_def, map_mul, hσalg, ← Algebra.smul_def]

  have hπγ'' : ∀ i j k, πl (T''.γ i j k) = Tl.γ i j k := by
    intro i j k
    have h1 : e' i * e' j = ∑ m, T''.γ i j m • e' m := by
      conv_lhs => rw [← e'.sum_repr (e' i * e' j)]
      rfl
    have h2 : e i * e j = ∑ m, Tl.γ i j m • e m := by
      have := TAlg.eq_sum_coord_smul_basis Tl (e i * e j)
      rw [this]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [TAlg.basis_mul_basis_coord]
    have h3 : σ (e' i * e' j) = ∑ m, πl (T''.γ i j m) • e m := by
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hσ_smul, hσe]
    rw [map_mul, hσe, hσe, h2] at h3
    have := congrArg (fun x => e.repr x k) h3
    simp only [repr_sum_smul] at this
    exact this.symm

  let γ'l : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → R'l := fun i j k =>
    algebraMap A'[X] R'l (γ' i j k)
  have hδ : ∀ i j k, ∃ z : R'l, T''.γ i j k - γ'l i j k = εl * z := by
    intro i j k
    apply hkerl
    rw [map_sub, hπγ'', hπl_alg]
    change algebraMap A[X] Rl (γ i j k) - algebraMap A[X] Rl ((γ' i j k).map π) = 0
    rw [hγ'π, sub_self]
  choose zδ hzδ using hδ
  let φl : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → R'l := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else if i ≤ j then zδ i j k else zδ j i k
  have hγ'l1 : ∀ j k, γ'l 0 j k = if j = k then 1 else 0 := fun j k => by
    change algebraMap A'[X] R'l (γ' 0 j k) = _
    rw [hγ'1]; split_ifs <;> simp
  have hδ0 : ∀ j k, T''.γ 0 j k - γ'l 0 j k = 0 := fun j k => by
    rw [T''.unit, hγ'l1, sub_self]
  have hφl : ∀ i j k, T''.γ i j k - γ'l i j k = εl * φl i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [φl, if_pos h, mul_zero]
      rcases h with rfl | rfl
      · exact hδ0 j k
      · rw [T''.comm, show γ'l i 0 k = γ'l 0 i k from by
          change algebraMap A'[X] R'l (γ' i 0 k) = algebraMap A'[X] R'l (γ' 0 i k)
          rw [hγ'c]]
        exact hδ0 i k
    · simp only [φl, if_neg h]
      split_ifs with hij
      · exact hzδ i j k
      · rw [T''.comm, show γ'l i j k = γ'l j i k from by
          change algebraMap A'[X] R'l (γ' i j k) = algebraMap A'[X] R'l (γ' j i k)
          rw [hγ'c]]
        exact hzδ j i k
  have hφl0 : ∀ j k, φl 0 j k = 0 := fun j k => by simp [φl]
  have hφlc : ∀ i j k, φl i j k = φl j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [φl, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [φl, if_neg h, if_neg h']
      by_cases hij : i ≤ j
      · by_cases hji : j ≤ i
        · have : i = j := le_antisymm hij hji
          subst this; rfl
        · rw [if_pos hij, if_neg hji]
      · have hji : j ≤ i := le_of_not_ge hij
        rw [if_neg hij, if_pos hji]

  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite Q'.primeCompl
    (fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) => φl p.1 p.2.1 p.2.2)
  choose hint hhint using fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) => hu p
  let g : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else if i ≤ j then hint (i, j, k) else hint (j, i, k)
  have hg : ∀ i j k, algebraMap A'[X] R'l (g i j k) = algebraMap A'[X] R'l u * φl i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [g, φl, if_pos h, map_zero, mul_zero]
    · simp only [g, if_neg h]
      split_ifs with hij
      · rw [hhint (i, j, k), Algebra.smul_def]
      · rw [hhint (j, i, k), Algebra.smul_def, hφlc i j k]
  have hg0 : ∀ j k, g 0 j k = 0 := fun j k => by simp [g]
  have hgc : ∀ i j k, g i j k = g j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [g, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [g, if_neg h, if_neg h']
      by_cases hij : i ≤ j
      · by_cases hji : j ≤ i
        · have : i = j := le_antisymm hij hji
          subst this; rfl
        · rw [if_pos hij, if_neg hji]
      · have hji : j ≤ i := le_of_not_ge hij
        rw [if_neg hij, if_pos hji]

  let Γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    (u : A'[X]) * γ' i j k + C ε * g i j k
  have hΓ : ∀ i j k, algebraMap A'[X] R'l (Γ i j k) = algebraMap A'[X] R'l u * T''.γ i j k := by
    intro i j k
    have h1 : T''.γ i j k = γ'l i j k + εl * φl i j k := by rw [← hφl]; ring
    change algebraMap A'[X] R'l ((u : A'[X]) * γ' i j k + C ε * g i j k) = _
    rw [h1, map_add, map_mul, map_mul, hg]
    ring

  have hassocΓ : ∀ i j l m, algebraMap A'[X] R'l
      ((∑ k, Γ i j k * Γ k l m) - ∑ k, Γ j l k * Γ i k m) = 0 := by
    intro i j l m
    simp only [map_sub, map_sum, map_mul, hΓ]
    have := T''.assoc i j l m
    have e1 : ∑ k, algebraMap A'[X] R'l ↑u * T''.γ i j k * (algebraMap A'[X] R'l ↑u * T''.γ k l m) =
        (algebraMap A'[X] R'l ↑u) ^ 2 * ∑ k, T''.γ i j k * T''.γ k l m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, algebraMap A'[X] R'l ↑u * T''.γ j l k * (algebraMap A'[X] R'l ↑u * T''.γ i k m) =
        (algebraMap A'[X] R'l ↑u) ^ 2 * ∑ k, T''.γ j l k * T''.γ i k m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2, this, sub_self]

  let E : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    ((∑ k, γ' i j k * g k l m) + ∑ k, g i j k * γ' k l m) -
      ((∑ k, γ' j l k * g i k m) + ∑ k, g j l k * γ' i k m)
  let F : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    (∑ k, g i j k * g k l m) - ∑ k, g j l k * g i k m
  have hexp : ∀ i j l m, (∑ k, Γ i j k * Γ k l m) - (∑ k, Γ j l k * Γ i k m) =
      C ε * ((u : A'[X]) ^ 2 * ac i j l m + (u : A'[X]) * E i j l m + C ε * F i j l m) := by
    intro i j l m
    have hprod : ∀ x y z t : A'[X], ((u : A'[X]) * x + C ε * y) * ((u : A'[X]) * z + C ε * t) =
        (u : A'[X]) ^ 2 * (x * z) + C ε * ((u : A'[X]) * (x * t + y * z) + C ε * (y * t)) := by
      intro x y z t; ring
    have e1 : ∑ k, Γ i j k * Γ k l m = (u : A'[X]) ^ 2 * ∑ k, γ' i j k * γ' k l m +
        C ε * ((u : A'[X]) * ((∑ k, γ' i j k * g k l m) + ∑ k, g i j k * γ' k l m) +
          C ε * ∑ k, g i j k * g k l m) := by
      simp only [Γ, hprod, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    have e2 : ∑ k, Γ j l k * Γ i k m = (u : A'[X]) ^ 2 * ∑ k, γ' j l k * γ' i k m +
        C ε * ((u : A'[X]) * ((∑ k, γ' j l k * g i k m) + ∑ k, g j l k * γ' i k m) +
          C ε * ∑ k, g j l k * g i k m) := by
      simp only [Γ, hprod, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    rw [e1, e2]
    have h3 := hac i j l m
    simp only [E, F]
    linear_combination (u : A'[X]) ^ 2 * h3

  have hW : ∀ i j l m, θX ((u : A'[X]) ^ 2 * ac i j l m + (u : A'[X]) * E i j l m +
      C ε * F i j l m) = 0 := by
    intro i j l m
    apply hannl
    rw [← hexp]
    exact hassocΓ i j l m

  let su : K[X] := θX u
  let gb : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => θX (g i j k)
  have hsu : su ∉ P := by
    intro h
    apply u.2
    change (u : A'[X]) ∈ Q'
    rw [hmemQ']; exact h
  have hsu0 : su ≠ 0 := fun h => hsu (by rw [h]; exact P.zero_mem)
  have hθγ' : ∀ i j k, θX (γ' i j k) = b.repr (b i * b j) k := fun i j k => by
    rw [hθX]; change ((γ' i j k).map π).map ρ = _; rw [hγ'π, hγB]
  refine ⟨su, hsu, gb, fun j k => ?_, fun i j k => ?_, fun i j l m => ?_⟩
  · change θX (g 0 j k) = 0; rw [hg0, map_zero]
  · change θX (g i j k) = θX (g j i k); rw [hgc]
  · have h := hW i j l m
    simp only [map_add, map_mul, map_pow, map_sub, map_sum, hθε, zero_mul, add_zero, hθγ', E]
      at h
    change (∑ k, gb j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * gb k l m) +
        (∑ k, b.repr (b j * b l) k * gb i k m) - (∑ k, gb i j k * b.repr (b k * b l) m) =
      su * (ac i j l m).map (ρ.comp π)
    have ha : (ac i j l m).map (ρ.comp π) = θX (ac i j l m) := rfl
    rw [ha]
    apply mul_left_cancel₀ hsu0
    have h' : su * (su * θX (ac i j l m)) = -(su * (((∑ k, b.repr (b i * b j) k * gb k l m) +
        ∑ k, gb i j k * b.repr (b k * b l) m) - ((∑ k, b.repr (b j * b l) k * gb i k m) +
          ∑ k, gb j l k * b.repr (b i * b k) m))) := by
      have : su ^ 2 * θX (ac i j l m) + su * (((∑ k, b.repr (b i * b j) k * gb k l m) +
        ∑ k, gb i j k * b.repr (b k * b l) m) - ((∑ k, b.repr (b j * b l) k * gb i k m) +
          ∑ k, gb j l k * b.repr (b i * b k) m)) = 0 := h
      linear_combination this
    rw [h']
    ring

end Main

end LocCobSol

end

private theorem local_coboundary
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (P : Ideal K[X]) (hP : P.IsMaximal)
    (hmono : ∃ y : B, ∀ z : B, ∃ q : Polynomial K[X],
      z - aeval y q ∈ P • (⊤ : Submodule K[X] B)) :
    ∃ s : K[X], s ∉ P ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        s * (ac i j l m).map (ρ.comp π) :=
  LocCobSol.main b hb0 A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγB γ' hγ'1 hγ'c hγ'π ac hac P hP
    hmono

end Aux5

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_coboundary_at_infinity_of_smallExtension_of_split.lean`.
namespace Aux6

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable


noncomputable section

namespace InfCobSol


section Twist

variable {S : Type*} [CommRing S] {N : ℕ} (d : Fin (N + 1) → ℕ)

theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → S[X]) (M : ℕ) :
    reflect M (∑ i ∈ s, f i) = ∑ i ∈ s, reflect M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, reflect_add, ih]

def tw (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) :
    Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X] :=
  fun i j k => reflect (D + d i + d j - d k) (Φ i j k)

theorem tw_apply (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (i j k : Fin (N + 1)) :
    tw d D Φ i j k = reflect (D + d i + d j - d k) (Φ i j k) := rfl

variable (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)


include hd0 hd in

theorem reflect_term (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (a b k c t : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d a + d b + d c - d t)) (Φ a b k * Ψ k c t) =
      tw d DΦ Φ a b k * tw d DΨ Ψ k c t := by
  by_cases h1 : d a + d b < d k
  · rw [VΦ a b k h1, zero_mul, reflect_zero, tw_apply, VΦ a b k h1, reflect_zero, zero_mul]
  by_cases h2 : d k + d c < d t
  · rw [VΨ k c t h2, mul_zero, reflect_zero, tw_apply, tw_apply, VΨ k c t h2, reflect_zero,
      mul_zero]
  have hsum : DΦ + DΨ + (d a + d b + d c - d t) =
      (DΦ + d a + d b - d k) + (DΨ + d k + d c - d t) := by omega
  rw [hsum, reflect_mul _ _ (HΦ a b k) (HΨ k c t), tw_apply, tw_apply]

include hd0 hd in

theorem reflect_P1 (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (i j l m : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d i + d j + d l - d m)) (∑ k, Φ i j k * Ψ k l m) =
      ∑ k, tw d DΦ Φ i j k * tw d DΨ Ψ k l m := by
  rw [reflect_sum]
  exact Finset.sum_congr rfl fun k _ => reflect_term d hd0 hd DΦ DΨ Φ Ψ HΦ VΦ HΨ VΨ i j k l m

include hd0 hd in

theorem reflect_P2 (DΦ DΨ : ℕ)
    (Φ Ψ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (HΦ : ∀ i j k, (Φ i j k).natDegree ≤ DΦ + d i + d j - d k)
    (VΦ : ∀ i j k, d i + d j < d k → Φ i j k = 0)
    (HΨ : ∀ i j k, (Ψ i j k).natDegree ≤ DΨ + d i + d j - d k)
    (VΨ : ∀ i j k, d i + d j < d k → Ψ i j k = 0)
    (Ψc : ∀ i j k, Ψ i j k = Ψ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (DΦ + DΨ + (d i + d j + d l - d m)) (∑ k, Φ j l k * Ψ i k m) =
      ∑ k, tw d DΦ Φ j l k * tw d DΨ Ψ i k m := by
  rw [reflect_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hN : d i + d j + d l - d m = d j + d l + d i - d m := by omega
  rw [Ψc i k m, hN, reflect_term d hd0 hd DΦ DΨ Φ Ψ HΦ VΦ HΨ VΨ j l k i m, tw_apply, tw_apply,
    tw_apply, Ψc k i m, Nat.add_right_comm DΨ (d k) (d i)]

def D2 (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j l m : Fin (N + 1)) : S[X] :=
  (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) + (∑ k, γ j l k * φ i k m) -
    (∑ k, φ i j k * γ k l m)

def assoc (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j l m : Fin (N + 1)) : S[X] :=
  (∑ k, γ i j k * γ k l m) - ∑ k, γ j l k * γ i k m

include hd0 hd in

theorem reflect_assoc (Γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Γ i j k).natDegree ≤ 0 + d i + d j - d k)
    (V : ∀ i j k, d i + d j < d k → Γ i j k = 0) (Γc : ∀ i j k, Γ i j k = Γ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (d i + d j + d l - d m) (assoc Γ i j l m) = assoc (tw d 0 Γ) i j l m := by
  have e : d i + d j + d l - d m = 0 + 0 + (d i + d j + d l - d m) := by ring
  rw [assoc, assoc, reflect_sub, e, reflect_P1 d hd0 hd 0 0 Γ Γ H V H V,
    reflect_P2 d hd0 hd 0 0 Γ Γ H V H V Γc]

include hd0 hd in

theorem reflect_D2 (Dφ : ℕ) (Γ φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Γ i j k).natDegree ≤ 0 + d i + d j - d k)
    (V : ∀ i j k, d i + d j < d k → Γ i j k = 0) (Γc : ∀ i j k, Γ i j k = Γ j i k)
    (Hφ : ∀ i j k, (φ i j k).natDegree ≤ Dφ + d i + d j - d k)
    (Vφ : ∀ i j k, d i + d j < d k → φ i j k = 0) (φc : ∀ i j k, φ i j k = φ j i k)
    (i j l m : Fin (N + 1)) :
    reflect (Dφ + (d i + d j + d l - d m)) (D2 Γ φ i j l m) =
      D2 (tw d 0 Γ) (tw d Dφ φ) i j l m := by
  have e1 : Dφ + (d i + d j + d l - d m) = Dφ + 0 + (d i + d j + d l - d m) := by ring
  have e2 : Dφ + (d i + d j + d l - d m) = 0 + Dφ + (d i + d j + d l - d m) := by ring
  have t1 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, φ j l k * Γ i k m) =
      ∑ k, tw d Dφ φ j l k * tw d 0 Γ i k m := by
    rw [e1]; exact reflect_P2 d hd0 hd Dφ 0 φ Γ Hφ Vφ H V Γc i j l m
  have t2 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, Γ i j k * φ k l m) =
      ∑ k, tw d 0 Γ i j k * tw d Dφ φ k l m := by
    rw [e2]; exact reflect_P1 d hd0 hd 0 Dφ Γ φ H V Hφ Vφ i j l m
  have t3 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, Γ j l k * φ i k m) =
      ∑ k, tw d 0 Γ j l k * tw d Dφ φ i k m := by
    rw [e2]; exact reflect_P2 d hd0 hd 0 Dφ Γ φ H V Hφ Vφ φc i j l m
  have t4 : reflect (Dφ + (d i + d j + d l - d m)) (∑ k, φ i j k * Γ k l m) =
      ∑ k, tw d Dφ φ i j k * tw d 0 Γ k l m := by
    rw [e1]; exact reflect_P1 d hd0 hd Dφ 0 φ Γ Hφ Vφ H V i j l m
  rw [D2, D2, reflect_sub, reflect_add, reflect_sub, t1, t2, t3, t4]

theorem tw_map {R₂ : Type*} [CommRing R₂] (f : S →+* R₂) (D : ℕ)
    (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j k : Fin (N + 1)) :
    (tw d D Φ i j k).map f = tw d D (fun i j k => (Φ i j k).map f) i j k := by
  rw [tw_apply, tw_apply, reflect_map]

theorem tw_tw (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X]) (i j k : Fin (N + 1)) :
    tw d 0 (tw d 0 Φ) i j k = Φ i j k := by
  rw [tw_apply, tw_apply, reflect_reflect]

theorem natDegree_tw_le (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (H : ∀ i j k, (Φ i j k).natDegree ≤ D + d i + d j - d k) (i j k : Fin (N + 1)) :
    (tw d D Φ i j k).natDegree ≤ D + d i + d j - d k := by
  rw [tw_apply]
  exact natDegree_reflect_le.trans (max_le le_rfl (H i j k))

theorem tw_unit (hd0 : d 0 = 0) (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (j k : Fin (N + 1)) :
    tw d 0 Φ 0 j k = if j = k then 1 else 0 := by
  rw [tw_apply, h, hd0]
  split_ifs with hjk
  · subst hjk; simp
  · exact reflect_zero

theorem tw_comm (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ i j k, Φ i j k = Φ j i k) (i j k : Fin (N + 1)) : tw d D Φ i j k = tw d D Φ j i k := by
  rw [tw_apply, tw_apply, h, Nat.add_right_comm]

theorem tw_zero_row (D : ℕ) (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h : ∀ j k, Φ 0 j k = 0) (j k : Fin (N + 1)) : tw d D Φ 0 j k = 0 := by
  rw [tw_apply, h, reflect_zero]

end Twist

section HV

variable {S : Type*} [CommRing S] {N : ℕ} (d : Fin (N + 1) → ℕ)
  (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)

include hd0 hd in
theorem H_of_table (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (hdg : ∀ i j k, i ≠ 0 → j ≠ 0 → (Φ i j k).natDegree ≤ d i + d j - d k) (i j k : Fin (N + 1)) :
    (Φ i j k).natDegree ≤ 0 + d i + d j - d k := by
  rw [zero_add]
  by_cases hi : i = 0
  · subst hi; rw [h1]; split_ifs <;> simp
  by_cases hj : j = 0
  · subst hj; rw [hc, h1]; split_ifs <;> simp
  exact hdg i j k hi hj

include hd0 hd in
theorem V_of_table (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = if j = k then 1 else 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (i j k : Fin (N + 1)) (hlt : d i + d j < d k) : Φ i j k = 0 := by
  by_cases hi : i = 0
  · subst hi; rw [h1]; split_ifs with h
    · subst h; rw [hd0] at hlt; omega
    · rfl
  by_cases hj : j = 0
  · subst hj; rw [hc, h1]; split_ifs with h
    · subst h; rw [hd0] at hlt; omega
    · rfl
  have := d_le_two d hd0 hd k; have := one_le_d d hd i hi; have := one_le_d d hd j hj
  omega

include hd0 hd in
theorem V_of_cochain (Φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → S[X])
    (h1 : ∀ j k, Φ 0 j k = 0) (hc : ∀ i j k, Φ i j k = Φ j i k)
    (i j k : Fin (N + 1)) (hlt : d i + d j < d k) : Φ i j k = 0 := by
  by_cases hi : i = 0
  · subst hi; exact h1 j k
  by_cases hj : j = 0
  · subst hj; rw [hc]; exact h1 i k
  have := d_le_two d hd0 hd k; have := one_le_d d hd i hi; have := one_le_d d hd j hj
  omega

end HV

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (τ : Fin (n + 1) → Fin (n + 1) → K) (hτu : IsUnit (Matrix.det (Matrix.of τ)))
    (hτ0 : ∀ j, τ j 0 = 1)
    (hτm : ∀ j i i', i ≠ 0 → i' ≠ 0 →
      τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m) :
    ∃ t : K[X], t ≠ 0 ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
      ∀ i j l m, D2 (fun i j k => b.repr (b i * b j) k) φ i j l m =
        t * (ac i j l m).map (ρ.comp π) := by
  classical

  set γB : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγBdef
  have hγB1 : ∀ j k, γB 0 j k = if j = k then 1 else 0 := fun j k => by
    simp only [hγBdef, hb0, one_mul, b.repr_self, Finsupp.single_apply]
  have hγBc : ∀ i j k, γB i j k = γB j i k := fun i j k => by simp only [hγBdef, mul_comm]
  have hγBa : ∀ i j l m, ∑ k, γB i j k * γB k l m = ∑ k, γB j l k * γB i k m := repr_mul_assoc b
  have HγB := H_of_table d hd0 hd γB hγB1 hγBc hdeg
  have VγB := V_of_table d hd0 hd γB hγB1 hγBc
  have Hγ := H_of_table d hd0 hd γ hγ1 hγc hγd
  have Vγ := V_of_table d hd0 hd γ hγ1 hγc
  have Hγ' := H_of_table d hd0 hd γ' hγ'1 hγ'c hγ'd
  have Vγ' := V_of_table d hd0 hd γ' hγ'1 hγ'c
  let γBt := tw d 0 γB
  let γt := tw d 0 γ
  let γ't := tw d 0 γ'
  let act : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    reflect (d i + d j + d l - d m) (ac i j l m)

  have hγBt1 : ∀ j k, γBt 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γB hγB1
  have hγBtc : ∀ i j k, γBt i j k = γBt j i k := tw_comm d 0 γB hγBc
  have hγBta : ∀ i j l m, ∑ k, γBt i j k * γBt k l m = ∑ k, γBt j l k * γBt i k m := by
    intro i j l m
    have := reflect_assoc d hd0 hd γB HγB VγB hγBc i j l m
    have h2 : assoc (tw d 0 γB) i j l m = 0 := by
      rw [← this, assoc, hγBa, sub_self, reflect_zero]
    rw [assoc, sub_eq_zero] at h2
    exact h2
  let Tt : Table K[X] n := ⟨γBt, hγBt1, hγBtc, hγBta⟩
  let Bt := TAlg Tt
  let bt : Module.Basis (Fin (n + 1)) K[X] Bt := TAlg.basis Tt
  have hbt0 : bt 0 = 1 := TAlg.basis_zero Tt
  have hbtrepr : ∀ i j k, bt.repr (bt i * bt j) k = γBt i j k := TAlg.repr_basis_mul_basis Tt

  have hγt1 : ∀ j k, γt 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γ hγ1
  have hγtc : ∀ i j k, γt i j k = γt j i k := tw_comm d 0 γ hγc
  have hγta : ∀ i j l m, ∑ k, γt i j k * γt k l m = ∑ k, γt j l k * γt i k m := by
    intro i j l m
    have := reflect_assoc d hd0 hd γ Hγ Vγ hγc i j l m
    have h2 : assoc (tw d 0 γ) i j l m = 0 := by
      rw [← this, assoc, hγa, sub_self, reflect_zero]
    rw [assoc, sub_eq_zero] at h2
    exact h2
  have hγtB : ∀ i j k, (γt i j k).map ρ = bt.repr (bt i * bt j) k := by
    intro i j k
    rw [hbtrepr]
    change (tw d 0 γ i j k).map ρ = tw d 0 γB i j k
    rw [tw_map]
    congr 1
    funext i j k; exact hγB i j k
  have hγ't1 : ∀ j k, γ't 0 j k = if j = k then 1 else 0 := tw_unit d hd0 0 γ' hγ'1
  have hγ'tc : ∀ i j k, γ't i j k = γ't j i k := tw_comm d 0 γ' hγ'c
  have hγ'tπ : ∀ i j k, (γ't i j k).map π = γt i j k := by
    intro i j k
    change (tw d 0 γ' i j k).map π = tw d 0 γ i j k
    rw [tw_map]
    congr 1
    funext i j k; exact hγ'π i j k
  have hact : ∀ i j l m, (∑ k, γ't i j k * γ't k l m) - (∑ k, γ't j l k * γ't i k m) =
      C ε * act i j l m := by
    intro i j l m
    have := reflect_assoc d hd0 hd γ' Hγ' Vγ' hγ'c i j l m
    rw [assoc, assoc] at this
    change (∑ k, tw d 0 γ' i j k * tw d 0 γ' k l m) - (∑ k, tw d 0 γ' j l k * tw d 0 γ' i k m) = _
    rw [← this, hac, reflect_C_mul]

  set c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K :=
    fun x y z => (γB x y z).coeff (d x + d y - d z)
    with hcdef
  have hc0 : ∀ y z, c 0 y z = if y = z then 1 else 0 := by
    intro y z
    simp only [hcdef, hγB1, hd0, zero_add]
    split_ifs with h
    · subst h; simp
    · simp
  have hcc : ∀ x y z, c x y z = c y x z := fun x y z => by
    simp only [hcdef, hγBc x y z, Nat.add_comm (d x) (d y)]
  have hτm' : ∀ j i i', τ j i * τ j i' = ∑ k, c i i' k * τ j k := by
    intro j i i'
    by_cases hi : i = 0
    · subst hi
      rw [hτ0, one_mul]
      simp only [hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hi' : i' = 0
    · subst hi'
      rw [hτ0, mul_one]
      simp only [hcc i 0, hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    exact hτm j i i' hi hi'
  let TD : Table K n := Tt.map (Polynomial.constantCoeff : K[X] →+* K)
  have hTD : ∀ i j k, TD.γ i j k = c i j k := by
    intro i j k
    change ((tw d 0 γB i j k)).coeff 0 = (γB i j k).coeff (d i + d j - d k)
    rw [tw_apply, coeff_reflect, revAt_zero, zero_add]
  let D := TAlg TD
  let redD : Bt →+* D := TAlg.mapHom Tt TD Polynomial.constantCoeff (fun _ _ _ => rfl)

  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of τ with hTdef
  let χf : D → (Fin (n + 1) → K) := fun x j => ∑ i, x.coord i * τ j i
  have hχmul : ∀ x y, χf (x * y) = χf x * χf y := by
    intro x y; funext j
    change ∑ m, (cst TD.γ x.coord y.coord m) * τ j m =
      (∑ i, x.coord i * τ j i) * ∑ k, y.coord k * τ j k
    simp only [cst_apply, hTD, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show x.coord i * τ j i * (y.coord k * τ j k) =
        x.coord i * y.coord k * (τ j i * τ j k) by ring,
      hτm' j i k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  let χ : D →+* (Fin (n + 1) → K) :=
    { toFun := χf
      map_one' := by
        funext j
        change ∑ i, (Pi.single 0 1 : Fin (n + 1) → K) i * τ j i = 1
        rw [Finset.sum_eq_single 0]
        · simp [hτ0]
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      map_mul' := hχmul
      map_zero' := by
        funext j
        change ∑ i, (0 : D).coord i * τ j i = 0
        simp [TAlg.coord_zero]
      map_add' := fun x y => by
        funext j
        change ∑ i, (x + y).coord i * τ j i = (∑ i, x.coord i * τ j i) + ∑ i, y.coord i * τ j i
        rw [TAlg.coord_add]
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib] }
  have hχ : ∀ x j, χ x j = ∑ i, x.coord i * τ j i := fun x j => rfl
  have hχT : ∀ x, χ x = T.mulVec x.coord := by
    intro x; funext j
    rw [hχ, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hTdef, Matrix.of_apply, mul_comm]
  have hχinj : Function.Injective χ := by
    intro x y hxy
    ext1
    have h1 : T.mulVec x.coord = T.mulVec y.coord := by rw [← hχT, ← hχT, hxy]
    have h2 := congrArg (T⁻¹.mulVec) h1
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hτu,
      Matrix.one_mulVec, Matrix.one_mulVec] at h2

  let aK : Fin (n + 1) → K := fun i => Infinite.natEmbedding K i
  have haK : Function.Injective aK := fun i j h =>
    Fin.ext ((Infinite.natEmbedding K).injective h)
  let yv : Fin (n + 1) → K := T⁻¹.mulVec aK
  have hyv : T.mulVec yv = aK := by
    change T.mulVec (T⁻¹.mulVec aK) = aK
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hτu, Matrix.one_mulVec]
  let y : Bt := TAlg.mk fun i => C (yv i)
  have hredy : redD y = TAlg.mk yv := by
    ext1; funext i
    rw [show (redD y).coord i = Polynomial.constantCoeff (y.coord i) from rfl]
    change Polynomial.constantCoeff (C (yv i)) = yv i
    rw [Polynomial.constantCoeff_apply, coeff_C_zero]
  have hχy : χ (redD y) = aK := by rw [hχT, hredy, ← hyv]

  have hscal : χ.comp (redD.comp ((algebraMap K[X] Bt).comp C)) =
      algebraMap K (Fin (n + 1) → K) := by
    refine RingHom.ext fun c0 => funext fun j => ?_
    change ∑ i, Polynomial.constantCoeff ((algebraMap K[X] Bt (C c0)).coord i) * τ j i = c0
    rw [TAlg.algebraMap_coord, Finset.sum_eq_single 0]
    · rw [Pi.single_eq_same, Polynomial.constantCoeff_apply, coeff_C_zero, hτ0, mul_one]
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPmax : (Ideal.span {(X : K[X])}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X

  have hmonoBt : ∃ y0 : Bt, ∀ z : Bt, ∃ q : Polynomial K[X],
      z - aeval y0 q ∈ (Ideal.span {(X : K[X])}) • (⊤ : Submodule K[X] Bt) := by
    refine ⟨y, fun z => ?_⟩
    let r : Fin (n + 1) → K := χ (redD z)
    let q₀ : K[X] := Lagrange.interpolate Finset.univ aK r
    refine ⟨q₀.map C, ?_⟩
    have hq₀ : ∀ j, q₀.eval (aK j) = r j := fun j =>
      Lagrange.eval_interpolate_at_node r haK.injOn (Finset.mem_univ j)
    have hev : ∀ (x : Fin (n + 1) → K) (j : Fin (n + 1)),
        (eval₂ (algebraMap K (Fin (n + 1) → K)) x q₀) j = q₀.eval (x j) := by
      intro x j
      have := hom_eval₂ q₀ (algebraMap K (Fin (n + 1) → K)) (Pi.evalRingHom (fun _ => K) j) x
      rw [Pi.evalRingHom_apply] at this
      rw [this]
      rfl
    have h1 : χ (redD (aeval y (q₀.map C))) = χ (redD z) := by
      rw [aeval_def, eval₂_map, hom_eval₂, hom_eval₂, hscal, hχy]
      funext j
      rw [hev, hq₀]
    have h2 : redD (z - aeval y (q₀.map C)) = 0 :=
      hχinj (by rw [map_sub, map_sub, h1, sub_self, map_zero])
    have h3 : ∀ k, (z - aeval y (q₀.map C)).coord k ∈ Ideal.span {(X : K[X])} := by
      intro k
      rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      have := congrArg (fun x : D => x.coord k) h2
      simp only [TAlg.mapHom_coord, TAlg.coord_zero, Pi.zero_apply,
        Polynomial.constantCoeff_apply] at this
      exact this
    rw [TAlg.eq_sum_coord_smul_basis Tt (z - aeval y (q₀.map C))]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (h3 k) Submodule.mem_top

  obtain ⟨s, hs, φt, hφt1, hφtc, hφtD⟩ :=
    Aux5.local_coboundary K n Bt bt hbt0
      A' A π hπ ε hker ρ hρ hann γt hγt1 hγtc hγta hγtB γ't hγ't1 hγ'tc hγ'tπ act hact
      (Ideal.span {(X : K[X])}) hPmax hmonoBt
  have hφtD' : ∀ i j l m, D2 γBt φt i j l m = s * (act i j l m).map (ρ.comp π) := by
    intro i j l m
    rw [← hφtD i j l m, D2]
    simp only [hbtrepr]

  let Dφ : ℕ := (Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) =>
    (φt p.1 p.2.1 p.2.2).natDegree) ⊔ s.natDegree
  have hDφ : ∀ i j k, (φt i j k).natDegree ≤ Dφ := fun i j k =>
    le_sup_of_le_left (Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) =>
      (φt p.1 p.2.1 p.2.2).natDegree) (Finset.mem_univ (i, j, k)))
  have hDs : s.natDegree ≤ Dφ := le_sup_right
  have Vφt := V_of_cochain d hd0 hd φt hφt1 hφtc
  have Hφt : ∀ i j k, (φt i j k).natDegree ≤ Dφ + d i + d j - d k := by
    intro i j k
    by_cases h : d i + d j < d k
    · rw [Vφt i j k h, natDegree_zero]; exact Nat.zero_le _
    · exact (hDφ i j k).trans (by omega)
  have HγBt : ∀ i j k, (γBt i j k).natDegree ≤ 0 + d i + d j - d k := natDegree_tw_le d 0 γB HγB
  have VγBt : ∀ i j k, d i + d j < d k → γBt i j k = 0 := fun i j k h => by
    change tw d 0 γB i j k = 0
    rw [tw_apply, VγB i j k h, reflect_zero]
  let φ := tw d Dφ φt
  let t := reflect Dφ s
  have hs0 : s.coeff 0 ≠ 0 := fun h =>
    hs (Ideal.mem_span_singleton.2 (Polynomial.X_dvd_iff.2 h))
  have htcoeff : t.coeff Dφ = s.coeff 0 := by
    change (reflect Dφ s).coeff Dφ = _
    rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self]
  have ht0 : t ≠ 0 := fun h => hs0 (by rw [← htcoeff, h, coeff_zero])
  have htdeg : t.natDegree = Dφ :=
    le_antisymm (natDegree_reflect_le.trans (max_le le_rfl hDs))
      (le_natDegree_of_ne_zero (by rw [htcoeff]; exact hs0))
  have hφD2 : ∀ i j l m, D2 γB φ i j l m = t * (ac i j l m).map (ρ.comp π) := by
    intro i j l m
    have h := congrArg (reflect (Dφ + (d i + d j + d l - d m))) (hφtD' i j l m)
    rw [reflect_D2 d hd0 hd Dφ γBt φt HγBt VγBt hγBtc Hφt Vφt hφtc] at h
    have htw : tw d 0 γBt = γB := by
      funext i j k; exact tw_tw d γB i j k
    rw [htw] at h
    change D2 γB (tw d Dφ φt) i j l m = reflect Dφ s * (ac i j l m).map (ρ.comp π)
    rw [h]
    change reflect (Dφ + (d i + d j + d l - d m))
      (s * (reflect (d i + d j + d l - d m) (ac i j l m)).map (ρ.comp π)) = _
    have hdeg2 : ((reflect (d i + d j + d l - d m) (ac i j l m)).map (ρ.comp π)).natDegree ≤
        d i + d j + d l - d m := by
      rw [← reflect_map]
      exact natDegree_reflect_le.trans (max_le le_rfl (natDegree_map_le.trans (hacd i j l m)))
    rw [reflect_mul _ _ hDs hdeg2, ← reflect_map, reflect_reflect]
  refine ⟨t, ht0, φ, fun j k => tw_zero_row d Dφ φt hφt1 j k,
    fun i j k => tw_comm d Dφ φt hφtc i j k,
    fun i j k hi hj => ?_, hφD2⟩
  rw [htdeg]
  exact natDegree_tw_le d Dφ φt Hφt i j k

end Main

end InfCobSol

end

private theorem coboundary_infinity
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0)
    (hγ'c : ∀ i j k, γ' i j k = γ' j i k)
    (hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k)
    (hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k)
    (ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X])
    (hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      Polynomial.C ε * ac i j l m)
    (hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m) :
    ∃ t : K[X], t ≠ 0 ∧ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
      ∀ i j l m, (∑ k, φ j l k * b.repr (b i * b k) m) - (∑ k, b.repr (b i * b j) k * φ k l m) +
          (∑ k, b.repr (b j * b l) k * φ i k m) - (∑ k, φ i j k * b.repr (b k * b l) m) =
        t * (ac i j l m).map (ρ.comp π) := by
  obtain ⟨τ, hτu, hτ0, hτm⟩ := hinf
  exact InfCobSol.main b d hb0 hd0 hd hdeg τ hτu hτ0 hτm A' A π hπ ε hker ρ hρ hann γ hγ1 hγc
    hγa hγd
    hγB γ' hγ'1 hγ'c hγ'π hγ'd ac hac hacd

end Aux6

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_mul_eq_hochschild_coboundary_of_discr_ne_zero.lean`.
namespace Aux7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable
open scoped nonZeroDivisors


noncomputable section

namespace GenH2Sol

section Coord

variable {R : Type*} [CommRing R] {N : ℕ}


theorem D1_neg (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (-lam) i j m = -D1 γ lam i j m := by
  have := D1_smul γ (-1) lam i j m
  simpa using this

theorem D1_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) :
    f (D1 γ lam i j m) = D1 (fun i j k => f (γ i j k)) (fun i m => f (lam i m)) i j m := by
  simp only [D1, map_add, map_sub, map_sum, map_mul]

theorem D2_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    f (D2 γ φ i j l m) = D2 (fun i j k => f (γ i j k)) (fun i j k => f (φ i j k)) i j l m := by
  simp only [D2, map_add, map_sub, map_sum, map_mul]

theorem hd2_expand (γ φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)
    (X Y Z : Fin (N + 1) → R) (s : Fin (N + 1)) :
    cst γ X (cst φ Y Z) s - cst φ (cst γ X Y) Z s + cst φ X (cst γ Y Z) s -
        cst γ (cst φ X Y) Z s =
      ∑ k, ∑ l, ∑ t, X k * Y l * Z t * D2 γ φ k l t s := by
  simp only [cst_cst_left, cst_cst_right, D2, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

end Coord

section Based

variable {L : Type*} [Field L] {F : Type*} [CommRing F] [Algebra L F] {N : ℕ}
  (bF : Module.Basis (Fin (N + 1)) L F)
  (γL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L)
  (hγL : ∀ i j m, bF.repr (bF i * bF j) m = γL i j m)


theorem repr_basis_eq_single (i : Fin (N + 1)) :
    (fun k => bF.repr (bF i) k) = (Pi.single i 1 : Fin (N + 1) → L) := by
  funext k
  rw [bF.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

include hγL in
theorem repr_mul (x y : F) (m : Fin (N + 1)) :
    bF.repr (x * y) m = cst γL (fun i => bF.repr x i) (fun j => bF.repr y j) m := by
  have hx : x = ∑ i, bF.repr x i • bF i := (bF.sum_repr x).symm
  have hy : y = ∑ j, bF.repr y j • bF j := (bF.sum_repr y).symm
  conv_lhs => rw [hx, hy, Finset.sum_mul_sum]
  rw [map_sum, Finsupp.finsetSum_apply, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, hγL, smul_eq_mul]

def Ψf (ψL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L) (x y : F) : F :=
  ∑ m, cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) m • bF m

variable (ψL : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → L)

theorem Ψf_repr (x y : F) (m : Fin (N + 1)) :
    bF.repr (Ψf bF ψL x y) m = cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) m :=
  repr_sum_smul bF _ m

theorem Ψf_add_left (x₁ x₂ y : F) : Ψf bF ψL (x₁ + x₂) y = Ψf bF ψL x₁ y + Ψf bF ψL x₂ y := by
  unfold Ψf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← add_smul]
  congr 1
  simp only [cst_apply, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Ψf_smul_left (c : L) (x y : F) : Ψf bF ψL (c • x) y = c • Ψf bF ψL x y := by
  unfold Ψf
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul]
  congr 1
  simp only [cst_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem Ψf_symm (hψLc : ∀ i j k, ψL i j k = ψL j i k) (x y : F) :
    Ψf bF ψL x y = Ψf bF ψL y x := by
  unfold Ψf
  rw [cst_comm_of ψL hψLc (fun i => bF.repr x i) (fun j => bF.repr y j)]

def ΨL (hψLc : ∀ i j k, ψL i j k = ψL j i k) : F →ₗ[L] F →ₗ[L] F :=
  LinearMap.mk₂ L (Ψf bF ψL) (Ψf_add_left bF ψL) (Ψf_smul_left bF ψL)
    (fun x y₁ y₂ => by
      rw [Ψf_symm bF ψL hψLc, Ψf_add_left, Ψf_symm bF ψL hψLc y₁, Ψf_symm bF ψL hψLc y₂])
    (fun c x y => by rw [Ψf_symm bF ψL hψLc, Ψf_smul_left, Ψf_symm bF ψL hψLc])

theorem ΨL_apply (hψLc : ∀ i j k, ψL i j k = ψL j i k) (x y : F) :
    ΨL bF ψL hψLc x y = Ψf bF ψL x y := rfl

theorem ΨL_one (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hone : bF 0 = 1)
    (hψL1 : ∀ j k, ψL 0 j k = 0) (y : F) : ΨL bF ψL hψLc 1 y = 0 := by
  apply bF.repr.injective
  ext m
  rw [ΨL_apply, Ψf_repr, map_zero, Finsupp.zero_apply, ← hone, repr_basis_eq_single,
    cst_single_left]
  exact Finset.sum_eq_zero fun q _ => by rw [hψL1, mul_zero]

include hγL in
theorem ΨL_coc (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hγLc : ∀ i j k, γL i j k = γL j i k)
    (hD2 : ∀ i j l m, D2 γL ψL i j l m = 0) (x y z : F) :
    x • ΨL bF ψL hψLc y z - ΨL bF ψL hψLc (x * y) z + ΨL bF ψL hψLc x (y * z) -
      z • ΨL bF ψL hψLc x y = 0 := by
  apply bF.repr.injective
  ext s
  simp only [smul_eq_mul, map_sub, map_add, map_zero, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.zero_apply, ΨL_apply]
  rw [repr_mul bF γL hγL, repr_mul bF γL hγL, Ψf_repr, Ψf_repr]
  have e1 : (fun j => bF.repr (Ψf bF ψL y z) j) =
      cst ψL (fun i => bF.repr y i) (fun j => bF.repr z j) := funext fun j => Ψf_repr bF ψL y z j
  have e2 : (fun i => bF.repr (x * y) i) = cst γL (fun i => bF.repr x i) (fun j => bF.repr y j) :=
    funext fun j => repr_mul bF γL hγL x y j
  have e3 : (fun j => bF.repr (y * z) j) = cst γL (fun i => bF.repr y i) (fun j => bF.repr z j) :=
    funext fun j => repr_mul bF γL hγL y z j
  have e4 : (fun j => bF.repr (Ψf bF ψL x y) j) =
      cst ψL (fun i => bF.repr x i) (fun j => bF.repr y j) := funext fun j => Ψf_repr bF ψL x y j
  rw [e1, e2, e3, e4, cst_comm_of γL hγLc (fun i => bF.repr z i), hd2_expand]
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ =>
    Finset.sum_eq_zero fun t _ => by rw [hD2, mul_zero]

include hγL in

theorem key (hψLc : ∀ i j k, ψL i j k = ψL j i k) (hγLc : ∀ i j k, γL i j k = γL j i k)
    (l : F →ₗ[L] F)
    (hl : ∀ x y, ΨL bF ψL hψLc x y = l (x * y) - x • l y - y • l x) (i j m : Fin (N + 1)) :
    ψL i j m = -D1 γL (fun i m => bF.repr (l (bF i)) m) i j m := by
  have h := congrArg (fun w => bF.repr w m) (hl (bF i) (bF j))
  have lhs : bF.repr (ΨL bF ψL hψLc (bF i) (bF j)) m = ψL i j m := by
    rw [ΨL_apply, Ψf_repr, repr_basis_eq_single, repr_basis_eq_single, cst_single_single]
  have hbb : bF i * bF j = ∑ k, γL i j k • bF k := by
    conv_lhs => rw [← bF.sum_repr (bF i * bF j)]
    exact Finset.sum_congr rfl fun k _ => by rw [hγL]
  have t1 : bF.repr (l (bF i * bF j)) m = ∑ k, γL i j k * bF.repr (l (bF k)) m := by
    rw [hbb, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have t2 : bF.repr (bF i • l (bF j)) m = ∑ q, bF.repr (l (bF j)) q * γL i q m := by
    rw [smul_eq_mul, repr_mul bF γL hγL, repr_basis_eq_single, cst_single_left]
  have t3 : bF.repr (bF j • l (bF i)) m = ∑ q, bF.repr (l (bF i)) q * γL q j m := by
    rw [smul_eq_mul, repr_mul bF γL hγL, repr_basis_eq_single, cst_single_left]
    exact Finset.sum_congr rfl fun q _ => by rw [hγLc]
  simp only [map_sub, Finsupp.sub_apply] at h
  rw [lhs, t1, t2, t3] at h
  rw [h, D1]
  ring

end Based

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B]
  [Algebra K[X] B]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, D2 (fun i j k => b.repr (b i * b j) k) ψ i j l m = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = D1 (fun i j k => b.repr (b i * b j) k) lam i j m := by
  classical

  let L := FractionRing K[X]
  let F := FractionRing B
  haveI : Module.Finite K[X] B := Module.Finite.of_basis b
  haveI : Module.Free K[X] B := Module.Free.of_basis b
  have hinjB : Function.Injective (algebraMap K[X] B) := by
    intro f g hfg
    have h1 : ∀ f : K[X], b.repr (algebraMap K[X] B f) 0 = f := fun f => by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [← h1 f, ← h1 g, hfg]
  haveI : FaithfulSMul K[X] B := (faithfulSMul_iff_algebraMap_injective K[X] B).2 hinjB
  haveI : Algebra.IsIntegral K[X] B := inferInstance
  haveI : IsIntegralClosure B K[X] F := IsIntegralClosure.of_isIntegrallyClosed B K[X] F
  haveI : Algebra.IsAlgebraic L F := isAlgebraic_of_isFractionRing (R := K[X]) (S := B) L F
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid B K[X]⁰) F :=
    IsIntegralClosure.isLocalization K[X] L F B
  let bF : Module.Basis (Fin (n + 1)) L F := b.localizationLocalization L K[X]⁰ F
  have hbF : ∀ i, bF i = algebraMap B F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply L K[X]⁰ F b i
  have hbFrepr : ∀ (x : B) (i : Fin (n + 1)), bF.repr (algebraMap B F x) i =
      algebraMap K[X] L (b.repr x i) := fun x i =>
    Module.Basis.localizationLocalization_repr_algebraMap L K[X]⁰ F b x i
  haveI : FiniteDimensional L F := Module.Finite.of_basis bF

  have hdiscL : Algebra.discr L bF ≠ 0 := by
    rw [Algebra.discr_localizationLocalization K[X] K[X]⁰ F b]
    exact fun h => hdisc ((IsFractionRing.injective K[X] L) (by rw [h, map_zero]))
  have hnondeg : (Algebra.traceForm L F).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (Algebra.traceForm L F) bF
    rw [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def]
    exact hdiscL
  haveI : Algebra.IsSeparable L F := ((traceForm_nondegenerate_tfae L F).out 3 1).mp hnondeg
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable L F

  let γL : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L := fun i j k =>
    algebraMap K[X] L (b.repr (b i * b j) k)
  let ψL : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → L := fun i j k => algebraMap K[X] L (ψ i j k)
  have hγL : ∀ i j m, bF.repr (bF i * bF j) m = γL i j m := fun i j m => by
    rw [hbF, hbF, ← map_mul, hbFrepr]
  have hγLc : ∀ i j k, γL i j k = γL j i k := fun i j k => by
    change algebraMap K[X] L (b.repr (b i * b j) k) = algebraMap K[X] L (b.repr (b j * b i) k)
    rw [mul_comm]
  have hψLc : ∀ i j k, ψL i j k = ψL j i k := fun i j k => by
    change algebraMap K[X] L (ψ i j k) = algebraMap K[X] L (ψ j i k)
    rw [hψc]
  have hψL1 : ∀ j k, ψL 0 j k = 0 := fun j k => by
    change algebraMap K[X] L (ψ 0 j k) = 0
    rw [hψ1, map_zero]
  have hD2L : ∀ i j l m, D2 γL ψL i j l m = 0 := fun i j l m => by
    have := congrArg (algebraMap K[X] L) (hψa i j l m)
    rw [D2_map, map_zero] at this
    exact this
  have hbF0 : bF 0 = 1 := by rw [hbF, hb0, map_one]

  obtain ⟨l, hl1, hl⟩ :=
    Aux4.formally_smooth_linear L F F
      (ΨL bF ψL hψLc) (fun x y => by rw [ΨL_apply, ΨL_apply, Ψf_symm bF ψL hψLc])
      (ΨL_one bF ψL hψLc hbF0 hψL1) (ΨL_coc bF γL hγL ψL hψLc hγLc hD2L)
  have hkey := key bF γL hγL ψL hψLc hγLc l hl
  set lamL : Fin (n + 1) → Fin (n + 1) → L := fun i m => bF.repr (l (bF i)) m with hlamLdef
  have hlamL0 : ∀ m, lamL 0 m = 0 := fun m => by
    change bF.repr (l (bF 0)) m = 0
    rw [hbF0, hl1, map_zero, Finsupp.zero_apply]

  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite K[X]⁰
    (fun p : Fin (n + 1) × Fin (n + 1) => -lamL p.1 p.2)
  choose lamf hlamf using fun p : Fin (n + 1) × Fin (n + 1) => hu p
  let lam : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lamf (i, m)
  have hlam : ∀ i m, algebraMap K[X] L (lam i m) = (u : K[X]) • (-lamL i m) := fun i m =>
    hlamf (i, m)
  have hu0 : (u : K[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero u
  refine ⟨u, hu0, lam, fun m => ?_, fun i j m => ?_⟩
  · apply IsFractionRing.injective K[X] L
    rw [hlam, hlamL0, neg_zero, smul_zero, map_zero]
  · apply IsFractionRing.injective K[X] L
    rw [map_mul, D1_map]
    have hlam' : (fun i m => algebraMap K[X] L (lam i m)) = ((algebraMap K[X] L u) • (-lamL)) := by
      funext i m
      rw [hlam, Pi.smul_apply, Pi.smul_apply, Pi.neg_apply, Pi.neg_apply, Algebra.smul_def,
        smul_eq_mul]
    rw [hlam', D1_smul, D1_neg]
    change algebraMap K[X] L u * ψL i j m = _
    rw [hkey i j m]

end Main

end GenH2Sol

end

private theorem hochschild_coboundary
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (hb0 : b 0 = 1)
    (hdisc : Algebra.discr K[X] b ≠ 0)
    (ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hψ1 : ∀ j k, ψ 0 j k = 0) (hψc : ∀ i j k, ψ i j k = ψ j i k)
    (hψa : ∀ i j l m, (∑ k, ψ j l k * b.repr (b i * b k) m) -
      (∑ k, b.repr (b i * b j) k * ψ k l m) +
        (∑ k, b.repr (b j * b l) k * ψ i k m) - (∑ k, ψ i j k * b.repr (b k * b l) m) = 0) :
    ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
      ∀ i j m, u * ψ i j m = (∑ k, lam j k * b.repr (b i * b k) m) -
        (∑ k, b.repr (b i * b j) k * lam k m) + (∑ k, lam i k * b.repr (b k * b j) m) :=
  GenH2Sol.main b hb0 hdisc ψ hψ1 hψc hψa

end Aux7

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.lean`.
namespace Aux8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable


noncomputable section

namespace PatchSol

section TableAlgebra


variable {R : Type*} [CommRing R] {N : ℕ}


section Semantics

variable (T : Table R N)

def L1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x : TAlg T) : TAlg T :=
  TAlg.mk fun m => ∑ i, x.coord i * lam i m

def L2 (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) : TAlg T :=
  TAlg.mk (cst φ x.coord y.coord)

def hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) : TAlg T :=
  x * L1 T lam y - L1 T lam (x * y) + L1 T lam x * y

def hd2 (Φ : TAlg T → TAlg T → TAlg T) (x y z : TAlg T) : TAlg T :=
  x * Φ y z - Φ (x * y) z + Φ x (y * z) - Φ x y * z

theorem coord_mul_L1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (x * L1 T lam y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, lam j q * T.γ i q m := by
  rw [TAlg.coord_mul, cst_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [L1, TAlg.coord_mk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem coord_L1_mul (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (L1 T lam (x * y)).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, T.γ i j q * lam q m := by
  simp only [L1, TAlg.coord_mk, TAlg.coord_mul, cst_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sum3_rot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem sum3_rot' (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) :
    ∑ q, ∑ j, ∑ i, f q j i = ∑ i, ∑ j, ∑ q, f q j i := by
  calc ∑ q, ∑ j, ∑ i, f q j i = ∑ j, ∑ q, ∑ i, f q j i := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ q, f q j i := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ q, f q j i := Finset.sum_comm

theorem coord_L1_mul' (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (L1 T lam x * y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * ∑ q, lam i q * T.γ q j m := by
  rw [TAlg.coord_mul, cst_apply]
  simp only [L1, TAlg.coord_mk, Finset.sum_mul, Finset.mul_sum]
  rw [sum3_rot']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun q _ => ?_
  ring

theorem coord_hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (x y : TAlg T) (m : Fin (N + 1)) :
    (hd1 T lam x y).coord m = ∑ i, ∑ j, x.coord i * y.coord j * D1 T.γ lam i j m := by
  simp only [hd1, TAlg.coord_add, TAlg.coord_sub, Pi.add_apply, Pi.sub_apply, coord_mul_L1,
    coord_L1_mul, coord_L1_mul', D1, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem coord_hd2 (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (x y z : TAlg T)
    (s : Fin (N + 1)) :
    (hd2 T (L2 T φ) x y z).coord s =
      ∑ k, ∑ l, ∑ t, x.coord k * y.coord l * z.coord t * D2 T.γ φ k l t s := by
  simp only [hd2, L2, TAlg.coord_add, TAlg.coord_sub, Pi.add_apply, Pi.sub_apply,
    TAlg.coord_mul, cst_cst_left, cst_cst_right, D2, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum3_single (f : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l : Fin (N + 1)) :
    ∑ k, ∑ q, ∑ t, (Pi.single i 1 : Fin (N + 1) → R) k * (Pi.single j 1 : Fin (N + 1) → R) q *
      (Pi.single l 1 : Fin (N + 1) → R) t * f k q t = f i j l := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single l]
  · simp
  · intro t _ ht; simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ l) h
  · intro q _ hq; simp [Pi.single_eq_of_ne hq]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum2_single (f : Fin (N + 1) → Fin (N + 1) → R) (i j : Fin (N + 1)) :
    ∑ k, ∑ q, (Pi.single i 1 : Fin (N + 1) → R) k * (Pi.single j 1 : Fin (N + 1) → R) q * f k q =
      f i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro q _ hq; simp [Pi.single_eq_of_ne hq]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem L2_D1_eq_hd1 (lam : Fin (N + 1) → Fin (N + 1) → R) (y z : TAlg T) :
    L2 T (D1 T.γ lam) y z = hd1 T lam y z := by
  ext1
  funext m
  rw [coord_hd1]
  rfl

theorem hd2_hd1_eq_zero (lam : Fin (N + 1) → Fin (N + 1) → R) (x y z : TAlg T) :
    hd2 T (hd1 T lam) x y z = 0 := by
  simp only [hd2, hd1, mul_assoc]
  ring

theorem D2_D1 (lam : Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 T.γ (D1 T.γ lam) i j l m = 0 := by
  have h := coord_hd2 T (D1 T.γ lam) (TAlg.basis T i) (TAlg.basis T j) (TAlg.basis T l) m
  rw [TAlg.coord_basis, TAlg.coord_basis, TAlg.coord_basis, sum3_single] at h
  rw [← h]
  have hfun : L2 T (D1 T.γ lam) = hd1 T lam := by
    funext y z; exact L2_D1_eq_hd1 T lam y z
  rw [hfun, hd2_hd1_eq_zero, TAlg.coord_zero, Pi.zero_apply]

end Semantics

section Linear

variable (γ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R)

theorem D2_add (φ φ' : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (φ + φ') i j l m = D2 γ φ i j l m + D2 γ φ' i j l m := by
  simp only [D2, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring

theorem D2_smul (c : R) (φ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (c • φ) i j l m = c * D2 γ φ i j l m := by
  simp only [D2, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_sub]
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_ <;>
    exact Finset.sum_congr rfl fun k _ => by ring

theorem D2_zero (i j l m : Fin (N + 1)) :
    D2 γ (0 : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) i j l m = 0 := by
  simp [D2]

theorem D2_sub (φ φ' : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → R) (i j l m : Fin (N + 1)) :
    D2 γ (φ - φ') i j l m = D2 γ φ i j l m - D2 γ φ' i j l m := by
  simp only [D2, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]; ring

theorem D1_add (lam lam' : Fin (N + 1) → Fin (N + 1) → R) (i j m : Fin (N + 1)) :
    D1 γ (lam + lam') i j m = D1 γ lam i j m + D1 γ lam' i j m := by
  simp only [D1, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring


theorem D1_symm (hγc : ∀ i j k, γ i j k = γ j i k) (lam : Fin (N + 1) → Fin (N + 1) → R)
    (i j m : Fin (N + 1)) : D1 γ lam i j m = D1 γ lam j i m := by
  simp only [D1]
  have h1 : ∑ k, lam j k * γ i k m = ∑ k, lam j k * γ k i m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc i k m]
  have h2 : ∑ k, γ i j k * lam k m = ∑ k, γ j i k * lam k m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc i j k]
  have h3 : ∑ k, lam i k * γ k j m = ∑ k, lam i k * γ j k m :=
    Finset.sum_congr rfl fun k _ => by rw [hγc k j m]
  rw [h1, h2, h3]; ring

theorem D1_norm (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (lam : Fin (N + 1) → Fin (N + 1) → R) (hlam : ∀ m, lam 0 m = 0) (j m : Fin (N + 1)) :
    D1 γ lam 0 j m = 0 := by
  simp only [D1, hlam, zero_mul, Finset.sum_const_zero, add_zero, hγ1]
  rw [Finset.sum_eq_single m, Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ m) h

end Linear

end TableAlgebra

section Degrees

variable {K : Type u} [Field K] {n : ℕ} (d : Fin (n + 1) → ℕ)
  (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
  (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
  (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
  (hγc : ∀ i j k, γ i j k = γ j i k)
  (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)


include hγ1 hγc in
theorem natDegree_γ_zero_right (i m : Fin (n + 1)) : (γ i 0 m).natDegree = 0 := by
  rw [hγc, hγ1]; split_ifs <;> simp

include hd0 hd hγ1 hγc hγd in

theorem natDegree_D1_le (E : ℕ) (r : Fin (n + 1) → Fin (n + 1) → K[X]) (hr0 : ∀ m, r 0 m = 0)
    (hr : ∀ i m, r i m = 0 ∨ (r i m).natDegree + 1 ≤ E) (i j m : Fin (n + 1)) (hi : i ≠ 0)
    (hj : j ≠ 0) : (D1 γ r i j m).natDegree ≤ E + d i + d j - d m := by
  have hdm := d_le_two d hd0 hd m
  have hdi := one_le_d d hd i hi
  have hdj := one_le_d d hd j hj
  have hdi2 := d_le_two d hd0 hd i
  have hdj2 := d_le_two d hd0 hd j
  simp only [D1]
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    rcases hr j k with h | h
    · rw [h, zero_mul, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    by_cases hk : k = 0
    · subst hk; rw [natDegree_γ_zero_right γ hγ1 hγc]; omega
    · have := hγd i k m hi hk
      have hdk := d_le_two d hd0 hd k
      omega
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; rw [hr0, mul_zero, natDegree_zero]; exact Nat.zero_le _
    rcases hr k m with h | h
    · rw [h, mul_zero, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    have := hγd i j k hi hj
    have hdk := one_le_d d hd k hk
    omega
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    rcases hr i k with h | h
    · rw [h, zero_mul, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    by_cases hk : k = 0
    · subst hk
      have h0 : (γ 0 j m).natDegree = 0 := by rw [hγ1]; split_ifs <;> simp
      rw [h0]
      omega
    · have := hγd k j m hk hj
      have hdk := d_le_two d hd0 hd k
      omega

end Degrees

section Main

variable {K : Type u} [Field K] {n : ℕ}

def multIdeal (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X]) : Ideal K[X] where
  carrier := {s | ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
    (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧ ∀ i j l m, D2 γ φ i j l m = s * a i j l m}
  zero_mem' := ⟨0, fun _ _ => rfl, fun _ _ _ => rfl, fun i j l m => by rw [D2_zero, zero_mul]⟩
  add_mem' := by
    rintro s s' ⟨φ, h1, h2, h3⟩ ⟨φ', h1', h2', h3'⟩
    refine ⟨φ + φ', fun j k => by simp [h1, h1'], fun i j k => by
      simp only [Pi.add_apply, h2 i j k, h2' i j k], fun i j l m => ?_⟩
    rw [D2_add, h3, h3', add_mul]
  smul_mem' := by
    rintro c s ⟨φ, h1, h2, h3⟩
    refine ⟨c • φ, fun j k => by simp [h1], fun i j k => by
      simp only [Pi.smul_apply, h2 i j k], fun i j l m => ?_⟩
    rw [D2_smul, h3, smul_eq_mul, mul_assoc]

theorem mem_multIdeal (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X]) (s : K[X]) :
    s ∈ multIdeal γ a ↔ ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, D2 γ φ i j l m = s * a i j l m :=
  Iff.rfl

theorem main (d : Fin (n + 1) → ℕ)
    (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧ s ∈ multIdeal γ a)
    (t : K[X]) (ht : t ≠ 0) (φi : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hφi1 : ∀ j k, φi 0 j k = 0) (hφic : ∀ i j k, φi i j k = φi j i k)
    (hφid : ∀ i j k, i ≠ 0 → j ≠ 0 → (φi i j k).natDegree ≤ t.natDegree + d i + d j - d k)
    (hφia : ∀ i j l m, D2 γ φi i j l m = t * a i j l m)
    (hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) → (∀ i j l m, D2 γ ψ i j l m = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m = D1 γ lam i j m) :
    ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ d i + d j - d k) ∧
      ∀ i j l m, D2 γ φ i j l m = a i j l m := by
  let T : Table K[X] n := ⟨γ, hγ1, hγc, hγa⟩

  have htop : multIdeal γ a = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsP, hs⟩ := hloc P hP
    exact hsP (hle hs)
  have h1 : (1 : K[X]) ∈ multIdeal γ a := by rw [htop]; exact Submodule.mem_top
  obtain ⟨φ₀, hφ₀1, hφ₀c, hφ₀a⟩ := (mem_multIdeal γ a 1).1 h1
  simp only [one_mul] at hφ₀a

  let ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := t • φ₀ - φi
  have hψ1 : ∀ j k, ψ 0 j k = 0 := fun j k => by simp [ψ, hφ₀1, hφi1]
  have hψc : ∀ i j k, ψ i j k = ψ j i k := fun i j k => by
    simp only [ψ, Pi.sub_apply, Pi.smul_apply, hφ₀c i j k, hφic i j k]
  have hψa : ∀ i j l m, D2 γ ψ i j l m = 0 := fun i j l m => by
    change D2 γ (t • φ₀ - φi) i j l m = 0
    rw [D2_sub, D2_smul, hφ₀a, hφia, sub_self]

  obtain ⟨u, hu, lam, hlam0, hlam⟩ := hgen ψ hψ1 hψc hψa
  have hut : u * t ≠ 0 := mul_ne_zero hu ht

  let q : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lam i m / (u * t)
  let r : Fin (n + 1) → Fin (n + 1) → K[X] := fun i m => lam i m % (u * t)
  have hqr : ∀ i m, lam i m = (u * t) * q i m + r i m := fun i m =>
    (EuclideanDomain.div_add_mod (lam i m) (u * t)).symm
  have hq0 : ∀ m, q 0 m = 0 := fun m => by simp [q, hlam0]
  have hr0 : ∀ m, r 0 m = 0 := fun m => by simp [r, hlam0]
  have hrdeg : ∀ i m, r i m = 0 ∨ (r i m).natDegree + 1 ≤ (u * t).natDegree := by
    intro i m
    by_cases h : r i m = 0
    · exact Or.inl h
    · right
      have hlt : (r i m).degree < (u * t).degree := EuclideanDomain.mod_lt (lam i m) hut
      have := Polynomial.natDegree_lt_natDegree h hlt
      omega

  let φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => φ₀ i j k - D1 γ q i j k
  have hlamq : lam = (u * t) • q + r := by
    funext i m; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hqr i m

  have hkey : ∀ i j k, (u * t) * φ i j k = u * φi i j k + D1 γ r i j k := by
    intro i j k
    have e1 : u * ψ i j k = D1 γ lam i j k := hlam i j k
    have e2 : D1 γ lam i j k = (u * t) * D1 γ q i j k + D1 γ r i j k := by
      rw [hlamq, D1_add, D1_smul]
    have e3 : u * ψ i j k = u * (t * φ₀ i j k) - u * φi i j k := by
      simp only [ψ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    change (u * t) * (φ₀ i j k - D1 γ q i j k) = u * φi i j k + D1 γ r i j k
    have : (u * t) * φ₀ i j k = u * φi i j k + (u * t) * D1 γ q i j k + D1 γ r i j k := by
      linear_combination e1 + e2 - e3
    rw [mul_sub, this]; ring
  refine ⟨φ, fun j k => ?_, fun i j k => ?_, fun i j k hi hj => ?_, fun i j l m => ?_⟩
  · change φ₀ 0 j k - D1 γ q 0 j k = 0
    rw [hφ₀1, D1_norm γ hγ1 q hq0, sub_zero]
  · change φ₀ i j k - D1 γ q i j k = φ₀ j i k - D1 γ q j i k
    rw [hφ₀c i j k, D1_symm γ hγc q i j k]
  ·
    have hR : ((u * t) * φ i j k).natDegree ≤ (u * t).natDegree + (d i + d j - d k) := by
      rw [hkey]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        have := hφid i j k hi hj
        rw [natDegree_mul hu ht]
        omega
      · have := natDegree_D1_le d hd0 hd γ hγ1 hγc hγd (u * t).natDegree r hr0 hrdeg i j k hi hj
        omega
    by_cases hφ0 : φ i j k = 0
    · rw [hφ0, natDegree_zero]; exact Nat.zero_le _
    · rw [natDegree_mul hut hφ0] at hR
      omega
  · change D2 γ (fun i j k => φ₀ i j k - D1 γ q i j k) i j l m = a i j l m
    have : (fun i j k => φ₀ i j k - D1 γ q i j k) = φ₀ - D1 γ q := by
      funext i j k; rfl
    rw [this, D2_sub, hφ₀a, D2_D1 T q, sub_zero]

end Main

end PatchSol

end

open PatchSol in
private theorem bounded_two_cochain
    (K : Type u) [Field K] (n : ℕ) (d : Fin (n + 1) → ℕ)
    (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = s * a i j l m)
    (hinfty : ∃ t : K[X], t ≠ 0 ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = t * a i j l m)
    (hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) →
      (∀ i j l m, (∑ k, ψ j l k * γ i k m) - (∑ k, γ i j k * ψ k l m) +
          (∑ k, γ j l k * ψ i k m) - (∑ k, ψ i j k * γ k l m) = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m =
          (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)) :
    ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ d i + d j - d k) ∧
      ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
        (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = a i j l m := by
  obtain ⟨t, ht, φi, hφi1, hφic, hφid, hφia⟩ := hinfty
  have hloc' : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧ s ∈ multIdeal γ a := by
    intro P hP
    obtain ⟨s, hs, φ, h1, h2, h3⟩ := hloc P hP
    exact ⟨s, hs, φ, h1, h2, h3⟩
  exact main d hd0 hd γ hγ1 hγc hγa hγd a hloc' t ht φi hφi1 hφic hφid hφia hgen

end Aux8

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension.lean`.
namespace Aux9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable


noncomputable section

namespace SmallExtSol

section LiftPoly

variable {S T : Type*} [CommRing S] [CommRing T]

def liftPoly (s : T → S) (f : T[X]) : S[X] :=
  ∑ t ∈ Finset.range (f.natDegree + 1), C (s (f.coeff t)) * X ^ t

theorem coeff_liftPoly (s : T → S) (hs0 : s 0 = 0) (f : T[X]) (t : ℕ) :
    (liftPoly s f).coeff t = s (f.coeff t) := by
  rw [liftPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases ht : t < f.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by omega), hs0]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

theorem map_liftPoly (f' : S →+* T) (s : T → S) (hs0 : s 0 = 0) (hs : ∀ a, f' (s a) = a)
    (f : T[X]) : (liftPoly s f).map f' = f := by
  ext t
  rw [coeff_map, coeff_liftPoly s hs0, hs]

theorem natDegree_liftPoly_le (s : T → S) (hs0 : s 0 = 0) (f : T[X]) :
    (liftPoly s f).natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_liftPoly s hs0, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast ht), hs0]

open Classical in

def sect0 (f' : S →+* T) (hf : Function.Surjective f') : T → S :=
  fun a => if a = 0 then 0 else Function.surjInv hf a

open Classical in
theorem sect0_zero (f' : S →+* T) (hf : Function.Surjective f') : sect0 f' hf 0 = 0 := by
  simp [sect0]

open Classical in
theorem apply_sect0 (f' : S →+* T) (hf : Function.Surjective f') (a : T) :
    f' (sect0 f' hf a) = a := by
  by_cases h : a = 0
  · simp [sect0, h]
  · rw [sect0, if_neg h]; exact Function.surjInv_eq hf a


def divPoly (ε : S) (g : S[X]) : S[X] :=
  ∑ t ∈ Finset.range (g.natDegree + 1), C (divε ε (g.coeff t)) * X ^ t

theorem coeff_divPoly (ε : S) (g : S[X]) (t : ℕ) : (divPoly ε g).coeff t = divε ε (g.coeff t) := by
  rw [divPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases ht : t < g.natDegree + 1
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by omega), divε_zero]
    intro b hb
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hb)

theorem C_mul_divPoly (ε : S) (g : S[X]) (hg : ∀ t, ε ∣ g.coeff t) : C ε * divPoly ε g = g := by
  ext t
  rw [coeff_C_mul, coeff_divPoly, mul_divε ε _ (hg t)]

theorem natDegree_divPoly_le (ε : S) (g : S[X]) : (divPoly ε g).natDegree ≤ g.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_divPoly, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast ht), divε_zero]

end LiftPoly

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {B : Type v} [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra K[X] B]


theorem main
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hsmall : ∀ a : A', ρ (π a) = 0 → ε * a = 0)
    (hnil : ∀ a : A', ρ (π a) = 0 → IsNilpotent a)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k)
    (hε : ε ≠ 0) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X],
      (∀ j k, γ' 0 j k = if j = k then 1 else 0) ∧
      (∀ i j k, γ' i j k = γ' j i k) ∧
      (∀ i j l m, ∑ k, γ' i j k * γ' k l m = ∑ k, γ' j l k * γ' i k m) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k) ∧
      (∀ i j k, (γ' i j k).map π = γ i j k) := by
  classical

  have hρπ : Function.Surjective (ρ.comp π) := hρ.comp hπ
  have hπε : π ε = 0 := (hker ε).2 (dvd_refl ε)
  have hε2 : ε * ε = 0 := hsmall ε (by rw [hπε, map_zero])
  have hCε2 : (C ε : A'[X]) * C ε = 0 := by rw [← C_mul, hε2, C_0]
  have hunit : ∀ a : A', ρ (π a) ≠ 0 → IsUnit a := by
    intro a ha
    obtain ⟨a₁, ha₁⟩ := hρπ (ρ (π a))⁻¹
    have hm : IsNilpotent (a * a₁ - 1) := hnil _ (by
      rw [map_sub, map_mul, map_sub, map_mul, map_one, map_one]
      change ρ (π a) * (ρ.comp π) a₁ - 1 = 0
      rw [ha₁, mul_inv_cancel₀ ha, sub_self])
    have hu : IsUnit (a * a₁) := by
      have := hm.isUnit_one_add
      rwa [add_sub_cancel] at this
    exact isUnit_of_mul_isUnit_left hu
  have hann : ∀ a : A', ε * a = 0 → ρ (π a) = 0 := by
    intro a ha
    by_contra hne
    obtain ⟨u, rfl⟩ := hunit a hne
    exact hε (by simpa using congrArg (· * (↑u⁻¹ : A')) ha)

  set γB : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγBdef
  have hγB1 : ∀ j k, γB 0 j k = if j = k then 1 else 0 := repr_mul_unit b hb0
  have hγBc : ∀ i j k, γB i j k = γB j i k := fun i j k => by
    simp only [hγBdef, mul_comm]
  have hγBa : ∀ i j l m, ∑ k, γB i j k * γB k l m = ∑ k, γB j l k * γB i k m :=
    repr_mul_assoc b

  let sA : A → A' := sect0 π hπ
  have hsA0 : sA 0 = 0 := sect0_zero π hπ
  have hsA : ∀ a, π (sA a) = a := apply_sect0 π hπ
  let γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 then (if j = k then 1 else 0) else if j = 0 then (if i = k then 1 else 0)
      else liftPoly sA (γ i j k)
  have hγ'1 : ∀ j k, γ' 0 j k = if j = k then 1 else 0 := fun j k => by simp [γ']
  have hγ'1r : ∀ i k, γ' i 0 k = if i = k then 1 else 0 := fun i k => by
    by_cases hi : i = 0
    · subst hi; simp [γ']
    · simp [γ', hi]
  have hγ'c : ∀ i j k, γ' i j k = γ' j i k := by
    intro i j k
    by_cases hi : i = 0
    · subst hi; rw [hγ'1, hγ'1r]
    by_cases hj : j = 0
    · subst hj; rw [hγ'1, hγ'1r]
    simp only [γ', if_neg hi, if_neg hj, hγc i j k]
  have hγ'π : ∀ i j k, (γ' i j k).map π = γ i j k := by
    intro i j k
    by_cases hi : i = 0
    · subst hi; rw [hγ'1, hγ1]; split_ifs <;> simp
    by_cases hj : j = 0
    · subst hj; rw [hγ'1r, hγc, hγ1]; split_ifs <;> simp
    simp only [γ', if_neg hi, if_neg hj]
    exact map_liftPoly π sA hsA0 hsA _
  have hγ'd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k := by
    intro i j k hi hj
    simp only [γ', if_neg hi, if_neg hj]
    exact (natDegree_liftPoly_le sA hsA0 _).trans (hγd i j k hi hj)
  have hγ'd0 : ∀ i j k, i = 0 ∨ j = 0 → (γ' i j k).natDegree = 0 := by
    rintro i j k (rfl | rfl)
    · rw [hγ'1]; split_ifs <;> simp
    · rw [hγ'1r]; split_ifs <;> simp

  have hdle : ∀ m, d m ≤ 2 := fun m => by
    by_cases hm : m = 0
    · rw [hm, hd0]; exact Nat.zero_le _
    · rcases hd m hm with h | h <;> omega
  have hdge : ∀ m, m ≠ 0 → 1 ≤ d m := fun m hm => by rcases hd m hm with h | h <;> omega

  let assoc' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m)
  have hassoc'π : ∀ i j l m, (assoc' i j l m).map π = 0 := by
    intro i j l m
    simp only [assoc', Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, hγ'π]
    rw [hγa, sub_self]

  have hdegprod : ∀ i j k l m, i ≠ 0 → j ≠ 0 → l ≠ 0 →
      (γ' i j k * γ' k l m).natDegree ≤ d i + d j + d l - d m := by
    intro i j k l m hi hj hl
    by_cases hk : k = 0
    · subst hk
      rw [hγ'1]
      split_ifs with hlm
      · subst hlm
        have := hγ'd i j 0 hi hj
        rw [hd0] at this
        rw [mul_one]
        omega
      · rw [mul_zero, natDegree_zero]; exact Nat.zero_le _
    refine natDegree_mul_le.trans ?_
    · have h1 := hγ'd i j k hi hj
      have h2 := hγ'd k l m hk hl
      have := hdle k; have := hdle m; have := hdge k hk; have := hdge l hl
      have := hdge i hi; have := hdge j hj
      omega

  have hU1 : ∀ (j : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, γ' 0 j k * F k = F j := by
    intro j F
    rw [Finset.sum_eq_single j]
    · rw [hγ'1, if_pos rfl, one_mul]
    · intro k _ hk; rw [hγ'1, if_neg (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hU2 : ∀ (m : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, F k * γ' 0 k m = F m := by
    intro m F
    rw [Finset.sum_eq_single m]
    · rw [hγ'1, if_pos rfl, mul_one]
    · intro k _ hk; rw [hγ'1, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  have hU3 : ∀ (i : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, γ' i 0 k * F k = F i := by
    intro i F
    rw [Finset.sum_eq_single i]
    · rw [hγ'1r, if_pos rfl, one_mul]
    · intro k _ hk; rw [hγ'1r, if_neg (Ne.symm hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hU4 : ∀ (m : Fin (n + 1)) (F : Fin (n + 1) → A'[X]), ∑ k, F k * γ' k 0 m = F m := by
    intro m F
    rw [Finset.sum_eq_single m]
    · rw [hγ'1r, if_pos rfl, mul_one]
    · intro k _ hk; rw [hγ'1r, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ m) h
  have hassoc'd : ∀ i j l m, (assoc' i j l m).natDegree ≤ d i + d j + d l - d m := by
    intro i j l m
    by_cases hi : i = 0
    · subst hi
      have : assoc' 0 j l m = 0 := by
        change (∑ k, γ' 0 j k * γ' k l m) - (∑ k, γ' j l k * γ' 0 k m) = 0
        rw [hU1 j (fun k => γ' k l m), hU2 m (fun k => γ' j l k), sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    by_cases hj : j = 0
    · subst hj
      have : assoc' i 0 l m = 0 := by
        change (∑ k, γ' i 0 k * γ' k l m) - (∑ k, γ' 0 l k * γ' i k m) = 0
        rw [hU3 i (fun k => γ' k l m), hU1 l (fun k => γ' i k m), sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    by_cases hl : l = 0
    · subst hl
      have : assoc' i j 0 m = 0 := by
        change (∑ k, γ' i j k * γ' k 0 m) - (∑ k, γ' j 0 k * γ' i k m) = 0
        rw [hU4 m (fun k => γ' i j k), hU3 j (fun k => γ' i k m), hγ'c i j m, sub_self]
      rw [this, natDegree_zero]; exact Nat.zero_le _
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => hdegprod i j k l m hi hj hl
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
      have := hdegprod j l k i m hj hl hi
      have e : d j + d l + d i - d m = d i + d j + d l - d m := by omega
      rw [← e, hγ'c i k m]; exact this

  let ac : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    divPoly ε (assoc' i j l m)
  have hac : ∀ i j l m, (∑ k, γ' i j k * γ' k l m) - (∑ k, γ' j l k * γ' i k m) =
      C ε * ac i j l m := by
    intro i j l m
    change assoc' i j l m = C ε * divPoly ε (assoc' i j l m)
    rw [C_mul_divPoly]
    intro t
    rw [← hker]
    have := congrArg (fun F : A[X] => F.coeff t) (hassoc'π i j l m)
    simpa only [coeff_map, coeff_zero] using this
  have hacd : ∀ i j l m, (ac i j l m).natDegree ≤ d i + d j + d l - d m := fun i j l m =>
    (natDegree_divPoly_le ε _).trans (hassoc'd i j l m)

  haveI : Module.Finite K[X] B := Module.Finite.of_basis b
  haveI : FaithfulSMul K[X] B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro f g hfg
    have h1 : ∀ f : K[X], b.repr (algebraMap K[X] B f) 0 = f := fun f => by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0, map_smul, b.repr_self, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rw [← h1 f, ← h1 g, hfg]
  have hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, (∑ k, φ j l k * γB i k m) - (∑ k, γB i j k * φ k l m) +
          (∑ k, γB j l k * φ i k m) - (∑ k, φ i j k * γB k l m) =
            s * (ac i j l m).map (ρ.comp π) := by
    intro P hP
    have hmono := Aux1.aeval_sub
      K B P hP
    exact Aux5.local_coboundary K n B b hb0
      A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγB γ' hγ'1 hγ'c hγ'π ac hac P hP hmono
  have hinfty := Aux6.coboundary_infinity K n B b
    d hb0 hd0 hd hdeg hinf A' A π hπ ε hker ρ hρ hann γ hγ1 hγc hγa hγd hγB γ' hγ'1 hγ'c hγ'π
    hγ'd ac hac hacd
  have hdisc := Aux2.discr_ne_zero K n B b d hb0 hd0 hd hdeg hinf
  have hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) →
      (∀ i j l m, (∑ k, ψ j l k * γB i k m) - (∑ k, γB i j k * ψ k l m) +
          (∑ k, γB j l k * ψ i k m) - (∑ k, ψ i j k * γB k l m) = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m =
          (∑ k, lam j k * γB i k m) - (∑ k, γB i j k * lam k m) + (∑ k, lam i k * γB k j m) :=
    fun ψ h1 h2 h3 =>
      Aux7.hochschild_coboundary K n B b hb0 hdisc ψ h1
        h2 h3
  obtain ⟨φ, hφ1, hφc, hφd, hφa⟩ :=
    Aux8.bounded_two_cochain K n d hd0 hd γB hγB1 hγBc
      hγBa hdeg (fun i j l m => (ac i j l m).map (ρ.comp π)) hloc hinfty hgen

  let sK : K → A' := sect0 (ρ.comp π) hρπ
  have hsK0 : sK 0 = 0 := sect0_zero _ hρπ
  have hsK : ∀ a, (ρ.comp π) (sK a) = a := apply_sect0 _ hρπ
  let φt : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    if i = 0 ∨ j = 0 then 0 else liftPoly sK (φ i j k)
  have hφc0 : ∀ i k, φ i 0 k = 0 := fun i k => by rw [hφc, hφ1]
  have hφtred : ∀ i j k, (φt i j k).map (ρ.comp π) = φ i j k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · simp only [φt, if_pos h, Polynomial.map_zero]
      rcases h with rfl | rfl
      · rw [hφ1]
      · rw [hφc0]
    · simp only [φt, if_neg h]
      exact map_liftPoly _ sK hsK0 hsK _
  have hφt0 : ∀ j k, φt 0 j k = 0 := fun j k => by simp [φt]
  have hφt0r : ∀ i k, φt i 0 k = 0 := fun i k => by simp [φt]
  have hφtc : ∀ i j k, φt i j k = φt j i k := by
    intro i j k
    by_cases h : i = 0 ∨ j = 0
    · have h' : j = 0 ∨ i = 0 := h.symm
      simp only [φt, if_pos h, if_pos h']
    · have h' : ¬(j = 0 ∨ i = 0) := fun h' => h h'.symm
      simp only [φt, if_neg h, if_neg h', hφc i j k]
  have hφtd : ∀ i j k, i ≠ 0 → j ≠ 0 → (φt i j k).natDegree ≤ d i + d j - d k := by
    intro i j k hi hj
    have h : ¬(i = 0 ∨ j = 0) := by tauto
    simp only [φt, if_neg h]
    exact (natDegree_liftPoly_le sK hsK0 _).trans (hφd i j k hi hj)
  have hγ'red : ∀ i j k, (γ' i j k).map (ρ.comp π) = γB i j k := fun i j k => by
    rw [← Polynomial.map_map, hγ'π, hγB]
  let γ'' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j k =>
    γ' i j k + C ε * φt i j k

  let E : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X] := fun i j l m =>
    ((∑ k, γ' i j k * φt k l m) + ∑ k, φt i j k * γ' k l m) -
      ((∑ k, γ' j l k * φt i k m) + ∑ k, φt j l k * γ' i k m)
  have hexpand : ∀ x y z t : A'[X],
      (x + C ε * y) * (z + C ε * t) = x * z + C ε * (x * t + y * z) := by
    intro x y z t
    linear_combination (y * t) * hCε2
  have hassoc'' : ∀ i j l m,
      (∑ k, γ'' i j k * γ'' k l m) - (∑ k, γ'' j l k * γ'' i k m) =
        C ε * (ac i j l m + E i j l m) := by
    intro i j l m
    have e1 : ∑ k, γ'' i j k * γ'' k l m =
        (∑ k, γ' i j k * γ' k l m) + C ε * ((∑ k, γ' i j k * φt k l m) +
          ∑ k, φt i j k * γ' k l m) := by
      simp only [γ'', hexpand, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    have e2 : ∑ k, γ'' j l k * γ'' i k m =
        (∑ k, γ' j l k * γ' i k m) + C ε * ((∑ k, γ' j l k * φt i k m) +
          ∑ k, φt j l k * γ' i k m) := by
      simp only [γ'', hexpand, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    rw [e1, e2]
    have := hac i j l m
    simp only [E]
    linear_combination this
  have hEred : ∀ i j l m, (ac i j l m + E i j l m).map (ρ.comp π) = 0 := by
    intro i j l m
    have hD := hφa i j l m
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul,
      hγ'red, hφtred, E]
    rw [← hD]
    ring
  have hkill : ∀ i j l m, C ε * (ac i j l m + E i j l m) = 0 := by
    intro i j l m
    ext t
    rw [coeff_C_mul, coeff_zero]
    apply hsmall
    have := congrArg (fun F : K[X] => F.coeff t) (hEred i j l m)
    simpa only [coeff_map, coeff_zero, RingHom.comp_apply] using this
  refine ⟨γ'', fun j k => ?_, fun i j k => ?_, fun i j l m => ?_, fun i j k hi hj => ?_,
    fun i j k => ?_⟩
  · simp only [γ'', hγ'1, hφt0, mul_zero, add_zero]
  · simp only [γ'', hγ'c i j k, hφtc i j k]
  · rw [← sub_eq_zero, hassoc'', hkill]
  · refine (natDegree_add_le _ _).trans (max_le (hγ'd i j k hi hj) ?_)
    exact (natDegree_C_mul_le _ _).trans (hφtd i j k hi hj)
  · simp only [γ'', Polynomial.map_add, Polynomial.map_mul, map_C, hπε, C_0, zero_mul, add_zero,
      hγ'π]

end Main

end SmallExtSol

end

open SmallExtSol in
private theorem lift_normal_form
    (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hsmall : ∀ a : A', ρ (π a) = 0 → ε * a = 0)
    (hnil : ∀ a : A', ρ (π a) = 0 → IsNilpotent a)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X],
      (∀ j k, γ' 0 j k = if j = k then 1 else 0) ∧
      (∀ i j k, γ' i j k = γ' j i k) ∧
      (∀ i j l m, ∑ k, γ' i j k * γ' k l m = ∑ k, γ' j l k * γ' i k m) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k) ∧
      (∀ i j k, (γ' i j k).map π = γ i j k) := by
  by_cases hε : ε = 0
  ·
    subst hε
    have hinj : Function.Injective π := by
      intro x y hxy
      have : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hker, zero_dvd_iff, sub_eq_zero] at this
      exact this
    let e : A' ≃+* A := RingEquiv.ofBijective π ⟨hinj, hπ⟩
    have he : ∀ x, π (e.symm x) = x := fun x => e.apply_symm_apply x
    have hcomp : π.comp (e.symm : A ≃+* A').toRingHom = RingHom.id A := by
      ext x; exact he x
    refine ⟨fun i j k => (γ i j k).map (e.symm : A ≃+* A').toRingHom, fun j k => ?_,
      fun i j k => ?_, fun i j l m => ?_, fun i j k hi hj => ?_, fun i j k => ?_⟩
    · dsimp only
      rw [hγ1]; split_ifs <;> simp
    · dsimp only
      rw [hγc]
    · dsimp only
      have h := congrArg (Polynomial.map (e.symm : A ≃+* A').toRingHom) (hγa i j l m)
      simpa only [Polynomial.map_sum, Polynomial.map_mul] using h
    · dsimp only
      rw [natDegree_map_eq_of_injective (RingEquiv.injective _)]; exact hγd i j k hi hj
    · dsimp only
      rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · exact main b d hb0 hd0 hd hdeg hinf A' A π hπ ε hker ρ hρ hsmall hnil γ hγ1 hγc hγa hγd hγB hε

end Aux9

-- Adapted from
-- `P2M/Sol/S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder.lean`.
namespace Aux10

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open CoordTable


noncomputable section

namespace WittLiftNF


section Witt

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectRing K p]

local notation "𝕎" => WittVector p

def rho (m : ℕ) : TruncatedWittVector p (m + 1) K →+* K :=
  RingHom.liftOfRightInverse (WittVector.truncate (m + 1)) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨WittVector.constantCoeff, by
      intro x hx
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker, WittVector.constantCoeff_apply]
      exact hx 0 (Nat.succ_pos m)⟩

theorem rho_truncate (m : ℕ) (x : 𝕎 K) :
    rho p K m (WittVector.truncate (m + 1) x) = x.coeff 0 :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem rho_apply (m : ℕ) (x : TruncatedWittVector p (m + 1) K) : rho p K m x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 1) K x
  rw [rho_truncate, WittVector.coeff_truncate]
  rfl

theorem rho_surjective (m : ℕ) : Function.Surjective (rho p K m) := fun x =>
  ⟨WittVector.truncate (m + 1) (WittVector.teichmuller p x), by
    rw [rho_truncate, WittVector.teichmuller_coeff_zero]⟩

theorem rho_zero_injective : Function.Injective (rho p K 0) := by
  intro x y h
  rw [rho_apply, rho_apply] at h
  ext i
  have hi : i = 0 := Fin.ext (by have := i.2; simp only [Fin.val_zero]; omega)
  subst hi
  exact h

def rhoZeroEquiv : TruncatedWittVector p 1 K ≃+* K :=
  RingEquiv.ofBijective (rho p K 0) ⟨rho_zero_injective p K, rho_surjective p K 0⟩

theorem rhoZeroEquiv_apply (x : TruncatedWittVector p 1 K) : rhoZeroEquiv p K x = rho p K 0 x := rfl

abbrev piT (m : ℕ) : TruncatedWittVector p (m + 2) K →+* TruncatedWittVector p (m + 1) K :=
  TruncatedWittVector.truncate (Nat.le_succ (m + 1))

theorem piT_surjective (m : ℕ) : Function.Surjective (piT p K m) :=
  TruncatedWittVector.truncate_surjective _

theorem rho_piT (m : ℕ) (a : TruncatedWittVector p (m + 2) K) :
    rho p K m (piT p K m a) = rho p K (m + 1) a := by
  rw [rho_apply, rho_apply, TruncatedWittVector.coeff_truncate]
  rfl

theorem truncate_p_pow_mul_eq_zero (m : ℕ) (D : 𝕎 K) :
    WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 2) * D) = 0 := by
  rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 2)).1
    (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))

theorem piT_eq_zero_iff (m : ℕ) (a : TruncatedWittVector p (m + 2) K) :
    piT p K m a = 0 ↔ ((p : TruncatedWittVector p (m + 2) K) ^ (m + 1)) ∣ a := by
  obtain ⟨A, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K a
  rw [TruncatedWittVector.truncate_wittVector_truncate, ← RingHom.mem_ker,
    WittVector.mem_ker_truncate]
  constructor
  · intro h
    have hA : A ∈ Ideal.span {(p : 𝕎 K) ^ (m + 1)} :=
      (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero A (m + 1)).2 h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hA
    refine ⟨WittVector.truncate (m + 2) c, ?_⟩
    rw [hc, map_mul, map_pow, map_natCast]
  · rintro ⟨c, hc⟩
    obtain ⟨C, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K c
    have hEq : WittVector.truncate (m + 2) A =
        WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 1) * C) := by
      rw [hc, map_mul, map_pow, map_natCast]
    have hk : A - (p : 𝕎 K) ^ (m + 1) * C ∈
        RingHom.ker (WittVector.truncate (p := p) (R := K) (m + 2)) := by
      rw [RingHom.mem_ker, map_sub, hEq, sub_self]
    rw [WittVector.mem_ker_truncate] at hk
    have hk' : ∀ i < m + 1, (A - (p : 𝕎 K) ^ (m + 1) * C).coeff i = 0 :=
      fun i hi => hk i (by omega)
    rw [← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero] at hk'
    intro i hi
    rw [hk' i hi]
    exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).1
      (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)) i hi

theorem exists_eq_p_mul_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) :
    ∃ D : 𝕎 K, a = WittVector.truncate (m + 2) ((p : 𝕎 K) * D) := by
  obtain ⟨A, rfl⟩ := WittVector.truncate_surjective (p := p) (m + 2) K a
  rw [rho_piT, rho_truncate] at h
  have hA : A ∈ Ideal.span {(p : 𝕎 K)} :=
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero A).2 h
  obtain ⟨D, hD⟩ := Ideal.mem_span_singleton.1 hA
  exact ⟨D, by rw [hD]⟩

theorem p_pow_mul_eq_zero_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) :
    (p : TruncatedWittVector p (m + 2) K) ^ (m + 1) * a = 0 := by
  obtain ⟨D, rfl⟩ := exists_eq_p_mul_of_rho_piT_eq_zero p K m a h
  have : (p : TruncatedWittVector p (m + 2) K) ^ (m + 1) =
      WittVector.truncate (m + 2) ((p : 𝕎 K) ^ (m + 1)) := by
    rw [map_pow, map_natCast]
  rw [this, ← map_mul, ← mul_assoc, ← pow_succ]
  exact truncate_p_pow_mul_eq_zero p K m D

theorem isNilpotent_of_rho_piT_eq_zero (m : ℕ) (a : TruncatedWittVector p (m + 2) K)
    (h : rho p K m (piT p K m a) = 0) : IsNilpotent a := by
  obtain ⟨D, rfl⟩ := exists_eq_p_mul_of_rho_piT_eq_zero p K m a h
  refine ⟨m + 2, ?_⟩
  rw [← map_pow, mul_pow]
  exact truncate_p_pow_mul_eq_zero p K m _

theorem truncate_le_refl {m : ℕ} (x : TruncatedWittVector p m K) :
    TruncatedWittVector.truncate (le_refl m) x = x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) m K x
  rw [TruncatedWittVector.truncate_wittVector_truncate]

theorem eq_of_forall_map_truncate {P Q : (𝕎 K)[X]}
    (h : ∀ m : ℕ, P.map (WittVector.truncate (m + 1)) = Q.map (WittVector.truncate (m + 1))) :
    P = Q := by
  ext t c
  have h1 := congrArg
    (fun F : (TruncatedWittVector p (c + 1) K)[X] => (F.coeff t).coeff (Fin.last c))
    (h c)
  simpa only [Polynomial.coeff_map, WittVector.coeff_truncate, Fin.val_last] using h1

theorem constantCoeff_eq_rho_comp_truncate :
    (WittVector.constantCoeff : 𝕎 K →+* K) = (rho p K 0).comp (WittVector.truncate (0 + 1)) := by
  ext x
  rw [RingHom.comp_apply, rho_truncate, WittVector.constantCoeff_apply]

end Witt

section Tower

variable {p : ℕ} [hp : Fact p.Prime] {K : Type u} [Field K] [IsAlgClosed K] [CharP K p]
  {n : ℕ} {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra K[X] B]

local notation "𝕎" => WittVector p

structure Datum (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B] where

  b : Module.Basis (Fin (n + 1)) K[X] B

  d : Fin (n + 1) → ℕ
  hb0 : b 0 = 1
  hd0 : d 0 = 0
  hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2
  hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k
  hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧ (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k

variable (p) (D : Datum K n B)

structure Good (m : ℕ)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X]) :
    Prop where
  unit : ∀ j k, γ 0 j k = if j = k then 1 else 0
  comm : ∀ i j k, γ i j k = γ j i k
  assoc : ∀ i j l m', ∑ k, γ i j k * γ k l m' = ∑ k, γ j l k * γ i k m'
  deg : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ D.d i + D.d j - D.d k
  red : ∀ i j k, (γ i j k).map (rho p K m) = D.b.repr (D.b i * D.b j) k

def table0 : Table ((TruncatedWittVector p 1 K)[X]) n :=
  (tableOfBasis D.b D.hb0).map
    (Polynomial.mapRingHom ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom)

theorem table0_γ (i j k : Fin (n + 1)) :
    (table0 p D).γ i j k =
      (D.b.repr (D.b i * D.b j) k).map
        ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom := rfl

theorem good_table0 : Good p D 0 (table0 p D).γ where
  unit := (table0 p D).unit
  comm := (table0 p D).comm
  assoc := (table0 p D).assoc
  deg i j k hi hj := by
    rw [table0_γ, Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective _)]
    exact D.hdeg i j k hi hj
  red i j k := by
    rw [table0_γ, Polynomial.map_map]
    have : (rho p K 0).comp
        ((rhoZeroEquiv p K).symm : K ≃+* TruncatedWittVector p 1 K).toRingHom = RingHom.id K := by
      ext x
      change rhoZeroEquiv p K ((rhoZeroEquiv p K).symm x) = x
      exact RingEquiv.apply_symm_apply _ _
    rw [this, Polynomial.map_id]

theorem exists_step (m : ℕ)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X])
    (hγ : Good p D m γ) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 2) K)[X],
      Good p D (m + 1) γ' ∧ ∀ i j k, (γ' i j k).map (piT p K m) = γ i j k := by
  obtain ⟨γ', h1, hc, ha, hdg, hred⟩ :=
    Aux9.lift_normal_form K n B D.b D.d
      D.hb0 D.hd0 D.hd D.hdeg D.hinf
      (TruncatedWittVector p (m + 2) K) (TruncatedWittVector p (m + 1) K) (piT p K m)
      (piT_surjective p K m) ((p : TruncatedWittVector p (m + 2) K) ^ (m + 1))
      (piT_eq_zero_iff p K m) (rho p K m) (rho_surjective p K m)
      (p_pow_mul_eq_zero_of_rho_piT_eq_zero p K m) (isNilpotent_of_rho_piT_eq_zero p K m)
      γ hγ.unit hγ.comm hγ.assoc hγ.deg hγ.red
  have hcomp : (rho p K m).comp (piT p K m) = rho p K (m + 1) := by
    ext a; exact rho_piT p K m a
  refine ⟨γ', ⟨h1, hc, ha, hdg, fun i j k => ?_⟩, hred⟩
  rw [← hγ.red i j k, ← hred i j k, Polynomial.map_map, hcomp]

def stage : (m : ℕ) →
    {γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → (TruncatedWittVector p (m + 1) K)[X] //
      Good p D m γ}
  | 0 => ⟨(table0 p D).γ, good_table0 p D⟩
  | m + 1 => ⟨(exists_step p D m (stage m).1 (stage m).2).choose,
      (exists_step p D m (stage m).1 (stage m).2).choose_spec.1⟩

theorem stage_succ_map (m : ℕ) (i j k : Fin (n + 1)) :
    ((stage p D (m + 1)).1 i j k).map (piT p K m) = (stage p D m).1 i j k :=
  (exists_step p D m (stage p D m).1 (stage p D m).2).choose_spec.2 i j k

theorem stage_compat (c : ℕ) : ∀ (e : ℕ) (i j k : Fin (n + 1)),
    ((stage p D (c + e)).1 i j k).map
        (TruncatedWittVector.truncate (by omega : c + 1 ≤ c + e + 1)) = (stage p D c).1 i j k
  | 0, i, j, k => by
    have : TruncatedWittVector.truncate (p := p) (R := K) (le_refl (c + 1)) = RingHom.id _ := by
      ext1 x; exact truncate_le_refl p K x
    change ((stage p D c).1 i j k).map (TruncatedWittVector.truncate (le_refl (c + 1))) = _
    rw [this, Polynomial.map_id]
  | e + 1, i, j, k => by
    have h1 : c + 1 ≤ c + e + 1 := by omega
    have h2 : c + e + 1 ≤ c + e + 2 := by omega
    change ((stage p D (c + e + 1)).1 i j k).map (TruncatedWittVector.truncate (h1.trans h2)) = _
    rw [← TruncatedWittVector.truncate_comp h1 h2, ← Polynomial.map_map]
    have h3 : ((stage p D (c + e + 1)).1 i j k).map (TruncatedWittVector.truncate h2) =
        (stage p D (c + e)).1 i j k := stage_succ_map p D (c + e) i j k
    rw [h3]
    exact stage_compat c e i j k

-- At each truncation length, the map out of `ℕ[X]` that sends `X` to the `t`-th coefficient of
-- the stage's `(i, j, k)` structure constant; at length zero any map is the unique one.
def coeffMaps (i j k : Fin (n + 1)) (t : ℕ) : ∀ m : ℕ, ℕ[X] →+* TruncatedWittVector p m K
  | 0 => Polynomial.eval₂RingHom (Nat.castRingHom _) 0
  | m + 1 => Polynomial.eval₂RingHom (Nat.castRingHom _) (((stage p D m).1 i j k).coeff t)

theorem coeffMaps_compat (i j k : Fin (n + 1)) (t : ℕ) (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) :
    (TruncatedWittVector.truncate hm).comp (coeffMaps p D i j k t m₂) =
      coeffMaps p D i j k t m₁ := by
  refine Polynomial.ringHom_ext' (ext_nat _ _) ?_
  rcases m₁ with _ | c
  · exact TruncatedWittVector.ext fun a => a.elim0
  · obtain ⟨e, rfl⟩ : ∃ e, m₂ = c + e + 1 := ⟨m₂ - c - 1, by omega⟩
    have h := congrArg (fun P => P.coeff t) (stage_compat p D c e i j k)
    simpa [coeffMaps, Polynomial.coeff_map] using h

-- The Witt vector whose truncations are the `t`-th coefficients of the stages, as Mathlib's
-- `WittVector.liftFun` of the compatible maps `coeffMaps` applied to `X`.
def wlim (i j k : Fin (n + 1)) (t : ℕ) : 𝕎 K :=
  WittVector.liftFun (coeffMaps p D i j k t) X

theorem truncate_wlim (m : ℕ) (i j k : Fin (n + 1)) (t : ℕ) :
    WittVector.truncate (m + 1) (wlim p D i j k t) = ((stage p D m).1 i j k).coeff t := by
  rw [wlim, WittVector.truncate_liftFun (m + 1) (coeffMaps_compat p D i j k t)]
  simp [coeffMaps]

def Γlim (i j k : Fin (n + 1)) : (𝕎 K)[X] :=
  ∑ t ∈ Finset.range 5, C (wlim p D i j k t) * X ^ t

theorem coeff_Γlim (i j k : Fin (n + 1)) (t : ℕ) :
    (Γlim p D i j k).coeff t = if t < 5 then wlim p D i j k t else 0 := by
  rw [Γlim, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with ht
  · rw [Finset.sum_eq_single t]
    · rw [if_pos rfl]
    · intro s _ hs; rw [if_neg (Ne.symm hs)]
    · intro h; exact absurd (Finset.mem_range.2 ht) h
  · refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg]
    rintro rfl
    exact ht (Finset.mem_range.1 hs)

theorem natDegree_stage_le (m : ℕ) (i j k : Fin (n + 1)) :
    ((stage p D m).1 i j k).natDegree ≤ 4 := by
  have hG := (stage p D m).2
  by_cases hi : i = 0
  · subst hi; rw [hG.unit]; split_ifs <;> simp
  by_cases hj : j = 0
  · subst hj; rw [hG.comm, hG.unit]; split_ifs <;> simp
  refine (hG.deg i j k hi hj).trans ?_
  have h1 := D.hd i hi
  have h2 := D.hd j hj
  omega

theorem map_truncate_Γlim (m : ℕ) (i j k : Fin (n + 1)) :
    (Γlim p D i j k).map (WittVector.truncate (m + 1)) = (stage p D m).1 i j k := by
  ext t : 2
  rw [Polynomial.coeff_map, coeff_Γlim]
  split_ifs with ht
  · exact truncate_wlim p D m i j k t
  · rw [map_zero]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := natDegree_stage_le p D m i j k
    omega

def tableLim : Table ((𝕎 K)[X]) n where
  γ := Γlim p D
  unit j k := by
    apply eq_of_forall_map_truncate p K
    intro m
    rw [map_truncate_Γlim, (stage p D m).2.unit]
    split_ifs <;> simp
  comm i j k := by
    apply eq_of_forall_map_truncate p K
    intro m
    rw [map_truncate_Γlim, map_truncate_Γlim, (stage p D m).2.comm]
  assoc i j l m' := by
    apply eq_of_forall_map_truncate p K
    intro m
    simp only [Polynomial.map_sum, Polynomial.map_mul, map_truncate_Γlim]
    exact (stage p D m).2.assoc i j l m'

theorem tableLim_γ (i j k : Fin (n + 1)) : (tableLim p D).γ i j k = Γlim p D i j k := rfl

theorem natDegree_Γlim_le (i j k : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) :
    (Γlim p D i j k).natDegree ≤ D.d i + D.d j - D.d k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_Γlim]
  split_ifs with h5
  · ext m
    have hlt : ((stage p D m).1 i j k).natDegree < t :=
      lt_of_le_of_lt ((stage p D m).2.deg i j k hi hj) (by exact_mod_cast ht)
    have h := congrArg (TruncatedWittVector.coeff (Fin.last m)) (truncate_wlim p D m i j k t)
    rw [WittVector.coeff_truncate, Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      TruncatedWittVector.coeff_zero, Fin.val_last] at h
    rw [h, WittVector.zero_coeff]
  · rfl

theorem map_constantCoeff_Γlim (i j k : Fin (n + 1)) :
    (Γlim p D i j k).map (WittVector.constantCoeff : 𝕎 K →+* K) = D.b.repr (D.b i * D.b j) k := by
  rw [constantCoeff_eq_rho_comp_truncate p K, ← Polynomial.map_map, map_truncate_Γlim]
  exact (stage p D 0).2.red i j k

abbrev red : (𝕎 K)[X] →+* K[X] := Polynomial.mapRingHom (WittVector.constantCoeff : 𝕎 K →+* K)

theorem red_apply (f : (𝕎 K)[X]) : red p f = f.map (WittVector.constantCoeff : 𝕎 K →+* K) := rfl

theorem red_Γlim (i j k : Fin (n + 1)) :
    red p ((tableLim p D).γ i j k) = D.b.repr (D.b i * D.b j) k :=
  map_constantCoeff_Γlim p D i j k

def piFun (x : TAlg (tableLim p D)) : B := ∑ i, red p (x.coord i) • D.b i

theorem piFun_add (x y : TAlg (tableLim p D)) : piFun p D (x + y) = piFun p D x + piFun p D y := by
  simp only [piFun, TAlg.coord_add, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem piFun_single (i : Fin (n + 1)) (f : (𝕎 K)[X]) :
    piFun p D (TAlg.mk (Pi.single i f)) = red p f • D.b i := by
  rw [piFun, TAlg.coord_mk, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem piFun_one : piFun p D 1 = 1 := by
  have : (1 : TAlg (tableLim p D)) = TAlg.mk (Pi.single 0 1) := rfl
  rw [this, piFun_single, map_one, one_smul, D.hb0]

theorem b_mul_b (i j : Fin (n + 1)) :
    D.b i * D.b j = ∑ m, D.b.repr (D.b i * D.b j) m • D.b m :=
  (D.b.sum_repr (D.b i * D.b j)).symm

theorem piFun_mul (x y : TAlg (tableLim p D)) :
    piFun p D (x * y) = piFun p D x * piFun p D y := by
  have hL : piFun p D (x * y) =
      ∑ m, ∑ i, ∑ j, (red p (x.coord i) * red p (y.coord j) * D.b.repr (D.b i * D.b j) m) •
        D.b m := by
    rw [piFun]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TAlg.coord_mul, cst_apply, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, red_Γlim]
  have hR : piFun p D x * piFun p D y =
      ∑ i, ∑ j, ∑ m, (red p (x.coord i) * red p (y.coord j) * D.b.repr (D.b i * D.b j) m) •
        D.b m := by
    rw [piFun, piFun, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
    conv_lhs => rw [b_mul_b D i j]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  rw [hL, hR]
  exact sum3_rot _

def piB : TAlg (tableLim p D) →+* B where
  toFun := piFun p D
  map_one' := piFun_one p D
  map_mul' := piFun_mul p D
  map_zero' := by simp [piFun]
  map_add' := piFun_add p D

theorem piB_apply (x : TAlg (tableLim p D)) : piB p D x = ∑ i, red p (x.coord i) • D.b i := rfl

theorem piB_algebraMap (f : (𝕎 K)[X]) :
    piB p D (algebraMap (𝕎 K)[X] (TAlg (tableLim p D)) f) =
      algebraMap K[X] B (f.map (WittVector.constantCoeff : 𝕎 K →+* K)) := by
  have : algebraMap (𝕎 K)[X] (TAlg (tableLim p D)) f = TAlg.mk (Pi.single 0 f) := by
    ext1; rw [TAlg.algebraMap_coord, TAlg.coord_mk]
  rw [this]
  change piFun p D _ = _
  rw [piFun_single, D.hb0, Algebra.algebraMap_eq_smul_one]
  rfl

theorem piB_basis (i : Fin (n + 1)) : piB p D (TAlg.basis (tableLim p D) i) = D.b i := by
  rw [TAlg.basis_apply]
  change piFun p D _ = _
  rw [piFun_single, map_one, one_smul]

theorem natDegree_repr_basis_mul (i j k : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) :
    ((TAlg.basis (tableLim p D)).repr
        (TAlg.basis (tableLim p D) i * TAlg.basis (tableLim p D) j) k).natDegree ≤
      D.d i + D.d j - D.d k := by
  rw [TAlg.repr_basis_mul_basis, tableLim_γ]
  exact natDegree_Γlim_le p D i j k hi hj

end Tower

end WittLiftNF

end

open WittLiftNF in
private theorem witt_lift
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    ∃ (Bt : Type u) (_ : CommRing Bt) (_ : Algebra (WittVector p K)[X] Bt)
      (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (π : Bt →+* B),
      bt 0 = 1 ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k) ∧
      (∀ f : (WittVector p K)[X],
        π (algebraMap (WittVector p K)[X] Bt f) =
          algebraMap K[X] B (f.map (WittVector.constantCoeff : WittVector p K →+* K))) ∧
      (∀ i, π (bt i) = b i) := by
  let D : Datum K n B := ⟨b, d, hb0, hd0, hd, hdeg, hinf⟩
  exact ⟨TAlg (tableLim p D), inferInstance, inferInstance, TAlg.basis (tableLim p D), piB p D,
    TAlg.basis_zero _, natDegree_repr_basis_mul p D, piB_algebraMap p D, piB_basis p D⟩

end Aux10


open Polynomial

namespace AlgebraicCurve

/-- **Witt-vector lift of a normal-form basis.** Let $p$ be a prime, $K$ an algebraically closed
field of characteristic $p$, and $B$ an integrally closed domain that is a $K[X]$-algebra with a
$K[X]$-basis $b_0, \dots, b_n$ such that $b_0 = 1$. Write $b_i b_j = \sum_k c_{ij}^k b_k$ with
$c_{ij}^k \in K[X]$, and let $d_0 = 0$ and $d_i \in \{1, 2\}$ for $i \neq 0$. Suppose that
$\deg c_{ij}^k \le d_i + d_j - d_k$ (truncated subtraction) for all $i, j \neq 0$ and all $k$, and
that there is a matrix $(\tau_{jk})$ over $K$ with nonzero determinant such that $\tau_{j0} = 1$
for every $j$ and $\tau_{ji} \tau_{ji'} = \sum_k a_{ii'}^k \tau_{jk}$ for every $j$ and all
$i, i' \neq 0$, where $a_{ii'}^k$ is the coefficient of $X^{d_i + d_{i'} - d_k}$ in $c_{ii'}^k$.
Then there are a commutative $W(K)[X]$-algebra $\tilde B$, a $W(K)[X]$-basis
$\tilde b_0, \dots, \tilde b_n$ of $\tilde B$ and a ring homomorphism $\pi : \tilde B \to B$ such
that $\tilde b_0 = 1$, the structure constants of $\tilde b$ satisfy the same degree bounds, $\pi$
sends the image in $\tilde B$ of each $f \in W(K)[X]$ to the image in $B$ of the polynomial
obtained by applying the constant-coefficient map $W(K) \to K$ to the coefficients of $f$, and
$\pi(\tilde b_i) = b_i$ for every $i$. -/
public theorem exists_wittVector_lift_of_normalFormOrder
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 →
      ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    ∃ (Bt : Type u) (_ : CommRing Bt) (_ : Algebra (WittVector p K)[X] Bt)
      (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (π : Bt →+* B),
      bt 0 = 1 ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k) ∧
      (∀ f : (WittVector p K)[X],
        π (algebraMap (WittVector p K)[X] Bt f) =
          algebraMap K[X] B (f.map (WittVector.constantCoeff : WittVector p K →+* K))) ∧
      (∀ i, π (bt i) = b i) :=
  Aux10.witt_lift p K n B b d hb0 hd0 hd hdeg hinf

end AlgebraicCurve

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq.lean`,
`Definitions/Def_EllipticCurve_TateModule.lean`,
`Definitions/Def_ModularCurve_JZeroTateModule.lean`,
`Theorems/Thm_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard.lean`
and
`P2M/Sol/S_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq.lean`,
`P2M/Sol/S_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard.lean`
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

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.RingHom

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

open scoped TensorProduct

/-- The Tate module of an additive commutative group `M` at `p`: compatible
sequences `x : ℕ → M` with `(p ^ n) • x n = 0` and `p • x (n + 1) = x n`,
as an additive subgroup of `ℕ → M`. -/
def TateModule (p : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {x | ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy n =>
    ⟨by rw [Pi.add_apply, smul_add, (hx n).1, (hy n).1, add_zero],
     by rw [Pi.add_apply, Pi.add_apply, smul_add, (hx n).2, (hy n).2]⟩
  zero_mem' := fun n => ⟨smul_zero _, by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]⟩
  neg_mem' := fun {x} hx n =>
    ⟨by rw [Pi.neg_apply, smul_neg, (hx n).1, neg_zero],
     by rw [Pi.neg_apply, Pi.neg_apply, smul_neg, (hx n).2]⟩

namespace TateModule

variable {p : ℕ} {M : Type*} [AddCommGroup M]

theorem torsion (x : TateModule p M) (n : ℕ) : ((p ^ n : ℕ) : ℤ) • (x : ℕ → M) n = 0 := (x.2 n).1

theorem compat (x : TateModule p M) (n : ℕ) : ((p : ℕ) : ℤ) • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (x.2 n).2

theorem compat_pow (x : TateModule p M) (n k : ℕ) :
    ((p ^ k : ℕ) : ℤ) • (x : ℕ → M) (n + k) = (x : ℕ → M) n := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_one, one_smul, Nat.add_zero]
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, mul_smul]
    show ((p ^ k : ℕ) : ℤ) • (((p : ℕ) : ℤ) • (x : ℕ → M) ((n + k) + 1)) = _
    rw [compat, ih]

@[simp] theorem coe_add (x y : TateModule p M) : ((x + y : TateModule p M) : ℕ → M) = x + y := rfl
@[simp] theorem coe_zero : ((0 : TateModule p M) : ℕ → M) = 0 := rfl
@[simp] theorem coe_neg (x : TateModule p M) : ((-x : TateModule p M) : ℕ → M) = -x := rfl
@[simp] theorem coe_sub (x y : TateModule p M) : ((x - y : TateModule p M) : ℕ → M) = x - y := rfl

theorem apply_zero (x : TateModule p M) : (x : ℕ → M) 0 = 0 := by
  have h := torsion x 0
  rwa [pow_zero, Nat.cast_one, one_smul] at h

theorem natCast_smul_eq_mod {n c : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0) :
    (c : ℤ) • m = ((c % p ^ n : ℕ) : ℤ) • m := by
  conv_lhs => rw [← Nat.div_add_mod c (p ^ n)]
  rw [Nat.cast_add, add_smul, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, zero_add]

theorem natCast_smul_eq_of_zmod_eq {n c d : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0)
    (h : (c : ZMod (p ^ n)) = d) : (c : ℤ) • m = (d : ℤ) • m := by
  rw [natCast_smul_eq_mod hm, natCast_smul_eq_mod (c := d) hm,
      (ZMod.natCast_eq_natCast_iff' c d _).1 h]

variable [Fact p.Prime]

theorem toZModPow_eq_appr (n : ℕ) (a : ℤ_[p]) : PadicInt.toZModPow n a = (a.appr n : ZMod (p ^ n))
    := rfl

theorem appr_succ_smul_eq (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a.appr (n + 1) : ℕ) : ℤ) • (x : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := by
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ,
      RingHom.comp_apply,
    toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p n.le_succ)]

noncomputable instance instSMul : SMul ℤ_[p] (TateModule p M) :=
  ⟨fun a x => ⟨fun n => ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n, fun n =>
    ⟨by rw [smul_comm, torsion, smul_zero], by rw [smul_comm, compat, appr_succ_smul_eq]⟩⟩⟩

@[simp] theorem smul_apply (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a • x : TateModule p M) : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := rfl

noncomputable instance instModule : Module ℤ_[p] (TateModule p M) where
  one_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply]
    have h : (((1 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((1 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_one, Nat.cast_one]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_one, one_smul]
  mul_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, smul_apply, smul_apply, smul_smul, ← Nat.cast_mul]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_mul, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (funext fun n => by rw [smul_apply, coe_zero, Pi.zero_apply,
      smul_zero])
  smul_add a x y := Subtype.ext (funext fun n => by
    rw [smul_apply, coe_add, Pi.add_apply, smul_add, coe_add, Pi.add_apply, smul_apply, smul_apply])
  add_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_add, Pi.add_apply, smul_apply, smul_apply, ← add_smul, ← Nat.cast_add]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_add, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_zero, Pi.zero_apply]
    have h : (((0 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_zero, Nat.cast_zero]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]

theorem natCast_padicInt_smul_apply (c : ℕ) (x : TateModule p M) (n : ℕ) :
    (((c : ℤ_[p]) • x : TateModule p M) : ℕ → M) n = (c : ℤ) • (x : ℕ → M) n := by
  rw [smul_apply]
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, map_natCast]

theorem smul_apply_eq_zero_of_mem_span {n : ℕ} {a : ℤ_[p]}
    (ha : a ∈ Ideal.span {(p : ℤ_[p]) ^ n}) (x : TateModule p M) :
    ((a • x : TateModule p M) : ℕ → M) n = 0 := by
  rw [smul_apply]
  have h : ((a.appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
    rw [← toZModPow_eq_appr, Nat.cast_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact ha
  rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]

variable (p M) in

def proj (n : ℕ) : TateModule p M →+ M where
  toFun x := (x : ℕ → M) n
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fact p.Prime] in
@[simp] theorem proj_apply (n : ℕ) (x : TateModule p M) : proj p M n x = (x : ℕ → M) n := rfl

omit [Fact p.Prime] in
theorem torsionBy_proj (n : ℕ) (x : TateModule p M) : ((p ^ n : ℕ) : ℤ) • proj p M n x = 0 :=
  torsion x n

omit [Fact p.Prime] in
theorem proj_mem_torsionBy (n : ℕ) (x : TateModule p M) :
    proj p M n x ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  (Submodule.mem_torsionBy_iff _ _).2 (torsion x n)


end TateModule

namespace TateModule

open Submodule

variable {p : ℕ} {M : Type*} [AddCommGroup M]

theorem mem_torsionBy_add {n : ℕ} {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) (k : ℕ) :
    m ∈ torsionBy ℤ M ((p ^ (n + k) : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero]

theorem smul_mem_torsionBy_of_mem_succ {n : ℕ} {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ (n + 1) : ℕ)
    : ℤ)) :
    ((p : ℕ) : ℤ) • m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [smul_smul, ← Nat.cast_mul, ← pow_succ, hm]

theorem pow_smul_mem_torsionBy {n k : ℕ} {m : M} (hk : k ≤ n) (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ)
    : ℤ)) :
    ((p ^ (n - k) : ℕ) : ℤ) • m ∈ torsionBy ℤ M ((p ^ k : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [smul_smul, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hk, hm]

theorem mem_torsionBy_one_of_smul_eq_zero {m : M} (hm : ((p : ℕ) : ℤ) • m = 0) :
    m ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff, pow_one]; exact hm

theorem smul_eq_zero_of_mem_torsionBy_one {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) :
    ((p : ℕ) : ℤ) • m = 0 := by
  rw [mem_torsionBy_iff, pow_one] at hm; exact hm

section Counting

variable [Fact p.Prime]

theorem finite_torsionBy {r : ℕ} (hcard : ∀ n : ℕ,
    Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ) :
    Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

variable (p M) in

def mulP (n : ℕ) : torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ) →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) where
  toFun m := ⟨((p : ℕ) : ℤ) • (m : M), smul_mem_torsionBy_of_mem_succ m.2⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' _ _ := Subtype.ext (smul_add _ _ _)

omit [Fact p.Prime] in
@[simp] theorem coe_mulP (n : ℕ) (m : torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ)) :
    (mulP p M n m : M) = ((p : ℕ) : ℤ) • (m : M) := rfl

variable (p M) in

def kerMulPEquiv (n : ℕ) : (mulP p M n).ker ≃ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) where
  toFun m := ⟨(m.1 : M), mem_torsionBy_one_of_smul_eq_zero (by
    have h := m.2; rw [AddMonoidHom.mem_ker] at h; exact congrArg Subtype.val h)⟩
  invFun m := ⟨⟨(m : M), by
      rw [mem_torsionBy_iff, pow_succ, Nat.cast_mul, mul_smul,
          smul_eq_zero_of_mem_torsionBy_one m.2,
        smul_zero]⟩,
    by rw [AddMonoidHom.mem_ker]; exact Subtype.ext (smul_eq_zero_of_mem_torsionBy_one m.2)⟩
  left_inv m := rfl
  right_inv m := rfl

theorem mulP_surjective {r : ℕ}
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ) :
    Function.Surjective (mulP p M n) := by
  haveI := finite_torsionBy hcard (n + 1)
  haveI := finite_torsionBy hcard n
  have hker : Nat.card (mulP p M n).ker = p ^ r := by
    rw [Nat.card_congr (kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP p M n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulP p M n)).toEquiv,
      hker] at h
  have hrange : Nat.card (mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos r) ?_
    rw [← h, pow_succ, mul_pow]
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem exists_smul_eq_of_mem_torsionBy
    {r : ℕ} (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {n : ℕ} {m : M}
    (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ m' ∈ torsionBy ℤ M ((p ^ (n + 1) : ℕ) : ℤ), ((p : ℕ) : ℤ) • m' = m := by
  obtain ⟨m', hm'⟩ := mulP_surjective hcard n ⟨m, hm⟩
  exact ⟨m', m'.2, congrArg Subtype.val hm'⟩

noncomputable def liftAux
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : (j : ℕ) → torsionBy ℤ M ((p ^ (n + j) : ℕ) : ℤ)
  | 0 => m
  | j + 1 => next (n + j) (liftAux next n m j)

noncomputable def liftFun
    (next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ))
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) (k : ℕ) : M :=
  if n ≤ k then (liftAux next n m (k - n) : M) else ((p ^ (n - k) : ℕ) : ℤ) • (m : M)

omit [Fact p.Prime] in
theorem liftFun_of_le {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} {k : ℕ} (hk : n ≤ k) :
    liftFun next n m k = (liftAux next n m (k - n) : M) := ite_eq_left hk

omit [Fact p.Prime] in
theorem liftFun_of_lt {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} {k : ℕ} (hk : k < n) :
    liftFun next n m k = ((p ^ (n - k) : ℕ) : ℤ) • (m : M) := ite_eq_right (not_le.mpr hk)

omit [Fact p.Prime] in
theorem coe_liftAux_congr {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} {j j' : ℕ} (h : j =
    j') :
    (liftAux next n m j : M) = (liftAux next n m j' : M) := by subst h; rfl

omit [Fact p.Prime] in
theorem pow_smul_coe_liftAux {next} {n : ℕ} {m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)} (j : ℕ) {e : ℕ}
    (he : e = n + j) : ((p ^ e : ℕ) : ℤ) • (liftAux next n m j : M) = 0 := by
  subst he; exact (mem_torsionBy_iff _ _).mp (liftAux next n m j).2

omit [Fact p.Prime] in

theorem liftFun_mem
    {next : (k : ℕ) → torsionBy ℤ M ((p ^ k : ℕ) : ℤ) → torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ)}
    (hnext : ∀ k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)), ((p : ℕ) : ℤ) • (next k m : M) = m)
    (n : ℕ) (m : torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) : liftFun next n m ∈ TateModule p M := by
  intro k
  constructor
  ·
    by_cases hk : n ≤ k
    · rw [liftFun_of_le hk]
      exact pow_smul_coe_liftAux (k - n) (by omega)
    · rw [liftFun_of_lt (not_le.mp hk)]
      exact (mem_torsionBy_iff _ _).mp (pow_smul_mem_torsionBy (not_le.mp hk).le m.2)
  ·
    by_cases hk : n ≤ k
    · rw [liftFun_of_le hk, liftFun_of_le (by omega : n ≤ k + 1),
        coe_liftAux_congr (by omega : k + 1 - n = (k - n) + 1)]
      exact hnext _ _
    · by_cases hk' : n ≤ k + 1
      · have hn : n = k + 1 := by omega
        subst hn
        rw [liftFun_of_le le_rfl, liftFun_of_lt (by omega : k < k + 1),
            coe_liftAux_congr (Nat.sub_self _),
          Nat.add_sub_cancel_left, pow_one]
        rfl
      · rw [liftFun_of_lt (not_le.mp hk'), liftFun_of_lt (not_le.mp hk), smul_smul, ← Nat.cast_mul,
          ← pow_succ', show n - (k + 1) + 1 = n - k by omega]


end Counting

end TateModule

namespace TateModule

/-- The rational Tate module: the tensor product of the Tate module with
the field of `p`-adic numbers over the ring of `p`-adic integers. -/
abbrev RationalTateModule (p : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M] : Type _ :=
  ℚ_[p] ⊗[ℤ_[p]] TateModule p M

open Submodule

variable {p : ℕ} {M : Type*} [AddCommGroup M] {r : ℕ}

private theorem proj_surjective' [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) (n : ℕ) :
    ∀ m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ), ∃ x : TateModule p M, proj p M n x = m := by
  intro m hm
  choose next hnext using fun k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) => mulP_surjective hcard k m
  refine ⟨⟨liftFun next n ⟨m, hm⟩,
    liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨m, hm⟩⟩, ?_⟩
  rw [proj_apply]
  change liftFun next n ⟨m, hm⟩ n = m
  rw [liftFun_of_le le_rfl, coe_liftAux_congr (Nat.sub_self n)]
  rfl

private theorem exists_tuple_of_card_eq_pow [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (hV : Nat.card V = p ^ r) :
    ∃ v : Fin r → V, ∀ a : Fin r → ℤ, ∑ i, a i • v i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  have hp : p.Prime := Fact.out
  have hrank : Module.finrank (ZMod p) V = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) V hrank
  refine ⟨b, fun a h => ?_⟩
  have h' : ∑ i, ((a i : ZMod p)) • b i = 0 := by
    simp only [Int.cast_smul_eq_zsmul]; exact h
  have hli := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => (a i : ZMod p)) h'
  exact fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) p).mp (hli i)

private theorem exists_indep_tuple_torsionBy_one [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    ∃ e : Fin r → M, (∀ i, e i ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) ∧
      ∀ a : Fin r → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  haveI := finite_torsionBy hcard 1
  have hmod : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), p • m = 0 := fun m =>
    Subtype.ext (by
      rw [coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ, Submodule.coe_zero]
      exact smul_eq_zero_of_mem_torsionBy_one m.2)
  letI : Module (ZMod p) (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) := AddCommGroup.zmodModule hmod
  have h1 : Nat.card (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ r := by rw [hcard 1, pow_one]
  obtain ⟨v, hv⟩ := exists_tuple_of_card_eq_pow (p := p) h1
  refine ⟨fun i => (v i : M), fun i => (v i).2, fun a ha => hv a (Subtype.ext ?_)⟩
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [coe_smul_of_tower, Submodule.coe_zero]
  exact ha

private theorem exists_tuple' [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    ∃ x : Fin r → TateModule p M,
      ∀ a : Fin r → ℤ, ∑ i, a i • ((x i : ℕ → M)) 1 = 0 → ∀ i, (p : ℤ) ∣ a i := by
  obtain ⟨e, he, h1⟩ := exists_indep_tuple_torsionBy_one hcard
  choose x hx using fun i => proj_surjective' hcard 1 (e i) (he i)
  have hx1 : ∀ i : Fin r, ((x i : ℕ → M)) 1 = e i := fun i => by
    have h := hx i; rwa [proj_apply] at h
  refine ⟨x, fun a ha => h1 a ?_⟩
  calc ∑ i, a i • e i
      = ∑ i, a i • ((x i : ℕ → M)) 1 := Finset.sum_congr rfl fun i _ => by rw [hx1 i]
    _ = 0 := ha

variable [Fact p.Prime]

omit [Fact p.Prime] in
private theorem dvd_of_rel_apply {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i,
        (p : ℤ) ∣ a i) :
    ∀ (n : ℕ) (a : Fin r → ℤ), (∑ i, a i • ((x i : TateModule p M) : ℕ → M) n) = 0 →
      ∀ i, ((p ^ n : ℕ) : ℤ) ∣ a i := by
  intro n
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a hab

    have hab1 : (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 := by
      have hcp : ∀ i, ((p ^ n : ℕ) : ℤ) • ((x i : TateModule p M) : ℕ → M) (n + 1) =
          ((x i : TateModule p M) : ℕ → M) 1 := fun i => Nat.add_comm n 1 ▸ compat_pow (x i) 1 n
      calc ∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1
          = ((p ^ n : ℕ) : ℤ) • ∑ i, a i • ((x i : TateModule p M) : ℕ → M) (n + 1) := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, hcp]
        _ = 0 := by rw [hab, smul_zero]
    choose a' ha' using fun i => h1 a hab1 i

    have hab' : (∑ i, a' i • ((x i : TateModule p M) : ℕ → M) n) = 0 := by
      refine hab.symm.trans (Finset.sum_congr rfl fun i _ => ?_) |>.symm
      rw [ha', mul_comm, mul_smul, compat]
    intro i
    rw [pow_succ', Nat.cast_mul, ha']
    exact mul_dvd_mul_left _ (ih a' hab' i)

private noncomputable def levelMap (x : Fin r → TateModule p M) (n : ℕ)
    (c : Fin r → ZMod (p ^ n)) : torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  ⟨∑ i, ((c i).val : ℤ) • ((x i : TateModule p M) : ℕ → M) n, by
    rw [mem_torsionBy_iff, Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, TateModule.torsion, smul_zero]⟩

private theorem levelMap_injective {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i, (p : ℤ) ∣ a i)
    (n : ℕ) : Function.Injective (levelMap x n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  intro c d h
  have h' : (∑ i, (((c i).val : ℤ) - (d i).val) • ((x i : TateModule p M) : ℕ → M) n) = 0 := by
    have hv := sub_eq_zero.mpr (congrArg Subtype.val h)
    simp only [levelMap, ← Finset.sum_sub_distrib, ← sub_smul] at hv
    exact hv
  have key : ∀ {u v : ZMod (p ^ n)}, ((p ^ n : ℕ) : ℤ) ∣ (u.val : ℤ) - v.val → u = v := fun {u v}
      huv => by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (v.val : ℤ) (u.val : ℤ) (p ^ n)).mpr huv
    rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        eq_comm] at this
  exact funext fun i => key (dvd_of_rel_apply h1 n _ h' i)

private theorem levelMap_bijective
    (hcard' : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i, (p : ℤ) ∣ a i)
    (n : ℕ) : Function.Bijective (levelMap x n) := by
  haveI : Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out :
        p.Prime).ne_zero))
  refine (levelMap_injective h1 n).bijective_of_nat_card_le ?_
  rw [hcard', Nat.card_pi, Finset.prod_const, Nat.card_zmod, Finset.card_univ, Fintype.card_fin]

private theorem exists_eq_levelMap
    (hcard' : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i, (p : ℤ) ∣ a i)
    (n : ℕ) {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ a : Fin r → ℕ, (∑ i, (a i : ℤ) • ((x i : TateModule p M) : ℕ → M) n) = m := by
  obtain ⟨c, hc⟩ := (levelMap_bijective hcard' h1 n).2 ⟨m, hm⟩
  exact ⟨fun i => (c i).val, congrArg Subtype.val hc⟩

omit [Fact p.Prime] in
private theorem coe_sum_apply (f : Fin r → TateModule p M) (n : ℕ) :
    ((∑ i, f i : TateModule p M) : ℕ → M) n = ∑ i, ((f i : TateModule p M) : ℕ → M) n := by
  rw [AddSubgroup.val_finsetSum]; exact Finset.sum_apply n Finset.univ _

private theorem linearIndependent_tuple {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i,
        (p : ℤ) ∣ a i) :
    LinearIndependent ℤ_[p] x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hlev : ∀ n i, ((p ^ n : ℕ) : ℤ) ∣ ((g i).appr n : ℤ) := fun n =>
    dvd_of_rel_apply h1 n (fun i => ((g i).appr n : ℤ)) (by
      have hn : ((∑ i, g i • x i : TateModule p M) : ℕ → M) n = 0 := by
        rw [hg, TateModule.coe_zero, Pi.zero_apply]
      rw [coe_sum_apply] at hn
      simp only [TateModule.smul_apply] at hn
      exact hn)
  intro i
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
  exact Int.natCast_dvd_natCast.mp (hlev n i)

private theorem mem_span_tuple
    (hcard' : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i, (p : ℤ) ∣ a i)
    (z : TateModule p M) : ∃ s : Fin r → ℤ_[p], (∑ i, s i • x i) = z := by
  choose a ha using fun n => exists_eq_levelMap hcard' h1 n (proj_mem_torsionBy n z)

  have hcompat : ∀ n i, ((p ^ n : ℕ) : ℤ) ∣ (a (n + 1) i : ℤ) - a n i := fun n =>
    dvd_of_rel_apply h1 n (fun i => (a (n + 1) i : ℤ) - a n i) (by
      simp_rw [sub_smul, Finset.sum_sub_distrib, ha n, sub_eq_zero, proj_apply,
        ← compat z n, ← proj_apply (n + 1) z, ← ha (n + 1), Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, compat])
  have hci : ∀ (i : Fin r) (k : ℕ), (p : ℤ) ^ k ∣ (fun k => (a k i : ℤ)) (k + 1) - (fun k => (a k
      i : ℤ)) k :=
    fun i k => by rw [← Nat.cast_pow]; exact hcompat k i
  refine ⟨fun i => PadicInt.ofIntSeq (fun k => (a k i : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (hci i)),
    Subtype.ext (funext fun n => ?_)⟩
  rw [← proj_apply n z, ← ha n]
  rw [coe_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TateModule.smul_apply]
  refine natCast_smul_eq_of_zmod_eq (TateModule.torsion (x i) n) ?_
  rw [← toZModPow_eq_appr,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a k i : ℤ)) p (hci i) n, Int.cast_natCast]

private theorem top_le_span_tuple
    (hcard' : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    {x : Fin r → TateModule p M}
    (h1 : ∀ a : Fin r → ℤ, (∑ i, a i • ((x i : TateModule p M) : ℕ → M) 1) = 0 → ∀ i,
        (p : ℤ) ∣ a i) :
    ⊤ ≤ span ℤ_[p] (Set.range x) := by
  rw [top_le_span_range_iff_forall_exists_fun]
  exact mem_span_tuple hcard' h1

private noncomputable def basisOfCardPow
    (hcard' : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Module.Basis (Fin r) ℤ_[p] (TateModule p M) :=
  Module.Basis.mk (v := (exists_tuple' hcard').choose)
    (linearIndependent_tuple (exists_tuple' hcard').choose_spec)
    (top_le_span_tuple hcard' (exists_tuple' hcard').choose_spec)

variable [Fact p.Prime]

/-- From the exact torsion counts `Nat.card (M[p ^ n]) = (p ^ n) ^ d` for
all `n`, the Tate module is a finite free `ℤ_[p]`-module of rank `d`, and
its rationalization has rank `d` over `ℚ_[p]`. -/
public theorem finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ M) ∧ Module.Free ℤ_[ℓ] (TateModule ℓ M) ∧
      Module.finrank ℤ_[ℓ] (TateModule ℓ M) = d ∧
      Module.finrank ℚ_[ℓ] (RationalTateModule ℓ M) = d := by
  classical
  let b := basisOfCardPow (p := ℓ) (M := M) (r := d) hcard
  have b' := b.baseChange ℚ_[ℓ]
  refine ⟨Module.Finite.of_basis b, Module.Free.of_basis b, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  · rw [Module.finrank_eq_card_basis b', Fintype.card_fin]

/-- From the exact torsion counts `Nat.card (M[p ^ n]) = (p ^ n) ^ d` for
all `n`, the Tate module has a basis indexed by `Fin d` over `ℤ_[p]`. -/
public theorem nonempty_basis_of_natCard_torsionBy_pow_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Nonempty (Module.Basis (Fin d) ℤ_[ℓ] (TateModule ℓ M)) :=
  ⟨basisOfCardPow (p := ℓ) (M := M) (r := d) hcard⟩

end TateModule

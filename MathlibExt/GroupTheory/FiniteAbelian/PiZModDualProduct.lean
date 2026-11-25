/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod.lean`
and
`P2M/Sol/S_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod.lean`
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
The private helpers below are likewise adapted from the FLT files
`Thm_AddCommGroup_nonempty_addEquiv_of_forall_natCard_torsionBy_eq.lean`,
`Thm_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero.lean`
and `Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean`, with their
`P2M/Sol/` counterparts, at the same commit.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

@[expose] public section

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

universe u v





private theorem natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩), fun y => ⟨(y.1.1, y.2.1), ?_⟩,
    fun x => rfl, fun y => rfl⟩
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).1
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).2
  · rw [Submodule.mem_torsionBy_iff, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨(Submodule.mem_torsionBy_iff _ _).mp y.1.2, (Submodule.mem_torsionBy_iff _ _).mp y.2.2⟩


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators



namespace AlgFAC

private noncomputable def tors (G : Type) [AddCommGroup G] (N : ℕ) : ℕ := Nat.card {x : G // N •
  x = 0}

private theorem tors_congr {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') (N : ℕ) :
    tors G N = tors G' N := by
  unfold tors
  refine Nat.card_congr ⟨fun x => ⟨e x.1, by rw [← map_nsmul, x.2, map_zero]⟩,
    fun y => ⟨e.symm y.1, by rw [← map_nsmul, y.2, map_zero]⟩, fun x => ?_, fun y => ?_⟩
  · apply Subtype.ext; simp
  · apply Subtype.ext; simp

private theorem tors_prod (G G' : Type) [AddCommGroup G] [AddCommGroup G'] (N : ℕ) :
    tors (G × G') N = tors G N * tors G' N := by
  unfold tors
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, (Prod.ext_iff.mp x.2).1⟩, ⟨x.1.2,
    (Prod.ext_iff.mp x.2).2⟩),
    fun y => ⟨(y.1.1, y.2.1), Prod.ext y.1.2 y.2.2⟩, fun x => rfl, fun y => rfl⟩

private theorem tors_pi {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] (N : ℕ) :
    tors (∀ i, G i) N = ∏ i, tors (G i) N := by
  unfold tors
  rw [← Nat.card_pi]
  refine Nat.card_congr ⟨fun x i => ⟨x.1 i, congrFun x.2 i⟩, fun y => ⟨fun i => (y i).1,
    funext fun i => (y i).2⟩,
    fun x => rfl, fun y => rfl⟩

private theorem tors_zmod (n : ℕ) [NeZero n] (N : ℕ) : tors (ZMod n) N = Nat.gcd N n := by
  classical
  unfold tors

  let φ : ZMod n →+ ZMod n := nsmulAddMonoidHom N
  have hker : Nat.card {x : ZMod n // N • x = 0} = Nat.card φ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1, x.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hrange : φ.range = AddSubgroup.zmultiples ((N : ℕ) : ZMod n) := by
    ext x
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff, φ, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(y.val : ℤ), by rw [zsmul_eq_mul, nsmul_eq_mul, Int.cast_natCast,
        ZMod.natCast_zmod_val, mul_comm]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k : ZMod n), by rw [nsmul_eq_mul, zsmul_eq_mul, mul_comm]⟩
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card (ZMod n) := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
  rw [hrange, Nat.card_zmultiples, ZMod.addOrderOf_coe _ (NeZero.ne n), Nat.card_zmod] at h1
  rw [hker]
  have hg : 0 < n.gcd N := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  have hdiv : n / n.gcd N * n.gcd N = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n N)
  have hq : 0 < n / n.gcd N := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) (Nat.gcd_dvd_left n N)) hg
  rw [Nat.gcd_comm]
  have := h1

  nlinarith [this, hdiv]

private theorem tors_pi_zmod {ι : Type} [Fintype ι] (n : ι → ℕ) [∀ i, NeZero (n i)] (N : ℕ) :
    tors (∀ i, ZMod (n i)) N = ∏ i, Nat.gcd N (n i) := by
  rw [tors_pi]
  simp_rw [tors_zmod]

end AlgFAC

namespace AlgFAC

private theorem card_torsionBy_eq_tors (A : Type u) [AddCommGroup A] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A N) = Nat.card {x : A // N • x = 0} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

private noncomputable def torsU (G : Type u) [AddCommGroup G] (N : ℕ) : ℕ := Nat.card {x : G //
  N • x = 0}

private theorem torsU_congr {G : Type u} {G' : Type} [AddCommGroup G] [AddCommGroup G'] (e : G
  ≃+ G') (N : ℕ) :
    torsU G N = tors G' N := by
  unfold tors torsU
  refine Nat.card_congr ⟨fun x => ⟨e x.1, by rw [← map_nsmul, x.2, map_zero]⟩,
    fun y => ⟨e.symm y.1, by rw [← map_nsmul, y.2, map_zero]⟩, fun x => ?_, fun y => ?_⟩
  · apply Subtype.ext; simp
  · apply Subtype.ext; simp

private theorem exists_pi_zmod (G : Type u) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, (p i).Prime) (e : ι → ℕ),
      Nonempty (G ≃+ ∀ i, ZMod (p i ^ e i)) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  exact ⟨ι, hι, p, hp, e, ⟨f.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (p i ^
    e i))).toAddEquiv⟩⟩

section Match

variable {ι : Type} [Fintype ι] [DecidableEq ι] (p e : ι → ℕ)

private def S (r k : ℕ) : ℕ := ∑ i, if p i = r then min k (e i) else 0

private def cge (r k : ℕ) : ℕ := (Finset.univ.filter fun i => p i = r ∧ k ≤ e i).card

private def ceq (r k : ℕ) : ℕ := (Finset.univ.filter fun i => p i = r ∧ e i = k).card

private theorem prod_gcd_prime_pow (hp : ∀ i, (p i).Prime) (r : ℕ) (hr : r.Prime) (k : ℕ) :
    ∏ i, Nat.gcd (r ^ k) (p i ^ e i) = r ^ S p e r k := by
  unfold S
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : p i = r
  · rw [ite_eq_left h, h]
    rcases le_total k (e i) with hk | hk
    · rw [min_eq_left hk, Nat.gcd_eq_left (pow_dvd_pow r hk)]
    · rw [min_eq_right hk, Nat.gcd_eq_right (pow_dvd_pow r hk)]
  · rw [ite_eq_right h, pow_zero]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr (hp i)).mpr (Ne.symm h))

private theorem S_succ (r k : ℕ) : S p e r (k + 1) = S p e r k + cge p e r (k + 1) := by
  unfold S cge
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p i = r
  · simp only [h, true_and, ite_true]
    by_cases hk : k + 1 ≤ e i
    · rw [ite_eq_left hk, min_eq_left hk, min_eq_left (Nat.le_of_succ_le hk)]
    · have hle : e i ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_not_le hk)
      rw [ite_eq_right hk, add_zero, min_eq_right (Nat.le_succ_of_le hle), min_eq_right hle]
  · simp [h]

private theorem cge_eq (r k : ℕ) : cge p e r k = ceq p e r k + cge p e r (k + 1) := by
  unfold cge ceq
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_or_lt_of_le h2 with h | h
      · exact Or.inl ⟨h1, h.symm⟩
      · exact Or.inr ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2 ▸ le_rfl⟩
      · exact ⟨h1, Nat.le_of_succ_le h2⟩
  · rw [Finset.disjoint_filter]
    rintro i - ⟨-, h⟩ ⟨-, h'⟩
    omega

end Match

section Match2

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (p e : ι → ℕ) (q f : κ → ℕ)

private theorem ceq_eq_of_S_eq (r : ℕ) (hS : ∀ k, S p e r k = S q f r k) (k : ℕ) (hk : 1 ≤ k) :
    ceq p e r k = ceq q f r k := by
  have hcge : ∀ k, 1 ≤ k → cge p e r k = cge q f r k := by
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 := S_succ p e r k
    have h2 := S_succ q f r k
    rw [hS k, hS (k + 1)] at h1
    omega
  have h1 := cge_eq p e r k
  have h2 := cge_eq q f r k
  rw [hcge k hk, hcge (k + 1) (by omega)] at h1
  omega

private def piSubtypeAddEquiv {ι : Type} (A : ι → Type) [∀ i,
  AddCommGroup (A i)] (P : ι → Prop) [DecidablePred P]
    (hP : ∀ i, ¬ P i → Subsingleton (A i)) : (∀ i, A i) ≃+ (∀ i : {i // P i}, A i.1) where
  toFun x i := x i.1
  invFun y i := if h : P i then y ⟨i, h⟩ else 0
  left_inv x := by
    funext i
    by_cases h : P i
    · simp [h]
    · haveI := hP i h
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]
  map_add' x y := rfl

private theorem nonempty_addEquiv_of_prod_gcd_eq (hp : ∀ i, (p i).Prime) (hq : ∀ j, (q j).Prime)
    (h : ∀ N : ℕ, ∏ i, Nat.gcd N (p i ^ e i) = ∏ j, Nat.gcd N (q j ^ f j)) :
    Nonempty ((∀ i, ZMod (p i ^ e i)) ≃+ (∀ j, ZMod (q j ^ f j))) := by
  classical

  have hS : ∀ r, r.Prime → ∀ k, S p e r k = S q f r k := by
    intro r hr k
    have := h (r ^ k)
    rw [prod_gcd_prime_pow p e hp r hr, prod_gcd_prime_pow q f hq r hr] at this
    exact Nat.pow_right_injective hr.two_le this
  have hceq : ∀ r k, r.Prime → 1 ≤ k → ceq p e r k = ceq q f r k :=
    fun r k hr hk => ceq_eq_of_S_eq p e q f r (hS r hr) k hk

  let I₁ := {i : ι // e i ≠ 0}
  let J₁ := {j : κ // f j ≠ 0}
  let key : I₁ → ℕ × ℕ := fun i => (p i.1, e i.1)
  let key' : J₁ → ℕ × ℕ := fun j => (q j.1, f j.1)
  have hfib : ∀ c : ℕ × ℕ, Fintype.card {i : I₁ // key i = c} = Fintype.card {j : J₁ // key' j =
    c} := by
    rintro ⟨r, k⟩

    have eI : {i : I₁ // key i = (r, k)} ≃ {i : ι // p i = r ∧ e i = k ∧ e i ≠ 0} :=
      ⟨fun x => ⟨x.1.1, (Prod.ext_iff.mp x.2).1, (Prod.ext_iff.mp x.2).2, x.1.2⟩,
       fun y => ⟨⟨y.1, y.2.2.2⟩, Prod.ext y.2.1 y.2.2.1⟩, fun x => rfl, fun y => rfl⟩
    have eJ : {j : J₁ // key' j = (r, k)} ≃ {j : κ // q j = r ∧ f j = k ∧ f j ≠ 0} :=
      ⟨fun x => ⟨x.1.1, (Prod.ext_iff.mp x.2).1, (Prod.ext_iff.mp x.2).2, x.1.2⟩,
       fun y => ⟨⟨y.1, y.2.2.2⟩, Prod.ext y.2.1 y.2.2.1⟩, fun x => rfl, fun y => rfl⟩
    rw [Fintype.card_congr eI, Fintype.card_congr eJ, Fintype.card_subtype, Fintype.card_subtype]
    by_cases hk : k = 0
    · subst hk
      rw [Finset.card_eq_zero.mpr, Finset.card_eq_zero.mpr] <;>
        simp [Finset.filter_eq_empty_iff]
    by_cases hr : r.Prime
    · have h1 : (Finset.univ.filter fun i => p i = r ∧ e i = k ∧ e i ≠ 0) =
          Finset.univ.filter fun i => p i = r ∧ e i = k := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, b ▸ hk⟩⟩
      have h2 : (Finset.univ.filter fun j => q j = r ∧ f j = k ∧ f j ≠ 0) =
          Finset.univ.filter fun j => q j = r ∧ f j = k := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, b ▸ hk⟩⟩
      rw [h1, h2]
      exact hceq r k hr (Nat.one_le_iff_ne_zero.mpr hk)
    · have h1 : (Finset.univ.filter fun i => p i = r ∧ e i = k ∧ e i ≠ 0) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ hh => hr (by rw [← hh.1]; exact hp i)
      have h2 : (Finset.univ.filter fun j => q j = r ∧ f j = k ∧ f j ≠ 0) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j _ hh => hr (by rw [← hh.1]; exact hq j)
      rw [h1, h2]
      rfl
  let σ : I₁ ≃ J₁ := Equiv.ofFiberEquiv (f := key) (g := key') fun c => Fintype.equivOfCardEq
    (hfib c)
  have hσ : ∀ i : I₁, key' (σ i) = key i := fun i => Equiv.ofFiberEquiv_map _ i
  have hnm : ∀ i : I₁, p i.1 ^ e i.1 = q (σ i).1 ^ f (σ i).1 := by
    intro i
    have := hσ i
    simp only [key, key', Prod.ext_iff] at this
    rw [this.1, this.2]

  have hsubI : ∀ i : ι, ¬ (e i ≠ 0) → Subsingleton (ZMod (p i ^ e i)) := by
    intro i hi
    rw [not_not] at hi
    rw [hi, pow_zero]
    infer_instance
  have hsubJ : ∀ j : κ, ¬ (f j ≠ 0) → Subsingleton (ZMod (q j ^ f j)) := by
    intro j hj
    rw [not_not] at hj
    rw [hj, pow_zero]
    infer_instance
  let E1 : (∀ i, ZMod (p i ^ e i)) ≃+ (∀ i : I₁, ZMod (p i.1 ^ e i.1)) :=
    piSubtypeAddEquiv (fun i => ZMod (p i ^ e i)) (fun i => e i ≠ 0) hsubI
  let E2 : (∀ i : I₁, ZMod (p i.1 ^ e i.1)) ≃+ (∀ i : I₁, ZMod (q (σ i).1 ^ f (σ i).1)) :=
    AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (hnm i)).toAddEquiv
  let E3 : (∀ i : I₁, ZMod (q (σ i).1 ^ f (σ i).1)) ≃+ (∀ j : J₁, ZMod (q j.1 ^ f j.1)) :=
    (LinearEquiv.piCongrLeft ℤ (fun j : J₁ => ZMod (q j.1 ^ f j.1)) σ).toAddEquiv
  let E4 : (∀ j, ZMod (q j ^ f j)) ≃+ (∀ j : J₁, ZMod (q j.1 ^ f j.1)) :=
    piSubtypeAddEquiv (fun j => ZMod (q j ^ f j)) (fun j => f j ≠ 0) hsubJ
  exact ⟨E1.trans (E2.trans (E3.trans E4.symm))⟩

end Match2

end AlgFAC

open AlgFAC in
private theorem nonempty_addEquiv_of_forall_natCard_torsionBy_eq
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (h : ∀ N : ℕ, Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) = Nat.card (Submodule.torsionBy ℤ B
      (N : ℤ))) :
    Nonempty (A ≃+ B) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨fA⟩⟩ := exists_pi_zmod A
  obtain ⟨κ, hκ, q, hq, f, ⟨fB⟩⟩ := exists_pi_zmod B
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : ∀ j, NeZero (q j ^ f j) := fun j => ⟨pow_ne_zero _ (hq j).ne_zero⟩
  have hprof : ∀ N : ℕ, ∏ i, Nat.gcd N (p i ^ e i) = ∏ j, Nat.gcd N (q j ^ f j) := by
    intro N
    rw [← tors_pi_zmod, ← tors_pi_zmod, ← torsU_congr fA, ← torsU_congr fB]
    have := h N
    rwa [card_torsionBy_eq_tors, card_torsionBy_eq_tors] at this
  obtain ⟨E⟩ := nonempty_addEquiv_of_prod_gcd_eq p e q f hp hq hprof
  exact ⟨fA.trans (E.trans fB.symm)⟩



open scoped BigOperators

namespace PoleB1

private theorem exists_addMonoidHom_injective_forall_nsmul_eq_zero_iff {M n : ℕ} [NeZero M] (hn
  : n ∣ M) :
    ∃ g : ZMod n →+ ZMod M, Function.Injective g ∧ ∀ y : ZMod M, n • y = 0 ↔ y ∈ Set.range g := by
  obtain ⟨q, hq⟩ := hn
  have hM : M ≠ 0 := NeZero.ne M
  have hn0 : n ≠ 0 := by rintro rfl; rw [zero_mul] at hq; exact hM hq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hM hq
  haveI : NeZero n := ⟨hn0⟩
  have hkill : (zmultiplesHom (ZMod M) (q : ZMod M)) (n : ℤ) = 0 := by
    show (n : ℤ) • (q : ZMod M) = 0
    rw [zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ← hq, ZMod.natCast_self]
  let g : ZMod n →+ ZMod M := ZMod.lift n ⟨zmultiplesHom (ZMod M) (q : ZMod M), hkill⟩
  have hg : ∀ z : ℤ, g (z : ZMod n) = ((z * q : ℤ) : ZMod M) := by
    intro z
    rw [show g (z : ZMod n) = (zmultiplesHom (ZMod M) (q : ZMod M)) z from ZMod.lift_coe n _ z]
    show z • (q : ZMod M) = _
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  refine ⟨g, ?_, ?_⟩
  · intro x₁ x₂ h
    obtain ⟨z₁, rfl⟩ := ZMod.intCast_surjective x₁
    obtain ⟨z₂, rfl⟩ := ZMod.intCast_surjective x₂
    rw [hg, hg] at h
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    rw [← sub_mul, hq, Nat.cast_mul] at h
    exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0) h
  · intro y
    constructor
    · intro hy
      obtain ⟨w, rfl⟩ := ZMod.intCast_surjective y
      have : ((n * w : ℤ) : ZMod M) = 0 := by
        rw [Int.cast_mul, Int.cast_natCast, ← nsmul_eq_mul]; exact hy
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hq, Nat.cast_mul] at this
      obtain ⟨v, hv⟩ := Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hn0) this
      refine ⟨(v : ZMod n), ?_⟩
      rw [hg, mul_comm, ← hv]
    · rintro ⟨x, rfl⟩
      rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

private def torsionSub (n : ℕ) (D : Type*) [AddCommGroup D] : AddSubgroup D where
  carrier := {y | n • y = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, nsmul_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_nsmul, ha, neg_zero]

private theorem mem_torsionSub {n : ℕ} {D : Type*} [AddCommGroup D] (y : D) : y ∈ torsionSub n D
  ↔ n • y = 0 := Iff.rfl

private noncomputable def homZModEquivTorsion (n : ℕ) (D : Type*) [AddCommGroup D] :
    (ZMod n →+ D) ≃+ torsionSub n D where
  toFun f := ⟨f 1, by rw [mem_torsionSub, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self,
    map_zero]⟩
  invFun y := ZMod.lift n ⟨zmultiplesHom D y.1, by
    show (n : ℤ) • y.1 = 0
    rw [natCast_zsmul]; exact y.2⟩
  left_inv f := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [ZMod.lift_coe]
    show z • f 1 = f z
    rw [← map_zsmul, zsmul_eq_mul, mul_one]
  right_inv y := by
    apply Subtype.ext
    dsimp only
    rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) from Int.cast_one.symm, ZMod.lift_coe]
    simp
  map_add' f f' := by
    apply Subtype.ext; rfl

private theorem nonempty_addEquiv_hom_zmod_zmod {d n : ℕ} [NeZero d] (hn : n ∣ d) :
    Nonempty ((ZMod n →+ ZMod d) ≃+ ZMod n) := by
  obtain ⟨g, hinj, hrange⟩ := exists_addMonoidHom_injective_forall_nsmul_eq_zero_iff (M := d) hn

  have hTR : torsionSub n (ZMod d) = g.range := by
    ext y
    rw [mem_torsionSub, AddMonoidHom.mem_range, hrange]
    constructor <;> (rintro ⟨x, hx⟩; exact ⟨x, hx⟩)
  exact ⟨(homZModEquivTorsion n (ZMod d)).trans ((AddEquiv.addSubgroupCongr hTR).trans
    (AddMonoidHom.ofInjective hinj).symm)⟩

private theorem nonempty_addEquiv_addMonoidHom_zmod (L : Type u) [AddCommGroup L] [Finite L] {d
  : ℕ} [NeZero d]
    (hd : ∀ x : L, d • x = 0) : Nonempty ((L →+ ZMod d) ≃+ L) := by
  classical
  obtain ⟨ι, hι, nn, hnn, ⟨eL⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' L

  let eP : L ≃ₗ[ℤ] ((i : ι) → ZMod (nn i)) :=
    eL.toIntLinearEquiv.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (nn i)))

  have hdiv : ∀ i, nn i ∣ d := by
    intro i
    haveI : NeZero (nn i) := ⟨by have := hnn i; omega⟩
    have h1 : d • eP.symm (Pi.single i (1 : ZMod (nn i))) = 0 := hd _
    have h2 : d • (Pi.single i (1 : ZMod (nn i)) : (j : ι) → ZMod (nn j)) = 0 := by
      have := congrArg eP h1
      rwa [map_nsmul, LinearEquiv.apply_symm_apply, map_zero] at this
    have h3 := congrFun h2 i
    rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at h3
    exact (ZMod.natCast_eq_zero_iff d (nn i)).mp h3

  have hcomp : ∀ i, Nonempty ((ZMod (nn i) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ZMod (nn i)) := fun i => by
    obtain ⟨e⟩ := nonempty_addEquiv_hom_zmod_zmod (d := d) (hdiv i)
    exact ⟨((addMonoidHomLequivInt (A := ZMod (nn i)) (B := ZMod d) ℤ).symm.trans
      e.toIntLinearEquiv)⟩
  have ec : ∀ i, (ZMod (nn i) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ZMod (nn i) := fun i => (hcomp i).some

  let E1 : (L →+ ZMod d) ≃ₗ[ℤ] (L →ₗ[ℤ] ZMod d) := addMonoidHomLequivInt ℤ
  let E2 : (L →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] (((i : ι) → ZMod (nn i)) →ₗ[ℤ] ZMod d) :=
    LinearEquiv.congrLeft (ZMod d) ℤ eP
  let E3 : (((i : ι) → ZMod (nn i)) →ₗ[ℤ] ZMod d) ≃ₗ[ℤ] ((i : ι) → (ZMod (nn i) →ₗ[ℤ] ZMod d)) :=
    (LinearMap.lsum ℤ (fun i => ZMod (nn i)) ℤ).symm
  let E4 : ((i : ι) → (ZMod (nn i) →ₗ[ℤ] ZMod d)) ≃ₗ[ℤ] ((i : ι) → ZMod (nn i)) :=
    LinearEquiv.piCongrRight ec
  exact ⟨(E1.trans (E2.trans (E3.trans (E4.trans eP.symm)))).toAddEquiv⟩

end PoleB1

open PoleB1 in
private theorem nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L) := by
  exact PoleB1.nonempty_addEquiv_addMonoidHom_zmod L hd

namespace AddEquiv



open scoped BigOperators

/-- If a finite abelian group `L`, together with its dual
`L →+ ZMod d` where `d = ∏ i, δ i`, is isomorphic to the product of
`Π i, ZMod (δ i)` with itself, then `L` itself is isomorphic to
`Π i, ZMod (δ i)`.

The dual factor forces every element of `L` to be killed by `d`, hence
`L` is isomorphic to its dual; comparing the cardinalities of the
`N`-torsion subgroups of the two sides of the resulting product
isomorphism then gives the claim for every `N`, and a finite abelian
group is determined by those cardinalities. -/
public theorem nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (L : Type u) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod d) ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) :
    Nonempty (L ≃+ ((i : Fin g) → ZMod (δ i))) := by
  classical
  haveI hd0 : NeZero d := by
    refine ⟨?_⟩
    rw [← hδd]
    exact Finset.prod_ne_zero_iff.2 fun i _ => NeZero.ne (δ i)
  have hδdvd : ∀ i, δ i ∣ d := by
    intro i
    rw [← hδd]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hdH : ∀ y : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)), d • y = 0 := by
    intro y
    have h1 : ∀ z : ((i : Fin g) → ZMod (δ i)), d • z = 0 := by
      intro z; funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        (ZMod.natCast_eq_zero_iff d (δ i)).2 (hδdvd i), zero_mul]
    rw [Prod.smul_mk, h1, h1]; rfl
  have hdL : ∀ x : L, d • x = 0 := by
    intro x
    have h : d • (x, (0 : L →+ ZMod d)) = 0 := by
      apply e.injective
      rw [map_nsmul, map_zero, hdH]
    have h2 := congrArg Prod.fst h
    simpa using h2
  obtain ⟨φ⟩ := nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero L d hdL
  let e2 : L × L ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) :=
    (AddEquiv.prodCongr (AddEquiv.refl L) φ.symm).trans e

  have hcongr : ∀ N : ℕ,
      Nat.card (Submodule.torsionBy ℤ (L × L) (N : ℤ)) =
        Nat.card (Submodule.torsionBy ℤ
          (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) (N : ℤ)) := by
    intro N
    refine Nat.card_congr (e2.toEquiv.subtypeEquiv fun x => ?_)
    change x ∈ Submodule.torsionBy ℤ (L × L) (N : ℤ) ↔
      e2 x ∈ Submodule.torsionBy ℤ _ (N : ℤ)
    rw [Submodule.mem_torsionBy_iff, Submodule.mem_torsionBy_iff, ← map_zsmul,
      e2.map_eq_zero_iff]
  refine nonempty_addEquiv_of_forall_natCard_torsionBy_eq L ((i : Fin g) → ZMod (δ i)) fun N => ?_
  have h := hcongr N
  rw [natCard_torsionBy_prod_eq_mul, natCard_torsionBy_prod_eq_mul] at h
  exact Nat.mul_self_inj.1 h

end AddEquiv

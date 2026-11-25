/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
import MathlibExt.GroupTheory.DicksonPGL2Wild
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases

/-!
# Class number versus orders of nilpotent subgroups

The group $\mathrm{PGL}_2(\mathbf F_{11})$ refutes the proposed bound on the class number
by the order of a nilpotent subgroup. Companion matrices give twelve distinct nonidentity
conjugacy classes. Any subgroup of order greater than twelve has an odd prime divisor. If the
subgroup were nilpotent, its center would contain an element of that prime order, whose
centralizer in the projective group has order at most twelve.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ClassNumberNilpotentSubgroupKourovka14Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.54 (M. W. Liebeck, L. Pyber).
UnsolvedMath record UM-00701039 (`KOU-14.54`), dataset ulamai/UnsolvedMath v1.8.0.

`k(G)` is `Nat.card (ConjClasses G)`; nilpotent subgroups are `Group.IsNilpotent N`.
-/

/-- **Liebeck–Pyber problem on the class number and nilpotent subgroups.** The proposition that
every finite group $G$ has a nilpotent subgroup $N$ whose order $|N|$ is at least the number
$k(G)$ of conjugacy classes of $G$. This is Kourovka Problem 14.54 (M. W. Liebeck, L. Pyber). -/
def classNumberAtMostNilpotentSubgroupOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ N : Subgroup G, Group.IsNilpotent N ∧
    Nat.card (ConjClasses G) ≤ Nat.card N

open Matrix
open scoped MatrixGroups

local notation "F" => ZMod 11
local notation "G" => PGL(2, F)
local notation "L" => GL (Fin 2) F
private instance primeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

private abbrev π : L →* G := ProjGenLinGroup.mk

private lemma card_projective : Nat.card G = 1320 := by
  rw [MetaMathlibExt.Dickson.card_projGenLinGroup_fin_two (ZMod 11), ZMod.card]
  decide

private instance finiteProjective : Finite G :=
  Nat.finite_of_card_ne_zero (by rw [card_projective]; decide)

/-- A projective equality between lifts is an equality of matrices up to a nonzero scalar. -/
private lemma scalar_of_eq {A B : L} (h : π A = π B) :
    ∃ u : Fˣ, u.val • A.val = B.val := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  exact ⟨u, by simpa [scalar_apply, smul_eq_mul_diagonal] using congrArg Units.val hu⟩

-- Ten companion matrices have trace one. The two with trace zero have determinants
-- in different square classes. All twelve have a nonzero off-diagonal entry.
private def repTrace (i : Fin 12) : F := if i.val < 10 then 1 else 0
private def repDet (i : Fin 12) : F :=
  if i.val < 10 then i.val + 1 else if i.val = 10 then 1 else 2

private noncomputable def rep (i : Fin 12) : L :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -repDet i; 1, repTrace i] (by
    simp only [det_fin_two_of, zero_mul, mul_one, zero_sub, neg_neg]
    exact (by decide : ∀ j, repDet j ≠ 0) i)

private lemma rep_not_one (i : Fin 12) : π (rep i) ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ := scalar_of_eq (B := 1) h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hu
  simp [rep, GeneralLinearGroup.mkOfDetNeZero] at he

private lemma reps_separated {i j : Fin 12} (h : IsConj (π (rep i)) (π (rep j))) : i = j := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨C, rfl⟩ := ProjGenLinGroup.mk_surjective g
  obtain ⟨u, hu⟩ := scalar_of_eq (A := C * rep i * C⁻¹) (B := rep j) (by simpa using hg)
  have ht := congrArg Matrix.trace hu
  have hd := congrArg Matrix.det hu
  simp only [Units.val_mul, trace_smul, trace_units_conj, smul_eq_mul] at ht
  simp only [Units.val_mul, det_smul, Fintype.card_fin, det_units_conj] at hd
  have ht' : (u : F) * repTrace i = repTrace j := by
    simpa [rep, trace_fin_two_of, GeneralLinearGroup.mkOfDetNeZero] using ht
  have hd' : (u : F) ^ 2 * repDet i = repDet j := by
    simpa [rep, GeneralLinearGroup.mkOfDetNeZero, det_fin_two_of] using hd
  exact (by decide : ∀ (a b : Fin 12) (z : F), z ≠ 0 →
    z * repTrace a = repTrace b → z ^ 2 * repDet a = repDet b → a = b) i j u u.ne_zero ht' hd'

private lemma class_number_lower : 13 ≤ Nat.card (ConjClasses G) := by
  let f : Option (Fin 12) → ConjClasses G
    | none => ConjClasses.mk 1
    | some i => ConjClasses.mk (π (rep i))
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact False.elim (rep_not_one _ (isConj_one_right.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)))
    · exact False.elim (rep_not_one _ (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)))
    · exact congrArg some (reps_separated (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  simpa using Nat.card_le_card_of_injective f hf

-- A traceless two-by-two matrix squares to a scalar.
private lemma trace_ne_zero {A : L} (hA : π A ^ 2 ≠ 1) : A.val.trace ≠ 0 := by
  intro ht
  apply hA
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨-A.val.det, ?_⟩
  rw [trace_fin_two] at ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalar_apply, det_fin_two, sq, Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> grind

-- A projective commutation with a nonzero-trace matrix lifts to an actual commutation,
-- since a conjugate has the same trace.
private lemma commute_of_projective {A B : L} (ht : A.val.trace ≠ 0)
    (h : Commute (π B) (π A)) : Commute B.val A.val := by
  have hconj : π (B * A * B⁻¹) = π A := by
    simp only [map_mul, map_inv, mul_inv_eq_iff_eq_mul, h.eq]
  obtain ⟨u, hu⟩ := scalar_of_eq hconj
  have he := congrArg Matrix.trace hu
  simp only [trace_smul, Units.val_mul, trace_units_conj, smul_eq_mul] at he
  have hu1 : (u : F) = 1 := (mul_eq_right₀ ht).mp he
  rw [hu1, one_smul] at hu
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp (Units.ext hu))

-- Two entries determine a commuting matrix. Use the first or second column if the
-- corresponding off-diagonal entry of A is nonzero, and the diagonal otherwise.
private lemma card_commuting_lifts (H : Subgroup L) {A : L} (ha : π A ≠ 1)
    (hc : ∀ B : H, Commute B.val.val A.val) : Nat.card H ≤ 121 := by
  let coords (B : H) : F × F :=
    if A 1 0 ≠ 0 then (B.val 0 0, B.val 1 0)
    else if A 0 1 ≠ 0 then (B.val 0 1, B.val 1 1)
    else (B.val 0 0, B.val 1 1)
  have hinj : Function.Injective coords := by
    intro B C he
    let D := B.val.val - C.val.val
    have hD : D * A.val = A.val * D := by
      simp only [D, sub_mul, mul_sub, (hc B).eq, (hc C).eq]
    have eqn (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hD
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at eqn
    suffices hzero : D = 0 from Subtype.ext (Units.ext (sub_eq_zero.mp hzero))
    have entry (i j : Fin 2) (h : B.val i j = C.val i j) : D i j = 0 := sub_eq_zero.mpr h
    suffices D 0 0 = 0 ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = 0 by
      ext i j
      change D i j = 0
      fin_cases i <;> fin_cases j <;> tauto
    by_cases h10 : A 1 0 ≠ 0
    · simp only [coords, ite_eq_left h10, Prod.mk.injEq] at he
      grind only [entry 0 0 he.1, entry 1 0 he.2, eqn 0 0, eqn 1 0]
    by_cases h01 : A 0 1 ≠ 0
    · simp only [coords, ite_eq_right h10, ite_eq_left h01, Prod.mk.injEq] at he
      grind only [entry 0 1 he.1, entry 1 1 he.2, eqn 0 1, eqn 1 1]
    have hdiag : A 0 0 ≠ A 1 1 := by
      intro heq
      apply ha
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨A 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [scalar_apply, diagonal, heq, not_not.mp h10, not_not.mp h01]
    simp only [coords, ite_eq_right h10, ite_eq_right h01, Prod.mk.injEq] at he
    grind only [entry 0 0 he.1, entry 1 1 he.2, eqn 0 1, eqn 1 0]
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card] using
    Nat.card_le_card_of_injective coords hinj

private lemma card_lifts (N : Subgroup G) : Nat.card (N.comap π) = 10 * Nat.card N := by
  have hL : Nat.card L = 13200 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    decide
  apply Nat.eq_of_mul_eq_mul_right N.index_pos
  rw [mul_assoc, N.card_mul_index, card_projective, ← N.index_comap_of_surjective
    (f := π) ProjGenLinGroup.mk_surjective, Subgroup.card_mul_index, hL]
  decide

private lemma nilpotent_order_le (N : Subgroup G) [Group.IsNilpotent N] : Nat.card N ≤ 12 := by
  by_contra! hlarge
  have hd : Nat.card N ∣ 8 * 3 * 5 * 11 := by
    change Nat.card N ∣ 1320
    rw [← card_projective]
    exact N.card_subgroup_dvd_card
  obtain ⟨p, hp, hgt, hdvd⟩ : ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ Nat.card N := by
    by_cases h₃ : 3 ∣ Nat.card N
    · exact ⟨3, by decide, by decide, h₃⟩
    by_cases h₅ : 5 ∣ Nat.card N
    · exact ⟨5, by decide, by decide, h₅⟩
    by_cases h₁₁ : 11 ∣ Nat.card N
    · exact ⟨11, by decide, by decide, h₁₁⟩
    have cancel (q : ℕ) (hq : q.Prime) (hqN : ¬q ∣ Nat.card N) {k : ℕ}
        (h : Nat.card N ∣ k * q) : Nat.card N ∣ k :=
      (hq.coprime_iff_not_dvd.mpr hqN).symm.dvd_of_dvd_mul_right h
    have hsmall := cancel 3 (by decide) h₃ (cancel 5 (by decide) h₅ (cancel 11 (by decide) h₁₁ hd))
    have := Nat.le_of_dvd (by decide : 0 < 8) hsmall
    omega
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (Group.IsNilpotent.prime_dvd_card_center hdvd)
  obtain ⟨A, hA⟩ := ProjGenLinGroup.mk_surjective (z.val.val : G)
  have hord : orderOf (π A) = p := by
    rw [show π A = z.val.val from hA, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hsq : π A ^ 2 ≠ 1 := fun h => by
    have := Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one h)
    omega
  have hnon : π A ≠ 1 := fun h => hsq (by simp [h])
  have hc (B : N.comap π) : Commute B.val.val A.val := by
    apply commute_of_projective (trace_ne_zero hsq)
    change π B.val * ProjGenLinGroup.mk A = ProjGenLinGroup.mk A * π B.val
    rw [hA]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property ⟨π B.val, B.property⟩)
  have hbound := card_commuting_lifts (N.comap π) hnon hc
  rw [card_lifts] at hbound
  omega

/-- **The class number can exceed the order of every nilpotent subgroup.** There is a finite group
$G$ such that the number $k(G)$ of conjugacy classes of $G$ is greater than $|N|$ for every
nilpotent subgroup $N$ of $G$.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 14.54 (M. W. Liebeck, L. Pyber); resolution: S. Tertooy, Class numbers and nilpotent
subgroups of PGL(2,q), preprint, arXiv:2606.21404 (2026), abstract: for certain odd prime powers q,
k(PGL(2,q)) exceeds the order of every nilpotent subgroup; the Kourovka Notebook (21st issue) marks
14.54 solved (No, not always), https://arxiv.org/abs/2606.21404.
-/
theorem classNumberAtMostNilpotentSubgroupOrder_refuted :
    ¬ classNumberAtMostNilpotentSubgroupOrder := by
  intro h
  obtain ⟨N, hN, hcard⟩ := h G
  have := nilpotent_order_le N
  have := class_number_lower
  omega

end MathlibExt.GroupTheory.ClassNumberNilpotentSubgroupKourovka14Problem54Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow.lean`
and
`P2M/Sol/S_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open MvPolynomial

/-- The three relations `xy - p`, `y ^ n` and `x ^ b - x ^ a` in
`ℤ[x, y]`, with the two variables indexed by `Bool`. -/
public noncomputable def truncatedDieudonneRelations (p n a b : ℕ) :
    Set (MvPolynomial Bool ℤ) :=
  {X true * X false - C (p : ℤ), X false ^ n, X true ^ b - X true ^ a}

/-- The relation set consists exactly of the three displayed polynomials. -/
public theorem truncatedDieudonneRelations_eq (p n a b : ℕ) :
    truncatedDieudonneRelations p n a b =
      {X true * X false - C (p : ℤ), X false ^ n,
        X true ^ b - X true ^ a} :=
  rfl

noncomputable section

namespace TruncatedDieudonneCount


private abbrev I (p n a b : ℕ) : Ideal (MvPolynomial Bool ℤ) :=
  Ideal.span (truncatedDieudonneRelations p n a b)

private abbrev E (p n a b : ℕ) : Type := MvPolynomial Bool ℤ ⧸ I p n a b

variable {p n a b : ℕ}

private abbrev mk : MvPolynomial Bool ℤ →+* E p n a b := Ideal.Quotient.mk (I p n a b)

private abbrev u : E p n a b := mk (X true)
private abbrev v : E p n a b := mk (X false)

private theorem u_mul_v : (u : E p n a b) * v = (p : E p n a b) := by
  have h : (mk (X true * X false - C (p : ℤ)) : E p n a b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (by simp [truncatedDieudonneRelations]))
  rw [map_sub, map_mul, sub_eq_zero] at h
  rw [h, eq_intCast, map_intCast, Int.cast_natCast]

private theorem v_pow_n : (v : E p n a b) ^ n = 0 := by
  have h : (mk (X false ^ n) : E p n a b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (by simp [truncatedDieudonneRelations]))
  rwa [map_pow] at h

private theorem u_pow_b : (u : E p n a b) ^ b = u ^ a := by
  have h : (mk (X true ^ b - X true ^ a) : E p n a b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.subset_span (by simp [truncatedDieudonneRelations]))
  rwa [map_sub, map_pow, map_pow, sub_eq_zero] at h

private def comb (c : Fin b → ℤ) : E p n a b := ∑ i : Fin b, (c i : E p n a b) * u ^ (i : ℕ)

private theorem comb_add (c c' : Fin b → ℤ) :
    comb (p := p) (n := n) (a := a) (c + c') = comb c + comb c' := by
  unfold comb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, Int.cast_add, add_mul]

private theorem comb_zero : comb (p := p) (n := n) (a := a) (0 : Fin b → ℤ) = 0 := by
  unfold comb
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, Int.cast_zero, zero_mul]

private theorem comb_single (i : Fin b) (c : ℤ) :
    comb (p := p) (n := n) (a := a) (Pi.single i c) = (c : E p n a b) * u ^ (i : ℕ) := by
  classical
  unfold comb
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, Int.cast_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem exists_comb_mul_u (hab : a < b) (c : Fin b → ℤ) :
    ∃ c' : Fin b → ℤ, comb (p := p) (n := n) (a := a) c * u = comb c' := by
  classical
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  refine ⟨Fin.cons 0 (fun i : Fin b' => c (Fin.castSucc i)) +
    Pi.single ⟨a, hab⟩ (c (Fin.last b')), ?_⟩
  rw [comb_add, comb_single]
  unfold comb
  rw [Finset.sum_mul, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Int.cast_zero, zero_mul, zero_add, Fin.cons_succ, Fin.val_castSucc,
    Fin.val_succ, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_succ]
  · rw [mul_assoc, ← pow_succ, u_pow_b]

private theorem exists_normalForm (hab : a < b) (x : E p n a b) :
    ∃ (c : Fin b → ℤ) (y : E p n a b), x = comb c + v * y := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction P using MvPolynomial.induction_on with
  | C z =>
    refine ⟨Pi.single ⟨0, by omega⟩ z, 0, ?_⟩
    rw [comb_single, mul_zero, add_zero, eq_intCast, map_intCast]
    change (z : E p n a b) = (z : E p n a b) * u ^ (0 : ℕ)
    rw [pow_zero, mul_one]
  | add P Q hP hQ =>
    obtain ⟨c, y, hc⟩ := hP
    obtain ⟨c', y', hc'⟩ := hQ
    refine ⟨c + c', y + y', ?_⟩
    rw [map_add, hc, hc', comb_add, mul_add]
    abel
  | mul_X P s hP =>
    obtain ⟨c, y, hc⟩ := hP
    rw [map_mul, hc]
    cases s with
    | false =>
      refine ⟨0, comb c + v * y, ?_⟩
      change (comb c + v * y) * v = _
      rw [comb_zero, zero_add, mul_comm]
    | true =>
      obtain ⟨c', hc'⟩ := exists_comb_mul_u (p := p) (n := n) hab c
      refine ⟨c', y * u, ?_⟩
      change (comb c + v * y) * u = _
      rw [add_mul, hc', mul_assoc]

private abbrev Ev (p n a b m : ℕ) : Type := E p n a b ⧸ Ideal.span {(v : E p n a b) ^ m}

private theorem natCast_p_mem_span_v : (p : E p n a b) ∈ Ideal.span {(v : E p n a b) ^ 1} := by
  rw [pow_one, Ideal.mem_span_singleton', ← u_mul_v]
  exact ⟨u, rfl⟩

private theorem finite_and_card_Ev_one (hp : 0 < p) (hab : a < b) :
    Finite (Ev p n a b 1) ∧ Nat.card (Ev p n a b 1) ≤ p ^ b := by
  haveI : NeZero p := ⟨hp.ne'⟩
  let θ : (Fin b → ZMod p) → Ev p n a b 1 := fun c =>
    Ideal.Quotient.mk _ (comb fun i => ((c i).val : ℤ))
  have hθ : Function.Surjective θ := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, y, rfl⟩ := exists_normalForm hab x
    refine ⟨fun i => (c i : ZMod p), ?_⟩
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]

    have key : ∀ i : Fin b, ((((c i : ZMod p)).val : ℤ) : E p n a b) *
        u ^ (i : ℕ) - (c i : E p n a b) * u ^ (i : ℕ) =
        (p : E p n a b) * ((-(c i / p : ℤ) : E p n a b) * u ^ (i : ℕ)) := by
      intro i
      rw [ZMod.val_intCast, ← sub_mul, ← mul_assoc, ← Int.cast_sub,
        ← Int.cast_natCast (R := E p n a b) p,
        ← Int.cast_neg, ← Int.cast_mul]
      congr 2
      rw [Int.emod_def]
      ring
    have hdiff : (comb (p := p) (n := n) (a := a)
        fun i => (((c i : ZMod p)).val : ℤ)) - (comb c + v * y) =
        (p : E p n a b) * (∑ i : Fin b, (-(c i / p : ℤ) : E p n a b) * u ^ (i : ℕ)) - v * y := by
      unfold comb
      rw [Finset.mul_sum, ← sub_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => key i
    rw [hdiff]
    refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ natCast_p_mem_span_v) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by rw [pow_one]; rfl))
  refine ⟨Finite.of_surjective θ hθ, ?_⟩
  calc Nat.card (Ev p n a b 1) ≤ Nat.card (Fin b → ZMod p) := Nat.card_le_card_of_surjective θ hθ
    _ = p ^ b := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem span_succ_le (m : ℕ) :
    Ideal.span {(v : E p n a b) ^ (m + 1)} ≤ Ideal.span {(v : E p n a b) ^ m} := by
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow _ (Nat.le_succ m)

private def red (m : ℕ) : Ev p n a b (m + 1) →+* Ev p n a b m :=
  Ideal.Quotient.factor (span_succ_le m)

private theorem red_surjective (m : ℕ) :
    Function.Surjective (red (p := p) (n := n) (a := a) (b := b) m) :=
  Ideal.Quotient.factor_surjective _

private theorem card_ker_red_le (hp : 0 < p) (hab : a < b) (m : ℕ) :
    Finite (red (p := p) (n := n) (a := a) (b := b) m).toAddMonoidHom.ker ∧
      Nat.card (red (p := p) (n := n) (a := a) (b := b) m).toAddMonoidHom.ker ≤ p ^ b := by
  obtain ⟨hfin, hcard⟩ := finite_and_card_Ev_one (n := n) hp hab
  haveI := hfin
  let s : Ev p n a b 1 → (red (p := p) (n := n) (a := a) (b := b) m).toAddMonoidHom.ker := fun x =>
    ⟨Ideal.Quotient.mk _ (Quotient.out x * (v : E p n a b) ^ m), by
      rw [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, red,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)⟩
  have hs : Function.Surjective s := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, red,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
    obtain ⟨r, rfl⟩ := hy
    refine ⟨Ideal.Quotient.mk _ r, Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (Quotient.out _ * (v : E p n a b) ^ m) =
      Ideal.Quotient.mk _ (r * (v : E p n a b) ^ m)

    have hdiff : (Quotient.out
        (Ideal.Quotient.mk (Ideal.span {(v : E p n a b) ^ 1}) r) : E p n a b) - r ∈
        Ideal.span {(v : E p n a b) ^ 1} := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hdiff
    have hout : (Quotient.out
        (Ideal.Quotient.mk (Ideal.span {(v : E p n a b) ^ 1}) r) : E p n a b) =
        r + z * v ^ 1 := by rw [hz]; abel
    rw [hout, add_mul, map_add, add_eq_left, Ideal.Quotient.eq_zero_iff_mem, pow_one, mul_assoc,
      ← pow_succ']
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact ⟨Finite.of_surjective s hs, le_trans (Nat.card_le_card_of_surjective s hs) hcard⟩

private theorem finite_and_card_Ev (hp : 0 < p) (hab : a < b) (m : ℕ) :
    Finite (Ev p n a b m) ∧ Nat.card (Ev p n a b m) ≤ (p ^ b) ^ m := by
  induction m with
  | zero =>
    have htop : Ideal.span {(v : E p n a b) ^ 0} = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (Ev p n a b 0) := Ideal.Quotient.subsingleton_iff.2 htop
    haveI : Finite (Ev p n a b 0) := Finite.of_subsingleton
    exact ⟨inferInstance, by
      rw [pow_zero]; exact Finite.card_le_one_iff_subsingleton.2 inferInstance⟩
  | succ m ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨hfinK, hcardK⟩ := card_ker_red_le (n := n) hp hab m
    haveI := hfin
    haveI := hfinK
    set K := (red (p := p) (n := n) (a := a) (b := b) m).toAddMonoidHom.ker with hK
    have hq : Nat.card (Ev p n a b (m + 1) ⧸ K) = Nat.card (Ev p n a b m) :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
        (red (p := p) (n := n) (a := a) (b := b) m).toAddMonoidHom (red_surjective m)).toEquiv
    haveI : Finite (Ev p n a b (m + 1) ⧸ K) :=
      Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivOfSurjective _
        (red_surjective (p := p) (n := n) (a := a) (b := b) m)).toEquiv.symm
    have hprod := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
    have hne : Nat.card (Ev p n a b (m + 1)) ≠ 0 := by
      rw [hprod]
      exact mul_ne_zero (Nat.card_pos (α := Ev p n a b (m + 1) ⧸ K)).ne' (Nat.card_pos (α := K)).ne'
    refine ⟨Nat.finite_of_card_ne_zero hne, ?_⟩
    rw [hprod, hq, pow_succ (p ^ b) m]
    exact Nat.mul_le_mul hcard hcardK

private theorem finite_and_card_E (hp : 0 < p) (hab : a < b) :
    Finite (E p n a b) ∧ Nat.card (E p n a b) ≤ p ^ (n * b) := by
  obtain ⟨hfin, hcard⟩ := finite_and_card_Ev (n := n) hp hab n
  haveI := hfin
  have hbot : Ideal.span {(v : E p n a b) ^ n} = ⊥ := by
    rw [v_pow_n, Ideal.span_singleton_eq_bot]
  let e : Ev p n a b n ≃+* E p n a b := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _)
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
  rw [← Nat.card_congr e.toEquiv, mul_comm, pow_mul]
  exact hcard
end TruncatedDieudonneCount

end

/-- The quotient of `ℤ[x, y]` by the relations `xy - p`, `y ^ n` and
`x ^ b - x ^ a` is finite, of cardinality at most `p ^ (n * b)`, for
`0 < p` and `a < b`. -/
public theorem MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
    (p : ℕ) (hp : 0 < p) (n a b : ℕ) (hab : a < b) :
    Finite (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n,
          MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ∧
      Nat.card (MvPolynomial Bool ℤ ⧸ Ideal.span
        ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
          MvPolynomial.X false ^ n,
          MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} :
          Set (MvPolynomial Bool ℤ))) ≤ p ^ (n * b) :=
  TruncatedDieudonneCount.finite_and_card_E hp hab

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean`
and
`P2M/Sol/S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean`
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

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

private theorem nonempty_zmodSqAddEquiv_of_card_eq_sq {p : ℕ} (hp : p.Prime)
    (M : Type*) [AddCommGroup M] [Module (ZMod p) M]
    (hcard : Nat.card M = p ^ 2) :
    Nonempty ((ZMod p × ZMod p) ≃+ M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite M :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) M = 2 := by
    have hcard2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
    rw [hcard, Nat.card_zmod] at hcard2
    exact (Nat.pow_right_injective hp.two_le hcard2).symm
  exact ⟨((Module.finBasisOfFinrankEq (ZMod p) M hfr).equivFun.trans
    (LinearEquiv.finTwoArrow (R := ZMod p) (M := ZMod p))).symm.toAddEquiv⟩

private def pSmulHom (M : Type*) [AddCommGroup M] (p : ℕ) : M →+ M :=
  AddMonoidHom.mk' (fun t => p • t) fun a b => smul_add p a b

private lemma pSmulHom_apply (M : Type*) [AddCommGroup M] (p : ℕ) (t : M) :
    pSmulHom M p t = p • t := rfl

private def pSmulHomKerEquivTorsionBy (M : Type*) [AddCommGroup M] (p : ℕ) :
    (pSmulHom M p).ker ≃ Submodule.torsionBy ℤ M (p : ℤ) where
  toFun T := ⟨(T : M), by
    have hT := T.2
    rw [AddMonoidHom.mem_ker, pSmulHom_apply] at hT
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul ℤ p ((T : M))]
    exact hT⟩
  invFun T := ⟨(T : M), by
    have hT := T.2
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul ℤ p ((T : M))] at hT
    rw [AddMonoidHom.mem_ker, pSmulHom_apply]
    exact hT⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem forall_exists_zsmul_pair_of_step {M : Type*} [AddCommGroup M] {p k : ℕ}
    {x y : M}
    (hexp : ∀ t : M, p ^ k • t = 0)
    (hstep : ∀ t : M, ∃ (a b : ℤ) (s : M), t = a • x + b • y + (p : ℤ) • s) :
    ∀ t : M, ∃ a b : ℤ, t = a • x + b • y := by
  have hiter : ∀ (j : ℕ) (t : M), ∃ (a b : ℤ) (s : M),
      t = a • x + b • y + ((p : ℤ)) ^ j • s := by
    intro j
    induction j with
    | zero =>
      intro t
      exact ⟨0, 0, t, by simp⟩
    | succ j ih =>
      intro t
      obtain ⟨a, b, s, hs⟩ := ih t
      obtain ⟨a', b', s', hs'⟩ := hstep s
      refine ⟨a + (p : ℤ) ^ j * a', b + (p : ℤ) ^ j * b', s', ?_⟩
      calc t = a • x + b • y + (p : ℤ) ^ j • s := hs
        _ = a • x + b • y + (p : ℤ) ^ j • (a' • x + b' • y + (p : ℤ) • s') := by
            rw [← hs']
        _ = a • x + b • y + (((p : ℤ) ^ j * a') • x + ((p : ℤ) ^ j * b') • y
              + ((p : ℤ) ^ j * (p : ℤ)) • s') := by
            rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        _ = (a + (p : ℤ) ^ j * a') • x + (b + (p : ℤ) ^ j * b') • y
              + (p : ℤ) ^ (j + 1) • s' := by
            rw [add_smul, add_smul, pow_succ]
            abel
  intro t
  obtain ⟨a, b, s, hs⟩ := hiter k t
  refine ⟨a, b, ?_⟩
  have hzero : ((p : ℤ)) ^ k • s = 0 := by
    have hcast : ((p : ℤ)) ^ k • s = (p ^ k : ℕ) • s := by
      rw [← Nat.cast_pow, natCast_zsmul]
    rw [hcast]
    exact hexp s
  rw [hs, hzero, add_zero]

private theorem nonempty_zmodPowSqAddEquiv_of_span_pair {n : ℕ} (hn : n ≠ 0)
    (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    (hcard : Nat.card M = n ^ 2) (x y : M)
    (hgen : ∀ t : M, ∃ a b : ℤ, t = a • x + b • y) :
    Nonempty ((ZMod n × ZMod n) ≃+ M) := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Finite M :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn)
  let f : (ZMod n × ZMod n) →+ M := AddMonoidHom.mk' (fun c => c.1 • x + c.2 • y) (by
    intro c d
    show (c.1 + d.1) • x + (c.2 + d.2) • y = (c.1 • x + c.2 • y) + (d.1 • x + d.2 • y)
    rw [add_smul, add_smul]
    abel)
  have hfsurj : Function.Surjective f := by
    intro t
    obtain ⟨a, b, ht⟩ := hgen t
    refine ⟨((a : ZMod n), (b : ZMod n)), ?_⟩
    show ((a : ℤ) : ZMod n) • x + ((b : ℤ) : ZMod n) • y = t
    rw [Int.cast_smul_eq_zsmul (ZMod n) a x, Int.cast_smul_eq_zsmul (ZMod n) b y, ht]
  have hcards : Nat.card (ZMod n × ZMod n) = Nat.card M := by
    rw [Nat.card_prod, Nat.card_zmod, hcard]
    ring
  exact ⟨AddEquiv.ofBijective f
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hfsurj, hcards⟩)⟩

private theorem nonempty_zmodPowSqAddEquiv_of_card_pow {p : ℕ} (hp : p.Prime) (k : ℕ)
    (M : Type*) [AddCommGroup M]
    (hexp : ∀ t : M, p ^ k • t = 0)
    (hcard : Nat.card M = p ^ (2 * k))
    (hcardp : Nat.card (Submodule.torsionBy ℤ M (p : ℤ)) = p ^ 2) :
    Nonempty ((ZMod (p ^ k) × ZMod (p ^ k)) ≃+ M) := by
  haveI : Finite M :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have h1 : Nat.card M = 1 := by simpa using hcard
    have hle : Nat.card (Submodule.torsionBy ℤ M (p : ℤ)) ≤ Nat.card M :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [hcardp, h1] at hle
    exact absurd (le_trans (Nat.pow_le_pow_left hp.two_le 2) hle) (by norm_num)
  · set K : AddSubgroup M := (pSmulHom M p).ker with hKdef
    set R : AddSubgroup M := (pSmulHom M p).range with hRdef
    haveI : Nonempty R := ⟨0⟩
    have hKcard : Nat.card K = p ^ 2 := by
      rw [hKdef, Nat.card_congr (pSmulHomKerEquivTorsionBy M p)]
      exact hcardp
    have hMK : Nat.card K * K.index = Nat.card M := AddSubgroup.card_mul_index K
    have hKR : K.index = Nat.card R := by
      rw [hKdef, hRdef]
      exact AddSubgroup.index_ker (pSmulHom M p)
    have hMR : Nat.card R * R.index = Nat.card M := AddSubgroup.card_mul_index R
    have hRQ : R.index = Nat.card (M ⧸ R) := AddSubgroup.index_eq_card R
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hQcard : Nat.card (M ⧸ R) = p ^ 2 := by
      have h1 : Nat.card K * Nat.card R = Nat.card M := by rw [← hKR]; exact hMK
      have h2 : Nat.card R * Nat.card (M ⧸ R) = Nat.card M := by rw [← hRQ]; exact hMR
      have h3 : Nat.card R * Nat.card (M ⧸ R) = Nat.card R * Nat.card K := by
        rw [h2, ← h1, mul_comm]
      rw [Nat.eq_of_mul_eq_mul_left hRpos h3, hKcard]
    have hQkill : ∀ q : M ⧸ R, p • q = 0 := by
      intro q
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective R q
      rw [← map_nsmul]
      have hmem : p • t ∈ R := by
        rw [hRdef]
        exact AddMonoidHom.mem_range.mpr ⟨t, pSmulHom_apply M p t⟩
      rwa [← QuotientAddGroup.ker_mk' R, AddMonoidHom.mem_ker] at hmem
    obtain ⟨E⟩ : Nonempty ((ZMod p × ZMod p) ≃+ (M ⧸ R)) := by
      letI : Module (ZMod p) (M ⧸ R) := AddCommGroup.zmodModule hQkill
      exact nonempty_zmodSqAddEquiv_of_card_eq_sq hp (M ⧸ R) hQcard
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective R (E ((1 : ZMod p), (0 : ZMod p)))
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective R (E ((0 : ZMod p), (1 : ZMod p)))
    have hstep : ∀ t : M, ∃ (a b : ℤ) (s : M), t = a • x + b • y + (p : ℤ) • s := by
      intro t
      obtain ⟨a, ha⟩ := ZMod.intCast_surjective ((E.symm ((QuotientAddGroup.mk' R) t)).1)
      obtain ⟨b, hb⟩ := ZMod.intCast_surjective ((E.symm ((QuotientAddGroup.mk' R) t)).2)
      have hxy : (QuotientAddGroup.mk' R) (a • x + b • y) =
          (QuotientAddGroup.mk' R) t := by
        rw [map_add, map_zsmul, map_zsmul, hx, hy, ← map_zsmul E, ← map_zsmul E,
          ← map_add E]
        have hpair : a • ((1 : ZMod p), (0 : ZMod p)) + b • ((0 : ZMod p), (1 : ZMod p))
            = E.symm ((QuotientAddGroup.mk' R) t) := by
          apply Prod.ext
          · simpa [Int.smul_one_eq_cast] using ha
          · simpa [Int.smul_one_eq_cast] using hb
        rw [hpair, AddEquiv.apply_symm_apply]
      have h0 : (QuotientAddGroup.mk' R) (t - (a • x + b • y)) = 0 := by
        rw [map_sub, hxy, sub_self]
      have hmem : t - (a • x + b • y) ∈ R := by
        rwa [← QuotientAddGroup.ker_mk' R, AddMonoidHom.mem_ker]
      rw [hRdef] at hmem
      obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp hmem
      rw [pSmulHom_apply] at hs
      refine ⟨a, b, s, ?_⟩
      rw [natCast_zsmul, hs]
      abel
    have hgen : ∀ t : M, ∃ a b : ℤ, t = a • x + b • y :=
      forall_exists_zsmul_pair_of_step hexp hstep
    letI : Module (ZMod (p ^ k)) M := AddCommGroup.zmodModule hexp
    exact nonempty_zmodPowSqAddEquiv_of_span_pair (pow_ne_zero k hp.ne_zero) M
      (by rw [hcard, show 2 * k = k * 2 from Nat.mul_comm 2 k, pow_mul]) x y hgen

private def torsionByPowPTorsionEquiv {A : Type*} [AddCommGroup A] (p k : ℕ)
    (hk : k ≠ 0) :
    (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) (p : ℤ)) ≃
      (Submodule.torsionBy ℤ A (p : ℤ)) where
  toFun T := ⟨((T : Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) : A), by
    have hT := T.2
    rw [Submodule.mem_torsionBy_iff] at hT
    rw [Submodule.mem_torsionBy_iff]
    exact congrArg Subtype.val hT⟩
  invFun T := ⟨⟨(T : A), by
      rw [Submodule.mem_torsionBy_iff]
      have hT : (p : ℤ) • (T : A) = 0 := by
        have := T.2
        rwa [Submodule.mem_torsionBy_iff] at this
      have hkk : ((p ^ k : ℕ) : ℤ) = ((p ^ (k - 1) : ℕ) : ℤ) * (p : ℤ) := by
        push_cast
        rw [← pow_succ]
        congr 1
        omega
      rw [hkk, mul_smul, hT, smul_zero]⟩, by
    rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    have hT : (p : ℤ) • (T : A) = 0 := by
      have := T.2
      rwa [Submodule.mem_torsionBy_iff] at this
    exact hT⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

private theorem nonempty_zmodPowSqAddEquiv_torsionBy_of_card_pow {A : Type*}
    [AddCommGroup A] {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) = p ^ (2 * k))
    (hcardp : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ 2) :
    Nonempty ((ZMod (p ^ k) × ZMod (p ^ k)) ≃+
      Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) := by
  refine nonempty_zmodPowSqAddEquiv_of_card_pow hp k _ ?_ hcard ?_
  · intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ (p ^ k) t]
    exact Submodule.smul_torsionBy _ t
  · rw [← hcardp]
    exact Nat.card_congr (torsionByPowPTorsionEquiv p k hk)

private def torsionByMulCoprimeSplitAddEquiv {A : Type*} [AddCommGroup A] (M N : ℕ)
    (a b : ℤ)
    (hab : (M : ℤ) * a + (N : ℤ) * b = 1) :
    Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ) ≃+
      Submodule.torsionBy ℤ A (M : ℤ) × Submodule.torsionBy ℤ A (N : ℤ) where
  toFun t :=
    (⟨((N : ℤ) * b) • (t : A), by
        have ht : ((M * N : ℕ) : ℤ) • (t : A) = 0 := by
          have h2 := t.2
          rwa [Submodule.mem_torsionBy_iff] at h2
        rw [Submodule.mem_torsionBy_iff, smul_smul,
          show (M : ℤ) * ((N : ℤ) * b) = b * ((M * N : ℕ) : ℤ) by push_cast; ring,
          ← smul_smul, ht, smul_zero]⟩,
     ⟨((M : ℤ) * a) • (t : A), by
        have ht : ((M * N : ℕ) : ℤ) • (t : A) = 0 := by
          have h2 := t.2
          rwa [Submodule.mem_torsionBy_iff] at h2
        rw [Submodule.mem_torsionBy_iff, smul_smul,
          show (N : ℤ) * ((M : ℤ) * a) = a * ((M * N : ℕ) : ℤ) by push_cast; ring,
          ← smul_smul, ht, smul_zero]⟩)
  invFun uv := ⟨(uv.1 : A) + (uv.2 : A), by
    have hu : (M : ℤ) • (uv.1 : A) = 0 := by
      have h2 := uv.1.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    have hv : (N : ℤ) • (uv.2 : A) = 0 := by
      have h2 := uv.2.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    rw [Submodule.mem_torsionBy_iff, smul_add,
      show ((M * N : ℕ) : ℤ) • (uv.1 : A) = 0 by
        rw [show ((M * N : ℕ) : ℤ) = (N : ℤ) * (M : ℤ) by push_cast; ring,
          ← smul_smul, hu, smul_zero],
      show ((M * N : ℕ) : ℤ) • (uv.2 : A) = 0 by
        rw [show ((M * N : ℕ) : ℤ) = (M : ℤ) * (N : ℤ) by push_cast; ring,
          ← smul_smul, hv, smul_zero],
      add_zero]⟩
  left_inv t := by
    apply Subtype.ext
    show ((N : ℤ) * b) • (t : A) + ((M : ℤ) * a) • (t : A) = (t : A)
    rw [← add_smul, show (N : ℤ) * b + (M : ℤ) * a = 1 by linarith [hab], one_smul]
  right_inv uv := by
    have hu : (M : ℤ) • (uv.1 : A) = 0 := by
      have h2 := uv.1.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    have hv : (N : ℤ) • (uv.2 : A) = 0 := by
      have h2 := uv.2.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    apply Prod.ext
    · apply Subtype.ext
      show ((N : ℤ) * b) • ((uv.1 : A) + (uv.2 : A)) = (uv.1 : A)
      rw [smul_add,
        show ((N : ℤ) * b) • (uv.2 : A) = 0 by
          rw [show (N : ℤ) * b = b * (N : ℤ) by ring, ← smul_smul, hv, smul_zero],
        show ((N : ℤ) * b) • (uv.1 : A) = (uv.1 : A) by
          rw [show (N : ℤ) * b = 1 - (M : ℤ) * a by linarith [hab], sub_smul, one_smul,
            show (M : ℤ) * a = a * (M : ℤ) by ring, ← smul_smul, hu, smul_zero,
            sub_zero],
        add_zero]
    · apply Subtype.ext
      show ((M : ℤ) * a) • ((uv.1 : A) + (uv.2 : A)) = (uv.2 : A)
      rw [smul_add,
        show ((M : ℤ) * a) • (uv.1 : A) = 0 by
          rw [show (M : ℤ) * a = a * (M : ℤ) by ring, ← smul_smul, hu, smul_zero],
        show ((M : ℤ) * a) • (uv.2 : A) = (uv.2 : A) by
          rw [show (M : ℤ) * a = 1 - (N : ℤ) * b by linarith [hab], sub_smul, one_smul,
            show (N : ℤ) * b = b * (N : ℤ) by ring, ← smul_smul, hv, smul_zero,
            sub_zero],
        zero_add]
  map_add' t s := by
    apply Prod.ext
    · apply Subtype.ext
      show ((N : ℤ) * b) • ((t : A) + (s : A))
        = ((N : ℤ) * b) • (t : A) + ((N : ℤ) * b) • (s : A)
      rw [smul_add]
    · apply Subtype.ext
      show ((M : ℤ) * a) • ((t : A) + (s : A))
        = ((M : ℤ) * a) • (t : A) + ((M : ℤ) * a) • (s : A)
      rw [smul_add]

private theorem nonempty_torsionByMulAddEquiv_prod_of_coprime {A : Type*}
    [AddCommGroup A] {M N : ℕ} (hcop : Nat.Coprime M N) :
    Nonempty (Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ) ≃+
      Submodule.torsionBy ℤ A (M : ℤ) × Submodule.torsionBy ℤ A (N : ℤ)) := by
  have hbez : (M : ℤ) * Nat.gcdA M N + (N : ℤ) * Nat.gcdB M N = 1 := by
    have h := Nat.gcd_eq_gcd_ab M N
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact_mod_cast h.symm
  exact ⟨torsionByMulCoprimeSplitAddEquiv M N (Nat.gcdA M N) (Nat.gcdB M N) hbez⟩

private def zmodSqCrtAddEquiv {M N : ℕ} (hcop : Nat.Coprime M N) :
    (ZMod (M * N) × ZMod (M * N)) ≃+ (ZMod M × ZMod M) × (ZMod N × ZMod N) :=
  (AddEquiv.prodCongr (ZMod.chineseRemainder hcop).toAddEquiv
    (ZMod.chineseRemainder hcop).toAddEquiv).trans
    (AddEquiv.prodProdProdComm (ZMod M) (ZMod N) (ZMod M) (ZMod N))

private theorem nonempty_zmodSqAddEquiv_torsionBy_mul_of_coprime {A : Type*}
    [AddCommGroup A] {M N : ℕ} (hcop : Nat.Coprime M N)
    (hM : Nonempty ((ZMod M × ZMod M) ≃+ Submodule.torsionBy ℤ A (M : ℤ)))
    (hN : Nonempty ((ZMod N × ZMod N) ≃+ Submodule.torsionBy ℤ A (N : ℤ))) :
    Nonempty ((ZMod (M * N) × ZMod (M * N)) ≃+
      Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ)) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eN⟩ := hN
  obtain ⟨eT⟩ := nonempty_torsionByMulAddEquiv_prod_of_coprime (A := A) hcop
  exact ⟨((zmodSqCrtAddEquiv hcop).trans (AddEquiv.prodCongr eM eN)).trans eT.symm⟩

private theorem nonempty_zmodSqAddEquiv_torsionBy_one {A : Type*} [AddCommGroup A] :
    Nonempty ((ZMod 1 × ZMod 1) ≃+ Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) := by
  haveI : Subsingleton (Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := x.2; have hy := y.2
    rw [Submodule.mem_torsionBy_iff] at hx hy
    simp only [Nat.cast_one, one_smul] at hx hy
    rw [hx, hy]
  refine ⟨AddEquiv.ofBijective
    (0 : ZMod 1 × ZMod 1 →+ Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) ⟨?_, ?_⟩⟩
  · intro a b _
    exact Subsingleton.elim a b
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

namespace AddCommGroup

/-- If every divisor torsion subgroup of an abelian group `A` has square
cardinality `d ^ 2`, then the `n`-torsion subgroup is a square of `ZMod n`. -/
public theorem nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hc : Nat.card (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) = p ^ (2 * k) := by
        rw [hcard (p ^ k) dvd_rfl, ← pow_mul, Nat.mul_comm]
      have hcp : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ 2 :=
        hcard p (dvd_pow_self p hk.ne')
      exact nonempty_zmodPowSqAddEquiv_torsionBy_of_card_pow hp hk.ne' hc hcp
  | zero => exact absurd rfl hn
  | one => exact nonempty_zmodSqAddEquiv_torsionBy_one
  | coprime a b _ _ hab iha ihb =>
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
      exact nonempty_zmodSqAddEquiv_torsionBy_mul_of_coprime hab
        (iha ha0 fun d hd => hcard d (hd.mul_right b))
        (ihb hb0 fun d hd => hcard d (hd.mul_left a))

end AddCommGroup

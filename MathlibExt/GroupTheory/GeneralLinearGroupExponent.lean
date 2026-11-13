/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
/-- A prime does not divide one less than a positive power of itself. -/
private theorem prime_not_dvd_pow_sub_one (p i : ℕ) (hp : p.Prime) :
    ¬ p ∣ p ^ (i + 1) - 1 := by
  intro h
  have h1 : p ∣ p ^ (i + 1) := dvd_pow_self p (by omega)
  have h2 : p ∣ p ^ (i + 1) - (p ^ (i + 1) - 1) := Nat.dvd_sub h1 h
  have h3 : p ^ (i + 1) - (p ^ (i + 1) - 1) = 1 := by
    have hpos : 1 ≤ p ^ (i + 1) := Nat.one_le_pow _ _ hp.pos
    omega
  rw [h3] at h2
  exact hp.ne_one (Nat.dvd_one.mp h2)

private theorem coprime_pow_clog_lcm (p m : ℕ) (hp : p.Prime) :
    Nat.Coprime (p ^ Nat.clog p m)
      ((Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) := by
  have H : ((Finset.range m).prod (fun i => p ^ (i + 1) - 1)).Coprime
      (p ^ Nat.clog p m) := by
    apply Nat.Coprime.prod_left
    intro i _
    exact ((hp.coprime_iff_not_dvd.mpr
      (prime_not_dvd_pow_sub_one p i hp)).pow_left _).symm
  exact Nat.Coprime.coprime_dvd_right (Finset.lcm_dvd_prod _ _) H.symm

private theorem pow_sub_one_eq_divisor_prod (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    p ^ n - 1 = ∏ i ∈ n.divisors, ((Polynomial.cyclotomic i ℤ).eval (p : ℤ)).natAbs := by
  have h1 : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hprod := Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have heval : ∏ i ∈ n.divisors,
      (Polynomial.cyclotomic i ℤ).eval (p : ℤ) = (p : ℤ) ^ n - 1 := by
    calc ∏ i ∈ n.divisors, (Polynomial.cyclotomic i ℤ).eval (p : ℤ)
        = Polynomial.eval (p : ℤ)
          (∏ i ∈ n.divisors, Polynomial.cyclotomic i ℤ) :=
          (Polynomial.eval_prod _ _ _).symm
      _ = Polynomial.eval (p : ℤ) (Polynomial.X ^ n - 1 : Polynomial ℤ) := by
          rw [hprod]
      _ = (p : ℤ) ^ n - 1 := by simp
  have hcast : (((∏ i ∈ n.divisors, ((Polynomial.cyclotomic i ℤ).eval (p : ℤ)).natAbs : ℕ)) : ℤ) =
      ∏ i ∈ n.divisors, (Polynomial.cyclotomic i ℤ).eval (p : ℤ) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact Int.natAbs_of_nonneg (le_of_lt (Polynomial.cyclotomic_pos' i h1))
  have hnat : (((p ^ n - 1 : ℕ)) : ℤ) = (p : ℤ) ^ n - 1 := by
    have hle : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hzz : (((p ^ n - 1 : ℕ)) : ℤ) =
      (((∏ i ∈ n.divisors, ((Polynomial.cyclotomic i ℤ).eval (p : ℤ)).natAbs : ℕ)) : ℤ) := by
    rw [hnat, ← heval, ← hcast]
  exact Nat.cast_injective hzz

private theorem coprime_cycVal_of_not_dvd (p k n : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) (hdvd : ¬ k ∣ n) :
    Nat.Coprime (((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs)
      (((Polynomial.cyclotomic n ℤ).eval (p : ℤ)).natAbs) := by
  by_contra hnc
  have hgcd : Nat.gcd (((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs)
      (((Polynomial.cyclotomic n ℤ).eval (p : ℤ)).natAbs) ≠ 1 := by
    intro h
    exact hnc (Nat.coprime_iff_gcd_eq_one.mpr h)
  obtain ⟨q, hq, hqgcd⟩ := Nat.exists_prime_and_dvd hgcd
  have hqk : q ∣ ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs :=
    hqgcd.trans (Nat.gcd_dvd_left _ _)
  have hqn : q ∣ ((Polynomial.cyclotomic n ℤ).eval (p : ℤ)).natAbs :=
    hqgcd.trans (Nat.gcd_dvd_right _ _)
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hqdvd_k : (q : ℤ) ∣ (Polynomial.cyclotomic k ℤ).eval (p : ℤ) :=
    Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr hqk)
  have hqdvd_n : (q : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval (p : ℤ) :=
    Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr hqn)
  have hq0k : (((Polynomial.cyclotomic k ℤ).eval (p : ℤ) : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hqdvd_k
  have hq0n : (((Polynomial.cyclotomic n ℤ).eval (p : ℤ) : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hqdvd_n
  have hmap_k : ((Polynomial.cyclotomic k ℤ).map
      (Int.castRingHom (ZMod q))) = Polynomial.cyclotomic k (ZMod q) :=
    Polynomial.map_cyclotomic k _
  have hmap_n : ((Polynomial.cyclotomic n ℤ).map
      (Int.castRingHom (ZMod q))) = Polynomial.cyclotomic n (ZMod q) :=
    Polynomial.map_cyclotomic n _
  have hpq : (p : ZMod q) = Int.castRingHom (ZMod q) (p : ℤ) := by simp
  have hroot_k : (Polynomial.cyclotomic k (ZMod q)).IsRoot (p : ZMod q) := by
    rw [← hmap_k, hpq]
    change Polynomial.eval _ _ = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    simpa using hq0k
  have hroot_n : (Polynomial.cyclotomic n (ZMod q)).IsRoot (p : ZMod q) := by
    rw [← hmap_n, hpq]
    change Polynomial.eval _ _ = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    simpa using hq0n
  obtain ⟨a, k', hk'nd, hk'eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) q hq.ne_one
  obtain ⟨b, n', hn'nd, hn'eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) q hq.ne_one
  have hk'ne : (k' : ZMod q) ≠ 0 := fun hz =>
    hk'nd ((ZMod.natCast_eq_zero_iff k' q).mp hz)
  have hn'ne : (n' : ZMod q) ≠ 0 := fun hz =>
    hn'nd ((ZMod.natCast_eq_zero_iff n' q).mp hz)
  have : NeZero (k' : ZMod q) := ⟨hk'ne⟩
  have : NeZero (n' : ZMod q) := ⟨hn'ne⟩
  have hprim_k : IsPrimitiveRoot (p : ZMod q) k' := by
    have h := hk'eq ▸ hroot_k
    exact Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp h
  have hprim_n : IsPrimitiveRoot (p : ZMod q) n' := by
    have h := hn'eq ▸ hroot_n
    exact Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp h
  have hkk' : k' = n' := IsPrimitiveRoot.unique hprim_k hprim_n
  by_cases hab : a ≤ b
  · have hqa : q ^ a ∣ q ^ b := pow_dvd_pow q hab
    have hkd : k' ∣ n' := hkk' ▸ dvd_rfl
    have hkn_dvd : k ∣ n := by
      rw [hk'eq, hn'eq]
      exact mul_dvd_mul hqa hkd
    exact hdvd hkn_dvd
  · have hab : b < a := not_le.mp hab
    have hn'pos : 0 < n' :=
      Nat.pos_of_ne_zero (fun hz => hn'nd (hz ▸ dvd_zero q))
    have hlt : q ^ b < q ^ a := Nat.pow_lt_pow_right hq.one_lt hab
    have hlt2 : q ^ b * n' < q ^ a * n' :=
      Nat.mul_lt_mul_of_pos_right hlt hn'pos
    have hnk : n < k := by
      rw [hn'eq, hk'eq, hkk']
      exact hlt2
    exact absurd hkn (not_lt_of_gt hnk)

private theorem lcm_eq_cyclotomic_prod (p m : ℕ) (hp : p.Prime) :
    (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) =
      ∏ k ∈ Finset.Icc 1 m, ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs := by
  induction m with
  | zero => simp
  | succ m IH =>
    have hL : (Finset.range (m + 1)).lcm (fun i => p ^ (i + 1) - 1) =
        Nat.lcm (p ^ (m + 1) - 1)
          ((Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) := by
      rw [Finset.range_add_one, Finset.lcm_insert]
      rfl
    have hP : (∏ k ∈ Finset.Icc 1 (m + 1),
          ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs) =
        (∏ k ∈ Finset.Icc 1 m,
          ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs) *
          ((Polynomial.cyclotomic (m + 1) ℤ).eval (p : ℤ)).natAbs :=
      Finset.prod_Icc_succ_top (by omega) _
    have hdiv := pow_sub_one_eq_divisor_prod p (m + 1) hp (by omega)
    have hsplit : (m + 1).divisors =
        insert (m + 1) ((Finset.Icc 1 m).filter (fun k => k ∣ m + 1)) := by
      ext k
      simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_Icc]
      constructor
      · rintro ⟨hd, -⟩
        by_cases hkm : k = m + 1
        · exact Or.inl hkm
        · have hle : k ≤ m + 1 := Nat.le_of_dvd (by omega) hd
          have hpos : 0 < k := Nat.pos_of_dvd_of_pos hd (by omega)
          exact Or.inr ⟨⟨by omega, by omega⟩, hd⟩
      · rintro (rfl | ⟨⟨-, -⟩, hd⟩)
        · exact ⟨dvd_rfl, by omega⟩
        · exact ⟨hd, by omega⟩
    have hnotmem : m + 1 ∉
        (Finset.Icc 1 m).filter (fun k => k ∣ m + 1) := by
      intro hmem
      rw [Finset.mem_filter, Finset.mem_Icc] at hmem
      obtain ⟨⟨-, hle⟩, -⟩ := hmem
      omega
    set D := ∏ k ∈ (Finset.Icc 1 m).filter (fun k => k ∣ m + 1),
      ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs with hD
    set A := ∏ k ∈ (Finset.Icc 1 m).filter (fun k => ¬ k ∣ m + 1),
      ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs with hA
    have hdiv2 : p ^ (m + 1) - 1 =
        ((Polynomial.cyclotomic (m + 1) ℤ).eval (p : ℤ)).natAbs * D := by
      rw [hdiv, hsplit, Finset.prod_insert hnotmem]
    have hPm : (∏ k ∈ Finset.Icc 1 m,
        ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs) = D * A := by
      have h := Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 m)
        (fun k => k ∣ m + 1)
        (fun k => ((Polynomial.cyclotomic k ℤ).eval (p : ℤ)).natAbs)
      exact h.symm
    have hcop :
        Nat.Coprime (((Polynomial.cyclotomic (m + 1) ℤ).eval (p : ℤ)).natAbs)
          A := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.prod_left
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨h1, hle⟩, hnd⟩ := hk
      exact coprime_cycVal_of_not_dvd p k (m + 1) h1 (by omega) hnd
    rw [hL, hP, hdiv2, IH, hPm,
      mul_comm (((Polynomial.cyclotomic (m + 1) ℤ).eval (p : ℤ)).natAbs) D,
      Nat.lcm_mul_left, Nat.Coprime.lcm_eq_mul hcop]
    ring

private theorem charpoly_dvd_X_pow_sub_one_of_mem_GL (p m : ℕ) (hp : p.Prime)
    (g : Matrix.GeneralLinearGroup (Fin m) (ZMod p)) :
    (g.val).charpoly ∣ Polynomial.X ^
      (p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set K := AlgebraicClosure (ZMod p) with hK
  set A := g.val with hA
  set χ := A.charpoly with hχ
  set L := (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) with hL
  set femb : ZMod p →+* K := algebraMap (ZMod p) K with hfemb
  have hfinj : Function.Injective femb := RingHom.injective _
  set χK := χ.map femb with hχK
  have hmonic : χ.Monic := Matrix.charpoly_monic _
  have hmonicK : χK.Monic := hmonic.map femb
  have hχK0 : χK ≠ 0 := hmonicK.ne_zero
  have hdet_unit : IsUnit (Matrix.det A) :=
    IsUnit.map Matrix.detMonoidHom ⟨g, hA.symm⟩
  have hdet_eq : Matrix.det A = (-1) ^ Fintype.card (Fin m) * χ.coeff 0 :=
    Matrix.det_eq_sign_charpoly_coeff _
  have heval0 : Polynomial.eval (0 : K) χK = femb (Polynomial.eval 0 χ) := by
    rw [hχK, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Polynomial.coeff_zero_eq_eval_zero]
  have hA1 : ∀ μ ∈ χK.roots, μ ≠ 0 := by
    intro μ hμ h0
    subst h0
    have hroot0 : Polynomial.eval (0 : K) χK = 0 :=
      (Polynomial.mem_roots hχK0).mp hμ
    rw [heval0] at hroot0
    have he0 : Polynomial.eval (0 : ZMod p) χ = 0 :=
      hfinj (by rwa [map_zero])
    have hc0 : χ.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]; exact he0
    rw [hdet_eq, hc0, mul_zero] at hdet_unit
    exact (IsUnit.ne_zero hdet_unit) rfl
  have hlin : ∀ μ ∈ χK.roots,
      Polynomial.X - Polynomial.C μ ∣ Polynomial.X ^ L - 1 := by
    intro μ hμ
    have hμ0 : μ ≠ 0 := hA1 μ hμ
    have hroot : χK.IsRoot μ := (Polynomial.mem_roots hχK0).mp hμ
    have haevalF : Polynomial.aeval μ χ = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot
    have hint : IsIntegral (ZMod p) μ := ⟨χ, hmonic, haevalF⟩
    set E := IntermediateField.adjoin (ZMod p) {μ} with hEdef
    have : Module.Finite (ZMod p) ↥E :=
      (IntermediateField.adjoin.powerBasis hint).finite
    set d := (minpoly (ZMod p) μ).natDegree with hd
    have hd1 : 1 ≤ d := minpoly.natDegree_pos hint
    have hd_le : d ≤ m := by
      have hdiv := minpoly.dvd (ZMod p) μ haevalF
      have hle := Polynomial.natDegree_le_of_dvd hdiv hmonic.ne_zero
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hle
      exact hle
    have hfin : Module.finrank (ZMod p) ↥E = d :=
      IntermediateField.adjoin.finrank hint
    have hcardF : Nat.card (ZMod p) = p := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
    have hcardE : Nat.card ↥E = p ^ d := by
      have hnc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥E)
      rw [hcardF, hfin] at hnc
      exact hnc
    have hmem : μ ∈ IntermediateField.adjoin (ZMod p) {μ} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton μ)
    set μ' : ↥E := ⟨μ, hmem⟩ with hμ'def
    have hμ'coe : ((μ' : ↥E) : K) = μ := rfl
    have hμ'ne : μ' ≠ 0 := by
      intro hz
      apply hμ0
      have hcc := congrArg ((↑) : ↥E → K) hz
      simpa [hμ'coe] using hcc
    set u' := Units.mk0 μ' hμ'ne with hu'def
    have hord_dvd : orderOf u' ∣ p ^ d - 1 := by
      have h := orderOf_dvd_natCard u'
      rw [Nat.card_units, hcardE] at h
      exact h
    have hpow : u' ^ (p ^ d - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd
    have hK : μ ^ (p ^ d - 1) = 1 := by
      have h2 : ((u' ^ (p ^ d - 1)) : ↥E) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
      rw [hu'def, Units.val_mk0] at h2
      have h4 := congrArg ((↑) : ↥E → K) h2
      simpa [hμ'coe] using h4
    have hdivL : p ^ d - 1 ∣ L := by
      have hmem' : d - 1 ∈ Finset.range m :=
        Finset.mem_range.mpr (by omega)
      have h := Finset.dvd_lcm (s := Finset.range m)
        (f := fun i => p ^ (i + 1) - 1) hmem'
      have h2 : p ^ (d - 1 + 1) - 1 = p ^ d - 1 := by
        rw [Nat.sub_add_cancel hd1]
      rwa [h2] at h
    have hμL : μ ^ L = 1 := by
      obtain ⟨t, ht⟩ := hdivL
      rw [ht, pow_mul, hK, one_pow]
    exact Polynomial.dvd_iff_isRoot.mpr (by
      change Polynomial.eval μ (Polynomial.X ^ L - 1) = 0
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hμL, sub_self])
  have hfac : χK =
      (Multiset.map (fun μ => Polynomial.X - Polynomial.C μ) χK.roots).prod :=
    Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits χK) hmonicK
  have hcardroots : χK.roots.card = m := by
    have h1 := Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits χK)
    rw [hχK, Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] at h1
    exact h1.symm
  have hdiv_roots : χK ∣ ((Polynomial.X ^ L - 1 : Polynomial K) ^ m) := by
    have h2 : (Multiset.map (fun _ => (Polynomial.X ^ L - 1 : Polynomial K))
        χK.roots).prod = ((Polynomial.X ^ L - 1 : Polynomial K) ^ m) := by
      rw [Multiset.map_const', Multiset.prod_replicate, hcardroots]
    rw [hfac, ← h2]
    exact Multiset.prod_dvd_prod_of_dvd _ _ (fun μ hμ => hlin μ hμ)
  have hdesc : χ ∣ ((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ m) := by
    have hmap : χ.map femb ∣
        (((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ m).map femb) := by
      have h1 : (((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ m).map femb) =
          ((Polynomial.X ^ L - 1 : Polynomial K) ^ m) := by
        simp
      rw [h1, ← hχK]
      exact hdiv_roots
    exact (Polynomial.map_dvd_map _ hfinj hmonic).mp hmap
  have hpow_le : m ≤ p ^ Nat.clog p m := Nat.le_pow_clog hp.one_lt m
  have hA3 : (((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ m)) ∣
      ((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ (p ^ Nat.clog p m)) :=
    pow_dvd_pow _ hpow_le
  have hfrob : ((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ (p ^ Nat.clog p m)) =
      Polynomial.X ^ (L * p ^ Nat.clog p m) - 1 := by
    have h := sub_pow_char_pow (Polynomial.X ^ L : Polynomial (ZMod p)) 1
      (Nat.clog p m)
    rwa [one_pow, ← pow_mul] at h
  have hN : L * p ^ Nat.clog p m = p ^ Nat.clog p m * L := mul_comm _ _
  have h5 : ((Polynomial.X ^ L - 1 : Polynomial (ZMod p)) ^ (p ^ Nat.clog p m)) ∣
      Polynomial.X ^ (p ^ Nat.clog p m * L) - 1 := by
    have h5' : (Polynomial.X ^ (L * p ^ Nat.clog p m) - 1 : Polynomial (ZMod p)) =
        (Polynomial.X ^ (p ^ Nat.clog p m * L) - 1 : Polynomial (ZMod p)) := by
      rw [hN]
    rw [← h5', ← hfrob]
  exact dvd_trans hdesc (dvd_trans hA3 h5)

private theorem pow_sub_one_dvd_exponent_of_mem_Icc (p m : ℕ) (hp : p.Prime)
    (d : ℕ) (hd : d ∈ Finset.Icc 1 m) : p ^ d - 1 ∣
    Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Finset.mem_Icc] at hd
  obtain ⟨hd1, hdm⟩ := hd
  have hd0 : d ≠ 0 := by omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (GaloisField p d)ˣ)
  have hcard : Nat.card (GaloisField p d) = p ^ d := GaloisField.card p d hd0
  have hord : orderOf ζ = p ^ d - 1 := by
    have h1 : orderOf ζ = Nat.card ((GaloisField p d)ˣ) :=
      orderOf_eq_card_of_forall_mem_zpowers hζ
    rw [h1, Nat.card_units, hcard]
  have hE : Module.finrank (ZMod p) (GaloisField p d) = d :=
    GaloisField.finrank p hd0
  have hfr : Module.finrank (ZMod p)
      ((GaloisField p d) × (Fin (m - d) → ZMod p)) = m := by
    rw [Module.finrank_prod, hE, Module.finrank_pi, Fintype.card_fin]
    omega
  let b := Module.finBasisOfFinrankEq (ZMod p)
    ((GaloisField p d) × (Fin (m - d) → ZMod p)) hfr
  let f : ((GaloisField p d) × (Fin (m - d) → ZMod p)) →* Matrix (Fin m) (Fin m) (ZMod p) :=
    (Algebra.leftMulMatrix b).toRingHom.toMonoidHom
  have hf : Function.Injective f := Algebra.leftMulMatrix_injective b
  have hφinj : Function.Injective
      (Units.map f : ((GaloisField p d) × (Fin (m - d) → ZMod p))ˣ →
        (Matrix (Fin m) (Fin m) (ZMod p))ˣ) := by
    intro u v h
    apply Units.ext
    exact hf (Units.ext_iff.mp h)
  have hinl : Function.Injective
      (MonoidHom.inl (GaloisField p d) (Fin (m - d) → ZMod p)) := by
    intro a c h
    exact congrArg Prod.fst h
  let u := Units.map (MonoidHom.inl (GaloisField p d) (Fin (m - d) → ZMod p)) ζ
  have hinl_map : Function.Injective
      (Units.map (MonoidHom.inl (GaloisField p d) (Fin (m - d) → ZMod p))) := by
    intro a c h
    apply Units.ext
    exact hinl (Units.ext_iff.mp h)
  have e1 : orderOf u = orderOf ζ :=
    orderOf_injective _ hinl_map ζ
  have e2 : orderOf (Units.map f u) = orderOf u :=
    orderOf_injective _ hφinj u
  have e3 : orderOf (Units.map f u) ∣
      Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) :=
    Monoid.order_dvd_exponent _
  rw [← hord, ← e1, ← e2]
  exact e3

private theorem pow_clog_dvd_exponent (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    p ^ Nat.clog p m ∣
      Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hm1 : m = 1
  · subst hm1
    rw [Nat.clog_one_right]
    exact one_dvd _
  · have hm2 : 2 ≤ m := by omega
    have hmonic : (Polynomial.X ^ m : Polynomial (ZMod p)).Monic :=
      Polynomial.monic_X_pow m
    have hdeg : (Polynomial.X ^ m : Polynomial (ZMod p)).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow]
      simp
      omega
    have : Nontrivial (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p))) :=
      AdjoinRoot.nontrivial _ hdeg
    have hinj : Function.Injective
        (algebraMap (ZMod p)
          (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p)))) :=
      RingHom.injective _
    have : CharP (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p))) p :=
      charP_of_injective_algebraMap hinj p
    have hXdvd : ∀ j, (Polynomial.X ^ m : Polynomial (ZMod p)) ∣
        Polynomial.X ^ j ↔ m ≤ j := by
      intro j
      constructor
      · intro h
        rw [Polynomial.X_pow_dvd_iff] at h
        by_contra hlt
        have hlt' : j < m := lt_of_not_ge hlt
        have h1 := h j hlt'
        rw [Polynomial.coeff_X_pow] at h1
        simp at h1
      · intro h
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
        exact ⟨Polynomial.X ^ t, pow_add _ _ _⟩
    set x := AdjoinRoot.root (Polynomial.X ^ m : Polynomial (ZMod p)) with hx
    have hxj : ∀ j, x ^ j = AdjoinRoot.mk
        (Polynomial.X ^ m : Polynomial (ZMod p)) (Polynomial.X ^ j) := by
      intro j
      rw [hx, ← AdjoinRoot.mk_X]
      exact (map_pow _ _ _).symm
    have hxzero : ∀ j, x ^ j = 0 ↔ m ≤ j := by
      intro j
      rw [hxj j, AdjoinRoot.mk_eq_zero, hXdvd j]
    have hnil : IsNilpotent x := ⟨m, (hxzero m).mpr le_rfl⟩
    have hu : IsUnit (1 + x) := hnil.isUnit_one_add
    let u := hu.unit
    have hpow : ∀ k, (1 + x) ^ (p ^ k) = 1 + x ^ (p ^ k) := by
      intro k
      simpa using add_pow_char_pow (1 : AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p))) x p k
    have hc0 : Nat.clog p m ≠ 0 := by
      intro hz
      have hle := Nat.le_pow_clog hp.one_lt m
      rw [hz] at hle
      simp at hle
      omega
    have hcm : m ≤ p ^ Nat.clog p m := Nat.le_pow_clog hp.one_lt m
    have hpred : p ^ (Nat.clog p m).pred < m :=
      Nat.pow_pred_clog_lt_self hp.one_lt (by omega)
    have hu1 : u ^ (p ^ Nat.clog p m) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hpow,
        (hxzero _).mpr hcm, add_zero]
      rfl
    have hu0 : u ^ (p ^ (Nat.clog p m).pred) ≠ 1 := by
      intro hcon
      have h1 : (1 + x) ^ (p ^ (Nat.clog p m).pred) = 1 := by
        have h2 := Units.ext_iff.mp hcon
        rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at h2
        simpa using h2
      rw [hpow] at h1
      have h2 : x ^ (p ^ (Nat.clog p m).pred) = 0 :=
        add_left_cancel_iff.mp (h1.trans (add_zero _).symm)
      exact (not_le.mpr hpred) ((hxzero _).mp h2)
    have hcp : (Nat.clog p m).pred + 1 = Nat.clog p m := by
      have h := Nat.succ_pred_eq_of_ne_zero hc0
      rwa [Nat.succ_eq_add_one] at h
    have hord : orderOf u = p ^ Nat.clog p m := by
      have h2 : u ^ (p ^ ((Nat.clog p m).pred + 1)) = 1 := by
        rw [hcp]
        exact hu1
      have h3 := orderOf_eq_prime_pow hu0 h2
      rw [hcp] at h3
      exact h3
    have hfr : Module.finrank (ZMod p)
        (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p))) = m := by
      have hpb := PowerBasis.finrank (AdjoinRoot.powerBasis' hmonic)
      rw [hpb]
      exact Polynomial.natDegree_X_pow m
    have := (AdjoinRoot.powerBasis' hmonic).finite
    let b := Module.finBasisOfFinrankEq (ZMod p)
      (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p))) hfr
    let f : AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p)) →*
        Matrix (Fin m) (Fin m) (ZMod p) :=
      (Algebra.leftMulMatrix b).toRingHom.toMonoidHom
    have hf : Function.Injective f := Algebra.leftMulMatrix_injective b
    have hφinj : Function.Injective
        (Units.map f : (AdjoinRoot (Polynomial.X ^ m : Polynomial (ZMod p)))ˣ →
          (Matrix (Fin m) (Fin m) (ZMod p))ˣ) := by
      intro v w h
      apply Units.ext
      exact hf (Units.ext_iff.mp h)
    have e2 : orderOf (Units.map f u) = orderOf u :=
      orderOf_injective _ hφinj u
    have e3 : orderOf (Units.map f u) ∣
        Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) :=
      Monoid.order_dvd_exponent _
    rw [← hord, ← e2]
    exact e3

/-- **Exponent of the general linear group over a prime field.** Let $p$ be a prime and let
$m \ge 1$. The exponent of the group $\mathrm{GL}_m(\mathbb{F}_p)$ of invertible $m \times m$
matrices over $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$ is

$$p^{\lceil \log_p m \rceil} \cdot \operatorname{lcm}(p - 1, p^2 - 1, \dots, p^m - 1),$$

and this number equals $p^{\lceil \log_p m \rceil} \prod_{k=1}^{m} \Phi_k(p)$, where $\Phi_k$
denotes the $k$-th cyclotomic polynomial.

Proves `Wanted` entry `generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct`.

Source: Eugene Karolinsky and Dmytro Seliutin, *Carmichael Numbers for GL(m)*,
Journal of Integer Sequences 23 (2020), Article 20.10.6,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Karolinsky/kar2.tex>,
Theorem `fermat_matr` (quoting J. B. Marshall, *On the extension of Fermat's
theorem to matrices of order n*, Proc. Edinb. Math. Soc. 6 (1939), and
I. Niven, *Fermat's theorem for matrices*, Duke Math. J. 15 (1948)), lines
139-144; the lcm/cyclotomic identity is the paper's Proposition, lines
113-118.
-/
theorem generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct
    (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) =
        p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) ∧
      ((p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) : ℕ) : ℤ) =
        (p : ℤ) ^ Nat.clog p m *
          ∏ k ∈ Finset.Icc 1 m, (Polynomial.cyclotomic k ℤ).eval (p : ℤ) := by
  have hA : Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) ∣
      p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    have hCH : Polynomial.aeval (g.val) (g.val.charpoly) = 0 :=
      Matrix.aeval_self_charpoly _
    obtain ⟨q, hq⟩ := charpoly_dvd_X_pow_sub_one_of_mem_GL p m hp g
    have hzero : Polynomial.aeval (g.val)
        ((Polynomial.X ^
          (p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) - 1 :
          Polynomial (ZMod p))) = 0 := by
      rw [hq, map_mul, hCH, zero_mul]
    have hcomp : Polynomial.aeval (g.val)
        ((Polynomial.X ^
          (p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) - 1 :
          Polynomial (ZMod p))) = (g.val) ^
          (p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) - 1 := by
      simp
    rw [hcomp] at hzero
    have hM : (g.val) ^
        (p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1)) = 1 :=
      sub_eq_zero.mp hzero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    simpa using hM
  have hL : (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) ∣
      Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) := by
    rw [Finset.lcm_dvd_iff]
    intro b hb
    rw [Finset.mem_range] at hb
    exact pow_sub_one_dvd_exponent_of_mem_Icc p m hp (b + 1)
      (by rw [Finset.mem_Icc]; omega)
  have hB : p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) ∣
      Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_pow_clog_lcm p m hp)
      (pow_clog_dvd_exponent p m hp hm) hL
  have hC := lcm_eq_cyclotomic_prod p m hp
  refine ⟨Nat.dvd_antisymm hA hB, ?_⟩
  have h1 : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hcast : ((p ^ Nat.clog p m *
      (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) : ℕ) : ℤ) =
      (p : ℤ) ^ Nat.clog p m *
        (((Finset.range m).lcm (fun i => p ^ (i + 1) - 1) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast, hC, Nat.cast_prod]
  apply congrArg
  apply Finset.prod_congr rfl
  intro k _
  exact Int.natAbs_of_nonneg
    (le_of_lt (Polynomial.cyclotomic_pos' k h1))

end
end MetaMathlibExt

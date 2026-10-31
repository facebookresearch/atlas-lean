/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Counting monic irreducible polynomials over a finite field

For a finite field `K` with `q` elements, let `N_d` be the number of monic irreducible
polynomials of degree `d` over `K`. Partitioning the degree-`n` extension of `K` by minimal
polynomials gives Gauss's formula `∑_{d ∣ n} d N_d = q ^ n`.

## Main definitions

* `FiniteField.monicIrreducibleCount`: `N_d`

## Main statements

* `FiniteField.finite_setOf_monic_irreducible_natDegree_eq`
* `FiniteField.sum_divisors_mul_monicIrreducibleCount`: `∑_{d ∣ n} d N_d = q ^ n`
* `FiniteField.sum_divisors_mul_monicIrreducibleCount_zmod`: the case `K = ZMod p`
-/

@[expose] public section

open Polynomial Finset

namespace FiniteField

variable (K : Type*) [Field K]

/-- The number `N_d` of monic irreducible polynomials of degree `d` over the field `K`. It is the
`Nat.card` of the corresponding subtype, which is finite when `K` is finite
(`FiniteField.finite_setOf_monic_irreducible_natDegree_eq`). -/
noncomputable def monicIrreducibleCount (d : ℕ) : ℕ :=
  Nat.card {f : K[X] // f.Monic ∧ Irreducible f ∧ f.natDegree = d}

variable [Finite K]

/-- Over a finite field there are finitely many monic irreducible polynomials of each degree. -/
theorem finite_setOf_monic_irreducible_natDegree_eq (d : ℕ) :
    {f : K[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = d}.Finite := by
  have hinj : Set.InjOn (fun f : K[X] => fun i : Fin (d + 1) => f.coeff i)
      {f : K[X] | f.Monic ∧ Irreducible f ∧ f.natDegree = d} := by
    rintro f ⟨-, -, hf⟩ g ⟨-, -, hg⟩ h
    ext i
    by_cases hi : i ≤ d
    · exact congrFun h ⟨i, by omega⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- **Gauss's formula** for the number of monic irreducible polynomials over a finite field `K`
with `q` elements: `∑_{d ∣ n} d N_d = q ^ n` for `n ≠ 0`. -/
theorem sum_divisors_mul_monicIrreducibleCount {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, d * monicIrreducibleCount K d = Nat.card K ^ n := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : NeZero n := ⟨hn⟩
  set L := Extension K p n
  have : Fintype L := Fintype.ofFinite _
  have hcardL : Fintype.card L = Nat.card K ^ n := by
    rw [Fintype.card_eq_nat_card, natCard_extension]
  have hq1 : 1 < Nat.card K ^ n := Nat.one_lt_pow hn Finite.one_lt_card
  -- `X ^ q ^ n - X` splits over `L` with every element of `L` as a simple root.
  have hbig0 : (X ^ Nat.card K ^ n - X : L[X]) ≠ 0 := X_pow_card_sub_X_ne_zero _ hq1
  have hbigdeg : (X ^ Nat.card K ^ n - X : L[X]).natDegree = Nat.card K ^ n :=
    X_pow_card_sub_X_natDegree_eq _ hq1
  have hbigroots : (X ^ Nat.card K ^ n - X : L[X]).roots = Finset.univ.val := by
    rw [← hcardL]; exact roots_X_pow_card_sub_X _
  have hbigsplits : (X ^ Nat.card K ^ n - X : L[X]).Splits := by
    rw [splits_iff_card_roots, hbigroots, hbigdeg, ← Finset.card_def, Finset.card_univ, hcardL]
  -- A monic irreducible of degree `d ∣ n` has exactly `d` roots in `L`.
  have hfiber : ∀ d : ℕ, d ∣ n → ∀ f : K[X], f.Monic → Irreducible f → f.natDegree = d →
      {a ∈ (univ : Finset L) | minpoly K a = f}.card = d := by
    intro d hd f hm hirr hdeg
    have hmapdvd : f.map (algebraMap K L) ∣ (X ^ Nat.card K ^ n - X : L[X]) := by
      simpa using Polynomial.map_dvd (algebraMap K L)
        ((hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp (hdeg ▸ hd))
    have hmap0 : f.map (algebraMap K L) ≠ 0 := (hm.map _).ne_zero
    have hsplits := hbigsplits.of_dvd hbig0 hmapdvd
    have hnodup : (f.map (algebraMap K L)).roots.Nodup := by
      refine Multiset.nodup_of_le (roots.le_of_dvd hbig0 hmapdvd) ?_
      rw [hbigroots]; exact Finset.univ.nodup
    have hcardroots : (f.map (algebraMap K L)).roots.card = d := by
      rw [splits_iff_card_roots.mp hsplits, hm.natDegree_map, hdeg]
    have hset : {a ∈ (univ : Finset L) | minpoly K a = f}
        = (f.map (algebraMap K L)).roots.toFinset := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset, mem_roots hmap0,
        IsRoot.def, eval_map, ← aeval_def]
      constructor
      · rintro rfl; exact minpoly.aeval _ _
      · intro h; exact (minpoly.eq_of_irreducible_of_monic hirr h hm).symm
    rw [hset, Multiset.toFinset_card_of_nodup hnodup, hcardroots]
  -- Degrees of minimal polynomials divide `n`.
  have hdegdvd : ∀ a : L, (minpoly K a).natDegree ∣ n := by
    intro a
    have h := minpoly.degree_dvd (IsIntegral.of_finite K a)
    rwa [finrank_extension] at h
  -- Partition `L` by the degree of the minimal polynomial, then by the minimal polynomial.
  have step1 : (univ : Finset L).card
      = ∑ d ∈ n.divisors, {a ∈ (univ : Finset L) | (minpoly K a).natDegree = d}.card := by
    refine card_eq_sum_card_fiberwise fun a _ => ?_
    simp only [mem_coe, Nat.mem_divisors]
    exact ⟨hdegdvd a, hn⟩
  have step2 : ∀ d ∈ n.divisors,
      {a ∈ (univ : Finset L) | (minpoly K a).natDegree = d}.card
        = d * monicIrreducibleCount K d := by
    intro d hdmem
    obtain ⟨hd, -⟩ := Nat.mem_divisors.mp hdmem
    have hfin := finite_setOf_monic_irreducible_natDegree_eq K d
    have hB : ∀ f : K[X], f ∈ hfin.toFinset ↔ (f.Monic ∧ Irreducible f ∧ f.natDegree = d) := by
      intro f; simp [Set.Finite.mem_toFinset]
    rw [card_eq_sum_card_fiberwise (f := minpoly K) (t := hfin.toFinset) fun a ha => by
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ha
      simp only [mem_coe, hB]
      exact ⟨minpoly.monic (IsIntegral.of_finite _ a),
        minpoly.irreducible (IsIntegral.of_finite _ a), ha⟩]
    have hval : ∀ f ∈ hfin.toFinset,
        {a ∈ {a ∈ (univ : Finset L) | (minpoly K a).natDegree = d} | minpoly K a = f}.card
          = d := by
      intro f hf
      obtain ⟨hm, hirr, hdeg⟩ := (hB f).mp hf
      calc _ = {a ∈ (univ : Finset L) | minpoly K a = f}.card := by
            rw [filter_filter]
            congr 1
            exact filter_congr fun a _ => ⟨fun h => h.2, fun h => ⟨h ▸ hdeg, h⟩⟩
        _ = d := hfiber d hd f hm hirr hdeg
    rw [sum_congr rfl hval, sum_const, smul_eq_mul, mul_comm, monicIrreducibleCount]
    congr 1
    exact (Nat.card_eq_card_finite_toFinset hfin).symm
  rw [← hcardL, ← card_univ, step1]
  exact (sum_congr rfl step2).symm

/-- Gauss's formula over `ZMod p`: `∑_{d ∣ n} d N_d = p ^ n` for `n ≠ 0`. -/
theorem sum_divisors_mul_monicIrreducibleCount_zmod (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : n ≠ 0) : ∑ d ∈ n.divisors, d * monicIrreducibleCount (ZMod p) d = p ^ n := by
  rw [sum_divisors_mul_monicIrreducibleCount _ hn, Nat.card_zmod]

end FiniteField

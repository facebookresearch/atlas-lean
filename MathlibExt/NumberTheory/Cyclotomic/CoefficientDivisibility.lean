/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The coefficient-divisibility argument is adapted from
`P2M/Sol/S_flt_regular.lean`, lines 521–611, in
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC; licensed under Apache 2.0.
That source credits the flt-regular project (Apache 2.0), copyright its
participants: Alex J. Best, Christopher Birkbeck, Riccardo Brasca,
Eric Rodriguez Boidi, Ruben Van de Velde, and Andrew Yang.
This adaptation factors the argument through all coefficient differences
and uses Mathlib's integral power basis without the extraction framework.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Integer divisibility of cyclotomic coefficients

For a primitive root of prime order `p`, integer divisibility of a sum of
`p` powers forces divisibility of all coefficient differences. If one
coefficient is zero, it forces divisibility of every coefficient.
The modulus is an arbitrary integer, including zero and negative integers.
-/

open scoped NumberField
open Finset

namespace IsPrimitiveRoot

private theorem sum_smul_pow_eq_sum_sub_last {L : Type*} [Field L]
    {n : ℕ} {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ (n + 1))
    (hn : 1 < n + 1) (f : Fin (n + 1) → ℤ) :
    ∑ j, f j • ζ ^ (j : ℕ) =
      ∑ i : Fin n, (f i.castSucc - f (Fin.last n)) • ζ ^ (i : ℕ) := by
  rw [Fin.sum_univ_castSucc]
  have hlast : ζ ^ n = -∑ i : Fin n, ζ ^ (i : ℕ) := by
    simpa [Finset.sum_range] using hζ.pow_sub_one_eq hn
  simp only [Fin.val_last, Fin.val_castSucc, hlast, smul_neg,
    smul_sum, sub_smul, sum_sub_distrib]
  exact (sub_eq_add_neg _ _).symm

private theorem int_dvd_coeff_sub_last {n : ℕ} [hp : Fact (n + 1).Prime]
    {L : Type*} [Field L] [CharZero L]
    [IsCyclotomicExtension {n + 1} ℚ L] {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ (n + 1)) {f : Fin (n + 1) → ℤ} {m : ℤ}
    (hdiv : (m : 𝓞 L) ∣ ∑ j, f j • ζ ^ (j : ℕ)) (i : Fin n) :
    m ∣ f i.castSucc - f (Fin.last n) := by
  have hz : IsPrimitiveRoot (ζ : L) (n + 1) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let pb := hz.integralPowerBasis
  have hd : pb.dim = n := by
    simpa [pb] using hz.integralPowerBasis_dim.trans (Nat.totient_prime hp.out)
  let b := pb.basis.reindex (finCongr hd)
  have hb (j : Fin n) : b j = ζ ^ (j : ℕ) := by
    simp only [b, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rw [show pb.gen = ζ from hz.integralPowerBasis_gen]
    rfl
  obtain ⟨y, hy⟩ := hdiv
  rw [hζ.sum_smul_pow_eq_sum_sub_last hp.out.one_lt] at hy
  simp_rw [← hb] at hy
  have hc := congrArg (b.coord i) hy
  rw [← b.equivFun_symm_apply, b.coord_equivFun_symm] at hc
  rw [hc, ← zsmul_eq_mul]
  exact b.dvd_coord_smul i y m

/-- Divisibility by an integer of a prime-order cyclotomic sum forces
that integer to divide every difference of coefficients. No coefficient
needs to vanish, and the integer modulus may be zero or negative. -/
public theorem int_dvd_coeff_sub_of_dvd_sum {p : ℕ} [hp : Fact p.Prime]
    {L : Type*} [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ} {m : ℤ}
    (hdiv : (m : 𝓞 L) ∣ ∑ j, f j • ζ ^ (j : ℕ)) (i j : Fin p) :
    m ∣ f i - f j := by
  cases p with
  | zero => exact (hp.out.ne_zero rfl).elim
  | succ n =>
    have hd (k : Fin (n + 1)) : m ∣ f k - f (Fin.last n) := by
      refine Fin.lastCases ?_ (fun a => ?_) k
      · simp
      · exact hζ.int_dvd_coeff_sub_last hdiv a
    simpa only [sub_sub_sub_cancel_right] using dvd_sub (hd i) (hd j)

/-- If an integer divides a prime-order cyclotomic sum and some coefficient
is zero, it divides every coefficient. The zero coefficient may occur at
any index. This is the zero-anchored coefficient lemma from the regular-prime
FLT development, with no restriction on the sign or vanishing of `m`. -/
public theorem int_dvd_coeff_of_dvd_sum {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ}
    (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : (m : 𝓞 L) ∣ ∑ j, f j • ζ ^ (j : ℕ)) : ∀ j, m ∣ f j := by
  obtain ⟨i, hi⟩ := hf
  intro j
  simpa only [hi, sub_zero] using hζ.int_dvd_coeff_sub_of_dvd_sum hdiv j i

end IsPrimitiveRoot

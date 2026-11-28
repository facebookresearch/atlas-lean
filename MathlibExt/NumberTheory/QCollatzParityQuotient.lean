/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QCollatzParityCongruence
import Mathlib.Data.Fintype.EquivFin

/-!
# The q-Collatz parity vector on finite quotients

For odd power series `A` and `B` over `ZMod 2` and every positive `n`, reducing the parity vector
modulo `2 ^ n` gives a bijection from the quotient by `X ^ n` to `ZMod (2 ^ n)`. The congruence
criterion gives injectivity, and the first `n` coefficients count the source classes.

## References

* Kenneth G. Monks, *On q-Analogs of the 3x + 1 Dynamical System*, Journal of Integer
  Sequences 28 (2025), Article 25.6.8, pp. 1–13, §2.1, Corollary 12 (p. 8).
  The proof uses Monks's Theorem 11 via `qCollatzParityVector_modEq_iff` in
  `MathlibExt.NumberTheory.QCollatzParityCongruence`.
-/

namespace MetaMathlibExt

open PowerSeries

/-- **Parity vectors induce bijections modulo $q^n$.** Let $A, B \in \mathbb{F}_2[[q]]$ be odd
(constant term $1$), let $\mathrm{PV}_{A,B}$ be the parity vector map of the $q$-analog $T_{A,B}$
of the $3x+1$ map, and let $n \ge 1$ be an integer. Then there is a bijection
$e : \mathbb{F}_2[[q]]/(q^n) \to \mathbb{Z}/2^n\mathbb{Z}$ such that, for every
$a \in \mathbb{F}_2[[q]]$, $e$ sends the class of $a$ to the residue of $\mathrm{PV}_{A,B}(a)$
modulo $2^n$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 12 (`jis-2025-25.6.8-cor-12`). -/
public theorem qCollatzParityVector_quotient_bijection (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (PowerSeries (ZMod 2) ⧸ Ideal.span {(X : PowerSeries (ZMod 2)) ^ n}) ≃ ZMod (2 ^ n),
      ∀ a, e (Ideal.Quotient.mk _ a) = PadicInt.toZModPow n (qCollatzParityVector A B a) := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  let I := Ideal.span {(X : PowerSeries (ZMod 2)) ^ (j + 1)}
  let residue (a : PowerSeries (ZMod 2)) := PadicInt.toZModPow (j + 1) (qCollatzParityVector A B a)
  have hquot (a b : PowerSeries (ZMod 2)) :
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ X ^ (j + 1) ∣ a - b := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hresidue (a b : PowerSeries (ZMod 2)) :
      residue a = residue b ↔ Ideal.Quotient.mk I a = Ideal.Quotient.mk I b :=
    (qCollatzParityVector_modEq_iff A B hA hB j a b).trans (hquot a b).symm
  let f : (PowerSeries (ZMod 2) ⧸ I) → ZMod (2 ^ (j + 1)) :=
    Quotient.lift residue fun a b hab => (hresidue a b).mpr (Quotient.sound hab)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hresidue a b).mp hxy
  let firstCoeffs (a : PowerSeries (ZMod 2)) (i : Fin (j + 1)) := coeff i a
  have hcoeffs (a b : PowerSeries (ZMod 2)) :
      firstCoeffs a = firstCoeffs b ↔ Ideal.Quotient.mk I a = Ideal.Quotient.mk I b := by
    rw [hquot, X_pow_dvd_iff]
    constructor
    · intro h i hi
      simpa only [map_sub, sub_eq_zero] using congrFun h ⟨i, hi⟩
    · intro h
      funext i
      simpa only [map_sub, sub_eq_zero] using h i i.isLt
  let g : (PowerSeries (ZMod 2) ⧸ I) → Fin (j + 1) → ZMod 2 :=
    Quotient.lift firstCoeffs fun a b hab => (hcoeffs a b).mpr (Quotient.sound hab)
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact (hcoeffs a b).mp hxy
    · intro v
      let a := PowerSeries.mk fun i => if hi : i < j + 1 then v ⟨i, hi⟩ else 0
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      funext i
      change coeff i a = v i
      simp only [a, coeff_mk, dite_eq_left i.isLt]
  let _ := Fintype.ofEquiv (Fin (j + 1) → ZMod 2) (Equiv.ofBijective g hg).symm
  have hcard : Fintype.card (PowerSeries (ZMod 2) ⧸ I) = Fintype.card (ZMod (2 ^ (j + 1))) := by
    rw [Fintype.card_of_bijective hg, Fintype.card_fun, Fintype.card_fin, ZMod.card, ZMod.card]
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩),
    fun _ => rfl⟩

end MetaMathlibExt

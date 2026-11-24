/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fintype
import MathlibExt.Combinatorics.Enumerative.RHorseNumberFubini
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Eventual periodicity of the `r`-Fubini numbers modulo an integer

This file proves Schreyer's Corollary 12, `rFubini_add_carmichael_modEq`: for `r ≥ 1`, the
`r`-Fubini numbers satisfy `F_r(n + λ(K)) ≡ F_r(n) (mod K)` for every `n ≥ r - 1 + R`, where `λ`
is the Carmichael function and `R` is the largest exponent in the prime factorization of `K`.
The paper's `r`-Fubini number `F_r(n)` (Definition 3: weak orderings of an `n`-element set in
which `r` distinguished elements are pairwise untied) is the number of surjections
`f : Fin n → Fin k`, summed over `k`, that are injective on the elements of value `< r`.

The proof follows the source. Sorting the values of the first `r` points identifies the
`r`-Fubini count with `r!` times the `r`-horse count, so Schreyer's Fubini formula for `r`-horse
numbers (`rHorseNumber_eq_stirlingFirst_sum_fubini`) writes `F_r(n)` as an integer combination of
the Fubini numbers `F(n - j)` with `j < r`. Each Fubini number is an integer combination of the
powers `i ^ (n - j)`, and `i ^ (e + λ(K)) ≡ i ^ e (mod K)` as soon as `e ≥ R`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-! ### Powers modulo `K` -/

/-- Every exponent in the prime factorization of `K` is at most the largest one. -/
private theorem rFubini_factorization_le_sup (K p : ℕ) :
    K.factorization p ≤ K.factorization.support.sup K.factorization := by
  by_cases hp : p ∈ K.factorization.support
  · exact Finset.le_sup hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _

/-- The largest exponent in the prime factorization of `K ≥ 2` is positive. -/
private theorem rFubini_one_le_sup {K : ℕ} (hK : 2 ≤ K) :
    1 ≤ K.factorization.support.sup K.factorization := by
  have hp : K.minFac.Prime := Nat.minFac_prime (by omega)
  have hpos : 0 < K.factorization K.minFac :=
    hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd K)
  exact hpos.trans_le (rFubini_factorization_le_sup K K.minFac)

/-- For `K ≥ 2` and every exponent `e` at least the largest exponent in the prime factorization
of `K`, the power `x ^ e` is unchanged modulo `K` by adding `λ(K)` to the exponent. -/
private theorem rFubini_pow_modEq {K : ℕ} (hK : 2 ≤ K) (x e : ℕ)
    (he : K.factorization.support.sup K.factorization ≤ e) :
    x ^ e ≡ x ^ (e + carmichael K) [MOD K] := by
  have hK0 : K ≠ 0 := by omega
  have he1 : 1 ≤ e := (rFubini_one_le_sup hK).trans he
  have hle : x ^ e ≤ x ^ (e + carmichael K) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [zero_pow (by omega), zero_pow (by omega)]
    · exact Nat.pow_le_pow_right hx (by omega)
  refine (Nat.modEq_iff_dvd' hle).mpr ((Nat.dvd_iff_prime_pow_dvd_dvd _ K).mpr ?_)
  intro p k hp hpk
  have hke : k ≤ e := ((hp.pow_dvd_iff_le_factorization hK0).mp hpk).trans
    ((rFubini_factorization_le_sup K p).trans he)
  rw [pow_add, ← Nat.mul_sub_one]
  by_cases hpx : p ∣ x
  · exact Dvd.dvd.mul_right ((pow_dvd_pow p hke).trans (pow_dvd_pow_of_dvd hpx e)) _
  · refine Dvd.dvd.mul_left ?_ _
    have hcop : Nat.Coprime x (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx).symm
    have hx : 0 < x := Nat.pos_of_ne_zero fun h => hpx (h ▸ dvd_zero p)
    have hunit : ZMod.unitOfCoprime x hcop ^ carmichael K = 1 := by
      obtain ⟨c, hc⟩ := carmichael_dvd hpk
      rw [hc, pow_mul, pow_carmichael, one_pow]
    have hcast : ((x ^ carmichael K : ℕ) : ZMod (p ^ k)) = ((1 : ℕ) : ZMod (p ^ k)) := by
      have h := congrArg (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k))) hunit
      simpa [ZMod.coe_unitOfCoprime] using h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hx)).mp
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast).symm

/-- `rFubini_pow_modEq` in `ZMod K`. -/
private theorem rFubini_natCast_pow_add_carmichael {K : ℕ} (hK : 2 ≤ K) (x e : ℕ)
    (he : K.factorization.support.sup K.factorization ≤ e) :
    (x : ZMod K) ^ (e + carmichael K) = (x : ZMod K) ^ e := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
  exact (rFubini_pow_modEq hK x e he).symm

/-! ### Fubini numbers modulo `K` -/

/-- The Fubini number `F(t)` as an alternating sum of powers `j ^ t`, summed over `k ≤ N` for any
`N ≥ t`. -/
private theorem rFubini_fubiniNumber_intCast (t N : ℕ) (htN : t ≤ N) :
    (fubiniNumber t : ℤ) = ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ t := by
  have hext : fubiniNumber t =
      ∑ k ∈ Finset.range (N + 1), Nat.stirlingSecond t k * k.factorial := by
    rw [fubiniNumber_eq_sum]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), zero_mul]
  rw [hext, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := stirlingSecond_mul_factorial_eq_sum t k
  exact_mod_cast h

/-- The Fubini numbers are periodic modulo `K ≥ 2` with period `λ(K)` from the largest exponent
in the prime factorization of `K` on. -/
private theorem rFubini_fubiniNumber_add_carmichael {K : ℕ} (hK : 2 ≤ K) (e : ℕ)
    (he : K.factorization.support.sup K.factorization ≤ e) :
    (fubiniNumber (e + carmichael K) : ZMod K) = (fubiniNumber e : ZMod K) := by
  rw [← Int.cast_natCast (R := ZMod K) (fubiniNumber (e + carmichael K)),
    ← Int.cast_natCast (R := ZMod K) (fubiniNumber e),
    rFubini_fubiniNumber_intCast _ (e + carmichael K) le_rfl,
    rFubini_fubiniNumber_intCast e (e + carmichael K) (by omega)]
  push_cast
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [rFubini_natCast_pow_add_carmichael hK j e he]

/-! ### `r`-Fubini numbers through `r`-horse numbers -/

/-- A permutation of the first `r` points of `Fin m`, extended by the identity. -/
private def rFubini_extendPerm {r m : ℕ} (hrm : r ≤ m) (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin m) :=
  σ.viaFintypeEmbedding (Fin.castLEEmb hrm)

private theorem rFubini_extendPerm_castLE {r m : ℕ} (hrm : r ≤ m) (σ : Equiv.Perm (Fin r))
    (i : Fin r) : rFubini_extendPerm hrm σ (Fin.castLE hrm i) = Fin.castLE hrm (σ i) :=
  σ.viaFintypeEmbedding_apply_image (Fin.castLEEmb hrm) i

private theorem rFubini_extendPerm_symm_castLE {r m : ℕ} (hrm : r ≤ m)
    (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (rFubini_extendPerm hrm σ).symm (Fin.castLE hrm i) = Fin.castLE hrm (σ.symm i) := by
  rw [Equiv.symm_apply_eq, rFubini_extendPerm_castLE, Equiv.apply_symm_apply]

/-- Injectivity on the points below `r` is injectivity of the restriction to `Fin r`. -/
private theorem rFubini_injOn_iff {r m k : ℕ} (hrm : r ≤ m) (f : Fin m → Fin k) :
    (∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j) ↔
      Function.Injective (f ∘ Fin.castLE hrm) := by
  constructor
  · intro h a b hab
    exact Fin.castLE_injective hrm (h _ _ a.2 b.2 hab)
  · intro h i j hi hj hij
    have hij' : (f ∘ Fin.castLE hrm) ⟨i, hi⟩ = (f ∘ Fin.castLE hrm) ⟨j, hj⟩ := hij
    exact Fin.ext (Fin.mk.inj_iff.mp (h hij'))

/-- Sorting the values of the first `r` points: a surjection that is injective on the points
below `r` is a permutation of `Fin r` together with a surjection that is strictly increasing on
those points. -/
private def rFubini_sortEquiv {r m : ℕ} (hrm : r ≤ m) (k : ℕ) :
    { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j } ≃
      Equiv.Perm (Fin r) × { g : Fin m → Fin k // Function.Surjective g ∧
        ∀ i j : Fin r, i < j → g (Fin.castLE hrm i) < g (Fin.castLE hrm j) } where
  toFun f := (Tuple.sort (f.1 ∘ Fin.castLE hrm),
    ⟨f.1 ∘ rFubini_extendPerm hrm (Tuple.sort (f.1 ∘ Fin.castLE hrm)),
      f.2.1.comp (Equiv.surjective _), fun i j hij => by
        have hinj := (rFubini_injOn_iff hrm f.1).mp f.2.2
        have hsm : StrictMono ((f.1 ∘ Fin.castLE hrm) ∘ Tuple.sort (f.1 ∘ Fin.castLE hrm)) :=
          (Tuple.monotone_sort _).strictMono_of_injective (hinj.comp (Equiv.injective _))
        simpa only [Function.comp_apply, rFubini_extendPerm_castLE] using hsm hij⟩)
  invFun p := ⟨p.2.1 ∘ (rFubini_extendPerm hrm p.1).symm,
    p.2.2.1.comp (Equiv.surjective _), by
      rw [rFubini_injOn_iff hrm]
      intro a b hab
      simp only [Function.comp_apply, rFubini_extendPerm_symm_castLE] at hab
      have hsm : StrictMono (p.2.1 ∘ Fin.castLE hrm) := fun i j hij => p.2.2.2 i j hij
      exact p.1.symm.injective (hsm.injective hab)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv p := by
    obtain ⟨σ, g, hg, hinc⟩ := p
    have hsm : StrictMono (g ∘ Fin.castLE hrm) := fun i j hij => hinc i j hij
    have hcomp : ((g ∘ (rFubini_extendPerm hrm σ).symm) ∘ Fin.castLE hrm) ∘ σ =
        g ∘ Fin.castLE hrm := by
      funext i
      simp [rFubini_extendPerm_symm_castLE]
    have hsort : Tuple.sort ((g ∘ (rFubini_extendPerm hrm σ).symm) ∘ Fin.castLE hrm) = σ := by
      refine (Tuple.eq_sort_iff.mpr ⟨hcomp ▸ hsm.monotone, fun i j _ hfij => ?_⟩).symm
      have hgij : (g ∘ Fin.castLE hrm) i = (g ∘ Fin.castLE hrm) j := by
        rw [← hcomp]
        exact hfij
      rw [hsm.injective hgij]
    refine Prod.ext hsort (Subtype.ext ?_)
    change (g ∘ (rFubini_extendPerm hrm σ).symm) ∘ rFubini_extendPerm hrm
      (Tuple.sort ((g ∘ (rFubini_extendPerm hrm σ).symm) ∘ Fin.castLE hrm)) = g
    rw [hsort]
    funext x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- The `r`-Fubini count onto `Fin k` is `r!` times the `r`-horse count onto `Fin k`. -/
private theorem rFubini_card_eq {r m : ℕ} (hrm : r ≤ m) (k : ℕ) :
    Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j } =
      r.factorial * Nat.card { g : Fin m → Fin k // Function.Surjective g ∧
        ∀ i j : Fin r, i < j → g (Fin.castLE hrm i) < g (Fin.castLE hrm j) } := by
  rw [Nat.card_congr (rFubini_sortEquiv hrm k), Nat.card_prod, Nat.card_perm, Nat.card_fin]

/-- The `r`-Fubini number `F_r(m)`, `r ≤ m`, as an integer combination of the Fubini numbers
`F(m - j)`, `j ≤ r`. -/
private theorem rFubini_intCast_eq {r m : ℕ} (hrm : r ≤ m) :
    ((∑ k ∈ Finset.range (m + 1), Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j } : ℕ) : ℤ) =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℤ) ^ j * (Nat.stirlingFirst r (r - j) : ℤ) * (fubiniNumber (m - j) : ℤ) := by
  have hQ : ((∑ k ∈ Finset.range (m + 1), Nat.card { f : Fin m → Fin k //
        Function.Surjective f ∧
          ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j } : ℕ) : ℚ) =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) * (fubiniNumber (m - j) : ℚ) := by
    rw [Nat.cast_sum]
    simp_rw [rFubini_card_eq hrm, Nat.cast_mul]
    rw [← Finset.mul_sum, rHorseNumber_eq_stirlingFirst_sum_fubini m r hrm, ← mul_assoc,
      mul_one_div_cancel (by positivity), one_mul]
  exact_mod_cast hQ

/-- **Eventual periodicity of the $r$-Fubini numbers modulo $K$.** For a natural number $r \ge 1$
and a natural number $m$, let $F_r(m)$ be the number of pairs $(k, f)$ of a natural number
$k \le m$ and a surjection $f : \{0, \dots, m - 1\} \to \{0, \dots, k - 1\}$ that is injective on
the elements less than $r$; equivalently, $F_r(m)$ counts the weak orderings of $m$ elements in
which the elements less than $r$ are pairwise untied. Let $K$ be a natural number, let
$\lambda(K)$ be the value of the Carmichael function at $K$, and let $R$ be the largest exponent
in the prime factorization of $K$ ($R = 0$ for $K \le 1$). Then
$F_r(n + \lambda(K)) \equiv F_r(n) \pmod K$ for every natural number $n \ge r - 1 + R$.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Corollary 12 (`jis-2025-25.4.1-cor-12`). -/
public theorem rFubini_add_carmichael_modEq (K r n : ℕ) (hr : 1 ≤ r)
    (hn : r - 1 + K.factorization.support.sup K.factorization ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j }
    rFubini (n + carmichael K) ≡ rFubini n [MOD K] := by
  intro rFubini
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K
    · rw [ArithmeticFunction.map_zero, add_zero]
    · exact Nat.modEq_one
  have hrn : r ≤ n := by
    have := rFubini_one_le_sup hK
    omega
  have key : (((rFubini (n + carmichael K) : ℕ) : ℤ) : ZMod K) =
      (((rFubini n : ℕ) : ℤ) : ZMod K) := by
    simp only [rFubini]
    rw [rFubini_intCast_eq (by omega), rFubini_intCast_eq hrn]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j r with hjr | hjr
    · rw [show n + carmichael K - j = n - j + carmichael K by omega,
        rFubini_fubiniNumber_add_carmichael hK (n - j) (by omega)]
    · obtain rfl : j = r := by omega
      obtain ⟨s, rfl⟩ : ∃ s, j = s + 1 := ⟨j - 1, by omega⟩
      simp
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa only [Int.cast_natCast] using key

end MetaMathlibExt

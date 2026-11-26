/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import MathlibExt.NumberTheory.GeneralizedFrobeniusNumber
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Beck–Kifer reduction for generalized Frobenius numbers

Representation counts are preserved by removing the first coefficient's residue modulo the
common factor of the remaining generators. This gives the Beck–Kifer reduction of the
generalized Frobenius number.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 1 (`integers-2026-A63-lem-1`), quoted from Beck
and Kifer, Lemma 4.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem exists_residue (a ℓ : ℕ) (hℓ : 0 < ℓ) (hc : Nat.Coprime a ℓ) (m : ℤ) :
    ∃ r : ℕ, r < ℓ ∧ ∃ q : ℤ, m = ℓ * q + a * r := by
  have hℓz : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  obtain ⟨u, hu⟩ := Int.mod_coprime hc
  obtain ⟨r, hr, hrmod⟩ := Int.existsUnique_equiv_nat (u * m) hℓz
  have hmod : (a : ℤ) * r ≡ m [ZMOD ℓ] := by
    calc
      (a : ℤ) * r ≡ a * (u * m) [ZMOD ℓ] := hrmod.mul_left a
      _ ≡ m [ZMOD ℓ] := by simpa [mul_assoc] using hu.mul_right m
  obtain ⟨q, hq⟩ := Int.modEq_iff_add_fac.mp hmod
  exact ⟨r, by exact_mod_cast hr, q, by linarith⟩

private theorem sum_cons_mul (k a ℓ : ℕ) (b : Fin k → ℕ) (x : Fin (k + 1) → ℕ) :
    ∑ i, (x i : ℤ) * (Fin.cons a (fun j => ℓ * b j) : Fin (k + 1) → ℕ) i =
      (x 0 : ℤ) * a + ℓ * ∑ i, (x i.succ : ℤ) * b i := by
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_mul,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem repCount_transport (k a ℓ : ℕ) (b : Fin k → ℕ) (ha : 0 < a) (hb : ∀ i, 0 < b i)
    (hℓ : 0 < ℓ) (hc : Nat.Coprime a ℓ) (r : ℕ) (hr : r < ℓ) (q : ℤ) :
    frobeniusRepCount (Fin.cons a (fun i => ℓ * b i)) (ℓ * q + a * r) =
      frobeniusRepCount (Fin.cons a b) q := by
  let f : (Fin (k + 1) → ℕ) → (Fin (k + 1) → ℕ) :=
    fun x => Fin.cons (r + ℓ * x 0) (Fin.tail x)
  have hℓz : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hsource := frobeniusRepCount_ne_top (a := Fin.cons a b)
    (fun i => Fin.cases ha hb i) q
  have htarget := frobeniusRepCount_ne_top (a := Fin.cons a (fun i => ℓ * b i))
    (fun i => Fin.cases ha (fun j => Nat.mul_pos hℓ (hb j)) i) (ℓ * q + a * r)
  rw [← ENat.natCast_toNat htarget, ← ENat.natCast_toNat hsource]
  symm
  unfold frobeniusRepCount
  rw [← Set.ncard_def, ← Set.ncard_def]
  congr 1
  refine Set.ncard_congr' (Set.BijOn.equiv f ⟨?_, ?_, ?_⟩)
  · intro x hx
    change ∑ i, (f x i : ℤ) * (Fin.cons a (fun j => ℓ * b j) : Fin (k + 1) → ℕ) i = ℓ * q + a * r
    rw [sum_cons_mul]
    have hx : (x 0 : ℤ) * a + ∑ i, (x i.succ : ℤ) * b i = q := by
      simpa only [Set.mem_ofPred_eq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hx
    simp only [f, Fin.cons_zero, Fin.cons_succ, Fin.tail, Nat.cast_add, Nat.cast_mul]
    rw [← hx]
    ring
  · intro x _ y _ hxy
    have h0 : r + ℓ * x 0 = r + ℓ * y 0 := congrArg (fun z => z 0) hxy
    have h0 : x 0 = y 0 := Nat.mul_left_cancel hℓ (Nat.add_left_cancel h0)
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    simpa only [f, Fin.cons_succ, Fin.tail] using congrArg (fun z => z j.succ) hxy
  · intro x hx
    have hx : (x 0 : ℤ) * a + ℓ * ∑ i, (x i.succ : ℤ) * b i = ℓ * q + a * r :=
      (sum_cons_mul k a ℓ b x).symm.trans hx
    have hdvd : (ℓ : ℤ) ∣ ((x 0 : ℤ) - r) * a := by
      refine ⟨q - ∑ i, (x i.succ : ℤ) * b i, ?_⟩
      nlinarith [hx]
    have hdvd : (ℓ : ℤ) ∣ (x 0 : ℤ) - r :=
      Int.dvd_of_dvd_mul_left_of_gcd_one hdvd (by
        simpa only [Int.gcd_natCast_natCast] using hc.symm.gcd_eq_one)
    have hremz : (x 0 : ℤ) % ℓ = (r : ℤ) := by
      calc
        (x 0 : ℤ) % ℓ = (r : ℤ) % ℓ :=
          Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)
        _ = r := Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr)
    have hrem : x 0 % ℓ = r := by exact_mod_cast hremz
    have hfirst : r + ℓ * (x 0 / ℓ) = x 0 := by
      simpa only [hrem] using Nat.mod_add_div (x 0) ℓ
    let y := Fin.cons (x 0 / ℓ) (Fin.tail x)
    have hfy : f y = x := by
      dsimp [f, y]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [hfirst, Fin.cons_self_tail]
    refine ⟨y, ?_, hfy⟩
    change ∑ i, (y i : ℤ) * (Fin.cons a b : Fin (k + 1) → ℕ) i = q
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, y, Fin.tail]
    have hfirstz : (r : ℤ) + ℓ * (x 0 / ℓ : ℕ) = x 0 := by exact_mod_cast hfirst
    apply mul_left_cancel₀ hℓz
    nlinarith [hx, hfirstz]

/-- **Beck–Kifer reduction by a common factor of all generators but the first.** Let $K \ge 2$,
let $a_1$ and $\ell$ be positive integers, and let $a'_2, \dots, a'_K$ be positive integers with
$\gcd(a'_2, \dots, a'_K) = 1$ such that $\gcd(a_1, \ell a'_2, \dots, \ell a'_K) = 1$. Let $s$ be a
natural number. If $g'$ is the generalized Frobenius number $g(a_1, a'_2, \dots, a'_K; s)$, then
$\ell g' + a_1(\ell - 1)$ is the generalized Frobenius number
$g(a_1, \ell a'_2, \dots, \ell a'_K; s)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 1 (`integers-2026-A63-lem-1`), quoted from Beck
and Kifer, Lemma 4. -/
public theorem isGenFrobeniusNumber_cons_mul_of_gcd (k : ℕ) (a₁ ℓ : ℕ)
    (a' : Fin (k + 1) → ℕ) (ha₁ : 0 < a₁) (ha' : ∀ i, 0 < a' i) (hℓ : 0 < ℓ)
    (hgcd' : Finset.univ.gcd a' = 1)
    (hgcd : Finset.univ.gcd (Fin.cons a₁ (fun i => ℓ * a' i) : Fin (k + 2) → ℕ) = 1)
    (s : ℕ) (g' : ℤ) (hg' : IsGenFrobeniusNumber (Fin.cons a₁ a' : Fin (k + 2) → ℕ) s g') :
    IsGenFrobeniusNumber (Fin.cons a₁ (fun i => ℓ * a' i) : Fin (k + 2) → ℕ) s
      (ℓ * g' + a₁ * ((ℓ : ℤ) - 1)) := by
  have htail : Finset.univ.gcd (fun i => ℓ * a' i) = ℓ := by
    rw [Finset.gcd_mul_left, hgcd']
    simp
  have hc : Nat.Coprime a₁ ℓ := by
    rw [Fin.univ_succ, Finset.gcd_cons, Finset.map_eq_image, Finset.gcd_image] at hgcd
    change Nat.gcd a₁ (Finset.univ.gcd (fun i => ℓ * a' i)) = 1 at hgcd
    change Nat.gcd a₁ ℓ = 1
    rwa [htail] at hgcd
  have hℓz : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have ha₁z : (0 : ℤ) < a₁ := by exact_mod_cast ha₁
  constructor
  · have hr : ℓ - 1 < ℓ := by omega
    have hcast : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by omega
    rw [← hcast, repCount_transport (k + 1) a₁ ℓ a' ha₁ ha' hℓ hc (ℓ - 1) hr g']
    exact hg'.1
  · intro m hm
    obtain ⟨r, hr, q, hq⟩ := exists_residue a₁ ℓ hℓ hc m
    have hrz : (r : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
    have hgq : g' < q := by
      have hbound := mul_le_mul_of_nonneg_left hrz ha₁z.le
      rw [hq] at hm
      nlinarith
    rw [hq, repCount_transport (k + 1) a₁ ℓ a' ha₁ ha' hℓ hc r hr q]
    exact hg'.2 q hgq

end

end MetaMathlibExt

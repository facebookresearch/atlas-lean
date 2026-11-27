/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QAnalogCollatz
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Conjugacy of the q-Collatz and 2-adic Collatz maps

For power series `A` and `B` over `ZMod 2` with constant term `1`, the q-Collatz map with
parameters `A` and `B` is conjugate to the 2-adic Collatz map; `A = 1 + X`, `B = 1` is a special
case. Both maps are conjugate to the shift on binary sequences through their parity sequences.
-/

namespace MetaMathlibExt

open PowerSeries Filter Topology

namespace qCollatz_one_add_X_conjugate_twoAdicCollatz

private def itinerary {R : Type*} (step : R → R) (residue : R → ZMod 2)
    (x : R) (n : ℕ) : ZMod 2 :=
  residue (step^[n] x)

private def approximation {R : Type*} [Zero R] (branch : ZMod 2 → R → R)
    (digits : ℕ → ZMod 2) : ℕ → R
  | 0 => 0
  | n + 1 => branch (digits 0) (approximation branch (fun i => digits (i + 1)) n)

-- Inverse branches preserve the prescribed first digit and add one power of the parameter
-- to the divisibility of a difference. Finite compositions thus specify a unique limit.
private theorem itinerary_bijective {R : Type*} [CommRing R] [IsDomain R]
    (π : R) (hπ : π ≠ 0) (residue : R →+* ZMod 2) (hπ₀ : residue π = 0)
    (u : Rˣ) (hu : residue (u : R) = 1) (c : R) (hc : residue c = 1) (step : R → R)
    (hstep : ∀ x, π * step x = if residue x = 0 then x else (u : R) * x + c)
    (separated : ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0)
    (complete : ∀ f : ℕ → R, (∀ n m, n ≤ m → π ^ n ∣ f m - f n) →
      ∃ x, ∀ n, π ^ n ∣ x - f n) :
    Function.Bijective (itinerary step residue) := by
  classical
  let branch : ZMod 2 → R → R := fun b x =>
    if b = 0 then π * x else (↑u⁻¹ : R) * (π * x - c)
  have hu' : residue (↑u⁻¹ : R) = 1 := by
    have h : residue ((u : R) * (↑u⁻¹ : R)) = 1 := by simp
    rwa [map_mul, hu, one_mul] at h
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hbit : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
  have hresidue (b : ZMod 2) (x : R) : residue (branch b x) = b := by
    by_cases hb : b = 0
    · simp [branch, hb, hπ₀]
    · simp [branch, hπ₀, hu', hc, hneg, hbit b hb]
  have hleft (b : ZMod 2) (x : R) : step (branch b x) = x := by
    apply mul_left_cancel₀ hπ
    rw [hstep, hresidue]
    by_cases hb : b = 0 <;> simp [branch, hb, ← mul_assoc]
  have hright (x : R) : branch (residue x) (step x) = x := by
    by_cases hx : residue x = 0 <;> simp [branch, hx, hstep, ← mul_assoc]
  have contract (b : ZMod 2) (n : ℕ) (x y : R) (h : π ^ n ∣ x - y) :
      π ^ (n + 1) ∣ branch b x - branch b y := by
    obtain ⟨z, hz⟩ := h
    by_cases hb : b = 0
    · exact ⟨z, by simp [branch, hb, ← mul_sub, hz, pow_succ', mul_assoc]⟩
    · refine ⟨(↑u⁻¹ : R) * z, ?_⟩
      simp only [branch, ite_eq_right hb, ← mul_sub, sub_sub_sub_cancel_right, hz]
      rw [pow_succ]
      ring
  have htail (x : R) (n : ℕ) : itinerary step residue (step x) n =
      itinerary step residue x (n + 1) := by
    simp only [itinerary, Function.iterate_succ_apply]
  constructor
  · intro x y hxy
    suffices ∀ n : ℕ, π ^ n ∣ x - y from sub_eq_zero.mp (separated _ this)
    intro n
    induction n generalizing x y with
    | zero => simp
    | succ n ih =>
      have hzero : residue x = residue y := congrFun hxy 0
      have hnext : itinerary step residue (step x) = itinerary step residue (step y) :=
        funext fun i => (htail x i).trans ((congrFun hxy (i + 1)).trans (htail y i).symm)
      simpa only [hright] using
        (show π ^ (n + 1) ∣ branch (residue x) (step x) - branch (residue y) (step y) by
          rw [← hzero]
          exact contract _ n _ _ (ih hnext))
  · have happrox (s : ℕ → ZMod 2) (n m : ℕ) (h : n ≤ m) :
        π ^ n ∣ approximation branch s m - approximation branch s n := by
      induction n generalizing s m with
      | zero => simp
      | succ n ih =>
        cases m with
        | zero => omega
        | succ m =>
          exact contract _ n _ _ (ih _ m (Nat.le_of_succ_le_succ h))
    choose limit hlimit using fun s => complete (approximation branch s) (happrox s)
    have unfold_limit (s : ℕ → ZMod 2) :
        limit s = branch (s 0) (limit (fun i => s (i + 1))) := by
      apply sub_eq_zero.mp
      apply separated
      intro n
      cases n with
      | zero => simp
      | succ n =>
        have h := contract (s 0) n _ _ (hlimit (fun i => s (i + 1)) n)
        have hs := hlimit s (n + 1)
        rw [approximation] at hs
        exact (hs.sub h).trans (dvd_of_eq (by abel))
    have limit_code (s : ℕ → ZMod 2) (n : ℕ) :
        itinerary step residue (limit s) n = s n := by
      induction n generalizing s with
      | zero => rw [itinerary, Function.iterate_zero_apply, unfold_limit s, hresidue]
      | succ n ih =>
        rw [← htail]
        have h : step (limit s) = limit (fun i => s (i + 1)) := by
          rw [unfold_limit s, hleft]
        rw [h, ih]
    exact fun s => ⟨limit s, funext (limit_code s)⟩

private theorem powerSeries_separated (x : PowerSeries (ZMod 2))
    (h : ∀ n : ℕ, (X : PowerSeries (ZMod 2)) ^ n ∣ x) : x = 0 :=
  (forall_coeff_eq_zero x).mp fun i => X_pow_dvd_iff.mp (h (i + 1)) i (Nat.lt_succ_self i)

private theorem powerSeries_complete (f : ℕ → PowerSeries (ZMod 2))
    (hf : ∀ n m, n ≤ m → (X : PowerSeries (ZMod 2)) ^ n ∣ f m - f n) :
    ∃ x, ∀ n, (X : PowerSeries (ZMod 2)) ^ n ∣ x - f n := by
  refine ⟨PowerSeries.mk fun i => coeff i (f (i + 1)), fun n => X_pow_dvd_iff.mpr ?_⟩
  intro i hi
  have h := X_pow_dvd_iff.mp (hf (i + 1) n hi) i (Nat.lt_succ_self i)
  simp only [map_sub, sub_eq_zero] at h
  simp only [map_sub, coeff_mk, sub_eq_zero, h]

private theorem padic_dvd_iff (n : ℕ) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ^ n ∣ x ↔ ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  simpa only [Nat.cast_ofNat, Ideal.mem_span_singleton] using
    (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

private theorem padic_separated (x : ℤ_[2]) (h : ∀ n : ℕ, (2 : ℤ_[2]) ^ n ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt 2 (norm_pos_iff.mpr hx)
  exact hn.not_ge ((padic_dvd_iff n x).mp (h n))

private theorem padic_complete (f : ℕ → ℤ_[2])
    (hf : ∀ n m, n ≤ m → (2 : ℤ_[2]) ^ n ∣ f m - f n) :
    ∃ x, ∀ n, (2 : ℤ_[2]) ^ n ∣ x - f n := by
  have hdist (n m : ℕ) (h : n ≤ m) : dist (f m) (f n) ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
    rw [dist_eq_norm]
    exact (padic_dvd_iff n _).mp (hf n m h)
  have hc : CauchySeq f := Metric.cauchySeq_iff'.mpr fun ε hε => by
    obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt 2 hε
    exact ⟨n, fun m hm => (hdist n m hm).trans_lt hn⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun n => (padic_dvd_iff n _).mpr ?_⟩
  rw [← dist_eq_norm]
  exact le_of_tendsto (hx.dist tendsto_const_nhds) <|
    (eventually_ge_atTop n).mono fun m hm => hdist n m hm

private theorem padic_itinerary_bijective :
    Function.Bijective (itinerary twoAdicCollatz (PadicInt.toZMod (p := 2))) := by
  have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 1 := by
    rw [map_ofNat]
    decide
  have hunit : IsUnit (3 : ℤ_[2]) := by
    by_contra h
    have hm : (3 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, h3] at hm
    exact one_ne_zero hm
  obtain ⟨u, hu⟩ := hunit
  refine itinerary_bijective 2 two_ne_zero PadicInt.toZMod ?_ u (hu ▸ h3) 1 (map_one _)
    twoAdicCollatz (fun x => ?_) padic_separated padic_complete
  · rw [map_ofNat]
    decide
  · by_cases hx : PadicInt.toZMod x = 0
    · simpa only [ite_eq_left hx] using two_mul_twoAdicCollatz_of_even hx
    · simpa only [ite_eq_right hx, hu] using two_mul_twoAdicCollatz_of_odd hx

private theorem powerSeries_itinerary_bijective (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    Function.Bijective (itinerary (qCollatz A B) (constantCoeff (R := ZMod 2))) := by
  have hbit : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hA)
  refine itinerary_bijective X X_ne_zero constantCoeff constantCoeff_X u
    (by rw [hu]; exact hbit _ hA) B (hbit _ hB) (qCollatz A B) (fun x => ?_)
    powerSeries_separated powerSeries_complete
  rw [qCollatz, hu]
  split_ifs with hx
  · obtain ⟨y, rfl⟩ := X_dvd_iff.mpr hx
    rw [qShift_X_mul]
  · have hy : constantCoeff (A * x + B) = 0 := by
      have hone : (1 : ZMod 2) + 1 = 0 := by decide
      simpa [hbit _ hx, hbit _ hA, hbit _ hB] using hone
    obtain ⟨y, hy⟩ := X_dvd_iff.mpr hy
    rw [hy, qShift_X_mul]

end qCollatz_one_add_X_conjugate_twoAdicCollatz

open qCollatz_one_add_X_conjugate_twoAdicCollatz in
/-- **The $q$-Collatz map is conjugate to the $2$-adic $3x+1$ map.** Let $A$ and $B$ be odd
power series in $\mathbb{F}_2[[q]]$ (constant term $1$), let $T_{A,B}$ be the $q$-analog of the
$3x+1$ map on $\mathbb{F}_2[[q]]$, and let $T$ be the $3x+1$ map on the $2$-adic integers
$\mathbb{Z}_2$. Then there is a bijection $h : \mathbb{Z}_2 \to \mathbb{F}_2[[q]]$ with
$h^{-1}(T_{A,B}(h(x))) = T(x)$ for every $x \in \mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 2 (`jis-2025-25.6.8-thm-2`). -/
public theorem qCollatz_conjugate_twoAdicCollatz (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz A B (h x)) = twoAdicCollatz x := by
  classical
  let p := Equiv.ofBijective _ padic_itinerary_bijective
  let q := Equiv.ofBijective _ (powerSeries_itinerary_bijective A B hA hB)
  refine ⟨p.trans q.symm, fun x => (p.trans q.symm).injective ?_⟩
  simp only [Equiv.apply_symm_apply]
  apply q.injective
  funext n
  change constantCoeff ((qCollatz A B)^[n] (qCollatz A B (q.symm (p x)))) =
    q (q.symm (p (twoAdicCollatz x))) n
  rw [q.apply_symm_apply, ← Function.iterate_succ_apply]
  change q (q.symm (p x)) (n + 1) = p (twoAdicCollatz x) n
  rw [q.apply_symm_apply]
  exact congrArg (PadicInt.toZMod (p := 2)) (Function.iterate_succ_apply _ _ _)

/-- **The map $T_{1+q,1}$ is conjugate to the $2$-adic $3x+1$ map.** Let $T_q = T_{1+q,1}$
be the $q$-analog of the $3x+1$ map with $A = 1 + q$ and $B = 1$, so that $T_q(x) = x/q$ if $q$
divides $x$ and $T_q(x) = ((1+q)x + 1)/q$ otherwise, and let $T$ be the $3x+1$ map on the
$2$-adic integers $\mathbb{Z}_2$. Then there is a bijection $h : \mathbb{Z}_2 \to \mathbb{F}_2[[q]]$
with $h^{-1}(T_q(h(x))) = T(x)$ for every $x \in \mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Corollary 3 (`jis-2025-25.6.8-cor-3`). -/
public theorem qCollatz_one_add_X_conjugate_twoAdicCollatz :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz (1 + X) 1 (h x)) = twoAdicCollatz x :=
  qCollatz_conjugate_twoAdicCollatz (1 + X) 1 (by simp) (by simp)

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilter
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Bloom filters: the false-positive rate under uniform hashing

A Bloom filter (Bloom 1970) with `m` bits and `k` hash functions stores `n` elements by setting
the `k n` bits their hash values select; a query for a further element `y` reports "maybe
present" when all `k` bits selected by `y` are set. Under the standard idealisation of uniform
hashing, the `k n` hash values of the stored elements and the `k` hash values of `y` are
independent and uniform on the `m` bits. The probability space is finite and uniform: the
outcomes are the functions `Fin n → Fin k → Fin m` (stored hash values) paired with
`Fin k → Fin m` (query hash values), and probabilities are counting ratios.

Bloom's classical formula `(1 - (1 - 1/m) ^ (k n)) ^ k` is **not** the false-positive rate:
the bit occupancies are dependent. It is the `k`-th power of the expected fraction of set bits,
and, by Jensen's inequality, a lower bound on the exact rate (Bose et al. 2008 show the bound is
strict for `k ≥ 2`; the test file checks a strict instance).

## Main results

* `mayContain_insertAll_empty_iff`: after inserting a list into an empty filter, `y` is reported
  present iff every bit `y` selects is selected by some stored element: the event analysed
  below.
* `card_unset`: exactly `(m - 1) ^ (n * k)` outcomes leave a given bit unset, so a bit is unset
  with probability `(1 - 1/m) ^ (n * k)` (`prob_unset`).
* `expected_fraction_set`: the expected fraction of set bits is `1 - (1 - 1/m) ^ (n * k)`.
* `falsePositiveProb_eq`: the exact false-positive rate is the expectation of
  `(fraction of set bits) ^ k`.
* `classical_le_falsePositiveProb`: Bloom's formula is a lower bound on the exact rate.
* `exp_approx_le_falsePositiveProb`: so is the further approximation
  `(1 - exp (-(k n) / m)) ^ k`.
* `expApprox_optimal`: on real `k > 0` the approximation `(1 - exp (-k n / m)) ^ k` is minimal
  at `k = (m / n) log 2`, where it equals `(1 / 2) ^ k`.

Not covered: the exact closed form of the rate via Stirling numbers of the second kind
(Bose et al. 2008, Theorem 1) and its upper bounds.

## References

* B. H. Bloom, *Space/time trade-offs in hash coding with allowable errors*, Comm. ACM 13
  (1970), 422–426.
* P. Bose, H. Guo, E. Kranakis, A. Maheshwari, P. Morin, J. Morrison, M. Smid and Y. Tang,
  *On the false-positive rate of Bloom filters*, Inform. Process. Lett. 108 (2008), 210–213.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BloomFilter

open Finset

universe u

section Insert

variable {α : Type u} {m : ℕ}

/-- Insert every element of a list, left to right. -/
def insertAll (filter : BloomFilter α m) (xs : List α) : BloomFilter α m :=
  xs.foldl BloomFilter.insert filter

/-- Insertion keeps the hash functions. -/
theorem hashes_insertAll (filter : BloomFilter α m) (xs : List α) :
    (filter.insertAll xs).hashes = filter.hashes := by
  induction xs generalizing filter with
  | nil => rfl
  | cons x xs ih => exact ih (filter.insert x)

/-- After inserting a list, bit `i` is set iff it was set before or some hash function sends
some inserted element to `i`. -/
theorem bit_insertAll_iff (filter : BloomFilter α m) (xs : List α) (i : Fin m) :
    (filter.insertAll xs).bits[i] = true ↔
      filter.bits[i] = true ∨ ∃ x ∈ xs, ∃ h ∈ filter.hashes, h x = i := by
  induction xs generalizing filter with
  | nil => simp [insertAll]
  | cons x xs ih =>
      change ((filter.insert x).insertAll xs).bits[i] = true ↔ _
      rw [ih, bit_insert_iff]
      change (filter.bits[i] = true ∨ ∃ h ∈ filter.hashes, h x = i) ∨
          (∃ y ∈ xs, ∃ h ∈ filter.hashes, h y = i) ↔ _
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [or_assoc]

/-- The false-positive event: after inserting `xs` into an empty filter, `y` is reported
present iff every bit selected by `y` is selected by some stored element. -/
theorem mayContain_insertAll_empty_iff (hashes : List (α → Fin m)) (xs : List α) (y : α) :
    ((empty hashes).insertAll xs).mayContain y = true ↔
      ∀ h ∈ hashes, ∃ x ∈ xs, ∃ h' ∈ hashes, h' x = h y := by
  rw [mayContain_iff, hashes_insertAll]
  refine forall₂_congr fun h _ => ?_
  rw [bit_insertAll_iff]
  simp [empty]

end Insert

section Uniform

variable {m n k : ℕ}

/-- The bits set by the stored hash values `H a j` (element `a`, hash function `j`). -/
def setBits (H : Fin n → Fin k → Fin m) : Finset (Fin m) :=
  univ.image fun p : Fin n × Fin k => H p.1 p.2

/-- A bit is unset iff no stored hash value selects it. -/
theorem notMem_setBits_iff (H : Fin n → Fin k → Fin m) (i : Fin m) :
    i ∉ setBits H ↔ ∀ a j, H a j ≠ i := by
  simp [setBits]

variable (m n k) in
/-- The exact false-positive rate under uniform hashing: the fraction of outcomes (stored hash
values `H`, query hash values `q`) in which every query bit is set. -/
noncomputable def falsePositiveProb : ℝ :=
  (#{Hq : (Fin n → Fin k → Fin m) × (Fin k → Fin m) | ∀ j, Hq.2 j ∈ setBits Hq.1} : ℝ) /
    Fintype.card ((Fin n → Fin k → Fin m) × (Fin k → Fin m))

/-- Exactly `(m - 1) ^ (n * k)` outcomes of the stored hash values leave bit `i` unset. -/
theorem card_unset (i : Fin m) :
    #{H : Fin n → Fin k → Fin m | i ∉ setBits H} = (m - 1) ^ (n * k) := by
  have : ({H : Fin n → Fin k → Fin m | i ∉ setBits H} : Finset _) =
      Fintype.piFinset fun _ => Fintype.piFinset fun _ => univ.erase i := by
    ext H
    simp [notMem_setBits_iff, Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp [Fintype.card_piFinset, card_erase_of_mem, ← pow_mul, mul_comm]

/-- A given bit is unset with probability `(1 - 1/m) ^ (n * k)`. -/
theorem prob_unset (hm : 0 < m) (i : Fin m) :
    (#{H : Fin n → Fin k → Fin m | i ∉ setBits H} : ℝ) /
      Fintype.card (Fin n → Fin k → Fin m) = (1 - 1 / (m : ℝ)) ^ (n * k) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [card_unset]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  rw [← pow_mul, mul_comm k n, ← div_pow, sub_div, div_self hm']

private theorem sum_card_setBits :
    ∑ H : Fin n → Fin k → Fin m, (#(setBits H) : ℝ) =
      m * ((m : ℝ) ^ (n * k) - ((m : ℝ) - 1) ^ (n * k)) := by
  have hcard (H : Fin n → Fin k → Fin m) :
      (#(setBits H) : ℝ) = ∑ i : Fin m, if i ∈ setBits H then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole, Finset.filter_univ_mem]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  have hin (i : Fin m) :
      (∑ H : Fin n → Fin k → Fin m, if i ∈ setBits H then (1 : ℝ) else 0) =
        (m : ℝ) ^ (n * k) - ((m : ℝ) - 1) ^ (n * k) := by
    rw [Finset.sum_boole]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n → Fin k → Fin m))) (fun H => i ∈ setBits H)
    rw [card_unset, Finset.card_univ] at hsplit
    simp only [Fintype.card_fun, Fintype.card_fin] at hsplit
    have h1 : 1 ≤ m := Fin.pos i
    have hreal : (#{H : Fin n → Fin k → Fin m | i ∈ setBits H} : ℝ) +
        ((m : ℝ) - 1) ^ (n * k) = (m : ℝ) ^ (n * k) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hsplit
      push_cast [Nat.cast_sub h1] at this
      rw [this, ← pow_mul, mul_comm k n]
    linarith
  simp_rw [hin]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The expected fraction of set bits is `1 - (1 - 1/m) ^ (n * k)`. -/
theorem expected_fraction_set (hm : 0 < m) :
    (∑ H : Fin n → Fin k → Fin m, (#(setBits H) : ℝ) / m) /
      Fintype.card (Fin n → Fin k → Fin m) = 1 - (1 - 1 / (m : ℝ)) ^ (n * k) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [← Finset.sum_div, sum_card_setBits]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← pow_mul, mul_comm k n, one_sub_div hm', div_pow]
  field_simp

/-- The exact false-positive rate is the expectation of `(fraction of set bits) ^ k`. -/
theorem falsePositiveProb_eq (hm : 0 < m) :
    falsePositiveProb m n k =
      (∑ H : Fin n → Fin k → Fin m, ((#(setBits H) : ℝ) / m) ^ k) /
        Fintype.card (Fin n → Fin k → Fin m) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hcount : #{Hq : (Fin n → Fin k → Fin m) × (Fin k → Fin m) |
      ∀ j, Hq.2 j ∈ setBits Hq.1} = ∑ H : Fin n → Fin k → Fin m, #(setBits H) ^ k := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [← Finset.card_filter]
    have : ({q : Fin k → Fin m | ∀ j, q j ∈ setBits H} : Finset _) =
        Fintype.piFinset fun _ => setBits H := by
      ext q
      simp [Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    simp
  unfold falsePositiveProb
  rw [hcount, Fintype.card_prod]
  push_cast
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_div, mul_comm ((m : ℝ) ^ k)]

/-- **Bloom's formula is a lower bound** on the exact false-positive rate (Jensen's
inequality for `t ↦ t ^ k`). -/
theorem classical_le_falsePositiveProb (hm : 0 < m) :
    (1 - (1 - 1 / (m : ℝ)) ^ (n * k)) ^ k ≤ falsePositiveProb m n k := by
  rw [falsePositiveProb_eq hm, ← expected_fraction_set hm]
  set N : ℝ := (Fintype.card (Fin n → Fin k → Fin m) : ℝ)
  have hN : 0 < N := by
    simp only [N, Fintype.card_fun, Fintype.card_fin]
    positivity
  have hf : ∀ H ∈ (univ : Finset (Fin n → Fin k → Fin m)),
      0 ≤ (#(setBits H) : ℝ) / m := fun _ _ => by positivity
  rcases k with _ | j
  · simp [N]
  · have hJ := pow_sum_div_card_le_sum_pow hf j
    rw [Finset.card_univ] at hJ
    rw [div_pow, div_le_div_iff₀ (by positivity) hN]
    calc (∑ H, (#(setBits H) : ℝ) / m) ^ (j + 1) * N
        = (∑ H, (#(setBits H) : ℝ) / m) ^ (j + 1) / N ^ j * N ^ (j + 1) := by
          field_simp
          ring
      _ ≤ (∑ H, ((#(setBits H) : ℝ) / m) ^ (j + 1)) * N ^ (j + 1) := by
          gcongr

/-- The exponential approximation `(1 - exp (-(k n) / m)) ^ k` is also a lower bound. -/
theorem exp_approx_le_falsePositiveProb (hm : 0 < m) :
    (1 - Real.exp (-((n * k : ℕ) : ℝ) / m)) ^ k ≤ falsePositiveProb m n k := by
  refine le_trans ?_ (classical_le_falsePositiveProb hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 0 ≤ 1 - 1 / (m : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hm1
  have hexp : (1 - 1 / (m : ℝ)) ^ (n * k) ≤ Real.exp (-((n * k : ℕ) : ℝ) / m) := by
    calc (1 - 1 / (m : ℝ)) ^ (n * k) ≤ Real.exp (-(1 / (m : ℝ))) ^ (n * k) := by
          gcongr
          linarith [Real.add_one_le_exp (-(1 / (m : ℝ)))]
      _ = Real.exp (-((n * k : ℕ) : ℝ) / m) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hle1 : Real.exp (-((n * k : ℕ) : ℝ) / m) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (by positivity)
  gcongr

end Uniform

section OptimalK

private noncomputable def numerator (t : ℝ) : ℝ :=
  (1 - t) * Real.log (1 - t) - t * Real.log t

private lemma numerator_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt numerator (-Real.log (1 - t) - Real.log t - 2) t := by
  have h := ((Real.hasDerivAt_mul_log (by linarith : 1 - t ≠ 0)).comp t
    ((hasDerivAt_id t).const_sub 1)).sub (Real.hasDerivAt_mul_log ht0.ne')
  convert h using 1
  · ext x
    rfl
  · ring

private lemma numerator_deriv2 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (deriv^[2] numerator) t = (1 - t)⁻¹ - t⁻¹ := by
  have heq : deriv numerator =ᶠ[nhds t]
      (fun x => -Real.log (1 - x) - Real.log x - 2) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with x hx
    exact (numerator_hasDerivAt hx.1 hx.2).deriv
  have h := ((((hasDerivAt_id t).const_sub 1).log
    (by linarith : 1 - t ≠ 0)).neg.sub (Real.hasDerivAt_log ht0.ne')).sub_const 2
  change deriv (deriv numerator) t = _
  rw [heq.deriv_eq]
  convert h.deriv using 1 <;>
    simp only [Pi.sub_apply, Pi.neg_apply, id_eq, neg_div, one_div, neg_neg]

private lemma numerator_pos {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2) :
    0 < numerator t := by
  have hc : StrictConcaveOn ℝ (Set.Icc 0 (1 / 2)) numerator := by
    refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _) ?_ ?_
    · exact ((Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).sub
        Real.continuous_mul_log).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [numerator_deriv2 hx.1 (by linarith [hx.2])]
      exact sub_neg.mpr ((inv_lt_inv₀ (by linarith [hx.2]) hx.1).mpr (by linarith [hx.2]))
  have h := hc.lt_on_open_segment' (x := (0 : ℝ)) (y := (1 / 2 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
    (a := 1 - 2 * t) (b := 2 * t) (by linarith) (by linarith) (by ring)
  have hend : numerator 0 = 0 ∧ numerator (1 / 2) = 0 := by
    constructor <;> norm_num [numerator]
  have hpoint : (1 - 2 * t) • (0 : ℝ) + (2 * t) • (1 / 2 : ℝ) = t := by
    simp only [smul_eq_mul]
    ring
  rwa [hend.1, hend.2, min_self, hpoint] at h

private lemma log_product_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => Real.log x * Real.log (1 - x))
      (numerator t / (t * (1 - t))) t := by
  have h := (Real.hasDerivAt_log ht0.ne').mul
    (((hasDerivAt_id t).const_sub 1).log (by linarith : 1 - t ≠ 0))
  convert h using 1
  · ext x
    rfl
  · dsimp [numerator]
    field_simp [ht0.ne', (sub_pos.mpr ht1).ne']
    ring

private lemma log_product_strictMono :
    StrictMonoOn (fun t => Real.log t * Real.log (1 - t)) (Set.Ioc 0 (1 / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro t ht
    exact (log_product_hasDerivAt ht.1 (by linarith [ht.2])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    rw [(log_product_hasDerivAt ht.1 (by linarith [ht.2])).deriv]
    exact div_pos (numerator_pos ht.1 ht.2) (mul_pos ht.1 (by linarith [ht.2]))

private lemma log_product_half :
    Real.log (1 / 2) * Real.log (1 - 1 / 2) = Real.log 2 ^ 2 := by
  norm_num [Real.log_div]
  ring

private lemma log_product_lt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hne : t ≠ 1 / 2) : Real.log t * Real.log (1 - t) < Real.log 2 ^ 2 := by
  rcases lt_trichotomy t (1 / 2) with ht | ht | ht
  · calc
      Real.log t * Real.log (1 - t)
          < Real.log (1 / 2) * Real.log (1 - 1 / 2) :=
        log_product_strictMono ⟨ht0, ht.le⟩ (by constructor <;> norm_num) ht
      _ = Real.log 2 ^ 2 := log_product_half
  · exact (hne ht).elim
  · have hs : 1 - (1 - t) = t := by ring
    calc
      Real.log t * Real.log (1 - t)
          = Real.log (1 - t) * Real.log (1 - (1 - t)) := by rw [hs, mul_comm]
      _ < Real.log (1 / 2) * Real.log (1 - 1 / 2) :=
        log_product_strictMono ⟨by linarith, by linarith⟩
          (by constructor <;> norm_num) (by linarith)
      _ = Real.log 2 ^ 2 := log_product_half

/-- `log t * log (1 - t) ≤ (log 2) ^ 2` on `(0, 1)`. -/
theorem log_mul_log_one_sub_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log t * Real.log (1 - t) ≤ Real.log 2 ^ 2 := by
  by_cases ht : t = 1 / 2
  · subst t
    exact log_product_half.le
  · exact (log_product_lt ht0 ht1 ht).le

/-- Equality holds only at `t = 1 / 2`. -/
theorem log_mul_log_one_sub_eq_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log t * Real.log (1 - t) = Real.log 2 ^ 2 ↔ t = 1 / 2 := by
  constructor
  · intro heq
    by_contra hne
    exact (log_product_lt ht0 ht1 hne).ne heq
  · rintro rfl
    exact log_product_half


/-- The exponential approximation `(1 - exp (-κ n / m)) ^ κ` of the false-positive rate, as a
function of a real number `κ` of hash functions. -/
noncomputable def expApprox (m n : ℕ) (κ : ℝ) : ℝ := (1 - Real.exp (-κ * n / m)) ^ κ

/-- At `κ = (m / n) log 2` half of the bits are expected to be set and the approximation is
`(1 / 2) ^ κ`. -/
theorem expApprox_at_optimum {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    expApprox m n (m / n * Real.log 2) = (1 / 2) ^ ((m : ℝ) / n * Real.log 2) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold expApprox
  congr 1
  have : -((m : ℝ) / n * Real.log 2) * n / m = -Real.log 2 := by field_simp
  rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- **The optimal number of hash functions** for the exponential approximation: on real
`κ > 0`, `(1 - exp (-κ n / m)) ^ κ` is minimal at `κ = (m / n) log 2`. -/
theorem expApprox_optimal {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {κ : ℝ} (hκ : 0 < κ) :
    expApprox m n (m / n * Real.log 2) ≤ expApprox m n κ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := n / m with hr
  have hr0 : 0 < r := by positivity
  set t : ℝ := Real.exp (-κ * n / m) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have hexp_arg : -κ * n / m = -(κ * r) := by rw [hr]; ring
  have ht1 : t < 1 := by
    rw [ht, hexp_arg, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (by positivity)
  have hlogt : Real.log t = -(κ * r) := by rw [ht, hexp_arg, Real.log_exp]
  have hκ_eq : κ = -Real.log t / r := by rw [hlogt]; field_simp
  rw [expApprox_at_optimum hm hn]
  unfold expApprox
  rw [← ht, Real.rpow_def_of_pos (show (0 : ℝ) < 1 - t by linarith),
    Real.rpow_def_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  apply Real.exp_le_exp.mpr
  have hkey := log_mul_log_one_sub_le ht0 ht1
  have hlhs : Real.log (1 / 2) * ((m : ℝ) / n * Real.log 2) = -(Real.log 2 ^ 2) / r := by
    rw [one_div, Real.log_inv, hr]
    field_simp
  rw [hlhs, hκ_eq]
  have : Real.log (1 - t) * (-Real.log t / r) = -(Real.log t * Real.log (1 - t)) / r := by
    ring
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith) hr0.le

end OptimalK

end Cslib.Algorithms.Lean.BloomFilter

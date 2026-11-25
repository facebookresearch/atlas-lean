/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős problem 429

For every function $f : \mathbb{N} \to \mathbb{N}$ with $f(N) \to \infty$, the main result
`erdos429_refuted` produces an infinite set $A$ of natural numbers, sparse with respect to
$f$, meeting no residue class obstruction and admitting no translate consisting entirely
of primes. The set is a sparse subsequence of the even squares $4k^2$: even squares miss
a residue class modulo every prime, and the exponents are chosen diagonally so that every
integer translate of $A$ contains a composite value.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem429Wanted

open Filter

/-- An enumeration of the integers, used to diagonalise over all translates. -/
private def enumIdx (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 + 1 : ℕ)) : ℤ)

private lemma enumIdx_zero : enumIdx 0 = 0 := by simp [enumIdx]

private lemma enumIdx_surjective : Function.Surjective enumIdx := by
  intro z
  by_cases hz : 0 ≤ z
  · refine ⟨2 * z.natAbs, ?_⟩
    have hmod : (2 * z.natAbs) % 2 = 0 := by omega
    have hdiv : (2 * z.natAbs) / 2 = z.natAbs := by omega
    unfold enumIdx
    rw [ite_eq_left (by omega), hdiv]
    exact Int.natAbs_of_nonneg hz
  · have hzlt : z < 0 := lt_of_not_ge hz
    refine ⟨2 * z.natAbs - 1, ?_⟩
    have hm : 1 ≤ z.natAbs := Int.natAbs_pos.mpr (ne_of_lt hzlt)
    have hmod : (2 * z.natAbs - 1) % 2 = 1 := by omega
    have hdiv : (2 * z.natAbs - 1) / 2 + 1 = z.natAbs := by omega
    unfold enumIdx
    rw [ite_eq_right (by omega), hdiv]
    have hcast : ((z.natAbs : ℕ) : ℤ) = -z := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hzlt))
    rw [hcast, neg_neg]

/-- A threshold for `f`: every `N` at or beyond it has `M ≤ f N`. -/
private noncomputable def threshold (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (M : ℕ) : ℕ :=
  Classical.choose (Filter.eventually_atTop.mp
    (hf.eventually (Filter.eventually_ge_atTop M)))

private lemma threshold_spec {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} {M N : ℕ}
    (hN : threshold f hf M ≤ N) : M ≤ f N :=
  Classical.choose_spec (Filter.eventually_atTop.mp
    (hf.eventually (Filter.eventually_ge_atTop M))) N hN

/-- The modulus forced on the exponent for the translate `enumIdx j`: a multiple of it
makes the translate factor, except for the translate `1`, where the exponent is forced
to be `1` modulo `5`. -/
private def modulus (n : ℤ) : ℕ := if n = 1 then 5 else max 1 n.natAbs

private def residue (n : ℤ) : ℕ := if n = 1 then 1 else 0

private lemma modulus_pos (n : ℤ) : 0 < modulus n := by
  unfold modulus
  split <;> omega

private lemma residue_le_one (n : ℤ) : residue n ≤ 1 := by
  unfold residue
  split <;> omega

private lemma residue_eq_zero_of_ne {n : ℤ} (h : n ≠ 1) : residue n = 0 := by
  simp [residue, h]

/-- The product of the moduli up to `j`, used to make the exponents grow. -/
private def cumProd (j : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (j + 1), modulus (enumIdx i)

private lemma cumProd_pos (j : ℕ) : 0 < cumProd j :=
  Finset.prod_pos (fun _ _ => modulus_pos _)

private lemma modulus_dvd_cumProd (j : ℕ) : modulus (enumIdx j) ∣ cumProd j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self j))

/-- The running maximum of the thresholds, so the levels below are monotone. -/
private noncomputable def cumSup (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) : ℕ :=
  (Finset.range (j + 1)).sup (fun i => threshold f hf (i + 1))

private lemma cumSup_mono {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} : Monotone (cumSup f hf) :=
  fun _ _ hij => Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hij))

private lemma threshold_le_cumSup {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} (j : ℕ) :
    threshold f hf (j + 1) ≤ cumSup f hf j := by
  unfold cumSup
  show threshold f hf (j + 1) ≤
    (Finset.range (j + 1)).sup (fun i : ℕ => threshold f hf (i + 1))
  exact Finset.le_sup (f := fun i => threshold f hf (i + 1))
    (Finset.mem_range.mpr (Nat.lt_succ_self j))

/-- The level of index `j`, strictly increasing in `j`. -/
private noncomputable def level (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) : ℕ :=
  j + cumSup f hf j

private lemma level_strictMono {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} : StrictMono (level f hf) := by
  intro i j hij
  have h := cumSup_mono (f := f) (hf := hf) (le_of_lt hij)
  unfold level
  omega

/-- The exponent of the `j`-th element of the sparse set. -/
private noncomputable def expSeq (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) : ℕ :=
  cumProd j * (level f hf j + 1) + residue (enumIdx j)

private lemma cumProd_le_cumProd {i j : ℕ} (hij : i ≤ j) : cumProd i ≤ cumProd j := by
  unfold cumProd
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono (Nat.succ_le_succ hij))
  intro _ _ _
  exact modulus_pos _

private lemma expSeq_pos {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} (j : ℕ) :
    0 < expSeq f hf j := by
  have h : 0 < cumProd j * (level f hf j + 1) :=
    Nat.mul_pos (cumProd_pos j) (Nat.succ_pos _)
  unfold expSeq
  omega

private lemma expSeq_gt_level {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} (j : ℕ) :
    level f hf j < expSeq f hf j := by
  have h1 : level f hf j + 1 ≤ cumProd j * (level f hf j + 1) :=
    le_mul_of_one_le_left (Nat.zero_le _) (cumProd_pos j)
  unfold expSeq
  omega

private lemma expSeq_strictMono {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} : StrictMono (expSeq f hf) := by
  intro i j hij
  have hP : cumProd i ≤ cumProd j := cumProd_le_cumProd (le_of_lt hij)
  have hL : level f hf i < level f hf j := level_strictMono hij
  have h2 : cumProd i * (level f hf j + 1) ≤ cumProd j * (level f hf j + 1) :=
    Nat.mul_le_mul_right _ hP
  have hr : residue (enumIdx i) ≤ 1 := residue_le_one _
  have hkey : cumProd i * (level f hf i + 1) + residue (enumIdx i) <
      cumProd j * (level f hf j + 1) := by
    by_cases hres : residue (enumIdx i) = 0
    · have hlt : cumProd i * (level f hf i + 1) < cumProd i * (level f hf j + 1) :=
        (Nat.mul_lt_mul_left (cumProd_pos i)).mpr (by omega)
      omega
    · have hres1 : residue (enumIdx i) = 1 := by
        have hle := residue_le_one (enumIdx i)
        omega
      have hei : enumIdx i = 1 := by
        by_contra hne
        rw [residue_eq_zero_of_ne hne] at hres1
        exact zero_ne_one hres1
      have h5 : 5 ≤ cumProd i := by
        have hdvd := modulus_dvd_cumProd i
        rw [hei, show modulus (1 : ℤ) = 5 from by simp [modulus]] at hdvd
        exact Nat.le_of_dvd (cumProd_pos i) hdvd
      have hmul : cumProd i * (level f hf i + 2) ≤ cumProd i * (level f hf j + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have heq : cumProd i * (level f hf i + 2) =
          cumProd i * (level f hf i + 1) + cumProd i := by ring
      omega
  unfold expSeq
  omega

private lemma expSeq_ge_two_of_pos {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} {j : ℕ} (hj : 1 ≤ j) :
    2 ≤ expSeq f hf j := by
  have hL : 1 ≤ level f hf j := le_trans hj (Nat.le_add_right j _)
  have h2 : 2 ≤ cumProd j * (level f hf j + 1) := by
    calc 2 = 1 * 2 := by norm_num
      _ ≤ cumProd j * (level f hf j + 1) :=
          Nat.mul_le_mul (cumProd_pos j) (by omega)
  unfold expSeq
  omega

/-- The `j`-th element of the sparse set, an even square. -/
private noncomputable def termSeq (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (j : ℕ) : ℕ :=
  4 * (expSeq f hf j) ^ 2

private lemma termSeq_strictMono {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} :
    StrictMono (termSeq f hf) := by
  intro i j hij
  have h := expSeq_strictMono (f := f) (hf := hf) hij
  have hpow : (expSeq f hf i) ^ 2 < (expSeq f hf j) ^ 2 :=
    pow_lt_pow_left₀ h (Nat.zero_le _) two_ne_zero
  unfold termSeq
  exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mpr hpow

private lemma threshold_le_termSeq {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} (j : ℕ) :
    threshold f hf (j + 1) ≤ termSeq f hf j := by
  have h1 : threshold f hf (j + 1) ≤ cumSup f hf j := threshold_le_cumSup j
  have h2 : cumSup f hf j ≤ level f hf j := by unfold level; omega
  have h3 : level f hf j < expSeq f hf j := expSeq_gt_level j
  have h4 : expSeq f hf j ≤ (expSeq f hf j) ^ 2 :=
    Nat.le_self_pow two_ne_zero _
  have h5 : (expSeq f hf j) ^ 2 ≤ termSeq f hf j := by
    unfold termSeq
    exact Nat.le_mul_of_pos_left _ (by norm_num : 0 < 4)
  omega

private lemma modulus_dvd_expSeq_of_ne {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} {j : ℕ}
    (h : enumIdx j ≠ 1) : modulus (enumIdx j) ∣ expSeq f hf j := by
  obtain ⟨c, hc⟩ := modulus_dvd_cumProd j
  refine ⟨c * (level f hf j + 1), ?_⟩
  unfold expSeq
  rw [residue_eq_zero_of_ne h, hc, add_zero]
  ring

private lemma expSeq_eq_five_mul_add_one {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} {j : ℕ}
    (h : enumIdx j = 1) : ∃ q : ℕ, expSeq f hf j = 5 * q + 1 := by
  have hdvd : (5 : ℕ) ∣ cumProd j := by
    have h' := modulus_dvd_cumProd j
    rw [h, show modulus (1 : ℤ) = 5 from by simp [modulus]] at h'
    exact h'
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c * (level f hf j + 1), by
    unfold expSeq
    rw [show residue (enumIdx j) = 1 from by simp [residue, h], hc]
    ring⟩

/-- A value presented as a product of two factors larger than one is not prime. -/
private lemma not_prime_toNat_of_eq_mul {S : ℤ} {x y : ℕ} (hx : 1 < x) (hy : 1 < y)
    (hS : S = ((x * y : ℕ) : ℤ)) : ¬ S.toNat.Prime := by
  rw [hS, Int.toNat_natCast]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- No translate of the sparse set consists entirely of primes. -/
private lemma not_prime_shift {f : ℕ → ℕ}
    {hf : Filter.Tendsto f Filter.atTop Filter.atTop} (j : ℕ) :
    ¬ (enumIdx j + ((termSeq f hf j : ℕ) : ℤ)).toNat.Prime := by
  have hkpos : 0 < expSeq f hf j := expSeq_pos j
  have hterm : ((termSeq f hf j : ℕ) : ℤ) = 4 * (expSeq f hf j : ℤ) ^ 2 := by
    unfold termSeq
    push_cast
    ring
  by_cases h1 : enumIdx j = 1
  · obtain ⟨q, hq⟩ := expSeq_eq_five_mul_add_one h1
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exfalso
        rw [hj, enumIdx_zero] at h1
        exact zero_ne_one h1
      · exact hj
    have hk6 : 6 ≤ expSeq f hf j := by
      have hP : 5 ≤ cumProd j := by
        have h' := modulus_dvd_cumProd j
        rw [h1, show modulus (1 : ℤ) = 5 from by simp [modulus]] at h'
        exact Nat.le_of_dvd (cumProd_pos j) h'
      have hL : 1 ≤ level f hf j := le_trans hj1 (Nat.le_add_right j _)
      have h2 : 5 * 2 ≤ cumProd j * (level f hf j + 1) :=
        Nat.mul_le_mul hP (by omega)
      unfold expSeq
      omega
    have hqpos : 1 ≤ q := by
      have hge : 5 * q + 1 ≥ 6 := by rw [← hq]; exact hk6
      omega
    have hI : enumIdx j + ((termSeq f hf j : ℕ) : ℤ) =
        ((1 + 4 * (expSeq f hf j) ^ 2 : ℕ) : ℤ) := by
      rw [h1, hterm]
      push_cast
      ring
    rw [hI, Int.toNat_natCast]
    have hdvd : 5 ∣ 1 + 4 * (expSeq f hf j) ^ 2 :=
      ⟨20 * q ^ 2 + 8 * q + 1, by rw [hq]; ring⟩
    have hgt : 5 < 1 + 4 * (expSeq f hf j) ^ 2 := by
      have hsq : 36 ≤ (expSeq f hf j) ^ 2 := by
        calc 36 = 6 ^ 2 := by norm_num
          _ ≤ (expSeq f hf j) ^ 2 := Nat.pow_le_pow_left hk6 2
      omega
    intro hp
    rcases hp.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega
  by_cases h0 : enumIdx j = 0
  · refine not_prime_toNat_of_eq_mul (x := 2) (y := 2 * (expSeq f hf j) ^ 2)
      (by norm_num) ?_ ?_
    · have hsq : 1 ≤ (expSeq f hf j) ^ 2 := Nat.one_le_pow 2 _ hkpos
      omega
    · rw [h0, hterm]
      push_cast
      ring
  by_cases hm1 : enumIdx j = -1
  · have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exfalso
        rw [hj, enumIdx_zero] at hm1
        norm_num at hm1
      · exact hj
    have hk2 : 2 ≤ expSeq f hf j := expSeq_ge_two_of_pos hj1
    refine not_prime_toNat_of_eq_mul (x := 2 * expSeq f hf j - 1)
      (y := 2 * expSeq f hf j + 1) ?_ ?_ ?_
    · omega
    · omega
    · have hcast : (((2 * expSeq f hf j - 1) * (2 * expSeq f hf j + 1) : ℕ) : ℤ) =
          -1 + 4 * (expSeq f hf j : ℤ) ^ 2 := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * expSeq f hf j)]
        push_cast
        ring
      rw [hm1, hterm, ← hcast]
  · by_cases hs2 : 2 ≤ enumIdx j
    · have hZ : ((enumIdx j).natAbs : ℤ) = enumIdx j :=
        Int.natAbs_of_nonneg (by omega : 0 ≤ enumIdx j)
      have hm : 2 ≤ (enumIdx j).natAbs := by
        have h : (2 : ℤ) ≤ ((enumIdx j).natAbs : ℤ) := by rw [hZ]; exact_mod_cast hs2
        exact_mod_cast h
      have hmod : modulus (enumIdx j) = (enumIdx j).natAbs := by
        unfold modulus
        rw [ite_eq_right (by omega : enumIdx j ≠ 1)]
        exact max_eq_right (by omega : 1 ≤ (enumIdx j).natAbs)
      set m := (enumIdx j).natAbs with hmdef
      have hdvd : m ∣ expSeq f hf j := by
        rw [← hmod]
        exact modulus_dvd_expSeq_of_ne (by omega)
      obtain ⟨t, ht⟩ := hdvd
      have htpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with ht0 | ht0
        · exfalso
          rw [ht0, Nat.mul_zero] at ht
          omega
        · exact ht0
      refine not_prime_toNat_of_eq_mul (x := m)
        (y := 1 + 4 * m * t ^ 2) (by omega) ?_ ?_
      · have hpos : 0 < 4 * m * t ^ 2 :=
          Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (pow_pos htpos 2)
        omega
      · rw [hterm]
        have hkZ : (expSeq f hf j : ℤ) = (m : ℤ) * t := by
          rw [ht]
          push_cast
          ring
        have hs : enumIdx j = (m : ℤ) := hZ.symm
        rw [hkZ, hs]
        push_cast
        ring
    · have hsneg : enumIdx j ≤ -2 := by omega
      have hZ : ((enumIdx j).natAbs : ℤ) = -enumIdx j := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega : 0 ≤ -enumIdx j)
      have hm : 2 ≤ (enumIdx j).natAbs := by
        have h : (2 : ℤ) ≤ ((enumIdx j).natAbs : ℤ) := by rw [hZ]; omega
        exact_mod_cast h
      have hmod : modulus (enumIdx j) = (enumIdx j).natAbs := by
        unfold modulus
        rw [ite_eq_right (by omega : enumIdx j ≠ 1)]
        exact max_eq_right (by omega : 1 ≤ (enumIdx j).natAbs)
      set m := (enumIdx j).natAbs with hmdef
      have hdvd : m ∣ expSeq f hf j := by
        rw [← hmod]
        exact modulus_dvd_expSeq_of_ne (by omega)
      obtain ⟨t, ht⟩ := hdvd
      have htpos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with ht0 | ht0
        · exfalso
          rw [ht0, Nat.mul_zero] at ht
          omega
        · exact ht0
      refine not_prime_toNat_of_eq_mul (x := m)
        (y := 4 * m * t ^ 2 - 1) (by omega) ?_ ?_
      · have h8 : 8 ≤ 4 * m * t ^ 2 := by
          calc 8 = 4 * 2 * 1 := by norm_num
            _ ≤ 4 * m * t ^ 2 :=
                Nat.mul_le_mul (Nat.mul_le_mul (le_refl 4) hm)
                  (Nat.one_le_pow 2 t htpos)
        omega
      · rw [hterm]
        have hkZ : (expSeq f hf j : ℤ) = (m : ℤ) * t := by
          rw [ht]
          push_cast
          ring
        have hcast : ((4 * m * t ^ 2 - 1 : ℕ) : ℤ) =
            4 * (m : ℤ) * (t : ℤ) ^ 2 - 1 := by
          rw [Nat.cast_sub (by
            have hpos : 0 < 4 * m * t ^ 2 :=
              Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (pow_pos htpos 2)
            omega)]
          push_cast
          ring
        have hs : enumIdx j = -((m : ℕ) : ℤ) := by omega
        have hprod : ((m * (4 * m * t ^ 2 - 1) : ℕ) : ℤ) =
            (m : ℤ) * ((4 * m * t ^ 2 - 1 : ℕ) : ℤ) := Nat.cast_mul _ _
        rw [hkZ, hs, hprod, hcast]
        ring

def erdos429 : Prop :=
  ∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ A : Set ℕ, A.Infinite → (∀ N : ℕ, (A ∩ Set.Icc 1 N).ncard ≤ f N) →
      (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ b) →
      ∃ n : ℤ, ∀ a ∈ A, (n + (a : ℤ)).toNat.Prime

/-- **Sparse admissible sets without prime translates (Erdős Problem 429).** For every function
$f : \mathbb{N} \to \mathbb{N}$ with $f(N) \to \infty$ as $N \to \infty$, there is an infinite set
$A$ of natural numbers such that $|A \cap \{1, \ldots, N\}| \le f(N)$ for every natural number
$N$, for every prime $p$ some residue class modulo $p$ contains no element of $A$, and for every
integer $n$ some $a \in A$ makes $n + a$ not a positive prime.

Resolved false: Disproved by Weisenberg (2024); ported as a formal statement. Source: D.
Weisenberg, Sparse Admissible Sets and a Problem of Erdős and Graham, Integers (2024). Moved
from `OpenConjectures/NumberTheory/ErdosProblem429`.
-/
theorem erdos429_refuted : ¬ erdos429 := by
  rintro ⟨f, hf, hA⟩
  obtain ⟨n, hn⟩ := hA (Set.range (termSeq f hf))
    (Set.infinite_range_of_injective termSeq_strictMono.injective)
    (by
      intro N
      have key : ∀ j : ℕ, termSeq f hf j ≤ N → j + 1 ≤ f N := by
        intro j hjN
        exact threshold_spec (le_trans (threshold_le_termSeq j) hjN)
      have hsub : Set.range (termSeq f hf) ∩ Set.Icc 1 N ⊆
          termSeq f hf '' ↑(Finset.range (f N)) := by
        rintro a ⟨⟨j, rfl⟩, -, haN⟩
        refine ⟨j, ?_, rfl⟩
        rw [Finset.mem_coe, Finset.mem_range]
        have := key j haN
        omega
      calc (Set.range (termSeq f hf) ∩ Set.Icc 1 N).ncard
          ≤ (termSeq f hf '' ↑(Finset.range (f N))).ncard :=
            Set.ncard_le_ncard hsub
              (Set.Finite.image _ (Finset.finite_toSet _))
        _ = (↑(Finset.range (f N)) : Set ℕ).ncard :=
            Set.ncard_image_of_injective _ termSeq_strictMono.injective
        _ = f N := by rw [Set.ncard_coe_finset, Finset.card_range])
    (by
      intro p hp
      by_cases hp2 : p = 2
      · subst hp2
        refine ⟨1, ?_⟩
        rintro a ⟨j, rfl⟩ heq
        have h0 : ((termSeq f hf j : ℕ) : ZMod 2) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          exact ⟨2 * (expSeq f hf j) ^ 2, by unfold termSeq; ring⟩
        rw [h0] at heq
        exact zero_ne_one heq
      · have _ : Fact p.Prime := ⟨hp⟩
        obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
          rw [ZMod.ringChar_zmod_n]
          omega)
        refine ⟨b, ?_⟩
        rintro a ⟨j, rfl⟩ heq
        apply hb
        refine ⟨(2 * (expSeq f hf j : ZMod p)), ?_⟩
        rw [← heq]
        have hcast : ((termSeq f hf j : ℕ) : ZMod p) =
            ((2 * (expSeq f hf j : ZMod p))) ^ 2 := by
          unfold termSeq
          push_cast
          ring
        rw [hcast, pow_two])
  obtain ⟨j, hj⟩ := enumIdx_surjective n
  have ha : termSeq f hf j ∈ Set.range (termSeq f hf) := ⟨j, rfl⟩
  have hprime := hn (termSeq f hf j) ha
  rw [← hj] at hprime
  exact not_prime_shift j hprime

end MathlibExt.NumberTheory.ErdosProblem429Wanted

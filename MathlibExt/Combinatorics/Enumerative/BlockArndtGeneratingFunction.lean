/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating function of block Arndt compositions

`MetaMathlibExt.bivariateCountGF_blockArndt` gives the generating function by weight and number
of parts. A composition splits into full decreasing blocks and a possibly empty final block.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bivariate generating function of a two-index count.** For a function $a$ assigning a natural
number $a(n, m)$ to every pair of natural numbers $n, m$, its bivariate generating function is the
power series $\sum_{n \ge 0} \bigl(\sum_{m = 0}^{n} a(n, m)\, y^m\bigr) x^n$ in
$\mathbb{Z}[y][[x]]$, where $x$ marks the first index (the weight) and $y$ the second. Only the
terms with $m \le n$ enter; for counts with $a(n, m) = 0$ whenever $m > n$ it equals
$\sum_{n, m} a(n, m)\, x^n y^m$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2 (the series `A(x, y)`, `Ap(x, y)`,
`Bp(x, y)`, `B(x, y)`, `A_k(x, y)` and `A^{(k)}(x, y)`). -/
noncomputable def bivariateCountGF (a : ℕ → ℕ → ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m

/-- **Coefficients of a bivariate generating function.** For every function $a$ assigning a natural
number $a(n, m)$ to each pair of natural numbers and every $n \ge 0$, the coefficient of $x^n$ in
the bivariate generating function of $a$ is the polynomial
$\sum_{m = 0}^{n} a(n, m)\, y^m \in \mathbb{Z}[y]$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2. -/
theorem coeff_bivariateCountGF (a : ℕ → ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (bivariateCountGF a) =
      ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m := by
  simp [bivariateCountGF]

/-- **Number of $k$-block Arndt compositions.** For $k \ge 1$ and $n, m \ge 0$, $a^{(k)}(n, m)$ is
the number of $k$-block Arndt compositions of $n$ with $m$ parts: sequences
$(c_0, \ldots, c_{m-1})$ of positive integers with $c_0 + \cdots + c_{m-1} = n$ that strictly
decrease inside each block of $k$ consecutive positions $ki, ki + 1, \ldots, ki + k - 1$ (the last
block may be shorter), that is, $c_i > c_{i+1}$ for every $i$ with $i + 1 < m$ and
$i \not\equiv k - 1 \pmod{k}$. For $k = 2$ these are the Arndt compositions.

The definition is meant for $k \ge 1$; its value at $k = 0$ has no combinatorial meaning.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (definition of `k`-block Arndt
compositions). -/
def blockArndtCompositionCount (k n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % k ≠ k - 1 → (j : ℕ) = i + 1 → c j < c i).card

/-- **Four-part 3-block Arndt compositions of 10.** There are exactly $7$ three-block Arndt
compositions of $10$ with $4$ parts, that is, $a^{(3)}(10, 4) = 7$.

They are $(6,2,1,1)$, $(5,3,1,1)$, $(5,2,1,2)$, $(4,3,2,1)$, $(4,3,1,2)$, $(4,2,1,3)$ and
$(3,2,1,4)$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (list of the compositions counted by
`a^{(3)}(10) = 18`). -/
theorem blockArndtCompositionCount_three_ten_four : blockArndtCompositionCount 3 10 4 = 7 := by
  decide

end

namespace bivariateCountGF_blockArndt

noncomputable section

open Finset PowerSeries

private abbrev valid (k : ℕ) {m : ℕ} (c : Fin m → ℕ) :=
  (∀ i, 0 < c i) ∧
    ∀ i j : Fin m, (i : ℕ) % k ≠ k - 1 → (j : ℕ) = i + 1 → c j < c i

private abbrev decreasing {m : ℕ} (c : Fin m → ℕ) :=
  (∀ i, 0 < c i) ∧ StrictAnti c

private lemma valid_short {k m : ℕ} (hm : m ≤ k) (c : Fin m → ℕ) :
    valid k c ↔ decreasing c := by
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h
    cases m with
    | zero => exact fun i ↦ i.elim0
    | succ m =>
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      apply h i.castSucc i.succ _ rfl
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le i.castSucc.isLt hm)]
      simp only [Fin.val_castSucc]
      omega
  · intro h i j _ hij
    exact h (show i < j from Fin.lt_def.mpr (by omega))

private lemma valid_append {k m : ℕ} (a : Fin k → ℕ) (b : Fin m → ℕ) :
    valid k (Fin.append a b) ↔ decreasing a ∧ valid k b := by
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨(valid_short le_rfl a).mp ⟨fun i ↦ by simpa using hp (i.castAdd m), ?_⟩,
      fun i ↦ by simpa using hp (i.natAdd k), ?_⟩
    · intro i j hi hj
      simpa using hd (i.castAdd m) (j.castAdd m) hi hj
    · intro i j hi hj
      simpa using hd (i.natAdd k) (j.natAdd k) (by simpa using hi)
        (by simp [hj, Nat.add_assoc])
  · rintro ⟨⟨ha, hd⟩, hb, ht⟩
    constructor
    · intro i
      exact Fin.addCases (fun i ↦ by simpa using ha i) (fun i ↦ by simpa using hb i) i
    · intro i j
      induction i using Fin.addCases <;> induction j using Fin.addCases
      · rename_i i j
        intro _ hij
        simp only [Fin.val_castAdd] at hij
        simpa using hd (show i < j from Fin.lt_def.mpr (by omega))
      · simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.append_left, Fin.append_right]
        rename_i i j
        rw [Nat.mod_eq_of_lt i.isLt]
        omega
      · simp only [Fin.val_castAdd, Fin.val_natAdd]
        omega
      · simpa [Nat.add_assoc] using ht _ _

private def tuples {m : ℕ} (P : (Fin m → ℕ) → Prop) (n : ℕ) : Finset (Fin m → ℕ) := by
  classical
  exact (Finset.Nat.antidiagonalTuple m n).filter P

private lemma mem_tuples {m n : ℕ} {P : (Fin m → ℕ) → Prop} {c : Fin m → ℕ} :
    c ∈ tuples P n ↔ (∑ i, c i) = n ∧ P c := by
  classical
  simp [tuples, Finset.Nat.mem_antidiagonalTuple]

private def series {m : ℕ} (P : (Fin m → ℕ) → Prop) : PowerSeries ℤ :=
  mk fun n ↦ ((tuples P n).card : ℤ)

-- Splitting at a fixed position gives the Cauchy product of the two weight series.
private lemma series_append {a b : ℕ} (P : (Fin a → ℕ) → Prop) (Q : (Fin b → ℕ) → Prop)
    (R : (Fin (a + b) → ℕ) → Prop) (h : ∀ u v, R (Fin.append u v) ↔ P u ∧ Q v) :
    series R = series P * series Q := by
  classical
  ext n
  simp only [series, coeff_mk, coeff_mul]
  norm_cast
  let pieces := (antidiagonal n).sigma fun p ↦ tuples P p.1 ×ˢ tuples Q p.2
  rw [show (∑ p ∈ antidiagonal n, (tuples P p.1).card * (tuples Q p.2).card) = pieces.card
    by simp [pieces]]
  symm
  apply card_nbij' (fun z ↦ Fin.append z.2.1 z.2.2) (fun c ↦
    ⟨(∑ i, c (Fin.castAdd b i), ∑ j, c (Fin.natAdd a j)),
      (fun i ↦ c (Fin.castAdd b i)), fun j ↦ c (Fin.natAdd a j)⟩)
  · rintro ⟨⟨s, t⟩, u, v⟩ hz
    simp only [pieces, mem_coe, mem_sigma, mem_antidiagonal, mem_product, mem_tuples] at hz
    exact mem_tuples.mpr ⟨by simpa [Fin.sum_univ_add, hz.2.1.1, hz.2.2.1] using hz.1,
      (h u v).mpr ⟨hz.2.1.2, hz.2.2.2⟩⟩
  · intro c hc
    obtain ⟨hs, hr⟩ := mem_tuples.mp hc
    rw [← Fin.append_castAdd_natAdd (f := c)] at hr
    simp [pieces, mem_tuples, ← Fin.sum_univ_add, hs, (h _ _).mp hr]
  · rintro ⟨⟨s, t⟩, u, v⟩ hz
    simp only [pieces, mem_coe, mem_sigma, mem_product, mem_tuples] at hz
    simp [hz.2.1.1, hz.2.2.1]
  · intro c _
    exact Fin.append_castAdd_natAdd

private lemma tuples_eq_empty_of_lt {m n : ℕ} {P : (Fin m → ℕ) → Prop}
    (hp : ∀ c, P c → ∀ i, 0 < c i) (hn : n < m) : tuples P n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hs, hv⟩ := mem_tuples.mp hc
  have := sum_le_sum (s := (univ : Finset (Fin m))) (fun i _ ↦ show 1 ≤ c i from hp c hv i)
  simp [hs] at this
  omega

private abbrev blocks (r : ℕ) := series (@decreasing r)

-- Subtract one from each part. If the last part becomes zero, discard it.
private lemma decreasing_recurrence (r n : ℕ) :
    (tuples (@decreasing (r + 1)) (n + (r + 1))).card =
      (tuples (@decreasing (r + 1)) n).card + (tuples (@decreasing r) n).card := by
  classical
  rw [← card_disjSum]
  symm
  let join : (Fin (r + 1) → ℕ) ⊕ (Fin r → ℕ) → Fin (r + 1) → ℕ :=
    Sum.elim (fun a i ↦ a i + 1) (fun b ↦ Fin.snoc (fun i ↦ b i + 1) 1)
  let split (c : Fin (r + 1) → ℕ) : (Fin (r + 1) → ℕ) ⊕ (Fin r → ℕ) :=
    if c (Fin.last r) = 1 then .inr (fun i ↦ c i.castSucc - 1) else .inl (fun i ↦ c i - 1)
  apply card_nbij' join split
  · rintro (a | b) hz
    · obtain ⟨hs, _, hd⟩ := mem_tuples.mp (inl_mem_disjSum.mp hz)
      exact mem_tuples.mpr ⟨by simp [join, sum_add_distrib, hs], fun _ ↦ Nat.zero_lt_succ _,
        fun {_ _} hij ↦ Nat.succ_lt_succ (hd hij)⟩
    · obtain ⟨hs, hp, hd⟩ := mem_tuples.mp (inr_mem_disjSum.mp hz)
      refine mem_tuples.mpr ⟨by simp [join, Fin.sum_snoc, sum_add_distrib, hs, Nat.add_assoc],
        fun i ↦ Fin.lastCases (by simp [join]) (fun i ↦ by simp [join]) i, ?_⟩
      intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp [join, hp, Fin.le_last, hd.lt_iff_gt]
  · intro c hc
    obtain ⟨hs, hp, hd⟩ := mem_tuples.mp hc
    have add_one (i) : c i - 1 + 1 = c i := Nat.sub_add_cancel (hp i)
    have ht : ∑ i, (c i - 1) = n := by
      have : (∑ i, (c i - 1)) + (r + 1) = ∑ i, c i := by
        simpa [sum_add_distrib] using sum_congr (s₁ := univ) rfl (fun i _ ↦ add_one i)
      omega
    dsimp only [split]
    split_ifs with hlast
    · apply inr_mem_disjSum.mpr
      rw [Fin.sum_univ_castSucc, hlast] at ht
      refine mem_tuples.mpr ⟨by simpa using ht, fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
      · have := hd (Fin.castSucc_lt_last i)
        dsimp only
        omega
      · have := hd (Fin.castSucc_lt_castSucc_iff.mpr hij)
        have := hp j.castSucc
        dsimp only
        omega
    · apply inl_mem_disjSum.mpr
      refine mem_tuples.mpr ⟨ht, fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
      · have := hd.antitone (Fin.le_last i)
        have := hp (Fin.last r)
        dsimp only
        omega
      · have := hd hij
        have := hp j
        dsimp only
        omega
  · rintro (a | b) hz
    · have h := (mem_tuples.mp (inl_mem_disjSum.mp hz)).2.1 (Fin.last r)
      simp [join, split, Nat.ne_of_gt h]
    · simp [join, split]
  · intro c hc
    have hp := (mem_tuples.mp hc).2.1
    funext i
    dsimp only [split]
    split_ifs with hlast
    · induction i using Fin.lastCases <;> simp [join, hlast, Nat.sub_add_cancel (hp _)]
    · exact Nat.sub_add_cancel (hp i)

private lemma blocks_succ (r : ℕ) :
    blocks (r + 1) * (1 - X ^ (r + 1)) = blocks r * X ^ (r + 1) := by
  rw [mul_sub, mul_one]
  ext n
  simp only [map_sub, coeff_mul_X_pow', blocks, series, coeff_mk]
  split_ifs with h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp [Nat.add_comm (r + 1) d, decreasing_recurrence]
  · simp [tuples_eq_empty_of_lt (P := @decreasing (r + 1)) (fun _ hc ↦ hc.1) (Nat.lt_of_not_ge h)]

private abbrev denom (r : ℕ) : PowerSeries ℤ := ∏ i ∈ Ioc 0 r, (1 - X ^ i)

-- Iterating the one-block recurrence gives the triangular exponent.
private lemma blocks_mul_denom (r : ℕ) :
    blocks r * denom r = X ^ (r + 1).choose 2 := by
  induction r with
  | zero =>
    simp only [denom, Ioc_self, prod_empty, mul_one, Nat.choose_eq_zero_of_lt (by decide : 1 < 2),
      pow_zero]
    ext n
    cases n <;> simp [blocks, series, tuples, decreasing, coeff_one, StrictAnti]
  | succ r ih =>
    rw [show denom (r + 1) = denom r * (1 - X ^ (r + 1)) from
      prod_Ioc_succ_top (Nat.zero_le r) _]
    rw [mul_left_comm, blocks_succ, ← mul_assoc, mul_comm (denom r), ih,
      ← pow_add, Nat.choose_succ_succ' (r + 1) 1, Nat.choose_one_right, Nat.add_comm]

private abbrev liftSeries := PowerSeries.map (Polynomial.C : ℤ →+* Polynomial ℤ)

-- Read the coefficient of y^m as a power series in x.
private def slice (m : ℕ) : PowerSeries (Polynomial ℤ) →+ PowerSeries ℤ where
  toFun F := mk fun n ↦ (coeff n F).coeff m
  map_zero' := by ext; simp
  map_add' F G := by ext; simp

private lemma coeff_slice (m n : ℕ) (F : PowerSeries (Polynomial ℤ)) :
    coeff n (slice m F) = (coeff n F).coeff m := by simp [slice]

private lemma slice_mul_lift (m : ℕ) (F : PowerSeries (Polynomial ℤ)) (g : PowerSeries ℤ) :
    slice m (F * liftSeries g) = slice m F * g := by
  ext n
  simp only [coeff_slice, coeff_mul, Polynomial.finsetSum_coeff, liftSeries, coeff_map,
    Polynomial.coeff_mul_C]

private abbrev mark (j : ℕ) : PowerSeries (Polynomial ℤ) := C (Polynomial.X ^ j)

private lemma slice_mark (m j : ℕ) : slice m (mark j) = if m = j then 1 else 0 := by
  ext n
  by_cases h : m = j <;> by_cases hn : n = 0 <;>
    simp only [coeff_slice, mark, coeff_C, coeff_one, h, hn, map_zero,
      Polynomial.coeff_zero, Polynomial.coeff_X_pow, eq_self, ↓reduceIte]

private lemma slice_mul_mark (m j : ℕ) (F : PowerSeries (Polynomial ℤ)) :
    slice m (F * mark j) = if j ≤ m then slice (m - j) F else 0 := by
  ext n
  by_cases h : j ≤ m <;> simp only [coeff_slice, mark, coeff_mul_C, Polynomial.coeff_mul_X_pow',
    h, ↓reduceIte, map_zero]

private lemma slice_count (m k : ℕ) :
    slice m (bivariateCountGF (blockArndtCompositionCount k)) = series (@valid k m) := by
  classical
  ext n
  rw [coeff_slice, coeff_bivariateCountGF, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_natCast_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_range, series, coeff_mk]
  split_ifs with h
  · unfold blockArndtCompositionCount tuples
    congr 2
    ext c
    simp [valid]
  · rw [tuples_eq_empty_of_lt (P := @valid k m) (fun _ hc ↦ hc.1) (by omega)]
    simp

private abbrev tailDenom (j k : ℕ) : PowerSeries ℤ := ∏ i ∈ Ioc j k, (1 - X ^ i)

private lemma slice_numerator (m k : ℕ) :
    slice m (∑ j ∈ range k, mark j * liftSeries (X ^ (j + 1).choose 2 * tailDenom j k)) =
      if m < k then X ^ (m + 1).choose 2 * tailDenom m k else 0 := by
  simp only [map_sum, slice_mul_lift, slice_mark, ite_mul, one_mul, zero_mul, sum_ite_eq,
    mem_range]

private lemma identity (k : ℕ) :
    bivariateCountGF (blockArndtCompositionCount k) *
        (liftSeries (denom k) - mark k * liftSeries (X ^ (k + 1).choose 2)) =
      ∑ j ∈ range k, mark j * liftSeries (X ^ (j + 1).choose 2 * tailDenom j k) := by
  apply PowerSeries.ext
  intro n
  apply AddMonoidAlgebra.ext
  ext m
  rw [← coeff_slice, ← coeff_slice]
  congr 1
  rw [mul_sub, ← mul_assoc _ (mark k), map_sub, slice_mul_lift, slice_mul_lift, slice_mul_mark,
    slice_count, slice_numerator]
  -- Short compositions contribute to the numerator. Longer ones start with a full block.
  by_cases hm : m < k
  · rw [ite_eq_left hm, ite_eq_right (Nat.not_le_of_lt hm), zero_mul, sub_zero]
    have hs : @valid k m = @decreasing m := funext fun c ↦ propext (valid_short hm.le c)
    rw [hs, show denom k = denom m * tailDenom m k from
      (prod_Ioc_consecutive _ (Nat.zero_le _) hm.le).symm, ← mul_assoc, blocks_mul_denom]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hm)
    rw [ite_eq_right hm, ite_eq_left (Nat.le_add_right k d), Nat.add_sub_cancel_left, slice_count]
    rw [series_append (@decreasing k) (@valid k d) (@valid k (k + d)) valid_append]
    rw [mul_right_comm, blocks_mul_denom, mul_comm, sub_self]

end

end bivariateCountGF_blockArndt

open bivariateCountGF_blockArndt in
/-- **Generating function of block Arndt compositions.** Let $k \ge 1$, let $a^{(k)}(n, m)$ be
the number of $k$-block Arndt compositions of $n$ with $m$ parts, and let
$A^{(k)}(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a^{(k)}(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$.
Then
$A^{(k)}(x, y) \bigl(\prod_{\ell=1}^{k} (1 - x^\ell) - x^{\binom{k+1}{2}} y^k\bigr) =
\sum_{j=0}^{k-1} x^{\binom{j+1}{2}} y^j \prod_{\ell=j+1}^{k} (1 - x^\ell)$.
Equivalently, with $J_j(x, y) = x^{\binom{j+1}{2}} y^j \prod_{\ell=1}^{j} (1 - x^\ell)^{-1}$,
$A^{(k)}(x, y) = \bigl(\sum_{j=0}^{k-1} J_j(x, y)\bigr) / (1 - J_k(x, y))$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 12 (`integers-2024-A35-thm-12`). -/
public theorem bivariateCountGF_blockArndt (k : ℕ) (hk : 1 ≤ k) :
    bivariateCountGF (blockArndtCompositionCount k) *
        ((∏ ℓ ∈ Finset.Icc 1 k, (1 - PowerSeries.X ^ ℓ)) -
          PowerSeries.C (Polynomial.X ^ k) * PowerSeries.X ^ Nat.choose (k + 1) 2) =
      ∑ j ∈ Finset.range k,
        PowerSeries.C (Polynomial.X ^ j) * PowerSeries.X ^ Nat.choose (j + 1) 2 *
          ∏ ℓ ∈ Finset.Ioc j k, (1 - PowerSeries.X ^ ℓ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have interval : Finset.Icc 1 (r + 1) = Finset.Ioc 0 (r + 1) :=
    Finset.Icc_succ_left_eq_Ioc 0 _
  simpa only [liftSeries, denom, tailDenom, mark, map_prod, map_sub, map_one, map_pow,
    map_mul, PowerSeries.map_X, interval, mul_assoc] using identity (r + 1)

end MetaMathlibExt

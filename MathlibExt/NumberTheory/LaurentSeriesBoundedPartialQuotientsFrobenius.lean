/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotients

/-!
# Frobenius and continued fractions of formal Laurent series

Taking the field-cardinality power commutes with taking the polynomial part and with the
recurrences for complete quotients and convergents.
-/

namespace MetaMathlibExt

variable {K : Type*} [Field K]

private theorem support_pow_subset_of_add_mem {s : Set ℤ}
    (hs : ∀ i j, i ∈ s → j ∈ s → i + j ∈ s)
    {a : LaurentSeries K} (ha : a.support ⊆ s) {m : ℕ} (hm : m ≠ 0) :
    (a ^ m).support ⊆ s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  clear hm
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      rw [pow_succ]
      intro j hj
      obtain ⟨i, hi, k, hk, rfl⟩ := HahnSeries.support_mul_subset hj
      exact hs i k (ih hi) (ha hk)

private theorem laurentPolyPart_pow_card [Fintype K] (α : LaurentSeries K) :
    laurentPolyPart (α ^ Fintype.card K) = laurentPolyPart α ^ Fintype.card K := by
  let q := Fintype.card K
  let p := laurentPolyPart α
  let t := α - p
  have hq : q ≠ 0 := Fintype.card_ne_zero
  have hp : p.support ⊆ {i | i ≤ 0} := by
    intro i hi
    by_contra h
    exact hi (by simp [p, laurentPolyPart_coeff, show ¬ i ≤ 0 from h])
  have ht : t.support ⊆ {i | 0 < i} := by
    intro i hi
    by_contra h
    have h' : i ≤ 0 := le_of_not_gt h
    exact hi (by simp [t, p, HahnSeries.coeff_sub, laurentPolyPart_coeff, h'])
  -- Frobenius is additive, and the two summands stay on their respective sides of 0.
  have hpq : (p ^ q).support ⊆ {i | i ≤ 0} :=
    support_pow_subset_of_add_mem
      (fun i j hi hj => show i + j ≤ 0 from add_nonpos hi hj) hp hq
  have htq : (t ^ q).support ⊆ {i | 0 < i} :=
    support_pow_subset_of_add_mem
      (fun i j hi hj => show 0 < i + j from add_pos hi hj) ht hq
  have hα : p + t = α := by
    rw [add_comm, sub_add_cancel]
  have hpow : α ^ q = p ^ q + t ^ q :=
    hα ▸ map_add (FiniteField.frobeniusAlgHom K (LaurentSeries K)) p t
  change laurentPolyPart (α ^ q) = p ^ q
  rw [hpow]
  ext i
  by_cases hi : i ≤ 0
  · have hti : (t ^ q).coeff i = 0 := by
      by_contra h
      exact (not_lt_of_ge hi) (htq h)
    simp [laurentPolyPart_coeff, hi, HahnSeries.coeff_add, hti]
  · have hpi : (p ^ q).coeff i = 0 := by
      by_contra h
      exact hi (hpq h)
    simp [laurentPolyPart_coeff, hi, hpi]

/-- **Frobenius acts on continued fractions of Laurent series.** Let $K$ be a finite field with
$q$ elements and let $\alpha \in K((x^{-1}))$, with partial quotients $b_0, b_1, \dots$ and
convergent numerators and denominators $P_n, Q_n$, where $P_{-1} = 1$ and $Q_{-1} = 0$. Then for
every $n \ge 0$ the $n$-th partial quotient of $\alpha^q$ is $b_n^q$, and for every $n \ge -1$
the convergent numerator and denominator of $\alpha^q$ of index $n$ are $P_n^q$ and $Q_n^q$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 2 (`integers-2026-A57-lem-2`). -/
public theorem laurentPartialQuotient_pow_card [Fintype K] (α : LaurentSeries K) (n : ℕ) :
    laurentPartialQuotient (α ^ Fintype.card K) n =
        laurentPartialQuotient α n ^ Fintype.card K ∧
      laurentConvNum (α ^ Fintype.card K) n = laurentConvNum α n ^ Fintype.card K ∧
      laurentConvDen (α ^ Fintype.card K) n = laurentConvDen α n ^ Fintype.card K := by
  let F := FiniteField.frobeniusAlgHom K (LaurentSeries K)
  have hpoly (a : LaurentSeries K) : laurentPolyPart (F a) = F (laurentPolyPart a) :=
    laurentPolyPart_pow_card a
  have hcomplete (k : ℕ) : laurentCompleteQuotient (F α) k = F (laurentCompleteQuotient α k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [laurentCompleteQuotient, ih, hpoly, map_inv₀, map_sub]
  have hpartial (k : ℕ) : laurentPartialQuotient (F α) k = F (laurentPartialQuotient α k) := by
    simp only [laurentPartialQuotient, hcomplete, hpoly]
  have hconv (k : ℕ) : laurentConvNum (F α) k = F (laurentConvNum α k) ∧
      laurentConvDen (F α) k = F (laurentConvDen α k) := by
    induction k using Nat.twoStepInduction with
    | zero => simp [laurentConvNum, laurentConvDen]
    | one => exact ⟨hpartial 0, (map_one F).symm⟩
    | more k ih ih' =>
        obtain ⟨hn, hd⟩ := ih
        obtain ⟨hn', hd'⟩ := ih'
        simp only [laurentConvNum, laurentConvDen, hpartial, hn, hd, hn', hd', map_add, map_mul,
          and_self]
  exact ⟨hpartial n, hconv n⟩

end MetaMathlibExt

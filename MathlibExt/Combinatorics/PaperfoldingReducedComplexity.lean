/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.Data.List.Iterate

/-!
# Reduced complexities of the paperfolding word

`rhoRed_paperfolding_two_mul` shows that every positive even length has four distinct reductions
of paperfolding factors. Letters at consecutive even positions differ, so each such pair
contributes one change of letter regardless of the intervening letter.
`rhoAbRed_paperfolding_even` shows that at every positive even length exactly three reductions
remain when counted up to rearrangement. At lengths greater than one and congruent to one
modulo four, `rhoAbRed_paperfolding_mod_four_one` counts four: one for each neighboring even
run count and two for the intervening odd run count.

## References

* John M. Campbell, James D. Currie, and Narad Rampersad,
  [Reduced Complexities for Sequences Over Finite Alphabets](https://math.colgate.edu/~integers/aa34/aa34.pdf),
  INTEGERS 26 (2026), Article A34, pp. 1–15, Lemmas 4–6 and 8 and Theorem 3
  (even and length-one-modulo-four cases). The proof here uses the run analysis and
  constructs the two extreme run counts by repeatedly halving an even shift.
* The odd-length proof reuses `rhoRed_paperfolding_two_mul.red_factor_even_start`,
  `rhoRed_paperfolding_two_mul.red_even_length_even_start`, and
  `rhoRed_paperfolding_two_mul.red_factor_succ` from this module.
* The proof of `rhoAbRed_paperfolding_even` reuses `rhoRed_paperfolding_two_mul.reduced_range`
  from this module, `MathlibExt.Combinatorics.PaperfoldingReducedComplexity`.
-/

namespace MathlibExt.Combinatorics.ReducedComplexitiesWanted

open InfiniteWord

-- The middle letter agrees with one of its neighbors.
private theorem redWord_skip_middle (a b c : Bool) (w : List Bool) (h : c = !a) :
    redWord (a :: b :: c :: w) = a :: redWord (c :: w) := by
  subst c
  cases a <;> cases b <;> simp [redWord]

/-- **Runs in a word whose even-position letters alternate.** Let $n$ be a natural number and let
$w = w_0 w_1 \cdots w_{2n}$ be a binary word of length $2n + 1$ with $w_{2i} \ne w_{2i+2}$ for
every $i < n$, so that its even positions read $abab\cdots$ with $a \ne b$ and its odd positions
are arbitrary. Then the reduction of $w$, the word obtained by collapsing each maximal run of
equal letters of $w$ to a single letter, has length $n + 1$; that is, $w$ has exactly $n + 1$ runs.

The paper applies this to factors of the paperfolding word.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 4. -/
public theorem redWord_length_alternating_even (n : ℕ)
    (w : Fin (2 * n + 1) → Bool)
    (h : ∀ i : Fin n,
      w ⟨2 * i.val, by omega⟩ ≠ w ⟨2 * (i.val + 1), by omega⟩) :
    (redWord (List.ofFn w)).length = n + 1 := by
  induction n with
  | zero => simp only [List.ofFn_succ, List.ofFn_zero, redWord, List.length_cons, List.length_nil]
  | succ n ih =>
    let v : Fin (2 * n + 1) → Bool := fun i => w i.succ.succ
    have hv : ∀ i : Fin n,
        v ⟨2 * i.val, by omega⟩ ≠ v ⟨2 * (i.val + 1), by omega⟩ :=
      fun i => h i.succ
    have hfirst : v 0 = !(w 0) := Bool.eq_not_of_ne (h 0).symm
    rw [List.ofFn_succ, List.ofFn_succ]
    change (redWord (w 0 :: w (Fin.succ 0) :: List.ofFn v)).length = _
    rw [List.ofFn_succ (f := v), redWord_skip_middle _ _ _ _ hfirst, ← List.ofFn_succ (f := v),
      List.length_cons, ih v hv]

namespace rhoRed_paperfolding_two_mul

private theorem paperfoldingSeq_even_add (j m : ℕ) (hm : m % 2 = 1) :
    paperfoldingSeq (2 * (j + m)) = !paperfoldingSeq (2 * j) := by
  rw [paperfoldingSeq_even, paperfoldingSeq_even, ← decide_not, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  omega

private theorem factorList_succ (n i : ℕ) :
    factorList paperfoldingSeq (n + 1) i =
      paperfoldingSeq i :: factorList paperfoldingSeq n (i + 1) := by
  simp only [factorList, List.ofFn_succ, factor_apply, Fin.val_zero, Nat.add_zero]
  congr 2
  funext s
  change paperfoldingSeq (i + (s.val + 1)) = paperfoldingSeq (i + 1 + s.val)
  rw [Nat.add_right_comm, Nat.add_assoc]

private theorem redWord_cons_iterate (a b : Bool) (w : List Bool) (k : ℕ)
    (h : redWord (b :: w) = List.iterate Bool.not b k) :
    redWord (a :: b :: w) =
      List.iterate Bool.not a (k + (decide (a ≠ b)).toNat) := by
  cases a <;> cases b <;> simp [redWord, h]

private theorem red_factor_one (i : ℕ) :
    redWord (factorList paperfoldingSeq 1 i) = List.iterate Bool.not (paperfoldingSeq i) 1 := by
  simp [factorList, redWord]

private theorem red_factor_succ (k i a : ℕ)
    (h : redWord (factorList paperfoldingSeq (k + 1) (i + 1)) =
      List.iterate Bool.not (paperfoldingSeq (i + 1)) a) :
    redWord (factorList paperfoldingSeq (k + 1 + 1) i) =
      List.iterate Bool.not (paperfoldingSeq i)
        (a + (decide (paperfoldingSeq i ≠ paperfoldingSeq (i + 1))).toNat) := by
  simp only [factorList_succ] at h ⊢
  exact redWord_cons_iterate _ _ _ _ h

-- Adding k aligned pairs before a nonempty suffix adds k letters to the reduction.
private theorem red_factor_even_start (k j r a : ℕ)
    (h : redWord (factorList paperfoldingSeq (r + 1) (2 * (j + k))) =
      List.iterate Bool.not (paperfoldingSeq (2 * (j + k))) a) :
    redWord (factorList paperfoldingSeq (2 * k + r + 1) (2 * j)) =
      List.iterate Bool.not (paperfoldingSeq (2 * j)) (a + k) := by
  induction k generalizing j with
  | zero => simpa using h
  | succ k ih =>
    have htail := ih (j + 1) (by simpa only [show j + 1 + k = j + (k + 1) by omega] using h)
    rw [show 2 * (k + 1) + r + 1 = 2 * k + r + 1 + 1 + 1 by omega,
      factorList_succ, factorList_succ, show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
      factorList_succ, redWord_skip_middle _ _ _ _ (paperfoldingSeq_even_add j 1 rfl),
      ← factorList_succ, htail]
    simp [paperfoldingSeq_even_add j 1 rfl]

private def reducedWord (k : ℕ) (p : Bool × Bool) : List Bool :=
  List.iterate Bool.not p.1 (k + p.2.toNat + 1)

private theorem reducedWord_injective (k : ℕ) : Function.Injective (reducedWord k) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hfirst : a = c := by simpa [reducedWord] using congrArg List.head? h
  have hlast : b = d := by
    have hlen := congrArg List.length h
    cases b <;> cases d <;> simp [reducedWord, List.length_iterate] at hlen ⊢
  exact Prod.ext hfirst hlast

private def firstLetterAndChange (i : ℕ) : Bool × Bool :=
  (paperfoldingSeq i, decide (paperfoldingSeq i ≠ paperfoldingSeq (i + 1)))

private theorem red_even_length_even_start (k j : ℕ) :
    redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j)) =
      reducedWord k (paperfoldingSeq (2 * j), (firstLetterAndChange (2 * (j + k))).2) := by
  have htail := red_factor_succ 0 (2 * (j + k)) 1 (red_factor_one _)
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, red_factor_even_start k j 1 _ htail]
  simp only [reducedWord, firstLetterAndChange]
  congr 1
  omega

private theorem red_even_length_odd_start (k j : ℕ) :
    redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j + 1)) =
      reducedWord k (firstLetterAndChange (2 * j + 1)) := by
  have htail := red_factor_even_start k (j + 1) 0 1 (red_factor_one _)
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, Nat.add_zero] at htail
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, red_factor_succ _ _ _ htail]
  simp only [reducedWord, firstLetterAndChange]
  congr 1
  omega

-- Both values of the first letter and both possibilities for the first change occur.
private theorem firstLetterAndChange_odd_surjective :
    Function.Surjective (fun j => firstLetterAndChange (2 * j + 1)) := by
  rintro ⟨a, b⟩
  cases a <;> cases b
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨5, by decide +kernel⟩

private theorem reduced_range (k : ℕ) :
    Set.range (fun i => redWord (factorList paperfoldingSeq (2 * (k + 1)) i)) =
      Set.range (reducedWord k) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    change redWord (factorList paperfoldingSeq (2 * (k + 1)) i) ∈ _
    obtain ⟨j, rfl | rfl⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
    · rw [red_even_length_even_start]
      exact Set.mem_range_self _
    · rw [red_even_length_odd_start]
      exact Set.mem_range_self _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨j, hj⟩ := firstLetterAndChange_odd_surjective p
    refine ⟨2 * j + 1, ?_⟩
    change firstLetterAndChange (2 * j + 1) = p at hj
    change redWord (factorList paperfoldingSeq (2 * (k + 1)) (2 * j + 1)) = _
    rw [red_even_length_odd_start, hj]

end rhoRed_paperfolding_two_mul

/-- **Reduced complexity of the paperfolding word at even lengths.** Let $f$ be the regular
paperfolding sequence and let $\rho^{\mathrm{red}}_f(n)$ be the number of distinct reductions of
length-$n$ factors of $f$. For every $n \ge 1$, $\rho^{\mathrm{red}}_f(2n) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Lemma 5. -/
public theorem rhoRed_paperfolding_two_mul (n : ℕ) (hn : 1 ≤ n) :
    rhoRed paperfoldingSeq (2 * n) = 4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [rhoRed, factorSet, ← Set.range_comp]
  change (Set.range (fun i => redWord (factorList paperfoldingSeq (2 * (k + 1)) i))).ncard = 4
  rw [rhoRed_paperfolding_two_mul.reduced_range,
    Set.ncard_range_of_injective (rhoRed_paperfolding_two_mul.reducedWord_injective k)]
  simp [Nat.card_eq_fintype_card]

private theorem count_false_iterate_not_even (m : ℕ) (a : Bool) :
    (List.iterate Bool.not a (2 * m)).count false = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ]
    cases a <;> simp [ih]

private def signature (w : List Bool) : ℕ × ℕ := (w.length, w.count false)

private theorem signature_even (r : ℕ) (a : Bool) :
    signature (List.iterate Bool.not a (2 * r)) = (2 * r, r) := by
  simp [signature, count_false_iterate_not_even]

private theorem signature_odd (r : ℕ) (a : Bool) :
    signature (List.iterate Bool.not a (2 * r + 1)) = (2 * r + 1, r + (!a).toNat) := by
  cases a <;> simp [signature, count_false_iterate_not_even]

/-- **Reduced abelian complexity of the paperfolding word at even lengths.** Let $f$ be the
regular paperfolding sequence and let $\rho^{\mathrm{ab,red}}_f(n)$ be the number of reductions
of length-$n$ factors of $f$, counted up to rearrangement of their letters. For every even
$n > 0$, $\rho^{\mathrm{ab,red}}_f(n) = 3$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
public theorem rhoAbRed_paperfolding_even (n : ℕ) (hn : 0 < n)
    (he : Even n) :
    rhoAbRed paperfoldingSeq n = 3 := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp he
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [rhoAbRed_eq_ncard_range]
  change (Set.range (signature ∘ fun i =>
    redWord (factorList paperfoldingSeq (2 * (k + 1)) i))).ncard = 3
  rw [Set.range_comp, rhoRed_paperfolding_two_mul.reduced_range, ← Set.range_comp]
  have mem_signatures (p : ℕ × ℕ) :
      p ∈ Set.range (signature ∘ rhoRed_paperfolding_two_mul.reducedWord k) ↔
        p = signature (List.iterate Bool.not false (k + 1)) ∨
        p = signature (List.iterate Bool.not true (k + 1)) ∨
        p = signature (List.iterate Bool.not false (k + 1 + 1)) ∨
        p = signature (List.iterate Bool.not true (k + 1 + 1)) := by
    simp only [Set.mem_range, Prod.exists, Bool.exists_bool, Function.comp_apply,
      rhoRed_paperfolding_two_mul.reducedWord, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
    tauto
  -- Consecutive run lengths contribute one and two signatures, in either order.
  rw [Set.ncard_eq_three]
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' (k + 1)
  · refine ⟨(2 * r, r), (2 * r + 1, r + 1), (2 * r + 1, r), ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · ext p
      rw [mem_signatures, hr]
      simp only [signature_even, signature_odd, Bool.not_false, Bool.not_true, Bool.toNat_true,
        Bool.toNat_false, Nat.add_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  · refine ⟨(2 * r + 1, r + 1), (2 * r + 1, r), (2 * (r + 1), r + 1), ?_, ?_, ?_, ?_⟩
    · simp
    · simp; omega
    · simp
    · ext p
      rw [mem_signatures, hr, show 2 * r + 1 + 1 = 2 * (r + 1) by omega]
      simp only [signature_even, signature_odd, Bool.not_false, Bool.not_true, Bool.toNat_true,
        Bool.toNat_false, Nat.add_zero, Set.mem_insert_iff, Set.mem_singleton_iff, or_self]

private theorem paperfoldingSeq_opposite_at_even_shift (m : ℕ) (hm : 0 < m) (a : Bool) :
    ∃ j, paperfoldingSeq j = a ∧ paperfoldingSeq (j + 2 * m) = !a := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases h : m % 2 = 1
    · use 2 * a.toNat
      rw [← Nat.mul_add, rhoRed_paperfolding_two_mul.paperfoldingSeq_even_add _ _ h,
        paperfoldingSeq_even]
      cases a <;> decide
    · obtain ⟨j, hj, hj'⟩ := ih (m / 2) (by omega) (by omega)
      refine ⟨2 * j + 1, (paperfoldingSeq_odd j).trans hj, ?_⟩
      rwa [show 2 * j + 1 + 2 * m = 2 * (j + 2 * (m / 2)) + 1 by omega, paperfoldingSeq_odd]

-- To make both boundaries change, take `b = true`; to make neither change, take `b = false`.
private theorem paperfoldingSeq_odd_factor_boundaries (m : ℕ) (hm : 0 < m) (b : Bool) :
    ∃ j, paperfoldingSeq j = (if b then paperfoldingSeq (2 * j) else !paperfoldingSeq (2 * j)) ∧
      paperfoldingSeq (j + 2 * m) = !paperfoldingSeq j := by
  by_cases h : m % 2 = 1
  · use 2 * (!b).toNat
    constructor
    · cases b <;> decide +kernel
    · rw [← Nat.mul_add, rhoRed_paperfolding_two_mul.paperfoldingSeq_even_add _ _ h]
  · obtain ⟨r, hr, hr'⟩ := paperfoldingSeq_opposite_at_even_shift (m / 2) (by omega) b
    refine ⟨2 * r + 1, ?_, ?_⟩
    · rw [paperfoldingSeq_odd, hr, paperfoldingSeq_even]
      simp [show (2 * r + 1) % 2 = 1 by omega]
    · rwa [show 2 * r + 1 + 2 * m = 2 * (r + 2 * (m / 2)) + 1 by omega,
        paperfoldingSeq_odd, paperfoldingSeq_odd, hr]

open rhoRed_paperfolding_two_mul in
private theorem red_odd_length_odd_start (m j : ℕ) (hm : 0 < m) :
    redWord (factorList paperfoldingSeq (4 * m + 1) (2 * j + 1)) =
      List.iterate Bool.not (paperfoldingSeq j)
        (2 * m + (decide (paperfoldingSeq (2 * j) ≠ paperfoldingSeq (j + 2 * m))).toNat +
          (decide (paperfoldingSeq j ≠ !paperfoldingSeq (2 * j))).toNat) := by
  let k := 2 * m - 1
  have hk : k + 1 = 2 * m := by dsimp [k]; omega
  -- The inner block has `2 * m` runs. Its even-indexed endpoints have opposite letters.
  have hlast : paperfoldingSeq (2 * (j + 1 + k)) = paperfoldingSeq (2 * j) := by
    have hp : (j + 1 + k) % 2 = j % 2 := by omega
    simp only [paperfoldingSeq_even, hp]
  let right := (decide (paperfoldingSeq (2 * j) ≠ paperfoldingSeq (j + 2 * m))).toNat
  have htail : redWord (factorList paperfoldingSeq (2 * k + 1 + 1) (2 * j + 1 + 1)) =
      List.iterate Bool.not (paperfoldingSeq (2 * j + 1 + 1)) (k + right + 1) := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      show 2 * j + 1 + 1 = 2 * (j + 1) by omega, red_even_length_even_start]
    simp only [reducedWord, firstLetterAndChange, hlast, right,
      show 2 * (j + 1 + k) + 1 = 2 * (j + 2 * m) + 1 by omega, paperfoldingSeq_odd]
  have hred := red_factor_succ (2 * k + 1) (2 * j + 1) _ htail
  rwa [show 2 * k + 1 + 1 + 1 = 4 * m + 1 by omega,
    show 2 * j + 1 + 1 = 2 * (j + 1) by omega, paperfoldingSeq_even_add j 1 rfl,
    paperfoldingSeq_odd, show k + right + 1 = 2 * m + right by omega] at hred

private theorem signatures_mod_four_one (m : ℕ) (hm : 0 < m) :
    (Set.range fun i => signature (redWord (factorList paperfoldingSeq (4 * m + 1) i))) =
      {(2 * m, m), (2 * m + 1, m), (2 * m + 1, m + 1), (2 * (m + 1), m + 1)} := by
  have heven (j : ℕ) : redWord (factorList paperfoldingSeq (4 * m + 1) (2 * j)) =
      List.iterate Bool.not (paperfoldingSeq (2 * j)) (2 * m + 1) := by
    simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm 1 (2 * m),
      show 2 * (2 * m) = 4 * m by omega] using
      rhoRed_paperfolding_two_mul.red_factor_even_start (2 * m) j 0 1
        (rhoRed_paperfolding_two_mul.red_factor_one _)
  have hlong : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  have hextreme (b : Bool) : ∃ i, signature (redWord (factorList paperfoldingSeq (4 * m + 1) i)) =
      (2 * (m + b.toNat), m + b.toNat) := by
    obtain ⟨j, hj, hj'⟩ := paperfoldingSeq_odd_factor_boundaries m hm b
    use 2 * j + 1
    rw [red_odd_length_odd_start m j hm, hj', hj]
    cases b <;> simp [signature_even, hlong]
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl | rfl⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
    · rw [heven, signature_odd]
      cases paperfoldingSeq (2 * j) <;> simp
    · rw [red_odd_length_odd_start m j hm]
      generalize (decide (paperfoldingSeq (2 * j) ≠ paperfoldingSeq (j + 2 * m))) = a
      generalize (decide (paperfoldingSeq j ≠ !paperfoldingSeq (2 * j))) = b
      cases a <;> cases b <;> cases paperfoldingSeq j <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero, hlong, signature_even,
          signature_odd, Bool.not_true, Bool.not_false] <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · simpa using hextreme false
    · exact ⟨2, by rw [show (2 : ℕ) = 2 * 1 by decide, heven, signature_odd,
        paperfoldingSeq_even]; simp⟩
    · exact ⟨0, by rw [show (0 : ℕ) = 2 * 0 by decide, heven, signature_odd,
        paperfoldingSeq_even]; simp⟩
    · simpa using hextreme true

/-- **Reduced abelian complexity of the paperfolding word at lengths 1 mod 4.** Let $f$ be the
regular paperfolding sequence and let $\rho^{\mathrm{ab,red}}_f(n)$ be the number of reductions
of length-$n$ factors of $f$, counted up to rearrangement of their letters. For every $n > 1$
with $n \equiv 1 \pmod 4$, $\rho^{\mathrm{ab,red}}_f(n) = 4$.

Source: John M. Campbell, James D. Currie, and Narad
Rampersad, "Reduced Complexities for Sequences Over Finite
Alphabets", Theorem 3. -/
public theorem rhoAbRed_paperfolding_mod_four_one (n : ℕ)
    (hn : 1 < n) (h : n % 4 = 1) :
    rhoAbRed paperfoldingSeq n = 4 := by
  let m := n / 4
  have hm : 0 < m := by dsimp [m]; omega
  rw [show n = 4 * m + 1 by dsimp [m]; omega, rhoAbRed_eq_ncard_range]
  change (Set.range (fun i =>
    signature (redWord (factorList paperfoldingSeq (4 * m + 1) i)))).ncard = 4
  rw [signatures_mod_four_one m hm, Set.ncard_eq_four]
  refine ⟨(2 * m, m), (2 * m + 1, m), (2 * m + 1, m + 1), (2 * (m + 1), m + 1),
    ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals simp only [ne_eq, Prod.mk.injEq]
  all_goals omega

end MathlibExt.Combinatorics.ReducedComplexitiesWanted

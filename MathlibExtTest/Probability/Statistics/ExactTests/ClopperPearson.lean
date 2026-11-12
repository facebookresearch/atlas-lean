/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.ClopperPearson
public import MathlibExt.Probability.Statistics.ConfidenceSet

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathlibExt.Probability.Statistics.ExactTests
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.ExactTests.ClopperPearson

/-! ### `n = 0`: the only observation is `x = 0`, and the interval is `[0, 1]` -/

/-- `n = 0`, `x = 0`: `L = 0` and `U = 1`. -/
example {α : ℝ} (hα : α ≤ 2) :
    clopperPearsonLower 0 0 α = 0 ∧ clopperPearsonUpper 0 0 α = 1 :=
  ⟨clopperPearsonLower_zero 0 hα, clopperPearsonUpper_self 0 hα⟩

/-- `n = 0`: the upper-endpoint tail `P_p(X ≥ 1)` is an empty sum, so `P_p(X ≤ 0) = 1`
computed from Mathlib's `Bin(0, p) = δ₀`. -/
example (p : unitInterval) : (binomial 0 p).real (Iic 0) = 1 := by
  rw [binomial_zero]
  simp

/-! ### `n = 1`: `L(1) = α / 2` and `U(0) = 1 - α / 2` -/

/-- `n = 1`, `x = 1`: `P_p(X ≥ 1) = p`, so `L(1) = α / 2`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : clopperPearsonLower 1 1 α = α / 2 := by
  refine clopperPearsonLower_eq_of_binomTail_eq le_rfl le_rfl ⟨by linarith, by linarith⟩ ?_
  simp [binomTail]

/-- `n = 1`, `x = 0`: `P_p(X ≤ 0) = 1 - p`, so `U(0) = 1 - α / 2`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : clopperPearsonUpper 1 0 α = 1 - α / 2 := by
  refine clopperPearsonUpper_eq_of_binomTail_eq Nat.zero_lt_one ⟨by linarith, by linarith⟩ ?_
  simp [binomTail]

/-- `n = 1`: the boundary endpoints `L(0) = 0` and `U(1) = 1`. -/
example {α : ℝ} (hα1 : α < 1) :
    clopperPearsonLower 1 0 α = 0 ∧ clopperPearsonUpper 1 1 α = 1 :=
  ⟨clopperPearsonLower_zero 1 (by linarith), clopperPearsonUpper_self 1 (by linarith)⟩

/-! ### `n = 3`, `α = 1 / 4` (each tail gets `1 / 8`) -/

/-- `n = 3`, `x = 3`: `P_{1/2}(X ≥ 3) = (1/2)³ = 1/8`, so `L(3) = 1 / 2`. -/
example : clopperPearsonLower 3 3 (1 / 4) = 1 / 2 := by
  refine clopperPearsonLower_eq_of_binomTail_eq (by norm_num) le_rfl ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail]

/-- `n = 3`, `x = 0`: `P_{1/2}(X ≤ 0) = (1/2)³ = 1/8`, computed as `1 - P_{1/2}(X ≥ 1)` with
`P_{1/2}(X ≥ 1) = 3/8 + 3/8 + 1/8`, so `U(0) = 1 / 2`. -/
example : clopperPearsonUpper 3 0 (1 / 4) = 1 / 2 := by
  refine clopperPearsonUpper_eq_of_binomTail_eq (by norm_num) ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- The same tail from Mathlib's binomial masses: `Bin(3, 1/2)({3}) = 1/8`, and this is the
whole upper tail `Bin(3, 1/2)([3, ∞))` at the lower endpoint `L(3) = 1/2`. -/
example : (binomial 3 ⟨1 / 2, by norm_num, by norm_num⟩).real {3} = 1 / 8 ∧
    upperTail (binomial 3 ⟨1 / 2, by norm_num, by norm_num⟩) 3 = 1 / 8 := by
  refine ⟨?_, ?_⟩
  · rw [binomial_real_singleton]
    norm_num
  · rw [upperTail_binomial]
    norm_num [binomTail]

/-- An interior endpoint: `n = 3`, `x = 1`, `α = 122/125`. `P_{1/5}(X ≥ 1) = 1 - (4/5)³ =
61/125 = α / 2`, so `L(1) = 1 / 5`. -/
example : clopperPearsonLower 3 1 (122 / 125) = 1 / 5 := by
  refine clopperPearsonLower_eq_of_binomTail_eq le_rfl (by norm_num) ⟨by norm_num, by norm_num⟩ ?_
  norm_num [binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- `n = 3`, `x = 1` gives a proper interior interval `0 < L(1) ≤ U(1) < 1`. -/
example {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < clopperPearsonLower 3 1 α ∧ clopperPearsonLower 3 1 α ≤ clopperPearsonUpper 3 1 α ∧
      clopperPearsonUpper 3 1 α < 1 :=
  ⟨(clopperPearsonLower_mem_Ioo le_rfl (by norm_num) hα0 (by linarith)).1,
    clopperPearsonLower_le_clopperPearsonUpper (by norm_num) hα0 hα1.le,
    (clopperPearsonUpper_mem_Ioo (by norm_num) hα0 (by linarith)).2⟩

/-- Test inversion at `n = 3`, `x = 3`, `α = 1/4`: `p = 3/4` is inside the interval because
`P_{3/4}(X ≥ 3) = 27/64 ≥ 1/8`. -/
example : clopperPearsonLower 3 3 (1 / 4) ≤ 3 / 4 := by
  rw [clopperPearsonLower_le_iff le_rfl (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [binomTail]

/-- Test inversion at `n = 3`, `x = 3`, `α = 1/4`: `p = 1/4` is outside the interval because
`P_{1/4}(X ≥ 3) = 1/64 < 1/8`. -/
example : ¬ clopperPearsonLower 3 3 (1 / 4) ≤ 1 / 4 := by
  rw [clopperPearsonLower_le_iff le_rfl (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num [binomTail]

/-! ### Coverage -/

/-- The coverage theorem applied to the canonical binomial count (`id` under `Bin(n, p)`). -/
example (n : ℕ) (p : unitInterval) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α ≤ (binomial n p).real
      {k | clopperPearsonLower n k α ≤ p ∧ (p : ℝ) ≤ clopperPearsonUpper n k α} :=
  clopperPearson_coverage HasLaw.id hα0 hα1

/-- The one-sided bounds each cover with probability at least `1 - α / 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X (binomial n p) P) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    1 - α / 2 ≤ P.real {ω | clopperPearsonLower n (X ω) α ≤ p} ∧
      1 - α / 2 ≤ P.real {ω | (p : ℝ) ≤ clopperPearsonUpper n (X ω) α} :=
  ⟨clopperPearsonLower_coverage hX hα0 hα1, clopperPearsonUpper_coverage hX hα0 hα1⟩

/-! Helpers (private): the one-sided true-`p` receipts, shared by the one-sided
`example`s below and the two-sided combination. -/

private theorem lowerReceipt {n : ℕ} {p : unitInterval}
    (hvalid : IsValidPValue (binomial n p) (upperTailPValue (binomial n p) id))
    (hL : ∀ {x : ℕ} {a r : ℝ}, x ≤ n → 0 < a → a < 2 → r ∈ Set.Icc (0 : ℝ) 1 →
      (clopperPearsonLower n x a ≤ r ↔ a / 2 ≤ binomTail n x r))
    (hUB : ∀ (m y : ℕ) (r : unitInterval), upperTail (binomial m r) y = binomTail m y r)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 - s ≤ (binomial n p).real {x | clopperPearsonLower n x (2 * s) ≤ (p : ℝ)} := by
  have hcov := coverage_of_isValidPValue
    (P := fun _ : Unit => binomial n p) (τ := fun _ : Unit => p)
    (p := fun (q : unitInterval) (ω : ℕ) => upperTailPValue (binomial n q) id ω)
    (hp := fun t => Measurable.of_discrete)
    (hvalid := fun _ => hvalid)
    (hα := ⟨le_of_lt hs0, le_of_lt hs1⟩) ()
  refine hcov.trans (measureReal_mono ?_)
  intro x hx
  simp only [Set.mem_ofPred_eq]
  simp only [confSetOfTests, Set.mem_ofPred_eq, upperTailPValue, id_eq, not_le] at hx
  rw [hUB n x p] at hx
  by_cases hxn : x ≤ n
  · exact (hL (x := x) (a := 2 * s) (r := (p : ℝ)) hxn (by linarith) (by linarith) p.2).mpr
      (by linarith)
  · exfalso
    have hnx : n < x := by omega
    have h0 : binomTail n x (p : ℝ) = 0 := binomTail_of_lt hnx (p : ℝ)
    linarith

private theorem upperReceipt {n : ℕ} {p : unitInterval}
    (hU : ∀ {x : ℕ} {a r : ℝ}, x ≤ n → 0 < a → a < 2 → r ∈ Set.Icc (0 : ℝ) 1 →
      (r ≤ clopperPearsonUpper n x a ↔ a / 2 ≤ 1 - binomTail n (x + 1) r))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 - s ≤ (binomial n p).real {x | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)} := by
  have hUeq1 : ∀ {x : ℕ}, n < x → clopperPearsonUpper n x (2 * s) = 1 := by
    intro x hnx
    have hset : {r : ℝ | r ∈ Set.Icc 0 1 ∧ (2 * s) / 2 ≤ 1 - binomTail n (x + 1) r}
        = Set.Icc 0 1 := by
      ext r
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact h.1
      · intro hr
        refine ⟨hr, ?_⟩
        have h0 : binomTail n (x + 1) r = 0 := binomTail_of_lt (by omega) r
        rw [h0, sub_zero]
        linarith
    rw [clopperPearsonUpper, hset, csSup_Icc zero_le_one]
  have hle_of_mem : ∀ {x : ℕ},
      x ∈ {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)}ᶜ → x ≤ n := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    by_contra hcon
    have hnx : n < x := by omega
    have h1 := hUeq1 hnx
    have hp1 : (p : ℝ) ≤ 1 := p.2.2
    linarith
  have hsub : {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)}ᶜ
      ⊆ {x : ℕ | (binomial n p).real (Set.Iic x) < s} := by
    intro x hx
    have hxn : x ≤ n := hle_of_mem hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
    simp only [Set.mem_ofPred_eq]
    have hiff := hU (x := x) (a := 2 * s) (r := (p : ℝ)) hxn (by linarith) (by linarith) p.2
    rw [binomial_real_Iic n x p, ← not_le]
    intro hle
    exact hx (hiff.mpr (by linarith))
  have hBfin : {x : ℕ | (binomial n p).real (Set.Iic x) < s}.Finite := by
    have hsubB : {x : ℕ | (binomial n p).real (Set.Iic x) < s} ⊆ ↑(Finset.range (n + 1)) := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hcon
      have hnx1 : n < x + 1 := by omega
      have h1 : (binomial n p).real (Set.Iic x) = 1 := by
        rw [binomial_real_Iic n x p, binomTail_of_lt hnx1 _, sub_zero]
      linarith
    exact (Finset.finite_toSet _).subset hsubB
  have hEcompl_le : (binomial n p).real
      {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)}ᶜ ≤ s := by
    by_cases hBempty : {x : ℕ | (binomial n p).real (Set.Iic x) < s} = ∅
    · have hle := measureReal_mono (μ := binomial n p) hsub
      rw [hBempty, measureReal_empty] at hle
      linarith
    · have hBne : {x : ℕ | (binomial n p).real (Set.Iic x) < s}.Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hBempty
      obtain ⟨b, hb⟩ := hBne
      have hne : hBfin.toFinset.Nonempty := ⟨b, hBfin.mem_toFinset.mpr hb⟩
      refine le_trans (measureReal_mono hsub) ?_
      have hkB : (binomial n p).real (Set.Iic (hBfin.toFinset.max' hne)) < s :=
        hBfin.mem_toFinset.mp (Finset.max'_mem _ hne)
      have hBIic : {x : ℕ | (binomial n p).real (Set.Iic x) < s}
          ⊆ Set.Iic (hBfin.toFinset.max' hne) := by
        intro x hx
        simp only [Set.mem_Iic]
        exact Finset.le_max' _ _ (hBfin.mem_toFinset.mpr hx)
      exact (lt_of_le_of_lt (measureReal_mono hBIic) hkB).le
  have hcompl := probReal_compl_eq_one_sub (μ := binomial n p)
    (s := {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)}) MeasurableSet.of_discrete
  linarith

/-- Lower one-sided receipt: the inverted boundary p-value covers, and the Clopper–Pearson
lower set contains the inverted acceptance event (outward inclusion via `measureReal_mono`;
no event equality is claimed, since inversion accepts at `s < tail` while the CP set uses
`s ≤ tail`). -/
example {n : ℕ} {p : unitInterval}
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 - s ≤ (binomial n p).real {x | clopperPearsonLower n x (2 * s) ≤ (p : ℝ)} := by
  exact lowerReceipt (isValidPValue_upperTailPValue HasLaw.id)
    (fun hxn ha0 ha2 hr => clopperPearsonLower_le_iff hxn ha0 ha2 hr)
    (fun m y r => upperTail_binomial m y r) hs0 hs1

/-- Upper one-sided receipt, proved structurally: the complement of the upper event is
contained in a downward-closed null-controlled set. No lower-tail p-value validity is used
(none exists on main). -/
example {n : ℕ} {p : unitInterval}
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    1 - s ≤ (binomial n p).real {x | (p : ℝ) ≤ clopperPearsonUpper n x (2 * s)} := by
  exact upperReceipt
    (fun hxn ha0 ha2 hr => le_clopperPearsonUpper_iff hxn ha0 ha2 hr) hs0 hs1

/-- Two-sided combination at `α / 2` per side: the union bound over the two one-sided
complements. -/
example {n : ℕ} {p : unitInterval}
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    1 - α ≤ (binomial n p).real
      {x | clopperPearsonLower n x α ≤ (p : ℝ) ∧ (p : ℝ) ≤ clopperPearsonUpper n x α} := by
  have hs0 : (0 : ℝ) < α / 2 := by linarith
  have hs1 : α / 2 < 1 := by linarith
  have h2s : 2 * (α / 2) = α := by ring
  have hlow := lowerReceipt
    (isValidPValue_upperTailPValue (μ := binomial n p) (ν := binomial n p) (X := id)
      HasLaw.id)
    (fun hxn ha0 ha2 hr => clopperPearsonLower_le_iff hxn ha0 ha2 hr)
    (fun m y r => upperTail_binomial m y r) hs0 hs1
  rw [h2s] at hlow
  have hup := upperReceipt (n := n) (p := p)
    (fun hxn ha0 ha2 hr => le_clopperPearsonUpper_iff hxn ha0 ha2 hr) hs0 hs1
  rw [h2s] at hup
  have hcA := probReal_compl_eq_one_sub (μ := binomial n p)
    (s := {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ)}) MeasurableSet.of_discrete
  have hcB := probReal_compl_eq_one_sub (μ := binomial n p)
    (s := {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x α}) MeasurableSet.of_discrete
  have hunion := measureReal_union_le (μ := binomial n p)
    {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ)}ᶜ
    {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x α}ᶜ
  have hgoal := probReal_compl_eq_one_sub (μ := binomial n p)
    (s := {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ) ∧ (p : ℝ) ≤ clopperPearsonUpper n x α})
    MeasurableSet.of_discrete
  have hcompl : {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ) ∧
      (p : ℝ) ≤ clopperPearsonUpper n x α}ᶜ
      = {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ)}ᶜ ∪
        {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x α}ᶜ := by
    rw [show {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ) ∧
      (p : ℝ) ≤ clopperPearsonUpper n x α}
      = {x : ℕ | clopperPearsonLower n x α ≤ (p : ℝ)} ∩
        {x : ℕ | (p : ℝ) ≤ clopperPearsonUpper n x α} from rfl,
      Set.compl_inter]
  rw [hcompl] at hgoal
  linarith

/-- Boundary: `L(n, 0, α) = 0` and `U(n, n, α) = 1` for `α ≤ 2`. -/
example (n : ℕ) {α : ℝ} (hα : α ≤ 2) :
    clopperPearsonLower n 0 α = 0 ∧ clopperPearsonUpper n n α = 1 := by
  exact ⟨clopperPearsonLower_zero n hα, clopperPearsonUpper_self n hα⟩

end MathlibExtTest.Probability.Statistics.ExactTests.ClopperPearson

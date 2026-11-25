/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Randomized
import MathlibExt.Probability.ProbabilityMassFunction.Uniform
import MathlibExt.Probability.Statistics.Learning.FiniteRisk

/-!
# Newman's theorem: public coins versus private coins

A public-coin protocol (`PublicCoinProtocol`) lets Alice and Bob read a shared random string.
In a private-coin protocol each party only sees its own random string: we model it as a
deterministic protocol in which Alice holds `(x, a)` and Bob holds `(y, b)`, with `a` and `b`
independent and uniform on finite sets. Newman's theorem says that public coins save at most
`log₂(n / ε²) + O(1)` bits on `n`-bit inputs, at the price of doubling the error
(I. Newman, "Private vs. common random bits in communication complexity", Inform. Process. Lett.
39 (1991); stated as Theorem 3.5 in A. Rao and A. Yehudayoff, *Communication Complexity*,
early draft).
-/

@[expose] public section

namespace MathlibExt.Computability.CommunicationComplexity

/-- **Error probability of a private-coin protocol.** For a deterministic protocol `p` in which
Alice holds `(x, a)` and Bob holds `(y, b)`, with nonempty finite sets `RA` and `RB` of private
random strings, the fraction of pairs `(a, b) ∈ RA × RB` on which `p` outputs a value other than
`f x y`: the probability of an error when `a` and `b` are independent and uniform. For an empty
set, which is excluded, every event would get probability `0`. -/
noncomputable def privateErrorProb {X Y RA RB : Type*} [Fintype RA] [Fintype RB] [Nonempty RA]
    [Nonempty RB] (p : Protocol (X × RA) (Y × RB)) (f : X → Y → Bool) (x : X) (y : Y) : ℚ :=
  ((Finset.univ.filter fun r : RA × RB => p.eval (x, r.1) (y, r.2) ≠ f x y).card : ℚ) /
    (Fintype.card RA * Fintype.card RB)

open MeasureTheory

/-- Run a deterministic protocol on the first components of the parties' inputs. -/
private def ignoreCoins {X Y A B : Type*} : Protocol X Y → Protocol (X × A) (Y × B)
  | .output b => .output b
  | .alice f p q => .alice (f ∘ Prod.fst) (ignoreCoins p) (ignoreCoins q)
  | .bob f p q => .bob (f ∘ Prod.fst) (ignoreCoins p) (ignoreCoins q)

private lemma eval_ignoreCoins {X Y A B : Type*} (p : Protocol X Y)
    (x : X × A) (y : Y × B) : (ignoreCoins p).eval x y = p.eval x.1 y.1 := by
  induction p <;> simp_all [ignoreCoins, Protocol.eval]

private lemma depth_ignoreCoins {X Y A B : Type*} (p : Protocol X Y) :
    (ignoreCoins (A := A) (B := B) p).depth = p.depth := by
  induction p <;> simp_all [ignoreCoins, Protocol.depth]

/-- One table simultaneously approximates the uniform probability of every bad event. -/
private lemma exists_table {I R : Type} [Fintype I] [Fintype R] [Nonempty R]
    (bad : I → Set R) {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 0 < m)
    (htail : 2 * (Fintype.card I : ℝ) * Real.exp (-2 * m * ε ^ 2) < 1) :
    ∃ S : Fin m → R, ∀ i,
      (m : ℝ)⁻¹ * ∑ a, (bad i).indicator (1 : R → ℝ) (S a) ≤
        (Nat.card (bad i) : ℝ) / Fintype.card R + ε := by
  classical
  let : MeasurableSpace R := ⊤
  let μ := (PMF.uniformFintype R).toMeasure
  let e := Fintype.equivFin I
  let f (j : Fin (Fintype.card I)) := (bad (e.symm j)).indicator (1 : R → ℝ)
  have hb := ProbabilityTheory.measure_exists_abs_empirical_sub_integral_ge_le μ hm f
    (fun _ => Measurable.of_discrete) (fun j => ae_of_all _ fun r => by
      simp only [f, Set.indicator, Pi.one_apply]
      split <;> norm_num) hε.le
  have hmean (i : I) :
      ∫ r, (bad i).indicator (1 : R → ℝ) r ∂μ =
        (Nat.card (bad i) : ℝ) / Fintype.card R := by
    rw [integral_indicator_one MeasurableSet.of_discrete, measureReal_def,
      PMF.toMeasure_uniformFintype_apply _ MeasurableSet.of_discrete]
    simp [Nat.card_eq_fintype_card]
  by_contra! h
  have hall : {S : Fin m → R | ∃ j, ε ≤
      |(m : ℝ)⁻¹ * ∑ a, f j (S a) - ∫ r, f j r ∂μ|} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro S
    obtain ⟨i, hi⟩ := h S
    refine ⟨e i, le_trans ?_ (le_abs_self _)⟩
    simpa only [f, Equiv.symm_apply_apply, hmean] using (le_sub_iff_add_le'.2 hi.le)
  rw [hall, probReal_univ] at hb
  exact (not_lt_of_ge hb) htail

/-- A power-of-two table size makes each address a fixed-length bit string. -/
private lemma exists_address_length {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hhalf : ε ≤ 1 / 2) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.logb 2 (n / ε ^ 2) + 2 ∧
      2 * (n : ℝ) ≤ (2 : ℝ) ^ k * ε ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hratio : 1 ≤ (n : ℝ) / ε ^ 2 := by
    apply (le_div_iff₀ hsq).2
    nlinarith [mul_nonneg hε.le (show 0 ≤ 1 - ε by linarith)]
  let b := Real.logb 2 (n / ε ^ 2)
  refine ⟨⌈b⌉₊ + 1, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio)
    push_cast
    dsimp [b] at *
    linarith
  · have hpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
        (zero_lt_one.trans_le hratio)).1 (Nat.le_ceil b)
    rw [Real.rpow_natCast, div_le_iff₀ hsq] at hpow
    rw [pow_succ]
    linarith

/-- The union bound over the pairs of bit strings is strictly below one. -/
private lemma tail_lt_one {n m : ℕ} (hn : 1 ≤ n) {ε : ℝ}
    (hm : 2 * (n : ℝ) ≤ m * ε ^ 2) :
    2 * (Fintype.card ((Fin n → Bool) × (Fin n → Bool)) : ℝ) *
      Real.exp (-2 * m * ε ^ 2) < 1 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp 1 * (Real.exp 1 ^ n * Real.exp 1 ^ n) *
          Real.exp (-2 * m * ε ^ 2) := by gcongr
    _ < 1 := by
      rw [← Real.exp_nat_mul, mul_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        Real.exp_lt_one_iff]
      linarith

/-- **Newman's theorem.** There is a constant `C₀` such that for every `n ≥ 1` and
`0 < ε ≤ 1 / 2`: if
`g : {0,1}^n × {0,1}^n → {0,1}` is computed by a public-coin protocol (with a nonempty finite
set of random strings) of cost `c` and error at most `ε` on every input, then it is computed by
a private-coin protocol, with nonempty finite sets of private random strings, of cost at most
`c + log₂(n / ε²) + C₀` and error at most `2ε` on every input (A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Theorem 3.5, attributed there to Newman, 1991). The
source leaves the range of `ε` implicit; its proof samples `O(n / ε²)` random strings, and some
upper bound on `ε` is needed: for large `ε` a cost-0 protocol meets the hypothesis while
`log₂(n / ε²)` is negative. -/
theorem newman_private_coins :
    ∃ C₀ : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (g : (Fin n → Bool) → (Fin n → Bool) → Bool) (R : Type) [Fintype R] [Nonempty R]
        (P : PublicCoinProtocol (Fin n → Bool) (Fin n → Bool) R),
        (∀ x y, (P.errorProb g x y : ℝ) ≤ ε) →
        ∃ (RA RB : Type) (_ : Fintype RA) (_ : Fintype RB) (_ : Nonempty RA) (_ : Nonempty RB)
          (p : Protocol ((Fin n → Bool) × RA) ((Fin n → Bool) × RB)),
          (p.depth : ℝ) ≤ P.cost + Real.logb 2 (n / ε ^ 2) + C₀ ∧
            ∀ x y, (privateErrorProb p g x y : ℝ) ≤ 2 * ε := by
  classical
  refine ⟨2, ?_⟩
  intro n hn ε hε hhalf g R _ _ P hP
  obtain ⟨k, hk, hsize⟩ := exists_address_length hn hε hhalf
  let A := Fin k → Bool
  let m := Fintype.card A
  have hm : m = 2 ^ k := by simp [m, A]
  let bad (i : (Fin n → Bool) × (Fin n → Bool)) : Set R :=
    {r | (P.run r).eval i.1 i.2 ≠ g i.1 i.2}
  have htail := tail_lt_one (m := m) hn (by simpa [hm] using hsize)
  obtain ⟨S, hS⟩ := exists_table bad hε Fintype.card_pos htail
  -- Alice samples a uniform row and sends its address. Bob needs no randomness.
  let e := Fintype.equivFin A
  let run (a : A) : Protocol ((Fin n → Bool) × A) ((Fin n → Bool) × Unit) :=
    ignoreCoins (P.run (S (e a)))
  let p := Protocol.aliceSends k Prod.snd run
  refine ⟨A, Unit, inferInstance, inferInstance, inferInstance, inferInstance, p, ?_, ?_⟩
  · have hd : p.depth ≤ k + P.cost := Protocol.depth_aliceSends_le _ _ _ fun a => by
      simpa only [run, depth_ignoreCoins] using P.depth_le_cost (S (e a))
    exact (show (p.depth : ℝ) ≤ k + P.cost by exact_mod_cast hd).trans (by linarith)
  · intro x y
    have hmean : (Nat.card (bad (x, y)) : ℝ) / Fintype.card R ≤ ε := by
      simpa [bad, PublicCoinProtocol.errorProb, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hP x y
    let loss := (bad (x, y)).indicator (1 : R → ℝ)
    have heval (a : A) (b : Unit) :
        p.eval (x, a) (y, b) = (P.run (S (e a))).eval x y := by
      simp only [p, Protocol.eval_aliceSends, run, eval_ignoreCoins]
    have hcount : (privateErrorProb p g x y : ℝ) = (m : ℝ)⁻¹ * ∑ a, loss (S a) := by
      rw [privateErrorProb]
      push_cast
      rw [Finset.natCast_card_filter, Fintype.sum_prod_type]
      simp only [heval, Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, mul_one]
      rw [← e.sum_comp (fun a => loss (S a))]
      simp [loss, bad, Set.indicator, m, A, div_eq_inv_mul]
    rw [hcount]
    exact (hS (x, y)).trans (by simpa only [two_mul] using add_le_add_left hmean ε)

end MathlibExt.Computability.CommunicationComplexity

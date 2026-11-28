/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidPartialSum
import MathlibExt.NumberTheory.LexMinimalExtensionMonoid

open MetaMathlibExt

/-- An empty prefix forces the first summand to equal its zero competitor. -/
example {η₁ η₂ : ℕ → ℕ} (h : IsLexMinimalExtensionOf (η₁ + η₂) 0)
    (h₁ : IsBinomidIndex η₁) (h₂ : IsBinomidIndex η₂) : η₁ = 0 := by
  have hmin := (h.of_add h₁ h₂).1
  rcases hmin.2 _ (isBinomidIndex_const 0) (by simp) with heq | ⟨j, _, hj⟩
  · exact heq
  · exact (Nat.not_lt_zero _ hj).elim

/-- The sequence 0, 1, 2, … can be replaced by zero after its first entry. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) :
    ¬ IsLexMinimalExtensionOf (η + fun i => i) 1 := by
  intro h
  have hmin := (h.of_add hη (isBinomidIndex_of_monotone monotone_id)).2
  rcases hmin.2 _ (isBinomidIndex_const 0) (by simp) with heq | ⟨j, _, hj⟩
  · exact Nat.one_ne_zero (congrFun heq 1)
  · exact Nat.not_lt_zero _ hj

/-- There are no maximizing positive indices in an empty prefix. -/
example (η : ℕ → ℕ) : maxAverageIndices η 0 = ∅ := by
  simp [maxAverageIndices]

/-- For the prefix `0, 2`, an odd length cannot attain its maximal average of one. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 2)
    (k : ℕ) : binomidAverage η (2 * k + 1) ≠ 1 := by
  have h₂ : binomidAverage η 2 = 1 := by
    norm_num [binomidAverage, Finset.sum_range_succ, h₀, h₁]
  have hJ : maxAverageIndices η 2 = {2} := by
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    norm_num [maxAverageIndices, hI, Finset.filter_insert, Finset.filter_singleton,
      binomidAverage_one, h₀, h₂]
  intro heq
  have hd := hη.gcd_maxAverageIndices_dvd (i := 2 * k + 1) (by omega)
    ⟨2, by simp [hJ], heq.trans h₂.symm⟩
  simp [hJ] at hd

/-- For the zero sequence even a single initial entry gives least period one. -/
example : IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → (0 : ℕ → ℕ) (i + q) = (0 : ℕ → ℕ) i} 1 := by
  simpa [maxAverageIndices_one] using
    (isLexMinimalExtensionOf_zero 1).isLeast_period_gcd_maxAverageIndices le_rfl

/-- The prefix `0, 0, 0, 4, 0, 2` attains its largest average at lengths four and six.
Its lex-minimal extension has least eventual period two, although two is not a maximizer. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 6)
    (hpre : ∀ i < 6, η i = if i = 3 then 4 else if i = 5 then 2 else 0) :
    IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i} 2 := by
  have hI : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by decide
  have hJ : maxAverageIndices η 6 = {4, 6} := by
    norm_num [maxAverageIndices, hI, Finset.filter_insert, Finset.filter_singleton,
      binomidAverage, Finset.sum_range_succ, hpre]
  simpa [hJ, show gcd (4 : ℕ) 6 = 2 by decide] using
    hη.isLeast_period_gcd_maxAverageIndices (by decide)

/-- The singleton containing zero generates the zero submonoid but fails independence. -/
example : ¬ IsAddMonoidBasis ({0} : Set ℕ) {0} :=
  fun h => h.zero_notMem rfl

/-- The constant two sequence splits into two nonzero constant one sequences. -/
example : ¬ IsAtomicBinomidIndex (fun _ => 2) := by
  intro h
  rcases h.2.2 _ _ (isBinomidIndex_const 1) (isBinomidIndex_const 1) rfl with hz | hz <;>
    exact Nat.one_ne_zero (congrFun hz 0)

/-- In the zero submonoid the empty sum generates everything and the only basis is empty. -/
example {ι : Type*} (B : Set (ι → ℕ)) :
    IsAddMonoidBasis (↑(⊥ : AddSubmonoid (ι → ℕ))) B ↔ B = ∅ := by
  rw [isAddMonoidBasis_iff_eq_atoms]
  · simp
  · intro x hx
    simp [AddSubmonoid.mem_bot.mp hx]

/-- On one coordinate, the unique basis of the full monoid consists of the unit vector. -/
example (B : Set (Unit → ℕ)) :
    IsAddMonoidBasis (Set.univ : Set (Unit → ℕ)) B ↔ B = {1} := by
  let M : AddSubmonoid (Unit → ℕ) := ⊤
  have atoms : {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0} = {1} := by
    ext a
    constructor
    · rintro ⟨_, ha, hsplit⟩
      have hpos : 0 < a () := Nat.pos_of_ne_zero fun h => ha (funext fun _ => h)
      let b : Unit → ℕ := fun i => a i - 1
      have hab : a = 1 + b := funext fun _ => by
        change a () = 1 + (a () - 1)
        omega
      rcases hsplit 1 (by trivial) b (by trivial) hab with h | h
      · exact (Nat.one_ne_zero (congrFun h ())).elim
      · simpa [h] using hab
    · rintro rfl
      refine ⟨by trivial, fun h => Nat.one_ne_zero (congrFun h ()), ?_⟩
      intro y _ z _ heq
      have h : 1 = y () + z () := congrFun heq ()
      rcases Nat.eq_zero_or_pos (y ()) with hy | hy
      · exact Or.inl (funext fun _ => hy)
      · exact Or.inr (funext fun _ => (show z () = 0 by omega))
  change IsAddMonoidBasis (M : Set (Unit → ℕ)) B ↔ B = {1}
  rw [isAddMonoidBasis_iff_eq_atoms, atoms]
  intro x _
  rw [atoms]
  have hx : x = x () • (1 : Unit → ℕ) := by
    ext i
    simp
  exact hx ▸ AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure rfl) _

private abbrev knapsackPrefix (η : ℕ → ℕ) (c : ℕ) : ℕ := ∑ i ∈ Finset.range c, η i

private abbrev knapsackWeight (n : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 2, n i * i

private abbrev knapsackValue (η n : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 2, n i * knapsackPrefix η i

-- Compute both optima independently using the prefix [0, 2]. At capacity two, one item of
-- weight two suffices; at capacity five, it is used twice and a weight-one item fills the slack.
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 2)
    (c : ℕ) (hc : c = 2 ∨ c = 5) :
    ∃ n : ℕ → ℕ, knapsackWeight n = c ∧ knapsackValue η n = knapsackPrefix η c ∧
      ∀ k : ℕ → ℕ, knapsackWeight k ≤ c → knapsackValue η k ≤ knapsackValue η n := by
  have hS1 : knapsackPrefix η 1 = 0 := by simp [knapsackPrefix, h₀]
  have hS2 : knapsackPrefix η 2 = 2 := by simp [knapsackPrefix, Finset.sum_range_succ, h₀, h₁]
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hW (n : ℕ → ℕ) : knapsackWeight n = n 1 + n 2 * 2 := by simp [knapsackWeight, hI]
  have hV (n : ℕ → ℕ) : knapsackValue η n = n 2 * 2 := by simp [knapsackValue, hI, hS1, hS2]
  rcases hc with rfl | rfl
  · let n : ℕ → ℕ := fun i => if i = 2 then 1 else 0
    refine ⟨n, by norm_num [hW, n], by norm_num [hV, hS2, n], ?_⟩
    intro k hk
    rw [hW] at hk
    norm_num [hV, n]
    omega
  · have hrec (j : ℕ) (hj : 2 < j) : knapsackPrefix η j =
        (Finset.Ico 1 j).sup (fun i => knapsackPrefix η (j - i) + knapsackPrefix η i) :=
      (isBinomidIndex_iff_partialSum η).2 2 hη j hj
    have hI3 : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by decide
    have hI4 : Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) := by decide
    have hI5 : Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) := by decide
    have hS3 : knapsackPrefix η 3 = 2 := by
      rw [hrec 3 (by decide), hI3]
      norm_num [Finset.sup_insert, hS1, hS2]
    have hS4 : knapsackPrefix η 4 = 4 := by
      rw [hrec 4 (by decide), hI4]
      norm_num [Finset.sup_insert, hS1, hS2, hS3]
    have hS5 : knapsackPrefix η 5 = 4 := by
      rw [hrec 5 (by decide), hI5]
      norm_num [Finset.sup_insert, hS1, hS2, hS3, hS4]
    let n : ℕ → ℕ := fun i => if i = 1 then 1 else if i = 2 then 2 else 0
    refine ⟨n, by norm_num [hW, n], by norm_num [hV, hS5, n], ?_⟩
    intro k hk
    rw [hW] at hk
    norm_num [hV, n]
    omega

-- The zero sequence satisfies the binomid prefix/suffix inequality directly.
example : ∑ _ ∈ Finset.range 2, (0 : ℕ) ≤ ∑ _ ∈ Finset.Ico 1 3, (0 : ℕ) := by simp

example : IsBinomidIndex (fun _ => 0) := (isLexMinimalExtensionOf_zero 1).isBinomidIndex

-- A concrete client: with only unit weights, exact filling forces three copies.
example : ∃ n : ℕ → ℕ, n 1 = 3 := by
  obtain ⟨n, hw, _⟩ := (isLexMinimalExtensionOf_zero 1).exists_knapsack
    (c := 3) (by decide) (by decide)
  exact ⟨n, by simpa using hw⟩

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.AlgebraicGeometry.BernsteinBoxes
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MvPolynomial

private theorem bernstein_one {σ : Type*} [Fintype σ] (n k : σ → ℕ) :
    bernsteinCoeff n (1 : MvPolynomial σ ℝ) k = 1 := by
  simpa only [C_1] using bernsteinCoeff_C n k 1

-- Each constraint has its own coordinate-degree vector.
example {σ ι κ : Type*} [Fintype σ] {I : Finset ι} {J : Finset κ}
    {g : ι → MvPolynomial σ ℝ} {h : κ → MvPolynomial σ ℝ}
    {ng : ι → σ → ℕ} {nh : κ → σ → ℕ} {a b : σ → ℝ}
    (hab : a ≤ b)
    (hg : ∀ i ∈ I, ∀ v, (g i).degreeOf v ≤ ng i v)
    (hh : ∀ j ∈ J, ∀ v, (h j).degreeOf v ≤ nh j v)
    (cg : ∀ i ∈ I, ∀ k : (v : σ) → Fin (ng i v + 1),
      0 ≤ bernsteinCoeff (ng i) (boxPullback a b (g i)) (fun v => k v))
    (ch : ∀ j ∈ J, ∀ k : (v : σ) → Fin (nh j v + 1),
      bernsteinCoeff (nh j) (boxPullback a b (h j)) (fun v => k v) = 0) :
    Set.Icc a b ⊆ basicClosedSet I J g h :=
  Icc_subset_basicClosedSet_of_bernsteinCoeff hab hg hh cg ch

-- Intrinsic semialgebraicity needs no ordering of endpoints.
example {σ : Type*} [Fintype σ] (a b : σ → ℝ) :
    TauCeti.IsSemialgebraic (Set.Icc a b) :=
  TauCeti.isSemialgebraic_Icc a b

private noncomputable def disk : MvPolynomial (Fin 2) ℝ := 1 - X 0 ^ 2 - X 1 ^ 2

private theorem disk_degree (v : Fin 2) : disk.degreeOf v ≤ 2 := by
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sub_le _ _ _).trans
    exact max_le (by simp) ((degreeOf_pow_le _ _ _).trans (by fin_cases v <;> simp [degreeOf_X]))
  · exact (degreeOf_pow_le _ _ _).trans (by fin_cases v <;> simp [degreeOf_X])

private theorem disk_small_coeff (k : Fin 2 → Fin 3) :
    0 ≤ bernsteinCoeff (fun _ => 2) (boxPullback ![-1/2, -1/2] ![1/2, 1/2] disk)
      (fun v => k v) := by
  have hp : boxPullback ![-1/2, -1/2] ![1/2, 1/2] disk =
      C (1/2) + X 0 + X 1 - X 0 ^ 2 - X 1 ^ 2 := by
    apply MvPolynomial.funext
    intro x
    norm_num [eval_boxPullback, disk]
    ring
  rw [hp]
  generalize h0 : k 0 = i
  generalize h1 : k 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [sub_eq_add_neg, bernsteinCoeff_add, bernsteinCoeff_neg, bernsteinCoeff_C, X, pow_two,
      monomial_mul_monomial, bernsteinCoeff_monomial, Fin.prod_univ_two,
      Finsupp.single_apply, h0, h1, Nat.choose]

-- A genuine two-variable disk enclosure: all nine degree-(2,2) coefficients
-- on this box are at least 1/2 (positivity suffices for inclusion).
example : Set.Icc (![-1/2, -1/2] : Fin 2 → ℝ) ![1/2, 1/2] ⊆
    basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit) (fun _ => disk) (fun _ => 0) := by
  apply Icc_subset_basicClosedSet_of_bernsteinCoeff
    (ng := fun _ _ => 2) (nh := fun _ _ => 0)
  · intro v; fin_cases v <;> norm_num
  · exact fun _ _ => disk_degree
  · simp
  · exact fun _ _ => disk_small_coeff
  · simp

private theorem disk_far_coeff (k : Fin 2 → Fin 3) :
    bernsteinCoeff (fun _ => 2) (boxPullback ![2, 0] ![3, 1] disk) (fun v => k v) < 0 := by
  have hp : boxPullback ![2, 0] ![3, 1] disk =
      C (-3) - (4 : ℝ) • X 0 - X 0 ^ 2 - X 1 ^ 2 := by
    norm_num [boxPullback, disk, smul_eq_C_mul, map_ofNat]
    ring
  rw [hp]
  generalize h0 : k 0 = i
  generalize h1 : k 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [sub_eq_add_neg, bernsteinCoeff_add, bernsteinCoeff_neg,
      bernsteinCoeff_smul, bernsteinCoeff_C, X, pow_two,
      monomial_mul_monomial, bernsteinCoeff_monomial, Fin.prod_univ_two,
      Finsupp.single_apply, h0, h1, Nat.choose]

example : Disjoint (Set.Icc (![2, 0] : Fin 2 → ℝ) ![3, 1])
    (basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit) (fun _ => disk) (fun _ => 0)) :=
  disjoint_Icc_basicClosedSet_of_bernsteinCoeff_neg (i := ()) (by simp) disk_degree
    (by intro v; fin_cases v <;> norm_num) disk_far_coeff

-- Nonpositive coefficients do not imply disjointness: [1,2]×{0} has
-- coefficients 0,-1,-3 and contains the feasible disk boundary point (1,0).
example (k : Fin 2 → Fin 3) :
    bernsteinCoeff (fun _ => 2) (boxPullback ![1, 0] ![2, 0] disk) (fun v => k v) ≤ 0 := by
  have hp : boxPullback ![1, 0] ![2, 0] disk = -(2 : ℝ) • X 0 - X 0 ^ 2 := by
    norm_num [boxPullback, disk, smul_eq_C_mul, map_ofNat]
    ring
  rw [hp]
  generalize h0 : k 0 = i
  fin_cases i <;>
    norm_num [sub_eq_add_neg, bernsteinCoeff_add, bernsteinCoeff_neg,
      bernsteinCoeff_smul, X, pow_two,
      monomial_mul_monomial, bernsteinCoeff_monomial, Fin.prod_univ_two,
      Finsupp.single_apply, h0, Nat.choose]

example : ¬Disjoint (Set.Icc (![1, 0] : Fin 2 → ℝ) ![2, 0])
    (basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit) (fun _ => disk) (fun _ => 0)) := by
  intro hd
  apply (Set.disjoint_left.mp hd) (a := ![1, 0])
  · constructor <;> intro v <;> fin_cases v <;> norm_num
  · norm_num [basicClosedSet, disk]

-- A genuinely nonconstant equality can vanish on a box with a collapsed
-- coordinate. The degree vector is heterogeneous and includes zero.
example : Set.Icc (![-1, 0] : Fin 2 → ℝ) ![1, 0] ⊆
    basicClosedSet (∅ : Finset Unit) ({()} : Finset Unit)
      (fun _ => 0) (fun _ => X 1) := by
  apply Icc_subset_basicClosedSet_of_bernsteinCoeff
    (ng := fun _ _ => 0) (nh := fun _ => ![0, 1])
  · intro v; fin_cases v <;> norm_num
  · simp
  · intro j hj v; fin_cases v <;> simp [degreeOf_X]
  · simp
  · intro j hj k
    simp [boxPullback]

example : Disjoint (Set.Icc (![-1, 1] : Fin 2 → ℝ) ![1, 2])
    (basicClosedSet (∅ : Finset Unit) ({()} : Finset Unit)
      (fun _ => 0) (fun _ => X 1)) := by
  apply disjoint_Icc_basicClosedSet_of_bernsteinCoeff_eq_pos
    (j := ()) (n := ![0, 1]) (by simp)
  · intro v; fin_cases v <;> simp [degreeOf_X]
  · intro v; fin_cases v <;> norm_num
  · intro k
    have hp : boxPullback ![-1, 1] ![1, 2] (X 1 : MvPolynomial (Fin 2) ℝ) =
        C 1 + X 1 := by norm_num [boxPullback, map_ofNat]
    rw [hp, bernsteinCoeff_add, bernsteinCoeff_C]
    generalize h : k 1 = i
    fin_cases i <;> norm_num [bernsteinCoeff_add, bernsteinCoeff_C, X,
      bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply, h, Nat.choose]

example : Disjoint (Set.Icc (![-1, -2] : Fin 2 → ℝ) ![1, -1])
    (basicClosedSet (∅ : Finset Unit) ({()} : Finset Unit)
      (fun _ => 0) (fun _ => X 1)) := by
  apply disjoint_Icc_basicClosedSet_of_bernsteinCoeff_eq_neg
    (j := ()) (n := ![0, 1]) (by simp)
  · intro v; fin_cases v <;> simp [degreeOf_X]
  · intro v; fin_cases v <;> norm_num
  · intro k
    have hp : boxPullback ![-1, -2] ![1, -1] (X 1 : MvPolynomial (Fin 2) ℝ) =
        C (-2) + X 1 := by norm_num [boxPullback, map_ofNat]
    rw [hp, bernsteinCoeff_add, bernsteinCoeff_C]
    generalize h : k 1 = i
    fin_cases i <;> norm_num [X, bernsteinCoeff_monomial, Fin.prod_univ_two,
      Finsupp.single_apply, h, Nat.choose]

private noncomputable def intervalConstraints : Fin 2 → MvPolynomial (Fin 1) ℝ :=
  ![X 0 + 1, 1 - X 0]

private noncomputable def outerLower : Fin 2 → Fin 1 → ℝ := ![![-3], ![2]]
private noncomputable def outerUpper : Fin 2 → Fin 1 → ℝ := ![![-2], ![3]]

private theorem outer_disjoint (i : Fin 2) :
    Disjoint (Set.Icc (outerLower i) (outerUpper i))
      (basicClosedSet Finset.univ (∅ : Finset Unit) intervalConstraints (fun _ => 0)) := by
  -- The left box violates x+1≥0, while the right one violates 1-x≥0.
  apply disjoint_Icc_basicClosedSet_of_bernsteinCoeff_neg
    (i := i) (n := fun _ => 1) (by simp)
  · intro v
    fin_cases i
    · exact (degreeOf_add_le _ _ _).trans (by fin_cases v; simp)
    · exact (degreeOf_sub_le _ _ _).trans (by fin_cases v; simp)
  · intro v; fin_cases i <;> fin_cases v <;> norm_num [outerLower, outerUpper]
  · intro k
    have hp : boxPullback (outerLower i) (outerUpper i) (intervalConstraints i) =
        ![C (-2) + X 0, C (-1) - X 0] i := by
      fin_cases i <;> norm_num [boxPullback, intervalConstraints, outerLower, outerUpper,
        map_ofNat] <;> ring
    rw [hp]
    generalize hk : k 0 = j
    fin_cases i <;> fin_cases j <;>
      norm_num [sub_eq_add_neg, bernsteinCoeff_add, bernsteinCoeff_neg,
        bernsteinCoeff_C, bernstein_one,
        X, bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply, hk, Nat.choose]

-- A finite cover can use a different obstruction on each component. This is
-- a union of boxes, not the interval hull, which contains feasible points.
example : Disjoint (⋃ i ∈ (Finset.univ : Finset (Fin 2)),
      Set.Icc (outerLower i) (outerUpper i))
    (basicClosedSet Finset.univ (∅ : Finset Unit) intervalConstraints (fun _ => 0)) :=
  Set.disjoint_iUnion₂_left.mpr (fun i _ => outer_disjoint i)

example : TauCeti.IsSemialgebraic (⋃ i ∈ (Finset.univ : Finset (Fin 2)),
    Set.Icc (outerLower i) (outerUpper i)) :=
  TauCeti.IsSemialgebraic.biUnion Finset.univ.finite_toSet
    (fun _ _ => TauCeti.isSemialgebraic_Icc _ _)

-- An independently supplied target cover transfers disjointness in the
-- correct direction. Here the cover is proved for two actual points.
example : Disjoint ({![-3], ![3]} : Set (Fin 1 → ℝ))
    (basicClosedSet Finset.univ (∅ : Finset Unit) intervalConstraints (fun _ => 0)) := by
  have hc : ({![-3], ![3]} : Set (Fin 1 → ℝ)) ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin 2)), Set.Icc (outerLower i) (outerUpper i) := by
    intro x hx
    rcases hx with rfl | hx
    · apply Set.mem_iUnion₂.mpr ⟨0, Finset.mem_univ _, ?_⟩
      constructor <;> intro v <;> fin_cases v <;> norm_num [outerLower, outerUpper]
    · have hx' : x = ![3] := Set.mem_singleton_iff.mp hx
      subst x
      apply Set.mem_iUnion₂.mpr ⟨1, Finset.mem_univ _, ?_⟩
      constructor <;> intro v <;> fin_cases v <;> norm_num [outerLower, outerUpper]
  exact (Set.disjoint_iUnion₂_left.mpr (fun i _ => outer_disjoint i)).mono_left hc

-- Generic finite-union containment composes with the new API directly.
example {τ σ ι κ : Type*} [Fintype σ] (K : Finset τ)
    {a b : τ → σ → ℝ} {I : Finset ι} {J : Finset κ}
    {g : ι → MvPolynomial σ ℝ} {h : κ → MvPolynomial σ ℝ}
    {ng : τ → ι → σ → ℕ} {nh : τ → κ → σ → ℕ}
    (hab : ∀ t ∈ K, a t ≤ b t)
    (hg : ∀ t ∈ K, ∀ i ∈ I, ∀ v, (g i).degreeOf v ≤ ng t i v)
    (hh : ∀ t ∈ K, ∀ j ∈ J, ∀ v, (h j).degreeOf v ≤ nh t j v)
    (cg : ∀ t ∈ K, ∀ i ∈ I, ∀ k : (v : σ) → Fin (ng t i v + 1),
      0 ≤ bernsteinCoeff (ng t i) (boxPullback (a t) (b t) (g i)) (fun v => k v))
    (ch : ∀ t ∈ K, ∀ j ∈ J, ∀ k : (v : σ) → Fin (nh t j v + 1),
      bernsteinCoeff (nh t j) (boxPullback (a t) (b t) (h j)) (fun v => k v) = 0) :
    (⋃ t ∈ K, Set.Icc (a t) (b t)) ⊆ basicClosedSet I J g h :=
  Set.iUnion₂_subset fun t ht =>
    Icc_subset_basicClosedSet_of_bernsteinCoeff (hab t ht) (hg t ht) (hh t ht)
      (cg t ht) (ch t ht)

-- Empty variables still give an inhabited one-point box and one coefficient.
example (a b : Empty → ℝ) : Set.Icc a b ⊆
    basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit)
      (fun _ => C 2) (fun _ => 0) := by
  apply Icc_subset_basicClosedSet_of_bernsteinCoeff
    (ng := fun _ _ => 0) (nh := fun _ _ => 0)
  · intro v; exact v.elim
  · intro i hi v; exact v.elim
  · simp
  · intro i hi k; norm_num [boxPullback, bernsteinCoeff_C]
  · simp

example (a b : Empty → ℝ) : (Set.Icc a b).Nonempty :=
  ⟨a, (fun v => v.elim), (fun v => v.elim)⟩

-- With no constraints the criterion is vacuous, including zero degrees.
example {σ : Type*} [Fintype σ] {a b : σ → ℝ} (hab : a ≤ b) :
    Set.Icc a b ⊆ basicClosedSet (∅ : Finset Unit) (∅ : Finset Unit)
      (fun _ => 0) (fun _ => 0) := by
  apply Icc_subset_basicClosedSet_of_bernsteinCoeff (ng := fun _ _ => 0)
    (nh := fun _ _ => 0) hab <;> simp

-- A crossing box has both signs among its coefficients and contains both
-- feasible and infeasible points; these sufficient criteria are not classifiers.
example : bernsteinCoeff (fun _ : Fin 1 => 1)
    (boxPullback ![-1] ![1] (X 0)) (fun _ => 0) = -1 ∧
    bernsteinCoeff (fun _ : Fin 1 => 1)
    (boxPullback ![-1] ![1] (X 0)) (fun _ => 1) = 1 := by
  have hp : boxPullback ![-1] ![1] (X 0 : MvPolynomial (Fin 1) ℝ) =
      C (-1) + (2 : ℝ) • X 0 := by norm_num [boxPullback, smul_eq_C_mul, map_ofNat]
  rw [hp]
  norm_num [bernsteinCoeff_add, bernsteinCoeff_C, bernsteinCoeff_smul, bernstein_one, X,
    bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply, Nat.choose]

example : (![1] : Fin 1 → ℝ) ∈ Set.Icc ![-1] ![1] ∧
    ![1] ∈ basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit)
      (fun _ => X 0) (fun _ => 0) ∧
    (![-1] : Fin 1 → ℝ) ∈ Set.Icc ![-1] ![1] ∧
    ![-1] ∉ basicClosedSet ({()} : Finset Unit) (∅ : Finset Unit)
      (fun _ => X 0) (fun _ => 0) := by
  norm_num [Set.mem_Icc, Pi.le_def, Fin.forall_fin_one, basicClosedSet]

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Mark Sepanski
-/
module

public import MathlibExt.Combinatorics.SymmetricFunctionsYoungTableaux
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathlibExtTest.Combinatorics.SymmetricFunctionsYoungTableaux

open MetaMathlibExt

-- Combinatorics 490: Omega Involution


theorem MvPolynomial.omegaAlgHom_esymm_two :
    (MvPolynomial.omegaAlgHom (Fin 2) ℤ
        ⟨MvPolynomial.esymm (Fin 2) ℤ 2,
          MvPolynomial.esymm_isSymmetric _ _ _⟩ :
        MvPolynomial (Fin 2) ℤ) =
      MvPolynomial.hsymm (Fin 2) ℤ 2 := by
  have h := MvPolynomial.esymmAlgEquiv_symm_apply (σ := Fin 2) ℤ
    (show Fintype.card (Fin 2) = 2 from rfl) 1
  rw [MvPolynomial.omegaAlgHom, AlgHom.comp_apply,
    AlgEquiv.coe_algHom]
  erw [h, MvPolynomial.aeval_X]
  rfl

-- Combinatorics 494: Exponential Specialization


theorem MvPowerSeries.exponentialSpecialization_values :
    (MvPowerSeries.X 0 :
        MvPowerSeries ℕ ℚ).exponentialSpecialization =
      PowerSeries.X ∧
      (MvPowerSeries.X 0 ^ 2 :
        MvPowerSeries ℕ ℚ).exponentialSpecialization = 0 ∧
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries ℕ ℚ).exponentialSpecialization =
        PowerSeries.C (1 / 2) * PowerSeries.X ^ 2 := by
  have key : ∀ m j : ℕ,
      (∑ i ∈ Finset.range m, Finsupp.single i 1 : ℕ →₀ ℕ) j =
        if j < m then 1 else 0 := by
    intro m j
    simp [Finset.sum_apply', Finsupp.single_apply]
  have e1 : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, Finsupp.single i 1 : ℕ →₀ ℕ) =
        Finsupp.single 0 1 ↔ m = 1 := fun m =>
    ⟨fun h => by
      have h0 := congrArg (fun g : ℕ →₀ ℕ => g 0) h
      have h1 := congrArg (fun g : ℕ →₀ ℕ => g 1) h
      simp [key] at h0 h1
      omega, by rintro rfl; simp⟩
  have e2 : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, Finsupp.single i 1 : ℕ →₀ ℕ) ≠
        Finsupp.single 0 2 := by
    intro m h
    have h0 := congrArg (fun g : ℕ →₀ ℕ => g 0) h
    simp [key] at h0
    split_ifs at h0
    omega
  have e3 : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, Finsupp.single i 1 : ℕ →₀ ℕ) =
        Finsupp.single 0 1 + Finsupp.single 1 1 ↔ m = 2 :=
    fun m => ⟨fun h => by
      have h1 := congrArg (fun g : ℕ →₀ ℕ => g 1) h
      have h2 := congrArg (fun g : ℕ →₀ ℕ => g 2) h
      simp [key] at h1 h2
      omega, by rintro rfl; simp [Finset.sum_range_succ]⟩
  refine ⟨?a, ?b, ?c⟩ <;> ext m <;>
    simp only [MvPowerSeries.exponentialSpecialization,
      PowerSeries.coeff_mk]
  case a =>
    simp only [MvPowerSeries.coeff_X, PowerSeries.coeff_X, e1]
    split_ifs with h <;> simp [h]
  case b =>
    rw [MvPowerSeries.coeff_X_pow, if_neg (e2 m)]
    simp
  case c =>
    simp only [MvPowerSeries.X,
      MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial,
      PowerSeries.coeff_C_mul_X_pow, e3]
    split_ifs with h <;> simp [h]

-- Combinatorics 495: Scalar Product of Symmetric Polynomials


theorem symmetricScalarProduct_values :
    let p₁ : MvPolynomial.symmetricSubalgebra (Fin 2) ℤ :=
      ⟨MvPolynomial.psum (Fin 2) ℤ 1,
        (MvPolynomial.mem_symmetricSubalgebra _).2
          (MvPolynomial.psum_isSymmetric _ _ _)⟩
    let p₂ : MvPolynomial.symmetricSubalgebra (Fin 2) ℤ :=
      ⟨MvPolynomial.psum (Fin 2) ℤ 2,
        (MvPolynomial.mem_symmetricSubalgebra _).2
          (MvPolynomial.psum_isSymmetric _ _ _)⟩
    symmetricScalarProduct p₁ p₁ = 1 ∧
      symmetricScalarProduct (p₁ * p₁ - p₂) (p₁ * p₁ - p₂) = 4 ∧
      symmetricScalarProduct p₁ (p₁ * p₁ - p₂) = 0 := by
  intro p₁ p₂
  open _root_.MvPolynomial _root_.MathlibExtTest.Combinatorics.SymmetricFunctionsYoungTableaux.MvPolynomial in
  have ha : (∏ i : Fin 2, ∏ j ∈ Finset.Ioi i, (X i - X j) :
      MvPolynomial (Fin 2) ℤ) = X 0 - X 1 := by
    rw [Fin.prod_univ_two,
      show Finset.Ioi (0 : Fin 2) = {1} by decide,
      show Finset.Ioi (1 : Fin 2) = ∅ by decide]
    simp
  open _root_.MvPolynomial _root_.MathlibExtTest.Combinatorics.SymmetricFunctionsYoungTableaux.MvPolynomial in
  have hP : (X 0 - X 1) * ((p₁ : MvPolynomial (Fin 2) ℤ)) =
      X 0 ^ 2 - X 1 ^ 2 := by
    simp only [p₁, psum, Fin.sum_univ_two, pow_one]
    ring
  open _root_.MvPolynomial _root_.MathlibExtTest.Combinatorics.SymmetricFunctionsYoungTableaux.MvPolynomial Finsupp in
  have hQ : (X 0 - X 1) *
      ((p₁ * p₁ - p₂ : symmetricSubalgebra (Fin 2) ℤ) :
        MvPolynomial (Fin 2) ℤ) =
      monomial (single 0 2 + single 1 1) 2 -
        monomial (single 0 1 + single 1 2) 2 := by
    have e1 : (2 * (X 0 ^ 2 * X 1) : MvPolynomial (Fin 2) ℤ) =
        monomial (single 0 2 + single 1 1) 2 := by
      rw [show (2 : MvPolynomial (Fin 2) ℤ) = C 2 from rfl,
        X_pow_eq_monomial, X, monomial_mul, C_mul_monomial]
      simp
    have e2 : (2 * (X 0 * X 1 ^ 2) : MvPolynomial (Fin 2) ℤ) =
        monomial (single 0 1 + single 1 2) 2 := by
      rw [show (2 : MvPolynomial (Fin 2) ℤ) = C 2 from rfl,
        X_pow_eq_monomial, X, monomial_mul, C_mul_monomial]
      simp
    rw [← e1, ← e2]
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, p₁, p₂,
      psum, Fin.sum_univ_two, pow_one]
    ring
  open Finsupp in
  have s20 : (single (1 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠
      single 0 2 := by
    intro h
    have := congrArg (fun g : Fin 2 →₀ ℕ => g 0) h
    simp at this
  open Finsupp in
  have e12 : (single (0 : Fin 2) 1 + single 1 2 : Fin 2 →₀ ℕ) ≠
      single 0 2 + single 1 1 := by
    intro h
    have := congrArg (fun g : Fin 2 →₀ ℕ => g 0) h
    simp at this
  open Finsupp in
  have bad : ∀ b : Fin 2 →₀ ℕ,
      (∀ i j : Fin 2, i < j → b j < b i) →
      single (1 : Fin 2) 2 ≠ b ∧
        single (0 : Fin 2) 1 + single 1 2 ≠ b := by
    intro b hb
    constructor <;> rintro rfl <;>
      · have := hb 0 1 (by decide)
        simp at this
  unfold symmetricScalarProduct
  simp only [ha, hP, hQ]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single (Finsupp.single 0 2)]
    · simp [MvPolynomial.coeff_X_pow, s20]
    · intro b hb hne
      rw [Finset.mem_filter] at hb
      simp [MvPolynomial.coeff_X_pow, Ne.symm hne,
        (bad b hb.2).1]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
      refine ⟨by simp [MvPolynomial.coeff_X_pow, s20], ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · rw [Finset.sum_eq_single
      (Finsupp.single 0 2 + Finsupp.single 1 1)]
    · simp [MvPolynomial.coeff_monomial, e12]
    · intro b hb hne
      rw [Finset.mem_filter] at hb
      simp [MvPolynomial.coeff_monomial, Ne.symm hne,
        (bad b hb.2).2]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
      refine ⟨by simp [MvPolynomial.coeff_monomial, e12], ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_filter] at hb
    by_cases hb0 : b = Finsupp.single 0 2
    · subst hb0
      open Finsupp in
      have h1 : single (0 : Fin 2) 2 + single 1 1 ≠
          single 0 2 := by
        intro h
        have := congrArg (fun g : Fin 2 →₀ ℕ => g 1) h
        simp at this
      open Finsupp in
      have h2 : single (0 : Fin 2) 1 + single 1 2 ≠
          single 0 2 := by
        intro h
        have := congrArg (fun g : Fin 2 →₀ ℕ => g 0) h
        simp at this
      simp [MvPolynomial.coeff_monomial, h1, h2]
    · simp [MvPolynomial.coeff_X_pow, Ne.symm hb0,
        (bad b hb.2).1]

-- Combinatorics 497: Skew Shape


theorem SkewShape.exists_examples :
    (∃ s : SkewShape,
      s.outer = YoungDiagram.ofRowLens [6, 5, 3, 3] (by decide) ∧
        s.inner = YoungDiagram.ofRowLens [3, 1] (by decide)) ∧
    (¬ ∃ s : SkewShape,
      s.outer = YoungDiagram.ofRowLens [2, 1] (by decide) ∧
        s.inner = YoungDiagram.ofRowLens [3] (by decide)) ∧
    (∃ s : SkewShape,
      s.outer = YoungDiagram.ofRowLens [2, 1] (by decide) ∧
        s.inner = ⊥) ∧
    (∃ s t : SkewShape,
      s.outer = YoungDiagram.ofRowLens [2, 1] (by decide) ∧
        s.inner = YoungDiagram.ofRowLens [2, 1] (by decide) ∧
        t.outer = ⊥ ∧ t.inner = ⊥ ∧ s ≠ t ∧
        s.outer.cells \ s.inner.cells =
          t.outer.cells \ t.inner.cells) := by
  refine ⟨⟨⟨_, _, ?_⟩, rfl, rfl⟩, ?_,
    ⟨⟨_, ⊥, bot_le⟩, rfl, rfl⟩,
    ⟨⟨_, _, le_rfl⟩, ⟨⊥, ⊥, le_rfl⟩, rfl, rfl, rfl, rfl,
      fun h => absurd (congrArg (fun s => s.outer.cells) h)
        (by decide), by simp⟩⟩
  · rw [← YoungDiagram.cells_subset_iff]
    decide
  · rintro ⟨⟨o, i, h⟩, rfl, rfl⟩
    exact absurd (SetLike.le_def.mp h
      (by decide : ((0, 2) : ℕ × ℕ) ∈
        YoungDiagram.ofRowLens [3] _)) (by decide)

-- Combinatorics 498: Semistandard Young Tableau of Skew Shape


theorem skewSemistandardYoungTableau_example :
    (∃ s : SkewShape,
      s.outer = YoungDiagram.ofRowLens [6, 5, 3, 3] (by decide) ∧
      s.inner = YoungDiagram.ofRowLens [3, 1] (by decide) ∧
      (∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[0, 0, 0, 3, 4, 4],
          [0, 1, 4, 7, 7], [2, 2, 6],
          [3, 8, 8]].getD i []).getD j 0) ∧
      (¬ ∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[0, 0, 0, 3, 4, 4],
          [0, 0, 4, 7, 7], [2, 2, 6],
          [3, 8, 8]].getD i []).getD j 0) ∧
      (¬ ∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[0, 0, 0, 4, 3, 4],
          [0, 1, 4, 7, 7], [2, 2, 6],
          [3, 8, 8]].getD i []).getD j 0) ∧
      (¬ ∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[0, 0, 0, 3, 4, 4],
          [0, 1, 4, 7, 7], [2, 2, 6],
          [2, 8, 8]].getD i []).getD j 0) ∧
      (¬ ∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[1, 0, 0, 3, 4, 4],
          [0, 1, 4, 7, 7], [2, 2, 6],
          [3, 8, 8]].getD i []).getD j 0) ∧
      (¬ ∃ T : SkewSemistandardYoungTableau s,
        T.entry = fun i j => ([[0, 0, 0, 3, 4, 4, 5],
          [0, 1, 4, 7, 7], [2, 2, 6],
          [3, 8, 8]].getD i []).getD j 0)) ∧
    (∃ s : SkewShape, s.outer = ⊥ ∧ s.inner = ⊥ ∧
      ∃ T : SkewSemistandardYoungTableau s,
        ∀ T' : SkewSemistandardYoungTableau s, T' = T) := by
  refine ⟨⟨⟨YoungDiagram.ofRowLens [6, 5, 3, 3] (by decide),
    YoungDiagram.ofRowLens [3, 1] (by decide), ?_⟩, rfl, rfl,
    ⟨⟨_, ?_, ?_, ?_, ?_⟩, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨⊥, ⊥, le_rfl⟩, rfl, rfl,
    ⟨fun _ _ => 0, fun h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ => rfl⟩, ?_⟩
  · rw [← YoungDiagram.cells_subset_iff]
    decide
  · intro i j h1 h2
    simp only [YoungDiagram.mem_ofRowLens] at h1 h2
    obtain ⟨hi, hj⟩ := h1
    simp at hi
    interval_cases i <;> simp at hj h2 ⊢ <;> interval_cases j <;>
      simp_all
  · intro i j1 j2 hlt h1 h2 h3 h4
    simp only [YoungDiagram.mem_ofRowLens] at h1 h2 h3 h4
    obtain ⟨hi, hj1⟩ := h1
    obtain ⟨hi', hj2⟩ := h3
    simp at hi
    interval_cases i <;> simp at hj1 hj2 h2 h4 ⊢ <;>
      interval_cases j2 <;> interval_cases j1 <;> simp_all
  · intro i1 i2 j hlt h1 h2 h3 h4
    simp only [YoungDiagram.mem_ofRowLens] at h1 h2 h3 h4
    obtain ⟨hi1, hj1⟩ := h1
    obtain ⟨hi2, hj2⟩ := h3
    simp at hi1 hi2
    interval_cases i2 <;> interval_cases i1 <;>
      simp at hj1 hj2 h2 h4 ⊢ <;> interval_cases j <;> simp_all
  · intro i j h
    have hL : ∀ L : List (List ℕ), L.length ≤ i →
        (L.getD i []).getD j 0 = 0 := fun L hL => by
      rw [List.getD_eq_default _ _ hL]
      rfl
    rcases Nat.lt_or_ge i 4 with hi | hi
    · rcases Nat.lt_or_ge j 6 with hj | hj
      · interval_cases i <;> interval_cases j <;>
          first | rfl | exact (h ⟨by decide, by decide⟩).elim
      · interval_cases i <;>
          exact List.getD_eq_default _ _ (by simp; omega)
    · exact hL _ (by simp; omega)
  · rintro ⟨T, hT⟩
    have h := T.pos (i := 1) (j := 1) (by decide) (by decide)
    rw [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.row_weak (i := 0) (j1 := 3) (j2 := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.col_strict (i1 := 2) (i2 := 3) (j := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.zeros (i := 0) (j := 0) (by decide)
    rw [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.zeros (i := 0) (j := 6) (by decide)
    rw [hT] at h
    exact absurd h (by decide)
  · rintro ⟨e, p, r, c, z⟩
    simp only [SkewSemistandardYoungTableau.mk.injEq]
    funext i j
    exact z (by simp)

-- Combinatorics 500: Standard Young Tableau of Skew Shape


theorem skewStandardYoungTableau_examples :
    let A : SkewShape → List (List ℕ) → Prop := fun s L =>
      ∃ T : SkewStandardYoungTableau s,
        ∀ i j, T.entry i j = (L.getD i []).getD j 0
    let s : SkewShape :=
      ⟨YoungDiagram.ofRowLens [3, 2] (by decide),
        YoungDiagram.ofRowLens [1] (by decide), by
          rw [← YoungDiagram.cells_subset_iff]; decide⟩
    let t : SkewShape :=
      ⟨YoungDiagram.ofRowLens [2, 1] (by decide), ⊥, bot_le⟩
    A s [[0, 1, 3], [2, 4]] ∧ ¬ A s [[0, 1, 2], [2, 3]] ∧
      ¬ A s [[0, 1, 1], [2, 3]] ∧ ¬ A s [[0, 1, 3], [2, 5]] ∧
      ¬ A s [[0, 3, 1], [2, 4]] ∧ ¬ A s [[0, 3, 4], [1, 2]] ∧
      ¬ A s [[5, 1, 3], [2, 4]] ∧
      ¬ A s [[0, 1, 3], [2, 4], [6]] ∧
      A t [[1, 2], [3]] ∧ A t [[1, 3], [2]] ∧
      ∃ T : SkewStandardYoungTableau ⟨⊥, ⊥, le_rfl⟩,
        ∀ T', T' = T := by
  intro A s t
  have key : ∀ (r : SkewShape) (L : List (List ℕ)),
      (∀ c ∈ r.outer.cells \ r.inner.cells,
        (L.getD c.1 []).getD c.2 0 ∈
          Finset.Icc 1 (r.outer.cells \ r.inner.cells).card) →
      (∀ c ∈ r.outer.cells \ r.inner.cells,
        ∀ d ∈ r.outer.cells \ r.inner.cells,
          (L.getD c.1 []).getD c.2 0 =
            (L.getD d.1 []).getD d.2 0 → c = d) →
      (∀ k ∈ Finset.Icc 1 (r.outer.cells \ r.inner.cells).card,
        ∃ c ∈ r.outer.cells \ r.inner.cells,
          (L.getD c.1 []).getD c.2 0 = k) →
      (∀ c ∈ r.outer.cells \ r.inner.cells,
        ∀ d ∈ r.outer.cells \ r.inner.cells, c.1 = d.1 →
          c.2 < d.2 → (L.getD c.1 []).getD c.2 0 ≤
            (L.getD d.1 []).getD d.2 0) →
      (∀ c ∈ r.outer.cells \ r.inner.cells,
        ∀ d ∈ r.outer.cells \ r.inner.cells, c.2 = d.2 →
          c.1 < d.1 → (L.getD c.1 []).getD c.2 0 <
            (L.getD d.1 []).getD d.2 0) →
      (∀ i < L.length, ∀ j < (L.getD i []).length,
        (i, j) ∉ r.outer.cells \ r.inner.cells →
          (L.getD i []).getD j 0 = 0) →
      A r L := by
    intro r L hm hi hs hr hc hz
    have mem : ∀ {i j : ℕ}, (i, j) ∈ r.outer →
        (i, j) ∉ r.inner →
        (i, j) ∈ r.outer.cells \ r.inner.cells := fun h1 h2 =>
      Finset.mem_sdiff.mpr ⟨(YoungDiagram.mem_cells _).mpr h1,
        fun h => h2 ((YoungDiagram.mem_cells _).mp h)⟩
    refine ⟨⟨⟨fun i j => (L.getD i []).getD j 0,
      ?_, ?_, ?_, ?_⟩, ?_⟩, fun _ _ => rfl⟩
    · intro i j h1 h2
      exact (Finset.mem_Icc.mp (hm _ (mem h1 h2))).1
    · intro i j1 j2 hlt a1 b1 a2 b2
      exact hr _ (mem a1 b1) _ (mem a2 b2) rfl hlt
    · intro i1 i2 j hlt a1 b1 a2 b2
      exact hc _ (mem a1 b1) _ (mem a2 b2) rfl hlt
    · intro i j h
      by_cases hil : i < L.length
      · by_cases hjl : j < (L.getD i []).length
        · refine hz i hil j hjl fun hd => h ?_
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hd
          exact ⟨(YoungDiagram.mem_cells _).mp h1,
            fun h => h2 ((YoungDiagram.mem_cells _).mpr h)⟩
        · exact List.getD_eq_default _ _ (Nat.le_of_not_lt hjl)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hil)]
        exact List.getD_nil
    · refine ⟨fun c hc => ?_, fun c hc d hd h => hi c hc d hd h,
        fun k hk => ?_⟩
      · exact Set.mem_Icc.mpr (Finset.mem_Icc.mp (hm c hc))
      · obtain ⟨c, hc, he⟩ := hs k (Finset.mem_Icc.mpr hk)
        exact ⟨c, hc, he⟩
  have ext : ∀ (r : SkewShape)
      (T T' : SkewStandardYoungTableau r),
      (∀ i j, T.entry i j = T'.entry i j) → T = T' := by
    rintro r ⟨⟨e, _, _, _, _⟩, _⟩ ⟨⟨e', _, _, _, _⟩, _⟩ h
    obtain rfl : e = e' := funext fun i => funext fun j => h i j
    rfl
  have cell : ∀ {i j : ℕ},
      (i, j) ∈ s.outer.cells \ s.inner.cells →
      (i, j) ∈ (↑(s.outer.cells \ s.inner.cells) :
        Set (ℕ × ℕ)) := fun h => h
  refine ⟨key _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    key _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    key _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), ?_⟩
  · rintro ⟨T, hT⟩
    have h := T.bijOn.injOn (cell (i := 0) (j := 2) (by decide))
      (cell (i := 1) (j := 0) (by decide))
      (by simp only [hT]; rfl)
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    obtain ⟨c, hc, he⟩ := T.bijOn.surjOn
      (show 4 ∈ Set.Icc 1
          (s.outer.cells \ s.inner.cells).card from
        Set.mem_Icc.mpr ⟨by decide, by decide⟩)
    simp only [hT] at he
    rw [Finset.mem_coe] at hc
    revert c
    decide
  · rintro ⟨T, hT⟩
    have h := T.bijOn.mapsTo (cell (i := 1) (j := 1) (by decide))
    simp only [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.row_weak (i := 0) (j1 := 1) (j2 := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.col_strict (i1 := 0) (i2 := 1) (j := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    simp only [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.zeros (i := 0) (j := 0) (by decide)
    simp only [hT] at h
    exact absurd h (by decide)
  · rintro ⟨T, hT⟩
    have h := T.zeros (i := 2) (j := 0) (by decide)
    simp only [hT] at h
    exact absurd h (by decide)
  · obtain ⟨T, hT⟩ := key ⟨⊥, ⊥, le_rfl⟩ [] (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
    exact ⟨T, fun T' => ext _ _ _ fun i j => by
      rw [hT, T'.zeros (by simp [YoungDiagram.notMem_bot])]
      simp⟩

end MathlibExtTest.Combinatorics.SymmetricFunctionsYoungTableaux

end

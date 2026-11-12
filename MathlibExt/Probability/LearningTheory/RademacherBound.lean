/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Probability.LearningTheory.Rademacher

@[expose] public section

/-! # Rademacher averages of a finite class

The empirical Rademacher average of a nonempty finite class of
Boolean functions on `m` sample points is at most
`√(2 log |H| / m)`: Massart's finite-class lemma specialized to
`±1`-valued vectors. This is the symmetrization input of roadmap
package ML-08 of the Atlas TCS canon roadmap; the generalization
theorem built on it is a follow-up. This is proved by specializing
the general Massart lemma `massart_finite_class` in
`MathlibExt/Probability/LearningTheory/Rademacher.lean` to the
`±1` embedding of `H`, not by a second MGF argument.

Source: Shalev-Shwartz and Ben-David, Understanding Machine
Learning (2014), Lemma 26.2 (Massart).
-/

open Finset

/-- The `±1` vector of a Boolean function. -/
private def signVec {m : ℕ} (h : Fin m → Bool) : Fin m → ℝ :=
  fun i => if h i then (1 : ℝ) else -1

/-- The `±1` embedding is injective. -/
private lemma signVec_injective {m : ℕ} : Function.Injective (signVec (m := m)) := by
  intro a b hab
  funext i
  have h := congrFun hab i
  by_cases ha : a i = true
  · by_cases hb : b i = true
    · rw [ha, hb]
    · exfalso
      have hb' : b i = false := by simpa using hb
      have h1 : signVec a i = 1 := by simp [signVec, ha]
      have h2 : signVec b i = -1 := by simp [signVec, hb']
      rw [h1, h2] at h
      norm_num at h
  · by_cases hb : b i = true
    · exfalso
      have ha' : a i = false := by simpa using ha
      have h1 : signVec a i = -1 := by simp [signVec, ha']
      have h2 : signVec b i = 1 := by simp [signVec, hb]
      rw [h1, h2] at h
      norm_num at h
    · have ha' : a i = false := by simpa using ha
      have hb' : b i = false := by simpa using hb
      rw [ha', hb']

/-- The supremum over the `±1` embedding of `H` is the supremum
over `H` itself. -/
private lemma sup_signVec {m : ℕ} {H : Finset (Fin m → Bool)} (hH : H.Nonempty)
    (σ : Fin m → Bool) :
    (H.image signVec).sup' (hH.image signVec)
        (fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * v i) =
      H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1)) := by
  classical
  rw [Finset.sup'_image]
  simp only [Function.comp_def, signVec]

/-- Every embedded vector has Euclidean norm `√m`, so the norm
supremum over the embedding is `√m`. -/
private lemma norm_sup_signVec {m : ℕ} {H : Finset (Fin m → Bool)} (hH : H.Nonempty) :
    (H.image signVec).sup' (hH.image signVec)
        (fun v => Real.sqrt (∑ i, v i ^ 2)) = Real.sqrt m := by
  classical
  rw [Finset.sup'_image]
  have hfun : (fun v : Fin m → ℝ => Real.sqrt (∑ i, v i ^ 2)) ∘ (signVec (m := m)) =
      fun _ : Fin m → Bool => Real.sqrt (m : ℝ) := by
    funext h
    have hsum : ∑ i, (signVec h i) ^ 2 = (m : ℝ) := by
      have h1 : ∀ i : Fin m, (signVec h i) ^ 2 = 1 := by
        intro i
        by_cases hi : h i = true <;> simp [signVec, hi]
      simp [h1]
    simp [hsum]
  rw [hfun]
  exact Finset.sup'_const _ _

/-- Finite-class Rademacher bound: for a nonempty finite class `H`
of Boolean functions on `m` sample points (each `h : Fin m → Bool`
read through its values on the sample, encoded as `±1`), the
empirical Rademacher average is at most `√(2 log |H| / m)`. -/
theorem rademacher_finite_class {m : ℕ} (hm : 0 < m)
    {H : Finset (Fin m → Bool)} (hH : H.Nonempty) :
    (∑ σ : Fin m → Bool,
      H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
        (if h i then (1 : ℝ) else -1))) / 2 ^ m / m ≤
    Real.sqrt (2 * Real.log H.card / m) := by
  classical
  have hcard : (H.image signVec).card = H.card :=
    Finset.card_image_of_injective H signVec_injective
  have hmass := massart_finite_class (S := H.image signVec) (hH.image signVec)
  rw [hcard, norm_sup_signVec hH] at hmass
  simp only [sup_signVec hH] at hmass
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlog : (0 : ℝ) ≤ Real.log H.card := by
    apply Real.log_nonneg
    exact_mod_cast Finset.card_pos.mpr hH
  have hsqrtm : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmpos)
  have hdiv : Real.sqrt (2 * Real.log H.card) * Real.sqrt (m : ℝ) / (m : ℝ) =
      Real.sqrt (2 * Real.log H.card / (m : ℝ)) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.log H.card)]
    rw [mul_div_assoc]
    have hfact : Real.sqrt (m : ℝ) / (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
      field_simp
      exact Real.sq_sqrt hmpos.le
    rw [hfact, mul_one_div]
  calc (∑ σ : Fin m → Bool,
        H.sup' hH (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ m / m
      ≤ (Real.sqrt (2 * Real.log H.card) * Real.sqrt (m : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hmass hmpos.le
    _ = Real.sqrt (2 * Real.log H.card / (m : ℝ)) := hdiv

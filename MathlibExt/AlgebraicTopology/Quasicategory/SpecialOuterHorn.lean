/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan

/-!
# Joyal's special outer horn filling: the three-dimensional case

This file is packet T18, attacking the blocker recorded in
`MathlibExt/AlgebraicTopology/Quasicategory/CoreKan.lean`: Joyal's
special outer horn filling for quasicategories in dimensions at
least `3`. The cases `n ≤ 2` are proved in `CoreKan.lean`
(`exists_fill_horn_two_zero_of_isEquivalence` and
`exists_fill_horn_two_last_of_isEquivalence`).

## What is proved here

* A simplex-level inner-horn filler for quasicategories
  (`SSet.exists_simplex_of_isCompatible`), together with explicit
  three-dimensional forms (`exists_simplex_three_missing_one` and
  `exists_simplex_three_missing_two`, kept public for
  `SpecialOuterHornGeneral.lean`) and private four-dimensional
  forms used only in this file. These are the
  `horn.IsCompatible`/`yonedaEquiv` translations of
  `horn.IsCompatible.exists_lift_of_quasicategory` of `CoreKan.lean`,
  in the form in which the Dugger–Spivak prism argument is carried
  out: a simplex is produced from its prescribed faces.
* Special outer horn filling in dimension `3`, on both sides:
  `exists_fill_horn_three_zero_of_isEquivalence` and
  `exists_fill_horn_three_last_of_isEquivalence`, packaged with
  the dimension-`2` cases of `CoreKan.lean` as
  `exists_fill_horn_left_of_isEquivalence_of_le_one` and
  `exists_fill_horn_right_of_isEquivalence_of_le_one` (special
  outer horn filling in dimensions `2` and `3` for every
  quasicategory). Given
  `σ₀ : Λ[3, 0] ⟶ X` in a quasicategory `X` whose `(0, 1)`-edge is
  an equivalence, with faces `A = (0, 2, 3)`, `B = (0, 1, 3)`,
  `C = (0, 1, 2)`, inverse edge `g = (1, 0)` and inverse triangles
  `α = (0, 1, 0)`, `β = (1, 0, 1)` from an `Edge.InvStruct`, the
  filler is built by twelve inner-horn fillings in dimensions `3`
  and `4`:
  1. round one: `W₂ = (1, 0, 1, 2)` and `W₃ = (1, 0, 1, 3)` along
     `Λ[3, 2]`, producing `τ₂ = (1, 0, 2)`, `τ₃ = (1, 0, 3)`;
  2. round two: provisional `F'₂ = (0, 1, 0, 2)`,
     `F'₃ = (0, 1, 0, 3)` along `Λ[3, 2]`, whose `d₂` faces are
     provisional `(0, 1, 2)'`, `(0, 1, 3)'` with the correct
     boundaries but not a priori equal to `C`, `B`;
  3. correction, which is the two-step argument in Joyal's slice
     `X / ∂Δ{2, 3}` written out in `X`: a `Λ[3, 2]` filler
     `H = (0, 1, 0, 1)` and `Λ[4, 2]` fillers `(0, 1, 0, 1, i)` for
     `i = 2, 3` produce homotopies `ηᵢ = (0, 1, 1, i)` from the
     provisional faces to the prescribed ones, all sharing the
     underlying homotopy `η₀ = (0, 1, 1)`; then a `Λ[3, 1]` filler
     `K = (0, 1, 1, 0)` and `Λ[4, 1]` fillers `(0, 1, 1, 0, i)`
     produce corrected `F₂ = (0, 1, 0, 2)`, `F₃ = (0, 1, 0, 3)`
     with `d₂ F₂ = C`, `d₂ F₃ = B`, sharing a common last face
     `α' = (0, 1, 0)`;
  4. `τ = (1, 0, 2, 3)` along `Λ[3, 1]`, and the final
     `Λ[4, 2]` horn on vertices `(0, 1, 0', 2, 3)` with faces
     `τ`, the degenerate `(0, 0, 2, 3)`, `F₃`, `F₂`; the `d₂`
     face of its filler is the desired `3`-simplex.

## Not proved in this file

* Dimensions `n ≥ 4` are not proved in this file; they are proved
  in
  `MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
  (packet T21), which carries out the subset induction of Dugger's
  filtration in all dimensions and proves
  `SSet.hasSpecialOuterHornFilling_of_quasicategory` and hence
  `SSet.kanComplex_core_of_quasicategory`. The argument above is
  the `n = 3` case of that filtration; the right-hand case
  `exists_fill_horn_three_last_of_isEquivalence` is its mirror
  image under reversing all vertex sequences.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace SSet

variable {X : SSet.{u}}

section SimplexHornFiller

-- Public: consumed by `SpecialOuterHornGeneral.lean` (the all-dimensions induction).
/-- Inner horn filling in a quasicategory, at the level of
simplices: a family of `(n + 1)`-simplices indexed by the faces
other than `i`, satisfying the usual face compatibilities, is the
family of faces of an `(n + 2)`-simplex. This is
`horn.IsCompatible.exists_lift_of_quasicategory` read through
`yonedaEquiv`. -/
theorem exists_simplex_of_isCompatible [Quasicategory X]
    {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    (s : ∀ (j : Fin (n + 3)) (_ : j ≠ i), X _⦋n + 1⦌)
    (hs : ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (s j hj) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (s k hk)) :
    ∃ σ : X _⦋n + 2⦌, ∀ (j : Fin (n + 3)) (hj : j ≠ i),
      X.δ j σ = s j hj := by
  have hf : horn.IsCompatible (fun j hj ↦ yonedaEquiv.symm (s j hj)) := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm, hs j k hj hk hjk]
  obtain ⟨φ, hφ⟩ := hf.exists_lift_of_quasicategory h0 hn
  refine ⟨yonedaEquiv φ, fun j hj ↦ ?_⟩
  rw [← stdSimplex.yonedaEquiv_δ_comp, hφ j hj, Equiv.apply_symm_apply]

-- Public: consumed by `SpecialOuterHornGeneral.lean` (underlying `Λ[3, 2]` filler `H`).
/-- The `Λ[3, 2]` filler at simplex level: `2`-simplices `s₀`,
`s₁`, `s₃` satisfying the three compatibilities are the `0`-, `1`-
and `3`-faces of a `3`-simplex in a quasicategory. -/
theorem exists_simplex_three_missing_two [Quasicategory X]
    {s₀ s₁ s₃ : X _⦋2⦌}
    (h₀₁ : X.δ (0 : Fin 3) s₀ = X.δ (0 : Fin 3) s₁)
    (h₀₃ : X.δ (2 : Fin 3) s₀ = X.δ (0 : Fin 3) s₃)
    (h₁₃ : X.δ (2 : Fin 3) s₁ = X.δ (1 : Fin 3) s₃) :
    ∃ σ : X _⦋3⦌, X.δ (0 : Fin 4) σ = s₀ ∧ X.δ (1 : Fin 4) σ = s₁ ∧
      X.δ (3 : Fin 4) σ = s₃ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (2 : Fin 4)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₁, s₀, s₃] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;> simp_all)
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 1 (by decide),
    by simpa using hσ 3 (by decide)⟩

-- Public: consumed by `SpecialOuterHornGeneral.lean` (underlying `Λ[3, 1]` filler `Ks`).
/-- The `Λ[3, 1]` filler at simplex level: `2`-simplices `s₀`,
`s₂`, `s₃` satisfying the three compatibilities are the `0`-, `2`-
and `3`-faces of a `3`-simplex in a quasicategory. -/
theorem exists_simplex_three_missing_one [Quasicategory X]
    {s₀ s₂ s₃ : X _⦋2⦌}
    (h₀₂ : X.δ (1 : Fin 3) s₀ = X.δ (0 : Fin 3) s₂)
    (h₀₃ : X.δ (2 : Fin 3) s₀ = X.δ (0 : Fin 3) s₃)
    (h₂₃ : X.δ (2 : Fin 3) s₂ = X.δ (2 : Fin 3) s₃) :
    ∃ σ : X _⦋3⦌, X.δ (0 : Fin 4) σ = s₀ ∧ X.δ (2 : Fin 4) σ = s₂ ∧
      X.δ (3 : Fin 4) σ = s₃ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (1 : Fin 4)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₀, s₂, s₃] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;>
          first | (simp_all; done) | (simp_all; rfl))
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 2 (by decide),
    by simpa using hσ 3 (by decide)⟩

/-- The `Λ[4, 2]` filler at simplex level: `3`-simplices `s₀`,
`s₁`, `s₃`, `s₄` satisfying the six compatibilities are the `0`-,
`1`-, `3`- and `4`-faces of a `4`-simplex in a quasicategory. -/
private theorem exists_simplex_four_missing_two [Quasicategory X]
    {s₀ s₁ s₃ s₄ : X _⦋3⦌}
    (h₀₁ : X.δ (0 : Fin 4) s₀ = X.δ (0 : Fin 4) s₁)
    (h₀₃ : X.δ (2 : Fin 4) s₀ = X.δ (0 : Fin 4) s₃)
    (h₀₄ : X.δ (3 : Fin 4) s₀ = X.δ (0 : Fin 4) s₄)
    (h₁₃ : X.δ (2 : Fin 4) s₁ = X.δ (1 : Fin 4) s₃)
    (h₁₄ : X.δ (3 : Fin 4) s₁ = X.δ (1 : Fin 4) s₄)
    (h₃₄ : X.δ (3 : Fin 4) s₃ = X.δ (3 : Fin 4) s₄) :
    ∃ σ : X _⦋4⦌, X.δ (0 : Fin 5) σ = s₀ ∧ X.δ (1 : Fin 5) σ = s₁ ∧
      X.δ (3 : Fin 5) σ = s₃ ∧ X.δ (4 : Fin 5) σ = s₄ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (2 : Fin 5)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₁, s₀, s₃, s₄] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;>
          first | (simp_all; done) | (simp_all; rfl))
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 1 (by decide),
    by simpa using hσ 3 (by decide), by simpa using hσ 4 (by decide)⟩

/-- The `Λ[4, 1]` filler at simplex level: `3`-simplices `s₀`,
`s₂`, `s₃`, `s₄` satisfying the six compatibilities are the `0`-,
`2`-, `3`- and `4`-faces of a `4`-simplex in a quasicategory. -/
private theorem exists_simplex_four_missing_one [Quasicategory X]
    {s₀ s₂ s₃ s₄ : X _⦋3⦌}
    (h₀₂ : X.δ (1 : Fin 4) s₀ = X.δ (0 : Fin 4) s₂)
    (h₀₃ : X.δ (2 : Fin 4) s₀ = X.δ (0 : Fin 4) s₃)
    (h₀₄ : X.δ (3 : Fin 4) s₀ = X.δ (0 : Fin 4) s₄)
    (h₂₃ : X.δ (2 : Fin 4) s₂ = X.δ (2 : Fin 4) s₃)
    (h₂₄ : X.δ (3 : Fin 4) s₂ = X.δ (2 : Fin 4) s₄)
    (h₃₄ : X.δ (3 : Fin 4) s₃ = X.δ (3 : Fin 4) s₄) :
    ∃ σ : X _⦋4⦌, X.δ (0 : Fin 5) σ = s₀ ∧ X.δ (2 : Fin 5) σ = s₂ ∧
      X.δ (3 : Fin 5) σ = s₃ ∧ X.δ (4 : Fin 5) σ = s₄ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (1 : Fin 5)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₀, s₂, s₃, s₄] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;>
          first | (simp_all; done) | (simp_all; rfl))
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 2 (by decide),
    by simpa using hσ 3 (by decide), by simpa using hσ 4 (by decide)⟩

/-- The `Λ[4, 3]` filler at simplex level: `3`-simplices `s₀`,
`s₁`, `s₂`, `s₄` satisfying the six compatibilities are the `0`-,
`1`-, `2`- and `4`-faces of a `4`-simplex in a quasicategory. -/
private theorem exists_simplex_four_missing_three [Quasicategory X]
    {s₀ s₁ s₂ s₄ : X _⦋3⦌}
    (h₀₁ : X.δ (0 : Fin 4) s₀ = X.δ (0 : Fin 4) s₁)
    (h₀₂ : X.δ (1 : Fin 4) s₀ = X.δ (0 : Fin 4) s₂)
    (h₀₄ : X.δ (3 : Fin 4) s₀ = X.δ (0 : Fin 4) s₄)
    (h₁₂ : X.δ (1 : Fin 4) s₁ = X.δ (1 : Fin 4) s₂)
    (h₁₄ : X.δ (3 : Fin 4) s₁ = X.δ (1 : Fin 4) s₄)
    (h₂₄ : X.δ (3 : Fin 4) s₂ = X.δ (2 : Fin 4) s₄) :
    ∃ σ : X _⦋4⦌, X.δ (0 : Fin 5) σ = s₀ ∧ X.δ (1 : Fin 5) σ = s₁ ∧
      X.δ (2 : Fin 5) σ = s₂ ∧ X.δ (4 : Fin 5) σ = s₄ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (3 : Fin 5)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₁, s₂, s₀, s₄] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;>
          first | (simp_all; done) | (simp_all; rfl))
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 1 (by decide),
    by simpa using hσ 2 (by decide), by simpa using hσ 4 (by decide)⟩

end SimplexHornFiller

section FaceComputations

/-- The simplicial identity `δᵢδⱼ = δⱼ₋₁δᵢ` for `i < j`, at the
level of simplices. -/
private lemma δ_δ_of_lt {n : ℕ} (s : X _⦋n + 2⦌) (i : Fin (n + 2))
    (j : Fin (n + 3)) (h : Fin.castSucc i < j) :
    X.δ i (X.δ j s) = X.δ (j.pred h.ne_zero) (X.δ (Fin.castSucc i) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_δ' X h) s

/-- The simplicial identity `δᵢδⱼ₊₁ = δⱼδᵢ` for `i ≤ j`, at the
level of simplices. -/
private lemma δ_δ_of_le {n : ℕ} (s : X _⦋n + 2⦌) (i j : Fin (n + 2))
    (h : i ≤ j) :
    X.δ i (X.δ (Fin.succ j) s) = X.δ j (X.δ (Fin.castSucc i) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_δ X h) s

/-- The `0`-face of the `0`-degeneracy of a `2`-simplex. -/
private lemma δ_zero_σ_zero_two (s : X _⦋2⦌) :
    X.δ (0 : Fin 4) (X.σ (0 : Fin 3) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' X
    (show (0 : Fin 4) = Fin.castSucc (0 : Fin 3) from rfl)) s

/-- The `1`-face of the `0`-degeneracy of a `2`-simplex. -/
private lemma δ_one_σ_zero_two (s : X _⦋2⦌) :
    X.δ (1 : Fin 4) (X.σ (0 : Fin 3) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' X
    (show (1 : Fin 4) = Fin.succ (0 : Fin 3) from rfl)) s

/-- The `2`-face of the `0`-degeneracy of a `2`-simplex. -/
private lemma δ_two_σ_zero_two (s : X _⦋2⦌) :
    X.δ (2 : Fin 4) (X.σ (0 : Fin 3) s) =
      X.σ (0 : Fin 2) (X.δ (1 : Fin 3) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_gt' X
    (show Fin.succ (0 : Fin 3) < (2 : Fin 4) by decide)) s

/-- The `3`-face of the `0`-degeneracy of a `2`-simplex. -/
private lemma δ_three_σ_zero_two (s : X _⦋2⦌) :
    X.δ (3 : Fin 4) (X.σ (0 : Fin 3) s) =
      X.σ (0 : Fin 2) (X.δ (2 : Fin 3) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_gt' X
    (show Fin.succ (0 : Fin 3) < (3 : Fin 4) by decide)) s

/-- The `0`-face of the `0`-degeneracy of a `1`-simplex. -/
private lemma δ_zero_σ_zero_one (s : X _⦋1⦌) :
    X.δ (0 : Fin 3) (X.σ (0 : Fin 2) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' X
    (show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) from rfl)) s

/-- The `1`-face of the `0`-degeneracy of a `1`-simplex. -/
private lemma δ_one_σ_zero_one (s : X _⦋1⦌) :
    X.δ (1 : Fin 3) (X.σ (0 : Fin 2) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' X
    (show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl)) s

/-- The `2`-face of the `0`-degeneracy of a `1`-simplex. -/
private lemma δ_two_σ_zero_one (s : X _⦋1⦌) :
    X.δ (2 : Fin 3) (X.σ (0 : Fin 2) s) =
      X.σ (0 : Fin 1) (X.δ (1 : Fin 2) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_gt' X
    (show Fin.succ (0 : Fin 2) < (2 : Fin 3) by decide)) s

/-- The `0`-face of the `1`-degeneracy of a `1`-simplex. -/
private lemma δ_zero_σ_one_one (s : X _⦋1⦌) :
    X.δ (0 : Fin 3) (X.σ (1 : Fin 2) s) =
      X.σ (0 : Fin 1) (X.δ (0 : Fin 2) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_le X
    (show (0 : Fin 2) ≤ Fin.castSucc (0 : Fin 1) by decide)) s

/-- The `1`-face of the `1`-degeneracy of a `1`-simplex. -/
private lemma δ_one_σ_one_one (s : X _⦋1⦌) :
    X.δ (1 : Fin 3) (X.σ (1 : Fin 2) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' X
    (show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from rfl)) s

/-- The `2`-face of the `1`-degeneracy of a `1`-simplex. -/
private lemma δ_two_σ_one_one (s : X _⦋1⦌) :
    X.δ (2 : Fin 3) (X.σ (1 : Fin 2) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' X
    (show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl)) s

/-- The `0`-face of the `2`-degeneracy of a `2`-simplex. -/
private lemma δ_zero_σ_two_two (s : X _⦋2⦌) :
    X.δ (0 : Fin 4) (X.σ (2 : Fin 3) s) =
      X.σ (1 : Fin 2) (X.δ (0 : Fin 3) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_le X
    (show (0 : Fin 3) ≤ Fin.castSucc (1 : Fin 2) by decide)) s

/-- The `1`-face of the `2`-degeneracy of a `2`-simplex. -/
private lemma δ_one_σ_two_two (s : X _⦋2⦌) :
    X.δ (1 : Fin 4) (X.σ (2 : Fin 3) s) =
      X.σ (1 : Fin 2) (X.δ (1 : Fin 3) s) :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_le X
    (show (1 : Fin 3) ≤ Fin.castSucc (1 : Fin 2) by decide)) s

/-- The `2`-face of the `2`-degeneracy of a `2`-simplex. -/
private lemma δ_two_σ_two_two (s : X _⦋2⦌) :
    X.δ (2 : Fin 4) (X.σ (2 : Fin 3) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' X
    (show (2 : Fin 4) = Fin.castSucc (2 : Fin 3) from rfl)) s

/-- The `3`-face of the `2`-degeneracy of a `2`-simplex. -/
private lemma δ_three_σ_two_two (s : X _⦋2⦌) :
    X.δ (3 : Fin 4) (X.σ (2 : Fin 3) s) = s :=
  ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' X
    (show (3 : Fin 4) = Fin.succ (2 : Fin 3) from rfl)) s

end FaceComputations

section ThreeDimensionalLeft

/-- Special outer horn filling for `Λ[3, 0]` in a quasicategory: a
horn whose `(0, 1)`-edge is an equivalence extends to `Δ[3]`. The
proof is the prism argument described in the file header: rounds
one and two along `Λ[3, 2]`, the correction in the slice over
`∂Δ{2, 3}` written out as `Λ[3, 2]`/`Λ[4, 2]` and
`Λ[3, 1]`/`Λ[4, 1]` fillings sharing underlying simplices, and a
final `Λ[4, 2]` filling. -/
theorem exists_fill_horn_three_zero_of_isEquivalence [Quasicategory X]
    (σ₀ : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ X, σ₀ = Λ[3, (0 : Fin 4)].ι ≫ σ := by
  -- The three faces of the horn: `A = (0, 2, 3)`, `B = (0, 1, 3)`,
  -- `C = (0, 1, 2)`.
  set A := σ₀.app _ (horn.face (0 : Fin 4) 1 (by decide)) with hAdef
  set B := σ₀.app _ (horn.face (0 : Fin 4) 2 (by decide)) with hBdef
  set C := σ₀.app _ (horn.face (0 : Fin 4) 3 (by decide)) with hCdef
  have rel : ∀ (j k : Fin 4) (hj : j ≠ (0 : Fin 4)) (hk : k ≠ (0 : Fin 4))
      (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk))
          (σ₀.app _ (horn.face (0 : Fin 4) j hj)) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk))
          (σ₀.app _ (horn.face (0 : Fin 4) k hk)) := by
    intro j k hj hk hjk
    have hf₁ : horn.ι (0 : Fin 4) j hj ≫ σ₀ =
        yonedaEquiv.symm (σ₀.app _ (horn.face (0 : Fin 4) j hj)) := by
      rw [horn.ι, yonedaEquiv_symm_comp]
    have hf₂ : horn.ι (0 : Fin 4) k hk ≫ σ₀ =
        yonedaEquiv.symm (σ₀.app _ (horn.face (0 : Fin 4) k hk)) := by
      rw [horn.ι, yonedaEquiv_symm_comp]
    have hc := (horn.IsCompatible.of_hom σ₀).δ_pred_comp j k hj hk hjk
    rw [hf₁, hf₂, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm] at hc
    exact yonedaEquiv.symm.injective hc
  have rAB : X.δ (1 : Fin 3) A = X.δ (1 : Fin 3) B :=
    rel 1 2 (by decide) (by decide) (by decide)
  have rAC : X.δ (2 : Fin 3) A = X.δ (1 : Fin 3) C :=
    rel 1 3 (by decide) (by decide) (by decide)
  have rBC : X.δ (2 : Fin 3) B = X.δ (2 : Fin 3) C :=
    rel 2 3 (by decide) (by decide) (by decide)
  -- Edges and vertices, as faces of `A`, `B`, `C`.
  set e01 := X.δ (2 : Fin 3) C with he01def
  set e02 := X.δ (1 : Fin 3) C with he02def
  set e12 := X.δ (0 : Fin 3) C with he12def
  set e03 := X.δ (1 : Fin 3) B with he03def
  set e13 := X.δ (0 : Fin 3) B with he13def
  set x0 := X.δ (1 : Fin 2) e01 with hx0def
  set x1 := X.δ (0 : Fin 2) e01 with hx1def
  -- The `(0, 1)`-edge of the horn is `e01`; fix inverse data for it.
  have hδface : (Λ[3, (0 : Fin 4)] : SSet.{u}).δ (2 : Fin 3)
      (horn.face (0 : Fin 4) 3 (by decide)) =
      leftHornEdgeSimplex.{u} 1 := by decide
  have hed : (leftHornEdge σ₀).edge = e01 := by
    rw [leftHornEdge_edge]
    have h2 : σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet.{u}).δ (2 : Fin 3)
        (horn.face (0 : Fin 4) 3 (by decide))) =
        X.δ (2 : Fin 3) (σ₀.app _ (horn.face (0 : Fin 4) 3 (by decide))) :=
      NatTrans.naturality_apply σ₀ (SimplexCategory.δ (2 : Fin 3)).op _
    rw [hδface] at h2
    exact h2
  have h01 : (Edge.mk' e01).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (leftHornEdge σ₀).edge = (Edge.mk' e01).edge from hed)).mp h
  obtain ⟨I⟩ := h01.nonempty_invStruct
  set g := I.inv.edge with hgdef
  set α := I.homInvId.simplex with hαdef
  set β := I.invHomId.simplex with hβdef
  have α0 : X.δ (0 : Fin 3) α = g := I.homInvId.d₀
  have α1 : X.δ (1 : Fin 3) α = X.σ (0 : Fin 1) x0 := by
    rw [hαdef, I.homInvId.d₁, Edge.id_edge, hx0def]
  have α2 : X.δ (2 : Fin 3) α = e01 := I.homInvId.d₂
  have β0 : X.δ (0 : Fin 3) β = e01 := I.invHomId.d₀
  have β1 : X.δ (1 : Fin 3) β = X.σ (0 : Fin 1) x1 := by
    rw [hβdef, I.invHomId.d₁, Edge.id_edge, hx1def]
  have β2 : X.δ (2 : Fin 3) β = g := I.invHomId.d₂
  have gsrc : X.δ (1 : Fin 2) g = x1 := I.inv.src_eq
  -- Vertex computations: sources of the edges `e12`, `e13`, `e02`, `e03`.
  have v12 : X.δ (1 : Fin 2) e12 = x1 := by
    have hdd : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) C) =
        X.δ (0 : Fin 2) (X.δ (2 : Fin 3) C) :=
      (δ_δ_of_le C (0 : Fin 2) (1 : Fin 2) (by decide)).symm
    exact hdd
  have v13 : X.δ (1 : Fin 2) e13 = x1 := by
    have hdd : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) B) =
        X.δ (0 : Fin 2) (X.δ (2 : Fin 3) B) :=
      (δ_δ_of_le B (0 : Fin 2) (1 : Fin 2) (by decide)).symm
    rw [rBC] at hdd
    exact hdd
  have v02 : X.δ (1 : Fin 2) e02 = x0 := by
    have hdd : X.δ (1 : Fin 2) (X.δ (1 : Fin 3) C) =
        X.δ (1 : Fin 2) (X.δ (2 : Fin 3) C) :=
      (δ_δ_of_le C (1 : Fin 2) (1 : Fin 2) (by decide)).symm
    exact hdd
  have v03 : X.δ (1 : Fin 2) e03 = x0 := by
    have hdd : X.δ (1 : Fin 2) (X.δ (1 : Fin 3) B) =
        X.δ (1 : Fin 2) (X.δ (2 : Fin 3) B) :=
      (δ_δ_of_le B (1 : Fin 2) (1 : Fin 2) (by decide)).symm
    rw [rBC] at hdd
    exact hdd
  -- Round one: `W₂ = (1, 0, 1, 2)` along `Λ[3, 2]`, producing
  -- `τ₂ = (1, 0, 2)`.
  obtain ⟨W2, hW2_0, hW2_1, hW2_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := C) (s₁ := X.σ (0 : Fin 2) e12) (s₃ := β)
    (by rw [δ_zero_σ_zero_one, he12def])
    (by rw [β0, he01def])
    (by rw [δ_two_σ_zero_one, v12, β1])
  set τ2 := X.δ (2 : Fin 4) W2 with hτ2def
  have τ2_0 : X.δ (0 : Fin 3) τ2 = e02 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) W2) =
        X.δ (1 : Fin 3) (X.δ (0 : Fin 4) W2) :=
      δ_δ_of_lt W2 (0 : Fin 3) (2 : Fin 4) (by decide)
    rw [hW2_0] at hdd
    exact hdd
  have τ2_1 : X.δ (1 : Fin 3) τ2 = e12 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) W2) =
        X.δ (1 : Fin 3) (X.δ (1 : Fin 4) W2) :=
      δ_δ_of_lt W2 (1 : Fin 3) (2 : Fin 4) (by decide)
    rw [hW2_1, δ_one_σ_zero_one] at hdd
    exact hdd
  have τ2_2 : X.δ (2 : Fin 3) τ2 = g := by
    have hdd : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) W2) =
        X.δ (2 : Fin 3) (X.δ (3 : Fin 4) W2) :=
      (δ_δ_of_le W2 (2 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hW2_3, β2] at hdd
    exact hdd
  -- Round one: `W₃ = (1, 0, 1, 3)` along `Λ[3, 2]`, producing
  -- `τ₃ = (1, 0, 3)`.
  obtain ⟨W3, hW3_0, hW3_1, hW3_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := B) (s₁ := X.σ (0 : Fin 2) e13) (s₃ := β)
    (by rw [δ_zero_σ_zero_one, he13def])
    (by rw [rBC, β0])
    (by rw [δ_two_σ_zero_one, v13, β1])
  set τ3 := X.δ (2 : Fin 4) W3 with hτ3def
  have τ3_0 : X.δ (0 : Fin 3) τ3 = e03 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) W3) =
        X.δ (1 : Fin 3) (X.δ (0 : Fin 4) W3) :=
      δ_δ_of_lt W3 (0 : Fin 3) (2 : Fin 4) (by decide)
    rw [hW3_0] at hdd
    exact hdd
  have τ3_1 : X.δ (1 : Fin 3) τ3 = e13 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) W3) =
        X.δ (1 : Fin 3) (X.δ (1 : Fin 4) W3) :=
      δ_δ_of_lt W3 (1 : Fin 3) (2 : Fin 4) (by decide)
    rw [hW3_1, δ_one_σ_zero_one] at hdd
    exact hdd
  have τ3_2 : X.δ (2 : Fin 3) τ3 = g := by
    have hdd : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) W3) =
        X.δ (2 : Fin 3) (X.δ (3 : Fin 4) W3) :=
      (δ_δ_of_le W3 (2 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hW3_3, β2] at hdd
    exact hdd
  -- Round two: provisional `F'₂ = (0, 1, 0, 2)` along `Λ[3, 2]`;
  -- its `d₂` face `Cp` is a provisional `(0, 1, 2)`.
  obtain ⟨Fp2, hFp2_0, hFp2_1, hFp2_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := τ2) (s₁ := X.σ (0 : Fin 2) e02) (s₃ := α)
    (by rw [τ2_0, δ_zero_σ_zero_one])
    (by rw [τ2_2, α0])
    (by rw [δ_two_σ_zero_one, v02, α1])
  set Cp := X.δ (2 : Fin 4) Fp2 with hCpdef
  have Cp_0 : X.δ (0 : Fin 3) Cp = e12 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) Fp2) =
        X.δ (1 : Fin 3) (X.δ (0 : Fin 4) Fp2) :=
      δ_δ_of_lt Fp2 (0 : Fin 3) (2 : Fin 4) (by decide)
    rw [hFp2_0, τ2_1] at hdd
    exact hdd
  have Cp_1 : X.δ (1 : Fin 3) Cp = e02 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) Fp2) =
        X.δ (1 : Fin 3) (X.δ (1 : Fin 4) Fp2) :=
      δ_δ_of_lt Fp2 (1 : Fin 3) (2 : Fin 4) (by decide)
    rw [hFp2_1, δ_one_σ_zero_one] at hdd
    exact hdd
  have Cp_2 : X.δ (2 : Fin 3) Cp = e01 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) Fp2) =
        X.δ (2 : Fin 3) (X.δ (3 : Fin 4) Fp2) :=
      (δ_δ_of_le Fp2 (2 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hFp2_3, α2] at hdd
    exact hdd
  -- Round two: provisional `F'₃ = (0, 1, 0, 3)` along `Λ[3, 2]`;
  -- its `d₂` face `Bp` is a provisional `(0, 1, 3)`.
  obtain ⟨Fp3, hFp3_0, hFp3_1, hFp3_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := τ3) (s₁ := X.σ (0 : Fin 2) e03) (s₃ := α)
    (by rw [τ3_0, δ_zero_σ_zero_one])
    (by rw [τ3_2, α0])
    (by rw [δ_two_σ_zero_one, v03, α1])
  set Bp := X.δ (2 : Fin 4) Fp3 with hBpdef
  have Bp_0 : X.δ (0 : Fin 3) Bp = e13 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) Fp3) =
        X.δ (1 : Fin 3) (X.δ (0 : Fin 4) Fp3) :=
      δ_δ_of_lt Fp3 (0 : Fin 3) (2 : Fin 4) (by decide)
    rw [hFp3_0, τ3_1] at hdd
    exact hdd
  have Bp_1 : X.δ (1 : Fin 3) Bp = e03 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) Fp3) =
        X.δ (1 : Fin 3) (X.δ (1 : Fin 4) Fp3) :=
      δ_δ_of_lt Fp3 (1 : Fin 3) (2 : Fin 4) (by decide)
    rw [hFp3_1, δ_one_σ_zero_one] at hdd
    exact hdd
  have Bp_2 : X.δ (2 : Fin 3) Bp = e01 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) Fp3) =
        X.δ (2 : Fin 3) (X.δ (3 : Fin 4) Fp3) :=
      (δ_δ_of_le Fp3 (2 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hFp3_3, α2] at hdd
    exact hdd
  -- Correction, first step in the slice over `∂Δ{2, 3}`: the
  -- underlying `Λ[3, 2]` filler `H = (0, 1, 0, 1)`, whose missing
  -- face `η₀ = (0, 1, 1)` is a homotopy from `e01` to itself.
  obtain ⟨H, hH_0, hH_1, hH_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := β) (s₁ := X.σ (0 : Fin 2) e01) (s₃ := α)
    (by rw [β0, δ_zero_σ_zero_one])
    (by rw [β2, α0])
    (by rw [δ_two_σ_zero_one, α1, hx0def])
  set η0 := X.δ (2 : Fin 4) H with hη0def
  have η0_0 : X.δ (0 : Fin 3) η0 = X.σ (0 : Fin 1) x1 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (2 : Fin 4) H) =
        X.δ (1 : Fin 3) (X.δ (0 : Fin 4) H) :=
      δ_δ_of_lt H (0 : Fin 3) (2 : Fin 4) (by decide)
    rw [hH_0, β1] at hdd
    exact hdd
  have η0_1 : X.δ (1 : Fin 3) η0 = e01 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (2 : Fin 4) H) =
        X.δ (1 : Fin 3) (X.δ (1 : Fin 4) H) :=
      δ_δ_of_lt H (1 : Fin 3) (2 : Fin 4) (by decide)
    rw [hH_1, δ_one_σ_zero_one] at hdd
    exact hdd
  have η0_2 : X.δ (2 : Fin 3) η0 = e01 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (2 : Fin 4) H) =
        X.δ (2 : Fin 3) (X.δ (3 : Fin 4) H) :=
      (δ_δ_of_le H (2 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hH_3, α2] at hdd
    exact hdd
  -- The `Λ[4, 2]` filler `(0, 1, 0, 1, 2)`, whose missing face
  -- `η₂ = (0, 1, 1, 2)` is a homotopy from `Cp` to `C` over `η₀`.
  obtain ⟨Sη2, hSη2_0, hSη2_1, hSη2_3, hSη2_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := W2)
      (s₁ := X.σ (0 : Fin 3) C) (s₃ := Fp2) (s₄ := H)
      (by rw [hW2_0, δ_zero_σ_zero_two])
      (by rw [hFp2_0, hτ2def])
      (by rw [hW2_3, hH_0])
      (by rw [δ_two_σ_zero_two, hFp2_1, he02def])
      (by rw [δ_three_σ_zero_two, hH_1, he01def])
      (by rw [hFp2_3, hH_3])
  set η2 := X.δ (2 : Fin 5) Sη2 with hη2def
  have η2_0 : X.δ (0 : Fin 4) η2 = X.σ (0 : Fin 2) e12 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (2 : Fin 5) Sη2) =
        X.δ (1 : Fin 4) (X.δ (0 : Fin 5) Sη2) :=
      δ_δ_of_lt Sη2 (0 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη2_0, hW2_1] at hdd
    exact hdd
  have η2_1 : X.δ (1 : Fin 4) η2 = C := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Sη2) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Sη2) :=
      δ_δ_of_lt Sη2 (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη2_1, δ_one_σ_zero_two] at hdd
    exact hdd
  have η2_2 : X.δ (2 : Fin 4) η2 = Cp := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Sη2) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Sη2) :=
      (δ_δ_of_le Sη2 (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSη2_3] at hdd
    exact hdd
  have η2_3 : X.δ (3 : Fin 4) η2 = η0 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (2 : Fin 5) Sη2) =
        X.δ (2 : Fin 4) (X.δ (4 : Fin 5) Sη2) :=
      (δ_δ_of_le Sη2 (2 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSη2_4] at hdd
    exact hdd
  -- The `Λ[4, 2]` filler `(0, 1, 0, 1, 3)`, whose missing face
  -- `η₃ = (0, 1, 1, 3)` is a homotopy from `Bp` to `B` over `η₀`.
  obtain ⟨Sη3, hSη3_0, hSη3_1, hSη3_3, hSη3_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := W3)
      (s₁ := X.σ (0 : Fin 3) B) (s₃ := Fp3) (s₄ := H)
      (by rw [hW3_0, δ_zero_σ_zero_two])
      (by rw [hFp3_0, hτ3def])
      (by rw [hW3_3, hH_0])
      (by rw [δ_two_σ_zero_two, hFp3_1, he03def])
      (by rw [δ_three_σ_zero_two, rBC, hH_1, he01def])
      (by rw [hFp3_3, hH_3])
  set η3 := X.δ (2 : Fin 5) Sη3 with hη3def
  have η3_0 : X.δ (0 : Fin 4) η3 = X.σ (0 : Fin 2) e13 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (2 : Fin 5) Sη3) =
        X.δ (1 : Fin 4) (X.δ (0 : Fin 5) Sη3) :=
      δ_δ_of_lt Sη3 (0 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη3_0, hW3_1] at hdd
    exact hdd
  have η3_1 : X.δ (1 : Fin 4) η3 = B := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Sη3) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Sη3) :=
      δ_δ_of_lt Sη3 (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη3_1, δ_one_σ_zero_two] at hdd
    exact hdd
  have η3_2 : X.δ (2 : Fin 4) η3 = Bp := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Sη3) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Sη3) :=
      (δ_δ_of_le Sη3 (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSη3_3] at hdd
    exact hdd
  have η3_3 : X.δ (3 : Fin 4) η3 = η0 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (2 : Fin 5) Sη3) =
        X.δ (2 : Fin 4) (X.δ (4 : Fin 5) Sη3) :=
      (δ_δ_of_le Sη3 (2 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSη3_4] at hdd
    exact hdd
  -- Correction, second step in the slice over `∂Δ{2, 3}`: the
  -- underlying `Λ[3, 1]` filler `K = (0, 1, 1, 0)`; its missing
  -- face `α'` is a new inverse triangle `(0, 1, 0)`.
  obtain ⟨K, hK_0, hK_2, hK_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := X.σ (0 : Fin 2) g) (s₂ := α) (s₃ := η0)
    (by rw [δ_one_σ_zero_one, α0])
    (by rw [δ_two_σ_zero_one, gsrc, η0_0])
    (by rw [α2, η0_2])
  set α' := X.δ (1 : Fin 4) K with hα'def
  -- The `Λ[4, 1]` filler `(0, 1, 1, 0, 2)`, whose missing face is
  -- the corrected `F₂ = (0, 1, 0, 2)` with `d₂ F₂ = C`.
  obtain ⟨SF2, hSF2_0, hSF2_2, hSF2_3, hSF2_4⟩ :=
    exists_simplex_four_missing_one (X := X)
      (s₀ := X.σ (0 : Fin 3) τ2) (s₂ := Fp2) (s₃ := η2) (s₄ := K)
      (by rw [δ_one_σ_zero_two, hFp2_0])
      (by rw [δ_two_σ_zero_two, τ2_1, η2_0])
      (by rw [δ_three_σ_zero_two, τ2_2, hK_0])
      (by rw [η2_2, hCpdef])
      (by rw [hFp2_3, hK_2])
      (by rw [η2_3, hK_3])
  set F2 := X.δ (1 : Fin 5) SF2 with hF2def
  have F2_0 : X.δ (0 : Fin 4) F2 = τ2 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (1 : Fin 5) SF2) =
        X.δ (0 : Fin 4) (X.δ (0 : Fin 5) SF2) :=
      δ_δ_of_lt SF2 (0 : Fin 4) (1 : Fin 5) (by decide)
    rw [hSF2_0, δ_zero_σ_zero_two] at hdd
    exact hdd
  have F2_1 : X.δ (1 : Fin 4) F2 = X.σ (0 : Fin 2) e02 := by
    have hdd : X.δ (1 : Fin 4) (X.δ (1 : Fin 5) SF2) =
        X.δ (1 : Fin 4) (X.δ (2 : Fin 5) SF2) :=
      (δ_δ_of_le SF2 (1 : Fin 4) (1 : Fin 4) (by decide)).symm
    rw [hSF2_2, hFp2_1] at hdd
    exact hdd
  have F2_2 : X.δ (2 : Fin 4) F2 = C := by
    have hdd : X.δ (2 : Fin 4) (X.δ (1 : Fin 5) SF2) =
        X.δ (1 : Fin 4) (X.δ (3 : Fin 5) SF2) :=
      (δ_δ_of_le SF2 (1 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSF2_3, η2_1] at hdd
    exact hdd
  have F2_3 : X.δ (3 : Fin 4) F2 = α' := by
    have hdd : X.δ (3 : Fin 4) (X.δ (1 : Fin 5) SF2) =
        X.δ (1 : Fin 4) (X.δ (4 : Fin 5) SF2) :=
      (δ_δ_of_le SF2 (1 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSF2_4] at hdd
    exact hdd
  -- The `Λ[4, 1]` filler `(0, 1, 1, 0, 3)`, whose missing face is
  -- the corrected `F₃ = (0, 1, 0, 3)` with `d₂ F₃ = B`, sharing
  -- the last face `α'` with `F₂`.
  obtain ⟨SF3, hSF3_0, hSF3_2, hSF3_3, hSF3_4⟩ :=
    exists_simplex_four_missing_one (X := X)
      (s₀ := X.σ (0 : Fin 3) τ3) (s₂ := Fp3) (s₃ := η3) (s₄ := K)
      (by rw [δ_one_σ_zero_two, hFp3_0])
      (by rw [δ_two_σ_zero_two, τ3_1, η3_0])
      (by rw [δ_three_σ_zero_two, τ3_2, hK_0])
      (by rw [η3_2, hBpdef])
      (by rw [hFp3_3, hK_2])
      (by rw [η3_3, hK_3])
  set F3 := X.δ (1 : Fin 5) SF3 with hF3def
  have F3_0 : X.δ (0 : Fin 4) F3 = τ3 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (1 : Fin 5) SF3) =
        X.δ (0 : Fin 4) (X.δ (0 : Fin 5) SF3) :=
      δ_δ_of_lt SF3 (0 : Fin 4) (1 : Fin 5) (by decide)
    rw [hSF3_0, δ_zero_σ_zero_two] at hdd
    exact hdd
  have F3_1 : X.δ (1 : Fin 4) F3 = X.σ (0 : Fin 2) e03 := by
    have hdd : X.δ (1 : Fin 4) (X.δ (1 : Fin 5) SF3) =
        X.δ (1 : Fin 4) (X.δ (2 : Fin 5) SF3) :=
      (δ_δ_of_le SF3 (1 : Fin 4) (1 : Fin 4) (by decide)).symm
    rw [hSF3_2, hFp3_1] at hdd
    exact hdd
  have F3_2 : X.δ (2 : Fin 4) F3 = B := by
    have hdd : X.δ (2 : Fin 4) (X.δ (1 : Fin 5) SF3) =
        X.δ (1 : Fin 4) (X.δ (3 : Fin 5) SF3) :=
      (δ_δ_of_le SF3 (1 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSF3_3, η3_1] at hdd
    exact hdd
  have F3_3 : X.δ (3 : Fin 4) F3 = α' := by
    have hdd : X.δ (3 : Fin 4) (X.δ (1 : Fin 5) SF3) =
        X.δ (1 : Fin 4) (X.δ (4 : Fin 5) SF3) :=
      (δ_δ_of_le SF3 (1 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSF3_4] at hdd
    exact hdd
  -- The simplex `T = (1, 0, 2, 3)` along `Λ[3, 1]`.
  obtain ⟨T, hT_0, hT_2, hT_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := A) (s₂ := τ3) (s₃ := τ2)
    (by rw [rAB, τ3_0])
    (by rw [rAC, τ2_0])
    (by rw [τ3_2, τ2_2])
  -- The final `Λ[4, 2]` horn on vertices `(0, 1, 0', 2, 3)`, with
  -- faces `T`, the degenerate `(0, 0, 2, 3)`, `F₃`, `F₂`. Its
  -- filler's `d₂` face is the desired `3`-simplex `σs`.
  obtain ⟨Fs, hFs_0, hFs_1, hFs_3, hFs_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := T)
      (s₁ := X.σ (0 : Fin 3) A) (s₃ := F3) (s₄ := F2)
      (by rw [hT_0, δ_zero_σ_zero_two])
      (by rw [hT_2, F3_0])
      (by rw [hT_3, F2_0])
      (by rw [δ_two_σ_zero_two, rAB, F3_1])
      (by rw [δ_three_σ_zero_two, rAC, F2_1])
      (by rw [F3_3, F2_3])
  set σs := X.δ (2 : Fin 5) Fs with hσdef
  have hσ1 : X.δ (1 : Fin 4) σs = A := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Fs) :=
      δ_δ_of_lt Fs (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hFs_1, δ_one_σ_zero_two] at hdd
    exact hdd
  have hσ2 : X.δ (2 : Fin 4) σs = B := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Fs) :=
      (δ_δ_of_le Fs (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hFs_3, F3_2] at hdd
    exact hdd
  have hσ3 : X.δ (3 : Fin 4) σs = C := by
    have hdd : X.δ (3 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (2 : Fin 4) (X.δ (4 : Fin 5) Fs) :=
      (δ_δ_of_le Fs (2 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hFs_4, F2_2] at hdd
    exact hdd
  refine ⟨yonedaEquiv.symm σs, horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  fin_cases j
  · exact absurd rfl hj
  · exact congr_arg yonedaEquiv.symm hσ1.symm
  · exact congr_arg yonedaEquiv.symm hσ2.symm
  · exact congr_arg yonedaEquiv.symm hσ3.symm

end ThreeDimensionalLeft

section ThreeDimensionalRight

/-- Special outer horn filling for `Λ[3, 3]` in a quasicategory: a
horn whose `(2, 3)`-edge is an equivalence extends to `Δ[3]`. This
is the mirror image of
`exists_fill_horn_three_zero_of_isEquivalence` under reversing all
vertex sequences (`v ↦ 3 - v`): rounds one and two along
`Λ[3, 1]`, the correction in the slice over `∂Δ{0, 1}` written out
as `Λ[3, 1]`/`Λ[4, 2]` and `Λ[3, 2]`/`Λ[4, 3]` fillings sharing
underlying simplices, and a final `Λ[4, 2]` filling. -/
theorem exists_fill_horn_three_last_of_isEquivalence [Quasicategory X]
    (σ₀ : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ X, σ₀ = Λ[3, Fin.last 3].ι ≫ σ := by
  -- The three faces of the horn: `Cr = (1, 2, 3)`, `Br = (0, 2, 3)`,
  -- `Ar = (0, 1, 3)`.
  set Cr := σ₀.app _ (horn.face (Fin.last 3) 0 (by decide)) with hCrdef
  set Br := σ₀.app _ (horn.face (Fin.last 3) 1 (by decide)) with hBrdef
  set Ar := σ₀.app _ (horn.face (Fin.last 3) 2 (by decide)) with hArdef
  have rel : ∀ (j k : Fin 4) (hj : j ≠ Fin.last 3) (hk : k ≠ Fin.last 3)
      (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk))
          (σ₀.app _ (horn.face (Fin.last 3) j hj)) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk))
          (σ₀.app _ (horn.face (Fin.last 3) k hk)) := by
    intro j k hj hk hjk
    have hf₁ : horn.ι (Fin.last 3) j hj ≫ σ₀ =
        yonedaEquiv.symm (σ₀.app _ (horn.face (Fin.last 3) j hj)) := by
      rw [horn.ι, yonedaEquiv_symm_comp]
    have hf₂ : horn.ι (Fin.last 3) k hk ≫ σ₀ =
        yonedaEquiv.symm (σ₀.app _ (horn.face (Fin.last 3) k hk)) := by
      rw [horn.ι, yonedaEquiv_symm_comp]
    have hc := (horn.IsCompatible.of_hom σ₀).δ_pred_comp j k hj hk hjk
    rw [hf₁, hf₂, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm] at hc
    exact yonedaEquiv.symm.injective hc
  have rCrBr : X.δ (0 : Fin 3) Cr = X.δ (0 : Fin 3) Br :=
    rel 0 1 (by decide) (by decide) (by decide)
  have rCrAr : X.δ (1 : Fin 3) Cr = X.δ (0 : Fin 3) Ar :=
    rel 0 2 (by decide) (by decide) (by decide)
  have rBrAr : X.δ (1 : Fin 3) Br = X.δ (1 : Fin 3) Ar :=
    rel 1 2 (by decide) (by decide) (by decide)
  -- Edges and vertices, as faces of `Cr`, `Br`, `Ar`.
  set e23 := X.δ (0 : Fin 3) Cr with he23def
  set e13 := X.δ (1 : Fin 3) Cr with he13def
  set e12 := X.δ (2 : Fin 3) Cr with he12def
  set e03 := X.δ (1 : Fin 3) Ar with he03def
  set e02 := X.δ (2 : Fin 3) Br with he02def
  set x2 := X.δ (1 : Fin 2) e23 with hx2def
  set x3 := X.δ (0 : Fin 2) e23 with hx3def
  -- The `(2, 3)`-edge of the horn is `e23`; fix inverse data for it.
  have hδface : (Λ[3, Fin.last 3] : SSet.{u}).δ (0 : Fin 3)
      (horn.face (Fin.last 3) 0 (by decide)) =
      rightHornEdgeSimplex.{u} 1 := by decide
  have hed : (rightHornEdge σ₀).edge = e23 := by
    rw [rightHornEdge_edge]
    have h2 : σ₀.app _ ((Λ[3, Fin.last 3] : SSet.{u}).δ (0 : Fin 3)
        (horn.face (Fin.last 3) 0 (by decide))) =
        X.δ (0 : Fin 3) (σ₀.app _ (horn.face (Fin.last 3) 0 (by decide))) :=
      NatTrans.naturality_apply σ₀ (SimplexCategory.δ (0 : Fin 3)).op _
    rw [hδface] at h2
    exact h2
  have h23 : (Edge.mk' e23).IsEquivalence :=
    (Edge.isEquivalence_iff_of_edge_eq (show
      (rightHornEdge σ₀).edge = (Edge.mk' e23).edge from hed)).mp h
  obtain ⟨I⟩ := h23.nonempty_invStruct
  set g := I.inv.edge with hgdef
  set α := I.homInvId.simplex with hαdef
  set β := I.invHomId.simplex with hβdef
  have α0 : X.δ (0 : Fin 3) α = g := I.homInvId.d₀
  have α1 : X.δ (1 : Fin 3) α = X.σ (0 : Fin 1) x2 := by
    rw [hαdef, I.homInvId.d₁, Edge.id_edge, hx2def]
  have α2 : X.δ (2 : Fin 3) α = e23 := I.homInvId.d₂
  have β0 : X.δ (0 : Fin 3) β = e23 := I.invHomId.d₀
  have β1 : X.δ (1 : Fin 3) β = X.σ (0 : Fin 1) x3 := by
    rw [hβdef, I.invHomId.d₁, Edge.id_edge, hx3def]
  have β2 : X.δ (2 : Fin 3) β = g := I.invHomId.d₂
  have gtgt : X.δ (0 : Fin 2) g = x2 := I.inv.tgt_eq
  -- Vertex computations: targets of the edges `e12`, `e02`, `e13`, `e03`.
  have t12 : X.δ (0 : Fin 2) e12 = x2 := by
    have hdd : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) Cr) =
        X.δ (1 : Fin 2) (X.δ (0 : Fin 3) Cr) :=
      δ_δ_of_lt Cr (0 : Fin 2) (2 : Fin 3) (by decide)
    exact hdd
  have t02 : X.δ (0 : Fin 2) e02 = x2 := by
    have hdd : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) Br) =
        X.δ (1 : Fin 2) (X.δ (0 : Fin 3) Br) :=
      δ_δ_of_lt Br (0 : Fin 2) (2 : Fin 3) (by decide)
    rw [← rCrBr] at hdd
    exact hdd
  have t13 : X.δ (0 : Fin 2) e13 = x3 := by
    have hdd : X.δ (0 : Fin 2) (X.δ (1 : Fin 3) Cr) =
        X.δ (0 : Fin 2) (X.δ (0 : Fin 3) Cr) :=
      δ_δ_of_lt Cr (0 : Fin 2) (1 : Fin 3) (by decide)
    exact hdd
  have t03 : X.δ (0 : Fin 2) e03 = x3 := by
    have hdd : X.δ (0 : Fin 2) (X.δ (1 : Fin 3) Ar) =
        X.δ (0 : Fin 2) (X.δ (0 : Fin 3) Ar) :=
      δ_δ_of_lt Ar (0 : Fin 2) (1 : Fin 3) (by decide)
    rw [← rCrAr, t13] at hdd
    exact hdd
  -- Round one: `W₁ = (1, 2, 3, 2)` along `Λ[3, 1]`, producing
  -- `τ₁ = (1, 3, 2)`.
  obtain ⟨W1, hW1_0, hW1_2, hW1_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := α) (s₂ := X.σ (1 : Fin 2) e12) (s₃ := Cr)
    (by rw [α1, δ_zero_σ_one_one, t12])
    (by rw [α2, he23def])
    (by rw [δ_two_σ_one_one, he12def])
  set τ1 := X.δ (1 : Fin 4) W1 with hτ1def
  have τ1_0 : X.δ (0 : Fin 3) τ1 = g := by
    have hdd : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) W1) =
        X.δ (0 : Fin 3) (X.δ (0 : Fin 4) W1) :=
      δ_δ_of_lt W1 (0 : Fin 3) (1 : Fin 4) (by decide)
    rw [hW1_0, α0] at hdd
    exact hdd
  have τ1_1 : X.δ (1 : Fin 3) τ1 = e12 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) W1) =
        X.δ (1 : Fin 3) (X.δ (2 : Fin 4) W1) :=
      (δ_δ_of_le W1 (1 : Fin 3) (1 : Fin 3) (by decide)).symm
    rw [hW1_2, δ_one_σ_one_one] at hdd
    exact hdd
  have τ1_2 : X.δ (2 : Fin 3) τ1 = e13 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) W1) =
        X.δ (1 : Fin 3) (X.δ (3 : Fin 4) W1) :=
      (δ_δ_of_le W1 (1 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hW1_3] at hdd
    exact hdd
  -- Round one: `W₀ = (0, 2, 3, 2)` along `Λ[3, 1]`, producing
  -- `τ₀ = (0, 3, 2)`.
  obtain ⟨W0, hW0_0, hW0_2, hW0_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := α) (s₂ := X.σ (1 : Fin 2) e02) (s₃ := Br)
    (by rw [α1, δ_zero_σ_one_one, t02])
    (α2.trans rCrBr)
    (by rw [δ_two_σ_one_one, he02def])
  set τ0 := X.δ (1 : Fin 4) W0 with hτ0def
  have τ0_0 : X.δ (0 : Fin 3) τ0 = g := by
    have hdd : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) W0) =
        X.δ (0 : Fin 3) (X.δ (0 : Fin 4) W0) :=
      δ_δ_of_lt W0 (0 : Fin 3) (1 : Fin 4) (by decide)
    rw [hW0_0, α0] at hdd
    exact hdd
  have τ0_1 : X.δ (1 : Fin 3) τ0 = e02 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) W0) =
        X.δ (1 : Fin 3) (X.δ (2 : Fin 4) W0) :=
      (δ_δ_of_le W0 (1 : Fin 3) (1 : Fin 3) (by decide)).symm
    rw [hW0_2, δ_one_σ_one_one] at hdd
    exact hdd
  have τ0_2 : X.δ (2 : Fin 3) τ0 = e03 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) W0) =
        X.δ (1 : Fin 3) (X.δ (3 : Fin 4) W0) :=
      (δ_δ_of_le W0 (1 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hW0_3, rBrAr] at hdd
    exact hdd
  -- Round two: provisional `F'₁ = (1, 3, 2, 3)` along `Λ[3, 1]`;
  -- its `d₁` face `Crp` is a provisional `(1, 2, 3)`.
  obtain ⟨Fp1, hFp1_0, hFp1_2, hFp1_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := β) (s₂ := X.σ (1 : Fin 2) e13) (s₃ := τ1)
    (by rw [β1, δ_zero_σ_one_one, t13])
    (by rw [β2, τ1_0])
    (by rw [δ_two_σ_one_one, τ1_2])
  set Crp := X.δ (1 : Fin 4) Fp1 with hCrpdef
  have Crp_0 : X.δ (0 : Fin 3) Crp = e23 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) Fp1) =
        X.δ (0 : Fin 3) (X.δ (0 : Fin 4) Fp1) :=
      δ_δ_of_lt Fp1 (0 : Fin 3) (1 : Fin 4) (by decide)
    rw [hFp1_0, β0] at hdd
    exact hdd
  have Crp_1 : X.δ (1 : Fin 3) Crp = e13 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) Fp1) =
        X.δ (1 : Fin 3) (X.δ (2 : Fin 4) Fp1) :=
      (δ_δ_of_le Fp1 (1 : Fin 3) (1 : Fin 3) (by decide)).symm
    rw [hFp1_2, δ_one_σ_one_one] at hdd
    exact hdd
  have Crp_2 : X.δ (2 : Fin 3) Crp = e12 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) Fp1) =
        X.δ (1 : Fin 3) (X.δ (3 : Fin 4) Fp1) :=
      (δ_δ_of_le Fp1 (1 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hFp1_3, τ1_1] at hdd
    exact hdd
  -- Round two: provisional `F'₀ = (0, 3, 2, 3)` along `Λ[3, 1]`;
  -- its `d₁` face `Brp` is a provisional `(0, 2, 3)`.
  obtain ⟨Fp0, hFp0_0, hFp0_2, hFp0_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := β) (s₂ := X.σ (1 : Fin 2) e03) (s₃ := τ0)
    (by rw [β1, δ_zero_σ_one_one, t03])
    (by rw [β2, τ0_0])
    (by rw [δ_two_σ_one_one, τ0_2])
  set Brp := X.δ (1 : Fin 4) Fp0 with hBrpdef
  have Brp_0 : X.δ (0 : Fin 3) Brp = e23 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) Fp0) =
        X.δ (0 : Fin 3) (X.δ (0 : Fin 4) Fp0) :=
      δ_δ_of_lt Fp0 (0 : Fin 3) (1 : Fin 4) (by decide)
    rw [hFp0_0, β0] at hdd
    exact hdd
  have Brp_1 : X.δ (1 : Fin 3) Brp = e03 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) Fp0) =
        X.δ (1 : Fin 3) (X.δ (2 : Fin 4) Fp0) :=
      (δ_δ_of_le Fp0 (1 : Fin 3) (1 : Fin 3) (by decide)).symm
    rw [hFp0_2, δ_one_σ_one_one] at hdd
    exact hdd
  have Brp_2 : X.δ (2 : Fin 3) Brp = e02 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) Fp0) =
        X.δ (1 : Fin 3) (X.δ (3 : Fin 4) Fp0) :=
      (δ_δ_of_le Fp0 (1 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hFp0_3, τ0_1] at hdd
    exact hdd
  -- Correction, first step in the slice over `∂Δ{0, 1}`: the
  -- underlying `Λ[3, 1]` filler `H = (2, 3, 2, 3)`, whose missing
  -- face `η₀ = (2, 2, 3)` is a homotopy from `e23` to itself.
  obtain ⟨H, hH_0, hH_2, hH_3⟩ := exists_simplex_three_missing_one
    (X := X) (s₀ := β) (s₂ := X.σ (1 : Fin 2) e23) (s₃ := α)
    (by rw [β1, δ_zero_σ_one_one, hx3def])
    (by rw [β2, α0])
    (by rw [δ_two_σ_one_one, α2])
  set η0 := X.δ (1 : Fin 4) H with hη0def
  have η0_0 : X.δ (0 : Fin 3) η0 = e23 := by
    have hdd : X.δ (0 : Fin 3) (X.δ (1 : Fin 4) H) =
        X.δ (0 : Fin 3) (X.δ (0 : Fin 4) H) :=
      δ_δ_of_lt H (0 : Fin 3) (1 : Fin 4) (by decide)
    rw [hH_0, β0] at hdd
    exact hdd
  have η0_1 : X.δ (1 : Fin 3) η0 = e23 := by
    have hdd : X.δ (1 : Fin 3) (X.δ (1 : Fin 4) H) =
        X.δ (1 : Fin 3) (X.δ (2 : Fin 4) H) :=
      (δ_δ_of_le H (1 : Fin 3) (1 : Fin 3) (by decide)).symm
    rw [hH_2, δ_one_σ_one_one] at hdd
    exact hdd
  have η0_2 : X.δ (2 : Fin 3) η0 = X.σ (0 : Fin 1) x2 := by
    have hdd : X.δ (2 : Fin 3) (X.δ (1 : Fin 4) H) =
        X.δ (1 : Fin 3) (X.δ (3 : Fin 4) H) :=
      (δ_δ_of_le H (1 : Fin 3) (2 : Fin 3) (by decide)).symm
    rw [hH_3, α1] at hdd
    exact hdd
  -- The `Λ[4, 2]` filler `(1, 2, 3, 2, 3)`, whose missing face
  -- `η₁ = (1, 2, 2, 3)` is a homotopy from `Crp` to `Cr` over `η₀`.
  obtain ⟨Sη1, hSη1_0, hSη1_1, hSη1_3, hSη1_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := H)
      (s₁ := Fp1) (s₃ := X.σ (2 : Fin 3) Cr) (s₄ := W1)
      (by rw [hH_0, hFp1_0])
      (by rw [hH_2, δ_zero_σ_two_two, he23def])
      (by rw [hH_3, hW1_0])
      (by rw [hFp1_2, δ_one_σ_two_two, he13def])
      (by rw [hFp1_3, hτ1def])
      (by rw [δ_three_σ_two_two, hW1_3])
  set η1 := X.δ (2 : Fin 5) Sη1 with hη1def
  have η1_0 : X.δ (0 : Fin 4) η1 = η0 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (2 : Fin 5) Sη1) =
        X.δ (1 : Fin 4) (X.δ (0 : Fin 5) Sη1) :=
      δ_δ_of_lt Sη1 (0 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη1_0] at hdd
    exact hdd
  have η1_1 : X.δ (1 : Fin 4) η1 = Crp := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Sη1) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Sη1) :=
      δ_δ_of_lt Sη1 (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη1_1] at hdd
    exact hdd
  have η1_2 : X.δ (2 : Fin 4) η1 = Cr := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Sη1) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Sη1) :=
      (δ_δ_of_le Sη1 (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSη1_3, δ_two_σ_two_two] at hdd
    exact hdd
  have η1_3 : X.δ (3 : Fin 4) η1 = X.σ (1 : Fin 2) e12 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (2 : Fin 5) Sη1) =
        X.δ (2 : Fin 4) (X.δ (4 : Fin 5) Sη1) :=
      (δ_δ_of_le Sη1 (2 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSη1_4, hW1_2] at hdd
    exact hdd
  -- The `Λ[4, 2]` filler `(0, 2, 3, 2, 3)`, whose missing face
  -- `η₀B = (0, 2, 2, 3)` is a homotopy from `Brp` to `Br` over `η₀`.
  obtain ⟨Sη0, hSη0_0, hSη0_1, hSη0_3, hSη0_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := H)
      (s₁ := Fp0) (s₃ := X.σ (2 : Fin 3) Br) (s₄ := W0)
      (by rw [hH_0, hFp0_0])
      (by rw [hH_2, δ_zero_σ_two_two, ← rCrBr])
      (by rw [hH_3, hW0_0])
      (by rw [hFp0_2, δ_one_σ_two_two, rBrAr])
      (by rw [hFp0_3, hτ0def])
      (by rw [δ_three_σ_two_two, hW0_3])
  set η0B := X.δ (2 : Fin 5) Sη0 with hη0Bdef
  have η0B_0 : X.δ (0 : Fin 4) η0B = η0 := by
    have hdd : X.δ (0 : Fin 4) (X.δ (2 : Fin 5) Sη0) =
        X.δ (1 : Fin 4) (X.δ (0 : Fin 5) Sη0) :=
      δ_δ_of_lt Sη0 (0 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη0_0] at hdd
    exact hdd
  have η0B_1 : X.δ (1 : Fin 4) η0B = Brp := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Sη0) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Sη0) :=
      δ_δ_of_lt Sη0 (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hSη0_1] at hdd
    exact hdd
  have η0B_2 : X.δ (2 : Fin 4) η0B = Br := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Sη0) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Sη0) :=
      (δ_δ_of_le Sη0 (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hSη0_3, δ_two_σ_two_two] at hdd
    exact hdd
  have η0B_3 : X.δ (3 : Fin 4) η0B = X.σ (1 : Fin 2) e02 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (2 : Fin 5) Sη0) =
        X.δ (2 : Fin 4) (X.δ (4 : Fin 5) Sη0) :=
      (δ_δ_of_le Sη0 (2 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSη0_4, hW0_2] at hdd
    exact hdd
  -- Correction, second step in the slice over `∂Δ{0, 1}`: the
  -- underlying `Λ[3, 2]` filler `K = (3, 2, 2, 3)`; its missing
  -- face `β'` is a new inverse triangle `(3, 2, 3)`.
  obtain ⟨K, hK_0, hK_1, hK_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := η0) (s₁ := β) (s₃ := X.σ (1 : Fin 2) g)
    (by rw [η0_0, β0])
    (by rw [η0_2, δ_zero_σ_one_one, gtgt])
    (by rw [β2, δ_one_σ_one_one])
  set β' := X.δ (2 : Fin 4) K with hβ'def
  -- The `Λ[4, 3]` filler `(1, 3, 2, 2, 3)`, whose missing face is
  -- the corrected `F₁ = (1, 3, 2, 3)` with `d₁ F₁ = Cr`.
  obtain ⟨SF1, hSF1_0, hSF1_1, hSF1_2, hSF1_4⟩ :=
    exists_simplex_four_missing_three (X := X)
      (s₀ := K) (s₁ := η1) (s₂ := Fp1) (s₄ := X.σ (2 : Fin 3) τ1)
      (by rw [hK_0, η1_0])
      (by rw [hK_1, hFp1_0])
      (by rw [hK_3, δ_zero_σ_two_two, τ1_0])
      (by rw [η1_1, hCrpdef])
      (by rw [η1_3, δ_one_σ_two_two, τ1_1])
      (by rw [hFp1_3, δ_two_σ_two_two])
  set F1 := X.δ (3 : Fin 5) SF1 with hF1def
  have F1_0 : X.δ (0 : Fin 4) F1 = β' := by
    have hdd : X.δ (0 : Fin 4) (X.δ (3 : Fin 5) SF1) =
        X.δ (2 : Fin 4) (X.δ (0 : Fin 5) SF1) :=
      δ_δ_of_lt SF1 (0 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF1_0] at hdd
    exact hdd
  have F1_1 : X.δ (1 : Fin 4) F1 = Cr := by
    have hdd : X.δ (1 : Fin 4) (X.δ (3 : Fin 5) SF1) =
        X.δ (2 : Fin 4) (X.δ (1 : Fin 5) SF1) :=
      δ_δ_of_lt SF1 (1 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF1_1, η1_2] at hdd
    exact hdd
  have F1_2 : X.δ (2 : Fin 4) F1 = X.σ (1 : Fin 2) e13 := by
    have hdd : X.δ (2 : Fin 4) (X.δ (3 : Fin 5) SF1) =
        X.δ (2 : Fin 4) (X.δ (2 : Fin 5) SF1) :=
      δ_δ_of_lt SF1 (2 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF1_2, hFp1_2] at hdd
    exact hdd
  have F1_3 : X.δ (3 : Fin 4) F1 = τ1 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (3 : Fin 5) SF1) =
        X.δ (3 : Fin 4) (X.δ (4 : Fin 5) SF1) :=
      (δ_δ_of_le SF1 (3 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSF1_4, δ_three_σ_two_two] at hdd
    exact hdd
  -- The `Λ[4, 3]` filler `(0, 3, 2, 2, 3)`, whose missing face is
  -- the corrected `F₀ = (0, 3, 2, 3)` with `d₁ F₀ = Br`, sharing
  -- the first face `β'` with `F₁`.
  obtain ⟨SF0, hSF0_0, hSF0_1, hSF0_2, hSF0_4⟩ :=
    exists_simplex_four_missing_three (X := X)
      (s₀ := K) (s₁ := η0B) (s₂ := Fp0) (s₄ := X.σ (2 : Fin 3) τ0)
      (by rw [hK_0, η0B_0])
      (by rw [hK_1, hFp0_0])
      (by rw [hK_3, δ_zero_σ_two_two, τ0_0])
      (by rw [η0B_1, hBrpdef])
      (by rw [η0B_3, δ_one_σ_two_two, τ0_1])
      (by rw [hFp0_3, δ_two_σ_two_two])
  set F0 := X.δ (3 : Fin 5) SF0 with hF0def
  have F0_0 : X.δ (0 : Fin 4) F0 = β' := by
    have hdd : X.δ (0 : Fin 4) (X.δ (3 : Fin 5) SF0) =
        X.δ (2 : Fin 4) (X.δ (0 : Fin 5) SF0) :=
      δ_δ_of_lt SF0 (0 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF0_0] at hdd
    exact hdd
  have F0_1 : X.δ (1 : Fin 4) F0 = Br := by
    have hdd : X.δ (1 : Fin 4) (X.δ (3 : Fin 5) SF0) =
        X.δ (2 : Fin 4) (X.δ (1 : Fin 5) SF0) :=
      δ_δ_of_lt SF0 (1 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF0_1, η0B_2] at hdd
    exact hdd
  have F0_2 : X.δ (2 : Fin 4) F0 = X.σ (1 : Fin 2) e03 := by
    have hdd : X.δ (2 : Fin 4) (X.δ (3 : Fin 5) SF0) =
        X.δ (2 : Fin 4) (X.δ (2 : Fin 5) SF0) :=
      δ_δ_of_lt SF0 (2 : Fin 4) (3 : Fin 5) (by decide)
    rw [hSF0_2, hFp0_2] at hdd
    exact hdd
  have F0_3 : X.δ (3 : Fin 4) F0 = τ0 := by
    have hdd : X.δ (3 : Fin 4) (X.δ (3 : Fin 5) SF0) =
        X.δ (3 : Fin 4) (X.δ (4 : Fin 5) SF0) :=
      (δ_δ_of_le SF0 (3 : Fin 4) (3 : Fin 4) (by decide)).symm
    rw [hSF0_4, δ_three_σ_two_two] at hdd
    exact hdd
  -- The simplex `T = (0, 1, 3, 2)` along `Λ[3, 2]`.
  obtain ⟨T, hT_0, hT_1, hT_3⟩ := exists_simplex_three_missing_two
    (X := X) (s₀ := τ1) (s₁ := τ0) (s₃ := Ar)
    (by rw [τ1_0, τ0_0])
    (τ1_2.trans rCrAr)
    (by rw [τ0_2, he03def])
  -- The final `Λ[4, 2]` horn on vertices `(0, 1, 3, 2, 3)`, with
  -- faces `F₁`, `F₀`, the degenerate `(0, 1, 3, 3)`, `T`. Its
  -- filler's `d₂` face is the desired `3`-simplex `σs`.
  obtain ⟨Fs, hFs_0, hFs_1, hFs_3, hFs_4⟩ :=
    exists_simplex_four_missing_two (X := X) (s₀ := F1)
      (s₁ := F0) (s₃ := X.σ (2 : Fin 3) Ar) (s₄ := T)
      (by rw [F1_0, F0_0])
      (by rw [F1_2, δ_zero_σ_two_two, ← rCrAr])
      (by rw [F1_3, hT_0])
      (by rw [F0_2, δ_one_σ_two_two, he03def])
      (by rw [F0_3, hT_1])
      (by rw [δ_three_σ_two_two, hT_3])
  set σs := X.δ (2 : Fin 5) Fs with hσdef
  have hσ0 : X.δ (0 : Fin 4) σs = Cr := by
    have hdd : X.δ (0 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (1 : Fin 4) (X.δ (0 : Fin 5) Fs) :=
      δ_δ_of_lt Fs (0 : Fin 4) (2 : Fin 5) (by decide)
    rw [hFs_0, F1_1] at hdd
    exact hdd
  have hσ1 : X.δ (1 : Fin 4) σs = Br := by
    have hdd : X.δ (1 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (1 : Fin 4) (X.δ (1 : Fin 5) Fs) :=
      δ_δ_of_lt Fs (1 : Fin 4) (2 : Fin 5) (by decide)
    rw [hFs_1, F0_1] at hdd
    exact hdd
  have hσ2 : X.δ (2 : Fin 4) σs = Ar := by
    have hdd : X.δ (2 : Fin 4) (X.δ (2 : Fin 5) Fs) =
        X.δ (2 : Fin 4) (X.δ (3 : Fin 5) Fs) :=
      (δ_δ_of_le Fs (2 : Fin 4) (2 : Fin 4) (by decide)).symm
    rw [hFs_3, δ_two_σ_two_two] at hdd
    exact hdd
  refine ⟨yonedaEquiv.symm σs, horn.hom_ext' fun j hj ↦ ?_⟩
  rw [← Category.assoc, horn.ι_ι, horn.ι, yonedaEquiv_symm_comp,
    stdSimplex.δ_comp_yonedaEquiv_symm]
  fin_cases j
  · exact congr_arg yonedaEquiv.symm hσ0.symm
  · exact congr_arg yonedaEquiv.symm hσ1.symm
  · exact congr_arg yonedaEquiv.symm hσ2.symm
  · exact absurd rfl hj

end ThreeDimensionalRight

section UpToThree

/-- Special left outer horn filling in dimensions `2` and `3` for
every quasicategory: a horn `Λ[n + 2, 0] ⟶ X` with `n ≤ 1` whose
`(0, 1)`-edge is an equivalence extends to `Δ[n + 2]`. The case
`n = 0` is `exists_fill_horn_two_zero_of_isEquivalence` of
`CoreKan.lean`; the case `n = 1` is
`exists_fill_horn_three_zero_of_isEquivalence` above. -/
theorem exists_fill_horn_left_of_isEquivalence_of_le_one [Quasicategory X]
    {n : ℕ} (hn : n ≤ 1)
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ := by
  rcases n with _ | _ | n
  · exact exists_fill_horn_two_zero_of_isEquivalence σ₀ h
  · exact exists_fill_horn_three_zero_of_isEquivalence σ₀ h
  · omega

/-- Special right outer horn filling in dimensions `2` and `3` for
every quasicategory: a horn `Λ[n + 2, n + 2] ⟶ X` with `n ≤ 1`
whose last edge is an equivalence extends to `Δ[n + 2]`. The case
`n = 0` is `exists_fill_horn_two_last_of_isEquivalence` of
`CoreKan.lean`; the case `n = 1` is
`exists_fill_horn_three_last_of_isEquivalence` above. -/
theorem exists_fill_horn_right_of_isEquivalence_of_le_one [Quasicategory X]
    {n : ℕ} (hn : n ≤ 1)
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  rcases n with _ | _ | n
  · exact exists_fill_horn_two_last_of_isEquivalence σ₀ h
  · exact exists_fill_horn_three_last_of_isEquivalence σ₀ h
  · omega

end UpToThree

end SSet

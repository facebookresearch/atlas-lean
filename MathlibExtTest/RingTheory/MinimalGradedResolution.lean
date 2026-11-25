/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MinimalGradedResolution
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MathlibExtTest.RingTheory.MinimalGradedResolution

open MathlibExt.RingTheory.MinimalGradedResolution MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-! ### Homogeneous pieces of the polynomial ring -/

example (i : Fin n) : (X i : PolynomialRing k n) ∈ polynomialPiece (k := k) (n := n) 1 :=
  isWeightedHomogeneous_X k _ i

example (c : k) : (C c : PolynomialRing k n) ∈ polynomialPiece (k := k) (n := n) 0 :=
  isWeightedHomogeneous_C _ c

/-- The standard grading has no nonzero pieces in negative degree. -/
theorem polynomialPiece_eq_bot_of_neg {j : ℤ} (hj : j < 0) :
    polynomialPiece (k := k) (n := n) j = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun p hp ↦ ?_
  ext d
  by_contra hd
  have hw : Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) d = j := hp hd
  have : 0 ≤ Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) d := by
    rw [Finsupp.weight_apply]
    exact Finset.sum_nonneg fun i _ ↦ by simp
  omega

/-! ### The irrelevant ideal -/

example (i : Fin n) : (X i : PolynomialRing k n) ∈ irrelevant (k := k) (n := n) :=
  Ideal.subset_span ⟨i, rfl⟩

-- Boundary case: with no variables the irrelevant ideal is zero.
example : irrelevant (k := k) (n := 0) = ⊥ := by
  simp [irrelevant]

/-! ### Shifted free modules -/

-- A generator of degree `d i` multiplied by a variable lies in degree `d i + 1`.
example {b : ℕ} (d : Fin b → ℤ) (i : Fin b) (j : Fin n) :
    (Pi.single i (X j) : Fin b → PolynomialRing k n) ∈ freePiece d (d i + 1) := by
  intro l
  by_cases h : l = i
  · subst h
    simpa [polynomialPiece, mem_weightedHomogeneousSubmodule] using
      isWeightedHomogeneous_X k (fun _ : Fin n ↦ (1 : ℤ)) j
  · simp [h]

-- The basis vectors themselves lie in the degree of their shift.
example {b : ℕ} (d : Fin b → ℤ) (i : Fin b) :
    (Pi.single i 1 : Fin b → PolynomialRing k n) ∈ freePiece d (d i) := by
  intro l
  by_cases h : l = i
  · subst h
    simpa [polynomialPiece, mem_weightedHomogeneousSubmodule] using
      isWeightedHomogeneous_one k (fun _ : Fin n ↦ (1 : ℤ))
  · simp [h]

/-! ### The polynomial ring as a graded module over itself -/

/-- The polynomial ring with its standard grading, as a graded module over itself. -/
noncomputable def selfGrading : Grading (k := k) (n := n) (M := PolynomialRing k n) where
  piece := polynomialPiece
  isInternal := by
    classical
    let _ := MvPolynomial.weightedDecomposition k (fun _ : Fin n ↦ (1 : ℤ))
    exact DirectSum.Decomposition.isInternal
      (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : Fin n ↦ (1 : ℤ)))
  smul_mem _ _ _ hp _ hm := IsWeightedHomogeneous.mul hp hm
  boundedBelow := ⟨0, fun _ hj ↦ polynomialPiece_eq_bot_of_neg hj⟩

/-- The ranks of the minimal resolution `0 → S → S → 0` of `S` itself. -/
abbrev selfRanks : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

/-- The minimal resolution of the polynomial ring: a single free generator in degree `0`. -/
noncomputable def selfResolution : MinimalResolution (selfGrading (k := k) (n := n)) where
  ranks := selfRanks
  degrees _ _ := 0
  differential _ := 0
  augmentation := LinearMap.proj 0
  differential_graded _ _ _ _ := by simp
  augmentation_graded j x hx := by simpa [selfGrading] using hx 0
  augmentation_surjective s := ⟨fun _ ↦ s, rfl⟩
  exact_zero := by
    ext f
    simp only [LinearMap.range_zero, Submodule.mem_bot, LinearMap.mem_ker, LinearMap.proj_apply]
    refine ⟨fun h ↦ by simp [h], fun h ↦ funext fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]
    exact h
  exact_succ _ := Subsingleton.elim _ _
  minimal _ := by simp
  length_bound i hi := by
    cases i with
    | zero => omega
    | succ i => rfl

-- Its graded Betti table is one generator in homological degree `0` and internal degree `0`.
example : betti _ (selfResolution (k := k) (n := n)) 0 0 = 1 := by
  simp only [betti, selfResolution, Finset.filter_true]
  exact Finset.card_fin 1

example : betti _ (selfResolution (k := k) (n := n)) 0 1 = 0 := by
  simp [betti, selfResolution]

example (i : ℕ) (j : ℤ) : betti _ (selfResolution (k := k) (n := n)) (i + 1) j = 0 := by
  rw [betti, Finset.card_eq_zero]
  exact Finset.eq_empty_of_forall_notMem fun a ↦ a.elim0

-- Minimality is the containment of the differential in `𝔪 • F`; with `n = 0` it forces the
-- differential to vanish.
example (P : MinimalResolution (selfGrading (k := k) (n := 0))) (i : ℕ) :
    LinearMap.range (P.differential i) = ⊥ := by
  simpa [irrelevant] using P.minimal i

end MathlibExtTest.RingTheory.MinimalGradedResolution

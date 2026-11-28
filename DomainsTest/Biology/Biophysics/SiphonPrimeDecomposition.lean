/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.SiphonPrimeDecomposition
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Tests for minimal siphons and the monomial ideal of complexes -/

open MathlibExt.Biology.Dynamics.ComplexBalanced MvPolynomial
open WantedExt.Biology.Biophysics.SiphonPrimeDecompositionWanted

private def atom (a i : Bool) : ℕ := if i = a then 1 else 0

private def swapNetwork : ReactionNetwork Bool Bool where
  src := atom
  prod := fun r => atom (!r)

private theorem atom_hit_iff (U : Finset Bool) (a : Bool) :
    (∃ i ∈ U, 0 < atom a i) ↔ a ∈ U := by
  constructor
  · rintro ⟨i, hi, hpos⟩
    by_cases h : i = a
    · simpa only [h] using hi
    · simp [atom, h] at hpos
  · exact fun ha => ⟨a, ha, by simp [atom]⟩

-- Inspect the two reactions: a nonempty closed set must contain both species.
example (Z : Finset Bool) : IsMinimalSiphon swapNetwork Z ↔ Z = Finset.univ := by
  rw [isMinimalSiphon_iff_minimal_reaction_closed]
  simp only [swapNetwork, atom_hit_iff]
  apply minimal_iff_eq ⟨Finset.univ_nonempty, fun r _ => Finset.mem_univ r⟩
  rintro U ⟨⟨i, hi⟩, hclosed⟩
  intro j _
  cases i <;> cases j <;> first | exact hi | exact hclosed _ hi

private theorem varSet_eq_univ_of_covers (P : Ideal (MvPolynomial Bool ℚ)) [P.IsPrime]
    (hP : idealM swapNetwork ⊔ prodIdeal ≤ P) : varSet P = Finset.univ := by
  refine Finset.eq_univ_of_forall fun a => (atom_hit_iff _ _).mp ?_
  exact ((idealM_sup_prodIdeal_le_iff swapNetwork P).mp hP).2 (atom a)
    (swapNetwork.mem_complexes_iff.mpr ⟨a, Or.inl rfl⟩)

-- The coordinate prime of both variables contains the complex ideal. Every minimal prime
-- below it (and every other prime over the complex ideal) must contain both variables.
example : varSet '' (idealM swapNetwork ⊔ prodIdeal).minimalPrimes =
    {(Finset.univ : Finset Bool)} := by
  ext Z
  constructor
  · rintro ⟨P, hP, rfl⟩
    have := hP.isPrime
    exact Set.mem_singleton_iff.mpr (varSet_eq_univ_of_covers P hP.le)
  · intro hZ
    obtain rfl := Set.mem_singleton_iff.mp hZ
    let U : Finset Bool := Finset.univ
    let P : Ideal (MvPolynomial Bool ℚ) := Ideal.span (X '' (U : Set Bool))
    have : P.IsPrime := span_X_image_isPrime (U : Set Bool)
    have hvar : varSet P = U := varSet_span_X_image U
    have hP : idealM swapNetwork ⊔ prodIdeal ≤ P := by
      rw [idealM_sup_prodIdeal_le_iff, hvar]
      exact ⟨Finset.univ_nonempty, fun y hy => by
        obtain ⟨r, rfl | rfl⟩ := swapNetwork.mem_complexes_iff.mp hy
        · exact (atom_hit_iff U r).mpr (Finset.mem_univ r)
        · exact (atom_hit_iff U (!r)).mpr (Finset.mem_univ (!r))⟩
    obtain ⟨Q, hQ, _⟩ := Ideal.exists_minimalPrimes_le hP
    have := hQ.isPrime
    exact ⟨Q, hQ, varSet_eq_univ_of_covers Q hQ.le⟩

-- With no species, neither a nonempty siphon nor a minimal prime can exist.
example (N : ReactionNetwork PEmpty Unit) (Z : Finset PEmpty) : ¬ IsMinimalSiphon N Z := by
  rw [isMinimalSiphon_iff_minimal_reaction_closed]
  exact fun h => Finset.not_nonempty_empty (Finset.eq_empty_of_isEmpty Z ▸ h.prop.1)

example (N : ReactionNetwork PEmpty Unit) : (idealM N ⊔ prodIdeal).minimalPrimes = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun P hP => ?_
  have := hP.isPrime
  obtain ⟨i, _⟩ := ((idealM_sup_prodIdeal_le_iff N P).mp hP.le).1
  exact isEmptyElim i

#check @isMinimalSiphon_iff_idealM
#print axioms isMinimalSiphon_iff_idealM

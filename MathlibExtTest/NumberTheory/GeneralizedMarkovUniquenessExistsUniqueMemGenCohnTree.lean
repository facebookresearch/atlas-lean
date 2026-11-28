/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree

open MetaMathlibExt

private theorem root_triple :
    IsGenCohnTriple 0 !![(1 : ℤ), 1; 1, 2] !![3, 2; 4, 3] !![2, 1; 1, 1] 1 2 1 := by
  have h1 : IsGenMarkovNumber 0 1 := ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩
  have ht : IsGenMarkovTriple 0 1 2 1 := by norm_num [IsGenMarkovTriple]
  have h2 : IsGenMarkovNumber 0 2 := ⟨1, 1, ht⟩
  refine ⟨⟨?_, 1, rfl, h1, ?_⟩, ⟨?_, 2, rfl, h2, ?_⟩,
    ⟨?_, 1, rfl, h1, ?_⟩, ?_, rfl, rfl, rfl, ht⟩
  all_goals norm_num [Matrix.det_fin_two, Matrix.trace_fin_two, genCohnS]
  decide

example : ∃! p : ℤ × List Bool,
    genCohnTree 0 p.1 p.2 = (!![(1 : ℤ), 1; 1, 2], !![3, 2; 4, 3], !![2, 1; 1, 1]) :=
  IsGenCohnTriple.existsUnique_mem_genCohnTree root_triple (by decide) (by decide)

example (ℓ : ℤ) (w : List Bool)
    (h : genCohnTree 0 ℓ w = (!![(1 : ℤ), 1; 1, 2], !![3, 2; 4, 3], !![2, 1; 1, 1])) :
    (ℓ, w) = (1, []) := by
  obtain ⟨_, _, hu⟩ :=
    IsGenCohnTriple.existsUnique_mem_genCohnTree root_triple (by decide) (by decide)
  have hr : genCohnTree 0 1 [] =
      (!![(1 : ℤ), 1; 1, 2], !![3, 2; 4, 3], !![2, 1; 1, 1]) := by
    norm_num [genCohnTree, wideGenCohnTree, genCohnPath, genCohnStep,
      genCohnP1, genCohnQ1, genCohnS]
    decide
  exact (hu (ℓ, w) h).trans (hu (1, []) hr).symm

private def upperRightEntries
    (T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ) :
    ℤ × ℤ × ℤ :=
  (T.1 0 1, T.2.1 0 1, T.2.2 0 1)

private abbrev classicalRoot := (genCohnP1 0 1, genCohnQ1 0 1, genCohnR1 0 1)

-- The empty path retains the root. The two nonempty paths reach opposite endpoint orders.
example : genCohnPath 0 classicalRoot [] = classicalRoot := by decide

example : upperRightEntries (genCohnPath 0 classicalRoot []) = (1, 1, 1) := by decide

example : upperRightEntries (genCohnPath 0 classicalRoot [false, false]) = (1, 5, 2) := by decide

example : upperRightEntries (genCohnPath 0 classicalRoot [false, true]) = (2, 5, 1) := by decide

-- Compute the matrix and numerical moves independently on the asymmetric triple $(1,5,2)$.
private theorem left_step_calculation :
    upperRightEntries (genCohnStep 0 false (genCohnPath 0 classicalRoot [false, false])) =
      (1, 13, 5) ∧ genMarkovVieta 0 false (1, 5, 2) = (1, 13, 5) := by decide

private theorem right_step_calculation :
    upperRightEntries (genCohnStep 0 true (genCohnPath 0 classicalRoot [false, false])) =
      (5, 29, 2) ∧ genMarkovVieta 0 true (1, 5, 2) = (5, 29, 2) := by decide

-- A client needs only the numerical triple to get a matrix lift.
example : ∃ P Q R w, IsGenCohnTriple 0 P Q R 1 1 1 ∧
    (let T := genCohnPath 0 (P, Q, R) w
     IsGenCohnTriple 0 T.1 T.2.1 T.2.2 1 1 1) :=
  cohnTriple_reachable.1 1 1 1 (isGenMarkovTriple_one_one_one 0) le_rfl le_rfl

-- Lift the numerical triple, then use both Vieta directions on the certified endpoint.
example : ∃ P Q R w, IsGenCohnTriple 0 P Q R 1 1 1 ∧
    (let T := genCohnPath 0 (P, Q, R) w
     IsGenCohnTriple 0 T.1 T.2.1 T.2.2 1 5 2 ∧
       upperRightEntries (genCohnStep 0 false T) = (1, 13, 5) ∧
       upperRightEntries (genCohnStep 0 true T) = (5, 29, 2)) := by
  have hMarkov : IsGenMarkovTriple 0 1 5 2 := ⟨by decide, by decide, by decide, by decide⟩
  obtain ⟨P, Q, R, w, hRoot, hLift⟩ := cohnTriple_reachable.1 1 5 2 hMarkov (by decide) (by decide)
  let T := genCohnPath 0 (P, Q, R) w
  have hEntries (d : Bool) :
      upperRightEntries (genCohnStep 0 d T) =
        (↑(genMarkovVieta 0 d (1, 5, 2)).1, ↑(genMarkovVieta 0 d (1, 5, 2)).2.1,
          ↑(genMarkovVieta 0 d (1, 5, 2)).2.2) := by
    obtain ⟨h₁, h₂, h₃⟩ := cohnTriple_reachable.2 T.1 T.2.1 T.2.2 1 5 2 d hLift
    exact Prod.ext h₁ (Prod.ext h₂ h₃)
  refine ⟨P, Q, R, w, hRoot, hLift, ?_, ?_⟩
  · rw [hEntries false, left_step_calculation.2]
    decide
  · rw [hEntries true, right_step_calculation.2]
    decide

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree

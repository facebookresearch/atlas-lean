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

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessExistsUniqueMemGenCohnTree

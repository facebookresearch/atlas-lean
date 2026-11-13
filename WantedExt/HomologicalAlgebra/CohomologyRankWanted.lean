/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import MathlibExt.HomologicalAlgebra.CohomologyRank

@[expose] public section

/-!
# Cohomology rank identities

These three proof requests use the actual range rank and block differential
defined in the imported completed module. The equalities are additive in
natural numbers, and the complexes need only be finite-dimensional in each
degree.

Reference: R. van Dobben de Bruyn, *The equivalence of several conjectures
on independence of ℓ* (2020), Lemma 6.4 and Corollary 6.5,
https://arxiv.org/abs/1808.00119. These identities are internal lemmas of
that paper. Mathlib's long exact homology sequence follows Stacks Tag 0111,
https://stacks.math.columbia.edu/tag/0111.
-/

namespace MathlibExt.HomologicalAlgebra.CohomologyRankWanted

open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.MathlibExt.HomologicalAlgebra.CohomologyRank

universe u v

variable {K : Type u} [Field K]

/-- Lemma 6.4: the connecting map has rank equal to the excess rank of the
middle differential over the two outer ranks. -/
public theorem_wanted connecting_rank
    (S : ShortComplex (CochainComplex (ModuleCat.{v} K) ℤ)) (hS : S.ShortExact)
    [∀ j : ℤ, FiniteDimensional K (S.X₁.X j)]
    [∀ j : ℤ, FiniteDimensional K (S.X₂.X j)]
    [∀ j : ℤ, FiniteDimensional K (S.X₃.X j)] (i : ℤ) :
    homRank (hS.δ i (i + 1) rfl) +
        homRank (S.X₁.d i (i + 1)) + homRank (S.X₃.d i (i + 1)) =
      homRank (S.X₂.d i (i + 1))

variable {A B : CochainComplex (ModuleCat.{v} K) ℤ}

/-- Corollary 6.5: the rank of the induced cohomology map is the excess
rank of the block differential over the two component differentials. -/
public theorem_wanted homologyMap_rank_block
    (f : A ⟶ B) [∀ j : ℤ, FiniteDimensional K (A.X j)]
    [∀ j : ℤ, FiniteDimensional K (B.X j)] (i : ℤ) :
    homRank (HomologicalComplex.homologyMap f i) +
        homRank (A.d i (i + 1)) + homRank (B.d (i - 1) i) =
      Module.finrank K (LinearMap.range (cohomologyBlockDifferential f i))

/-- Corollary 6.5 with Mathlib's actual mapping cone differential.
Its sign convention changes no ranks. -/
public theorem_wanted homologyMap_rank_mappingCone
    (f : A ⟶ B) [∀ j : ℤ, FiniteDimensional K (A.X j)]
    [∀ j : ℤ, FiniteDimensional K (B.X j)] (i : ℤ) :
    homRank (HomologicalComplex.homologyMap f i) +
        homRank (A.d i (i + 1)) + homRank (B.d (i - 1) i) =
      homRank ((CochainComplex.mappingCone f).d (i - 1) i)

end MathlibExt.HomologicalAlgebra.CohomologyRankWanted

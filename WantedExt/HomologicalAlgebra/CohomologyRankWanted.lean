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
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Ranks of connecting homomorphisms and induced cohomology maps

For a short exact sequence of cochain complexes of finite-dimensional vector
spaces, the rank of its connecting homomorphism is the excess rank of the middle
differential over the two outer differentials. For a morphism of such complexes,
the rank of its induced map on cohomology is determined by a single block
differential of its mapping cone.

The statements below use actual Mathlib complexes, homology maps and connecting
homomorphisms. Rank means the dimension of the range of the underlying linear
map. The equalities are written additively in `ℕ`, avoiding truncated subtraction.
Complexes need only be finite-dimensional in each degree; they need not be bounded.

## References

* R. van Dobben de Bruyn, *The equivalence of several conjectures on independence
  of ℓ*, Épijournal de Géométrie Algébrique 4 (2020), Article 16,
  https://arxiv.org/abs/1808.00119, Lemma 6.4 and Corollary 6.5.
* The Stacks Project, https://stacks.math.columbia.edu/tag/0111, for the long exact
  homology sequence used by Mathlib's connecting homomorphism.

The rank identities hold over any field. They provide linear algebra used in
cohomological descent arguments; they assert no independence of a cohomology
theory. No source code has been copied from the references.

In the independence-of-ℓ paper these identities are proved internally.
They are recorded here as separate proof requests, rather than external
toolbox hypotheses for formalizing that paper's main theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.HomologicalAlgebra.CohomologyRankWanted

open CategoryTheory HomologicalComplex

universe u v

variable {K : Type u} [Field K]

/-- The rank of a morphism of vector spaces, as the dimension of its actual
linear-map range. -/
noncomputable def homRank {V W : ModuleCat.{v} K} (f : V ⟶ W) : ℕ :=
  Module.finrank K (LinearMap.range f.hom)

/-- **Lemma 6.4**: the connecting map `H^i(S.X₃) → H^(i+1)(S.X₁)` in a short
exact sequence has rank equal to the rank of the middle differential minus the
two outer ranks. The additive form has no natural-number subtraction. -/
public theorem_wanted connecting_rank
    (S : ShortComplex (CochainComplex (ModuleCat.{v} K) ℤ)) (hS : S.ShortExact)
    [∀ j : ℤ, FiniteDimensional K (S.X₁.X j)]
    [∀ j : ℤ, FiniteDimensional K (S.X₂.X j)]
    [∀ j : ℤ, FiniteDimensional K (S.X₃.X j)] (i : ℤ) :
    homRank (hS.δ i (i + 1) rfl) +
        homRank (S.X₁.d i (i + 1)) + homRank (S.X₃.d i (i + 1)) =
      homRank (S.X₂.d i (i + 1))

variable {A B : CochainComplex (ModuleCat.{v} K) ℤ}

/-- The block differential used in **Corollary 6.5**:
`(a, b) ↦ (d_A a, f a - d_B b)`, from `A^i × B^(i-1)` to
`A^(i+1) × B^i`. The product is the vector-space direct sum of these two terms.

Mathlib's mapping cone in degree `i - 1` uses the blocks `(-d_A, 0; f, d_B)`.
The two conventions have equal rank: multiplying the first input component and
the second output component by `-1` transforms one into the other. -/
noncomputable def cohomologyBlockDifferential (f : A ⟶ B) (i : ℤ) :
    (A.X i × B.X (i - 1)) →ₗ[K] (A.X (i + 1) × B.X i) :=
  (((A.d i (i + 1)).hom).comp (LinearMap.fst K (A.X i) (B.X (i - 1)))).prod
    (((f.f i).hom).comp (LinearMap.fst K (A.X i) (B.X (i - 1))) -
      ((B.d (i - 1) i).hom).comp (LinearMap.snd K (A.X i) (B.X (i - 1))))

/-- **Corollary 6.5**: the rank of `H^i(f)` is the excess rank of the displayed
block differential over the ranks of `d_A^i` and `d_B^(i-1)`. -/
public theorem_wanted homologyMap_rank_block
    (f : A ⟶ B) [∀ j : ℤ, FiniteDimensional K (A.X j)]
    [∀ j : ℤ, FiniteDimensional K (B.X j)] (i : ℤ) :
    homRank (HomologicalComplex.homologyMap f i) +
        homRank (A.d i (i + 1)) + homRank (B.d (i - 1) i) =
      Module.finrank K (LinearMap.range (cohomologyBlockDifferential f i))

/-- The same **Corollary 6.5**, using Mathlib's actual mapping cone differential
from degree `i - 1` to degree `i`. Its sign convention changes no ranks. -/
public theorem_wanted homologyMap_rank_mappingCone
    (f : A ⟶ B) [∀ j : ℤ, FiniteDimensional K (A.X j)]
    [∀ j : ℤ, FiniteDimensional K (B.X j)] (i : ℤ) :
    homRank (HomologicalComplex.homologyMap f i) +
        homRank (A.d i (i + 1)) + homRank (B.d (i - 1) i) =
      homRank ((CochainComplex.mappingCone f).d (i - 1) i)

end MathlibExt.HomologicalAlgebra.CohomologyRankWanted

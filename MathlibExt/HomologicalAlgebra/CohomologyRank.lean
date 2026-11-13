/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Linear maps for cohomology rank calculations

`homRank` is the dimension of the range of an actual morphism of vector
spaces. `cohomologyBlockDifferential` constructs the block linear map
`(a, b) ↦ (d_A a, f a - d_B b)` associated with a morphism of cochain
complexes.

## Reference

R. van Dobben de Bruyn, *The equivalence of several conjectures on independence
of ℓ*, Épijournal de Géométrie Algébrique 4 (2020), Article 16,
Lemma 6.4 and Corollary 6.5. https://arxiv.org/abs/1808.00119
-/

namespace MathlibExt.HomologicalAlgebra.CohomologyRank

open _root_.CategoryTheory _root_.HomologicalComplex

universe u v

variable {K : Type u} [Field K]

/-- The rank of a morphism of vector spaces, as the dimension of its actual
linear-map range. -/
noncomputable def homRank {V W : ModuleCat.{v} K} (f : V ⟶ W) : ℕ :=
  Module.finrank K (LinearMap.range f.hom)

variable {A B : CochainComplex (ModuleCat.{v} K) ℤ}

/-- The block differential `(a, b) ↦ (d_A a, f a - d_B b)` from
`A^i × B^(i-1)` to `A^(i+1) × B^i`. The product is the vector-space
direct sum of these two terms. -/
noncomputable def cohomologyBlockDifferential (f : A ⟶ B) (i : ℤ) :
    (A.X i × B.X (i - 1)) →ₗ[K] (A.X (i + 1) × B.X i) :=
  (((A.d i (i + 1)).hom).comp (LinearMap.fst K (A.X i) (B.X (i - 1)))).prod
    (((f.f i).hom).comp (LinearMap.fst K (A.X i) (B.X (i - 1))) -
      ((B.d (i - 1) i).hom).comp (LinearMap.snd K (A.X i) (B.X (i - 1))))

end MathlibExt.HomologicalAlgebra.CohomologyRank

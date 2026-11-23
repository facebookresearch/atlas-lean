/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free groups of type FP∞ and cohomological dimension (Kourovka Notebook Problem 6.4)

Kourovka Notebook, Archive of Solved Problems, Problem 6.4 (R. Bieri): a group G is of type (FP)_∞
if the trivial G-module ℤ has a resolution by finitely generated projective G-modules. Is it true
that every torsion-free group of type (FP)_∞ has finite cohomological dimension?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.Rep.Iso

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeFPInfinityCohomologicalDimensionKourovka6Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.4 (R. Bieri).
UnsolvedMath record UM-00700351 (`KOU-6.4`), dataset ulamai/UnsolvedMath v1.8.0.

The trivial module is `ℤ` as a `MonoidAlgebra ℤ G`-module (via Mathlib's
`Rep.toModuleMonoidAlgebra`). Type `(FP)_∞` is the existence of a projective resolution with
finitely generated terms, as in the OpenConjectures entry for Kourovka 6.3 (stated inline here). The
cohomological dimension of `G` is the projective dimension of the trivial module, so it is finite
exactly when `HasProjectiveDimensionLT` holds for some `n`. Torsion-free is written `∀ g, g ≠ 1 → ¬
IsOfFinOrder g`.
-/

open CategoryTheory

/-- Kourovka 6.4 (R. Bieri): every torsion-free group of type `(FP)_∞` (the trivial `ℤG`-module `ℤ`
has a projective resolution by finitely generated `ℤG`-modules) has finite cohomological dimension
(`ℤ` has finite projective dimension over `ℤG`). -/
def torsionFreeFPInfinityFiniteCohomologicalDimension : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    (∃ P : ProjectiveResolution ((Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)).obj
        (Rep.trivial ℤ G ℤ)), ∀ i : ℕ, Module.Finite (MonoidAlgebra ℤ G) (P.complex.X i)) →
    ∃ n : ℕ, HasProjectiveDimensionLT
      ((Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)).obj (Rep.trivial ℤ G ℤ)) n

/--
Resolved false: the Kourovka Archive answers 6.4 "No", citing Brown and Geoghegan (1984), An
infinite-dimensional torsion-free FP∞ group: some torsion-free group of type `(FP)_∞` has infinite
cohomological dimension. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 6.4 (R. Bieri); resolution: K. S. Brown and R. Geoghegan, An infinite-dimensional
torsion-free FP∞ group, Invent. Math. 77 (1984), 367-381, Kourovka Archive, Problem 6.4: No (Brown,
Geoghegan), https://doi.org/10.1007/BF01388451.
-/
public theorem_wanted torsionFreeFPInfinityFiniteCohomologicalDimension_refuted :
    ¬ torsionFreeFPInfinityFiniteCohomologicalDimension

end MathlibExt.GroupTheory.TorsionFreeFPInfinityCohomologicalDimensionKourovka6Problem4Wanted

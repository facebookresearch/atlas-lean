/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.LefschetzDecomposition

@[expose] public section

/-!
# Deligne's Lefschetz splitting criterion

The remaining proof request is the finite splitting of a bounded object
satisfying hard Lefschetz. The cohomology functor and the maps induced by
the degree-two morphism are defined in the imported completed module.

References: Deligne, *Théorème de Lefschetz et critères de dégénérescence
de suites spectrales* (1968), Theorem 1.5, p. 108,
https://doi.org/10.1007/BF02698925; de Cataldo–Migliorini,
*Hodge-theoretic aspects of the Decomposition Theorem*, §2.2,
https://www.math.stonybrook.edu/~mde/papers/20.pdf.
-/

namespace MathlibExt.CategoryTheory.LefschetzDecompositionWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Triangulated
open _root_.MathlibExt.CategoryTheory.LefschetzDecomposition

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (j : ℤ), (shiftFunctor C j).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Deligne's Lefschetz criterion: a bounded object with a hard Lefschetz
degree-two morphism admits a finite decomposition into its cohomology
objects shifted by their negative degrees.
Source: Deligne (1968), Theorem 1.5; de Cataldo–Migliorini, §2.2. -/
public theorem_wanted deligne_lefschetz_decomposition
    (t : TStructure C) (K : C) (η : K ⟶ K⟦(2 : ℤ)⟧)
    (hK : t.bounded K) (hη : HasHardLefschetz t η) :
    ∃ degrees : Finset ℤ,
      (∀ j : ℤ, j ∉ degrees →
        IsZero ((cohomologyFunctor t j).obj K)) ∧
      Nonempty (K ≅ biproduct
        (fun j : degrees ↦ (cohomologyFunctor t (j : ℤ)).obj K⟦-(j : ℤ)⟧))

end MathlibExt.CategoryTheory.LefschetzDecompositionWanted

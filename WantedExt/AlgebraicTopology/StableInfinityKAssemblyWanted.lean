/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.StableInfinityKSpectra

/-!
# Source-normalized connective K assembly

This construction implements BGT arXiv:1001.2282v4, Section 7.1 and
Definition 7.5. The output is the native Tau Ceti sphere module with its
actual interval-coordinate, finite-permutation and exact-functor maps.
Universal-invariant and corepresentability conclusions do not define K.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.StableInfinityKSpectra

open StableInfinityCategoryModels

universe u

/-- Assemble all full S-diagonals and their source maps into native spectra. -/
def_wanted native_connective_k_construction : ConnectiveKConstruction

/-- Shrink an actually small native simplicial category without changing its source. -/
def_wanted stable_small_presentation (C : StableInfinityCategory.{u})
    (h : ∀ k : SimplexCategoryᵒᵖ, Small.{0} (C.toSSet.obj k)) :
  StableSmallPresentation C

end MathlibExt.AlgebraicTopology.StableInfinityKSpectra

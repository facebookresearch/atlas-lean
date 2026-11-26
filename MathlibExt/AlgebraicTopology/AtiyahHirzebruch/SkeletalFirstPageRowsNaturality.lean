/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralSequence.FirstPageRowNaturality

/-!
# Naturality of first-page row homology

In an abelian category, consider spectral sequences with differential of bidegree (r,1−r),
starting at page 1. For fixed q the first-page row has objects E₁^{p,q} and differential
E₁^{p,q} → E₁^{p+1,q}. Its three-term complex at p−1,p,p+1 is identified with the
corresponding three-term complex of the full first page by identity components.

These comparisons commute with first-page maps. On homology they identify the row homology
with E₂^{p,q}, naturally for spectral-sequence maps using their successor-page compatibility.
This import provides the definitions in
MathlibExt.Algebra.Homology.SpectralSequence.FirstPageRowNaturality; the category and indexing
universes remain independent.
-/

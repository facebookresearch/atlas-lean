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

public import MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration

/-!
# Filtration of a spectral-object abutment

Let Y be a spectral object in an abelian category D, indexed by a preorder with least and
greatest elements. In integer degree n write A = H_Yⁿ(⊥,⊤). The restrictions r_i : A →
H_Yⁿ(i,⊤) define an increasing kernel filtration F_i = Ker(r_i), equal to Im(H_Yⁿ(⊥,i) → A).

For i₁ ≤ i₂ the endpoint window E_Yⁿ(⊥ ≤ i₁ ≤ i₂ ≤ ⊤) is canonically the associated graded
F_{i₂}/F_{i₁}. The restriction, image, kernel and quotient comparisons commute with
spectral-object maps. These definitions are available through
MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration, with independent object,
morphism and indexing universes.
-/

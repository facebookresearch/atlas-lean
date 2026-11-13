/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

@[expose] public section

/-!
# Wanted providers for rational perverse sheaves

The completed rational-sheaf, bounded-constructibility, support, costalk,
heart and perverse-cohomology definitions are in
`MathlibExt/AlgebraicGeometry/PerverseSheaves.lean`. This file records the
remaining construction of the characterized middle perverse theory and
its abelian heart for every complex variety.

## References

* M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  Ann. Sci. École Norm. Sup. (4) 38 (2005), §§3.3, 3.6.
  https://arxiv.org/abs/math/0306030
-/

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

open CategoryTheory

noncomputable section

/-! ## Wanted constructions -/

/-- Construct the rational middle perverse t-structure and the closure
properties needed for the bounded constructible category.
Source: de Cataldo–Migliorini (2005), §§3.3, 3.6. -/
public instance_wanted perverseSheafTheoryWanted (X : ComplexScheme)
    [IsComplexVariety X] : PerverseSheafTheory X

/-- The category of rational perverse sheaves is abelian.
Source: de Cataldo–Migliorini (2005), §3.6. -/
public instance_wanted perverseSheafAbelianWanted (X : ComplexScheme)
    [IsComplexVariety X] : Abelian (PerverseSheaf X)

end

end MathlibExt.AlgebraicGeometry.PerverseSheaves

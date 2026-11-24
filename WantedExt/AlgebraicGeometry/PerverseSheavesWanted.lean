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

The rational-sheaf, bounded-constructibility, support, costalk, heart and
perverse-cohomology definitions are in
`MathlibExt/AlgebraicGeometry/PerverseSheaves.lean`, where the middle perverse
t-structure is characterized by its support and cosupport conditions
(`PerverseSheafTheory`, unique when it exists). Request its existence on every
complex variety, and that its heart, the category of rational perverse sheaves,
is abelian. `instance_wanted` declarations are local to this file, so other
modules keep explicit `[PerverseSheafTheory X]` binders.

## References

* A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982), Théorème 1.3.6 and §2.2.
* M. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  Ann. Sci. École Norm. Sup. (4) 38 (2005), §§3.3, 3.6.
  https://arxiv.org/abs/math/0306030
-/

namespace WantedExt.AlgebraicGeometry.PerverseSheavesWanted

open CategoryTheory
open MathlibExt.AlgebraicGeometry.PerverseSheaves

noncomputable section

/-! ## Wanted constructions -/

/-- The category of rational perverse sheaves, the heart of the middle perverse
t-structure, is abelian.
Source: BBD, Théorème 1.3.6; de Cataldo–Migliorini (2005), §3.6. -/
public instance_wanted perverseSheafAbelianWanted (X : ComplexScheme)
    [IsComplexVariety X] [PerverseSheafTheory X] : Abelian (PerverseSheaf X)

/-- Construct the rational middle perverse t-structure and the closure
properties needed for the bounded constructible category: `PerverseSheafTheory X`,
stated as the coefficient-generic class at `k = ℚ` that it abbreviates.
Source: de Cataldo–Migliorini (2005), §§3.3, 3.6. -/
public instance_wanted perverseSheafTheoryWanted (X : ComplexScheme)
    [IsComplexVariety X] :
    MathlibExt.AlgebraicGeometry.CoefficientPerverseModels.CoefficientPerverseTheory ℚ X

end

end WantedExt.AlgebraicGeometry.PerverseSheavesWanted

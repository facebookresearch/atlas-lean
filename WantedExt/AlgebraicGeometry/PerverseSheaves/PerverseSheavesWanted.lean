/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.AlgebraicGeometry.PerverseSheaves.Basic

@[expose] public section

/-!
# Wanted construction of rational perverse sheaves

For every reduced, separated complex variety of finite type, request the
middle perverse t-structure with its support and cosupport characterizations,
its heart, and the abelian-category structure on that heart.

The definitions and public interface are in `Basic.lean`. Smoothness and
projectivity are hypotheses of particular applications and do not enter
this construction request.

## References

* M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
  §§3.3, 3.6. https://arxiv.org/abs/math/0306030
* Their survey, §2.3. https://arxiv.org/abs/0712.0349
-/

namespace MathlibExt.AlgebraicGeometry.PerverseSheaves

open CategoryTheory

/-- Construct the rational middle perverse t-structure and the closure
properties needed for the bounded constructible category.
Source: de Cataldo–Migliorini (2005), §§3.3, 3.6. -/
public instance_wanted perverseSheafTheoryWanted (X : ComplexScheme)
    [IsComplexVariety X] : PerverseSheafTheory X

/-- Construct the category of rational perverse sheaves as the heart of the
middle perverse t-structure.
Source: de Cataldo–Migliorini (2005), §3.6. -/
public def_wanted perverseSheaves (X : ComplexScheme)
    [IsComplexVariety X] : Type 1 :=
  letI : PerverseSheafTheory X := ❰perverseSheafTheoryWanted❱ X
  PerverseSheaf X

/-- The category of rational perverse sheaves is abelian.
Source: de Cataldo–Migliorini (2005), §3.6. -/
public instance_wanted perverseSheafAbelianWanted (X : ComplexScheme)
    [IsComplexVariety X] : Abelian (PerverseSheaf X)

end MathlibExt.AlgebraicGeometry.PerverseSheaves

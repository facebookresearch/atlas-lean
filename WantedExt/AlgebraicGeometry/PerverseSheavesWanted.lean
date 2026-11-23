/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

/-!
# Existence of the rational middle perverse t-structure

Beilinson–Bernstein–Deligne: on a complex variety, the bounded constructible
rational complexes form a triangulated subcategory of the derived category of
rational sheaves on `X(ℂ)`, and it carries a t-structure whose aisles are given
by the support and cosupport conditions of `PerverseSheafTheory`. Those
conditions determine the t-structure, so the instance requested here is the
unique one (`PerverseSheafTheory.instSubsingleton`).

## References

* A. A. Beilinson, J. Bernstein and P. Deligne, *Faisceaux pervers*,
  Astérisque 100 (1982), Chapter 2.
* M. A. A. de Cataldo and L. Migliorini, *The decomposition theorem, perverse
  sheaves and the topology of algebraic maps*, Bull. Amer. Math. Soc. 46 (2009),
  §2.3, equations (14) and (15). https://arxiv.org/abs/0712.0349
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PerverseSheavesWanted

open MathlibExt.AlgebraicGeometry.PerverseSheaves

/-- Every complex variety carries the rational middle perverse t-structure on
its bounded constructible complexes, characterized by the stalk and costalk
dimension conditions. -/
public instance_wanted perverseSheafTheory (X : ComplexScheme) [IsComplexVariety X] :
    PerverseSheafTheory X

end WantedExt.AlgebraicGeometry.PerverseSheavesWanted

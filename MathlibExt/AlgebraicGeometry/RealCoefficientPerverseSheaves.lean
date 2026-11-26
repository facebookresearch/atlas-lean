/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import MathlibExt.Algebra.RealSubfieldCoefficients

/-!
# Actual perverse realizations with a real coefficient subfield

The coefficient is an actual subfield A of R, with its canonical embedding
into C. The sheaf and derived categories, finite-rank local systems and
algebraic constructibility are the coefficient-generic constructions of
`ConstructibleComplexes` at `k = A`; extension of coefficients to `C` is its
`scalarExtension`. The characterized middle perverse t-structure `PerverseTheory A X`
is `CoefficientPerverseModels.CoefficientPerverseTheory` at `k = A`, with the
coefficient-generic stalk/costalk supports, as `PerverseSheaves.PerverseSheafTheory`
is its case `k = ℚ`. This extends the existing rational perverse dictionary; it
supplies no new perverse/Hodge theorem oracle and assumes no Hodge-module
preservation law.

Sources: Morihiko Saito, arXiv:1307.2140v5, Introduction and section 1.1;
the existing PerverseSheaves source credits for the middle t-structure;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, sheaf and
derived-category primitives, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealCoefficientPerverseSheaves

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry PerverseSheaves ComplexAnalytification Opposite
open MathlibExt.Algebra.RealSubfieldCoefficients

attribute [local instance] HasDerivedCategory.standard

variable (A : Subfield ℝ)

attribute [local instance] complexAlgebra

/-- The constant sheaf with coefficients in `A`. -/
def constantCoefficient (Z : TopCat.{0}) : ConstructibleComplexes.CoefficientSheaf A Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} A)).obj (ModuleCat.of A A)

/-- The middle perverse t-structure with coefficients in `A`:
`CoefficientPerverseModels.CoefficientPerverseTheory` at `k = A`, characterized by the stalk and
costalk support conditions with coefficients in `A`. -/
abbrev PerverseTheory (X : ComplexScheme) [IsComplexVariety X] :=
  CoefficientPerverseModels.CoefficientPerverseTheory A X

/-- For a subfield `A` of `ℝ` and a complex variety `X` equipped with a middle perverse theory with
coefficients in `A` (an instance of `PerverseTheory A X`), the characterized middle perverse
t-structure on the bounded algebraically constructible complexes of sheaves of `A`-vector spaces on
`X(ℂ)`. -/
def perverseTStructure (X : ComplexScheme) [IsComplexVariety X] [PerverseTheory A X] :
    _root_.CategoryTheory.Triangulated.TStructure
      (ConstructibleComplexes.boundedConstructible A X).FullSubcategory :=
  CoefficientPerverseModels.CoefficientPerverseTheory.t (k := A) (X := X)

abbrev Perverse (X : ComplexScheme) [IsComplexVariety X] [PerverseTheory A X] :=
  (perverseTStructure A X).heart.FullSubcategory

def perverseCohomology (X : ComplexScheme) [IsComplexVariety X] [PerverseTheory A X]
    (j : ℤ) (K : (ConstructibleComplexes.boundedConstructible A X).FullSubcategory) :
    Perverse A X :=
  ⟨((perverseTStructure A X).truncGELE 0 0).obj (K⟦j⟧), by
    rw [_root_.CategoryTheory.Triangulated.TStructure.mem_heart_iff]
    constructor <;> infer_instance⟩

/-- Extension of coefficients from `A` to `ℂ`: sectionwise tensor product,
then sheafification. -/
abbrev extendCoefficients (Z : TopCat.{0}) :
    ConstructibleComplexes.CoefficientSheaf A Z ⥤ ConstructibleComplexes.CoefficientSheaf ℂ Z :=
  ConstructibleComplexes.scalarExtension A ℂ Z

end MathlibExt.AlgebraicGeometry.RealCoefficientPerverseSheaves

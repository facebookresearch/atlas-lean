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
`scalarExtension`. The stalk/costalk supports and the characterized middle
perverse t-structure follow the rational definitions of `PerverseSheaves`, with
coefficients in `A`. This extends the existing rational perverse dictionary; it
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

/-- The algebraic image of the nonzero stalks of the `j`th cohomology sheaf. -/
def stalkSupport (X : ComplexScheme) (K : ConstructibleComplexes.CoefficientDerived A (space X))
    (j : ℤ) : Set X.left :=
  ComplexPoints.schemePoint '' {p : space X | ¬ IsZero
    (((DerivedCategory.homologyFunctor _ j).obj K).presheaf.stalk p)}

/-- The skyscraper with coefficients in `A` at a complex point, in degree zero. -/
def skyscraper (X : ComplexScheme) (p : space X) :
    ConstructibleComplexes.CoefficientDerived A (space X) := by
  classical
  exact (DerivedCategory.singleFunctor _ 0).obj (skyscraperSheaf p (ModuleCat.of A A))

/-- The algebraic image of nonzero `j`th costalk cohomology. -/
def costalkSupport (X : ComplexScheme) (K : ConstructibleComplexes.CoefficientDerived A (space X))
    (j : ℤ) : Set X.left :=
  ComplexPoints.schemePoint '' {p : space X | ¬ Subsingleton (skyscraper A X p ⟶ K⟦j⟧)}

/-- The middle perverse t-structure with coefficients in `A`, characterized by
its support and cosupport conditions as in `PerverseSheaves.PerverseSheafTheory`. -/
class PerverseTheory (X : ComplexScheme) [IsComplexVariety X] where
  [isTriangulated : (ConstructibleComplexes.boundedConstructible A X).IsTriangulated]
  t : _root_.CategoryTheory.Triangulated.TStructure
    (ConstructibleComplexes.boundedConstructible A X).FullSubcategory
  le_iff : ∀ K m, t.le m K ↔ ∀ j,
    SupportDimensionLE X (stalkSupport A X K.obj j) (m - j)
  ge_iff : ∀ K m, t.ge m K ↔ ∀ j,
    SupportDimensionLE X (costalkSupport A X K.obj j) (j - m)

attribute [instance] PerverseTheory.isTriangulated

/-- The support and cosupport conditions determine the perverse t-structure. -/
instance PerverseTheory.instSubsingleton (X : ComplexScheme) [IsComplexVariety X] :
    Subsingleton (PerverseTheory A X) where
  allEq := by
    rintro ⟨t₁, hle₁, hge₁⟩ ⟨t₂, hle₂, hge₂⟩
    have hle : t₁.le = t₂.le :=
      funext fun m ↦ funext fun K ↦ propext ((hle₁ K m).trans (hle₂ K m).symm)
    have hge : t₁.ge = t₂.ge :=
      funext fun m ↦ funext fun K ↦ propext ((hge₁ K m).trans (hge₂ K m).symm)
    have ht : t₁ = t₂ := by
      cases t₁
      cases t₂
      cases hle
      cases hge
      rfl
    subst ht
    rfl

def perverseTStructure (X : ComplexScheme) [IsComplexVariety X] [PerverseTheory A X] :=
  PerverseTheory.t (A := A) (X := X)

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

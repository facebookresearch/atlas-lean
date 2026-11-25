/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Middle perverse carriers over an actual coefficient field

This extends the existing rational support/cosupport normalization to
every coefficient field. The carrier is the original sheaf derived
category on the complex-point topology, with the native algebraic
constructibility condition. Its middle t-structure is characterized in
every degree by the actual stalk and skyscraper-costalk supports.
The supports `stalkSupport`, `costalkSupport` and the characterized structure
`CoefficientPerverseTheory` are stated in `PerverseSheaves`, so that the rational
`PerverseSheaves.PerverseSheafTheory` and the real-coefficient
`RealCoefficientPerverseSheaves.PerverseTheory` are literally its cases `k = ℚ` and
`k = A` for a subfield `A` of ℝ. The structure is a subsingleton. The real
coefficient embedding into ℂ is `RealSubfieldCoefficients.complexEmbedding`.

Sources: Saito1307.2140v5, Section1.1; de Cataldo--Migliorini,
arXiv:math/0504554, Sections3.3 and3.6, and arXiv:0712.0349,
Section2.3. Existing rational normalizations are reused from
PerverseSheaves. Native heart and truncation constructors are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0, Joël Riou.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

variable (k : Type) [Field k] (X : PerverseSheaves.ComplexScheme)

/-- The middle perverse condition on the original bounded algebraically constructible complex. -/
def middlePerverse : ObjectProperty (CoefficientDerived k (space X)) := fun K =>
  ConstructibleComplexes.boundedConstructible k X K ∧
    (∀ j : ℤ, SupportDimensionLE X (stalkSupport k X K j) (-j)) ∧
    (∀ j : ℤ, SupportDimensionLE X (costalkSupport k X K j) j)

/-- Every coefficient-perverse object and every original derived morphism. -/
abbrev PerverseCarrier := (middlePerverse k X).FullSubcategory

variable [IsComplexVariety X] [CoefficientPerverseTheory k X]

/-- The source-characterized middle perverse t-structure. -/
def perverseTStructure :
    Triangulated.TStructure (ConstructibleComplexes.boundedConstructible k X).FullSubcategory :=
  CoefficientPerverseTheory.t (k := k) (X := X)

/-- The native abelian heart on the same coefficient-derived complexes. -/
abbrev PerverseSheaf := (perverseTStructure k X).heart.FullSubcategory

/-- Actual coefficient perverse cohomology, formed by native truncation after the source shift. -/
def perverseCohomology (j : ℤ)
    (K : (ConstructibleComplexes.boundedConstructible k X).FullSubcategory) : PerverseSheaf k X :=
  ⟨((perverseTStructure k X).truncGELE 0 0).obj (K⟦j⟧), by
    rw [Triangulated.TStructure.mem_heart_iff]
    constructor <;> infer_instance⟩

/-- The original coefficient-derived object of an actual native perverse-heart object. -/
def underlyingDerived (K : PerverseSheaf k X) : CoefficientDerived k (space X) := K.obj.obj

end MathlibExt.AlgebraicGeometry.CoefficientPerverseModels

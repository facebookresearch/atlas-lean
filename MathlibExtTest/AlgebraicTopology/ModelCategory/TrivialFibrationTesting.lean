/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.TrivialFibrationTesting
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCylinder
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass

/-!
# Public clients of intrinsic trivial-fibration testing
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TrivialFibrationTesting

section Inverse

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
  {X Y T : C} {p : X ⟶ Y}

/-- The actual chosen section represents the inverse in the quotient,
with no initial, terminal, exactness or model assumption. -/
theorem sectionRepresentsInverse (D : P.DualDeformationData p) :
    ∃ e : P.homotopyQuotientFunctor.obj X ≅ P.homotopyQuotientFunctor.obj Y,
      e.hom = P.homotopyQuotientFunctor.map p ∧
        e.inv = P.homotopyQuotientFunctor.map D.section_ := by
  have : IsIso (P.homotopyQuotientFunctor.map p) :=
    (P.homotopyEquivalences_iff p).mp D.mem_homotopyEquivalences
  refine ⟨asIso (P.homotopyQuotientFunctor.map p), rfl, ?_⟩
  change inv (P.homotopyQuotientFunctor.map p) = P.homotopyQuotientFunctor.map D.section_
  apply (cancel_mono (P.homotopyQuotientFunctor.map p)).mp
  rw [IsIso.inv_hom_id, ← P.homotopyQuotientFunctor.map_comp, D.section_comp,
    P.homotopyQuotientFunctor.map_id]

/-- Dual data induce a bijection on actual classes into every target. -/
theorem allTargetClasses (D : P.DualDeformationData p) (T : C) :
    Function.Bijective (P.homotopyClassPrecomp p T) :=
  (P.homotopyEquivalences_iff_precomp_bijective p).mp D.mem_homotopyEquivalences T

end Inverse

section Boundary

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  [HasInitial C] [InitialMonoClass C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}] {X Y : C}

/-- The generic boundary lift supplies an actual section, both endpoints
and the whole over-base map, without any pushout or terminal hypothesis. -/
theorem genericBoundaryData (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) :
    ∃ (s : Y ⟶ X) (H : P.I.obj X ⟶ X),
      s ≫ p = 𝟙 Y ∧ (P.app X).i₀ ≫ H = 𝟙 X ∧
        (P.app X).i₁ ≫ H = p ≫ s ∧ H ≫ p = (P.app X).π ≫ p := by
  obtain ⟨D⟩ := P.nonempty_dualDeformationData_of_rlp_monomorphisms p hp
  exact ⟨D.section_, D.homotopy.h, D.section_comp, D.homotopy.h₀,
    D.homotopy.h₁, D.over_base⟩

end Boundary

open SSet SSet.joyalInterval

/-- Every map in the intrinsic trivial-fibration class is an actual
finite-J testing equivalence, without fibrancy on either endpoint. -/
theorem finiteJTesting {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms SSet).rlp p) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions p :=
  productPrecylinder.rlp_monomorphisms_le_testingEquivalences auxiliaryAnodyneExtensions p hp

/-- Both surjectivity and injectivity hold on arbitrary quotient classes
into every actual naive fibrant target of the specified finite-J system. -/
theorem finiteJClassBijection {X Y T : SSet.{u}} (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms SSet).rlp p)
    (hT : auxiliaryAnodyneExtensions.naiveFibrantObjects T) :
    Function.Bijective (productPrecylinder.homotopyClassPrecomp p T) :=
  (productPrecylinder.testingEquivalences_iff auxiliaryAnodyneExtensions p).mp
    (finiteJTesting p hp) T hT

end MathlibExtTest.AlgebraicTopology.ModelCategory.TrivialFibrationTesting

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolonomicCharacteristicSupportModels

/-!
# General regular holonomic native D-modules

Regularity is the local good-filtration criterion I_Lambda times gr(M)
equals zero. Here I_Lambda is the radical of the actual graded annihilator,
so the literal inclusion I_Lambda <= annihilator encodes that condition.
All symbols are the existing normalized actions
on actual native cokernel germs; every point of each source neighborhood
is tested. The carrier is the full D_X sheaf-module category, with no
restriction on support. Bounded regular holonomicity uses its native
cohomology. Regularity is independent of any RH comparison conclusion.

Source: Kashiwara--Schapira, Lectures on Regular and Irregular Holonomic
D-modules, IHES M/15/08 (May13,2015), Definition3.1.1, printed34/PDF35,
https://preprints.ihes.fr/storage/M-15-08.pdf. This states the local
analytic criterion on complex manifolds, for arbitrary support, and
references Kashiwara, D-modules and Microlocal Calculus, AMS217 (2003),
Section5.2. The equivalent radical-annihilator form is explicitly in Caillotto--Fiorot,
Algebraic connections vs. algebraic D-modules: regularity conditions,
arXiv:1512.02778v1 Section2, printed5, with the same Section5.2 reference.
DK1311.2374v2 Section2.5 references the same definition and defines the
bounded regular-holonomic category cohomologically. Mathlib56a005 native
modules, local cokernels, annihilators, radical ideals and homology,
Apache2.0. No copied source proof or completed source provider is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RegularHolonomicModels

open _root_.CategoryTheory TopologicalSpace
open HolonomicCharacteristicSupportModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open scoped Manifold ContDiff

variable (n : ℕ) (X : Type) [TopologicalSpace X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0}]
  [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Opens X) (V : Over U), HasWeakSheafify
    (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0}]
  [∀ (U : Opens X) (V : Over U),
    (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

structure LocalRegularGoodFiltration (N : NativeDModule n X) (U : Opens X) where
  good : LocalGoodFiltration n X N U
  symbol : ∀ (x : X) (hx : x ∈ U), SymbolAtPointSource n X N U good x hx
  holonomic : ∀ (x : X) (hx : x ∈ U),
    HasHolonomicSymbolDimension n X N U good x hx (symbol x hx)
  reducedCharacteristicAnnihilates : ∀ (x : X) (hx : x ∈ U),
    (characteristicIdeal n X N U good x hx (symbol x hx)).radical ≤
      characteristicIdeal n X N U good x hx (symbol x hx)

/-- The radical form is definitionally the reduced characteristic ideal's annihilation condition. -/
theorem LocalRegularGoodFiltration.gradedAnnihilator_isRadical
    {N : NativeDModule n X} {U : Opens X} (G : LocalRegularGoodFiltration n X N U)
    (x : X) (hx : x ∈ U) :
    (characteristicIdeal n X N U G.good x hx (G.symbol x hx)).IsRadical :=
  G.reducedCharacteristicAnnihilates x hx

/-- Kashiwara's local radical graded-annihilator condition on arbitrary-support D_X modules. -/
def IsRegularHolonomic (N : NativeDModule n X) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ Nonempty (LocalRegularGoodFiltration n X N U)

theorem isRegularHolonomic_isHolonomic {N : NativeDModule n X}
    (h : IsRegularHolonomic n X N) : IsHolonomic n X N := by
  intro x
  obtain ⟨U, hx, ⟨G⟩⟩ := h x
  exact ⟨U, hx, G.good, G.symbol x hx, G.holonomic x hx⟩

attribute [local instance] HasDerivedCategory.standard

def IsBoundedRegularHolonomic : ObjectProperty (DerivedCategory (NativeDModule n X)) := fun K =>
  IsBoundedDerived (NativeDModule n X) K ∧
    ∀ i : ℤ, IsRegularHolonomic n X
      ((DerivedCategory.homologyFunctor (NativeDModule n X) i).obj K)

abbrev RegularHolonomicDerived := (IsBoundedRegularHolonomic n X).FullSubcategory

theorem boundedRegularHolonomic_le_boundedHolonomic :
    IsBoundedRegularHolonomic n X ≤ IsBoundedHolonomic n X := by
  intro K h
  exact ⟨h.1, fun i => isRegularHolonomic_isHolonomic n X (h.2 i)⟩

def regularHolonomicInclusion : RegularHolonomicDerived n X ⥤ HolonomicDerived n X :=
  (IsBoundedRegularHolonomic n X).ιOfLE (boundedRegularHolonomic_le_boundedHolonomic n X)

end MathlibExt.AlgebraicGeometry.RegularHolonomicModels

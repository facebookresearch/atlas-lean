/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SubanalyticConstructibleSheaves
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

/-!
# Constructibility in arbitrary original real coordinate atlases

This includes the actual odd-dimensional M times R used by enhanced
sheaves. Strata are locally closed, locally finite subanalytic subsets
in the original charts. Their actual pullback sheaves are locally finite
rank constant coefficient sheaves. Derived constructibility is checked
on the original native cohomology objects and boundedness.

Source: DK1311.2374v2 Sections2.3,2.4,4.9;
Mathlib56a005 native charts, sheaf pullback and homology, Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RealSubanalyticConstructibleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open CompactSupportIndSheaves SubanalyticCoordinateModels SubanalyticConstructibleSheaves
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def IsSubanalyticInCharts (S : Set M) : Prop :=
  ∀ x : M, IsSubanalyticAt E ((chartAt E x) '' (S ∩ (chartAt E x).source)) ((chartAt E x) x)

structure RealSubanalyticPartition where
  index : Type
  stratum : index → Set M
  subanalytic : ∀ i, IsSubanalyticInCharts E M (stratum i)
  locallyClosed : ∀ i, IsLocallyClosedSubset M (stratum i)
  disjoint : Pairwise (fun i j => Disjoint (stratum i) (stratum j))
  covers : (⋃ i, stratum i) = Set.univ
  locallyFinite : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
    Set.Finite {i | (stratum i ∩ U).Nonempty}

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]

def realStratumInclusion (P : RealSubanalyticPartition E M) (i : P.index) :
    TopCat.of (P.stratum i) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def IsRealConstructible (F : OrdinarySheaf ℂ (TopCat.of M)) : Prop :=
  ∃ P : RealSubanalyticPartition E M, ∀ i : P.index,
    LocallyFiniteRank (TopCat.of (P.stratum i))
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℂ) (realStratumInclusion E M P i)).obj F)

attribute [local instance] HasDerivedCategory.standard

def IsBoundedRealConstructible (F : DerivedCategory (OrdinarySheaf ℂ (TopCat.of M))) : Prop :=
  IsBoundedDerived (OrdinarySheaf ℂ (TopCat.of M)) F ∧
    ∀ i : ℤ, IsRealConstructible E M
      ((DerivedCategory.homologyFunctor (OrdinarySheaf ℂ (TopCat.of M)) i).obj F)

end MathlibExt.AlgebraicGeometry.RealSubanalyticConstructibleModels

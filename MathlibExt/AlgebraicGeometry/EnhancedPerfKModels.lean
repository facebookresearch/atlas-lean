/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction
public import MathlibExt.CategoryTheory.NativeDGNerveModels

/-!
# Actual enhanced perfect DG inputs to the stable K construction

The perfect category is the native cofibrant perfect right-module category:
finite shifted cells, twisted differentials and actual localized retracts.
Its small model is connected by the whole enriched quasi-equivalence.
The stable input is fixed to that exact coherent nerve by an equality,
not by a free object classification or by H0 alone.

DG functors give the actual native coherent-nerve maps in all simplicial
degrees. Stability, idempotent completeness and exactness adapter proofs
are separate requests. The general BGT stable-category domain is in the
imported models; a DG realization is one positively defined example.

Sources: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2/4/7;
Toen--Vaquie, math/0503269v5, perfect DG modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedPerfKModels

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
open MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction

universe u

variable {k : Type u} [CommRing k] {A B : DGCat k}

/-- This source stable category is exactly the already specified whole enhanced Perf nerve. -/
structure EnhancedPerfectInput (P : SmallPerfectModel A) where
  category : PerfectInfinityCategory.{u}
  normalized : category.toStableInfinityCategory.toSSet = perfectNerve P

/-- Its q-fold K input is the actual native interval-diagram diagonal. -/
def perfectKSpace {P : SmallPerfectModel A} (C : EnhancedPerfectInput P) (q : ℕ) :=
  multiSDiagonal C.category.toStableInfinityCategory q

/-- The whole coherent nerve of the given enriched perfect functor is retained. -/
def nativePerfectMap {P : SmallPerfectModel A} {Q : SmallPerfectModel B}
    (C : EnhancedPerfectInput P) (D : EnhancedPerfectInput Q)
    (F : EnrichedFunctor (Cochains k) P.category Q.category) :
    C.category.toStableInfinityCategory.toSSet ⟶ D.category.toStableInfinityCategory.toSSet :=
  eqToHom C.normalized ≫ dgNerveMap F ≫ eqToHom D.normalized.symm

/-- The exactness adapter concerns that same full native nerve map. -/
def IsExactPerfectMap {P : SmallPerfectModel A} {Q : SmallPerfectModel B}
    (C : EnhancedPerfectInput P) (D : EnhancedPerfectInput Q)
    (F : EnrichedFunctor (Cochains k) P.category Q.category) : Prop :=
  IsExact C.category.toStableInfinityCategory D.category.toStableInfinityCategory
    (nativePerfectMap C D F)

/-- The actual exact input is obtained without selecting an unrelated functor. -/
def exactPerfectMap {P : SmallPerfectModel A} {Q : SmallPerfectModel B}
    {C : EnhancedPerfectInput P} {D : EnhancedPerfectInput Q}
    {F : EnrichedFunctor (Cochains k) P.category Q.category} (h : IsExactPerfectMap C D F) :
    ExactFunctor C.category.toStableInfinityCategory D.category.toStableInfinityCategory :=
  ⟨nativePerfectMap C D F, h⟩

end MathlibExt.AlgebraicGeometry.EnhancedPerfKModels

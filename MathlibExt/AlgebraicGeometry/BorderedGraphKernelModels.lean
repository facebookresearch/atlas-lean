/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinarySheafOpenCuts
public import MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
public import MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Actual graph kernels for bordered operations

The graph space is the original closed graph closure in the two ambient
spaces. Its finite-interior open cut carries the native constant sheaf;
the cut and closed direct image supply the actual ordinary graph kernel.
Restricted Yoneda gives its original Ind object, and native single/Q
puts that exact object in the bounded derived category.

The projections are the original continuous projections of the actual
graph, with the source projection proper by the chosen bordered-map
condition. No addition on opposite infinite endpoints is used.

Source: D'Agnolo--Kashiwara1311.2374v2, Definitions3.2.1 and3.3.4.
Native constant sheaves, single complexes and Q are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorderedGraphKernelModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open BorderedRealSpaceModels CompactSupportIndSheaves IndSheafCoefficientModels
open OrdinarySheafOpenCuts IndSheafBoundedTensorModels

variable (B C : BorderedSpace) (f : BorderedMap B C)

/-- The specified product of the two original ambient spaces. -/
def ambientProduct : TopCat.{0} := TopCat.of (B.ambient × C.ambient)

/-- The actual closed graph closure, with its native subspace topology. -/
def closedGraphSpace : TopCat.{0} := TopCat.of (graphClosure B C f.map)

/-- The original continuous closed-graph embedding. -/
def graphEmbedding : closedGraphSpace B C f ⟶ ambientProduct B C :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- This embedding is genuinely closed and proper. -/
theorem graphEmbedding_proper : IsProperMap (graphEmbedding B C f) :=
  isClosed_closure.isProperMap_subtypeVal

/-- The original graph source projection. -/
def graphSource : closedGraphSpace B C f ⟶ B.ambient :=
  TopCat.ofHom ⟨fun p ↦ p.val.1, continuous_fst.comp continuous_subtype_val⟩

/-- The bordered condition is exactly properness of this actual source projection. -/
theorem graphSource_proper : IsProperMap (graphSource B C f) := f.proper

/-- The original graph target projection. -/
def graphTarget : closedGraphSpace B C f ⟶ C.ambient :=
  TopCat.ofHom ⟨fun p ↦ p.val.2, continuous_snd.comp continuous_subtype_val⟩

/-- The actual open where both graph coordinates are in the original finite interiors. -/
def graphInterior : Opens (closedGraphSpace B C f) :=
  ⟨{p | p.val.1 ∈ B.openSet ∧ p.val.2 ∈ C.openSet},
    (B.openSet.isOpen.preimage (continuous_fst.comp continuous_subtype_val)).inter
      (C.openSet.isOpen.preimage (continuous_snd.comp continuous_subtype_val))⟩

/-- The first actual ambient projection used by the graph-kernel formula. -/
def firstProjection : ambientProduct B C ⟶ B.ambient := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The second actual ambient projection used by the graph-kernel formula. -/
def secondProjection : ambientProduct B C ⟶ C.ambient := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

variable (k : Type) [Field k]
  [HasSheafify (Opens.grothendieckTopology (closedGraphSpace B C f)) (ModuleCat.{0} k)]

/-- The native constant coefficient sheaf on the original closed graph closure. -/
def graphConstant : OrdinarySheaf k (closedGraphSpace B C f) :=
  (constantSheaf (Opens.grothendieckTopology (closedGraphSpace B C f)) (ModuleCat.{0} k)).obj
    (ModuleCat.of k k)

/-- The actual ordinary graph coefficient kernel, extended by zero from its finite-interior graph. -/
def graphKernelSheaf [T2Space C.ambient] : OrdinarySheaf k (ambientProduct B C) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (graphEmbedding B C f)).obj
    ((ordinaryOpenCut k (closedGraphSpace B C f) (graphInterior B C f)).obj
      (graphConstant B C f k))

variable [T2Space C.ambient]

/-- The original graph coefficient object in the actual compact-support Ind category. -/
def graphKernelInd (S : OrdinaryIndSource k (ambientProduct B C)) : IndSheaf k (ambientProduct B C) :=
  (ordinaryToInd k (ambientProduct B C) S).obj (graphKernelSheaf B C f k)

variable [CompactSheafSource k (ambientProduct B C)]

local instance graphAbelianPreadditive : Preadditive (IndSheaf k (ambientProduct B C)) :=
  Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- The native single complex on the same graph coefficient object. -/
def graphKernelComplex (S : OrdinaryIndSource k (ambientProduct B C)) :
    CochainComplex (IndSheaf k (ambientProduct B C)) ℤ :=
  (HomologicalComplex.single (IndSheaf k (ambientProduct B C)) (.up ℤ) 0).obj
    (graphKernelInd B C f k S)

/-- That original graph complex is literally supported in degree zero. -/
theorem graphKernelComplex_bounded (S : OrdinaryIndSource k (ambientProduct B C)) :
    termwiseBounded k (ambientProduct B C) (graphKernelComplex B C f k S) := by
  refine ⟨0, 0, ?_⟩
  intro n hn
  exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (graphKernelInd B C f k S) n (by omega)

/-- The original bounded-cochain graph object, retaining all original single-complex maps. -/
def boundedGraphKernelComplex (S : OrdinaryIndSource k (ambientProduct B C)) :
    BoundedIndComplex k (ambientProduct B C) :=
  ⟨graphKernelComplex B C f k S, graphKernelComplex_bounded B C f k S⟩

/-- The actual bounded derived graph coefficient kernel is the original bounded Q image. -/
def graphKernel (S : OrdinaryIndSource k (ambientProduct B C))
    (R : BoundedCohomologySource k (ambientProduct B C)) : BoundedIndDerived k (ambientProduct B C) :=
  (boundedQ k (ambientProduct B C) R).obj (boundedGraphKernelComplex B C f k S)

end MathlibExt.AlgebraicGeometry.BorderedGraphKernelModels

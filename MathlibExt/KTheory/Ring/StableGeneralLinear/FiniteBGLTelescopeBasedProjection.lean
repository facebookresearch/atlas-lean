/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeProjectionWeakEquivalence
public import MathlibExt.Topology.Category.TopCat.RealizedBasedWhitehead

/-!
# Based inverse data for the original finite-GL telescope projection

The forward map is the original telescope-to-stable-BGL realization.
Filtered right-comma contractibility proves that it is weak. The existing
based Whitehead construction then supplies an inverse and both whole
homotopies fixed at the original vertices. No comparison with a chosen
Q/plus inverse or caller equivalence is used.

This is an ordinary ring-carrier source. Native and probe transports are
subsequent maps; no probe universe is attached to a plain TopCat carrier.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe u

namespace AlgebraicKTheory.StableGL

/-- The original ordinary projection is weak in every ring-carrier universe. -/
public theorem ordinaryFiniteBGLTelescopeToBGL_mem_weakHomotopyEquivalences
    (R : Type u) [Semiring R] :
    TopCat.weakHomotopyEquivalences (ordinaryFiniteBGLTelescopeToBGL R) := by
  exact (TopCat.mem_weakHomotopyEquivalences_iff _).mpr
    ((SSet.mem_realizationWeakEquivalences_iff _).mp
      (finiteBGLTelescopeNerveToStableNerve_mem_realizationWeakEquivalences R))

/-- Both inverse families and the equivalence retain the literal projection.
The inverse is output data constructed from the actual weak map. -/
public structure FiniteBGLTelescopeBasedProjection (R : Type u) [Semiring R] where
  /-- The based inverse of the original ordinary telescope projection. -/
  inverse : ordinaryBGL R ⟶ ordinaryFiniteBGLTelescope R
  inverse_point :
    inverse (ordinaryBGLBasepoint R) = ordinaryFiniteBGLTelescopeBasepoint R
  /-- The complete left inverse homotopy fixed at the original telescope basepoint. -/
  left : ContinuousMap.HomotopyRel
    (ordinaryFiniteBGLTelescopeToBGL R ≫ inverse).hom
    (ContinuousMap.id (ordinaryFiniteBGLTelescope R))
      {ordinaryFiniteBGLTelescopeBasepoint R}
  /-- The complete right inverse homotopy fixed at the original BGL basepoint. -/
  right : ContinuousMap.HomotopyRel
    (inverse ≫ ordinaryFiniteBGLTelescopeToBGL R).hom
    (ContinuousMap.id (ordinaryBGL R)) {ordinaryBGLBasepoint R}
  /-- The homotopy equivalence with the original projection and the same based inverse. -/
  equivalence : ordinaryFiniteBGLTelescope R ≃ₕ ordinaryBGL R
  forward_eq : equivalence.toFun = (ordinaryFiniteBGLTelescopeToBGL R).hom
  backward_eq : equivalence.invFun = inverse.hom

/-- Based inverse data are derived internally from the original projection. -/
public def finiteBGLTelescopeBasedProjection (R : Type u) [Semiring R] :
    FiniteBGLTelescopeBasedProjection R := by
  let x := finiteBGLTelescopeBaseVertex R
  let y := classifyingVertex R
  let f : SSet.toTop.obj (finiteBGLTelescopeNerve R) ⟶
      SSet.toTop.obj (classifyingNerve R) := ordinaryFiniteBGLTelescopeToBGL R
  have hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y :=
    ordinaryFiniteBGLTelescopeToBGL_basepoint R
  have hf : TopCat.weakHomotopyEquivalences f :=
    ordinaryFiniteBGLTelescopeToBGL_mem_weakHomotopyEquivalences R
  exact
    { inverse := TopCat.realizedBasedHomotopyInverse x y f hxy hf
      inverse_point := TopCat.realizedBasedHomotopyInverse_point x y f hxy hf
      left := TopCat.realizedBasedLeftHomotopy x y f hxy hf
      right := TopCat.realizedBasedRightHomotopy x y f hxy hf
      equivalence := TopCat.realizedBasedHomotopyEquiv x y f hxy hf
      forward_eq := TopCat.realizedBasedHomotopyEquiv_toFun x y f hxy hf
      backward_eq := TopCat.realizedBasedHomotopyEquiv_invFun x y f hxy hf }

end AlgebraicKTheory.StableGL

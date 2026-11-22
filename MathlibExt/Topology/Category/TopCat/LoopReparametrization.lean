/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Category.TopCat.Basic
public import MathlibExt.Topology.Category.TopCat.EndpointFixedCorrection
public import MathlibExt.Topology.Homotopy.PathReparametrization

/-!
# Continuous reparameterization of the original based loop space

Every endpoint-preserving continuous interval map acts on the actual
compact-open loop space. Affine interpolation with the identity gives a
homotopy to the original loop. The start-pause parameter records the
constant first half introduced by concatenating a constant path.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

namespace TopCat

/-- Apply an endpoint-preserving parameter to every original based loop. -/
@[expose]
def loopReparamMap (B : TopCat.{u}) (b : B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    TopCat.of (LoopSpace B b) ⟶ TopCat.of (LoopSpace B b) :=
  TopCat.ofHom (ContinuousMap.pathReparamMap (a := b) (b := b) r hr hr0 hr1)

/-- Reparameterization retains every value of the original loop. -/
theorem loopReparamMap_apply (B : TopCat.{u}) (b : B)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (gamma : LoopSpace B b) (t : unitInterval) :
    loopReparamMap B b r hr hr0 hr1 gamma t = gamma (r t) :=
  ContinuousMap.pathReparamMap_apply r hr hr0 hr1 gamma t

/-- The full affine parameter family gives a homotopy to the original loop map. -/
def loopReparamHomotopy (B : TopCat.{u}) (b : B)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    ContinuousMap.Homotopy (loopReparamMap B b r hr hr0 hr1).hom
      (ContinuousMap.id (LoopSpace B b)) :=
  ContinuousMap.pathReparamMapHomotopy (a := b) (b := b) r hr hr0 hr1

/-- The actual affine reparameterization homotopy fixes the literal constant loop
at every time. -/
theorem loopReparamHomotopy_fixed_constant_loop (B : TopCat.{u}) (b : B)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) (s : unitInterval) :
    loopReparamHomotopy B b r hr hr0 hr1 (s, Path.refl b) = Path.refl b := by
  apply Path.ext
  funext t
  exact ContinuousMap.pathReparamMapHomotopy_apply r hr hr0 hr1 (Path.refl b) s t

end TopCat

end

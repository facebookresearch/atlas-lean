/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels

/-!
# Relative Čech and matching source construction

Levels and every map are the actual native relative products, and
matching objects are native limits of lower-degree simplex maps.
The arc condition concerns these already fixed matching maps.

Source: Bhatt--Mathew1807.04725v4, Theorems5.13/5.16.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneralArcCoverModels

/-- Native finite relative products assemble the original cover's full Čech simplicial object. -/
def_wanted native_qcqs_cech {X Y : QcqsScheme} (f : Y ⟶ X) [HasFiniteProducts (Over X)] : CechSource f

/-- The actual lower-degree relative matching limits exist for every degree of a qcqs simplicial over-object. -/
def_wanted native_qcqs_matching_limits {X : QcqsScheme} (H : SimplicialObject (Over X)) :
  ∀ n : ℕ, HasLimit (matchingDiagram H n)

end MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels

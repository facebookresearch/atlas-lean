/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

/-!
# Assembling the original finite Cartier duals

Tate, p-divisible groups (1967); Scholze--Weinstein,
arXiv:1211.6357v2, Sections 1--3.3. This is the native geometric tower
assembly of completed finite dualization. Both inclusions and divisions
are fixed by the original source arrows. No finite Cartier duality,
generic Tate inverse limit or abstract point-group construction is requested.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleCartierTower

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

/-- Assemble the original finite duals with their displayed source-induced arrows. -/
public def_wanted geometricCartierDualTower
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) : CartierDualTower p R G

end WantedExt.AlgebraicGeometry.PDivisibleCartierTower

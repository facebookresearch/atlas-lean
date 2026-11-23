/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies

/-!
# Tests for log-Fano fibres of DVR models

A log-Fano fibre needs a boundary ideal whose restriction to the special fibre is nonzero: the
zero ideal, like the ideal of the special fibre itself, has none.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The zero ideal has no restriction to the special fibre, so it is not a log-Fano boundary. -/
example {X : CategoryTheory.Over (Spec (.of R))} {L : X.left.Modules} {n e : ℕ}
    (F : LogFanoFibre X L ⊥ n e) : False :=
  F.boundaryRestricts (Scheme.IdealSheafData.comap_bot _)

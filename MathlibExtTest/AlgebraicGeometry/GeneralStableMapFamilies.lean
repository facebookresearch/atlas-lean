/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

noncomputable section
open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

/-- All genera and marking counts support the constant target map; no
projective-space or degree-one datum is required by the general carrier. -/
private def constantFamily {S : Scheme.{0}} {n g : ℕ} (C : MarkedFamily S n g) :
    Family (𝟙 S) n g S (𝟙 S) := ⟨C, C.π, by simp⟩

example {S : Scheme.{0}} {n g : ℕ} (C : MarkedFamily S n g) (i : Fin n) :
    evaluation (constantFamily C) i = 𝟙 S := C.section_eq i

/-- Source isomorphisms preserve all geometric evaluation maps. -/
example {V S T : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} {b : T ⟶ S}
    {F G : Family q n g T b} (e : F ⟶ G) (i : Fin n) :
    evaluation F i = evaluation G i := evaluation_eq_of_hom F e i

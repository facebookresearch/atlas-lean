/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogarithmicGeometryAssociatedLogUnitCondition

/-!
# Tests for the associated log unit condition

The associated prelog has a unique unit-sheaf map compatible with its
structure map.

Sources: Kato, *Logarithmic structures of Fontaine--Illusie*, §1;
Nakayama--Ogus, *Relative rounding in toric and logarithmic geometry*,
Definition 3.4 and the following associated-log/chart construction,
https://math.berkeley.edu/~ogus/preprints/nakayamaogus.pdf;
Achinger--Ogus, *Monodromy and log geometry*, §3.1,
https://arxiv.org/abs/1802.02234.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.LogarithmicGeometryAssociatedLogUnitCondition

open CategoryTheory MathlibExt.AlgebraicGeometry.LogStructures
open WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted

universe u v

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (P : Prelog J O) :
    ∃! f : units J O ⟶ (associatedPrelog J P).left,
      f ≫ (associatedPrelog J P).hom = unitInclusion J O := by
  let L : LogStructure J O :=
    ⟨associatedPrelog J P, associated_log_unit_condition J O P⟩
  refine ⟨unitMap J L, unitMap_alpha J L, ?_⟩
  intro f hf
  simpa only [Category.id_comp] using
    factorThroughUnits J L f (𝟙 _) (by simpa using hf)

end MathlibExtTest.AlgebraicGeometry.LogarithmicGeometryAssociatedLogUnitCondition

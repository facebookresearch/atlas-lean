/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Whole native horn-face chart colimits

Mathlib's actual original horn-face/intersection multicoequalizer is
retained with the original omitted-face index. Minimal markings and
the exact base simplex lift the same colimit to the native slice;
native straightening transports it through the original adjunction.
No relative cell-left membership follows without its separate proof.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual full original horn faces form their genuine minimally marked same-base slice colimit, with every
original intersection retained. -/
def nativeHornFaceIsColimit (B : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) (σ : B _⦋n⦌) :
    IsColimit ((nativeSubcomplexBasisFunctor B n σ).mapCocone
      (horn.multicoequalizerDiagram i).multicofork.toLinearOrder) :=
  nativeSubcomplexIsColimit B n σ (horn.multicoequalizerDiagram i).multicofork.toLinearOrder
    ((Multicofork.isColimitMapEquiv _ _).symm (horn.isColimit i))

/-- Every whole native original horn chart is the actual marked face/intersection chart colimit at its unchanged
omitted-face index and base simplex. -/
def nativeHornChartFaceIsColimit (B : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) (σ : B _⦋n⦌) :
    IsColimit ((nativeSubcomplexChartFunctor B n σ).mapCocone
      (horn.multicoequalizerDiagram i).multicofork.toLinearOrder) :=
  nativeSubcomplexChartIsColimit B n σ (horn.multicoequalizerDiagram i).multicofork.toLinearOrder
    ((Multicofork.isColimitMapEquiv _ _).symm (horn.isColimit i))

end SSet.Marked

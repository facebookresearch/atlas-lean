/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The actual original point marking isomorphism

Both original zero-simplex markings are terminal marked objects. Their
whole original marked isomorphism has the unchanged underlying
identity in both directions and retains the actual original source
base coefficient. No higher-dimensional marking is identified.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The SAME original minimally and maximally marked point have their actual whole marked isomorphism. -/
def minimumMaximumPointIso : min (Δ[0] : SSet.{u}) ≅ max (Δ[0] : SSet.{u}) :=
  (parameterZeroIsTerminal .minimal).uniqueUpToIso (parameterZeroIsTerminal .maximal)

/-- Its original forward marked map is exactly the underlying identity on the original point. -/
theorem minimumMaximumPointIso_hom : (minimumMaximumPointIso.{u}).hom =
    (toMax (𝟙 (Δ[0] : SSet.{u})) : min (Δ[0] : SSet.{u}) ⟶ max (Δ[0] : SSet.{u})) :=
  (parameterZeroIsTerminal .maximal).hom_ext _ _

/-- The entire original inverse point map keeps precisely the same original underlying identity. -/
theorem minimumMaximumPointIso_inv_hom : (minimumMaximumPointIso.{u}).inv.hom = 𝟙 (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original marked point isomorphism keeps the supplied whole original base coefficient and both original
source markings. -/
def nativePointMarkingIso (B : SSet.{u}) (σ : B _⦋0⦌) :
    Over.mk (toMax (SSet.yonedaEquiv.symm σ) : min (Δ[0] : SSet.{u}) ⟶ max B) ≅
      Over.mk (toMax (SSet.yonedaEquiv.symm σ) : max (Δ[0] : SSet.{u}) ⟶ max B) := by
  refine Over.isoMk minimumMaximumPointIso ?_
  rw [minimumMaximumPointIso_hom]
  apply Hom.ext
  exact Category.id_comp (SSet.yonedaEquiv.symm σ)

/-- The whole original point over-isomorphism has precisely its unchanged original marked point map. -/
theorem nativePointMarkingIso_hom_left (B : SSet.{u}) (σ : B _⦋0⦌) :
    (nativePointMarkingIso B σ).hom.left =
      (toMax (𝟙 (Δ[0] : SSet.{u})) : min (Δ[0] : SSet.{u}) ⟶ max (Δ[0] : SSet.{u})) :=
  minimumMaximumPointIso_hom

end SSet.Marked

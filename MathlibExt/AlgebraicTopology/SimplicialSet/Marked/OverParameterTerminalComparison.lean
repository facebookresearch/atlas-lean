/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterLeibniz
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Original terminal-target relative mapping comparisons

The actual parameter adjunction preserves the original terminal slice
object in its mapping variable. The native pullback comparison against a
terminal target is therefore the original relative source restriction,
through the actual first-projection isomorphism. All original prisms,
base points and lifting squares are retained, without base fibrancy or
a marked-model assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The original terminal object in the marked slice gives a terminal native relative mapping complex. -/
def overParameterMappingTerminal (Z : Marked.{u}) (X : Over Z) :
    IsTerminal (relativeMappingComplex .maximal X.hom (𝟙 Z)) := by
  let G : Over Z ⥤ SSet.{u} := overTargetMappingFunctor .maximal Z X
  let _ : PreservesLimitsOfSize.{0, 0} G := (overParameterAdjunction Z X).rightAdjoint_preservesLimits
  let _ : PreservesLimit (Functor.empty (Over Z)) G :=
    (inferInstance : PreservesLimitsOfShape (Discrete PEmpty) G).preservesLimit
  exact (Over.mkIdTerminal (X := Z)).isTerminalObj G (Over.mk (𝟙 Z))

/-- The actual terminal-target pullback first projection is an isomorphism on the whole original relative
  mapping complex. -/
theorem overParameterMappingPullback_terminal_fst_isIso {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) (E : Over Z) :
    IsIso (overParameterMappingPullback f (Over.mkIdTerminal.from E)).fst := by
  let p := Over.mkIdTerminal.from E
  let T := Over.mk (𝟙 Z)
  let t : relativeMappingComplex .maximal Y.hom (𝟙 Z) ⟶ relativeMappingComplex .maximal X.hom (𝟙 Z) :=
    relativeMappingPre .maximal f.left Y.hom X.hom (𝟙 Z) (Over.w f)
  let _ : IsIso t := isIso_of_isTerminal (overParameterMappingTerminal Z Y)
    (overParameterMappingTerminal Z X) t
  exact (overParameterMappingPullback f p).isPullback.isIso_fst_of_isIso (inst := (inferInstanceAs (IsIso t)))

/-- The original terminal-target mapping comparison is the literal source restriction through its actual
  pullback-point isomorphism. -/
def overParameterMappingComparisonTerminalIso {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) (E : Over Z) :
    Arrow.mk (overParameterMappingComparison f (Over.mkIdTerminal.from E)) ≅
      Arrow.mk ((overMappingFunctor .maximal Z E).map f.op) := by
  let sq := overParameterMappingPullback f (Over.mkIdTerminal.from E)
  let π : relativeMappingComplex .maximal Y.hom E.hom ⟶ sq.pt := sq.π
  let a : sq.pt ⟶ relativeMappingComplex .maximal X.hom E.hom := sq.fst
  let t : relativeMappingComplex .maximal Y.hom E.hom ⟶ relativeMappingComplex .maximal X.hom E.hom :=
    (overMappingFunctor .maximal Z E).map f.op
  let hA : IsIso a := overParameterMappingPullback_terminal_fst_isIso f E
  let e : sq.pt ≅ relativeMappingComplex .maximal X.hom E.hom := @asIso _ _ _ _ a hA
  have h : π ≫ a = t := sq.π_fst
  exact Arrow.isoMk (Iso.refl _) e ((Category.id_comp t).trans h.symm)

/-- Original terminal-target boundary lifting tests are exactly the same native relative source restriction
  boundary tests. -/
theorem overParameterBoundary_terminal_lifting_iff {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) (E : Over Z) :
    (∀ n : ℕ, HasLiftingProperty
      (overParameterPushoutProduct (boundary.{u} n).ι f) (Over.mkIdTerminal.from E)) ↔
      modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal Z E).map f.op) := by
  exact (overParameterBoundary_lifting_iff f (Over.mkIdTerminal.from E)).trans
    (modelCategoryQuillen.I.rlp.arrow_iso_iff (overParameterMappingComparisonTerminalIso f E))

end SSet.Marked

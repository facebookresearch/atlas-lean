/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridNerve
public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQProjectionEquivalence

/-!
# The retained-Q projection is a realization weak equivalence

Every strict retained-Q fiber has an initial object: choose any fiber object,
use the direct C1 fiber morphism as its map to every other object, and use
thinness of the fiber category for uniqueness.  The generic initial-object
nerve theorem then makes its terminal nerve map a realization weak
equivalence.

Degreewise, the retained-Q projection is an equivalence of categories, so its
nerve map is a realization weak equivalence.  The rowwise-to-diagonal theorem
gives the corresponding diagonal result.  Postcomposition with the canonical
isomorphism from the discrete-Q diagonal to `NQ` produces the literal Q-side
comparison and proves that it is a realization weak equivalence.

This file introduces no grid-to-Stage map, outer-edgewise comparison,
Theorem A or B, pointed or loop-space map, spectrum statement, full Q/S
comparison, or naturality in exact functors.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure used by the original retained-Q weak comparison. -/
local instance quillenStageGridQProjectionWeakEquivalenceWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

namespace QuillenStageGridFiber

/-- A strict retained-Q fiber is weakly contractible when the canonical map
from its nerve to the chosen terminal simplicial set is a realization weak
equivalence. -/
def WeaklyContractible {a : SimplexCategory}
    (q : QuillenQSimplex C a) : Prop :=
  SSet.realizationWeakEquivalences
    (terminal.from (CategoryTheory.nerve (QuillenStageGridFiber q)))

end QuillenStageGridFiber

/-- Every strict retained-Q fiber has weakly contractible realized nerve. -/
theorem quillenStageGridFiber_weaklyContractible
    {a : SimplexCategory} (q : QuillenQSimplex C a) :
    QuillenStageGridFiber.WeaklyContractible q := by
  obtain ⟨X⟩ := quillenStageGridFiber_nonempty q
  let hX : IsInitial X := IsInitial.ofUniqueHom
    (fun Y => (quillenStageGridFiber_hom_nonempty X Y).some)
    (by
      intro Y f
      exact (quillenStageGridFiber_hom_subsingleton q X Y).allEq _ _)
  exact
    NerveContractible.terminal_from_mem_realizationWeakEquivalences_of_isInitial hX

/-- In each outer degree, the nerve map of the retained-Q projection is a
realization weak equivalence. -/
theorem quillenStageGridQProjectionNerve_app_mem_realizationWeakEquivalences
    (a : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences
      ((quillenStageGridQProjectionNerve (C := C)).app a) := by
  rw [quillenStageGridQProjectionNerve_app]
  let _ : (quillenStageGridQProjection C a.unop).IsEquivalence :=
    quillenStageGridQProjectionIsEquivalence C a.unop
  exact
    CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence _

/-- The diagonal retained-Q projection is a realization weak equivalence. -/
theorem quillenStageGridQProjectionDiagonal_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (quillenStageGridQProjectionDiagonal (C := C)) := by
  change SSet.realizationWeakEquivalences
    (SSet.simplicialDiagonalFunctor.map
      (quillenStageGridQProjectionNerve (C := C)))
  apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
  intro n
  exact quillenStageGridQProjectionNerve_app_mem_realizationWeakEquivalences
    (C := C) (op (SimplexCategory.mk n))

/-- The Q-side comparison from the diagonal Stage-grid nerve to the ordinary
Quillen Q-nerve.  It is literally the retained-Q diagonal projection followed
by the canonical discrete-diagonal isomorphism. -/
noncomputable def quillenStageGridToNQ :
    quillenStageGridDiagonal C ⟶ NQ C :=
  quillenStageGridQProjectionDiagonal (C := C) ≫
    (quillenQSimplexDiscreteDiagonalIso (C := C)).hom

/-- The Q-side Stage-grid comparison is a realization weak equivalence. -/
theorem quillenStageGridToNQ_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (quillenStageGridToNQ (C := C)) := by
  change SSet.realizationWeakEquivalences
    (quillenStageGridQProjectionDiagonal (C := C) ≫
      (quillenQSimplexDiscreteDiagonalIso (C := C)).hom)
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    quillenStageGridQProjectionDiagonal_mem_realizationWeakEquivalences
    (SSet.realizationWeakEquivalences.of_isIso _)

end AlgebraicKTheory

end

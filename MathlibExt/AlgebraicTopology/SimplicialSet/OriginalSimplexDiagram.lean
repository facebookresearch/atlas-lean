/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexIndexNerveSpan

/-!
# The SAME original full standard-simplex diagram augmentation

Every original simplex retains its actual entire standard-simplex
coefficient and map. The canonical identity pullback projection gives
both full inverse coefficient directions. The proved original simplex
resolution augmentation supplies weakness of this same direct diagram.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits
open scoped Simplicial

namespace SSet

/-- The entire original diagram of standard simplices over the same original input. -/
def originalSimplexDiagram (K : SSet.{u}) : SimplexIndex K ⥤ SSet.{u} :=
  CostructuredArrow.proj SSet.stdSimplex K ⋙ SSet.stdSimplex

/-- Every original simplex contributes its SAME entire original input map. -/
def originalSimplexCocone (K : SSet.{u}) :
    originalSimplexDiagram K ⟶ (CategoryTheory.Functor.const (SimplexIndex K)).obj K where
  app s := s.hom
  naturality s t f := by
    have h : SSet.stdSimplex.map f.left ≫ t.hom = s.hom := CostructuredArrow.w f
    exact h.trans (Category.comp_id _).symm

/-- The same full original identity-pullback projection gives both actual inverse standard-simplex coefficient
directions. -/
def originalSimplexPullbackComponentIso (K : SSet.{u}) (s : SimplexIndex K) :
    (simplexPullbackDiagram (𝟙 K)).obj s ≅ (originalSimplexDiagram K).obj s := by
  change pullback (𝟙 K) s.hom ≅ SSet.stdSimplex.obj s.left
  exact asIso (pullback.snd (𝟙 K) s.hom)

/-- The actual original identity pullback has both full inverse coefficient directions to the SAME original direct
standard-simplex diagram. -/
def originalSimplexPullbackIso (K : SSet.{u}) :
    simplexPullbackDiagram (𝟙 K) ≅ originalSimplexDiagram K :=
  NatIso.ofComponents (originalSimplexPullbackComponentIso K)
    (by intro s t f; exact simplexPullbackDiagram_map_snd (𝟙 K) f)

/-- The SAME full original standard-simplex BK augmentation. -/
def originalSimplexAugmentation (K : SSet.{u}) : bkHocolim (originalSimplexDiagram K) ⟶ K :=
  bkAugmentation (originalSimplexCocone K)

/-- The SAME original full standard-simplex augmentation is weak for every original simplicial input. -/
theorem originalSimplexAugmentation_weak (K : SSet.{u}) :
    realizationWeakEquivalences (originalSimplexAugmentation K) := by
  let e := originalSimplexPullbackIso K
  have hMap := bkHocolimMap_weak_universes e.hom (fun s => realizationWeakEquivalences.of_isIso (e.hom.app s))
  have hSquare := bkAugmentation_naturality e.hom (simplexPullbackCocone (𝟙 K))
    (originalSimplexCocone K) (𝟙 K) (fun s => by
      change pullback.snd (𝟙 K) s.hom ≫ s.hom = pullback.fst (𝟙 K) s.hom ≫ 𝟙 K
      exact pullback.condition.symm)
  have hComposite : realizationWeakEquivalences (bkHocolimMap e.hom ≫ originalSimplexAugmentation K) :=
    (hSquare.trans (Category.comp_id _)).symm ▸ originalSimplexIndexAugmentation_weak K
  exact realizationWeakEquivalences.of_precomp _ _ hMap hComposite

/-- Every original standard-simplex coefficient has its actual original weak point map. -/
theorem originalSimplexDiagram_point_weak (K : SSet.{u}) (s : SimplexIndex K) :
    realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from ((originalSimplexDiagram K).obj s)) :=
  SSet.stdSimplex_to_point_mem_realizationWeakEquivalences s.left

end SSet

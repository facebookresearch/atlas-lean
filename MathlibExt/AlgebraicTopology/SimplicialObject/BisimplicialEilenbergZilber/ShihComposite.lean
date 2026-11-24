/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihFormula
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneSurvivor

/-!
# The degreewise bisimplicial Alexander--Whitney--shuffle composite

This file writes the composite of the bisimplicial Alexander--Whitney and
shuffle chain maps as the explicit double sum indexed by a cut and a shuffle.
The simplex endomorphisms are the existing `awShuffleLeftHom` and
`awShuffleRightHom`; only their evaluation through `Bisimplicial.map` is new.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- One cut-and-shuffle summand in the degreewise
Alexander--Whitney--shuffle composite. -/
noncomputable def awShuffleDiagonalSummand (n : ℕ) (p : Fin (n + 1))
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p (n - (p : ℕ))) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
    AlgebraicTopology.Bisimplicial.map B
      (AlgebraicTopology.EilenbergZilber.awShuffleLeftHom n p s)
      (AlgebraicTopology.EilenbergZilber.awShuffleRightHom n p s)

/-- The full degreewise bisimplicial Alexander--Whitney--shuffle sum. -/
noncomputable def awShuffleDiagonalComponent (n : ℕ) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  ∑ p : Fin (n + 1),
    ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p (n - (p : ℕ)),
      awShuffleDiagonalSummand B n p s

/-- The front-degree-zero part of the degreewise composite. -/
noncomputable def awShuffleZeroComponent (n : ℕ) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle 0 n,
    awShuffleDiagonalSummand B n 0 s

omit [Limits.HasCountableCoproducts A] in
/-- The equality-indexed Alexander--Whitney face map is the generic
bisimplicial map induced by the front and back inclusions. -/
theorem faceToBidegreeOfEq_eq_map
    (p q n : ℕ) (h : p + q = n) :
    AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq B p q n h =
      AlgebraicTopology.Bisimplicial.map B
        (AlgebraicTopology.AlexanderWhitney.frontInclusion p q n h)
        (AlgebraicTopology.AlexanderWhitney.backInclusion p q n h) := by
  rfl

/-- The degree-`n` component of the Alexander--Whitney map followed by the
shuffle map is the explicit cut-and-shuffle double sum. -/
theorem alternatingMap_comp_f_eq_awShuffleDiagonalComponent (n : ℕ) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B ≫
        alternatingMap B).f n = awShuffleDiagonalComponent B n := by
  simp only [HomologicalComplex.comp_f,
    AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap_f,
    alternatingMap_f]
  rw [AlgebraicTopology.BisimplicialAlexanderWhitney.component_eq_sum]
  rw [Preadditive.sum_comp]
  unfold awShuffleDiagonalComponent
  apply Finset.sum_congr rfl
  intro p _
  unfold AlgebraicTopology.BisimplicialAlexanderWhitney.summand
  unfold AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
  rw [Category.assoc, totalι_comp_component]
  unfold shuffleBidegree
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  unfold awShuffleDiagonalSummand shuffleSummand
  rw [Preadditive.comp_zsmul]
  unfold shuffleMap
  rw [faceToBidegreeOfEq_eq_map]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  let h : (p : ℕ) + (n - (p : ℕ)) = n := by omega
  rw [← AlgebraicTopology.Bisimplicial.map_eqToHom B h.symm h.symm]
  rw [Preadditive.zsmul_comp]
  congr 1
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  unfold AlgebraicTopology.EilenbergZilber.awShuffleLeftHom
    AlgebraicTopology.EilenbergZilber.awShuffleRightHom
  rfl

end AlgebraicTopology.BisimplicialEilenbergZilber

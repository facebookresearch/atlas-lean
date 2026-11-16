/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels
public import MathlibExtTest.AlgebraicTopology.CategoricalSectionsModels

/-!
# The left slice retains an actual noninvertible arrow

The triangle 0→0→1 gives the arrow from id₀ to 0→1 in the
left slice of nerve(Fin2). Projection gives the original 0→1;
passing to a groupoid core or deleting the wrong vertex fails this test.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicTopology.SimplicialCovariantModels

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open scoped Simplicial

def base := nerve (Fin 2)

def point : base _⦋0⦌ := ComposableArrows.mk₀ (0 : Fin 2)

def source : (leftSlice base point) _⦋0⦌ :=
  ⟨ComposableArrows.mk₁ (𝟙 (0 : Fin 2)), rfl⟩

def target : (leftSlice base point) _⦋0⦌ :=
  ⟨ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide)), rfl⟩

def forward : (leftSlice base point) _⦋1⦌ :=
  ⟨ComposableArrows.mk₂ (𝟙 (0 : Fin 2))
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide)), rfl⟩

theorem forward_source : (leftSlice base point).δ 1 forward = source := by
  apply Subtype.ext
  change (ComposableArrows.mk₂ (𝟙 (0 : Fin 2))
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).whiskerLeft
      (SimplexCategory.toCat.map (prepend.map (SimplexCategory.δ (1 : Fin 2)))).toFunctor =
    ComposableArrows.mk₁ (𝟙 (0 : Fin 2))
  refine ComposableArrows.ext (n := 1) (fun i => ?_) (fun i hi => ?_)
  · fin_cases i <;> rfl
  · apply Subsingleton.elim

theorem forward_target : (leftSlice base point).δ 0 forward = target := by
  apply Subtype.ext
  change (ComposableArrows.mk₂ (𝟙 (0 : Fin 2))
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).whiskerLeft
      (SimplexCategory.toCat.map (prepend.map (SimplexCategory.δ (0 : Fin 2)))).toFunctor =
    ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
  refine ComposableArrows.ext (n := 1) (fun i => ?_) (fun i hi => ?_)
  · fin_cases i <;> rfl
  · apply Subsingleton.elim

theorem projection_forward :
    (targetProjection base point).app (op ⦋1⦌) forward =
      MathlibExtTest.AlgebraicTopology.CategoricalSectionsModels.forward := rfl

theorem projection_not_equivalence :
    ¬ IsEquivalenceEdge base ((targetProjection base point).app (op ⦋1⦌) forward) := by
  rw [projection_forward]
  exact MathlibExtTest.AlgebraicTopology.CategoricalSectionsModels.forward_not_equivalence

end MathlibExtTest.AlgebraicTopology.SimplicialCovariantModels

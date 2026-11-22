/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinatePairs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerLowerRootInverseGluing

/-!
# Genuine original lower inverse gluing on every full coordinate pair

The whole marked ordered positive lower/lower source theorem covers
every distinct ordered pair through its original ordinal labels.
Original marked coordinate swap retains both projections, giving all
reversed pairs. Diagonal pairs retain the identical original projection.
The dimension-one case has its single actual positive original vertex.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same genuine lower inverse maps agree on every entire original marked lower/lower root pair, including all
orders, swaps, diagonal pairs and dimensions, over every original base. -/
theorem nativeRootLowerPair_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (j k : Fin (n + 2)) (hj : 0 < j) (hk : 0 < k) :
    coneRootCoordinatePairLeft n (coneRootLowerIndex n j hj) (coneRootLowerIndex n k hk) ≫
      nativeLowerRootBoundaryInverse B σ j hj =
      coneRootCoordinatePairRight n (coneRootLowerIndex n j hj) (coneRootLowerIndex n k hk) ≫
        nativeLowerRootBoundaryInverse B σ k hk := by
  cases n with
  | zero =>
    have hj₀ : 0 < j.val := hj
    have hk₀ : 0 < k.val := hk
    have hj₁ : j.val = 1 := le_antisymm (Nat.le_of_lt_succ j.is_lt) (Nat.succ_le_of_lt hj₀)
    have hk₁ : k.val = 1 := le_antisymm (Nat.le_of_lt_succ k.is_lt) (Nat.succ_le_of_lt hk₀)
    have h : j = k := Fin.ext (hj₁.trans hk₁.symm)
    subst k
    apply Hom.ext
    rfl
  | succ n =>
    have ascending (x y : Fin (n + 3)) (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
        coneRootCoordinatePairLeft (n + 1) (coneRootLowerIndex (n + 1) x hx) (coneRootLowerIndex (n + 1) y hy) ≫
          nativeLowerRootBoundaryInverse B σ x hx =
          coneRootCoordinatePairRight (n + 1) (coneRootLowerIndex (n + 1) x hx) (coneRootLowerIndex (n + 1) y hy) ≫
            nativeLowerRootBoundaryInverse B σ y hy := by
      rcases x with ⟨x, hxBound⟩
      have hxy₀ : x < y.val := hxy
      have hy₀ : y.val ≤ n + 2 := Nat.le_of_lt_succ y.is_lt
      let x' : Fin (n + 2) := ⟨x, lt_of_lt_of_le hxy₀ hy₀⟩
      have hx' : 0 < x' := hx
      change coneLowerLowerRootFaceLeft (⟨x, hxBound⟩ : Fin (n + 3)) y ≫
        nativeLowerRootBoundaryInverse B σ (⟨x, hxBound⟩ : Fin (n + 3)) hx =
          coneLowerLowerRootFaceRight (⟨x, hxBound⟩ : Fin (n + 3)) y ≫ nativeLowerRootBoundaryInverse B σ y hy
      exact nativeLowerLowerRootInverse_condition B n σ x' y hxy hx'
    rcases lt_trichotomy j k with h | h | h
    · exact ascending j k hj hk h
    · subst k
      apply Hom.ext
      rfl
    · let a := coneRootLowerIndex.{u} (n + 1) j hj
      let b := coneRootLowerIndex.{u} (n + 1) k hk
      let e := coneRootCoordinatePairSwapIso (n + 1) a b
      let f := nativeLowerRootBoundaryInverse B σ j hj
      let g := nativeLowerRootBoundaryInverse B σ k hk
      have h₀ := ascending k j hk hj h
      have hs : e.hom ≫ (coneRootCoordinatePairLeft (n + 1) b a ≫ g) =
          e.hom ≫ (coneRootCoordinatePairRight (n + 1) b a ≫ f) := congrArg (fun q => e.hom ≫ q) h₀
      have hl : e.hom ≫ (coneRootCoordinatePairLeft (n + 1) b a ≫ g) = coneRootCoordinatePairRight (n + 1) a b ≫ g :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ g) (coneRootCoordinatePairSwapIso_left (n + 1) a b))
      have hr : e.hom ≫ (coneRootCoordinatePairRight (n + 1) b a ≫ f) = coneRootCoordinatePairLeft (n + 1) a b ≫ f :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ f) (coneRootCoordinatePairSwapIso_right (n + 1) a b))
      exact hr.symm.trans (hs.symm.trans hl)

end SSet.Marked

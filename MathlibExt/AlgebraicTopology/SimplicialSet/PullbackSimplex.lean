/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original simplices of a simplicial pullback

The two original projection maps identify each simplex of an actual
pullback with a pair of simplices having equal base images. Reconstruction
uses its specified pullback lift and Yoneda. The projection equations and
simplicial naturality retain the original maps.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.PullbackSimplex

variable {P X A B : SSet.{u}} {r : P ⟶ X} {q : P ⟶ A} {p : X ⟶ B} {s : A ⟶ B}

/-- The original full simplex is determined by its two pullback projections. -/
theorem hom_ext (h : IsPullback r q p s) {n : ℕ} {x y : P _⦋n⦌}
    (hr : r.app _ x = r.app _ y) (hq : q.app _ x = q.app _ y) : x = y := by
  apply yonedaEquiv.symm.injective
  apply h.hom_ext
  · apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hr
  · apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hq

/-- Reconstruct the original simplex from a pair with its actual base equality. -/
def lift (h : IsPullback r q p s) (n : ℕ) (x : X _⦋n⦌) (a : A _⦋n⦌)
    (w : p.app _ x = s.app _ a) : P _⦋n⦌ :=
  yonedaEquiv (h.lift (yonedaEquiv.symm x) (yonedaEquiv.symm a) (by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using w))

/-- Reconstruction retains the first original simplex exactly. -/
@[simp] theorem lift_fst (h : IsPullback r q p s) (n : ℕ) (x : X _⦋n⦌) (a : A _⦋n⦌)
    (w : p.app _ x = s.app _ a) : r.app _ (lift h n x a w) = x := by
  dsimp only [lift]
  rw [← yonedaEquiv_comp, h.lift_fst, Equiv.apply_symm_apply]

/-- Reconstruction retains the second original simplex exactly. -/
@[simp] theorem lift_snd (h : IsPullback r q p s) (n : ℕ) (x : X _⦋n⦌) (a : A _⦋n⦌)
    (w : p.app _ x = s.app _ a) : q.app _ (lift h n x a w) = a := by
  dsimp only [lift]
  rw [← yonedaEquiv_comp, h.lift_snd, Equiv.apply_symm_apply]

/-- Original simplices of the specified pullback are precisely the compatible pairs. -/
def equiv (h : IsPullback r q p s) (n : ℕ) :
    P _⦋n⦌ ≃ {z : X _⦋n⦌ × A _⦋n⦌ // p.app _ z.1 = s.app _ z.2} where
  toFun x := ⟨⟨r.app _ x, q.app _ x⟩,
    congrArg (fun f => f.app (op ⦋n⦌) x) h.w⟩
  invFun z := lift h n z.1.1 z.1.2 z.2
  left_inv x := hom_ext h (lift_fst h n _ _ _) (lift_snd h n _ _ _)
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext (lift_fst h n _ _ _) (lift_snd h n _ _ _)

/-- Simplicial operators commute with reconstruction using the same projections. -/
theorem lift_naturality (h : IsPullback r q p s) {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : X _⦋n⦌) (a : A _⦋n⦌) (w : p.app _ x = s.app _ a) :
    P.map f.op (lift h n x a w) =
      lift h m (X.map f.op x) (A.map f.op a) (by
        rw [p.naturality_apply, s.naturality_apply, w]) := by
  apply hom_ext h
  · rw [r.naturality_apply, lift_fst, lift_fst]
  · rw [q.naturality_apply, lift_snd, lift_snd]

end SSet.PullbackSimplex

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupHornOperators
public import Mathlib.Data.Fin.SuccPred

/-!
# Lower-face corrections in a simplicial group

Let `G : SimplicialObject GrpCat.{u}`. To prescribe a non-last face `j.castSucc` of an `(n +
  1)`-simplex
`x` as `h`, form the error `(δ j x)⁻¹ * h` and replace `x` by `x * σ j ((δ j x)⁻¹ * h)`. The
resulting face at `j.castSucc` is `h`. Pairwise face compatibility ensures that this correction
preserves previously prescribed faces at indices less than `j`; the order of multiplication is
valid for noncommutative groups.

For a family of `(n + 1)`-simplices indexed by the faces of an `(n + 2)`-simplex, with one
missing index `i`, the finite lower pass starts at the group identity and corrects faces in
increasing order. Under compatibility away from `i`, the pass at stage `i` has all the
prescribed faces strictly below `i`.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

attribute [local instance] underlyingGroup

variable (G : SimplicialObject GrpCat.{u})

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`lowerError G j x h = ((underlying G).δ (Fin.castSucc j) x)⁻¹ * h`.
The inverse of the current face multiplies the prescribed face on the left. -/
def lowerError {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n⦌ :=
  ((underlying G).δ (Fin.castSucc j) x)⁻¹ * h

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and prescribed face `h ∈ (underlying G) _⦋n⦌`,
`correctLower G j x h = x * (underlying G).σ j (lowerError G j x h)`.
This is an `(n + 1)`-simplex obtained by multiplying `x` on the right by the degeneracy of its
face error. -/
def correctLower {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n + 1⦌ :=
  x * (underlying G).σ j (lowerError G j x h)

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ (Fin.castSucc j) (correctLower G j x h) = h`.
Thus the correction prescribes the face at index `j`. -/
theorem correctLower_face {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G).δ (Fin.castSucc j) (correctLower G j x h) = h := by
  have hm := (G.map (SimplexCategory.δ (Fin.castSucc j)).op).hom.map_mul x
    ((underlying G).σ j (lowerError G j x h))
  have hd := (underlying G).δ_comp_σ_self_apply j (lowerError G j x h)
  exact hm.trans ((congrArg (fun y => (underlying G).δ (Fin.castSucc j) x * y) hd).trans
    (mul_inv_cancel_left _ h))

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and `h ∈ (underlying G) _⦋n⦌`, if `(underlying G).δ (Fin.castSucc j) x = h`, then
`lowerError G j x h = 1` in the degree-`n` group. -/
theorem lowerError_one {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) (hx : (underlying G).δ (Fin.castSucc j) x = h) :
    lowerError G j x h = 1 := by
  exact (congrArg (fun y => y⁻¹ * h) hx).trans (inv_mul_cancel h)

/-- For `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`, the index `lowerPairPred hkj : Fin (n +
2)` is `(Fin.castSucc j).pred _`, whose value is `j - 1`. The inequality guarantees that this
predecessor is defined; it is the second face index in the relation `δ k ∘ δ j = δ (j - 1) ∘ δ
k`. -/
def lowerPairPred {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j) : Fin (n + 2) :=
  (Fin.castSucc j).pred ((Fin.castSucc_lt_castSucc_iff.mpr hkj).ne_zero)

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For
`x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ (Fin.castSucc
k) x = b` and `δ k a = δ (lowerPairPred hkj) b`, where `δ` denotes the face maps of
`underlying G`. Then `δ k (lowerError G j x a) = 1`. -/
theorem lowerError_face_one {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ (lowerPairPred hkj) b) :
    (underlying G).δ k (lowerError G j x a) = 1 := by
  have hh := ConcreteCategory.congr_hom
    ((underlying G).δ_comp_δ' (Fin.castSucc_lt_castSucc_iff.mpr hkj)) x
  have hd : (underlying G).δ k ((underlying G).δ (Fin.castSucc j) x) =
      (underlying G).δ (lowerPairPred hkj) b :=
    hh.trans (congrArg ((underlying G).δ (lowerPairPred hkj)) hx)
  have hm := (G.map (SimplexCategory.δ k).op).hom.map_mul (((underlying G).δ (Fin.castSucc j)
    x)⁻¹) a
  have hi := (G.map (SimplexCategory.δ k).op).hom.map_inv ((underlying G).δ (Fin.castSucc j) x)
  exact hm.trans ((congrArg₂ (fun y z => y * z) (hi.trans (congrArg Inv.inv hd)) hc).trans
    (inv_mul_cancel _))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For
`x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, assume `δ (Fin.castSucc k)
x
= b` and `δ k a = δ (lowerPairPred hkj) b`. Then
`δ (Fin.castSucc k) (correctLower G j x a) = b`,
where `δ` denotes the face maps of `underlying G`. Prescribing face `j` therefore preserves
face
`k` under this compatibility equation. -/
theorem correctLower_preserves {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ (lowerPairPred hkj) b) :
    (underlying G).δ (Fin.castSucc k) (correctLower G j x a) = b := by
  let p := j.pred hkj.ne_zero
  have hp : k ≤ Fin.castSucc p := (Fin.le_castSucc_pred_iff hkj.ne_zero).mpr hkj
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_le hp) (lowerError G j x a)
  have he : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (lowerError G j x a)) =
      (underlying G).σ p ((underlying G).δ k (lowerError G j x a)) := by
    simpa only [p, Fin.succ_pred, CategoryTheory.types_comp_apply] using hs
  have hz : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (lowerError G j x a)) = 1 :=
    he.trans ((congrArg ((underlying G).σ p) (lowerError_face_one G hkj x a b hx hc)).trans
      ((G.map (SimplexCategory.σ p).op).hom.map_one))
  have hm := (G.map (SimplexCategory.δ (Fin.castSucc k)).op).hom.map_mul x
    ((underlying G).σ j (lowerError G j x a))
  exact hm.trans ((congrArg₂ (fun y z => y * z) hx hz).trans (mul_one b))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌`. The predicate `FaceCompatible G i h` requires that for every `k :
Fin
(n + 2)` and `j : Fin (n + 3)` with `Fin.castSucc k < j`, `Fin.castSucc k ≠ i`, and `j ≠ i`,
`(underlying G).δ k (h j) = (underlying G).δ (j.pred _) (h (Fin.castSucc k))`.
The value of the predecessor is `j - 1`; these are the pairwise face equations away from the
missing index `i`. -/
def FaceCompatible {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) : Prop :=
  ∀ (k : Fin (n + 2)) (j : Fin (n + 3)) (hkj : Fin.castSucc k < j)
    (_ : Fin.castSucc k ≠ i) (_ : j ≠ i),
      (underlying G).δ k (h j) = (underlying G).δ (j.pred hkj.ne_zero) (h (Fin.castSucc k))

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `h : Fin (n + 3) → (underlying G) _⦋n +
1⦌`, `lowerPass G h r` is an `(n + 2)`-simplex at stage `r : Fin (n + 3)`. It starts at the
group identity at stage zero and, from stage `Fin.castSucc j` to `j.succ`, applies
`correctLower G j` with prescribed face `h (Fin.castSucc j)`. -/
def lowerPass {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (r : Fin (n + 3)) :
    (underlying G) _⦋n + 2⦌ :=
  Fin.induction 1 (fun j x => correctLower G j x (h (Fin.castSucc j))) r

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `h : Fin (n + 3) → (underlying G) _⦋n +
1⦌`,
`lowerPass G h 0 = 1`,
where the right side is the identity of the degree-`n + 2` group. -/
theorem lowerPass_zero {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) : lowerPass G h 0 = 1
  := rfl

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`,
and `j : Fin (n + 2)`,
`lowerPass G h j.succ = correctLower G j (lowerPass G h (Fin.castSucc j)) (h (Fin.castSucc
j))`.
The step prescribes face `j` by the corresponding degeneracy correction. -/
theorem lowerPass_succ {n : ℕ} (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (j : Fin (n + 2)) :
    lowerPass G h j.succ = correctLower G j (lowerPass G h (Fin.castSucc j)) (h (Fin.castSucc j))
      := by
  simp only [lowerPass, Fin.induction_succ]

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` satisfy `FaceCompatible G i h`, the pairwise simplicial face
equations
away from `i`. For a stage `r : Fin (n + 3)` with `r ≤ i` and any `k : Fin (n + 3)` with `k <
r`,
`(underlying G).δ k (lowerPass G h r) = h k`.
Thus all faces strictly before the stage have their prescribed values. -/
theorem lowerPass_faces {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (r : Fin (n + 3)) (hr : r ≤ i) (k : Fin (n + 3)) (hkr : k < r) :
    (underlying G).δ k (lowerPass G h r) = h k := by
  induction r using Fin.induction with
  | zero => exact (not_lt_of_ge (Fin.zero_le k) hkr).elim
  | succ j ih =>
    have hjlt : Fin.castSucc j < i := lt_of_lt_of_le (show Fin.castSucc j < j.succ from
      Nat.lt_succ_self j.val) hr
    have hjle : Fin.castSucc j ≤ i := le_of_lt hjlt
    rw [lowerPass_succ]
    by_cases he : k = Fin.castSucc j
    · subst k
      exact correctLower_face G j _ _
    · have hklt : k < Fin.castSucc j := by
        have hv : k.val < j.val + 1 := hkr
        have hn : k.val ≠ j.val := fun e => he (Fin.ext e)
        exact Fin.lt_def.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp hv) hn)
      have hklast : k ≠ Fin.last (n + 2) := ne_of_lt (lt_trans hklt (Fin.castSucc_lt_last j))
      let k' := k.castPred hklast
      have hk' : Fin.castSucc k' = k := Fin.castSucc_castPred k hklast
      have hkj : k' < j := Fin.castSucc_lt_castSucc_iff.mp (by rw [hk']; exact hklt)
      have hx : (underlying G).δ (Fin.castSucc k') (lowerPass G h (Fin.castSucc j)) = h
        (Fin.castSucc k') := by
        simpa only [hk'] using ih hjle hklt
      have hp := hc k' (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.mpr hkj)
        (ne_of_lt (lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hkj) hjlt)) (ne_of_lt hjlt)
      have hf := correctLower_preserves G hkj (lowerPass G h (Fin.castSucc j))
        (h (Fin.castSucc j)) (h (Fin.castSucc k')) hx hp
      simpa only [hk'] using hf

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` satisfying the pairwise face equations `FaceCompatible G i h` away
from
`i`, every `k : Fin (n + 3)` with `k < i` satisfies
`(underlying G).δ k (lowerPass G h i) = h k`.
This describes the faces of the `(n + 2)`-simplex at the missing-index stage. -/
theorem lowerPass_below {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (k : Fin (n + 3)) (hki : k < i) :
    (underlying G).δ k (lowerPass G h i) = h k := lowerPass_faces G i h hc i (le_refl i) k hki

end SSet.SimplicialGroupHorn

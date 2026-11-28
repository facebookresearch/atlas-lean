/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupLowerHornCorrection

/-!
# Upper-face corrections and horn fillers in simplicial groups

Let `G : SimplicialObject GrpCat.{u}`. The correction `x * σ j ((δ (j + 1) x)⁻¹ * h)` makes
face `j + 1` equal to the prescribed simplex `h`. Pairwise face equations ensure that it
preserves earlier fixed faces at indices less than `j` and later fixed faces at indices
greater than `j + 1`.

For a compatible family of faces of an `(n + 2)`-simplex with missing index `i`, the upper
pass starts with the lower pass at `i` and corrects the remaining faces in decreasing order.
At stage `i`, its simplex has every prescribed face at an index different from `i`. The
construction uses multiplication and degeneracies in the degree groups and applies to
noncommutative simplicial groups.
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
`upperError G j x h = ((underlying G).δ j.succ x)⁻¹ * h`.
The inverse of the current face at `j + 1` multiplies the prescribed face on the left. -/
def upperError {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n⦌ := ((underlying G).δ j.succ x)⁻¹ * h

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and prescribed face `h ∈ (underlying G) _⦋n⦌`,
`correctUpper G j x h = x * (underlying G).σ j (upperError G j x h)`.
The error for face `j + 1` is lifted by degeneracy `j` and multiplied on the right of `x`. -/
def correctUpper {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G) _⦋n + 1⦌ := x * (underlying G).σ j (upperError G j
      x h)

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ j.succ (correctUpper G j x h) = h`.
The correction therefore prescribes the face at index `j + 1`. -/
theorem correctUpper_face {n : ℕ} (j : Fin (n + 1)) (x : (underlying G) _⦋n + 1⦌)
    (h : (underlying G) _⦋n⦌) : (underlying G).δ j.succ (correctUpper G j x h) = h := by
  have hm := (G.map (SimplexCategory.δ j.succ).op).hom.map_mul x ((underlying G).σ j (upperError G
    j x h))
  have hd := (underlying G).δ_comp_σ_succ_apply j (upperError G j x h)
  exact hm.trans ((congrArg (fun y => (underlying G).δ j.succ x * y) hd).trans
    (mul_inv_cancel_left _ h))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For
`x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ (Fin.castSucc
k)
x = b` and `δ k a = δ j b`. Then
`δ k (upperError G j x a) = 1`,
where `δ` denotes the face maps of `underlying G`. -/
theorem upperError_lower_face_one {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ j b) :
    (underlying G).δ k (upperError G j x a) = 1 := by
  have hlt : Fin.castSucc k < j.succ := lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hkj)
    (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val)
  have hh := ConcreteCategory.congr_hom ((underlying G).δ_comp_δ' hlt) x
  have hd : (underlying G).δ k ((underlying G).δ j.succ x) = (underlying G).δ j b := by
    have h := (congrArg ((underlying G).δ j) hx)
    simpa only [Fin.pred_succ, CategoryTheory.types_comp_apply] using hh.trans h
  have hm := (G.map (SimplexCategory.δ k).op).hom.map_mul (((underlying G).δ j.succ x)⁻¹) a
  have hi := (G.map (SimplexCategory.δ k).op).hom.map_inv ((underlying G).δ j.succ x)
  exact hm.trans ((congrArg₂ (fun (y z : (underlying G) _⦋n⦌) => y * z)
      (hi.trans (congrArg Inv.inv hd)) hc).trans
    (inv_mul_cancel _))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For
`x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ (Fin.castSucc
k)
x = b` and `δ k a = δ j b`. Then
`δ (Fin.castSucc k) (correctUpper G j x a) = b`.
Thus correcting face `j + 1` preserves face `k`; `δ` denotes the face maps of `underlying G`. -/
theorem correctUpper_preserves_lower {n : ℕ} {k j : Fin (n + 2)} (hkj : k < j)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ (Fin.castSucc k) x = b)
    (hc : (underlying G).δ k a = (underlying G).δ j b) :
    (underlying G).δ (Fin.castSucc k) (correctUpper G j x a) = b := by
  let p := j.pred hkj.ne_zero
  have hp : k ≤ Fin.castSucc p := (Fin.le_castSucc_pred_iff hkj.ne_zero).mpr hkj
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_le hp) (upperError G j x a)
  have he : (underlying G).δ (Fin.castSucc k) ((underlying G).σ j (upperError G j x a)) =
      (underlying G).σ p ((underlying G).δ k (upperError G j x a)) := by
    simpa only [p, Fin.succ_pred, CategoryTheory.types_comp_apply] using hs
  have hz := he.trans ((congrArg ((underlying G).σ p) (upperError_lower_face_one G hkj x a b hx
    hc)).trans
    ((G.map (SimplexCategory.σ p).op).hom.map_one))
  have hm := (G.map (SimplexCategory.δ (Fin.castSucc k)).op).hom.map_mul x ((underlying G).σ j
    (upperError G j x a))
  exact hm.trans ((congrArg₂
    (fun (y z : (underlying G) _⦋n + 1⦌) => y * z) hx hz).trans (mul_one b))

/-- For `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk : j.succ < k`, the index
`upperTailDeg hjk : Fin (n + 1)` is `j` with its bound tightened. The inequality implies `j <
n + 1`, so its successor is an admissible face index for a degree-`n + 1` simplex. -/
def upperTailDeg {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k) : Fin (n + 1) :=
  j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le hjk k.is_le))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk
: j.succ < k`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose
`δ k x = b` and `δ (upperTailDeg hjk).succ b = δ (k.pred hjk.ne_zero) a`. Then
`δ (k.pred hjk.ne_zero) (upperError G j x a) = 1`,
where `δ` denotes the face maps of `underlying G` and the predecessor has value `k - 1`. -/
theorem upperError_later_face_one {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ k x = b)
    (hc : (underlying G).δ (upperTailDeg hjk).succ b = (underlying G).δ (k.pred hjk.ne_zero) a) :
    (underlying G).δ (k.pred hjk.ne_zero) (upperError G j x a) = 1 := by
  have hp : Fin.castSucc (upperTailDeg hjk).succ = j.succ := Fin.ext rfl
  have hlt : Fin.castSucc (upperTailDeg hjk).succ < k := by rw [hp]; exact hjk
  have hh := ConcreteCategory.congr_hom ((underlying G).δ_comp_δ' hlt) x
  have hd : (underlying G).δ (k.pred hjk.ne_zero) ((underlying G).δ j.succ x) =
      (underlying G).δ (upperTailDeg hjk).succ b := by
    have h := (congrArg ((underlying G).δ (upperTailDeg hjk).succ) hx)
    simpa only [hp, CategoryTheory.types_comp_apply] using hh.symm.trans h
  have hm := (G.map (SimplexCategory.δ (k.pred hjk.ne_zero)).op).hom.map_mul (((underlying G).δ
    j.succ x)⁻¹) a
  have hi := (G.map (SimplexCategory.δ (k.pred hjk.ne_zero)).op).hom.map_inv ((underlying G).δ
    j.succ x)
  exact hm.trans ((congrArg₂ (fun (y z : (underlying G) _⦋n⦌) => y * z)
      (hi.trans (congrArg Inv.inv hd)) hc.symm).trans
    (inv_mul_cancel _))

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk
: j.succ < k`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose
`δ k x = b` and `δ (upperTailDeg hjk).succ b = δ (k.pred hjk.ne_zero) a`. Then
`δ k (correctUpper G j x a) = b`,
where `δ` denotes the face maps of `underlying G`. The compatibility equation ensures that
correcting face `j + 1` preserves the later face `k`. -/
theorem correctUpper_preserves_later {n : ℕ} {j : Fin (n + 2)} {k : Fin (n + 3)} (hjk : j.succ < k)
    (x : (underlying G) _⦋n + 2⦌) (a b : (underlying G) _⦋n + 1⦌)
    (hx : (underlying G).δ k x = b)
    (hc : (underlying G).δ (upperTailDeg hjk).succ b = (underlying G).δ (k.pred hjk.ne_zero) a) :
    (underlying G).δ k (correctUpper G j x a) = b := by
  have hs := ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_of_gt' hjk) (upperError G j x a)
  have hz : (underlying G).δ k ((underlying G).σ j (upperError G j x a)) = 1 :=
    hs.trans ((congrArg ((underlying G).σ (upperTailDeg hjk)) (upperError_later_face_one G hjk x a
      b hx hc)).trans
      ((G.map (SimplexCategory.σ (upperTailDeg hjk)).op).hom.map_one))
  have hm := (G.map (SimplexCategory.δ k).op).hom.map_mul x ((underlying G).σ j (upperError G j x
    a))
  exact hm.trans ((congrArg₂
    (fun (y z : (underlying G) _⦋n + 1⦌) => y * z) hx hz).trans (mul_one b))

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, missing index `i : Fin (n + 3)`, and `h : Fin
(n + 3) → (underlying G) _⦋n + 1⦌`, `upperPass G i h r` is an `(n + 2)`-simplex at stage `r :
Fin (n + 3)`. At the last stage it is `lowerPass G h i`. The descending step from `j.succ` to
`Fin.castSucc j` applies `correctUpper G j` with prescribed face `h j.succ`. -/
def upperPass {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) (r : Fin (n +
  3)) :
    (underlying G) _⦋n + 2⦌ :=
  Fin.reverseInduction (lowerPass G h i) (fun j x => correctUpper G j x (h j.succ)) r

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌`,
`upperPass G i h (Fin.last (n + 2)) = lowerPass G h i`.
The descending pass begins with the lower-pass simplex at the missing-face index. -/
theorem upperPass_last {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) :
    upperPass G i h (Fin.last (n + 2)) = lowerPass G h i := by
  simp only [upperPass, Fin.reverseInduction_last]

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌`, and `j : Fin (n + 2)`,
`upperPass G i h (Fin.castSucc j) = correctUpper G j (upperPass G i h j.succ) (h j.succ)`.
The step prescribes face `j + 1` by the corresponding degeneracy correction. -/
theorem upperPass_castSucc {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (j : Fin (n + 2)) : upperPass G i h (Fin.castSucc j) =
      correctUpper G j (upperPass G i h j.succ) (h j.succ) := by
  simp only [upperPass, Fin.reverseInduction_castSucc]

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` satisfy `FaceCompatible G i h`, the pairwise simplicial face
equations away from `i`. For a stage `r : Fin (n + 3)` with `i ≤ r`, the `(n + 2)`-simplex
`upperPass G i h r` has face `h k` at every index `k < i` and every index `r < k`. Thus the
pass preserves all prescribed lower faces and fills the faces strictly above its stage. -/
theorem upperPass_faces {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (r : Fin (n + 3)) (hr : i ≤ r) :
    (∀ (k : Fin (n + 3)), k < i → (underlying G).δ k (upperPass G i h r) = h k) ∧
      (∀ (k : Fin (n + 3)), r < k → (underlying G).δ k (upperPass G i h r) = h k) := by
  induction r using Fin.reverseInduction with
  | last =>
    rw [upperPass_last]
    exact ⟨fun k hk => lowerPass_below G i h hc k hk,
      fun k hk => (not_lt_of_ge (Fin.le_last k) hk).elim⟩
  | cast j ih =>
    have hji : i < j.succ := lt_of_le_of_lt hr (show Fin.castSucc j < j.succ from Nat.lt_succ_self
      j.val)
    have hi := ih (le_of_lt hji)
    rw [upperPass_castSucc]
    constructor
    · intro k hki
      have hkj : k < Fin.castSucc j := lt_of_lt_of_le hki hr
      have hklast : k ≠ Fin.last (n + 2) := ne_of_lt (lt_trans hkj (Fin.castSucc_lt_last j))
      let k' := k.castPred hklast
      have hk' : Fin.castSucc k' = k := Fin.castSucc_castPred k hklast
      have hkj' : k' < j := Fin.castSucc_lt_castSucc_iff.mp (by rw [hk']; exact hkj)
      have hx : (underlying G).δ (Fin.castSucc k') (upperPass G i h j.succ) = h (Fin.castSucc k')
        := by
        simpa only [hk'] using hi.1 k hki
      have hlt : Fin.castSucc k' < j.succ := by
        rw [hk']
        exact lt_trans hkj (show Fin.castSucc j < j.succ from Nat.lt_succ_self j.val)
      have hp := hc k' j.succ hlt (by rw [hk']; exact ne_of_lt hki) (ne_of_gt hji)
      have hp' : (underlying G).δ k' (h j.succ) = (underlying G).δ j (h (Fin.castSucc k')) := by
        simpa only [Fin.pred_succ] using hp
      have hf := correctUpper_preserves_lower G hkj' (upperPass G i h j.succ)
        (h j.succ) (h (Fin.castSucc k')) hx hp'
      simpa only [hk'] using hf
    · intro k hjk
      by_cases he : k = j.succ
      · subst k
        exact correctUpper_face G j _ _
      · have hjk' : j.succ < k := by
          have hv : j.val < k.val := hjk
          have hn : j.val + 1 ≠ k.val := fun e => he (Fin.ext e.symm)
          exact Fin.lt_def.mpr (lt_of_le_of_ne (Nat.succ_le_iff.mpr hv) hn)
        have hx := hi.2 k hjk'
        have hp : Fin.castSucc (upperTailDeg hjk').succ = j.succ := Fin.ext rfl
        have hlt : Fin.castSucc (upperTailDeg hjk').succ < k := by rw [hp]; exact hjk'
        have hh := hc (upperTailDeg hjk').succ k hlt
          (by rw [hp]; exact ne_of_gt hji) (ne_of_gt (lt_trans hji hjk'))
        have hh' : (underlying G).δ (upperTailDeg hjk').succ (h k) =
            (underlying G).δ (k.pred hjk'.ne_zero) (h j.succ) := by
          simpa only [hp] using hh
        exact correctUpper_preserves_later G hjk' (upperPass G i h j.succ) (h j.succ) (h k) hx hh'

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, missing index `i : Fin (n + 3)`, and face
family `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`, the `(n + 2)`-simplex `hornFiller G i h`
is `upperPass G i h i`. It is obtained by the increasing lower-face pass followed by the
decreasing upper-face pass. When the prescribed faces are compatible away from `i`, it has
each of those faces. -/
def hornFiller {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌) :
    (underlying G) _⦋n + 2⦌ := upperPass G i h i

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` satisfying `FaceCompatible G i h`, the pairwise face equations away
from `i`, every `k : Fin (n + 3)` with `k ≠ i` satisfies
`(underlying G).δ k (hornFiller G i h) = h k`.
Thus the constructed `(n + 2)`-simplex fills the compatible horn at index `i`. -/
theorem hornFiller_face {n : ℕ} (i : Fin (n + 3)) (h : Fin (n + 3) → (underlying G) _⦋n + 1⦌)
    (hc : FaceCompatible G i h) (k : Fin (n + 3)) (hki : k ≠ i) :
    (underlying G).δ k (hornFiller G i h) = h k := by
  have hx := upperPass_faces G i h hc i (le_refl i)
  rcases lt_or_gt_of_ne hki with h | h
  · exact hx.1 k h
  · exact hx.2 k h

end SSet.SimplicialGroupHorn

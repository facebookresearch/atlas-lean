/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupUpperHornCorrection
public import MathlibExt.CategoryTheory.DGSourceMore.SimplicialGroupKan

/-!
# Kan horn filling for simplicial groups

For every simplicial group `G : SimplicialObject GrpCat.{u}`, the underlying simplicial set
`underlying G` is a Kan complex. A compatible family of horn-face maps determines elements of
the degree groups through Yoneda evaluation. In dimension `n + 2`, these elements satisfy the
face equations needed for the lower and upper group corrections, which yield a simplex having
all the prescribed nonmissing faces. This is Moore's horn construction. The canonical Kan
instance and its original source attribution are supplied by
`MathlibExt.CategoryTheory.DGSourceMore.SimplicialGroupKan`; the explicit filler data and face
laws remain in the correction modules.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

attribute [local instance] underlyingGroup

variable (G : SimplicialObject GrpCat.{u})

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `i : Fin (n + 3)`. Given maps `f j hj :
Δ[n + 1] ⟶ underlying G` for every `j ≠ i`, the family `groupFaces G i f : Fin (n + 3) →
(underlying G) _⦋n + 1⦌` assigns `yonedaEquiv (f j hj)` to a nonmissing face `j`, and assigns
the group identity to the missing index `i`. -/
def groupFaces {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (j : Fin (n + 3)) : (underlying G) _⦋n + 1⦌ :=
  if hj : j ≠ i then SSet.yonedaEquiv (f j hj) else 1

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and a family of maps `f j
hj : Δ[n + 1] ⟶ underlying G` indexed by `j ≠ i`,
`groupFaces G i f j = yonedaEquiv (f j hj)`
whenever `hj : j ≠ i`. Thus every prescribed face retains its Yoneda value. -/
theorem groupFaces_at {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (j : Fin (n + 3)) (hj : j ≠ i) : groupFaces G i f j = SSet.yonedaEquiv (f j hj) :=
      dite_eq_left hj

/-- Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `i : Fin (n + 3)`. Suppose the maps `f j
hj : Δ[n + 1] ⟶ underlying G`, for `j ≠ i`, form a compatible horn family
(`SSet.horn.IsCompatible f`). Then `FaceCompatible G i (groupFaces G i f)` holds: for `k : Fin
(n + 2)` and `j : Fin (n + 3)` with `Fin.castSucc k < j` and both indices different from `i`,
the `k`-th face of the value at `j` equals the `(j - 1)`-st face of the value at `Fin.castSucc
k`. -/
theorem groupFaces_compatible {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (hf : SSet.horn.IsCompatible f) : FaceCompatible G i (groupFaces G i f) := by
  intro k j hkj hk hj
  have h := congrArg SSet.yonedaEquiv (hf.δ_pred_comp (Fin.castSucc k) j hk hj hkj)
  have hh : (underlying G).δ k (SSet.yonedaEquiv (f j hj)) =
      (underlying G).δ (j.pred hkj.ne_zero) (SSet.yonedaEquiv (f (Fin.castSucc k) hk)) := by
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Fin.castPred_castSucc] using h.symm
  exact (congrArg ((underlying G).δ k) (groupFaces_at G i f j hj)).trans
    (hh.trans (congrArg ((underlying G).δ (j.pred hkj.ne_zero)) (groupFaces_at G i f (Fin.castSucc
      k) hk)).symm)

end SSet.SimplicialGroupHorn

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierD.SixVertexRectangleBoundary
import Mathlib.Data.Fin.Rev

open Finset

namespace StatMech.FrontierD


def sixVertexRectangleReflectHorizontal {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) : SixVertexRectangleArrows N M where
  horizontal kj := ω.horizontal (kj.1.rev, kj.2)
  vertical ik := !ω.vertical (ik.1.rev, ik.2)


def sixVertexRectangleReflectVertical {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) : SixVertexRectangleArrows N M where
  horizontal kj := !ω.horizontal (kj.1, kj.2.rev)
  vertical ik := ω.vertical (ik.1, ik.2.rev)

@[simp] theorem sixVertexRectangleReflectHorizontal_involutive {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleReflectHorizontal (sixVertexRectangleReflectHorizontal ω) = ω := by
  apply SixVertexRectangleArrows.ext <;> funext v <;>
    simp [sixVertexRectangleReflectHorizontal]

@[simp] theorem sixVertexRectangleReflectVertical_involutive {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleReflectVertical (sixVertexRectangleReflectVertical ω) = ω := by
  apply SixVertexRectangleArrows.ext <;> funext v <;>
    simp [sixVertexRectangleReflectVertical]


def sixVertexBoundaryReflectHorizontal {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) : SixVertexRectangleBoundary N M where
  left := ξ.right
  right := ξ.left
  bottom i := !ξ.bottom i.rev
  top i := !ξ.top i.rev


def sixVertexBoundaryReflectVertical {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) : SixVertexRectangleBoundary N M where
  left j := !ξ.left j.rev
  right j := !ξ.right j.rev
  bottom := ξ.top
  top := ξ.bottom

theorem sixVertexRectangleReflectHorizontal_boundary {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectHorizontal ω) =
      sixVertexBoundaryReflectHorizontal (sixVertexRectangleBoundary ω) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexRectangleReflectHorizontal,
      sixVertexBoundaryReflectHorizontal]

theorem sixVertexRectangleReflectVertical_boundary {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectVertical ω) =
      sixVertexBoundaryReflectVertical (sixVertexRectangleBoundary ω) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexRectangleReflectVertical,
      sixVertexBoundaryReflectVertical]

@[simp] theorem sixVertexBoundaryReflectHorizontal_involutive {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :
    sixVertexBoundaryReflectHorizontal (sixVertexBoundaryReflectHorizontal ξ) = ξ := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexBoundaryReflectHorizontal]

@[simp] theorem sixVertexBoundaryReflectVertical_involutive {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :
    sixVertexBoundaryReflectVertical (sixVertexBoundaryReflectVertical ξ) = ξ := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexBoundaryReflectVertical]

private theorem bool_toNat_add_not_toNat (b : Bool) :
    b.toNat + (!b).toNat = 1 := by
  cases b <;> decide

private theorem sixVertexRectangleReflectHorizontal_localWeight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleReflectHorizontal ω).localWeight c v =
      ω.localWeight c (v.1.rev, v.2) := by
  rw [SixVertexRectangleArrows.localWeight, SixVertexRectangleArrows.localWeight]
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleReflectHorizontal, Fin.rev_castSucc, Fin.rev_succ, Bool.not_not]
  have hL := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.rev.castSucc, v.2))
  have hR := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.rev.succ, v.2))
  have hB := bool_toNat_add_not_toNat
    (ω.vertical (v.1.rev, v.2.castSucc))
  have hT := bool_toNat_add_not_toNat
    (ω.vertical (v.1.rev, v.2.succ))
  have hin :
      (ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.vertical (v.1.rev, v.2.castSucc)).toNat +
            (ω.vertical (v.1.rev, v.2.succ)).toNat = 2 ↔
        (ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (ω.vertical (v.1.rev, v.2.castSucc)).toNat +
            (!ω.vertical (v.1.rev, v.2.succ)).toNat = 2 := by omega
  have hc :
      ((ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat = 0 ∨
        (ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat = 2) ↔
      ((ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat = 0 ∨
        (ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat = 2) := by omega
  rw [if_congr hin (if_congr hc rfl rfl) rfl]
  split <;> (try split) <;> rfl

private theorem sixVertexRectangleReflectVertical_localWeight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleReflectVertical ω).localWeight c v =
      ω.localWeight c (v.1, v.2.rev) := by
  rw [SixVertexRectangleArrows.localWeight, SixVertexRectangleArrows.localWeight]
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleReflectVertical, Fin.rev_castSucc, Fin.rev_succ, Bool.not_not]
  have hL := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.castSucc, v.2.rev))
  have hR := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.succ, v.2.rev))
  have hB := bool_toNat_add_not_toNat
    (ω.vertical (v.1, v.2.rev.castSucc))
  have hT := bool_toNat_add_not_toNat
    (ω.vertical (v.1, v.2.rev.succ))
  have hin :
      (!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat +
            (ω.vertical (v.1, v.2.rev.succ)).toNat +
            (!ω.vertical (v.1, v.2.rev.castSucc)).toNat = 2 ↔
        (ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat +
            (ω.vertical (v.1, v.2.rev.castSucc)).toNat +
            (!ω.vertical (v.1, v.2.rev.succ)).toNat = 2 := by omega
  have hc :
      ((!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat = 0 ∨
        (!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat = 2) ↔
      ((ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat = 0 ∨
        (ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat = 2) := by omega
  rw [if_congr hin (if_congr hc rfl rfl) rfl]
  split <;> (try split) <;> rfl

private def sixVertexRectangleReflectHorizontalEquiv (N M : ℕ) :
    SixVertexRectangleArrows N M ≃ SixVertexRectangleArrows N M :=
  Function.Involutive.toPerm sixVertexRectangleReflectHorizontal
    sixVertexRectangleReflectHorizontal_involutive

private def sixVertexRectangleReflectVerticalEquiv (N M : ℕ) :
    SixVertexRectangleArrows N M ≃ SixVertexRectangleArrows N M :=
  Function.Involutive.toPerm sixVertexRectangleReflectVertical
    sixVertexRectangleReflectVertical_involutive

theorem sixVertexRectangleReflectHorizontal_weight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) :
    (sixVertexRectangleReflectHorizontal ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin N × Fin M, (sixVertexRectangleReflectHorizontal ω).localWeight c v =
        ∏ v : Fin N × Fin M, ω.localWeight c (v.1.rev, v.2) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact sixVertexRectangleReflectHorizontal_localWeight c ω v
    _ = ∏ v : Fin N × Fin M, ω.localWeight c v :=
      ((Fin.revPerm.prodCongr (Equiv.refl (Fin M))).prod_comp
        fun v => ω.localWeight c v)

theorem sixVertexRectangleReflectVertical_weight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) :
    (sixVertexRectangleReflectVertical ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin N × Fin M, (sixVertexRectangleReflectVertical ω).localWeight c v =
        ∏ v : Fin N × Fin M, ω.localWeight c (v.1, v.2.rev) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact sixVertexRectangleReflectVertical_localWeight c ω v
    _ = ∏ v : Fin N × Fin M, ω.localWeight c v :=
      (((Equiv.refl (Fin N)).prodCongr Fin.revPerm).prod_comp
        fun v => ω.localWeight c v)



theorem sixVertexRectangleBoundaryPartitionSum_reflectHorizontal
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexBoundaryReflectHorizontal ξ) =
      sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleBoundaryPartitionSum,
    sixVertexRectangleBoundaryPartitionSum]
  apply Fintype.sum_equiv (sixVertexRectangleReflectHorizontalEquiv N M)
  intro ω
  change (if sixVertexRectangleBoundary ω = sixVertexBoundaryReflectHorizontal ξ
      then ω.weight c else 0) =
    if sixVertexRectangleBoundary (sixVertexRectangleReflectHorizontal ω) = ξ
      then (sixVertexRectangleReflectHorizontal ω).weight c else 0
  rw [sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectHorizontal_boundary]
  have hiff :
      sixVertexBoundaryReflectHorizontal (sixVertexRectangleBoundary ω) = ξ ↔
        sixVertexRectangleBoundary ω = sixVertexBoundaryReflectHorizontal ξ := by
    constructor
    · intro h
      simpa using congrArg sixVertexBoundaryReflectHorizontal h
    · intro h
      simp [h]
  rw [if_congr hiff rfl rfl]



theorem sixVertexRectangleBoundaryPartitionSum_reflectVertical
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexBoundaryReflectVertical ξ) =
      sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleBoundaryPartitionSum,
    sixVertexRectangleBoundaryPartitionSum]
  apply Fintype.sum_equiv (sixVertexRectangleReflectVerticalEquiv N M)
  intro ω
  change (if sixVertexRectangleBoundary ω = sixVertexBoundaryReflectVertical ξ
      then ω.weight c else 0) =
    if sixVertexRectangleBoundary (sixVertexRectangleReflectVertical ω) = ξ
      then (sixVertexRectangleReflectVertical ω).weight c else 0
  rw [sixVertexRectangleReflectVertical_weight,
    sixVertexRectangleReflectVertical_boundary]
  have hiff :
      sixVertexBoundaryReflectVertical (sixVertexRectangleBoundary ω) = ξ ↔
        sixVertexRectangleBoundary ω = sixVertexBoundaryReflectVertical ξ := by
    constructor
    · intro h
      simpa using congrArg sixVertexBoundaryReflectVertical h
    · intro h
      simp [h]
  rw [if_congr hiff rfl rfl]

end StatMech.FrontierD

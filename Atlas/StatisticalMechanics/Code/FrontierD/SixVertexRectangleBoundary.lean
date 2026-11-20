/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.SixVertex

open Finset

namespace StatMech.FrontierD




@[ext]
structure SixVertexRectangleArrows (N M : ℕ) where
  horizontal : Fin (N + 1) × Fin M → Bool
  vertical : Fin N × Fin (M + 1) → Bool
deriving DecidableEq, Fintype

namespace SixVertexRectangleArrows

variable {N M : ℕ}


def incomingCount (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) : ℕ :=
  (ω.horizontal (v.1.castSucc, v.2)).toNat +
    (!ω.horizontal (v.1.succ, v.2)).toNat +
    (ω.vertical (v.1, v.2.castSucc)).toNat +
    (!ω.vertical (v.1, v.2.succ)).toNat


def IceRule (ω : SixVertexRectangleArrows N M) : Prop :=
  ∀ v, ω.incomingCount v = 2



def IsCType (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) : Prop :=
  ((ω.horizontal (v.1.castSucc, v.2)).toNat +
      (!ω.horizontal (v.1.succ, v.2)).toNat = 0) ∨
    ((ω.horizontal (v.1.castSucc, v.2)).toNat +
      (!ω.horizontal (v.1.succ, v.2)).toNat = 2)

noncomputable instance iceRuleDecidable (ω : SixVertexRectangleArrows N M) :
    Decidable ω.IceRule := Classical.propDecidable _

noncomputable instance isCTypeDecidable (ω : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) : Decidable (ω.IsCType v) :=
  Classical.propDecidable _



noncomputable def localWeight (c : ℝ) (ω : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) : ℝ :=
  if ω.incomingCount v = 2 then if ω.IsCType v then c else 1 else 0


noncomputable def weight (c : ℝ) (ω : SixVertexRectangleArrows N M) : ℝ :=
  ∏ v, ω.localWeight c v

theorem localWeight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    0 ≤ ω.localWeight c v := by
  unfold localWeight
  split_ifs <;> positivity

theorem weight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (ω : SixVertexRectangleArrows N M) : 0 ≤ ω.weight c := by
  exact Finset.prod_nonneg fun v _ => localWeight_nonneg hc ω v

end SixVertexRectangleArrows


@[ext]
structure SixVertexRectangleBoundary (N M : ℕ) where
  left : Fin M → Bool
  right : Fin M → Bool
  bottom : Fin N → Bool
  top : Fin N → Bool
deriving DecidableEq, Fintype


def sixVertexRectangleBoundary {N M : ℕ} (ω : SixVertexRectangleArrows N M) :
    SixVertexRectangleBoundary N M where
  left j := ω.horizontal (0, j)
  right j := ω.horizontal (Fin.last N, j)
  bottom i := ω.vertical (i, 0)
  top i := ω.vertical (i, Fin.last M)


abbrev SixVertexToroidalBoundary (N M : ℕ) :=
  (Fin M → Bool) × (Fin N → Bool)


def sixVertexToroidalRectangleBoundary {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : SixVertexRectangleBoundary N M where
  left := ξ.1
  right := ξ.1
  bottom := ξ.2
  top := ξ.2



def SixVertexToroidalBoundary.Balanced {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : Prop :=
  #{i | ξ.2 i} = N / 2

noncomputable instance sixVertexToroidalBoundaryBalancedDecidable {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : Decidable ξ.Balanced :=
  Classical.propDecidable _



noncomputable def sixVertexRectangleBoundaryPartitionSum
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) : ℝ :=
  ∑ ω : SixVertexRectangleArrows N M,
    if sixVertexRectangleBoundary ω = ξ then ω.weight c else 0



noncomputable def sixVertexRectangleFreePartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ω : SixVertexRectangleArrows N M, ω.weight c



noncomputable def sixVertexRectangleToroidalPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ξ : SixVertexToroidalBoundary N M,
    sixVertexRectangleBoundaryPartitionSum N M c
      (sixVertexToroidalRectangleBoundary ξ)


noncomputable def sixVertexRectangleBalancedPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ξ : SixVertexToroidalBoundary N M,
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0

theorem sixVertexRectangleBoundaryPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexRectangleBoundary N M) :
    0 ≤ sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  unfold sixVertexRectangleBoundaryPartitionSum
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact SixVertexRectangleArrows.weight_nonneg hc ω
  · exact le_rfl

theorem sixVertexRectangleToroidalPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleToroidalPartitionSum N M c := by
  unfold sixVertexRectangleToroidalPartitionSum
  exact Finset.sum_nonneg fun ξ _ =>
    sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _

theorem sixVertexRectangleBalancedPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleBalancedPartitionSum N M c := by
  unfold sixVertexRectangleBalancedPartitionSum
  apply Finset.sum_nonneg
  intro ξ hξ
  split_ifs
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _
  · exact le_rfl



theorem sixVertexRectangleFreePartitionSum_eq_sum_boundary
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleFreePartitionSum N M c =
      ∑ ξ : SixVertexRectangleBoundary N M,
        sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleFreePartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  simp



theorem sixVertexRectangleBalancedPartitionSum_le_toroidal
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      sixVertexRectangleToroidalPartitionSum N M c := by
  unfold sixVertexRectangleBalancedPartitionSum
  unfold sixVertexRectangleToroidalPartitionSum
  apply Finset.sum_le_sum
  intro ξ hξ
  split_ifs
  · exact le_rfl
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _


noncomputable def sixVertexRectangleMaxToroidalBoundaryPartitionSum
    (N M : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
    sixVertexRectangleBoundaryPartitionSum N M c
      (sixVertexToroidalRectangleBoundary ξ)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem sixVertexRectangleBoundaryPartitionSum_le_maxToroidal
    (N M : ℕ) (c : ℝ) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ≤
      sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  classical
  unfold sixVertexRectangleMaxToroidalBoundaryPartitionSum
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, rfl⟩

theorem sixVertexToroidalBoundary_card (N M : ℕ) :
    Fintype.card (SixVertexToroidalBoundary N M) = 2 ^ (N + M) := by
  simp [SixVertexToroidalBoundary, pow_add, mul_comm]




theorem sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleToroidalPartitionSum N M c ≤
      (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  rw [sixVertexRectangleToroidalPartitionSum]
  calc
    ∑ ξ : SixVertexToroidalBoundary N M,
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
        ≤ ∑ _ξ : SixVertexToroidalBoundary N M,
            sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
          apply Finset.sum_le_sum
          intro ξ hξ
          exact sixVertexRectangleBoundaryPartitionSum_le_maxToroidal N M c ξ
    _ = (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      simp only [Finset.card_univ]
      norm_cast
      exact sixVertexToroidalBoundary_card N M



theorem sixVertexRectangleMaxToroidalBoundary_exists
    (N M : ℕ) (c : ℝ) :
    ∃ ξ : SixVertexToroidalBoundary N M,
      sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ) =
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  obtain ⟨ξ, hξ, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem
      (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)) _)
  exact ⟨ξ, hmax⟩

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.SixVertexRectangleSymmetry

open Finset

namespace StatMech.FrontierD

@[simp] private theorem finAddCases_zero_succ {m n : ℕ} {α : Type*}
    (left : Fin (m + 1) → α) (right : Fin n → α) :
    Fin.addCases (m := m + 1) (n := n) left right 0 = left 0 := by
  change Fin.addCases left right (Fin.castAdd n (0 : Fin (m + 1))) = left 0
  rw [Fin.addCases_left]

@[simp] private theorem finAddCases_last_succ {m n : ℕ} {α : Type*}
    (left : Fin m → α) (right : Fin (n + 1) → α) :
    Fin.addCases (m := m) (n := n + 1) left right (Fin.last (m + n)) =
      right (Fin.last n) := by
  rw [← Fin.natAdd_last]
  exact Fin.addCases_right _

@[simp] private theorem finCastAdd_castSucc {w : ℕ} (i : Fin w) :
    (Fin.castAdd w i).castSucc = Fin.castAdd (w + 1) i := by
  ext
  rfl

@[simp] private theorem finCastAdd_castSucc_succ {n : ℕ} (i : Fin n) :
    (Fin.castAdd (n + 1) i.castSucc).succ = Fin.castAdd (n + 2) i.succ := by
  ext
  rfl

@[simp] private theorem finCastAdd_last_succ {n : ℕ} :
    (Fin.castAdd (n + 1) (Fin.last n)).succ =
      Fin.natAdd (n + 1) (0 : Fin (n + 2)) := by
  ext
  simp

@[simp] private theorem finAddCases_addNat_self {n : ℕ} {α : Type*}
    (left right : Fin n → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n) left right (Fin.addNat i n) = right i := by
  rw [show Fin.addNat i n = Fin.natAdd n i by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm], Fin.addCases_right]

private theorem finAddNat_eq_natAdd_self {n : ℕ} (i : Fin n) :
    Fin.addNat i n = Fin.natAdd n i := by
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

@[simp] private theorem finAddCases_addNat_castSucc_self {n : ℕ} {α : Type*}
    (left : Fin n → α) (right : Fin (n + 1) → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n + 1) left right
        (Fin.addNat i n).castSucc = right i.castSucc := by
  rw [show (Fin.addNat i n).castSucc = Fin.natAdd n i.castSucc by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm], Fin.addCases_right]

@[simp] private theorem finAddCases_addNat_succ_self {n : ℕ} {α : Type*}
    (left : Fin n → α) (right : Fin (n + 1) → α) (i : Fin n) :
    Fin.addCases (m := n) (n := n + 1) left right
        (Fin.addNat i n).succ = right i.succ := by
  rw [show (Fin.addNat i n).succ = Fin.natAdd n i.succ by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
    omega, Fin.addCases_right]





def sixVertexRectangleGlueQuadrants {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows (N + N) (M + M) where
  horizontal xy :=
    Fin.addCases (m := N) (n := N + 1)
      (fun xLeft =>
        Fin.addCases (m := M) (n := M)
          (fun yBottom => lowerLeft.horizontal (xLeft.castSucc, yBottom))
          (fun yTop => upperLeft.horizontal (xLeft.castSucc, yTop)) xy.2)
      (fun xRight =>
        Fin.addCases (m := M) (n := M)
          (fun yBottom => lowerRight.horizontal (xRight, yBottom))
          (fun yTop => upperRight.horizontal (xRight, yTop)) xy.2) xy.1
  vertical xy :=
    Fin.addCases (m := N) (n := N)
      (fun xLeft =>
        Fin.addCases (m := M) (n := M + 1)
          (fun yBottom => lowerLeft.vertical (xLeft, yBottom.castSucc))
          (fun yTop => upperLeft.vertical (xLeft, yTop)) xy.2)
      (fun xRight =>
        Fin.addCases (m := M) (n := M + 1)
          (fun yBottom => lowerRight.vertical (xRight, yBottom.castSucc))
          (fun yTop => upperRight.vertical (xRight, yTop)) xy.2) xy.1


def sixVertexRectangleGlueBoundary {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleBoundary N M) :
    SixVertexRectangleBoundary (N + N) (M + M) where
  left := Fin.addCases lowerLeft.left upperLeft.left
  right := Fin.addCases lowerRight.right upperRight.right
  bottom := Fin.addCases lowerLeft.bottom lowerRight.bottom
  top := Fin.addCases upperLeft.top upperRight.top

theorem sixVertexRectangleGlueQuadrants_boundary {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary
        (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight) =
      sixVertexRectangleGlueBoundary
        (sixVertexRectangleBoundary lowerLeft)
        (sixVertexRectangleBoundary lowerRight)
        (sixVertexRectangleBoundary upperLeft)
        (sixVertexRectangleBoundary upperRight) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  apply SixVertexRectangleBoundary.ext
  · funext y
    refine Fin.addCases ?_ ?_ y <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext y
    refine Fin.addCases ?_ ?_ y <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext x
    refine Fin.addCases ?_ ?_ x <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext x
    refine Fin.addCases ?_ ?_ x <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]



def SixVertexRectangleQuadrantsCompatible {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) : Prop :=
  (sixVertexRectangleBoundary lowerLeft).right =
      (sixVertexRectangleBoundary lowerRight).left ∧
    (sixVertexRectangleBoundary upperLeft).right =
      (sixVertexRectangleBoundary upperRight).left ∧
    (sixVertexRectangleBoundary lowerLeft).top =
      (sixVertexRectangleBoundary upperLeft).bottom ∧
    (sixVertexRectangleBoundary lowerRight).top =
      (sixVertexRectangleBoundary upperRight).bottom




theorem sixVertexRectangle_reflectedQuadrantsCompatible {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M)
    (ω₀ ω₁ ω₂ ω₃ : SixVertexRectangleArrows N M)
    (h₀ : sixVertexRectangleBoundary ω₀ = ξ)
    (h₁ : sixVertexRectangleBoundary ω₁ = ξ)
    (h₂ : sixVertexRectangleBoundary ω₂ = ξ)
    (h₃ : sixVertexRectangleBoundary ω₃ = ξ) :
    SixVertexRectangleQuadrantsCompatible
      ω₀
      (sixVertexRectangleReflectHorizontal ω₁)
      (sixVertexRectangleReflectVertical ω₂)
      (sixVertexRectangleReflectHorizontal
        (sixVertexRectangleReflectVertical ω₃)) := by
  rw [SixVertexRectangleQuadrantsCompatible,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    h₀, h₁, h₂, h₃]
  simp [sixVertexBoundaryReflectHorizontal, sixVertexBoundaryReflectVertical]



def sixVertexDoubledToroidalBoundary {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexToroidalBoundary (N + N) (M + M) :=
  (Fin.addCases ξ.1 (fun j => !ξ.1 j.rev),
    Fin.addCases ξ.2 (fun i => !ξ.2 i.rev))


theorem sixVertexRectangle_reflectedGlueBoundary_eq_toroidal {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleGlueBoundary
        (sixVertexToroidalRectangleBoundary ξ)
        (sixVertexBoundaryReflectHorizontal
          (sixVertexToroidalRectangleBoundary ξ))
        (sixVertexBoundaryReflectVertical
          (sixVertexToroidalRectangleBoundary ξ))
        (sixVertexBoundaryReflectHorizontal
          (sixVertexBoundaryReflectVertical
            (sixVertexToroidalRectangleBoundary ξ))) =
      sixVertexToroidalRectangleBoundary
        (sixVertexDoubledToroidalBoundary ξ) := by
  apply SixVertexRectangleBoundary.ext <;> funext k
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]



theorem sixVertexRectangleGlueQuadrants_localWeight_lowerLeft {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.castAdd N i, Fin.castAdd M j) =
      lowerLeft.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hright (j : Fin (M + 1)) :
      lowerLeft.horizontal (Fin.last (N + 1), j) =
        lowerRight.horizontal (0, j) := by
    have h := congrFun hcompat.1 j
    simpa [sixVertexRectangleBoundary] using h
  have htop (i : Fin (N + 1)) :
      lowerLeft.vertical (i, Fin.last (M + 1)) =
        upperLeft.vertical (i, 0) := by
    have h := congrFun hcompat.2.2.1 i
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, hright, htop]
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, hright]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, htop]
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants]



theorem sixVertexRectangleGlueQuadrants_localWeight_lowerRight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.natAdd N i, Fin.castAdd M j) =
      lowerRight.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have htop (i : Fin (N + 1)) :
      lowerRight.vertical (i, Fin.last (M + 1)) =
        upperRight.vertical (i, 0) := by
    have h := congrFun hcompat.2.2.2 i
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants, htop]
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants]



theorem sixVertexRectangleGlueQuadrants_localWeight_upperLeft {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.castAdd N i, Fin.natAdd M j) =
      upperLeft.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hright (j : Fin (M + 1)) :
      upperLeft.horizontal (Fin.last (N + 1), j) =
        upperRight.horizontal (0, j) := by
    have h := congrFun hcompat.2.1 j
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants, hright]
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants]



theorem sixVertexRectangleGlueQuadrants_localWeight_upperRight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.natAdd N i, Fin.natAdd M j) =
      upperRight.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  simp [SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleGlueQuadrants]



theorem sixVertexRectangleGlueQuadrants_weight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight) :
    (sixVertexRectangleGlueQuadrants
        lowerLeft lowerRight upperLeft upperRight).weight c =
      lowerLeft.weight c * lowerRight.weight c *
        upperLeft.weight c * upperRight.weight c := by
  let e : (Fin N ⊕ Fin N) × (Fin M ⊕ Fin M) ≃
      Fin (N + N) × Fin (M + M) :=
    finSumFinEquiv.prodCongr finSumFinEquiv
  rw [SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin (N + N) × Fin (M + M),
        (sixVertexRectangleGlueQuadrants
          lowerLeft lowerRight upperLeft upperRight).localWeight c v =
      ∏ v : (Fin N ⊕ Fin N) × (Fin M ⊕ Fin M),
        (sixVertexRectangleGlueQuadrants
          lowerLeft lowerRight upperLeft upperRight).localWeight c (e v) :=
        (e.prod_comp _).symm
    _ = (∏ i : Fin N, ∏ j : Fin M, lowerLeft.localWeight c (i, j)) *
          (∏ i : Fin N, ∏ j : Fin M, upperLeft.localWeight c (i, j)) *
          ((∏ i : Fin N, ∏ j : Fin M, lowerRight.localWeight c (i, j)) *
          (∏ i : Fin N, ∏ j : Fin M, upperRight.localWeight c (i, j))) := by
      simp only [e, Equiv.prodCongr_apply, Prod.map_apply,
        Fintype.prod_prod_type,
        Fintype.prod_sum_type, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right]
      simp only [
        sixVertexRectangleGlueQuadrants_localWeight_lowerLeft
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_lowerRight
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_upperLeft
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_upperRight
          hN hM c lowerLeft lowerRight upperLeft upperRight]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = lowerLeft.weight c * lowerRight.weight c *
          upperLeft.weight c * upperRight.weight c := by
      simp only [SixVertexRectangleArrows.weight, Fintype.prod_prod_type]
      ring

private theorem sixVertexRectangleGlueQuadrants_lowerLeft_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₀ =
      sixVertexRectangleBoundary b₀) :
    a₀ = b₀ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) x
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.right hboundary) y
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.horizontal
          (Fin.castAdd (N + 1) i, Fin.castAdd M y)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun j => ?_) y
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.top hboundary) x
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.vertical
          (Fin.castAdd N x, Fin.castAdd (M + 1) j)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h

private theorem sixVertexRectangleGlueQuadrants_lowerRight_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₁ =
      sixVertexRectangleBoundary b₁) :
    a₁ = b₁ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.horizontal
        (Fin.natAdd N x, Fin.castAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun j => ?_) y
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.top hboundary) x
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.vertical
          (Fin.natAdd N x, Fin.castAdd (M + 1) j)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h

private theorem sixVertexRectangleGlueQuadrants_upperLeft_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₂ =
      sixVertexRectangleBoundary b₂) :
    a₂ = b₂ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) x
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.right hboundary) y
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.horizontal
          (Fin.castAdd (N + 1) i, Fin.natAdd M y)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.vertical
        (Fin.castAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h

private theorem sixVertexRectangleGlueQuadrants_upperRight_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃) :
    a₃ = b₃ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.horizontal
        (Fin.natAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.vertical
        (Fin.natAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h


abbrev SixVertexRectangleBoundaryFiber {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :=
  {omega : SixVertexRectangleArrows N M // sixVertexRectangleBoundary omega = ξ}


abbrev SixVertexRectangleFourBoundaryCopies {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :=
  SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ



def sixVertexRectangleReflectedGlue {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    SixVertexRectangleArrows (N + N) (M + M) :=
  sixVertexRectangleGlueQuadrants omega.1.1
    (sixVertexRectangleReflectHorizontal omega.2.1.1)
    (sixVertexRectangleReflectVertical omega.2.2.1.1)
    (sixVertexRectangleReflectHorizontal
      (sixVertexRectangleReflectVertical omega.2.2.2.1))

theorem sixVertexRectangleReflectedGlue_compatible {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    SixVertexRectangleQuadrantsCompatible omega.1.1
      (sixVertexRectangleReflectHorizontal omega.2.1.1)
      (sixVertexRectangleReflectVertical omega.2.2.1.1)
      (sixVertexRectangleReflectHorizontal
        (sixVertexRectangleReflectVertical omega.2.2.2.1)) := by
  exact sixVertexRectangle_reflectedQuadrantsCompatible ξ
    omega.1.1 omega.2.1.1 omega.2.2.1.1 omega.2.2.2.1
    omega.1.2 omega.2.1.2 omega.2.2.1.2 omega.2.2.2.2


theorem sixVertexRectangleReflectedGlue_boundary {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    {ξ : SixVertexToroidalBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies
      (sixVertexToroidalRectangleBoundary ξ)) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectedGlue omega) =
      sixVertexToroidalRectangleBoundary
        (sixVertexDoubledToroidalBoundary ξ) := by
  rw [sixVertexRectangleReflectedGlue,
    sixVertexRectangleGlueQuadrants_boundary hN hM,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    omega.1.2, omega.2.1.2, omega.2.2.1.2, omega.2.2.2.2]
  exact sixVertexRectangle_reflectedGlueBoundary_eq_toroidal ξ


theorem sixVertexRectangleReflectedGlue_weight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    (sixVertexRectangleReflectedGlue omega).weight c =
      omega.1.1.weight c * omega.2.1.1.weight c *
        omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
  rw [sixVertexRectangleReflectedGlue,
    sixVertexRectangleGlueQuadrants_weight hN hM c _ _ _ _
      (sixVertexRectangleReflectedGlue_compatible omega),
    sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectVertical_weight,
    sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectVertical_weight]


theorem sixVertexRectangleReflectedGlue_injective {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M} :
    Function.Injective
      (sixVertexRectangleReflectedGlue :
        SixVertexRectangleFourBoundaryCopies ξ →
          SixVertexRectangleArrows (N + N) (M + M)) := by
  intro omega eta hglue
  have h₀ : omega.1.1 = eta.1.1 :=
    sixVertexRectangleGlueQuadrants_lowerLeft_injective hglue
      (omega.1.2.trans eta.1.2.symm)
  have hb₁ :
      sixVertexRectangleBoundary
          (sixVertexRectangleReflectHorizontal omega.2.1.1) =
        sixVertexRectangleBoundary
          (sixVertexRectangleReflectHorizontal eta.2.1.1) := by
    calc
      _ = sixVertexBoundaryReflectHorizontal
          (sixVertexRectangleBoundary omega.2.1.1) :=
        sixVertexRectangleReflectHorizontal_boundary _
      _ = sixVertexBoundaryReflectHorizontal ξ := by rw [omega.2.1.2]
      _ = sixVertexBoundaryReflectHorizontal
          (sixVertexRectangleBoundary eta.2.1.1) := by rw [eta.2.1.2]
      _ = _ := (sixVertexRectangleReflectHorizontal_boundary _).symm
  have href₁ :
      sixVertexRectangleReflectHorizontal omega.2.1.1 =
        sixVertexRectangleReflectHorizontal eta.2.1.1 :=
    sixVertexRectangleGlueQuadrants_lowerRight_injective hglue hb₁
  have h₁ : omega.2.1.1 = eta.2.1.1 := by
    simpa using congrArg sixVertexRectangleReflectHorizontal href₁
  have hb₂ :
      sixVertexRectangleBoundary
          (sixVertexRectangleReflectVertical omega.2.2.1.1) =
        sixVertexRectangleBoundary
          (sixVertexRectangleReflectVertical eta.2.2.1.1) := by
    calc
      _ = sixVertexBoundaryReflectVertical
          (sixVertexRectangleBoundary omega.2.2.1.1) :=
        sixVertexRectangleReflectVertical_boundary _
      _ = sixVertexBoundaryReflectVertical ξ := by rw [omega.2.2.1.2]
      _ = sixVertexBoundaryReflectVertical
          (sixVertexRectangleBoundary eta.2.2.1.1) := by rw [eta.2.2.1.2]
      _ = _ := (sixVertexRectangleReflectVertical_boundary _).symm
  have href₂ :
      sixVertexRectangleReflectVertical omega.2.2.1.1 =
        sixVertexRectangleReflectVertical eta.2.2.1.1 :=
    sixVertexRectangleGlueQuadrants_upperLeft_injective hglue hb₂
  have h₂ : omega.2.2.1.1 = eta.2.2.1.1 := by
    simpa using congrArg sixVertexRectangleReflectVertical href₂
  have href₃ :
      sixVertexRectangleReflectHorizontal
          (sixVertexRectangleReflectVertical omega.2.2.2.1) =
        sixVertexRectangleReflectHorizontal
          (sixVertexRectangleReflectVertical eta.2.2.2.1) :=
    sixVertexRectangleGlueQuadrants_upperRight_injective hglue
  have h₃ : omega.2.2.2.1 = eta.2.2.2.1 := by
    have h := congrArg
      (fun rho => sixVertexRectangleReflectVertical
        (sixVertexRectangleReflectHorizontal rho)) href₃
    simpa using h
  apply Prod.ext
  · exact Subtype.ext h₀
  · apply Prod.ext
    · exact Subtype.ext h₁
    · apply Prod.ext
      · exact Subtype.ext h₂
      · exact Subtype.ext h₃


def sixVertexRectangleReflectedGlueBoundaryFiber {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexRectangleFourBoundaryCopies
        (sixVertexToroidalRectangleBoundary ξ) →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexDoubledToroidalBoundary ξ)) :=
  fun omega => ⟨sixVertexRectangleReflectedGlue omega,
    sixVertexRectangleReflectedGlue_boundary hN hM omega⟩

theorem sixVertexRectangleReflectedGlueBoundaryFiber_injective {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (ξ : SixVertexToroidalBoundary N M) :
    Function.Injective
      (sixVertexRectangleReflectedGlueBoundaryFiber hN hM ξ) := by
  intro omega eta h
  apply sixVertexRectangleReflectedGlue_injective
  exact congrArg Subtype.val h


theorem sixVertexRectangleBoundaryPartitionSum_eq_fiberSum
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c ξ =
      ∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c := by
  rw [sixVertexRectangleBoundaryPartitionSum]
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun omega : SixVertexRectangleArrows N M =>
      sixVertexRectangleBoundary omega = ξ) (by simp)]
  exact (Finset.sum_filter _ _).symm



theorem sixVertexRectangleBoundaryPartitionSum_pow_four
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c ξ ^ 4 =
      ∑ omega : SixVertexRectangleFourBoundaryCopies ξ,
        omega.1.1.weight c * omega.2.1.1.weight c *
          omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  rw [show (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) ^ 4 =
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) *
      (∑ omega : SixVertexRectangleBoundaryFiber ξ, omega.1.weight c) by ring]
  simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  apply Fintype.sum_congr
  intro omega₀
  apply Fintype.sum_congr
  intro omega₁
  apply Fintype.sum_congr
  intro omega₂
  apply Fintype.sum_congr
  intro omega₃
  ring



theorem sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤
      sixVertexRectangleBoundaryPartitionSum (N + N) (M + M) c
        (sixVertexToroidalRectangleBoundary
          (sixVertexDoubledToroidalBoundary ξ)) := by
  rw [sixVertexRectangleBoundaryPartitionSum_pow_four]
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  let glue := sixVertexRectangleReflectedGlueBoundaryFiber hN hM ξ
  calc
    ∑ omega : SixVertexRectangleFourBoundaryCopies
          (sixVertexToroidalRectangleBoundary ξ),
        omega.1.1.weight c * omega.2.1.1.weight c *
          omega.2.2.1.1.weight c * omega.2.2.2.1.weight c =
      ∑ omega : SixVertexRectangleFourBoundaryCopies
          (sixVertexToroidalRectangleBoundary ξ),
        (glue omega).1.weight c := by
          apply Fintype.sum_congr
          intro omega
          exact (sixVertexRectangleReflectedGlue_weight hN hM c omega).symm
    _ = ∑ eta ∈ Finset.univ.image glue, eta.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleReflectedGlueBoundaryFiber_injective
          hN hM ξ).injOn]
    _ ≤ ∑ eta : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary
            (sixVertexDoubledToroidalBoundary ξ)), eta.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro eta heta hnot
        exact SixVertexRectangleArrows.weight_nonneg hc eta.1



theorem sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ^ 4 ≤
      sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
  refine (sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary
    hN hM hc ξ).trans ?_
  unfold sixVertexRectangleToroidalPartitionSum
  exact Finset.single_le_sum
    (fun eta _ => sixVertexRectangleBoundaryPartitionSum_nonneg
      (N + N) (M + M) hc (sixVertexToroidalRectangleBoundary eta))
    (Finset.mem_univ (sixVertexDoubledToroidalBoundary ξ))



theorem sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c ^ 4 ≤
      sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c := by
  obtain ⟨ξ, hξ⟩ :=
    sixVertexRectangleMaxToroidalBoundary_exists N M c
  rw [← hξ]
  exact sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledToroidal
    hN hM hc ξ

end StatMech.FrontierD

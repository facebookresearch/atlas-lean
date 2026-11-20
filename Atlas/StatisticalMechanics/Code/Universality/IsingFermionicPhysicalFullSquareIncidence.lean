/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Code.Universality.IsingFermionicPhysicalFullSquareGhost









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFullVertexCoordinate
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Int × Int := (x.1 0 + x.1 1, x.1 0 - x.1 1)

def fkIsingSquareFullFaceCoordinate
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    Int × Int :=
  let p := fkIsingSquareInteriorCellKey n c
  (p.1 + p.2 + 1, p.1 - p.2)

abbrev FKIsingSquareFullRadialNode (n : Nat) :=
  FKIsingSquareFullVertexNode n ⊕ FKIsingSquareFullFaceNode n

def fkIsingSquareFullRadialNodeCoordinate
    (n : Nat) : FKIsingSquareFullRadialNode n → Int × Int
  | .inl x => fkIsingSquareFullVertexCoordinate n x
  | .inr c => fkIsingSquareFullFaceCoordinate n c

theorem fkIsingSquareFullVertexCoordinate_sum_even
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Even ((fkIsingSquareFullVertexCoordinate n x).1 +
      (fkIsingSquareFullVertexCoordinate n x).2) := by
  refine ⟨x.1 0, ?_⟩
  simp [fkIsingSquareFullVertexCoordinate]

theorem fkIsingSquareFullFaceCoordinate_sum_not_even
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    ¬ Even ((fkIsingSquareFullFaceCoordinate n c).1 +
      (fkIsingSquareFullFaceCoordinate n c).2) := by
  rintro ⟨k, hk⟩
  simp [fkIsingSquareFullFaceCoordinate] at hk
  omega

theorem fkIsingSquareFull_exists_incidence_of_radiallyAdjacent
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1 + (1 : Int),
            (fkIsingSquareFullVertexCoordinate n x).2) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1,
            (fkIsingSquareFullVertexCoordinate n x).2 + (1 : Int)) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1 - (1 : Int),
            (fkIsingSquareFullVertexCoordinate n x).2) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1,
            (fkIsingSquareFullVertexCoordinate n x).2 - (1 : Int))) :
    ∃ e : FKIsingSquareInteriorRadialIncidence n hn,
      fkIsingSquareInteriorRadialEndpoint n hn e = x ∧
        fkIsingSquareInteriorRadialFaceKey n hn e =
          fkIsingSquareInteriorCellKey n c := by
  rcases h with h | h | h | h
  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change x.1 0 < (n : Int)
      omega
    let d := fkIsingSquareDirectionDart n x .east heast .counterclockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey

  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change x.1 0 < (n : Int)
      omega
    let d := fkIsingSquareDirectionDart n x .east heast .clockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey
  · have hwest : fkIsingSquareDirectionAvailable n x .west := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change -(n : Int) < x.1 0
      omega
    let d := fkIsingSquareDirectionDart n x .west hwest .counterclockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey
  · have hwest : fkIsingSquareDirectionAvailable n x .west := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change -(n : Int) < x.1 0
      omega
    let d := fkIsingSquareDirectionDart n x .west hwest .clockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey

def FKIsingSquareFullRadiallyAdjacent
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n) : Prop :=
  fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1 + 1,
        (fkIsingSquareFullVertexCoordinate n x).2) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1,
        (fkIsingSquareFullVertexCoordinate n x).2 + 1) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1 - 1,
        (fkIsingSquareFullVertexCoordinate n x).2) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1,
        (fkIsingSquareFullVertexCoordinate n x).2 - 1)

noncomputable def fkIsingSquareFullIncidenceOfAdjacent
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  Classical.choose
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_endpoint
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = x :=
  (Classical.choose_spec
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)).1

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_faceKey
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareInteriorRadialFaceKey n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) =
      fkIsingSquareInteriorCellKey n c :=
  (Classical.choose_spec
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)).2

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_fullFace
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = c := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareFullIncidenceOfAdjacent_faceKey]

theorem fkIsingSquareFullIncidenceOfAdjacent_unique
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (hend : fkIsingSquareInteriorRadialEndpoint n hn e = x)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c) :
    e = fkIsingSquareFullIncidenceOfAdjacent n hn x c h := by
  apply fkIsingSquareInteriorRadialIncidence_ext n hn
  · simpa using hend
  · rw [fkIsingSquareFullIncidenceOfAdjacent_faceKey]
    rw [← fkIsingSquareFullFaceOfRadialIncidence_key n hn e, hface]

theorem fkIsingSquareFullVertexCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullVertexCoordinate n) := by
  intro x y h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  simp [fkIsingSquareFullVertexCoordinate] at h0 h1
  apply Subtype.ext
  funext k
  fin_cases k
  · change x.1 0 = y.1 0
    omega
  · change x.1 1 = y.1 1
    omega

theorem fkIsingSquareFullFaceCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullFaceCoordinate n) := by
  intro c d h
  apply fkIsingSquareInteriorCellKey_injective n
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  simp [fkIsingSquareFullFaceCoordinate] at h0 h1
  apply Prod.ext <;> omega

theorem fkIsingSquareFullRadialNodeCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullRadialNodeCoordinate n) := by
  intro a b h
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact congrArg Sum.inl
            (fkIsingSquareFullVertexCoordinate_injective n h)
      | inr c =>
          exfalso
          have heven := fkIsingSquareFullVertexCoordinate_sum_even n x
          have hodd := fkIsingSquareFullFaceCoordinate_sum_not_even n c
          change fkIsingSquareFullVertexCoordinate n x =
            fkIsingSquareFullFaceCoordinate n c at h
          rw [h] at heven
          exact hodd heven
  | inr c =>
      cases b with
      | inl x =>
          exfalso
          have heven := fkIsingSquareFullVertexCoordinate_sum_even n x
          have hodd := fkIsingSquareFullFaceCoordinate_sum_not_even n c
          change fkIsingSquareFullFaceCoordinate n c =
            fkIsingSquareFullVertexCoordinate n x at h
          rw [← h] at heven
          exact hodd heven
      | inr d =>
          exact congrArg Sum.inr
            (fkIsingSquareFullFaceCoordinate_injective n h)

theorem fkIsingSquareFull_radiallyAdjacent_of_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    FKIsingSquareFullRadiallyAdjacent n
      (fkIsingSquareInteriorRadialEndpoint n hn e)
      (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  simpa [FKIsingSquareFullRadiallyAdjacent,
    fkIsingSquareFullVertexCoordinate,
    fkIsingSquareFullFaceCoordinate,
    fkIsingSquareInteriorRadialPrimalCoordinate,
    fkIsingSquareInteriorRadialFaceCoordinate] using
      fkIsingSquareInteriorRadial_coordinates_adjacent n hn e

theorem fkIsingSquareFullIncidenceOfAdjacent_of_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullIncidenceOfAdjacent n hn
        (fkIsingSquareInteriorRadialEndpoint n hn e)
        (fkIsingSquareFullFaceOfRadialIncidence n hn e)
        (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e) = e := by
  symm
  apply fkIsingSquareFullIncidenceOfAdjacent_unique
  · rfl
  · rfl

end

end StatMech.Universality

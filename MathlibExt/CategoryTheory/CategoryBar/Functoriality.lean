/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.Basic

/-!
# Category bar: degreewise coefficient maps

For fixed `C`, natural transformations `αR : R ⟶ R'` and `αL : L ⟶ L'`
induce degreewise maps `barObj C R L n → barObj C R' L' n`, with computation
lemmas for the underlying chain and coefficient projections, face/degeneracy
naturality, packaged `Data`/`SSet` maps, and identity/composition laws.

Endpoint convention as in `Basic`: `L` at the source, `R` at the target, `d₀`
acts through `L`, last face through `R`.

Provenance: same two-sided bar sources as `Basic` (nLab two-sided bar
construction overview and Shulman, *Homotopy limits and colimits and enriched
homotopy theory*, `arXiv:math/0610194`); strict ordinary specialization only.

Nonclaims: no index-category change or mixed coefficient/index laws (see
`Change`), no nerve/comma/Grothendieck comparison, no contraction or extra
degeneracy, and no weak-equivalence or realization consequence yet.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uR uL

namespace CategoryTheory

namespace CategoryBar

variable {C : Type u} [Category.{v} C]
variable {R R' : Cᵒᵖ ⥤ Type uR} {L L' : C ⥤ Type uL}

/-- Degreewise map induced by coefficient natural transformations. -/
def barCoeffMap (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ} :
    barObj C R L n → barObj C R' L' n
  | ⟨F, l, r⟩ => ⟨F, αL.app F.left l, αR.app (op F.right) r⟩

@[simp]
theorem barCoeffMap_mk (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (F : ComposableArrows C n) (l : L.obj F.left) (r : R.obj (op F.right)) :
    barCoeffMap (C := C) αR αL (⟨F, l, r⟩ : barObj C R L n) =
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ : barObj C R' L' n) :=
  rfl

@[simp]
theorem barCoeffMap_chain (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (x : barObj C R L n) :
    barChain (barCoeffMap (C := C) αR αL x) = barChain x := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barCoeffMap_coeffL (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (x : barObj C R L n) :
    barCoeffL (barCoeffMap (C := C) αR αL x) =
      αL.app (barChain x).left (barCoeffL x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barCoeffMap_coeffR (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (x : barObj C R L n) :
    barCoeffR (barCoeffMap (C := C) αR αL x) =
      αR.app (op (barChain x).right) (barCoeffR x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barCoeffMap_id {n : ℕ} (x : barObj C R L n) :
    barCoeffMap (𝟙 R) (𝟙 L) x = x := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barCoeffMap_comp {R'' : Cᵒᵖ ⥤ Type uR} {L'' : C ⥤ Type uL}
    (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'')
    {n : ℕ} (x : barObj C R L n) :
    barCoeffMap βR βL (barCoeffMap αR αL x) =
      barCoeffMap (αR ≫ βR) (αL ≫ βL) x := by
  obtain ⟨F, l, r⟩ := x
  rfl

/-- A left coefficient natural-transformation component commutes with a cast. -/
private theorem coeffL_cast_comm (αL : L ⟶ L') {X Y : C} (h : X = Y)
    (x : L.obj X) :
    αL.app Y (cast (congrArg L.obj h) x) =
      cast (congrArg L'.obj h) (αL.app X x) := by
  cases h
  rfl

/-- A right coefficient natural-transformation component commutes with a cast. -/
private theorem coeffR_cast_comm (αR : R ⟶ R') {X Y : C} (h : X = Y)
    (x : R.obj (op X)) :
    αR.app (op Y) (cast (congrArg (fun Z => R.obj (op Z)) h) x) =
      cast (congrArg (fun Z => R'.obj (op Z)) h) (αR.app (op X) x) := by
  cases h
  rfl

/-- Element-level naturality for a left coefficient map. -/
private theorem coeffL_map_naturality (αL : L ⟶ L') {X Y : C} (f : X ⟶ Y)
    (x : L.obj X) :
    αL.app Y (L.map f x) = L'.map f (αL.app X x) :=
  NatTrans.naturality_apply αL f x

private theorem barCoeffMap_δ_zero (αR : R ⟶ R') (αL : L ⟶ L')
    (n : ℕ) (x : barObj C R L (n + 1)) :
    barCoeffMap αR αL (barδ (R := R) (L := L) (0 : Fin (n + 2)) x) =
      barδ (R := R') (L := L') (0 : Fin (n + 2)) (barCoeffMap αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
  have hMapY : barCoeffMap αR αL y =
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) := by
    rw [hy]
    rfl
  have hDeltaY : barδ (R := R) (L := L) (0 : Fin (n + 2)) y =
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        cast (congrArg L.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L.map (F.map' 0 1) l),
        cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          r⟩ : barObj C R L n) := by
    rw [barδ_zero_eq y, hy]
  have hDeltaMap : barδ (R := R') (L := L') (0 : Fin (n + 2))
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) =
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        cast (congrArg L'.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L'.map (F.map' 0 1) (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    have h := barδ_zero_eq (R := R') (L := L') (n := n)
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1))
    rw [h]
  have hLHS : barCoeffMap αR αL (barδ (R := R) (L := L) (0 : Fin (n + 2)) y) =
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        αL.app (((nerve C).δ (0 : Fin (n + 2)) F)).left
          (cast (congrArg L.obj (rfl : F.obj' 1 =
            ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L.map (F.map' 0 1) l)),
        αR.app (op (((nerve C).δ (0 : Fin (n + 2)) F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            r)⟩ : barObj C R' L' n) := by
    rw [hDeltaY]
    exact barCoeffMap_mk αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') (0 : Fin (n + 2))
      (barCoeffMap αR αL y) =
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        cast (congrArg L'.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L'.map (F.map' 0 1) (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    rw [hMapY]
    exact hDeltaMap
  have hLeft : αL.app (((nerve C).δ (0 : Fin (n + 2)) F)).left
        (cast (congrArg L.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L.map (F.map' 0 1) l)) =
        cast (congrArg L'.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L'.map (F.map' 0 1) (αL.app F.left l)) := by
    have h1 := coeffL_cast_comm αL
      (rfl : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 2)) F).left)
      (L.map (F.map' 0 1) l)
    have h2 := coeffL_map_naturality αL (F.map' 0 1) l
    exact h1.trans (congrArg _ h2)
  have hRight : αR.app (op (((nerve C).δ (0 : Fin (n + 2)) F)).right)
        (cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          r) =
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r) :=
    coeffR_cast_comm αR
      (show F.obj ⟨n + 1, by omega⟩ =
        ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
        rw [CategoryTheory.nerve.δ_obj]
        rfl) r
  have hMid :
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        αL.app (((nerve C).δ (0 : Fin (n + 2)) F)).left
          (cast (congrArg L.obj (rfl : F.obj' 1 =
            ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L.map (F.map' 0 1) l)),
        αR.app (op (((nerve C).δ (0 : Fin (n + 2)) F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            r)⟩ : barObj C R' L' n) =
      (⟨(nerve C).δ (0 : Fin (n + 2)) F,
        cast (congrArg L'.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L'.map (F.map' 0 1) (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    have hPair : (αL.app (((nerve C).δ (0 : Fin (n + 2)) F)).left
          (cast (congrArg L.obj (rfl : F.obj' 1 =
            ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L.map (F.map' 0 1) l)),
          αR.app (op (((nerve C).δ (0 : Fin (n + 2)) F)).right)
            (cast (congrArg (fun Z => R.obj (op Z))
              (show F.obj ⟨n + 1, by omega⟩ =
                ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
                rw [CategoryTheory.nerve.δ_obj]
                rfl))
              r)) =
        (cast (congrArg L'.obj (rfl : F.obj' 1 =
            ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L'.map (F.map' 0 1) (αL.app F.left l)),
          cast (congrArg (fun Z => R'.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            (αR.app (op F.right) r)) :=
      Prod.ext hLeft hRight
    exact Sigma.ext rfl (heq_of_eq hPair)
  exact hLHS.trans (hMid.trans hRHS.symm)

/-- Element-level naturality for a right coefficient map. -/
private theorem coeffR_map_naturality (αR : R ⟶ R') {X Y : C} (f : Y ⟶ X)
    (x : R.obj (op X)) :
    αR.app (op Y) (R.map (Quiver.Hom.op f) x) =
      R'.map (Quiver.Hom.op f) (αR.app (op X) x) :=
  NatTrans.naturality_apply αR (Quiver.Hom.op f) x

private theorem barCoeffMap_δ_last (αR : R ⟶ R') (αL : L ⟶ L')
    (n : ℕ) (x : barObj C R L (n + 1)) :
    barCoeffMap αR αL
        (barδ (R := R) (L := L) (Fin.last (n + 1)) x) =
      barδ (R := R') (L := L') (Fin.last (n + 1))
        (barCoeffMap αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
  have hMapY : barCoeffMap αR αL y =
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) := by
    rw [hy]
    rfl
  have hDeltaY : barδ (R := R) (L := L) (Fin.last (n + 1)) y =
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l,
        cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩ :
        barObj C R L n) := by
    rw [barδ_last_eq y, hy]
  have hDeltaMap : barδ (R := R') (L := L') (Fin.last (n + 1))
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) =
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op (F.map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj C R' L' n) := by
    have h := barδ_last_eq (R := R') (L := L') (n := n)
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1))
    rw [h]
  have hLHS : barCoeffMap αR αL
      (barδ (R := R) (L := L) (Fin.last (n + 1)) y) =
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        αL.app (((nerve C).δ (Fin.last (n + 1)) F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
        αR.app (op (((nerve C).δ (Fin.last (n + 1)) F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
              have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                  F.obj ⟨n, by omega⟩ := by
                rw [CategoryTheory.nerve.δ_obj]
                congr 1
                exact congrFun Fin.succAbove_last _
              exact h.symm))
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ :
        barObj C R' L' n) := by
    rw [hDeltaY]
    exact barCoeffMap_mk αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') (Fin.last (n + 1))
      (barCoeffMap αR αL y) =
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op (F.map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj C R' L' n) := by
    rw [hMapY]
    exact hDeltaMap
  have hLeft : αL.app (((nerve C).δ (Fin.last (n + 1)) F)).left
        (cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l) =
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l) :=
    coeffL_cast_comm αL
      (show F.obj ⟨0, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
        rw [CategoryTheory.nerve.δ_obj]
        rfl) l
  have hRight : αR.app (op (((nerve C).δ (Fin.last (n + 1)) F)).right)
        (cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)) =
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op (F.map' n (n + 1)))
            (αR.app (op F.right) r)) := by
    have hCast := coeffR_cast_comm αR
      (show F.obj ⟨n, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
        have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
            F.obj ⟨n, by omega⟩ := by
          rw [CategoryTheory.nerve.δ_obj]
          congr 1
          exact congrFun Fin.succAbove_last _
        exact h.symm)
      (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)
    have hNat := coeffR_map_naturality αR (F.map' n (n + 1)) r
    exact hCast.trans (congrArg _ hNat)
  have hMid :
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        αL.app (((nerve C).δ (Fin.last (n + 1)) F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
        αR.app (op (((nerve C).δ (Fin.last (n + 1)) F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
              have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                  F.obj ⟨n, by omega⟩ := by
                rw [CategoryTheory.nerve.δ_obj]
                congr 1
                exact congrFun Fin.succAbove_last _
              exact h.symm))
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ :
        barObj C R' L' n) =
      (⟨(nerve C).δ (Fin.last (n + 1)) F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
            have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                F.obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op (F.map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj C R' L' n) := by
    have hPair : (αL.app (((nerve C).δ (Fin.last (n + 1)) F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
          αR.app (op (((nerve C).δ (Fin.last (n + 1)) F)).right)
            (cast (congrArg (fun Z => R.obj (op Z))
              (show F.obj ⟨n, by omega⟩ =
                ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
                have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                    F.obj ⟨n, by omega⟩ := by
                  rw [CategoryTheory.nerve.δ_obj]
                  congr 1
                  exact congrFun Fin.succAbove_last _
                exact h.symm))
              (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))) =
        (cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
          cast (congrArg (fun Z => R'.obj (op Z))
            (show F.obj ⟨n, by omega⟩ =
              ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
              have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                  F.obj ⟨n, by omega⟩ := by
                rw [CategoryTheory.nerve.δ_obj]
                congr 1
                exact congrFun Fin.succAbove_last _
              exact h.symm))
            (R'.map (Quiver.Hom.op (F.map' n (n + 1)))
              (αR.app (op F.right) r))) :=
      Prod.ext hLeft hRight
    exact Sigma.ext rfl (heq_of_eq hPair)
  exact hLHS.trans (hMid.trans hRHS.symm)

private theorem barCoeffMap_δ_inner (αR : R ⟶ R') (αL : L ⟶ L')
    (n : ℕ) (q : Fin n) (x : barObj C R L (n + 1)) :
    barCoeffMap αR αL
        (barδ (R := R) (L := L) q.castSucc.succ x) =
      barδ (R := R') (L := L') q.castSucc.succ
        (barCoeffMap αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
  have hMapY : barCoeffMap αR αL y =
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) := by
    rw [hy]
    rfl
  have hDeltaY : barδ (R := R) (L := L) q.castSucc.succ y =
      (⟨(nerve C).δ q.castSucc.succ F,
        cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l,
        cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          r⟩ : barObj C R L n) := by
    rw [barδ_castSucc_succ_eq q y, hy]
  have hDeltaMap : barδ (R := R') (L := L') q.castSucc.succ
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1)) =
      (⟨(nerve C).δ q.castSucc.succ F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    have h := barδ_castSucc_succ_eq (R := R') (L := L') (n := n) q
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' (n + 1))
    rw [h]
  have hLHS : barCoeffMap αR αL
      (barδ (R := R) (L := L) q.castSucc.succ y) =
      (⟨(nerve C).δ q.castSucc.succ F,
        αL.app (((nerve C).δ q.castSucc.succ F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
        αR.app (op (((nerve C).δ q.castSucc.succ F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact (Fin.succAbove_ne_last_last (by
                apply ne_of_apply_ne Fin.val
                rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                have hq := q.isLt
                omega)).symm))
            r)⟩ :
        barObj C R' L' n) := by
    rw [hDeltaY]
    exact barCoeffMap_mk αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') q.castSucc.succ
      (barCoeffMap αR αL y) =
      (⟨(nerve C).δ q.castSucc.succ F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    rw [hMapY]
    exact hDeltaMap
  have hLeft : αL.app (((nerve C).δ q.castSucc.succ F)).left
        (cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l) =
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l) :=
    coeffL_cast_comm αL
      (show F.obj ⟨0, by omega⟩ =
        ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
        rw [CategoryTheory.nerve.δ_obj]
        rfl) l
  have hRight : αR.app (op (((nerve C).δ q.castSucc.succ F)).right)
        (cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          r) =
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r) :=
    coeffR_cast_comm αR
      (show F.obj ⟨n + 1, by omega⟩ =
        ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
        rw [CategoryTheory.nerve.δ_obj]
        congr 1
        exact (Fin.succAbove_ne_last_last (by
          apply ne_of_apply_ne Fin.val
          rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
          have hq := q.isLt
          omega)).symm) r
  have hMid :
      (⟨(nerve C).δ q.castSucc.succ F,
        αL.app (((nerve C).δ q.castSucc.succ F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
        αR.app (op (((nerve C).δ q.castSucc.succ F)).right)
          (cast (congrArg (fun Z => R.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact (Fin.succAbove_ne_last_last (by
                apply ne_of_apply_ne Fin.val
                rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                have hq := q.isLt
                omega)).symm))
            r)⟩ :
        barObj C R' L' n) =
      (⟨(nerve C).δ q.castSucc.succ F,
        cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj C R' L' n) := by
    have hPair : (αL.app (((nerve C).δ q.castSucc.succ F)).left
          (cast (congrArg L.obj
            (show F.obj ⟨0, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l),
          αR.app (op (((nerve C).δ q.castSucc.succ F)).right)
            (cast (congrArg (fun Z => R.obj (op Z))
              (show F.obj ⟨n + 1, by omega⟩ =
                ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
                rw [CategoryTheory.nerve.δ_obj]
                congr 1
                exact (Fin.succAbove_ne_last_last (by
                  apply ne_of_apply_ne Fin.val
                  rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                  have hq := q.isLt
                  omega)).symm))
              r)) =
        (cast (congrArg L'.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
          cast (congrArg (fun Z => R'.obj (op Z))
            (show F.obj ⟨n + 1, by omega⟩ =
              ((nerve C).δ q.castSucc.succ F).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact (Fin.succAbove_ne_last_last (by
                apply ne_of_apply_ne Fin.val
                rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                have hq := q.isLt
                omega)).symm))
            (αR.app (op F.right) r)) :=
      Prod.ext hLeft hRight
    exact Sigma.ext rfl (heq_of_eq hPair)
  exact hLHS.trans (hMid.trans hRHS.symm)

theorem barCoeffMap_δ (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (i : Fin (n + 2)) (x : barObj C R L (n + 1)) :
    barCoeffMap αR αL (barδ (R := R) (L := L) i x) =
      barδ (R := R') (L := L') i (barCoeffMap αR αL x) := by
  refine Fin.cases ?_ ?_ i
  · exact barCoeffMap_δ_zero αR αL n x
  · intro q
    refine Fin.lastCases ?_ ?_ q
    · exact barCoeffMap_δ_last αR αL n x
    · intro q'
      exact barCoeffMap_δ_inner αR αL n q' x

theorem barCoeffMap_σ (αR : R ⟶ R') (αL : L ⟶ L') {n : ℕ}
    (i : Fin (n + 1)) (x : barObj C R L n) :
    barCoeffMap αR αL (barσ (R := R) (L := L) i x) =
      barσ (R := R') (L := L') i (barCoeffMap αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  set y : barObj C R L n := ⟨F, l, r⟩ with hy
  have hMapY : barCoeffMap αR αL y =
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ :
        barObj C R' L' n) := by
    rw [hy]
    rfl
  have hL : F.left = ((nerve C).σ i F).left := by
    change F.obj ⟨0, by omega⟩ = ((nerve C).σ i F).obj (0 : Fin _)
    rw [CategoryTheory.nerve.σ_obj]
    have h : (⟨0, by omega⟩ : Fin (n + 1)) = i.predAbove (0 : Fin (n + 2)) :=
      Fin.predAbove_right_zero.symm
    exact congrArg _ h
  have hR : F.right = ((nerve C).σ i F).right := by
    change F.obj ⟨n, by omega⟩ = ((nerve C).σ i F).obj (Fin.last _)
    rw [CategoryTheory.nerve.σ_obj]
    congr 1
    exact Fin.predAbove_right_last.symm
  have hSigmaY : barσ (R := R) (L := L) i y =
      (⟨(nerve C).σ i F,
        cast (congrArg L.obj hL) l,
        cast (congrArg (fun Z => R.obj (op Z)) hR) r⟩ : barObj C R L (n + 1)) := by
    rw [hy]
    rfl
  have hSigmaMap : barσ (R := R') (L := L') i
      (⟨F, αL.app F.left l, αR.app (op F.right) r⟩ : barObj C R' L' n) =
      (⟨(nerve C).σ i F,
        cast (congrArg L'.obj hL) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hR) (αR.app (op F.right) r)⟩ :
        barObj C R' L' (n + 1)) := by
    rfl
  have hLHS : barCoeffMap αR αL (barσ (R := R) (L := L) i y) =
      (⟨(nerve C).σ i F,
        αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l),
        αR.app (op (((nerve C).σ i F)).right)
          (cast (congrArg (fun Z => R.obj (op Z)) hR) r)⟩ :
        barObj C R' L' (n + 1)) := by
    rw [hSigmaY]
    exact barCoeffMap_mk αR αL _ _ _
  have hRHS : barσ (R := R') (L := L') i (barCoeffMap αR αL y) =
      (⟨(nerve C).σ i F,
        cast (congrArg L'.obj hL) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hR) (αR.app (op F.right) r)⟩ :
        barObj C R' L' (n + 1)) := by
    rw [hMapY]
    exact hSigmaMap
  have hLeft : αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l) =
        cast (congrArg L'.obj hL) (αL.app F.left l) :=
    coeffL_cast_comm αL hL l
  have hRight : αR.app (op (((nerve C).σ i F)).right)
        (cast (congrArg (fun Z => R.obj (op Z)) hR) r) =
        cast (congrArg (fun Z => R'.obj (op Z)) hR) (αR.app (op F.right) r) :=
    coeffR_cast_comm αR hR r
  have hMid :
      (⟨(nerve C).σ i F,
        αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l),
        αR.app (op (((nerve C).σ i F)).right)
          (cast (congrArg (fun Z => R.obj (op Z)) hR) r)⟩ :
        barObj C R' L' (n + 1)) =
      (⟨(nerve C).σ i F,
        cast (congrArg L'.obj hL) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hR) (αR.app (op F.right) r)⟩ :
        barObj C R' L' (n + 1)) := by
    have hPair : (αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l),
          αR.app (op (((nerve C).σ i F)).right)
            (cast (congrArg (fun Z => R.obj (op Z)) hR) r)) =
        (cast (congrArg L'.obj hL) (αL.app F.left l),
          cast (congrArg (fun Z => R'.obj (op Z)) hR) (αR.app (op F.right) r)) :=
      Prod.ext hLeft hRight
    exact Sigma.ext rfl (heq_of_eq hPair)
  exact hLHS.trans (hMid.trans hRHS.symm)

/-- Data-level bar map induced by coefficient natural transformations. -/
def categoryBarDataMap (αR : R ⟶ R') (αL : L ⟶ L') :
    categoryBarData (C := C) (R := R) (L := L) ⟶
      categoryBarData (C := C) (R := R') (L := L') where
  app n := ↾(barCoeffMap αR αL (n := n))
  w_δ := fun i => by
    ext x
    exact (barCoeffMap_δ αR αL i x).symm
  w_σ := fun i => by
    ext x
    exact (barCoeffMap_σ αR αL i x).symm

@[simp]
theorem categoryBarDataMap_app (αR : R ⟶ R') (αL : L ⟶ L') (n : ℕ) :
    (categoryBarDataMap αR αL).app n = ↾(barCoeffMap αR αL (n := n)) :=
  rfl

@[simp]
theorem categoryBarDataMap_id :
    categoryBarDataMap (𝟙 R) (𝟙 L) = 𝟙 _ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  ext x
  exact barCoeffMap_id x

@[simp]
theorem categoryBarDataMap_comp {R'' : Cᵒᵖ ⥤ Type uR} {L'' : C ⥤ Type uL}
    (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'') :
    categoryBarDataMap αR αL ≫ categoryBarDataMap βR βL =
      categoryBarDataMap (αR ≫ βR) (αL ≫ βL) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  ext x
  exact barCoeffMap_comp αR αL βR βL x

/-- Simplicial bar map induced by coefficient natural transformations. -/
noncomputable def categoryBarMap (αR : R ⟶ R') (αL : L ⟶ L') :
    categoryBar (C := C) (R := R) (L := L) ⟶
      categoryBar (C := C) (R := R') (L := L') :=
  SimplicialObject.Data.toSimplicialFunctor.map (categoryBarDataMap αR αL)

@[simp]
theorem categoryBarMap_app_mk (αR : R ⟶ R') (αL : L ⟶ L') (n : ℕ) :
    (categoryBarMap αR αL).app (op (SimplexCategory.mk n)) =
      ↾(barCoeffMap αR αL (n := n)) :=
  rfl

@[simp]
theorem categoryBarMap_id :
    categoryBarMap (𝟙 R) (𝟙 L) = 𝟙 _ := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  simp only [categoryBarMap]
  simp only [SimplicialObject.Data.toSimplicialFunctor_map_app_mk]
  simp only [categoryBarDataMap_id]
  simp only [SimplicialObject.id_app]
  simp only [NatTrans.id_app]
  simp only [categoryBarData_obj]
  simp only [categoryBar_obj]

@[simp]
theorem categoryBarMap_comp {R'' : Cᵒᵖ ⥤ Type uR} {L'' : C ⥤ Type uL}
    (αR : R ⟶ R') (αL : L ⟶ L') (βR : R' ⟶ R'') (βL : L' ⟶ L'') :
    categoryBarMap αR αL ≫ categoryBarMap βR βL =
      categoryBarMap (αR ≫ βR) (αL ≫ βL) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  exact barCoeffMap_comp αR αL βR βL x

end CategoryBar

end CategoryTheory

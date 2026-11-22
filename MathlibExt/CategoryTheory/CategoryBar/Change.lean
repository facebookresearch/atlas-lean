/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.Functoriality

/-!
# Category bar: pointwise index-category change

For `Φ : C ⥤ D`, `αR : R ⟶ Φ.op ⋙ R'` and `αL : L ⟶ Φ ⋙ L'`, the degreewise
map `barObj C R L n → barObj D R' L' n` sends `⟨F, l, r⟩` to the mapped chain
with pushed-forward coefficients, with chain `δ`/`σ` commutation,
face/degeneracy naturality, packaged `Data`/`SSet` maps, and identity,
composition, and mixed coefficient/index laws.

Endpoint convention as in `Basic`: `L` at the source, `R` at the target, `d₀`
acts through `L`, last face through `R`.

Provenance: same two-sided bar sources as `Basic` (nLab two-sided bar
construction overview and Shulman, *Homotopy limits and colimits and enriched
homotopy theory*, `arXiv:math/0610194`); strict ordinary specialization only.

Nonclaims: no nerve/comma/Grothendieck comparison, no contraction or extra
degeneracy, and no weak-equivalence or realization consequence yet.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uR uL

namespace CategoryTheory

namespace CategoryBar

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {R : Cᵒᵖ ⥤ Type uR} {R' : Dᵒᵖ ⥤ Type uR}
variable {L : C ⥤ Type uL} {L' : D ⥤ Type uL}

/-- Pointwise index-category change map. -/
def barIdxMap (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} : barObj C R L n → barObj D R' L' n
  | ⟨F, l, r⟩ =>
      ⟨(Φ.mapComposableArrows n).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩

@[simp]
theorem barIdxMap_mk (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (F : ComposableArrows C n) (l : L.obj F.left)
    (r : R.obj (op F.right)) :
    barIdxMap (C := C) (D := D) Φ αR αL (⟨F, l, r⟩ : barObj C R L n) =
      (⟨(Φ.mapComposableArrows n).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' n) :=
  rfl

@[simp]
theorem barIdxMap_chain (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (x : barObj C R L n) :
    barChain (barIdxMap (C := C) (D := D) Φ αR αL x) =
      (Φ.mapComposableArrows n).obj (barChain x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barIdxMap_coeffL (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (x : barObj C R L n) :
    barCoeffL (barIdxMap (C := C) (D := D) Φ αR αL x) =
      αL.app (barChain x).left (barCoeffL x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

@[simp]
theorem barIdxMap_coeffR (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (x : barObj C R L n) :
    barCoeffR (barIdxMap (C := C) (D := D) Φ αR αL x) =
      αR.app (op (barChain x).right) (barCoeffR x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

theorem barIdxMap_chain_nerveMap (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    (αL : L ⟶ Φ ⋙ L') {n : ℕ} (x : barObj C R L n) :
    barChain (barIdxMap (C := C) (D := D) Φ αR αL x) =
      (nerveMap Φ).app (Opposite.op (SimplexCategory.mk n)) (barChain x) := by
  obtain ⟨F, l, r⟩ := x
  rfl

private theorem mapComposableArrows_nerveδ (Φ : C ⥤ D) {n : ℕ}
    (i : Fin (n + 2)) (F : ComposableArrows C (n + 1)) :
    (Φ.mapComposableArrows n).obj ((nerve C).δ i F) =
      (nerve D).δ i ((Φ.mapComposableArrows (n + 1)).obj F) :=
  SSet.δ_naturality_apply (f := nerveMap Φ) i F

private theorem mapComposableArrows_nerveσ (Φ : C ⥤ D) {n : ℕ}
    (i : Fin (n + 1)) (F : ComposableArrows C n) :
    (Φ.mapComposableArrows (n + 1)).obj ((nerve C).σ i F) =
      (nerve D).σ i ((Φ.mapComposableArrows n).obj F) :=
  SSet.σ_naturality_apply (f := nerveMap Φ) i F

private theorem idxCoeffL_cast_comm (Φ : C ⥤ D) (αL : L ⟶ Φ ⋙ L')
    {X Y : C} (h : X = Y) (x : L.obj X) :
    αL.app Y (cast (congrArg L.obj h) x) =
      cast (congrArg (fun Z => L'.obj (Φ.obj Z)) h) (αL.app X x) := by
  cases h
  rfl

private theorem barIdxMap_δ_zero (Φ : C ⥤ D)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (n : ℕ) (x : barObj C R L (n + 1)) :
    barIdxMap (C := C) (D := D) Φ αR αL
        (barδ (R := R) (L := L) (0 : Fin (n + 2)) x) =
      barδ (R := R') (L := L') (0 : Fin (n + 2))
        (barIdxMap (C := C) (D := D) Φ αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  have hChain : (Φ.mapComposableArrows n).obj ((nerve C).δ (0 : Fin (n + 2)) F) =
      (nerve D).δ (0 : Fin (n + 2)) ((Φ.mapComposableArrows (n + 1)).obj F) :=
    mapComposableArrows_nerveδ Φ _ F
  have hDeltaC : barδ (R := R) (L := L) (0 : Fin (n + 2))
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
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
    have h := barδ_zero_eq (R := R) (L := L) (n := n)
      (⟨F, l, r⟩ : barObj C R L (n + 1))
    rw [h]
  have hMap : barIdxMap (C := C) (D := D) Φ αR αL
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) :=
    barIdxMap_mk Φ αR αL F l r
  have hDeltaD : barδ (R := R') (L := L') (0 : Fin (n + 2))
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) =
      (⟨(nerve D).δ (0 : Fin (n + 2)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj (rfl : ((Φ.mapComposableArrows (n + 1)).obj F).obj' 1 =
          ((nerve D).δ (0 : Fin (n + 2))
            ((Φ.mapComposableArrows (n + 1)).obj F)).left))
          (L'.map (((Φ.mapComposableArrows (n + 1)).obj F).map' 0 1)
            (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ (0 : Fin (n + 2))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
    have h := barδ_zero_eq (R := R') (L := L') (n := n)
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1))
    rw [h]
  have hLHS : barIdxMap (C := C) (D := D) Φ αR αL
      (barδ (R := R) (L := L) (0 : Fin (n + 2))
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ (0 : Fin (n + 2)) F),
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
            r)⟩ : barObj D R' L' n) := by
    rw [hDeltaC]
    exact barIdxMap_mk Φ αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') (0 : Fin (n + 2))
      (barIdxMap (C := C) (D := D) Φ αR αL
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(nerve D).δ (0 : Fin (n + 2)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj (rfl : ((Φ.mapComposableArrows (n + 1)).obj F).obj' 1 =
          ((nerve D).δ (0 : Fin (n + 2))
            ((Φ.mapComposableArrows (n + 1)).obj F)).left))
          (L'.map (((Φ.mapComposableArrows (n + 1)).obj F).map' 0 1)
            (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ (0 : Fin (n + 2))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
    rw [hMap]
    exact hDeltaD
  have hLeft : αL.app (((nerve C).δ (0 : Fin (n + 2)) F)).left
        (cast (congrArg L.obj (rfl : F.obj' 1 =
          ((nerve C).δ (0 : Fin (n + 2)) F).left))
          (L.map (F.map' 0 1) l)) =
        cast (congrArg L'.obj (rfl : ((Φ.mapComposableArrows (n + 1)).obj F).obj' 1 =
          ((nerve D).δ (0 : Fin (n + 2))
            ((Φ.mapComposableArrows (n + 1)).obj F)).left))
          (L'.map (((Φ.mapComposableArrows (n + 1)).obj F).map' 0 1)
            (αL.app F.left l)) := by
    have h1 := idxCoeffL_cast_comm Φ αL
      (rfl : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 2)) F).left)
      (L.map (F.map' 0 1) l)
    have h2 := NatTrans.naturality_apply αL (F.map' 0 1) l
    exact h1.trans (congrArg _ h2)
  have hRight : αR.app (op (((nerve C).δ (0 : Fin (n + 2)) F)).right)
        (cast (congrArg (fun Z => R.obj (op Z))
          (show F.obj ⟨n + 1, by omega⟩ =
            ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          r) =
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ (0 : Fin (n + 2))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r) := by
    cases show F.obj ⟨n + 1, by omega⟩ =
        ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _) from by
      rw [CategoryTheory.nerve.δ_obj]
      rfl
    rfl
  have hMid :
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ (0 : Fin (n + 2)) F),
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
            r)⟩ : barObj D R' L' n) =
      (⟨(nerve D).δ (0 : Fin (n + 2)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj (rfl : ((Φ.mapComposableArrows (n + 1)).obj F).obj' 1 =
          ((nerve D).δ (0 : Fin (n + 2))
            ((Φ.mapComposableArrows (n + 1)).obj F)).left))
          (L'.map (((Φ.mapComposableArrows (n + 1)).obj F).map' 0 1)
            (αL.app F.left l)),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ (0 : Fin (n + 2))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
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
        (cast (congrArg L'.obj (rfl : ((Φ.mapComposableArrows (n + 1)).obj F).obj' 1 =
            ((nerve D).δ (0 : Fin (n + 2))
              ((Φ.mapComposableArrows (n + 1)).obj F)).left))
            (L'.map (((Φ.mapComposableArrows (n + 1)).obj F).map' 0 1)
              (αL.app F.left l)),
          cast (congrArg (fun Z => R'.obj (op Z))
            (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
              ((nerve D).δ (0 : Fin (n + 2))
                ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            (αR.app (op F.right) r)) :=
      Prod.ext hLeft hRight
    exact Sigma.ext hChain (heq_of_eq hPair)
  exact hLHS.trans (hMid.trans hRHS.symm)

private theorem idxCoeffR_cast_comm (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    {X Y : C} (h : X = Y) (x : R.obj (Opposite.op X)) :
    αR.app (Opposite.op Y)
        (cast (congrArg (fun Z => R.obj (Opposite.op Z)) h) x) =
      cast (congrArg (fun Z => R'.obj (Opposite.op (Φ.obj Z))) h)
        (αR.app (Opposite.op X) x) := by
  cases h
  rfl

private theorem barIdxMap_δ_last (Φ : C ⥤ D)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (n : ℕ) (x : barObj C R L (n + 1)) :
    barIdxMap (C := C) (D := D) Φ αR αL
        (barδ (R := R) (L := L) (Fin.last (n + 1)) x) =
      barδ (R := R') (L := L') (Fin.last (n + 1))
        (barIdxMap (C := C) (D := D) Φ αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  have hChain : (Φ.mapComposableArrows n).obj ((nerve C).δ (Fin.last (n + 1)) F) =
      (nerve D).δ (Fin.last (n + 1)) ((Φ.mapComposableArrows (n + 1)).obj F) :=
    mapComposableArrows_nerveδ Φ (Fin.last (n + 1)) F
  have hDeltaC : barδ (R := R) (L := L) (Fin.last (n + 1))
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
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
          (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩ : barObj C R L n) := by
    have h := barδ_last_eq (R := R) (L := L) (n := n)
      (⟨F, l, r⟩ : barObj C R L (n + 1))
    rw [h]
  have hMap : barIdxMap (C := C) (D := D) Φ αR αL
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) :=
    barIdxMap_mk Φ αR αL F l r
  have hDeltaD : barδ (R := R') (L := L') (Fin.last (n + 1))
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) =
      (⟨(nerve D).δ (Fin.last (n + 1)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            have h : ((nerve D).δ (Fin.last (n + 1))
                ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) =
                ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op
            (((Φ.mapComposableArrows (n + 1)).obj F).map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj D R' L' n) := by
    have h := barδ_last_eq (R := R') (L := L') (n := n)
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1))
    rw [h]
  have hLHS : barIdxMap (C := C) (D := D) Φ αR αL
      (barδ (R := R) (L := L) (Fin.last (n + 1))
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ (Fin.last (n + 1)) F),
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
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ : barObj D R' L' n) := by
    rw [hDeltaC]
    exact barIdxMap_mk Φ αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') (Fin.last (n + 1))
      (barIdxMap (C := C) (D := D) Φ αR αL
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(nerve D).δ (Fin.last (n + 1)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            have h : ((nerve D).δ (Fin.last (n + 1))
                ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) =
                ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op
            (((Φ.mapComposableArrows (n + 1)).obj F).map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj D R' L' n) := by
    rw [hMap]
    exact hDeltaD
  have hLeft : αL.app (((nerve C).δ (Fin.last (n + 1)) F)).left
        (cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l) =
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l) := by
    cases show F.obj ⟨0, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _) from by
      rw [CategoryTheory.nerve.δ_obj]
      rfl
    rfl
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
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            have h : ((nerve D).δ (Fin.last (n + 1))
                ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) =
                ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op
            (((Φ.mapComposableArrows (n + 1)).obj F).map' n (n + 1)))
            (αR.app (op F.right) r)) := by
    have h1 := idxCoeffR_cast_comm Φ αR
      (show F.obj ⟨n, by omega⟩ =
        ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) by
        have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
            F.obj ⟨n, by omega⟩ := by
          rw [CategoryTheory.nerve.δ_obj]
          congr 1
          exact congrFun Fin.succAbove_last _
        exact h.symm)
      (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)
    have h2 := NatTrans.naturality_apply αR (Quiver.Hom.op (F.map' n (n + 1))) r
    exact h1.trans (congrArg _ h2)
  have hMid :
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ (Fin.last (n + 1)) F),
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
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ : barObj D R' L' n) =
      (⟨(nerve D).δ (Fin.last (n + 1)) ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ =
            ((nerve D).δ (Fin.last (n + 1))
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            have h : ((nerve D).δ (Fin.last (n + 1))
                ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) =
                ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact congrFun Fin.succAbove_last _
            exact h.symm))
          (R'.map (Quiver.Hom.op
            (((Φ.mapComposableArrows (n + 1)).obj F).map' n (n + 1)))
            (αR.app (op F.right) r))⟩ : barObj D R' L' n) := by
    exact Sigma.ext hChain (heq_of_eq (Prod.ext hLeft hRight))
  exact hLHS.trans (hMid.trans hRHS.symm)

private theorem barIdxMap_δ_inner (Φ : C ⥤ D)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (n : ℕ) (q : Fin n) (x : barObj C R L (n + 1)) :
    barIdxMap (C := C) (D := D) Φ αR αL
        (barδ (R := R) (L := L) q.castSucc.succ x) =
      barδ (R := R') (L := L') q.castSucc.succ
        (barIdxMap (C := C) (D := D) Φ αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  have hChain : (Φ.mapComposableArrows n).obj ((nerve C).δ q.castSucc.succ F) =
      (nerve D).δ q.castSucc.succ ((Φ.mapComposableArrows (n + 1)).obj F) :=
    mapComposableArrows_nerveδ Φ q.castSucc.succ F
  have hDeltaC : barδ (R := R) (L := L) q.castSucc.succ
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
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
    have h := barδ_castSucc_succ_eq (R := R) (L := L) (n := n) q
      (⟨F, l, r⟩ : barObj C R L (n + 1))
    rw [h]
  have hMap : barIdxMap (C := C) (D := D) Φ αR αL
      (⟨F, l, r⟩ : barObj C R L (n + 1)) =
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) :=
    barIdxMap_mk Φ αR αL F l r
  have hDeltaD : barδ (R := R') (L := L') q.castSucc.succ
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1)) =
      (⟨(nerve D).δ q.castSucc.succ ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
    have h := barδ_castSucc_succ_eq (R := R') (L := L') (n := n) q
      (⟨(Φ.mapComposableArrows (n + 1)).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' (n + 1))
    rw [h]
  have hLHS : barIdxMap (C := C) (D := D) Φ αR αL
      (barδ (R := R) (L := L) q.castSucc.succ
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ q.castSucc.succ F),
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
            r)⟩ : barObj D R' L' n) := by
    rw [hDeltaC]
    exact barIdxMap_mk Φ αR αL _ _ _
  have hRHS : barδ (R := R') (L := L') q.castSucc.succ
      (barIdxMap (C := C) (D := D) Φ αR αL
        (⟨F, l, r⟩ : barObj C R L (n + 1))) =
      (⟨(nerve D).δ q.castSucc.succ ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
    rw [hMap]
    exact hDeltaD
  have hLeft : αL.app (((nerve C).δ q.castSucc.succ F)).left
        (cast (congrArg L.obj
          (show F.obj ⟨0, by omega⟩ =
            ((nerve C).δ q.castSucc.succ F).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          l) =
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l) :=
    idxCoeffL_cast_comm Φ αL
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
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r) :=
    idxCoeffR_cast_comm Φ αR
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
      (⟨(Φ.mapComposableArrows n).obj ((nerve C).δ q.castSucc.succ F),
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
            r)⟩ : barObj D R' L' n) =
      (⟨(nerve D).δ q.castSucc.succ ((Φ.mapComposableArrows (n + 1)).obj F),
        cast (congrArg L'.obj
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨0, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (0 : Fin _) by
            rw [CategoryTheory.nerve.δ_obj]
            rfl))
          (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z))
          (show ((Φ.mapComposableArrows (n + 1)).obj F).obj ⟨n + 1, by omega⟩ =
            ((nerve D).δ q.castSucc.succ
              ((Φ.mapComposableArrows (n + 1)).obj F)).obj (Fin.last _) by
            rw [CategoryTheory.nerve.δ_obj]
            congr 1
            exact (Fin.succAbove_ne_last_last (by
              apply ne_of_apply_ne Fin.val
              rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
              have hq := q.isLt
              omega)).symm))
          (αR.app (op F.right) r)⟩ : barObj D R' L' n) := by
    exact Sigma.ext hChain (heq_of_eq (Prod.ext hLeft hRight))
  exact hLHS.trans (hMid.trans hRHS.symm)

theorem barIdxMap_δ (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (i : Fin (n + 2)) (x : barObj C R L (n + 1)) :
    barIdxMap (C := C) (D := D) Φ αR αL (barδ (R := R) (L := L) i x) =
      barδ (R := R') (L := L') i (barIdxMap (C := C) (D := D) Φ αR αL x) := by
  refine Fin.cases ?_ ?_ i
  · exact barIdxMap_δ_zero Φ αR αL n x
  · intro q
    refine Fin.lastCases ?_ ?_ q
    · exact barIdxMap_δ_last Φ αR αL n x
    · intro q'
      exact barIdxMap_δ_inner Φ αR αL n q' x

theorem barIdxMap_σ (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    {n : ℕ} (i : Fin (n + 1)) (x : barObj C R L n) :
    barIdxMap (C := C) (D := D) Φ αR αL (barσ (R := R) (L := L) i x) =
      barσ (R := R') (L := L') i (barIdxMap (C := C) (D := D) Φ αR αL x) := by
  obtain ⟨F, l, r⟩ := x
  have hChain : (Φ.mapComposableArrows (n + 1)).obj ((nerve C).σ i F) =
      (nerve D).σ i ((Φ.mapComposableArrows n).obj F) :=
    mapComposableArrows_nerveσ Φ i F
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
  have hLD : ((Φ.mapComposableArrows n).obj F).left =
      ((nerve D).σ i ((Φ.mapComposableArrows n).obj F)).left := by
    change ((Φ.mapComposableArrows n).obj F).obj ⟨0, by omega⟩ =
      ((nerve D).σ i ((Φ.mapComposableArrows n).obj F)).obj (0 : Fin _)
    rw [CategoryTheory.nerve.σ_obj]
    have h : (⟨0, by omega⟩ : Fin (n + 1)) = i.predAbove (0 : Fin (n + 2)) :=
      Fin.predAbove_right_zero.symm
    exact congrArg _ h
  have hRD : ((Φ.mapComposableArrows n).obj F).right =
      ((nerve D).σ i ((Φ.mapComposableArrows n).obj F)).right := by
    change ((Φ.mapComposableArrows n).obj F).obj ⟨n, by omega⟩ =
      ((nerve D).σ i ((Φ.mapComposableArrows n).obj F)).obj (Fin.last _)
    rw [CategoryTheory.nerve.σ_obj]
    congr 1
    exact Fin.predAbove_right_last.symm
  have hSigmaC : barσ (R := R) (L := L) i
      (⟨F, l, r⟩ : barObj C R L n) =
      (⟨(nerve C).σ i F,
        cast (congrArg L.obj hL) l,
        cast (congrArg (fun Z => R.obj (op Z)) hR) r⟩ : barObj C R L (n + 1)) := by
    rfl
  have hSigmaD : barσ (R := R') (L := L') i
      (⟨(Φ.mapComposableArrows n).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' n) =
      (⟨(nerve D).σ i ((Φ.mapComposableArrows n).obj F),
        cast (congrArg L'.obj hLD) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hRD)
          (αR.app (op F.right) r)⟩ : barObj D R' L' (n + 1)) := by
    rfl
  have hMap : barIdxMap (C := C) (D := D) Φ αR αL
      (⟨F, l, r⟩ : barObj C R L n) =
      (⟨(Φ.mapComposableArrows n).obj F, αL.app F.left l,
        αR.app (op F.right) r⟩ : barObj D R' L' n) :=
    barIdxMap_mk Φ αR αL F l r
  have hLHS : barIdxMap (C := C) (D := D) Φ αR αL
      (barσ (R := R) (L := L) i (⟨F, l, r⟩ : barObj C R L n)) =
      (⟨(Φ.mapComposableArrows (n + 1)).obj ((nerve C).σ i F),
        αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l),
        αR.app (op (((nerve C).σ i F)).right)
          (cast (congrArg (fun Z => R.obj (op Z)) hR) r)⟩ :
        barObj D R' L' (n + 1)) := by
    rw [hSigmaC]
    exact barIdxMap_mk Φ αR αL _ _ _
  have hRHS : barσ (R := R') (L := L') i
      (barIdxMap (C := C) (D := D) Φ αR αL
        (⟨F, l, r⟩ : barObj C R L n)) =
      (⟨(nerve D).σ i ((Φ.mapComposableArrows n).obj F),
        cast (congrArg L'.obj hLD) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hRD)
          (αR.app (op F.right) r)⟩ : barObj D R' L' (n + 1)) := by
    rw [hMap]
    exact hSigmaD
  have hLeft : αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l) =
        cast (congrArg L'.obj hLD) (αL.app F.left l) :=
    idxCoeffL_cast_comm Φ αL hL l
  have hRight : αR.app (op (((nerve C).σ i F)).right)
        (cast (congrArg (fun Z => R.obj (op Z)) hR) r) =
        cast (congrArg (fun Z => R'.obj (op Z)) hRD) (αR.app (op F.right) r) :=
    idxCoeffR_cast_comm Φ αR hR r
  have hMid :
      (⟨(Φ.mapComposableArrows (n + 1)).obj ((nerve C).σ i F),
        αL.app (((nerve C).σ i F)).left (cast (congrArg L.obj hL) l),
        αR.app (op (((nerve C).σ i F)).right)
          (cast (congrArg (fun Z => R.obj (op Z)) hR) r)⟩ :
        barObj D R' L' (n + 1)) =
      (⟨(nerve D).σ i ((Φ.mapComposableArrows n).obj F),
        cast (congrArg L'.obj hLD) (αL.app F.left l),
        cast (congrArg (fun Z => R'.obj (op Z)) hRD)
          (αR.app (op F.right) r)⟩ : barObj D R' L' (n + 1)) := by
    exact Sigma.ext hChain (heq_of_eq (Prod.ext hLeft hRight))
  exact hLHS.trans (hMid.trans hRHS.symm)

/-- Data-level bar map induced by change of indexing category with coefficient maps. -/
def categoryBarIdxDataMap (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    (αL : L ⟶ Φ ⋙ L') :
    categoryBarData (C := C) (R := R) (L := L) ⟶
      categoryBarData (C := D) (R := R') (L := L') where
  app n := ↾(barIdxMap Φ αR αL (n := n))
  w_δ := fun i => by
    ext x
    exact (barIdxMap_δ Φ αR αL i x).symm
  w_σ := fun i => by
    ext x
    exact (barIdxMap_σ Φ αR αL i x).symm

@[simp]
theorem categoryBarIdxDataMap_app (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    (αL : L ⟶ Φ ⋙ L') (n : ℕ) :
    (categoryBarIdxDataMap Φ αR αL).app n = ↾(barIdxMap Φ αR αL (n := n)) :=
  rfl

/-- Simplicial bar map induced by change of indexing category with coefficient maps. -/
noncomputable def categoryBarIdxMap (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    (αL : L ⟶ Φ ⋙ L') :
    categoryBar (C := C) (R := R) (L := L) ⟶
      categoryBar (C := D) (R := R') (L := L') :=
  SimplicialObject.Data.toSimplicialFunctor.map (categoryBarIdxDataMap Φ αR αL)

@[simp]
theorem categoryBarIdxMap_app_mk (Φ : C ⥤ D) (αR : R ⟶ Φ.op ⋙ R')
    (αL : L ⟶ Φ ⋙ L') (n : ℕ) :
    (categoryBarIdxMap Φ αR αL).app (op (SimplexCategory.mk n)) =
      ↾(barIdxMap Φ αR αL (n := n)) :=
  rfl

/-- Identity coefficient map on the left. -/
def idxIdL : L ⟶ (𝟭 C) ⋙ L where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- Identity coefficient map on the right. -/
def idxIdR : R ⟶ (𝟭 C).op ⋙ R where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

@[simp]
theorem barIdxMap_id {n : ℕ} (x : barObj C R L n) :
    barIdxMap (𝟭 C) idxIdR idxIdL x = x := by
  obtain ⟨F, l, r⟩ := x
  rw [barIdxMap_mk]
  exact Sigma.ext rfl HEq.rfl

@[simp]
theorem categoryBarIdxDataMap_id :
    categoryBarIdxDataMap (𝟭 C) (R := R) (L := L) idxIdR idxIdL = 𝟙 _ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  ext x
  simp only [categoryBarIdxDataMap_app, SimplicialObject.id_app]
  exact barIdxMap_id x

@[simp]
theorem categoryBarIdxMap_id :
    categoryBarIdxMap (𝟭 C) (R := R) (L := L) idxIdR idxIdL = 𝟙 _ := by
  simp only [categoryBarIdxMap, categoryBarIdxDataMap_id, Functor.map_id]
  rfl

variable {E : Type u} [Category.{v} E] {R'' : Eᵒᵖ ⥤ Type uR} {L'' : E ⥤ Type uL}

/-- Composite left coefficient map. -/
def compIdxL (Φ : C ⥤ D) (Ψ : D ⥤ E) (αL : L ⟶ Φ ⋙ L')
    (βL : L' ⟶ Ψ ⋙ L'') : L ⟶ (Φ ⋙ Ψ) ⋙ L'' where
  app X := αL.app X ≫ βL.app (Φ.obj X)
  naturality X Y f := by
    have hα := αL.naturality f
    have hβ := βL.naturality (Φ.map f)
    simp only [Functor.comp_map] at hα hβ ⊢
    rw [← Category.assoc, hα, Category.assoc, hβ, ← Category.assoc]

/-- Composite right coefficient map. -/
def compIdxR (Φ : C ⥤ D) (Ψ : D ⥤ E) (αR : R ⟶ Φ.op ⋙ R')
    (βR : R' ⟶ Ψ.op ⋙ R'') : R ⟶ (Φ ⋙ Ψ).op ⋙ R'' where
  app X := αR.app X ≫ βR.app (Φ.op.obj X)
  naturality X Y f := by
    have hα := αR.naturality f
    have hβ := βR.naturality (Φ.op.map f)
    simp only [Functor.comp_map] at hα hβ ⊢
    rw [← Category.assoc, hα, Category.assoc, hβ, ← Category.assoc]
    rfl

@[simp]
theorem compIdxL_app (Φ : C ⥤ D) (Ψ : D ⥤ E) (αL : L ⟶ Φ ⋙ L')
    (βL : L' ⟶ Ψ ⋙ L'') (X : C) :
    (compIdxL Φ Ψ αL βL).app X = αL.app X ≫ βL.app (Φ.obj X) :=
  rfl

@[simp]
theorem compIdxR_app (Φ : C ⥤ D) (Ψ : D ⥤ E) (αR : R ⟶ Φ.op ⋙ R')
    (βR : R' ⟶ Ψ.op ⋙ R'') (X : Cᵒᵖ) :
    (compIdxR Φ Ψ αR βR).app X = αR.app X ≫ βR.app (Φ.op.obj X) :=
  rfl

theorem barIdxMap_comp
    (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (βR : R' ⟶ Ψ.op ⋙ R'') (βL : L' ⟶ Ψ ⋙ L'')
    {n : ℕ} (x : barObj C R L n) :
    barIdxMap Ψ βR βL (barIdxMap Φ αR αL x) =
      barIdxMap (Φ ⋙ Ψ) (compIdxR Φ Ψ αR βR) (compIdxL Φ Ψ αL βL) x := by
  obtain ⟨F, l, r⟩ := x
  rfl

theorem categoryBarIdxDataMap_comp
    (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (βR : R' ⟶ Ψ.op ⋙ R'') (βL : L' ⟶ Ψ ⋙ L'') :
    categoryBarIdxDataMap Φ αR αL ≫ categoryBarIdxDataMap Ψ βR βL =
      categoryBarIdxDataMap (Φ ⋙ Ψ) (compIdxR Φ Ψ αR βR)
        (compIdxL Φ Ψ αL βL) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  ext x
  simp only [categoryBarIdxDataMap_app]
  exact barIdxMap_comp Φ Ψ αR αL βR βL x

theorem categoryBarIdxMap_comp
    (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (αR : R ⟶ Φ.op ⋙ R') (αL : L ⟶ Φ ⋙ L')
    (βR : R' ⟶ Ψ.op ⋙ R'') (βL : L' ⟶ Ψ ⋙ L'') :
    categoryBarIdxMap Φ αR αL ≫ categoryBarIdxMap Ψ βR βL =
      categoryBarIdxMap (Φ ⋙ Ψ) (compIdxR Φ Ψ αR βR)
        (compIdxL Φ Ψ αL βL) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  exact barIdxMap_comp Φ Ψ αR αL βR βL x

theorem barCoeff_idx_mixed
    (Φ : C ⥤ D)
    {R₁ R₂ : Cᵒᵖ ⥤ Type uR} {L₁ L₂ : C ⥤ Type uL}
    {S₁ S₂ : Dᵒᵖ ⥤ Type uR} {T₁ T₂ : D ⥤ Type uL}
    (γR : R₁ ⟶ R₂) (γL : L₁ ⟶ L₂) (δR : S₁ ⟶ S₂) (δL : T₁ ⟶ T₂)
    (αR : R₁ ⟶ Φ.op ⋙ S₁) (αL : L₁ ⟶ Φ ⋙ T₁)
    (αR' : R₂ ⟶ Φ.op ⋙ S₂) (αL' : L₂ ⟶ Φ ⋙ T₂)
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL))
    {n : ℕ} (x : barObj C R₁ L₁ n) :
    barCoeffMap δR δL (barIdxMap Φ αR αL x) =
      barIdxMap Φ αR' αL' (barCoeffMap γR γL x) := by
  obtain ⟨F, l, r⟩ := x
  have hLhom := NatTrans.congr_app hL F.left
  have hRhom := NatTrans.congr_app hR (op F.right)
  rw [NatTrans.comp_app, NatTrans.comp_app] at hLhom
  rw [NatTrans.comp_app, NatTrans.comp_app] at hRhom
  have hLpt := congrArg (fun m => m l) hLhom
  have hRpt := congrArg (fun m => m r) hRhom
  simp only [barCoeffMap_mk, barIdxMap_mk]
  exact Sigma.ext rfl (heq_of_eq (Prod.ext hLpt.symm hRpt.symm))

theorem categoryBarDataMap_idx_mixed
    (Φ : C ⥤ D)
    {R₁ R₂ : Cᵒᵖ ⥤ Type uR} {L₁ L₂ : C ⥤ Type uL}
    {S₁ S₂ : Dᵒᵖ ⥤ Type uR} {T₁ T₂ : D ⥤ Type uL}
    (γR : R₁ ⟶ R₂) (γL : L₁ ⟶ L₂) (δR : S₁ ⟶ S₂) (δL : T₁ ⟶ T₂)
    (αR : R₁ ⟶ Φ.op ⋙ S₁) (αL : L₁ ⟶ Φ ⋙ T₁)
    (αR' : R₂ ⟶ Φ.op ⋙ S₂) (αL' : L₂ ⟶ Φ ⋙ T₂)
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL)) :
    categoryBarIdxDataMap Φ αR αL ≫ categoryBarDataMap δR δL =
      categoryBarDataMap γR γL ≫ categoryBarIdxDataMap Φ αR' αL' := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp only [SimplicialObject.comp_app, categoryBarIdxDataMap_app,
    categoryBarDataMap_app]
  ext x
  exact barCoeff_idx_mixed Φ γR γL δR δL αR αL αR' αL' hR hL x

theorem categoryBarMap_idx_mixed
    (Φ : C ⥤ D)
    {R₁ R₂ : Cᵒᵖ ⥤ Type uR} {L₁ L₂ : C ⥤ Type uL}
    {S₁ S₂ : Dᵒᵖ ⥤ Type uR} {T₁ T₂ : D ⥤ Type uL}
    (γR : R₁ ⟶ R₂) (γL : L₁ ⟶ L₂) (δR : S₁ ⟶ S₂) (δL : T₁ ⟶ T₂)
    (αR : R₁ ⟶ Φ.op ⋙ S₁) (αL : L₁ ⟶ Φ ⋙ T₁)
    (αR' : R₂ ⟶ Φ.op ⋙ S₂) (αL' : L₂ ⟶ Φ ⋙ T₂)
    (hR : γR ≫ αR' = αR ≫ (Functor.whiskerLeft Φ.op δR))
    (hL : γL ≫ αL' = αL ≫ (Functor.whiskerLeft Φ δL)) :
    categoryBarIdxMap Φ αR αL ≫ categoryBarMap δR δL =
      categoryBarMap γR γL ≫ categoryBarIdxMap Φ αR' αL' := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  exact barCoeff_idx_mixed Φ γR γL δR δL αR αL αR' αL' hR hL x

end CategoryBar

end CategoryTheory

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarSimplicial
public import MathlibExt.CategoryTheory.Enriched.WeightedBarSimplicial
public import MathlibExt.CategoryTheory.CategoryBar.SimplicialReplacement

/-!
# Terminal-weight weighted bars and coefficient bars

The terminal-weight ordinary weighted bar has one redundant `PUnit`
coordinate in every indexing type. Removing it identifies each weighted-bar
degree with the coefficient-bar degree. The comparison commutes with all
outer faces and therefore induces an isomorphism of alternating-face chain
complexes.

This is a strict algebraic comparison. It introduces no new bar,
realization, homotopy-colimit, or spectral-sequence construction.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u vA uA

namespace CategoryTheory.CategoryHomology

variable {C : Type u} [Category.{v} C]
  {A : Type uA} [Category.{vA} A]
  [HasCoproducts.{max u v} A]
  (M : C ⥤ A)

/-- Remove the terminal weight from a weighted chain. -/
def terminalWeightIndexEquiv (n : ℕ) :
    StrictOrdinaryWeightedBar.WIdx C (CategoryBar.replUnit C) n ≃
      ComposableArrows C n where
  toFun x := x.1
  invFun x := ⟨x, PUnit.unit⟩
  left_inv x := by
    rcases x with ⟨chain, weight⟩
    rcases weight
    rfl
  right_inv _ := rfl

/-- Removing the terminal weight identifies a weighted-bar degree with the
coefficient-bar degree. -/
noncomputable def terminalWeightCoefficientBarDegreeIso (n : ℕ) :
    StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit C) M n ≅
      coefficientBarObj M n :=
  Sigma.whiskerEquiv
    (f := fun x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n => M.obj x.1.left)
    (g := coefficientBarFamily M n)
    (terminalWeightIndexEquiv n) (fun x => eqToIso
      (show coefficientBarFamily M n ((terminalWeightIndexEquiv n) x) =
        M.obj x.1.left by rfl))

@[reassoc]
theorem wbarIncl_terminalWeightCoefficientBarDegreeIso_hom
    (n : ℕ)
    (x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n) :
    StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit C) M n x ≫
      (terminalWeightCoefficientBarDegreeIso M n).hom =
        coefficientBarι M x.1 := by
  rw [terminalWeightCoefficientBarDegreeIso, Sigma.whiskerEquiv_hom,
    ]
  change Sigma.ι (fun x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) n => M.obj x.1.left) x ≫
      Sigma.map' (terminalWeightIndexEquiv n) (fun x =>
        (eqToIso (show coefficientBarFamily M n
          ((terminalWeightIndexEquiv n) x) = M.obj x.1.left by rfl)).inv) =
    Sigma.ι (coefficientBarFamily M n) x.1
  rw [Sigma.ι_comp_map']
  change 𝟙 (M.obj x.1.left) ≫
      Sigma.ι (coefficientBarFamily M n) x.1 =
    Sigma.ι (coefficientBarFamily M n) x.1
  simp

omit [HasCoproducts.{max u v} A] in
theorem srepFaceZeroComponent_eq_coefficientFaceHom
    {n : ℕ} (s : ComposableArrows C (n + 1)) :
    SrepBridge.srepFaceZeroComponent M s =
      coefficientFaceHom M (0 : Fin (n + 2)) s := by
  simp [SrepBridge.srepFaceZeroComponent,
    coefficientFaceHom, faceLeftHom]

set_option linter.flexible false in
-- The endpoint normalization is deliberately exposed before applying `map_id`.
omit [HasCoproducts.{max u v} A] in
theorem srepFaceLastComponent_eq_coefficientFaceHom
    {n : ℕ} (s : ComposableArrows C (n + 1)) :
    SrepBridge.srepFaceLastComponent M s =
      coefficientFaceHom M (Fin.last (n + 1)) s := by
  simp [SrepBridge.srepFaceLastComponent,
    coefficientFaceHom, faceLeftHom]
  change 𝟙 (M.obj (s.obj 0)) = M.map (𝟙 (s.obj 0))
  exact (M.map_id _).symm

omit [HasCoproducts.{max u v} A] in
theorem faceLeftHom_eq_eqToHom_of_ne_zero
    {n : ℕ} (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (s : ComposableArrows C (n + 1)) :
    faceLeftHom i s = eqToHom (face_left_eq_of_ne_zero
      (by exact fun h => hi0 (Fin.ext h)) s) := by
  unfold faceLeftHom
  have hidx : i.succAbove (0 : Fin (n + 1)) = 0 :=
    Fin.succAbove_ne_zero_zero hi0
  have hhom : (homOfLE (Fin.zero_le (i.succAbove 0)) :
      (0 : Fin (n + 2)) ⟶ i.succAbove 0) = eqToHom hidx.symm :=
    Subsingleton.elim _ _
  rw [hhom, CategoryTheory.eqToHom_map]

omit [HasCoproducts.{max u v} A] in
theorem wFaceInnerComponent_eq_coefficientFaceHom
    {n : ℕ} (i : Fin (n + 2)) (hi0 : i ≠ 0)
    [NeZero (n + 1)] (s : ComposableArrows C (n + 1)) :
    StrictOrdinaryWeightedBar.wFaceInnerComponent M i hi0 s =
      coefficientFaceHom M i s := by
  unfold StrictOrdinaryWeightedBar.wFaceInnerComponent coefficientFaceHom
  rw [faceLeftHom_eq_eqToHom_of_ne_zero i hi0 s,
    CategoryTheory.eqToHom_map]

theorem terminalWeightIndexEquiv_faceZero
    {n : ℕ}
    (x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    terminalWeightIndexEquiv n
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit C) n x) =
      (nerve C).δ 0 x.1 :=
  rfl

theorem terminalWeightIndexEquiv_faceLast
    {n : ℕ}
    (x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    terminalWeightIndexEquiv n
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit C) n x) =
      (nerve C).δ (Fin.last (n + 1)) x.1 :=
  by
    change x.1.δlast = (nerve C).δ (Fin.last (n + 1)) x.1
    have hfun : Fin.castSuccFunctor (n + 1) =
        (SimplexCategory.toCat.map
          (SimplexCategory.δ (Fin.last (n + 1)))).toFunctor :=
      Functor.ext
        (fun j => by
          change j.castSucc = (Fin.last (n + 1)).succAbove j
          exact (Fin.succAbove_last_apply j).symm)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact congrArg (fun K => x.1.whiskerLeft K) hfun

theorem terminalWeightIndexEquiv_faceInner
    {n : ℕ} (i : Fin (n + 2))
    (hiLast : i ≠ Fin.last (n + 1))
    (x : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) (n + 1)) :
    terminalWeightIndexEquiv n
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit C) n i hiLast x) =
      (nerve C).δ i x.1 :=
  rfl

theorem terminalWeightCoefficientBarDegreeIso_map
    {m n : ℕ}
    (e : StrictOrdinaryWeightedBar.WIdx C
      (CategoryBar.replUnit C) m →
        StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n)
    (d : ComposableArrows C m → ComposableArrows C n)
    (hd : ∀ x, (e x).1 = d x.1)
    (φW : ∀ x,
      (fun y : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) m => M.obj y.1.left) x ⟶
      (fun y : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n => M.obj y.1.left) (e x))
    (φC : ∀ s,
      coefficientBarFamily M m s ⟶ coefficientBarFamily M n (d s))
    (hφ : ∀ x, φC x.1 ≫ eqToHom
      (congrArg (coefficientBarFamily M n) (hd x).symm) = φW x) :
    (terminalWeightCoefficientBarDegreeIso M m).hom ≫
        Sigma.map' (f := coefficientBarFamily M n)
          (g := coefficientBarFamily M m) d φC =
      Sigma.map'
          (f := fun x : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n => M.obj x.1.left)
          (g := fun x : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) m => M.obj x.1.left)
          e φW ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom := by
  apply Sigma.hom_ext
  intro x
  let y := e x
  let z := d x.1
  have hidx : y.1 = z := hd x
  have htrans := Sigma.eqToHom_comp_ι
    (coefficientBarFamily M n) hidx
  have hWeighted :
      StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M m x ≫
        Sigma.map'
          (f := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n => M.obj y.1.left)
          (g := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) m => M.obj y.1.left)
          e φW =
        φW x ≫ StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n y := by
    change Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) m => M.obj y.1.left) x ≫
      Sigma.map'
        (f := fun y : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) n => M.obj y.1.left)
        (g := fun y : StrictOrdinaryWeightedBar.WIdx C
          (CategoryBar.replUnit C) m => M.obj y.1.left)
        e φW =
      φW x ≫ Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx C
        (CategoryBar.replUnit C) n => M.obj y.1.left) y
    exact Sigma.ι_comp_map' _ _ _
  calc
    StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M m x ≫
        ((terminalWeightCoefficientBarDegreeIso M m).hom ≫
          Sigma.map' (f := coefficientBarFamily M n)
            (g := coefficientBarFamily M m) d φC) =
      (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M m x ≫
        (terminalWeightCoefficientBarDegreeIso M m).hom) ≫
          Sigma.map' (f := coefficientBarFamily M n)
            (g := coefficientBarFamily M m) d φC :=
      (Category.assoc _ _ _).symm
    _ = coefficientBarι M x.1 ≫
          Sigma.map' (f := coefficientBarFamily M n)
            (g := coefficientBarFamily M m) d φC := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
    _ = φC x.1 ≫ coefficientBarι M z := by
      exact Sigma.ι_comp_map' _ _ _
    _ =
        φC x.1 ≫ (eqToHom _ ≫ coefficientBarι M y.1) := by
      exact congrArg (φC x.1 ≫ ·) htrans.symm
    _ = (φC x.1 ≫ eqToHom _) ≫ coefficientBarι M y.1 :=
      (Category.assoc _ _ _).symm
    _ = φW x ≫ coefficientBarι M y.1 := by rw [hφ]
    _ = φW x ≫
        (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n y ≫
            (terminalWeightCoefficientBarDegreeIso M n).hom) := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
    _ = (φW x ≫ StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n y) ≫
            (terminalWeightCoefficientBarDegreeIso M n).hom :=
      (Category.assoc _ _ _).symm
    _ = (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M m x ≫
        Sigma.map'
          (f := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n => M.obj y.1.left)
          (g := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) m => M.obj y.1.left)
          e φW) ≫ (terminalWeightCoefficientBarDegreeIso M n).hom := by
      exact congrArg
        (fun k => k ≫ (terminalWeightCoefficientBarDegreeIso M n).hom)
        hWeighted.symm
    _ = StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M m x ≫
        (Sigma.map'
          (f := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) n => M.obj y.1.left)
          (g := fun y : StrictOrdinaryWeightedBar.WIdx C
            (CategoryBar.replUnit C) m => M.obj y.1.left)
          e φW ≫ (terminalWeightCoefficientBarDegreeIso M n).hom) :=
      Category.assoc _ _ _

theorem terminalWeightCoefficientBarDegreeIso_faceZero
    (n : ℕ) :
    (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
        coefficientBarFace M (0 : Fin (n + 2)) =
      StrictOrdinaryWeightedBar.wbarFaceZero
          (CategoryBar.replUnit C) M n ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom := by
  apply Sigma.hom_ext
  intro x
  calc
    StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        ((terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
          coefficientBarFace M 0) =
      (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom) ≫
          coefficientBarFace M 0 :=
      (Category.assoc _ _ _).symm
    _ = coefficientBarι M x.1 ≫ coefficientBarFace M 0 := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
    _ = coefficientFaceHom M 0 x.1 ≫
        coefficientBarι M ((nerve C).δ 0 x.1) :=
      coefficientBarι_face M 0 x.1
    _ = SrepBridge.srepFaceZeroComponent M x.1 ≫
        coefficientBarι M ((nerve C).δ 0 x.1) := by
      rw [srepFaceZeroComponent_eq_coefficientFaceHom]
    _ = SrepBridge.srepFaceZeroComponent M x.1 ≫
        (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceZeroIdx
              (CategoryBar.replUnit C) n x) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom) := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
      rfl
    _ = (SrepBridge.srepFaceZeroComponent M x.1 ≫
        StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceZeroIdx
              (CategoryBar.replUnit C) n x)) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom :=
      (Category.assoc _ _ _).symm
    _ = (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        StrictOrdinaryWeightedBar.wbarFaceZero
          (CategoryBar.replUnit C) M n) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom := by
      rw [StrictOrdinaryWeightedBar.wbarFaceZero_ι]
    _ = StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (StrictOrdinaryWeightedBar.wbarFaceZero
          (CategoryBar.replUnit C) M n ≫
            (terminalWeightCoefficientBarDegreeIso M n).hom) :=
      Category.assoc _ _ _

theorem terminalWeightCoefficientBarDegreeIso_faceLast
    (n : ℕ) :
    (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
        coefficientBarFace M (Fin.last (n + 1)) =
      StrictOrdinaryWeightedBar.wbarFaceLast
          (CategoryBar.replUnit C) M n ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom := by
  apply Sigma.hom_ext
  intro x
  calc
    StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        ((terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
          coefficientBarFace M (Fin.last (n + 1))) =
      (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom) ≫
          coefficientBarFace M (Fin.last (n + 1)) :=
      (Category.assoc _ _ _).symm
    _ = coefficientBarι M x.1 ≫
        coefficientBarFace M (Fin.last (n + 1)) := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
    _ = coefficientFaceHom M (Fin.last (n + 1)) x.1 ≫
        coefficientBarι M
          ((nerve C).δ (Fin.last (n + 1)) x.1) :=
      coefficientBarι_face M (Fin.last (n + 1)) x.1
    _ = SrepBridge.srepFaceLastComponent M x.1 ≫
        coefficientBarι M
          ((nerve C).δ (Fin.last (n + 1)) x.1) := by
      rw [srepFaceLastComponent_eq_coefficientFaceHom]
    _ = SrepBridge.srepFaceLastComponent M x.1 ≫
        (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceLastIdx
              (CategoryBar.replUnit C) n x) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom) := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
      let y := StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit C) n x
      let z := (nerve C).δ (Fin.last (n + 1)) x.1
      have hidx : y.1 = z := terminalWeightIndexEquiv_faceLast x
      have htrans := Sigma.eqToHom_comp_ι
        (coefficientBarFamily M n) hidx
      calc
        SrepBridge.srepFaceLastComponent M x.1 ≫
              coefficientBarι M z =
            SrepBridge.srepFaceLastComponent M x.1 ≫
              (eqToHom _ ≫ coefficientBarι M y.1) := by
          exact congrArg
            (SrepBridge.srepFaceLastComponent M x.1 ≫ ·) htrans.symm
        _ = (SrepBridge.srepFaceLastComponent M x.1 ≫ eqToHom _) ≫
              coefficientBarι M y.1 :=
          (Category.assoc _ _ _).symm
        _ = SrepBridge.srepFaceLastComponent M x.1 ≫
              coefficientBarι M y.1 := by
          exact eq_of_heq (CategoryTheory.heq_comp rfl rfl rfl
            (CategoryTheory.comp_eqToHom_heq
              (SrepBridge.srepFaceLastComponent M x.1) _) HEq.rfl)
    _ = (SrepBridge.srepFaceLastComponent M x.1 ≫
        StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceLastIdx
              (CategoryBar.replUnit C) n x)) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom :=
      (Category.assoc _ _ _).symm
    _ = (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        StrictOrdinaryWeightedBar.wbarFaceLast
          (CategoryBar.replUnit C) M n) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom := by
      rw [StrictOrdinaryWeightedBar.wbarFaceLast_ι]
    _ = StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (StrictOrdinaryWeightedBar.wbarFaceLast
          (CategoryBar.replUnit C) M n ≫
            (terminalWeightCoefficientBarDegreeIso M n).hom) :=
      Category.assoc _ _ _

theorem terminalWeightCoefficientBarDegreeIso_faceInner
    (n : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)] :
    (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
        coefficientBarFace M i =
      StrictOrdinaryWeightedBar.wbarFaceInner
          (CategoryBar.replUnit C) M n i hi0 hiLast ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom := by
  apply Sigma.hom_ext
  intro x
  calc
    StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        ((terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
          coefficientBarFace M i) =
      (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom) ≫
          coefficientBarFace M i :=
      (Category.assoc _ _ _).symm
    _ = coefficientBarι M x.1 ≫ coefficientBarFace M i := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
    _ = coefficientFaceHom M i x.1 ≫
        coefficientBarι M ((nerve C).δ i x.1) :=
      coefficientBarι_face M i x.1
    _ = StrictOrdinaryWeightedBar.wFaceInnerComponent M i hi0 x.1 ≫
        coefficientBarι M ((nerve C).δ i x.1) := by
      rw [wFaceInnerComponent_eq_coefficientFaceHom]
    _ = StrictOrdinaryWeightedBar.wFaceInnerComponent M i hi0 x.1 ≫
        (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceInnerIdx
              (CategoryBar.replUnit C) n i hiLast x) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom) := by
      rw [wbarIncl_terminalWeightCoefficientBarDegreeIso_hom]
      rfl
    _ = (StrictOrdinaryWeightedBar.wFaceInnerComponent M i hi0 x.1 ≫
        StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M n
            (StrictOrdinaryWeightedBar.wFaceInnerIdx
              (CategoryBar.replUnit C) n i hiLast x)) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom :=
      (Category.assoc _ _ _).symm
    _ = (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        StrictOrdinaryWeightedBar.wbarFaceInner
          (CategoryBar.replUnit C) M n i hi0 hiLast) ≫
          (terminalWeightCoefficientBarDegreeIso M n).hom := by
      rw [StrictOrdinaryWeightedBar.wbarFaceInner_ι]
    _ = StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit C) M (n + 1) x ≫
        (StrictOrdinaryWeightedBar.wbarFaceInner
          (CategoryBar.replUnit C) M n i hi0 hiLast ≫
            (terminalWeightCoefficientBarDegreeIso M n).hom) :=
      Category.assoc _ _ _

theorem terminalWeightCoefficientBarDegreeIso_face
    (n : ℕ) (i : Fin (n + 2)) :
    (terminalWeightCoefficientBarDegreeIso M (n + 1)).hom ≫
        coefficientBarFace M i =
      StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit C) M n i ≫
        (terminalWeightCoefficientBarDegreeIso M n).hom := by
  by_cases h0 : i = 0
  · subst i
    rw [StrictOrdinaryWeightedBar.wbarδ_zero]
    exact terminalWeightCoefficientBarDegreeIso_faceZero M n
  by_cases hlast : i = Fin.last (n + 1)
  · subst i
    rw [StrictOrdinaryWeightedBar.wbarδ_last]
    exact terminalWeightCoefficientBarDegreeIso_faceLast M n
  · let _ : NeZero (n + 1) := ⟨by omega⟩
    rw [StrictOrdinaryWeightedBar.wbarδ_inner
      (CategoryBar.replUnit C) M n i h0 hlast]
    exact terminalWeightCoefficientBarDegreeIso_faceInner
      M n i h0 hlast

section

variable [Preadditive A]

/-- Alternating-face complex of the terminal-weight weighted bar. -/
noncomputable def terminalWeightBarComplex : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj
    (StrictOrdinaryWeightedBar.wbarSimplicial
      (CategoryBar.replUnit C) M)

theorem coefficientBarComplex_d_eq_sum (n : ℕ) :
    (coefficientBarComplex M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        coefficientBarFace M i := by
  unfold coefficientBarComplex
  change ((AlgebraicTopology.alternatingFaceMapComplex A).obj
    (coefficientBarSimplicial M)).d (n + 1) n = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact coefficientBarSimplicial_map_δ M i

theorem terminalWeightBarComplex_d_eq_sum (n : ℕ) :
    (terminalWeightBarComplex M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit C) M n i := by
  unfold terminalWeightBarComplex
  change ((AlgebraicTopology.alternatingFaceMapComplex A).obj
    (StrictOrdinaryWeightedBar.wbarSimplicial
      (CategoryBar.replUnit C) M)).d (n + 1) n = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact StrictOrdinaryWeightedBar.wbarSimplicial_map_δ
    (CategoryBar.replUnit C) M i

/-- Removing the terminal weight identifies the weighted-bar alternating
complex with the coefficient-bar alternating complex. -/
noncomputable def terminalWeightCoefficientBarComplexIso :
    terminalWeightBarComplex M ≅ coefficientBarComplex M :=
  HomologicalComplex.Hom.isoOfComponents
    (terminalWeightCoefficientBarDegreeIso M) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      change (terminalWeightCoefficientBarDegreeIso M (j + 1)).hom ≫
          (coefficientBarComplex M).d (j + 1) j =
        (terminalWeightBarComplex M).d (j + 1) j ≫
          (terminalWeightCoefficientBarDegreeIso M j).hom
      rw [coefficientBarComplex_d_eq_sum,
        terminalWeightBarComplex_d_eq_sum]
      simp only [Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
        (terminalWeightCoefficientBarDegreeIso_face M j k))

end

end CategoryTheory.CategoryHomology

end

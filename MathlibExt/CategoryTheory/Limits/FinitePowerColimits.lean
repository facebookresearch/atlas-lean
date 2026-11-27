/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Actual finite-function cocones over a filtered diagram

The pointwise finite product is the ORIGINAL type of functions `Fin n → X`.
Its colimit is derived from the existing filtered-colimit preservation of
finite limits. Injection and projection laws identify the resulting cofan
with the original componentwise maps, including the empty finite product.
No preservation statement for arbitrary infinite products is asserted.
-/

noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.Types

variable {J : Type v} [SmallCategory J]

/-- The actual finite-function diagram, with the original maps on EVERY
coordinate and the original target types. -/
public abbrev functionPowerDiagram (D : J ⥤ Type u) (n : ℕ) : J ⥤ Type u where
  obj j := Fin n → D.obj j
  map {j k} f := TypeCat.ofHom
    (fun (x : Fin n → D.obj j) (i : Fin n) => D.map f (x i) :
      (Fin n → D.obj j) → (Fin n → D.obj k))
  map_id j := by
    apply ConcreteCategory.hom_ext (C := Type u)
    intro x
    funext i
    simpa only [TypeCat.ofHom_apply, types_id_apply] using
      ConcreteCategory.congr_hom (D.map_id j) (x i)
  map_comp f g := by
    apply ConcreteCategory.hom_ext (C := Type u)
    intro x
    funext i
    simpa only [TypeCat.ofHom_apply, types_comp_apply] using
      ConcreteCategory.congr_hom (D.map_comp f g) (x i)

private def functionPowerCone (D : J ⥤ Type u) (n : ℕ) :
    Cone ((Functor.const (Discrete (Fin n))).obj D) where
  pt := functionPowerDiagram D n
  π := Discrete.natTrans (fun ⟨i⟩ =>
    (show functionPowerDiagram D n ⟶ D from
      { app := fun j => TypeCat.ofHom (fun (x : Fin n → D.obj j) => x i)
        naturality := by
          intro j k f
          apply ConcreteCategory.hom_ext (C := Type u)
          intro x
          simp only [types_comp_apply, TypeCat.ofHom_apply] }))

private def functionPowerConeIsLimit (D : J ⥤ Type u) (n : ℕ) :
    IsLimit (functionPowerCone D n) := by
  refine evaluationJointlyReflectsLimits _ (fun j => ?_)
  refine
    { lift := fun s => TypeCat.ofHom
        (fun (x : s.pt) (i : Fin n) => s.π.app ⟨i⟩ x)
      fac := ?_
      uniq := ?_ }
  · intro s i
    rcases i with ⟨i⟩
    rfl
  · intro s m w
    apply ConcreteCategory.hom_ext (C := Type u) (FC := TypeCat.Fun)
      (CC := fun T : Type u => T)
    intro x
    funext i
    let π : (Fin n → D.obj j) ⟶ D.obj j :=
      TypeCat.ofHom (fun (z : Fin n → D.obj j) => z i)
    have wi : m ≫ π = s.π.app ⟨i⟩ := w ⟨i⟩
    change m x i = s.π.app ⟨i⟩ x
    calc
      m x i = π (m x) :=
        (TypeCat.ofHom_apply (fun (z : Fin n → D.obj j) => z i) (m x)).symm
      _ = (m ≫ π) x := (types_comp_apply m π x).symm
      _ = s.π.app ⟨i⟩ x := types_congr_hom wi x

/-- The actual componentwise finite-function cofan of an original cofan. -/
public abbrev functionPowerCocone {D : J ⥤ Type u} (c : Cocone D) (n : ℕ) :
    Cocone (functionPowerDiagram D n) where
  pt := Fin n → c.pt
  ι := (show functionPowerDiagram D n ⟶ (Functor.const J).obj (Fin n → c.pt) from
    { app := fun j => TypeCat.ofHom
        (fun (x : Fin n → D.obj j) (i : Fin n) => c.ι.app j (x i) :
          (Fin n → D.obj j) → (Fin n → c.pt))
      naturality := by
        intro j k f
        rw [Functor.const_obj_map]
        apply ConcreteCategory.hom_ext (C := Type u) (FC := TypeCat.Fun)
          (CC := fun T : Type u => T)
        intro x
        funext i
        let legJ : (Fin n → D.obj j) ⟶ (Fin n → c.pt) :=
          TypeCat.ofHom (fun (z : Fin n → D.obj j) (a : Fin n) => c.ι.app j (z a))
        let legK : (Fin n → D.obj k) ⟶ (Fin n → c.pt) :=
          TypeCat.ofHom (fun (z : Fin n → D.obj k) (a : Fin n) => c.ι.app k (z a))
        let mapF : (Fin n → D.obj j) ⟶ (Fin n → D.obj k) :=
          (functionPowerDiagram D n).map f
        have hmap : mapF x i = D.map f (x i) :=
          congrFun (TypeCat.ofHom_apply
            (fun (z : Fin n → D.obj j) (a : Fin n) => D.map f (z a)) x) i
        have hlegK : legK (mapF x) i = c.ι.app k (mapF x i) :=
          congrFun (TypeCat.ofHom_apply
            (fun (z : Fin n → D.obj k) (a : Fin n) => c.ι.app k (z a)) (mapF x)) i
        have hlegJ : legJ x i = c.ι.app j (x i) :=
          congrFun (TypeCat.ofHom_apply
            (fun (z : Fin n → D.obj j) (a : Fin n) => c.ι.app j (z a)) x) i
        change (mapF ≫ legK) x i = (legJ ≫ 𝟙 (Fin n → c.pt)) x i
        calc
          (mapF ≫ legK) x i = legK (mapF x) i :=
            congrFun (types_comp_apply mapF legK x) i
          _ = c.ι.app k (D.map f (x i)) :=
            hlegK.trans (congrArg (c.ι.app k) hmap)
          _ = (D.map f ≫ c.ι.app k) (x i) :=
            (types_comp_apply (D.map f) (c.ι.app k) (x i)).symm
          _ = c.ι.app j (x i) := types_congr_hom (c.w f) (x i)
          _ = legJ x i := hlegJ.symm
          _ = (𝟙 (Fin n → c.pt)) (legJ x) i :=
            (congrFun (types_id_apply (Fin n → c.pt) (legJ x)) i).symm
          _ = (legJ ≫ 𝟙 (Fin n → c.pt)) x i :=
            (congrFun (types_comp_apply legJ (𝟙 (Fin n → c.pt)) x) i).symm })

private theorem functionPowerCocone_ι_computed
    {D : J ⥤ Type u} (c : Cocone D) (n : ℕ) (j : J)
    (x : Fin n → D.obj j) (i : Fin n) :
    (functionPowerCocone c n).ι.app j x i = c.ι.app j (x i) := rfl

/-- Every original injection is applied to the original tuple coordinate. -/
public theorem functionPowerCocone_ι
    {D : J ⥤ Type u} (c : Cocone D) (n : ℕ) (j : J)
    (x : Fin n → D.obj j) (i : Fin n) :
    (functionPowerCocone c n).ι.app j x i = c.ι.app j (x i) :=
  functionPowerCocone_ι_computed c n j x i

variable [IsFiltered J] [Small.{u} J]

/-- Filtered colimits give the actual colimit of the ORIGINAL finite
function cofan. The proof uses the existing finite-limit comparison;
the resulting whole injection is the given componentwise map. -/
public def functionPowerCoconeIsColimit
    {D : J ⥤ Type u} (c : Cocone D) (hc : IsColimit c) (n : ℕ) :
    IsColimit (functionPowerCocone c n) := by
  let P : Cone ((Functor.const (Discrete (Fin n))).obj D) := functionPowerCone D n
  let D' : Discrete (Fin n) ⥤ (J ⥤ Type u) :=
    (Functor.const (Discrete (Fin n))).obj D
  let cm : Cone (D' ⋙ (colim : (J ⥤ Type u) ⥤ Type u)) :=
    (colim : (J ⥤ Type u) ⥤ Type u).mapCone P
  let hm : IsLimit cm := isLimitOfPreserves
    (colim : (J ⥤ Type u) ⥤ Type u) (functionPowerConeIsLimit D n)
  let Q : Cone (D' ⋙ (colim : (J ⥤ Type u) ⥤ Type u)) :=
    { pt := Fin n → colimit D
      π := Discrete.natTrans (fun ⟨i⟩ =>
        TypeCat.ofHom (fun (x : Fin n → colimit D) => x i)) }
  let hQ : IsLimit Q := by
    refine
      { lift := fun s => TypeCat.ofHom
          (fun (x : s.pt) (i : Fin n) => s.π.app ⟨i⟩ x)
        fac := ?_
        uniq := ?_ }
    · intro s i
      rcases i with ⟨i⟩
      rfl
    · intro s m w
      apply ConcreteCategory.hom_ext (C := Type u) (FC := TypeCat.Fun)
        (CC := fun T : Type u => T)
      intro x
      funext i
      let π : (Fin n → colimit D) ⟶ colimit D :=
        TypeCat.ofHom (fun (z : Fin n → colimit D) => z i)
      have wi : m ≫ π = s.π.app ⟨i⟩ := w ⟨i⟩
      change m x i = s.π.app ⟨i⟩ x
      calc
        m x i = π (m x) :=
          (TypeCat.ofHom_apply (fun (z : Fin n → colimit D) => z i) (m x)).symm
        _ = (m ≫ π) x := (types_comp_apply m π x).symm
        _ = s.π.app ⟨i⟩ x := types_congr_hom wi x
  let eP : colimit (functionPowerDiagram D n) ≅ (Fin n → colimit D) :=
    hm.conePointUniqueUpToIso hQ
  let e : colimit D ≅ c.pt := (colimit.isColimit D).coconePointUniqueUpToIso hc
  let eTuple : (Fin n → colimit D) ≅ (Fin n → c.pt) :=
    (Equiv.piCongrRight (fun _ : Fin n => e.toEquiv)).toIso
  let eTotal : colimit (functionPowerDiagram D n) ≅ (functionPowerCocone c n).pt :=
    eP ≪≫ eTuple
  let projection (i : Fin n) : functionPowerDiagram D n ⟶ D := P.π.app ⟨i⟩
  let colimitProjection (i : Fin n) :
      colimit (functionPowerDiagram D n) ⟶ colimit D := colim.map (projection i)
  have hπ (i : Fin n) : eP.hom ≫ TypeCat.ofHom (fun (x : Fin n → colimit D) => x i) =
      colimitProjection i :=
    hm.conePointUniqueUpToIso_hom_comp hQ ⟨i⟩
  have hfac (j : J) : colimit.ι (functionPowerDiagram D n) j ≫ eTotal.hom =
      (functionPowerCocone c n).ι.app j := by
    apply ConcreteCategory.hom_ext (C := Type u) (FC := TypeCat.Fun)
      (CC := fun T : Type u => T)
    intro x
    funext i
    let y : colimit (functionPowerDiagram D n) :=
      colimit.ι (functionPowerDiagram D n) j x
    have hπ' : eP.hom y i = colimitProjection i y := by
      let π : (Fin n → colimit D) ⟶ colimit D :=
        TypeCat.ofHom (fun (z : Fin n → colimit D) => z i)
      calc
        eP.hom y i = π (eP.hom y) :=
          (TypeCat.ofHom_apply (fun (z : Fin n → colimit D) => z i) (eP.hom y)).symm
        _ = (eP.hom ≫ π) y := (types_comp_apply eP.hom π y).symm
        _ = colimitProjection i y := types_congr_hom (hπ i) y
    have hι : colimit.ι (functionPowerDiagram D n) j ≫ colimitProjection i =
        (projection i).app j ≫ colimit.ι D j :=
      colimit.ι_map (projection i) j
    have hproj : (projection i).app j x = x i := rfl
    have hι' : colimitProjection i y = colimit.ι D j (x i) := by
      calc
        colimitProjection i y =
            (colimit.ι (functionPowerDiagram D n) j ≫ colimitProjection i) x :=
          (types_comp_apply (colimit.ι (functionPowerDiagram D n) j)
            (colimitProjection i) x).symm
        _ = ((projection i).app j ≫ colimit.ι D j) x := types_congr_hom hι x
        _ = colimit.ι D j ((projection i).app j x) :=
          types_comp_apply ((projection i).app j) (colimit.ι D j) x
        _ = colimit.ι D j (x i) := congrArg (colimit.ι D j) hproj
    have heq : colimit.ι D j ≫ e.hom = c.ι.app j :=
      (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hc j
    have he : e.hom (colimit.ι D j (x i)) = c.ι.app j (x i) := by
      calc
        e.hom (colimit.ι D j (x i)) = (colimit.ι D j ≫ e.hom) (x i) :=
          (types_comp_apply (colimit.ι D j) e.hom (x i)).symm
        _ = c.ι.app j (x i) := types_congr_hom heq (x i)
    change e.hom (eP.hom (colimit.ι (functionPowerDiagram D n) j x) i) = c.ι.app j (x i)
    exact (congrArg e.hom hπ').trans
      ((congrArg e.hom hι').trans he)
  exact (colimit.isColimit (functionPowerDiagram D n)).ofIsoColimit
    (Cocone.ext eTotal hfac)

end CategoryTheory.Types

end

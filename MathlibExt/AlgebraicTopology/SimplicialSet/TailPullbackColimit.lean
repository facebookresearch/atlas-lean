/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original tail pullback-colimit geometry, including non-mono Y diagrams.
module
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.ColimitLimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SSet.RezkTailPullbackColimit

/-- The SAME original tail indices, with native order morphisms. -/
@[reducible]
def natTail (n : ℕ) : ℕ ⥤ ℕ where
  obj k := n + k
  map f := homOfLE (Nat.add_le_add_left (leOfHom f) n)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def natDrop (n : ℕ) : ℕ ⥤ ℕ where
  obj k := k - n
  map f := homOfLE (Nat.sub_le_sub_right (leOfHom f) n)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Tail finality is derived by the actual subtraction/addition adjunction. -/
theorem natTail_final (n : ℕ) : (natTail n).Final := by
  let adj : natDrop n ⊣ natTail n := Adjunction.mkOfHomEquiv
    { homEquiv := fun i k =>
        { toFun := fun f => homOfLE (Nat.sub_le_iff_le_add'.mp (leOfHom f))
          invFun := fun f => homOfLE (Nat.sub_le_iff_le_add'.mpr (leOfHom f))
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
      homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }
  exact CategoryTheory.Functor.final_of_adjunction adj

/-- The three objects/maps in each original tail cospan; no pullback outcome is provided. -/
@[reducible]
def tailCospanDiagram {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ) :
    ℕ ⥤ (WalkingCospan ⥤ SSet.{u}) where
  obj k := cospan (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k)))
  map {i j} f := cospanHomMk
    (F := cospan (p.app (n + i)) (Y.map (homOfLE (Nat.le_add_right n i))))
    (G := cospan (p.app (n + j)) (Y.map (homOfLE (Nat.le_add_right n j))))
    (Y.map ((natTail n).map f)) (X.map ((natTail n).map f)) (𝟙 (Y.obj n))
    (by
      change p.app (n + i) ≫ Y.map ((natTail n).map f) =
        X.map ((natTail n).map f) ≫ p.app (n + j)
      exact (p.naturality ((natTail n).map f)).symm)
    (by
      change Y.map (homOfLE (Nat.le_add_right n i)) ≫ Y.map ((natTail n).map f) =
        (𝟙 (Y.obj n)) ≫ Y.map (homOfLE (Nat.le_add_right n j))
      rw [Category.id_comp, ← Y.map_comp]
      exact congrArg Y.map (Subsingleton.elim _ _))
  map_id k := by
    apply NatTrans.ext
    funext j
    cases j with
    | none => change Y.map ((natTail n).map (𝟙 k)) = 𝟙 _; simp
    | some a => cases a with
      | left => change X.map ((natTail n).map (𝟙 k)) = 𝟙 _; simp
      | right => change (𝟙 (Y.obj n)) = (𝟙 (Y.obj n)); rfl
  map_comp f g := by
    apply NatTrans.ext
    funext j
    cases j with
    | none =>
        change Y.map ((natTail n).map (f ≫ g)) = Y.map ((natTail n).map f) ≫
            Y.map ((natTail n).map g)
        rw [Functor.map_comp, Functor.map_comp]
    | some a => cases a with
      | left =>
          change X.map ((natTail n).map (f ≫ g)) = X.map ((natTail n).map f) ≫
              X.map ((natTail n).map g)
          rw [Functor.map_comp, Functor.map_comp]
      | right => change (𝟙 (Y.obj n)) = (𝟙 (Y.obj n)) ≫ (𝟙 (Y.obj n)); simp

/-- The actual cospan colimit cocone, on the original apex map q and original Y injection. -/
@[reducible]
def tailCospanCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (tailCospanDiagram p n) where
  pt := cospan q (cY.ι.app n)
  ι :=
    { app := fun k => cospanHomMk
        (F := cospan (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))
        (G := cospan q (cY.ι.app n))
        (cY.ι.app (n + k)) (cX.ι.app (n + k)) (𝟙 (Y.obj n))
        (by
          change p.app (n + k) ≫ cY.ι.app (n + k) = cX.ι.app (n + k) ≫ q
          exact (hq (n + k)).symm)
        (by
          change Y.map (homOfLE (Nat.le_add_right n k)) ≫ cY.ι.app (n + k) =
            (𝟙 (Y.obj n)) ≫ cY.ι.app n
          simp)
      naturality := by
        intro i j f
        ext k
        cases k with
        | none => simp [tailCospanDiagram, cospanHomMk]
        | some a => cases a with
          | left => simp [tailCospanDiagram, cospanHomMk]
          | right => simp [tailCospanDiagram, cospanHomMk] }

/-- This is the literal diagram k↦pullback(p_(n+k),Y(n→n+k)). -/
@[reducible]
def tailPullbackDiagram {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ) : ℕ ⥤ SSet.{u} :=
  tailCospanDiagram p n ⋙ lim

/-- This is the literal cocone on pullback(q,ιY_n). -/
@[reducible]
def tailPullbackCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    Cocone (tailPullbackDiagram p n) :=
  lim.mapCocone (tailCospanCocone p n cX cY q hq)

theorem tailPullbackDiagram_map_legs {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {i j : ℕ} (f : i ⟶ j) :
    (tailPullbackDiagram p n).map f ≫
        pullback.fst (p.app (n + j)) (Y.map (homOfLE (Nat.le_add_right n j))) =
      pullback.fst (p.app (n + i)) (Y.map (homOfLE (Nat.le_add_right n i))) ≫
        X.map ((natTail n).map f) ∧
    (tailPullbackDiagram p n).map f ≫
        pullback.snd (p.app (n + j)) (Y.map (homOfLE (Nat.le_add_right n j))) =
      pullback.snd (p.app (n + i)) (Y.map (homOfLE (Nat.le_add_right n i))) := by
  constructor <;> simp [tailPullbackDiagram, tailCospanDiagram, cospanHomMk]

theorem tailPullbackCocone_legs {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) (k : ℕ) :
    (tailPullbackCocone p n cX cY q hq).ι.app k ≫ pullback.fst q (cY.ι.app n) =
      pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫ cX.ι.app (n + k) ∧
    (tailPullbackCocone p n cX cY q hq).ι.app k ≫ pullback.snd q (cY.ι.app n) =
      pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) := by
  constructor <;> simp [tailPullbackCocone, tailCospanCocone, cospanHomMk]

private theorem natColim_preservesFiniteLimits :
    PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  constructor
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) K
  intro a
  let E : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
  let _ : PreservesLimitsOfShape K
      ((CategoryTheory.Functor.whiskeringRight ℕ SSet.{u} (Type u)).obj E ⋙ colim) := inferInstance
  exact preservesLimitsOfShape_of_natIso (preservesColimitNatIso E).symm

/-- Genuine tail pullback-colimit comparison, even when the original Y maps are NOT mono. -/
def tailPullbackCoconeIsColimit {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    IsColimit (tailPullbackCocone p n cX cY q hq) := by
  let _ : IsConnected ℕ := CategoryTheory.IsFiltered.isConnected ℕ
  let _ : (natTail n).Final := natTail_final n
  have hcx : IsColimit (tailCospanCocone p n cX cY q hq) := by
    apply evaluationJointlyReflectsColimits
    intro j
    cases j with
    | none =>
        change IsColimit (cY.whisker (natTail n))
        exact (CategoryTheory.Functor.Final.isColimitWhiskerEquiv (natTail n) cY).symm hY
    | some a => cases a with
      | left =>
          change IsColimit (cX.whisker (natTail n))
          exact (CategoryTheory.Functor.Final.isColimitWhiskerEquiv (natTail n) cX).symm hX
      | right =>
          change IsColimit (constCocone ℕ (Y.obj n))
          exact isColimitConstCocone ℕ (Y.obj n)
  let _ : PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
    constructor
    intro K _ _
    apply preservesLimitsOfShape_of_evaluation (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) K
    intro a
    let E : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
    let _ : PreservesLimitsOfShape K
        ((CategoryTheory.Functor.whiskeringRight ℕ SSet.{u} (Type u)).obj E ⋙ colim) :=
            inferInstance
    exact preservesLimitsOfShape_of_natIso (preservesColimitNatIso E).symm
  let _ : PreservesColimitsOfShape ℕ (lim : (WalkingCospan ⥤ SSet.{u}) ⥤ SSet.{u}) :=
    (preservesColimitsOfShape_lim_iff_preservesLimitsOfShape_colim WalkingCospan ℕ SSet.{u}).2
        inferInstance
  exact isColimitOfPreserves lim hcx

/-- The whole canonical original colimit-to-pullback isomorphism. -/
def tailPullbackColimitIso {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    colimit (tailPullbackDiagram p n) ≅ pullback q (cY.ι.app n) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (tailPullbackCoconeIsColimit p n cX cY q hq hX hY)

theorem tailPullbackColimitIso_hom_legs {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) (k : ℕ) :
    colimit.ι (tailPullbackDiagram p n) k ≫ (tailPullbackColimitIso p n cX cY q hq hX hY).hom ≫
        pullback.fst q (cY.ι.app n) =
      pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫ cX.ι.app (n + k) ∧
    colimit.ι (tailPullbackDiagram p n) k ≫ (tailPullbackColimitIso p n cX cY q hq hX hY).hom ≫
        pullback.snd q (cY.ι.app n) =
      pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) := by
  have hi : colimit.ι (tailPullbackDiagram p n) k ≫
      (tailPullbackColimitIso p n cX cY q hq hX hY).hom =
        (tailPullbackCocone p n cX cY q hq).ι.app k :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
      (tailPullbackCoconeIsColimit p n cX cY q hq hX hY) k
  constructor
  · rw [← Category.assoc, hi]; exact (tailPullbackCocone_legs p n cX cY q hq k).1
  · rw [← Category.assoc, hi]; exact (tailPullbackCocone_legs p n cX cY q hq k).2

/-- The ORIGINAL aggregate first projection cocone into the given X colimit apex. -/
@[reducible]
def tailFirstProjectionCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) : Cocone (tailPullbackDiagram p n) :=
  (tailPullbackCocone p n cX cY q hq).extend (pullback.fst q (cY.ι.app n))

/-- The ORIGINAL aggregate second projection cocone into the same fixed Y(n). -/
@[reducible]
def tailSecondProjectionCocone {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) : Cocone (tailPullbackDiagram p n) :=
  (tailPullbackCocone p n cX cY q hq).extend (pullback.snd q (cY.ι.app n))

/-- Both inverse equations are on genuine aggregate original projections, never individual
stages. -/
theorem tailPullbackColimitIso_inv_legs {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY) :
    (tailPullbackColimitIso p n cX cY q hq hX hY).inv ≫
        colimit.desc (tailPullbackDiagram p n) (tailFirstProjectionCocone p n cX cY q hq) =
      pullback.fst q (cY.ι.app n) ∧
    (tailPullbackColimitIso p n cX cY q hq hX hY).inv ≫
        colimit.desc (tailPullbackDiagram p n) (tailSecondProjectionCocone p n cX cY q hq) =
      pullback.snd q (cY.ι.app n) := by
  let hcp := tailPullbackCoconeIsColimit p n cX cY q hq hX hY
  constructor
  · change ((colimit.isColimit (tailPullbackDiagram p n)).coconePointUniqueUpToIso hcp).inv ≫
        (colimit.isColimit (tailPullbackDiagram p n)).desc
          (tailFirstProjectionCocone p n cX cY q hq) = pullback.fst q (cY.ι.app n)
    rw [IsColimit.coconePointUniqueUpToIso_inv_desc]
    apply hcp.hom_ext
    intro j
    exact hcp.fac (tailFirstProjectionCocone p n cX cY q hq) j
  · change ((colimit.isColimit (tailPullbackDiagram p n)).coconePointUniqueUpToIso hcp).inv ≫
        (colimit.isColimit (tailPullbackDiagram p n)).desc
          (tailSecondProjectionCocone p n cX cY q hq) = pullback.snd q (cY.ι.app n)
    rw [IsColimit.coconePointUniqueUpToIso_inv_desc]
    apply hcp.hom_ext
    intro j
    exact hcp.fac (tailSecondProjectionCocone p n cX cY q hq) j

end SSet.RezkTailPullbackColimit

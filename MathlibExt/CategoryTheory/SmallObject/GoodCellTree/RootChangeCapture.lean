/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerPresentation

/-!
# Original bounded supports for compact sources across arbitrary roots

Map the same chosen bounded-support presentation by the actual Under.map.
Compactness belongs to the source under its own root. The mapped pieces
need no compactness assumption. Every returned raw factor has its original
root equation and its endpoint equation, using the same lower maps and
endpoint comparison. Bounded families keep all original roots and seeds.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u uI

namespace CategoryTheory.SmallObject.RootChangeCapture

open CategoryTheory.Limits BoundedLowerSupport

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] {X Y : C} (ρ : X ⟶ Y)

section Generic

variable {Z : P ⥤ Under Y} (L : LowerSetColimitData Z)
  (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) {E : Under Y} (γ : L.obj ⊤ ≅ E)

/-- The original endpoint presentation mapped through precisely the given root arrow. -/
def presentation : ColimitPresentation (Carrier (P := P) κ) ((Under.map ρ).obj E) := by
  let : IsConnected (Carrier (P := P) κ) := IsFiltered.isConnected _
  exact RootChangeColimits.mappedPresentation ρ (endpointPresentation κ L hPred γ)

@[simp]
theorem presentation_diag :
    (presentation κ ρ L hPred γ).diag = diagram κ L ⋙ Under.map ρ := rfl

/-- Every actual mapped piece retains its original chosen right object. -/
theorem presentation_object_right_function :
    (fun B : Carrier (P := P) κ => ((presentation κ ρ L hPred γ).diag.obj B).right) =
      (fun B : Carrier (P := P) κ => (L.obj B.1).right) := rfl

/-- Every actual mapped piece root is the original prescribed root composite. -/
theorem presentation_object_root_function :
    (fun B : Carrier (P := P) κ => ((presentation κ ρ L hPred γ).diag.obj B).hom) =
      (fun B : Carrier (P := P) κ => ρ ≫ (L.obj B.1).hom) := rfl

/-- Each native mapped leg is the image of the same original lower map and endpoint Iso. -/
theorem presentation_leg (B : Carrier (P := P) κ) :
    (presentation κ ρ L hPred γ).ι.app B =
      (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) := by
  change (Under.map ρ).map ((endpointPresentation κ L hPred γ).ι.app B) ≫ 𝟙 _ = _
  rw [Category.comp_id, endpointPresentation_leg]
  rfl

/-- The complete dependent right-leg function is the given original endpoint function. -/
theorem presentation_leg_right_function :
    (fun B : Carrier (P := P) κ => ((presentation κ ρ L hPred γ).ι.app B).right) =
      (fun B : Carrier (P := P) κ =>
        (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right) := by
  funext B
  rw [presentation_leg, Under.map_map_right]

/-- The complete dependent comparison function keeps all original lower-map right functions. -/
theorem presentation_map_right_function :
    (fun (B D : Carrier (P := P) κ) (f : B ⟶ D) =>
      ((presentation κ ρ L hPred γ).diag.map f).right) =
      (fun (B D : Carrier (P := P) κ) (f : B ⟶ D) => (L.map (leOfHom f)).right) := rfl

/-- Extending a genuine raw factor preserves its original root equation. -/
theorem extend_root {A : Under X} {B D : LowerSet P} (hBD : B ≤ D)
    (p : A.right ⟶ (L.obj B).right) (hRoot : A.hom ≫ p = ρ ≫ (L.obj B).hom) :
    A.hom ≫ (p ≫ (L.map hBD).right) = ρ ≫ (L.obj D).hom := by
  calc
    A.hom ≫ (p ≫ (L.map hBD).right) = (A.hom ≫ p) ≫ (L.map hBD).right :=
      (Category.assoc _ _ _).symm
    _ = (ρ ≫ (L.obj B).hom) ≫ (L.map hBD).right := congrArg (· ≫ _) hRoot
    _ = ρ ≫ (L.obj D).hom := by rw [Category.assoc, Under.w]

/-- Extending a factor uses precisely the original comparison and endpoint functions. -/
theorem extend_endpoint {A : C} {B D : LowerSet P} (hBD : B ≤ D)
    (p : A ⟶ (L.obj B).right) :
    (p ≫ (L.map hBD).right) ≫ (L.map (le_top : D ≤ ⊤) ≫ γ.hom).right =
      p ≫ (L.map (le_top : B ≤ ⊤) ≫ γ.hom).right := by
  simp only [Category.assoc, ← Under.comp_right, L.map_comp_assoc]

include hPred

/-- Native compactness returns an actual Under factor through an original bounded piece. -/
theorem existsUnderFactor {A : Under X} [IsCardinalPresentable A κ]
    (f : A ⟶ (Under.map ρ).obj E) :
    ∃ (B : Carrier (P := P) κ) (p : A ⟶ (Under.map ρ).obj (L.obj B.1)),
      p ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) = f := by
  let : EssentiallySmall.{w} (Carrier (P := P) κ) :=
    essentiallySmall_of_small_of_locallySmall (Carrier (P := P) κ)
  let pres := presentation κ ρ L hPred γ
  obtain ⟨B, p, hp⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ pres.isColimit f
  refine ⟨B, p, ?_⟩
  change p ≫ (presentation κ ρ L hPred γ).ι.app B = f at hp
  rw [presentation_leg] at hp
  exact hp

/-- The same actual Under factor can include a specified original bounded seed. -/
theorem existsUnderFactorContaining {A : Under X} [IsCardinalPresentable A κ]
    (f : A ⟶ (Under.map ρ).obj E) (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧
      ∃ (p : A ⟶ (Under.map ρ).obj (L.obj B.1)),
        p ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) = f := by
  obtain ⟨D, p, hp⟩ := existsUnderFactor κ ρ L hPred γ f
  let B := union κ seed D
  have hDB : D.1 ≤ B.1 := le_union_right κ seed D
  let q := p ≫ (Under.map ρ).map (L.map hDB)
  refine ⟨B, le_union_left κ seed D, q, ?_⟩
  calc
    q ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) =
        p ≫ (Under.map ρ).map (L.map hDB ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) := by
      simp only [q, Functor.map_comp, Category.assoc]
    _ = f := by simpa only [L.map_comp_assoc] using hp

/-- A root-compatible raw map has a compact-source factor and BOTH original equations. -/
theorem existsFactor {A : Under X} [IsCardinalPresentable A κ]
    (f : A.right ⟶ E.right) (hRoot : A.hom ≫ f = ρ ≫ E.hom) :
    ∃ (B : Carrier (P := P) κ) (p : A.right ⟶ (L.obj B.1).right),
      A.hom ≫ p = ρ ≫ (L.obj B.1).hom ∧
        p ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right = f := by
  let fUnder : A ⟶ (Under.map ρ).obj E := Under.homMk f hRoot
  obtain ⟨B, p, hp⟩ := existsUnderFactor κ ρ L hPred γ fUnder
  exact ⟨B, p.right, Under.w p, congrArg Under.Hom.right hp⟩

/-- Include the actual original seed while retaining both the root and endpoint functions. -/
theorem existsFactorContaining {A : Under X} [IsCardinalPresentable A κ]
    (f : A.right ⟶ E.right) (hRoot : A.hom ≫ f = ρ ≫ E.hom)
    (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧
      ∃ (p : A.right ⟶ (L.obj B.1).right),
        A.hom ≫ p = ρ ≫ (L.obj B.1).hom ∧
          p ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right = f := by
  let fUnder : A ⟶ (Under.map ρ).obj E := Under.homMk f hRoot
  obtain ⟨B, hSeed, p, hp⟩ := existsUnderFactorContaining κ ρ L hPred γ fUnder seed
  exact ⟨B, hSeed, p.right, Under.w p, congrArg Under.Hom.right hp⟩

/-- Native eventual equality is detected with the same mapped diagram and original lower maps. -/
theorem existsUnderEqualityContaining {A : Under X} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ)
    (f g : A ⟶ (Under.map ρ).obj (L.obj B.1))
    (he : f ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) =
      g ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom)) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      f ≫ (Under.map ρ).map (L.map hBD) = g ≫ (Under.map ρ).map (L.map hBD) := by
  let : EssentiallySmall.{w} (Carrier (P := P) κ) :=
    essentiallySmall_of_small_of_locallySmall (Carrier (P := P) κ)
  let pres := presentation κ ρ L hPred γ
  have he' : f ≫ pres.ι.app B = g ≫ pres.ι.app B := by
    simpa only [pres, presentation_leg] using he
  obtain ⟨D, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ pres.isColimit f g he'
  change f ≫ (Under.map ρ).map (L.map (leOfHom u)) =
    g ≫ (Under.map ρ).map (L.map (leOfHom u)) at hu
  let H := union κ seed D
  have hDH : D.1 ≤ H.1 := le_union_right κ seed D
  refine ⟨H, le_union_left κ seed D, (leOfHom u).trans hDH, ?_⟩
  have h := congrArg (fun k : A ⟶ (Under.map ρ).obj (L.obj D.1) =>
    k ≫ (Under.map ρ).map (L.map hDH)) hu
  simpa only [Category.assoc, ← Functor.map_comp, L.map_comp] using h

/-- Original raw equalities have an actual larger bounded support and both preserved root laws. -/
theorem existsEqualityContaining {A : Under X} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ) (f g : A.right ⟶ (L.obj B.1).right)
    (hRootF : A.hom ≫ f = ρ ≫ (L.obj B.1).hom)
    (hRootG : A.hom ≫ g = ρ ≫ (L.obj B.1).hom)
    (he : f ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right =
      g ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      A.hom ≫ (f ≫ (L.map hBD).right) = ρ ≫ (L.obj D.1).hom ∧
        A.hom ≫ (g ≫ (L.map hBD).right) = ρ ≫ (L.obj D.1).hom ∧
          f ≫ (L.map hBD).right = g ≫ (L.map hBD).right := by
  let fUnder : A ⟶ (Under.map ρ).obj (L.obj B.1) := Under.homMk f hRootF
  let gUnder : A ⟶ (Under.map ρ).obj (L.obj B.1) := Under.homMk g hRootG
  have he' : fUnder ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) =
      gUnder ≫ (Under.map ρ).map (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) :=
    Under.UnderMorphism.ext he
  obtain ⟨D, hSeed, hBD, hEq⟩ :=
    existsUnderEqualityContaining κ ρ L hPred γ B seed fUnder gUnder he'
  exact ⟨D, hSeed, hBD, extend_root ρ L hBD f hRootF,
    extend_root ρ L hBD g hRootG, congrArg Under.Hom.right hEq⟩

/-- A genuinely small family may have DIFFERENT actual source roots and root arrows.
Its common original bounded support contains every specified seed. -/
theorem existsFactorFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (roots : I → C) (ρs : ∀ i, roots i ⟶ Y) (A : ∀ i, Under (roots i))
    [∀ i, IsCardinalPresentable (A i) κ] (f : ∀ i, (A i).right ⟶ E.right)
    (hRoot : ∀ i, (A i).hom ≫ f i = ρs i ≫ E.hom)
    (seed : Carrier (P := P) κ) (seeds : I → Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ (∀ i, seeds i ≤ B) ∧
      ∃ (p : ∀ i, (A i).right ⟶ (L.obj B.1).right),
        ∀ i, (A i).hom ≫ p i = ρs i ≫ (L.obj B.1).hom ∧
          p i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right = f i := by
  have h (i : I) := existsFactorContaining κ (ρs i) L hPred γ (f i) (hRoot i) (seeds i)
  choose D hSeed p hRootP hEnd using h
  let U := indexedUnion κ D hI
  let B := union κ seed U
  have hi (i : I) : (D i).1 ≤ B.1 :=
    (le_indexedUnion κ D hI i).trans (le_union_right κ seed U)
  refine ⟨B, le_union_left κ seed U, fun i => (hSeed i).trans (hi i),
    fun i => p i ≫ (L.map (hi i)).right, ?_⟩
  intro i
  exact ⟨extend_root (ρs i) L (hi i) (p i) (hRootP i),
    (extend_endpoint L γ (hi i) (p i)).trans (hEnd i)⟩

/-- Genuinely small families of equalities have one original common support.
The base support and the base seed remain included for an EMPTY family. -/
theorem existsEqualityFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (roots : I → C) (ρs : ∀ i, roots i ⟶ Y) (A : ∀ i, Under (roots i))
    [∀ i, IsCardinalPresentable (A i) κ] (B seed : Carrier (P := P) κ)
    (seeds : I → Carrier (P := P) κ)
    (f g : ∀ i, (A i).right ⟶ (L.obj B.1).right)
    (hRootF : ∀ i, (A i).hom ≫ f i = ρs i ≫ (L.obj B.1).hom)
    (hRootG : ∀ i, (A i).hom ≫ g i = ρs i ≫ (L.obj B.1).hom)
    (he : ∀ i, f i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right =
      g i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom).right) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ (∀ i, seeds i ≤ D) ∧
      ∃ (hBD : B.1 ≤ D.1), ∀ i,
        (A i).hom ≫ (f i ≫ (L.map hBD).right) = ρs i ≫ (L.obj D.1).hom ∧
          (A i).hom ≫ (g i ≫ (L.map hBD).right) = ρs i ≫ (L.obj D.1).hom ∧
            f i ≫ (L.map hBD).right = g i ≫ (L.map hBD).right := by
  have h (i : I) := existsEqualityContaining κ (ρs i) L hPred γ B (seeds i)
    (f i) (g i) (hRootF i) (hRootG i) (he i)
  choose D hSeed hBD hRootFP hRootGP hEq using h
  let U := indexedUnion κ D hI
  let H := union κ seed (union κ B U)
  have hBH : B.1 ≤ H.1 :=
    (le_union_left κ B U).trans (le_union_right κ seed (union κ B U))
  have hi (i : I) : (D i).1 ≤ H.1 :=
    ((le_indexedUnion κ D hI i).trans (le_union_right κ B U)).trans
      (le_union_right κ seed (union κ B U))
  refine ⟨H, le_union_left κ seed (union κ B U), fun i => (hSeed i).trans (hi i),
    hBH, ?_⟩
  intro i
  refine ⟨extend_root (ρs i) L hBH (f i) (hRootF i),
    extend_root (ρs i) L hBH (g i) (hRootG i), ?_⟩
  have h := congrArg (fun k : (A i).right ⟶ (L.obj (D i).1).right =>
    k ≫ (L.map (hi i)).right) (hEq i)
  simpa only [Category.assoc, ← Under.comp_right, L.map_comp] using h

end Generic

section Tree

variable {α : Type t} {s : α → Arrow C} (T : CellTree s Y (P := P))
  (h : T.IsGood κ) (L : LowerSetColimitData T.diagram)

/-- The same good tree presentation uses exactly its original selected L and endpoint Iso. -/
def treePresentation : ColimitPresentation (Carrier (P := P) κ)
    ((Under.map ρ).obj T.endpointObj) :=
  presentation κ ρ L h.predecessor_lt (T.endpointIso L)

/-- The whole original tree leg function is retained across the given arbitrary root. -/
theorem treePresentation_leg_right_function :
    (fun B : Carrier (P := P) κ => ((treePresentation κ ρ T h L).ι.app B).right) =
      (fun B : Carrier (P := P) κ =>
        (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :=
  presentation_leg_right_function κ ρ L h.predecessor_lt (T.endpointIso L)

include h

/-- A compact source under its own root has both original factor equations in the target tree. -/
theorem existsTreeFactorContaining {A : Under X} [IsCardinalPresentable A κ]
    (f : A.right ⟶ T.endpointObj.right) (hRoot : A.hom ≫ f = ρ ≫ T.hom)
    (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧
      ∃ (p : A.right ⟶ (L.obj B.1).right),
        A.hom ≫ p = ρ ≫ (L.obj B.1).hom ∧
          p ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right = f :=
  existsFactorContaining κ ρ L h.predecessor_lt (T.endpointIso L) f hRoot seed

/-- The same tree detects original root-compatible raw equalities on a bounded larger support. -/
theorem existsTreeEqualityContaining {A : Under X} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ) (f g : A.right ⟶ (L.obj B.1).right)
    (hRootF : A.hom ≫ f = ρ ≫ (L.obj B.1).hom)
    (hRootG : A.hom ≫ g = ρ ≫ (L.obj B.1).hom)
    (he : f ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right =
      g ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      A.hom ≫ (f ≫ (L.map hBD).right) = ρ ≫ (L.obj D.1).hom ∧
        A.hom ≫ (g ≫ (L.map hBD).right) = ρ ≫ (L.obj D.1).hom ∧
          f ≫ (L.map hBD).right = g ≫ (L.map hBD).right :=
  existsEqualityContaining κ ρ L h.predecessor_lt (T.endpointIso L)
    B seed f g hRootF hRootG he

/-- Different original source roots share one bounded support in the SAME target tree. -/
theorem existsTreeFactorFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (roots : I → C) (ρs : ∀ i, roots i ⟶ Y) (A : ∀ i, Under (roots i))
    [∀ i, IsCardinalPresentable (A i) κ] (f : ∀ i, (A i).right ⟶ T.endpointObj.right)
    (hRoot : ∀ i, (A i).hom ≫ f i = ρs i ≫ T.hom)
    (seed : Carrier (P := P) κ) (seeds : I → Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ (∀ i, seeds i ≤ B) ∧
      ∃ (p : ∀ i, (A i).right ⟶ (L.obj B.1).right),
        ∀ i, (A i).hom ≫ p i = ρs i ≫ (L.obj B.1).hom ∧
          p i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right = f i :=
  existsFactorFamily κ L h.predecessor_lt (T.endpointIso L)
    hI roots ρs A f hRoot seed seeds

/-- Every original root and equality law survives a bounded tree-family comparison. -/
theorem existsTreeEqualityFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (roots : I → C) (ρs : ∀ i, roots i ⟶ Y) (A : ∀ i, Under (roots i))
    [∀ i, IsCardinalPresentable (A i) κ] (B seed : Carrier (P := P) κ)
    (seeds : I → Carrier (P := P) κ)
    (f g : ∀ i, (A i).right ⟶ (L.obj B.1).right)
    (hRootF : ∀ i, (A i).hom ≫ f i = ρs i ≫ (L.obj B.1).hom)
    (hRootG : ∀ i, (A i).hom ≫ g i = ρs i ≫ (L.obj B.1).hom)
    (he : ∀ i, f i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right =
      g i ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ (∀ i, seeds i ≤ D) ∧
      ∃ (hBD : B.1 ≤ D.1), ∀ i,
        (A i).hom ≫ (f i ≫ (L.map hBD).right) = ρs i ≫ (L.obj D.1).hom ∧
          (A i).hom ≫ (g i ≫ (L.map hBD).right) = ρs i ≫ (L.obj D.1).hom ∧
            f i ≫ (L.map hBD).right = g i ≫ (L.map hBD).right :=
  existsEqualityFamily κ L h.predecessor_lt (T.endpointIso L)
    hI roots ρs A B seed seeds f g hRootF hRootG he

end Tree

end CategoryTheory.SmallObject.RootChangeCapture

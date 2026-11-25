/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerSupport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability

/-!
# Actual compact-source factors through original bounded lower pieces

The original endpoint presentation supplies actual factors and eventual
equalities. Specified original seeds and bounded families are included
by genuine unions. The tree application keeps its original Under root,
colimits, endpoint comparison and free-object transposition.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u uI

namespace CategoryTheory.SmallObject.BoundedLowerPresentation

open CategoryTheory.Limits BoundedLowerSupport UnderColimits

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

section Generic

variable {Y : P ⥤ C} (L : LowerSetColimitData Y)
  (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) {E : C} (γ : L.obj ⊤ ≅ E)

include hPred

/-- An actual compact-source arrow factors through an original bounded selected piece. -/
theorem existsFactor {A : C} [IsCardinalPresentable A κ] (f : A ⟶ E) :
    ∃ (B : Carrier (P := P) κ) (p : A ⟶ L.obj B.1),
      p ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom = f := by
  let : EssentiallySmall.{w} (Carrier (P := P) κ) :=
    essentiallySmall_of_small_of_locallySmall (Carrier (P := P) κ)
  let pres := endpointPresentation κ L hPred γ
  obtain ⟨B, p, hp⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ pres.isColimit f
  refine ⟨B, p, ?_⟩
  change p ≫ (endpointPresentation κ L hPred γ).ι.app B = f at hp
  rw [endpointPresentation_leg κ L hPred γ B] at hp
  exact hp

/-- The same factor includes a specified bounded original seed with its literal inclusion. -/
theorem existsFactorContaining {A : C} [IsCardinalPresentable A κ]
    (f : A ⟶ E) (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ ∃ (p : A ⟶ L.obj B.1),
      p ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom = f := by
  obtain ⟨D, p, hp⟩ := existsFactor κ L hPred γ f
  let B := union κ seed D
  have hD : D.1 ≤ B.1 := by
    change D.1 ≤ seed.1 ⊔ D.1
    exact le_sup_right
  refine ⟨B, le_union_left κ seed D, p ≫ L.map hD, ?_⟩
  simpa only [Category.assoc, L.map_comp_assoc] using hp

/-- Equal original endpoint composites become equal on a bounded support containing both seeds. -/
theorem existsEqualityContaining {A : C} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ) (f g : A ⟶ L.obj B.1)
    (he : f ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom =
      g ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      f ≫ L.map hBD = g ≫ L.map hBD := by
  let : EssentiallySmall.{w} (Carrier (P := P) κ) :=
    essentiallySmall_of_small_of_locallySmall (Carrier (P := P) κ)
  let pres := endpointPresentation κ L hPred γ
  have he' : f ≫ pres.ι.app B = g ≫ pres.ι.app B := by
    simpa only [pres, endpointPresentation_leg] using he
  obtain ⟨D, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ pres.isColimit f g he'
  change f ≫ L.map (leOfHom u) = g ≫ L.map (leOfHom u) at hu
  let H := union κ seed D
  have hDH : D.1 ≤ H.1 := by
    change D.1 ≤ seed.1 ⊔ D.1
    exact le_sup_right
  refine ⟨H, le_union_left κ seed D, (leOfHom u).trans hDH, ?_⟩
  have h := congrArg (fun k : A ⟶ L.obj D.1 => k ≫ L.map hDH) hu
  simpa only [Category.assoc, L.map_comp] using h

/-- A genuinely bounded family of actual compact-source arrows has one original
bounded factor support. -/
theorem existsFactorFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (A : I → C) [∀ i, IsCardinalPresentable (A i) κ] (f : ∀ i, A i ⟶ E)
    (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ ∃ (p : ∀ i, A i ⟶ L.obj B.1),
      ∀ i, p i ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom = f i := by
  have h (i : I) := existsFactor κ L hPred γ (f i)
  choose D p hp using h
  let U := indexedUnion κ D hI
  let B := union κ seed U
  have hi (i : I) : (D i).1 ≤ B.1 := by
    exact (le_indexedUnion κ D hI i).trans (le_union_right κ seed U)
  refine ⟨B, le_union_left κ seed U, fun i => p i ≫ L.map (hi i), ?_⟩
  intro i
  simpa only [Category.assoc, L.map_comp_assoc] using hp i

/-- Bounded many actual equalities have one original common support, including the empty family. -/
theorem existsEqualityFamily {I : Type uI} (hI : HasCardinalLT I κ)
    (A : I → C) [∀ i, IsCardinalPresentable (A i) κ] (B seed : Carrier (P := P) κ)
    (f g : ∀ i, A i ⟶ L.obj B.1)
    (he : ∀ i, f i ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom =
      g i ≫ L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      ∀ i, f i ≫ L.map hBD = g i ≫ L.map hBD := by
  have h (i : I) := existsEqualityContaining κ L hPred γ B seed (f i) (g i) (he i)
  choose D hSeed hBD hEq using h
  let U := indexedUnion κ D hI
  let H := union κ seed (union κ B U)
  have hBU : B.1 ≤ H.1 :=
    (le_union_left κ B U).trans (le_union_right κ seed (union κ B U))
  have hi (i : I) : (D i).1 ≤ H.1 :=
    ((le_indexedUnion κ D hI i).trans (le_union_right κ B U)).trans
      (le_union_right κ seed (union κ B U))
  refine ⟨H, le_union_left κ seed (union κ B U), hBU, ?_⟩
  intro i
  have h := congrArg (fun k : A i ⟶ L.obj (D i).1 => k ≫ L.map (hi i)) (hEq i)
  simpa only [Category.assoc, L.map_comp] using h

end Generic

section Tree

variable {α : Type t} {s : α → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (h : T.IsGood κ) (L : LowerSetColimitData T.diagram)

include h

/-- The actual given good tree's endpoint has its original bounded-support native presentation. -/
def treePresentation : ColimitPresentation (Carrier (P := P) κ) T.endpointObj :=
  endpointPresentation κ L h.predecessor_lt (T.endpointIso L)

@[simp]
theorem treePresentation_diag : (treePresentation κ T h L).diag = diagram κ L := rfl

/-- The entire tree-presentation leg FUNCTION keeps its actual original endpoint comparison. -/
theorem treePresentation_leg_function :
    (fun B : Carrier (P := P) κ => (treePresentation κ T h L).ι.app B) =
      (fun B : Carrier (P := P) κ => L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom) :=
  endpointPresentation_leg_function κ L h.predecessor_lt (T.endpointIso L)

/-- A compact under-object's actual map factors through the same chosen tree piece. -/
theorem existsTreeFactor {A : Under X} [IsCardinalPresentable A κ] (f : A ⟶ T.endpointObj) :
    ∃ (B : Carrier (P := P) κ) (p : A ⟶ L.obj B.1),
      p ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom = f := by
  exact existsFactor κ L h.predecessor_lt (T.endpointIso L) f

/-- The original arbitrary-root factor can include any given bounded original seed. -/
theorem existsTreeFactorContaining {A : Under X} [IsCardinalPresentable A κ]
    (f : A ⟶ T.endpointObj) (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ ∃ (p : A ⟶ L.obj B.1),
      p ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom = f := by
  exact existsFactorContaining κ L h.predecessor_lt (T.endpointIso L) f seed

/-- The actual tree endpoint detects original compact-source equalities on a bounded
common support. -/
theorem existsTreeEqualityContaining {A : Under X} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ) (f g : A ⟶ L.obj B.1)
    (he : f ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom =
      g ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      f ≫ L.map hBD = g ≫ L.map hBD := by
  exact existsEqualityContaining κ L h.predecessor_lt (T.endpointIso L) B seed f g he

variable [HasBinaryCoproducts C]

/-- Every piece of the original bounded-support presentation is relatively presentable. -/
theorem piecePresentable [LocallySmall.{w} C] (B : Carrier (P := P) κ) :
    IsCardinalPresentable (L.obj B.1) κ :=
  RelativeCellPresentability.selectedLower κ T h L B.1 B.2

/-- A compact coefficient arrow has its actual factor, with the SAME costar
transposition and seed. -/
theorem existsRawFactorContaining {A : C} [IsCardinalPresentable A κ]
    (f : A ⟶ T.endpointObj.right) (seed : Carrier (P := P) κ) :
    ∃ (B : Carrier (P := P) κ), seed ≤ B ∧ ∃ (p : A ⟶ (L.obj B.1).right),
      p ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right = f := by
  let : IsCardinalPresentable ((Under.costar X).obj A) κ := costarPresentable κ A
  obtain ⟨B, hSeed, p, hp⟩ := existsTreeFactorContaining κ T h L (transpose f) seed
  refine ⟨B, hSeed, (Under.costarAdjForget X).homEquiv A (L.obj B.1) p, ?_⟩
  have he := congrArg ((Under.costarAdjForget X).homEquiv A T.endpointObj) hp
  rw [(Under.costarAdjForget X).homEquiv_naturality_right] at he
  simpa only [Under.forget_obj, Under.forget_map, transpose, Equiv.apply_symm_apply] using he

/-- Original raw coefficient equalities are detected through the SAME natural hom equivalence. -/
theorem existsRawEqualityContaining {A : C} [IsCardinalPresentable A κ]
    (B seed : Carrier (P := P) κ) (f g : A ⟶ (L.obj B.1).right)
    (he : f ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right =
      g ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :
    ∃ (D : Carrier (P := P) κ), seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
      f ≫ (L.map hBD).right = g ≫ (L.map hBD).right := by
  let : IsCardinalPresentable ((Under.costar X).obj A) κ := costarPresentable κ A
  have he' : transpose f ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom =
      transpose g ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom := by
    calc
      transpose f ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom =
          transpose (f ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :=
        transpose_target f (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom)
      _ = transpose (g ≫ (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom).right) :=
        congrArg (fun a => transpose a) he
      _ = transpose g ≫ L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom :=
        (transpose_target g (L.map (le_top : B.1 ≤ ⊤) ≫ (T.endpointIso L).hom)).symm
  obtain ⟨D, hSeed, hBD, hp⟩ :=
    existsTreeEqualityContaining κ T h L B seed (transpose f) (transpose g) he'
  refine ⟨D, hSeed, hBD, ?_⟩
  have he'' := congrArg ((Under.costarAdjForget X).homEquiv A (L.obj D.1)) hp
  rw [(Under.costarAdjForget X).homEquiv_naturality_right,
    (Under.costarAdjForget X).homEquiv_naturality_right] at he''
  simpa only [Under.forget_obj, Under.forget_map, transpose, Equiv.apply_symm_apply] using he''

end Tree

end CategoryTheory.SmallObject.BoundedLowerPresentation

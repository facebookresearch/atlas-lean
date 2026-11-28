/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntExtensionIso
public import MathlibExt.CategoryTheory.Monoidal.IntReconstruction
public import MathlibExt.CategoryTheory.Monoidal.DualComparison

/-!
# Comparison of monoidal extensions from Int

A monoidal natural isomorphism between restrictions of braided monoidal functors
out of Int extends uniquely to a monoidal natural isomorphism. The target of this
restriction theorem is symmetric monoidal and need not be rigid. For a right-rigid
target, every specified extension of a traced functor is therefore uniquely
monoidally isomorphic to the canonical extension. The source needs no duals.

This is the isomorphism-level universal property in the symmetric specialization
of Joyal, Street and
Verity, Traced monoidal categories (1996), Proposition 5.2,
https://doi.org/10.1017/S0305004100074338.
-/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
private def tensorComparison {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : E}
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y) :
    F.obj (X ⊗ Y) ≅ G.obj (X ⊗ Y) :=
  (μIso F X Y).symm ≪≫ (a ⊗ᵢ b) ≪≫ μIso G X Y

private def unitComparison {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] : F.obj (𝟙_ E) ≅ G.obj (𝟙_ E) :=
  (εIso F).symm ≪≫ εIso G

private def ComparisonSquare {E : Type*} [Category E] (F G : E ⥤ D)
    {X Y : E} (f : X ⟶ Y) (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y) : Prop :=
  F.map f ≫ b.hom = a.hom ≫ G.map f

omit [MonoidalCategory D] [SymmetricCategory D] in
private theorem ComparisonSquare.comp {E : Type*} [Category E] {F G : E ⥤ D}
    {X Y Z : E} {f : X ⟶ Y} {g : Y ⟶ Z}
    {a : F.obj X ≅ G.obj X} {b : F.obj Y ≅ G.obj Y} {c : F.obj Z ≅ G.obj Z}
    (h : ComparisonSquare F G f a b) (k : ComparisonSquare F G g b c) :
    ComparisonSquare F G (f ≫ g) a c := by
  dsimp only [ComparisonSquare] at *
  rw [F.map_comp, G.map_comp, Category.assoc, k, ← Category.assoc, h, Category.assoc]

omit [MonoidalCategory D] [SymmetricCategory D] in
private theorem ComparisonSquare.id {E : Type*} [Category E] (F G : E ⥤ D)
    {X : E} (a : F.obj X ≅ G.obj X) : ComparisonSquare F G (𝟙 X) a a := by
  simp [ComparisonSquare]

omit [MonoidalCategory D] [SymmetricCategory D] in
private theorem ComparisonSquare.inverse {E : Type*} [Category E] {F G : E ⥤ D}
    {X Y : E} (e : X ≅ Y) {a : F.obj X ≅ G.obj X} {b : F.obj Y ≅ G.obj Y}
    (h : ComparisonSquare F G e.hom a b) : ComparisonSquare F G e.inv b a := by
  dsimp only [ComparisonSquare] at *
  rw [← cancel_epi (F.map e.hom), ← cancel_mono (G.map e.hom)]
  simp only [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp,
    Category.assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id, h]

omit [SymmetricCategory D] in
private theorem ComparisonSquare.tensor {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal]
    {X Y X' Y' : E} {f : X ⟶ Y} {g : X' ⟶ Y'}
    {a : F.obj X ≅ G.obj X} {b : F.obj Y ≅ G.obj Y}
    {a' : F.obj X' ≅ G.obj X'} {b' : F.obj Y' ≅ G.obj Y'}
    (h : ComparisonSquare F G f a b) (k : ComparisonSquare F G g a' b') :
    ComparisonSquare F G (f ⊗ₘ g) (tensorComparison F G a a')
      (tensorComparison F G b b') := by
  dsimp only [ComparisonSquare] at h k ⊢
  simp only [tensorComparison, Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom,
    tensorIso_hom, map_tensor, Category.assoc, μ_δ_assoc]
  rw [tensorHom_comp_tensorHom_assoc, h, k, ← tensorHom_comp_tensorHom_assoc]

omit [SymmetricCategory D] in
private theorem ComparisonSquare.associator {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X Y Z : E}
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y) (c : F.obj Z ≅ G.obj Z) :
    ComparisonSquare F G (α_ X Y Z).hom
      (tensorComparison F G (tensorComparison F G a b) c)
      (tensorComparison F G a (tensorComparison F G b c)) := by
  dsimp only [ComparisonSquare, tensorComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, tensorIso_hom,
    map_associator, Category.assoc, μ_δ_assoc, tensorHom_def,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight]
  simp only [whiskerRight_μ_δ_assoc, whiskerLeft_μ_δ_assoc,
    whisker_exchange_assoc]
  monoidal

omit [SymmetricCategory D] in
private theorem ComparisonSquare.leftUnitor {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X : E} (a : F.obj X ≅ G.obj X) :
    ComparisonSquare F G (λ_ X).hom (tensorComparison F G (unitComparison F G) a) a := by
  dsimp only [ComparisonSquare, tensorComparison, unitComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, εIso_inv, εIso_hom,
    tensorIso_hom, map_leftUnitor, Category.assoc, μ_δ_assoc, tensorHom_def,
    MonoidalCategory.comp_whiskerRight]
  simp only [← MonoidalCategory.whisker_exchange_assoc,
    whiskerRight_ε_η_assoc]
  simp only [← leftUnitor_naturality, MonoidalCategory.whisker_exchange_assoc]

omit [SymmetricCategory D] in
private theorem ComparisonSquare.rightUnitor {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X : E} (a : F.obj X ≅ G.obj X) :
    ComparisonSquare F G (ρ_ X).hom (tensorComparison F G a (unitComparison F G)) a := by
  dsimp only [ComparisonSquare, tensorComparison, unitComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, εIso_inv, εIso_hom,
    tensorIso_hom, map_rightUnitor, Category.assoc, μ_δ_assoc, tensorHom_def',
    MonoidalCategory.whiskerLeft_comp]
  simp only [MonoidalCategory.whisker_exchange_assoc,
    whiskerLeft_ε_η_assoc]
  simp only [← rightUnitor_naturality, ← MonoidalCategory.whisker_exchange_assoc]

private theorem ComparisonSquare.braiding {E : Type*} [Category E] [MonoidalCategory E]
    [SymmetricCategory E] (F G : E ⥤ D) [F.Braided] [G.Braided] {X Y : E}
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y) :
    ComparisonSquare F G (β_ X Y).hom (tensorComparison F G a b)
      (tensorComparison F G b a) := by
  simp only [ComparisonSquare, tensorComparison, Iso.trans_hom, Iso.symm_hom,
    μIso_inv, μIso_hom, tensorIso_hom, Functor.map_braiding, Category.assoc, μ_δ_assoc,
    BraidedCategory.braiding_naturality_assoc]

omit [SymmetricCategory D] in
private theorem ComparisonSquare.whiskerLeft {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] {X Y Z : E} {f : Y ⟶ Z}
    (a : F.obj X ≅ G.obj X) {b : F.obj Y ≅ G.obj Y} {c : F.obj Z ≅ G.obj Z}
    (h : ComparisonSquare F G f b c) :
    ComparisonSquare F G (X ◁ f) (tensorComparison F G a b) (tensorComparison F G a c) := by
  simpa only [id_tensorHom] using (ComparisonSquare.id F G a).tensor h

omit [SymmetricCategory D] in
private theorem ComparisonSquare.whiskerRight {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] {X Y Z : E} {f : X ⟶ Y}
    {a : F.obj X ≅ G.obj X} {b : F.obj Y ≅ G.obj Y} (c : F.obj Z ≅ G.obj Z)
    (h : ComparisonSquare F G f a b) :
    ComparisonSquare F G (f ▷ Z) (tensorComparison F G a c) (tensorComparison F G b c) := by
  simpa only [tensorHom_id] using h.tensor (ComparisonSquare.id F G c)

omit [SymmetricCategory D] in
private theorem ComparisonSquare.coevaluation {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : E} [ExactPairing X Y]
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y)
    (h : (ExactPairing.map F X Y).coevaluation' ≫ (a.hom ⊗ₘ b.hom) =
      (ExactPairing.map G X Y).coevaluation') :
    ComparisonSquare F G (η_ X Y) (unitComparison F G) (tensorComparison F G a b) := by
  dsimp only [ComparisonSquare, tensorComparison, unitComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, εIso_inv, εIso_hom,
    tensorIso_hom]
  rw [← cancel_epi (ε F), ← cancel_mono (δ G X Y)]
  change (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫ _ =
    ε G ≫ G.map (η_ X Y) ≫ δ G X Y at h
  simpa only [Category.assoc, μ_δ, Category.comp_id, ε_η_assoc] using h

omit [SymmetricCategory D] in
private theorem ComparisonSquare.evaluation {E : Type*} [Category E] [MonoidalCategory E]
    (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : E} [ExactPairing X Y]
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y)
    (h : (b.hom ⊗ₘ a.hom) ≫ (ExactPairing.map G X Y).evaluation' =
      (ExactPairing.map F X Y).evaluation') :
    ComparisonSquare F G (ε_ X Y) (tensorComparison F G b a) (unitComparison F G) := by
  dsimp only [ComparisonSquare, tensorComparison, unitComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, εIso_inv, εIso_hom,
    tensorIso_hom]
  rw [← cancel_epi (μ F Y X), ← cancel_mono (η G)]
  change _ ≫ (μ G Y X ≫ G.map (ε_ X Y) ≫ η G) =
    μ F Y X ≫ F.map (ε_ X Y) ≫ η F at h
  simpa only [Category.assoc, μ_δ_assoc, ε_η, Category.comp_id] using h.symm

omit [SymmetricCategory D] in
private theorem ComparisonSquare.rightMate {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] {X Y Y' Z : E} [ExactPairing Y Y']
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y)
    (b' : F.obj Y' ≅ G.obj Y') (c : F.obj Z ≅ G.obj Z)
    (hη : ComparisonSquare F G (η_ Y Y') (unitComparison F G) (tensorComparison F G b b'))
    {f : X ⊗ Y ⟶ Z} (hf : ComparisonSquare F G f (tensorComparison F G a b) c) :
    ComparisonSquare F G (tensorRightHomEquiv X Y Y' Z f) a (tensorComparison F G c b') := by
  exact ((ComparisonSquare.rightUnitor F G a).inverse (ρ_ X)).comp
    ((hη.whiskerLeft a).comp
      (((ComparisonSquare.associator F G a b b').inverse (α_ X Y Y')).comp
        (hf.whiskerRight b')))

omit [SymmetricCategory D] in
private theorem ComparisonSquare.leftMateInv {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] {X Y Y' Z : E} [ExactPairing Y Y']
    (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y)
    (b' : F.obj Y' ≅ G.obj Y') (c : F.obj Z ≅ G.obj Z)
    (hε : ComparisonSquare F G (ε_ Y Y') (tensorComparison F G b' b) (unitComparison F G))
    {f : X ⟶ Y ⊗ Z} (hf : ComparisonSquare F G f a (tensorComparison F G b c)) :
    ComparisonSquare F G ((tensorLeftHomEquiv X Y Y' Z).symm f)
      (tensorComparison F G b' a) c := by
  exact (hf.whiskerLeft b').comp
    (((ComparisonSquare.associator F G b' b c).inverse (α_ Y' Y Z)).comp
      ((hε.whiskerRight c).comp (ComparisonSquare.leftUnitor F G c)))

omit [SymmetricCategory D] in
private theorem ComparisonSquare.coevaluation_of_square {E : Type*} [Category E]
    [MonoidalCategory E] (F G : E ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : E}
    [ExactPairing X Y] (a : F.obj X ≅ G.obj X) (b : F.obj Y ≅ G.obj Y)
    (h : ComparisonSquare F G (η_ X Y) (unitComparison F G) (tensorComparison F G a b)) :
    (ExactPairing.map F X Y).coevaluation' ≫ (a.hom ⊗ₘ b.hom) =
      (ExactPairing.map G X Y).coevaluation' := by
  have h' := congrArg (fun f => ε F ≫ f ≫ δ G X Y) h
  change (ε F ≫ F.map (η_ X Y) ≫ δ F X Y) ≫ _ =
    ε G ≫ G.map (η_ X Y) ≫ δ G X Y
  simpa only [tensorComparison, unitComparison, Iso.trans_hom, Iso.symm_hom,
    μIso_inv, μIso_hom, εIso_inv, εIso_hom, tensorIso_hom, Category.assoc,
    μ_δ, Category.comp_id, ε_η_assoc] using h'

omit [MonoidalCategory D] [SymmetricCategory D] in
private theorem ComparisonSquare.source {E : Type*} [Category E] {F G : E ⥤ D}
    (e : F ≅ G) {X Y : E} (f : X ≅ Y)
    {a : F.obj X ≅ G.obj X} {b : F.obj Y ≅ G.obj Y}
    (h : ComparisonSquare F G f.hom a b) (hb : e.app Y = b) : e.app X = a := by
  apply Iso.ext
  apply (cancel_mono (G.map f.hom)).1
  have hn := e.hom.naturality f.hom
  change F.map f.hom ≫ (e.app Y).hom = (e.app X).hom ≫ G.map f.hom at hn
  rw [hb] at hn
  exact hn.symm.trans h

omit [SymmetricCategory D] in
private theorem tensorComparison_left_dual {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    {P N : E} [ExactPairing P N]
    (hε : ComparisonSquare F G (ε_ P N)
      (tensorComparison F G (e.app N) (e.app P)) (unitComparison F G))
    (Y : E) (hP : e.app (P ⊗ (N ⊗ Y)) =
      tensorComparison F G (e.app P) (e.app (N ⊗ Y))) :
    e.app (N ⊗ Y) = tensorComparison F G (e.app N) (e.app Y) := by
  let l := tensorLeftHomEquiv Y P N (N ⊗ Y) (𝟙 (N ⊗ Y))
  have hl : ComparisonSquare F G l (e.app Y)
      (tensorComparison F G (e.app P) (e.app (N ⊗ Y))) := by
    have hn := e.hom.naturality l
    change F.map l ≫ (e.app (P ⊗ (N ⊗ Y))).hom = (e.app Y).hom ≫ G.map l at hn
    rw [hP] at hn
    exact hn
  have h := ComparisonSquare.leftMateInv (e.app Y) (e.app P) (e.app N)
    (e.app (N ⊗ Y)) hε hl
  dsimp only [l] at h
  rw [Equiv.symm_apply_apply] at h
  apply Iso.ext
  simpa only [ComparisonSquare, Functor.map_id, Category.id_comp, Category.comp_id] using h

omit [SymmetricCategory D] in
private theorem tensorComparison_tensor_left {E : Type*} [Category E] [MonoidalCategory E]
    {F G : E ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G) {X Y Z : E}
    (hXY : e.app (X ⊗ Y) = tensorComparison F G (e.app X) (e.app Y))
    (hYZ : e.app (Y ⊗ Z) = tensorComparison F G (e.app Y) (e.app Z))
    (hX : e.app (X ⊗ (Y ⊗ Z)) = tensorComparison F G (e.app X) (e.app (Y ⊗ Z))) :
    e.app ((X ⊗ Y) ⊗ Z) = tensorComparison F G (e.app (X ⊗ Y)) (e.app Z) := by
  rw [hXY]
  exact (ComparisonSquare.associator F G (e.app X) (e.app Y) (e.app Z)).source
    e (α_ X Y Z) (hX.trans (congrArg (tensorComparison F G (e.app X)) hYZ))

namespace IntConstruction
variable (T : SymmetricTrace C) (K L : IntConstruction T ⥤ D) [K.Braided] [L.Braided]

/-- The image under a monoidal functor of Int's named positive/negative pairing. -/
@[instance_reducible]
def mappedPositivePairing (A : C) :
    ExactPairing (K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T))
      (K.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) := by
  let _ := positivePairing T A
  exact ExactPairing.map K (⟨A, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, A⟩

variable (i : embedding T ⋙ K ≅ embedding T ⋙ L)

/-- The negative component is the canonical comparison of the mapped elementary pairings. -/
def negativeComparison (A : C) :
    K.obj (⟨𝟙_ C, A⟩ : IntConstruction T) ≅ L.obj (⟨𝟙_ C, A⟩ : IntConstruction T) := by
  let _ : ExactPairing ((embedding T ⋙ L).obj A)
      (L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) := mappedPositivePairing T L A
  exact rightDualIso (mappedPositivePairing T K A)
    (exactPairingCongrLeft (Y := L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) (i.app A))

/-- Positive and negative comparisons together preserve the mapped cup. -/
theorem negativeComparison_coevaluation (A : C) :
    (mappedPositivePairing T K A).coevaluation' ≫
      (i.hom.app A ⊗ₘ (negativeComparison T K L i A).hom) =
        (mappedPositivePairing T L A).coevaluation' := by
  let _ : ExactPairing ((embedding T ⋙ L).obj A)
      (L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) := mappedPositivePairing T L A
  have h := coevaluation_comp_rightDualIso (mappedPositivePairing T K A)
    (exactPairingCongrLeft (Y := L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) (i.app A))
  change (mappedPositivePairing T K A).coevaluation' ≫
    K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T) ◁ (negativeComparison T K L i A).hom =
      (mappedPositivePairing T L A).coevaluation' ≫
        i.inv.app A ▷ L.obj (⟨𝟙_ C, A⟩ : IntConstruction T) at h
  dsimp only [Functor.comp_obj, embedding] at *
  rw [tensorHom_def', ← Category.assoc, h]
  have hi := i.inv_hom_id_app A
  dsimp only [Functor.comp_obj, embedding] at hi
  simp only [Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    hi, id_whiskerRight, Category.comp_id]

/-- Positive and negative comparisons together preserve the mapped cap. -/
theorem negativeComparison_evaluation (A : C) :
    ((negativeComparison T K L i A).hom ⊗ₘ i.hom.app A) ≫
      (mappedPositivePairing T L A).evaluation' =
        (mappedPositivePairing T K A).evaluation' := by
  let _ : ExactPairing ((embedding T ⋙ L).obj A)
      (L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) := mappedPositivePairing T L A
  have h := rightDualIso_comp_evaluation (mappedPositivePairing T K A)
    (exactPairingCongrLeft (Y := L.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) (i.app A))
  change (negativeComparison T K L i A).hom ▷
      K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T) ≫
    L.obj (⟨𝟙_ C, A⟩ : IntConstruction T) ◁ i.hom.app A ≫
      (mappedPositivePairing T L A).evaluation' = _ at h
  dsimp only [Functor.comp_obj, embedding] at *
  simpa only [tensorHom_def, Category.assoc] using h

/-- The candidate comparison on an arbitrary positive/negative pair. -/
def comparisonComponent (X : IntConstruction T) : K.obj X ≅ L.obj X :=
  K.mapIso (decomposition T X) ≪≫
    (μIso K (⟨X.positive, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, X.negative⟩).symm ≪≫
      (i.app X.positive ⊗ᵢ negativeComparison T K L i X.negative) ≪≫
        μIso L (⟨X.positive, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, X.negative⟩ ≪≫
          L.mapIso (decomposition T X).symm

private theorem negativeComparison_unique (A : C)
    (b : K.obj (⟨𝟙_ C, A⟩ : IntConstruction T) ⟶ L.obj (⟨𝟙_ C, A⟩ : IntConstruction T))
    (h : (mappedPositivePairing T K A).coevaluation' ≫ (i.hom.app A ⊗ₘ b) =
      (mappedPositivePairing T L A).coevaluation') : b = (negativeComparison T K L i A).hom := by
  let _ := mappedPositivePairing T K A
  have he := h.trans (negativeComparison_coevaluation T K L i A).symm
  let a : K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T) ≅
      L.obj (⟨A, 𝟙_ C⟩ : IntConstruction T) := i.app A
  change (mappedPositivePairing T K A).coevaluation' ≫ (a.hom ⊗ₘ b) =
    (mappedPositivePairing T K A).coevaluation' ≫
      (a.hom ⊗ₘ (negativeComparison T K L i A).hom) at he
  simp only [tensorHom_def', ← Category.assoc, cancel_mono] at he
  change η_ (K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T))
      (K.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) ≫ _ ◁ b =
    η_ (K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T))
      (K.obj (⟨𝟙_ C, A⟩ : IntConstruction T)) ≫ _ ◁ (negativeComparison T K L i A).hom at he
  have hm := congrArg (tensorLeftHomEquiv (𝟙_ D)
    (K.obj (⟨A, 𝟙_ C⟩ : IntConstruction T))
    (K.obj (⟨𝟙_ C, A⟩ : IntConstruction T))
    (L.obj (⟨𝟙_ C, A⟩ : IntConstruction T))).symm he
  simpa only [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft, cancel_epi] using hm

variable [NatTrans.IsMonoidal i.hom]

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_positive_unit : i.app (𝟙_ C) = unitComparison K L := by
  apply Iso.ext
  have h := NatTrans.IsMonoidal.unit (τ := i.hom)
  change (ε K ≫ K.map (ε (embedding T))) ≫ i.hom.app (𝟙_ C) =
    ε L ≫ L.map (ε (embedding T)) at h
  rw [embedding_ε] at h
  erw [mapPair_id T (𝟙_ (IntConstruction T))] at h
  simp only [Functor.map_id, Category.comp_id] at h
  dsimp only [unitComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, εIso_inv, εIso_hom, Iso.app_hom]
  dsimp only [Functor.comp_obj, embedding] at *
  rw [← cancel_epi (ε K)]
  simpa only [Category.assoc, ε_η_assoc] using h

private theorem positivePairing_unit_coevaluation :
    (positivePairing T (𝟙_ C)).coevaluation' = (λ_ (𝟙_ (IntConstruction T))).inv := by
  apply hom_ext T
  change (λ_ ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv =
    (λ_ (𝟙_ C)).inv ⊗ₘ (ρ_ (𝟙_ C)).hom
  monoidal

private theorem comparison_negative_unit : negativeComparison T K L i (𝟙_ C) =
    unitComparison K L := by
  apply Iso.ext
  symm
  apply negativeComparison_unique T K L i (𝟙_ C)
  let _ := positivePairing T (𝟙_ C)
  have h := ComparisonSquare.coevaluation_of_square K L (unitComparison K L)
    (unitComparison K L)
    (show ComparisonSquare K L (η_ (𝟙_ (IntConstruction T)) (𝟙_ (IntConstruction T)))
      (unitComparison K L) (tensorComparison K L (unitComparison K L) (unitComparison K L)) by
        change ComparisonSquare K L (positivePairing T (𝟙_ C)).coevaluation' _ _
        rw [positivePairing_unit_coevaluation]
        exact (ComparisonSquare.leftUnitor K L (unitComparison K L)).inverse (λ_ _))
  change (mappedPositivePairing T K (𝟙_ C)).coevaluation' ≫
    ((unitComparison K L).hom ⊗ₘ (unitComparison K L).hom) = _ at h
  change (mappedPositivePairing T K (𝟙_ C)).coevaluation' ≫
    ((i.app (𝟙_ C)).hom ⊗ₘ (unitComparison K L).hom) = _
  rw [comparison_positive_unit]
  exact h

private theorem comparison_embedding_tensor (A B : C) :
    ComparisonSquare K L (μ (embedding T) A B)
      (tensorComparison K L (i.app A) (i.app B)) (i.app (A ⊗ B)) := by
  dsimp only [ComparisonSquare, tensorComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, μIso_inv, μIso_hom, tensorIso_hom]
  rw [← cancel_epi (μ K ((embedding T).obj A) ((embedding T).obj B))]
  have h := NatTrans.IsMonoidal.tensor (τ := i.hom) A B
  change (μ K _ _ ≫ K.map (μ (embedding T) A B)) ≫ i.hom.app (A ⊗ B) =
    (i.hom.app A ⊗ₘ i.hom.app B) ≫ μ L _ _ ≫ L.map (μ (embedding T) A B) at h
  simpa only [Category.assoc, μ_δ_assoc, Iso.app_hom] using h

private theorem comparison_embedded_cross {P V B U : C} (f : P ⊗ V ⟶ B ⊗ U) :
    ComparisonSquare K L
      (μ (embedding T) P V ≫ (embedding T).map f ≫ δ (embedding T) B U)
      (tensorComparison K L (i.app P) (i.app V))
      (tensorComparison K L (i.app B) (i.app U)) := by
  exact (comparison_embedding_tensor T K L i P V).comp
    ((show ComparisonSquare K L ((embedding T).map f) (i.app (P ⊗ V))
      (i.app (B ⊗ U)) from i.hom.naturality f).comp
      ((comparison_embedding_tensor T K L i B U).inverse (μIso (embedding T) B U)))

omit [NatTrans.IsMonoidal i.hom] in
private theorem comparison_decomposition (X : IntConstruction T) :
    ComparisonSquare K L (decomposition T X).hom (comparisonComponent T K L i X)
      (tensorComparison K L (i.app X.positive) (negativeComparison T K L i X.negative)) := by
  dsimp only [ComparisonSquare, comparisonComponent, tensorComparison, Functor.comp_obj, embedding]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, ← L.map_comp, Iso.inv_hom_id, L.map_id, Category.comp_id]

/-- The comparison components commute with every Int morphism. -/
theorem comparisonComponent_naturality {X Y : IntConstruction T} (f : X ⟶ Y) :
    K.map f ≫ (comparisonComponent T K L i Y).hom =
      (comparisonComponent T K L i X).hom ≫ L.map f := by
  let p (A : C) : IntConstruction T := ⟨A, 𝟙_ C⟩
  let n (A : C) : IntConstruction T := ⟨𝟙_ C, A⟩
  let a (A : C) : K.obj (p A) ≅ L.obj (p A) := i.app A
  let b (A : C) : K.obj (n A) ≅ L.obj (n A) := negativeComparison T K L i A
  let _ : ExactPairing (p X.negative) (n X.negative) := positivePairing T X.negative
  let _ : ExactPairing (p Y.negative) (n Y.negative) := positivePairing T Y.negative
  have hη : ComparisonSquare K L (η_ (p Y.negative) (n Y.negative))
      (unitComparison K L) (tensorComparison K L (a Y.negative) (b Y.negative)) :=
    ComparisonSquare.coevaluation K L (a _) (b _) (negativeComparison_coevaluation T K L i _)
  have hε : ComparisonSquare K L (ε_ (p X.negative) (n X.negative))
      (tensorComparison K L (b X.negative) (a X.negative)) (unitComparison K L) :=
    ComparisonSquare.evaluation K L (a _) (b _) (negativeComparison_evaluation T K L i _)
  have hg := comparison_embedded_cross T K L i (hom T f)
  have hr := ComparisonSquare.rightMate (a X.positive) (a Y.negative) (b Y.negative)
    (tensorComparison K L (a Y.positive) (a X.negative)) hη hg
  have hb := (ComparisonSquare.braiding K L (a Y.positive) (a X.negative)).whiskerRight
    (b Y.negative)
  have ha := ComparisonSquare.associator K L (a X.negative) (a Y.positive) (b Y.negative)
  have hl := ComparisonSquare.leftMateInv (a X.positive) (a X.negative) (b X.negative)
    (tensorComparison K L (a Y.positive) (b Y.negative)) hε (hr.comp (hb.comp ha))
  have h := (comparison_decomposition T K L i X).comp
    ((ComparisonSquare.braiding K L (a X.positive) (b X.negative)).comp
      (hl.comp ((comparison_decomposition T K L i Y).inverse (decomposition T Y))))
  change ComparisonSquare K L (reconstruct T (hom T f))
    (comparisonComponent T K L i X) (comparisonComponent T K L i Y) at h
  simpa only [reconstruct_hom, ComparisonSquare] using h

/-- An isomorphism between monoidal restrictions extends naturally across Int morphisms. -/
def restrictionLift : K ≅ L :=
  NatIso.ofComponents (comparisonComponent T K L i)
    (fun f => comparisonComponent_naturality T K L i f)

private theorem decomposition_positive (A : C) :
    decomposition T ((embedding T).obj A) = (ρ_ ((embedding T).obj A)).symm := by
  apply Iso.ext
  apply hom_ext T
  change (ρ_ A).inv ⊗ₘ (ρ_ (𝟙_ C)).hom = (ρ_ A).inv ⊗ₘ (λ_ (𝟙_ C)).hom
  rw [unitors_equal]

private theorem decomposition_negative (A : C) :
    decomposition T (⟨𝟙_ C, A⟩ : IntConstruction T) =
      (λ_ (⟨𝟙_ C, A⟩ : IntConstruction T)).symm := by
  apply Iso.ext
  apply hom_ext T
  change (ρ_ (𝟙_ C)).inv ⊗ₘ (ρ_ A).hom = (λ_ (𝟙_ C)).inv ⊗ₘ (ρ_ A).hom
  rw [unitors_inv_equal]

/-- The lifted comparison restricts to the supplied positive components. -/
theorem restrictionLift_positive (A : C) :
    (restrictionLift T K L i).app ((embedding T).obj A) = i.app A := by
  apply Iso.ext
  have hd := comparison_decomposition T K L i ((embedding T).obj A)
  have hu := (ComparisonSquare.rightUnitor K L (i.app A)).inverse (ρ_ ((embedding T).obj A))
  dsimp only [embedding] at hd
  rw [comparison_negative_unit] at hd
  have hp := congrArg Iso.hom (decomposition_positive T A)
  erw [hp] at hd
  apply (cancel_mono (L.map (ρ_ ((embedding T).obj A)).inv)).1
  exact hd.symm.trans hu

/-- The lifted comparison on a negative object is the canonical dual comparison. -/
theorem restrictionLift_negative (A : C) :
    (restrictionLift T K L i).app (⟨𝟙_ C, A⟩ : IntConstruction T) =
      negativeComparison T K L i A := by
  apply Iso.ext
  have hd := comparison_decomposition T K L i (⟨𝟙_ C, A⟩ : IntConstruction T)
  have hu := (ComparisonSquare.leftUnitor K L (negativeComparison T K L i A)).inverse
    (λ_ (⟨𝟙_ C, A⟩ : IntConstruction T))
  rw [comparison_positive_unit, decomposition_negative] at hd
  apply (cancel_mono (L.map (λ_ (⟨𝟙_ C, A⟩ : IntConstruction T)).inv)).1
  exact hd.symm.trans hu

/-- The lifted comparison respects the tensor unit. -/
private theorem restrictionLift_unit :
    (restrictionLift T K L i).app (𝟙_ (IntConstruction T)) = unitComparison K L :=
  (restrictionLift_positive T K L i (𝟙_ C)).trans (comparison_positive_unit T K L i)

private theorem restrictionLift_mixed (A B : C) :
    (restrictionLift T K L i).app
      ((⟨A, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, B⟩) =
        tensorComparison K L (i.app A) (negativeComparison T K L i B) := by
  apply Iso.ext
  apply (cancel_epi (K.map (decomposition T (⟨A, B⟩ : IntConstruction T)).hom)).1
  exact ((restrictionLift T K L i).hom.naturality
    (decomposition T (⟨A, B⟩ : IntConstruction T)).hom).trans
      (comparison_decomposition T K L i (⟨A, B⟩ : IntConstruction T)).symm

private theorem restrictionLift_positive_tensor (A : C) (Y : IntConstruction T) :
    (restrictionLift T K L i).app (((embedding T).obj A) ⊗ Y) =
      tensorComparison K L ((restrictionLift T K L i).app ((embedding T).obj A))
        ((restrictionLift T K L i).app Y) := by
  let e := restrictionLift T K L i
  let p (A : C) : IntConstruction T := ⟨A, 𝟙_ C⟩
  let n (A : C) : IntConstruction T := ⟨𝟙_ C, A⟩
  let b := negativeComparison T K L i Y.negative
  have hφ := ((ComparisonSquare.associator K L (i.app A) (i.app Y.positive) b).inverse
    (α_ (p A) (p Y.positive) (n Y.negative))).comp
      ((comparison_embedding_tensor T K L i A Y.positive).whiskerRight b)
  have hmid : e.app (p A ⊗ (p Y.positive ⊗ n Y.negative)) =
      tensorComparison K L (i.app A) (tensorComparison K L (i.app Y.positive) b) :=
    hφ.source e ((α_ (p A) (p Y.positive) (n Y.negative)).symm ≪≫
      (μIso (embedding T) A Y.positive) ▷ᵢ n Y.negative)
      (restrictionLift_mixed T K L i (A ⊗ Y.positive) Y.negative)
  have hd := ComparisonSquare.whiskerLeft (F := K) (G := L) (X := (embedding T).obj A)
    (i.app A) (comparison_decomposition T K L i Y)
  rw [restrictionLift_positive]
  exact hd.source e ((p A) ◁ᵢ decomposition T Y) hmid

private theorem restrictionLift_negative_tensor (A : C) (Y : IntConstruction T) :
    (restrictionLift T K L i).app ((⟨𝟙_ C, A⟩ : IntConstruction T) ⊗ Y) =
      tensorComparison K L ((restrictionLift T K L i).app (⟨𝟙_ C, A⟩ : IntConstruction T))
        ((restrictionLift T K L i).app Y) := by
  let _ : ExactPairing ((embedding T).obj A)
      (⟨𝟙_ C, A⟩ : IntConstruction T) := positivePairing T A
  apply tensorComparison_left_dual (restrictionLift T K L i) (P := (embedding T).obj A)
  · rw [restrictionLift_positive, restrictionLift_negative]
    exact ComparisonSquare.evaluation K L (i.app A) (negativeComparison T K L i A)
      (negativeComparison_evaluation T K L i A)
  · exact restrictionLift_positive_tensor T K L i A _

private theorem restrictionLift_tensor (X Y : IntConstruction T) :
    (restrictionLift T K L i).app (X ⊗ Y) =
      tensorComparison K L ((restrictionLift T K L i).app X) ((restrictionLift T K L i).app Y) := by
  let e := restrictionLift T K L i
  have ht := tensorComparison_tensor_left e
    (restrictionLift_positive_tensor T K L i X.positive (⟨𝟙_ C, X.negative⟩ : IntConstruction T))
    (restrictionLift_negative_tensor T K L i X.negative Y)
    (restrictionLift_positive_tensor T K L i X.positive _)
  have hd : ComparisonSquare K L (decomposition T X).hom (e.app X)
      (e.app ((⟨X.positive, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, X.negative⟩)) :=
    e.hom.naturality (decomposition T X).hom
  exact (hd.whiskerRight (e.app Y)).source e ((decomposition T X) ▷ᵢ Y) ht

/-- The comparison obtained from a monoidal restriction is itself monoidal. -/
instance restrictionLift_isMonoidal : NatTrans.IsMonoidal (restrictionLift T K L i).hom where
  unit := by
    have h := congrArg Iso.hom (restrictionLift_unit T K L i)
    change (restrictionLift T K L i).hom.app (𝟙_ (IntConstruction T)) = η K ≫ ε L at h
    simp only [h, ε_η_assoc]
  tensor X Y := by
    have h := congrArg Iso.hom (restrictionLift_tensor T K L i X Y)
    change (restrictionLift T K L i).hom.app (X ⊗ Y) =
      δ K X Y ≫ ((restrictionLift T K L i).hom.app X ⊗ₘ
        (restrictionLift T K L i).hom.app Y) ≫ μ L X Y at h
    simp only [h, μ_δ_assoc]

/-- Restriction of the lifted isomorphism is exactly the supplied isomorphism. -/
@[simp] theorem restrictionLift_restrict :
    Functor.isoWhiskerLeft (embedding T) (restrictionLift T K L i) = i := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact congrArg Iso.hom (restrictionLift_positive T K L i A)

/-- A monoidal isomorphism with the specified restriction is unique. -/
theorem restrictionLift_unique (e : K ≅ L) [NatTrans.IsMonoidal e.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e = i) : e = restrictionLift T K L i :=
  monoidalIso_eq_of_whiskerLeft_eq T e (restrictionLift T K L i)
    (h.trans (restrictionLift_restrict T K L i).symm)

/-- Restriction is full and faithful on monoidal natural isomorphisms. -/
theorem existsUnique_restrictionLift : ∃! e : K ≅ L,
    NatTrans.IsMonoidal e.hom ∧ Functor.isoWhiskerLeft (embedding T) e = i := by
  refine ⟨restrictionLift T K L i, ⟨inferInstance, restrictionLift_restrict T K L i⟩, ?_⟩
  intro e he
  let _ := he.1
  exact restrictionLift_unique T K L i e he.2

section RigidTarget
variable [RightRigidCategory D]
variable (F : C ⥤ D) [F.Braided] (hF : T.Preserves (symmetricTraceOfRigid D) F)
  (σ : embedding T ⋙ K ≅ F) [NatTrans.IsMonoidal σ.hom]

local instance : NatTrans.IsMonoidal (σ ≪≫ (extensionIso T F hF).symm).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (σ.hom ≫ (extensionIso T F hF).inv))

/-- Compare any braided monoidal extension with the canonical extension of a traced functor. -/
def extensionComparison : K ≅ extend T F hF :=
  restrictionLift T K (extend T F hF) (σ ≪≫ (extensionIso T F hF).symm)

/-- The universal comparison respects tensor products and the unit. -/
instance extensionComparison_isMonoidal :
    NatTrans.IsMonoidal (extensionComparison T K F hF σ).hom :=
  inferInstanceAs (NatTrans.IsMonoidal
    (restrictionLift T K (extend T F hF) (σ ≪≫ (extensionIso T F hF).symm)).hom)

/-- The comparison is compatible with the specified factorization through the embedding. -/
@[simp] theorem extensionComparison_compatible :
    Functor.isoWhiskerLeft (embedding T) (extensionComparison T K F hF σ) ≪≫
      extensionIso T F hF = σ := by
  simp only [extensionComparison, restrictionLift_restrict, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

/-- Any compatible monoidal comparison with the canonical extension is the universal one. -/
theorem extensionComparison_unique (e : K ≅ extend T F hF) [NatTrans.IsMonoidal e.hom]
    (h : Functor.isoWhiskerLeft (embedding T) e ≪≫ extensionIso T F hF = σ) :
    e = extensionComparison T K F hF σ := by
  apply restrictionLift_unique T K (extend T F hF) (σ ≪≫ (extensionIso T F hF).symm) e
  have he := congrArg (fun j => j ≪≫ (extensionIso T F hF).symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using he

/-- Every specified monoidal factorization has a unique compatible monoidal comparison. -/
theorem existsUnique_extensionComparison : ∃! e : K ≅ extend T F hF,
    NatTrans.IsMonoidal e.hom ∧
      Functor.isoWhiskerLeft (embedding T) e ≪≫ extensionIso T F hF = σ := by
  refine ⟨extensionComparison T K F hF σ,
    ⟨inferInstance, extensionComparison_compatible T K F hF σ⟩, ?_⟩
  intro e he
  let _ := he.1
  exact extensionComparison_unique T K F hF σ e he.2

local instance : NatTrans.IsMonoidal (Iso.refl (embedding T ⋙ K)).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 (embedding T ⋙ K)))

/-- Any braided monoidal functor out of Int into a right-rigid symmetric monoidal category is
the extension of its restriction, up to its canonical monoidal comparison. The source need not
have duals. -/
def universalComparison : K ≅ extend T (embedding T ⋙ K)
    (SymmetricTrace.Preserves.comp (embedding_preserves_trace T)
      (SymmetricTrace.preserves_of_rigid K)) :=
  extensionComparison T K (embedding T ⋙ K)
    (SymmetricTrace.Preserves.comp (embedding_preserves_trace T)
      (SymmetricTrace.preserves_of_rigid K)) (Iso.refl _)

/-- The canonical comparison with extension of the restriction is monoidal. -/
instance universalComparison_isMonoidal : NatTrans.IsMonoidal (universalComparison T K).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (extensionComparison T K (embedding T ⋙ K)
    (SymmetricTrace.Preserves.comp (embedding_preserves_trace T)
      (SymmetricTrace.preserves_of_rigid K)) (Iso.refl _)).hom)

end RigidTarget

end IntConstruction
end CategoryTheory

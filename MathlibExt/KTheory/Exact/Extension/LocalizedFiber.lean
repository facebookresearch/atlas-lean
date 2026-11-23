/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Fibered
public import MathlibExt.KTheory.Exact.Extension.Fiber
public import MathlibExt.CategoryTheory.ExactCategory.Biproduct
public import MathlibExt.CategoryTheory.ExactCategory.Zero
public import Mathlib.CategoryTheory.Core
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal
public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization

/-!
# Left addition on the original extension rows and quotient diagrams

The acting objects and morphisms are the original `Core C`. Adding `T` to
the kernel and middle of a row retains its given quotient. On an original
quotient diagram the core isomorphism acts inversely on the kernel and
middle-row inclusion and forwards on the middle map. The middle quotient
object and its two Quillen span legs are retained literally.

This provides the actual row and raw-arrow data for the cartesian direct-sum
action in Weibel IV.7.7 / Exercise IV.7.2. The maps descend through the
original quotient relation and give the
coherent core action below. No action or localization result is supplied
as a premise. Localization remains a subsequent step.
-/

@[expose] public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem biprod_map_admissible {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B')
    (hf : IsAdmissibleMono f) (hg : IsAdmissibleMono g) :
    IsAdmissibleMono (biprod.map f g) := by
  obtain ⟨Q, p, w, h⟩ := hf
  obtain ⟨Q', p', w', h'⟩ := hg
  exact isAdmissibleMono_f (isAdmissibleExact_biprod h h')

private theorem left_sum_exact (T : C) (S : ShortComplex C)
    (hS : IsAdmissibleExact S)
    (w : biprod.map (𝟙 T) S.f ≫ (biprod.snd ≫ S.g) = 0) :
    IsAdmissibleExact (ShortComplex.mk (biprod.map (𝟙 T) S.f)
      (biprod.snd ≫ S.g) w) := by
  let Z : ShortComplex C := ShortComplex.mk (𝟙 T) (0 : T ⟶ (0 : C)) (by simp)
  have hZ : IsAdmissibleExact Z := isAdmissibleExact_id_zero (isZero_zero C)
  let B := biprodShortComplex Z S
  let R : ShortComplex C :=
    ShortComplex.mk (biprod.map (𝟙 T) S.f) (biprod.snd ≫ S.g) w
  let e : B ≅ R :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (isoZeroBiprod (X := (0 : C)) (Y := S.X₃) (isZero_zero C)).symm
      (by simp [B, R, Z, biprodShortComplex])
      (by
        change (𝟙 _) ≫ (biprod.snd ≫ S.g) =
          biprod.map (0 : T ⟶ (0 : C)) S.g ≫ biprod.snd
        simp only [Category.id_comp, biprod.map_snd])
  exact isAdmissibleExact_of_iso e (isAdmissibleExact_biprod hZ hS)

private theorem twisted_left_sum_exact {T T' : C} (e : T ≅ T')
    (S : ShortComplex C) (hS : IsAdmissibleExact S)
    (w : biprod.map e.hom S.f ≫ (biprod.snd ≫ S.g) = 0) :
    IsAdmissibleExact (ShortComplex.mk (biprod.map e.hom S.f)
      (biprod.snd ≫ S.g) w) := by
  have wz : biprod.map (𝟙 T') S.f ≫ (biprod.snd ≫ S.g) = 0 := by
    rw [← Category.assoc, biprod.map_snd, Category.assoc, S.zero, comp_zero]
  let A : ShortComplex C :=
    ShortComplex.mk (biprod.map e.hom S.f) (biprod.snd ≫ S.g) w
  let B : ShortComplex C :=
    ShortComplex.mk (biprod.map (𝟙 T') S.f) (biprod.snd ≫ S.g) wz
  let φ : A ≅ B :=
    ShortComplex.isoMk (biprod.mapIso e (Iso.refl S.X₁)) (Iso.refl _) (Iso.refl _)
      (by
        change biprod.map e.hom (𝟙 S.X₁) ≫ biprod.map (𝟙 T') S.f =
          biprod.map e.hom S.f ≫ (𝟙 _)
        apply biprod.hom_ext <;> simp [Category.assoc])
      (by simp [A, B])
  exact isAdmissibleExact_of_iso φ.symm (left_sum_exact T' S hS wz)

namespace ExtensionCategory

/-- Add the original core object to the kernel and middle, retaining the given quotient. -/
def leftSumObj (T : Core C) (E : ExtensionCategory C) : ExtensionCategory C := by
  have w : biprod.map (𝟙 T.of) E.row.f ≫ (biprod.snd ≫ E.row.g) = 0 := by
    rw [← Category.assoc, biprod.map_snd, Category.assoc, E.row.zero, comp_zero]
  exact
    { row := ShortComplex.mk (biprod.map (𝟙 T.of) E.row.f) (biprod.snd ≫ E.row.g) w
      admissible := by exact left_sum_exact T.of E.row E.admissible w }

theorem leftSumObj_target (T : Core C) (E : ExtensionCategory C) :
    (target (C := C)).obj (leftSumObj T E) = (target (C := C)).obj E :=
  rfl

end ExtensionCategory

namespace ExtensionDiagram

/-- The direct-sum raw diagram keeps the actual quotient object and both span legs. -/
def leftSum {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    ExtensionDiagram (ExtensionCategory.leftSumObj T E')
      (ExtensionCategory.leftSumObj T' E) := by
  have w : biprod.map f.iso.inv d.j ≫ (biprod.snd ≫ d.q) = 0 := by
    rw [← Category.assoc, biprod.map_snd, Category.assoc, d.zero, comp_zero]
  exact
    { alpha := biprod.map f.iso.inv d.alpha
      alpha_admissible := by
        exact biprod_map_admissible _ _
          (IsAdmissibleMono.of_isIso f.iso.inv) d.alpha_admissible
      beta := biprod.map f.iso.hom d.beta
      beta_admissible := by
        exact biprod_map_admissible _ _
          (IsAdmissibleMono.of_isIso f.iso.hom) d.beta_admissible
      D := d.D
      j := biprod.map f.iso.inv d.j
      q := biprod.snd ≫ d.q
      zero := w
      admissible := by
        exact twisted_left_sum_exact f.iso.symm
          (ShortComplex.mk d.j d.q d.zero) d.admissible w
      lambda := d.lambda
      lambda_admissible := d.lambda_admissible
      mu := d.mu
      mu_admissible := d.mu_admissible
      j_eq := by
        apply biprod.hom_ext <;>
          simp [ExtensionCategory.leftSumObj, Category.assoc, d.j_eq]
      j_beta := by
        apply biprod.hom_ext <;>
          simp [ExtensionCategory.leftSumObj, Category.assoc, d.j_beta]
      q_lambda := by
        change (biprod.snd ≫ d.q) ≫ d.lambda = biprod.snd ≫ E'.row.g
        rw [Category.assoc, d.q_lambda]
      q_mu := by
        change (biprod.snd ≫ d.q) ≫ d.mu =
          biprod.map f.iso.hom d.beta ≫ (biprod.snd ≫ E.row.g)
        rw [← Category.assoc, biprod.map_snd, Category.assoc, Category.assoc, d.q_mu] }

theorem leftSum_alpha {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (leftSum f d).alpha = biprod.map f.iso.inv d.alpha :=
  rfl

theorem leftSum_beta {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (leftSum f d).beta = biprod.map f.iso.hom d.beta :=
  rfl

theorem leftSum_span {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (leftSum f d).toQuillenSpan = d.toQuillenSpan :=
  rfl

theorem leftSum_target {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (d : ExtensionDiagram E' E) :
    (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom (leftSum f d)) =
      (ExtensionCategory.target (C := C)).map (ExtensionCategory.mkHom d) := by
  rw [ExtensionCategory.target_map_mkHom, ExtensionCategory.target_map_mkHom, leftSum_span]
  rfl

theorem leftSum_rel {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} {d e : ExtensionDiagram E' E} (h : Rel d e) :
    Rel (leftSum f d) (leftSum f e) := by
  apply rel_of_components_eq
  · exact congrArg (biprod.map f.iso.inv) h.1
  · exact congrArg (biprod.map f.iso.hom) h.2.1

end ExtensionDiagram

end AlgebraicKTheory


namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem sum_hom_ext {E' E : ExtensionCategory C} (f g : E' ⟶ E)
    (ha : (homNormalization f).hom.1.unop.hom =
      (homNormalization g).hom.1.unop.hom)
    (hb : (homNormalization f).hom.2.hom = (homNormalization g).hom.2.hom) : f = g := by
  apply homNormalization.injective
  apply Functor.Elements.hom_ext
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    apply InducedWideCategory.Hom.ext
    exact ha
  · apply InducedWideCategory.Hom.ext
    exact hb

private theorem normalized_alpha_comp {E F G : ExtensionCategory C}
    (f : E ⟶ F) (g : F ⟶ G) :
    (homNormalization (f ≫ g)).hom.1.unop.hom =
      (homNormalization g).hom.1.unop.hom ≫ (homNormalization f).hom.1.unop.hom := by
  refine Quotient.inductionOn₂ f g ?_
  intro d e
  exact comp_alpha d e

private theorem normalized_beta_comp {E F G : ExtensionCategory C}
    (f : E ⟶ F) (g : F ⟶ G) :
    (homNormalization (f ≫ g)).hom.2.hom =
      (homNormalization f).hom.2.hom ≫ (homNormalization g).hom.2.hom := by
  refine Quotient.inductionOn₂ f g ?_
  intro d e
  exact comp_beta d e

private theorem normalized_beta_id (E : ExtensionCategory C) :
    (homNormalization (𝟙 E)).hom.2.hom = 𝟙 E.row.X₂ := by
  rw [homNormalization_id]
  rfl

private def originalMiddleMap {E F : ExtensionCategory C} (f : E ⟶ F) :
    E.row.X₂ ⟶ F.row.X₂ := (homNormalization f).hom.2.hom

private theorem originalMiddleMap_comp {E F G : ExtensionCategory C}
    (f : E ⟶ F) (g : F ⟶ G) :
    originalMiddleMap (f ≫ g) = originalMiddleMap f ≫ originalMiddleMap g :=
  normalized_beta_comp f g

private theorem originalMiddleMap_id (E : ExtensionCategory C) :
    originalMiddleMap (𝟙 E) = 𝟙 E.row.X₂ := normalized_beta_id E

/-- Descend the original direct-sum raw diagram through its actual quotient relation. -/
def leftSumMap {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (g : E' ⟶ E) : leftSumObj T E' ⟶ leftSumObj T' E :=
  Quotient.lift (fun d => mkHom (ExtensionDiagram.leftSum f d))
    (fun _d _e h => (mkHom_eq_iff _ _).2 (ExtensionDiagram.leftSum_rel f h)) g

/-- The descending map retains the actual inverse kernel component. -/
theorem leftSumMap_alpha {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (g : E' ⟶ E) :
    (homNormalization (leftSumMap f g)).hom.1.unop.hom =
      biprod.map f.iso.inv (homNormalization g).hom.1.unop.hom := by
  refine Quotient.inductionOn g ?_
  intro d
  rfl

/-- The descending map retains the actual forward middle component. -/
theorem leftSumMap_beta {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (g : E' ⟶ E) :
    (homNormalization (leftSumMap f g)).hom.2.hom =
      biprod.map f.iso.hom (homNormalization g).hom.2.hom := by
  refine Quotient.inductionOn g ?_
  intro d
  rfl

private theorem originalMiddleMap_leftSum {T U : Core C} (f : T ⟶ U)
    {E F : ExtensionCategory C} (g : E ⟶ F) :
    originalMiddleMap (leftSumMap f g) = biprod.map f.iso.hom (originalMiddleMap g) :=
  leftSumMap_beta f g

private theorem original_left_comp_middle {T U : Core C} (f : T ⟶ U)
    {E F : ExtensionCategory C} (g : leftSumObj U E ⟶ F) :
    originalMiddleMap (leftSumMap f (𝟙 E) ≫ g) =
      biprod.map f.iso.hom (𝟙 E.row.X₂) ≫ originalMiddleMap g := by
  have h := (originalMiddleMap_leftSum f (𝟙 E)).trans
    (congrArg (biprod.map f.iso.hom) (originalMiddleMap_id E))
  exact (originalMiddleMap_comp (leftSumMap f (𝟙 E)) g).trans
    (congrArg (· ≫ originalMiddleMap g) h)

/-- Both coordinates' identity arrows descend to the identity original row map. -/
theorem leftSumMap_id (T : Core C) (E : ExtensionCategory C) :
    leftSumMap (𝟙 T) (𝟙 E) = 𝟙 (leftSumObj T E) := by
  apply sum_hom_ext
  · rw [leftSumMap_alpha, homNormalization_id, homNormalization_id]
    change biprod.map (𝟙 T.of) (𝟙 E.row.X₁) = 𝟙 (T.of ⊞ E.row.X₁)
    apply biprod.hom_ext <;> simp
  · rw [leftSumMap_beta, homNormalization_id, homNormalization_id]
    change biprod.map (𝟙 T.of) (𝟙 E.row.X₂) = 𝟙 (T.of ⊞ E.row.X₂)
    apply biprod.hom_ext <;> simp

/-- Composition is the original category composition, in both coordinates. -/
theorem leftSumMap_comp {T T' T'' : Core C} (f : T ⟶ T') (g : T' ⟶ T'')
    {E E' E'' : ExtensionCategory C} (h : E ⟶ E') (k : E' ⟶ E'') :
    leftSumMap (f ≫ g) (h ≫ k) = leftSumMap f h ≫ leftSumMap g k := by
  apply sum_hom_ext
  · rw [leftSumMap_alpha, normalized_alpha_comp, normalized_alpha_comp]
    rw [leftSumMap_alpha, leftSumMap_alpha]
    change biprod.map (g.iso.inv ≫ f.iso.inv)
        ((homNormalization k).hom.1.unop.hom ≫ (homNormalization h).hom.1.unop.hom) =
      biprod.map g.iso.inv (homNormalization k).hom.1.unop.hom ≫
        biprod.map f.iso.inv (homNormalization h).hom.1.unop.hom
    apply biprod.hom_ext <;> simp [Category.assoc]
  · rw [leftSumMap_beta, normalized_beta_comp, normalized_beta_comp]
    rw [leftSumMap_beta, leftSumMap_beta]
    change biprod.map (f.iso.hom ≫ g.iso.hom)
        ((homNormalization h).hom.2.hom ≫ (homNormalization k).hom.2.hom) =
      biprod.map f.iso.hom (homNormalization h).hom.2.hom ≫
        biprod.map g.iso.hom (homNormalization k).hom.2.hom
    apply biprod.hom_ext <;> simp [Category.assoc]

/-- The actual core-times-extension direct-sum bifunctor. -/
def leftSumFunctor : Core C × ExtensionCategory C ⥤ ExtensionCategory C where
  obj p := leftSumObj p.1 p.2
  map f := leftSumMap f.1 f.2
  map_id p := leftSumMap_id p.1 p.2
  map_comp f g := leftSumMap_comp f.1 g.1 f.2 g.2

/-- The direct-sum action map leaves the actual Quillen target arrow unchanged. -/
theorem leftSumMap_target {T T' : Core C} (f : T ⟶ T')
    {E' E : ExtensionCategory C} (g : E' ⟶ E) :
    (target (C := C)).map (leftSumMap f g) = (target (C := C)).map g := by
  refine Quotient.inductionOn g ?_
  intro d
  exact ExtensionDiagram.leftSum_target f d

/-- The whole bifunctor lies over the original Quillen target, as a functor equality. -/
theorem leftSumFunctor_target :
    leftSumFunctor (C := C) ⋙ target =
      CategoryTheory.Prod.snd (Core C) (ExtensionCategory C) ⋙ target := by
  let L : Core C × ExtensionCategory C ⥤ QuillenQ C := leftSumFunctor ⋙ target
  let R : Core C × ExtensionCategory C ⥤ QuillenQ C :=
    CategoryTheory.Prod.snd (Core C) (ExtensionCategory C) ⋙ target
  let hObj : ∀ p, L.obj p = R.obj p := fun p => rfl
  refine CategoryTheory.Functor.ext (F := L) (G := R) hObj ?_
  intro p q f
  let A : QuillenQ C := (target (C := C)).obj p.2
  let B : QuillenQ C := (target (C := C)).obj q.2
  let qf : A ⟶ B := (target (C := C)).map (X := p.2) (Y := q.2) f.2
  let α : A ⟶ A := eqToHom (hObj p)
  let β : B ⟶ B := eqToHom (hObj q).symm
  have hα : α = 𝟙 A := eqToHom_refl A _
  have hβ : β = 𝟙 B := eqToHom_refl B _
  have hMap : L.map f = qf := leftSumMap_target f.1 f.2
  have hCast : α ≫ qf ≫ β = qf :=
    (congrArg₂ (fun (a : A ⟶ A) (b : B ⟶ B) => a ≫ qf ≫ b) hα hβ).trans
      ((congrArg (fun k : A ⟶ B => 𝟙 A ≫ k)
        (@Category.comp_id (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf)).trans
        (@Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf))
  exact hMap.trans hCast.symm

end AlgebraicKTheory.ExtensionCategory


namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction
open CategoryTheory.MonoidalCategory

/-- The original row regarded at its own literal given quotient. -/
def fixedView (E : ExtensionCategory C) : FixedTargetExtension C E.row.X₃ where
  A := E.row.X₁
  B := E.row.X₂
  i := E.row.f
  p := E.row.g
  zero := E.row.zero
  admissible := E.admissible

/-- The fixed view recovers the same original row. -/
theorem fixedView_toExtension (E : ExtensionCategory C) :
    (fixedView E).toExtension = E :=
  rfl

/-- A given-quotient iso pair gives its actual original row isomorphism. -/
def fixedRowIso {X : C} {F G : FixedTargetExtension C X} (h : F ⟶ G) :
    F.toExtension ≅ G.toExtension :=
  ((FixedTargetExtension.fiberInclusion X) ⋙ Functor.Fiber.fiberInclusion).mapIso (asIso h)

/-- The original middle map of a fixed row isomorphism is its stated component. -/
theorem fixedRowIso_beta {X : C} {F G : FixedTargetExtension C X} (h : F ⟶ G) :
    (homNormalization (fixedRowIso h).hom).hom.2.hom = h.b.hom :=
  rfl

private theorem middle_inverse_of_iso {E F : ExtensionCategory C} (e : E ≅ F)
    (b : E.row.X₂ ≅ F.row.X₂)
    (hb : (homNormalization e.hom).hom.2.hom = b.hom) :
    (homNormalization e.inv).hom.2.hom = b.inv := by
  apply (cancel_mono b.hom).mp
  have hc : (homNormalization (e.inv ≫ e.hom)).hom.2.hom =
      (homNormalization e.inv).hom.2.hom ≫ b.hom := by
    have hn := congrArg
      (fun k : F.subdivisionObj ⟶ F.subdivisionObj => k.hom.2.hom)
      (homNormalization_comp e.inv e.hom)
    exact hn.trans (congrArg ((homNormalization e.inv).hom.2.hom ≫ ·) hb)
  have hd : (homNormalization (e.inv ≫ e.hom)).hom.2.hom = 𝟙 F.row.X₂ :=
    (congrArg (fun k : F ⟶ F => (homNormalization k).hom.2.hom) e.inv_hom_id).trans
      (congrArg (fun k : F.subdivisionObj ⟶ F.subdivisionObj => k.hom.2.hom)
        (homNormalization_id F))
  exact (hc.symm.trans hd).trans b.inv_hom_id.symm

/-- The inverse original middle map is the inverse stated component. -/
theorem fixedRowIso_inv_beta {X : C} {F G : FixedTargetExtension C X} (h : F ⟶ G) :
    (homNormalization (fixedRowIso h).inv).hom.2.hom = h.b.inv := by
  exact middle_inverse_of_iso (fixedRowIso h) h.b (fixedRowIso_beta h)

/-- Every displayed fixed-quotient row isomorphism lies over the literal identity. -/
theorem fixedRowIso_target_hom {X : C} {F G : FixedTargetExtension C X} (h : F ⟶ G) :
    (target (C := C)).map (fixedRowIso h).hom = 𝟙 (⟨X⟩ : QuillenQ C) := by
  change (target (C := C)).map (mkHom (FixedTargetExtension.inclusionDiagram h)) = _
  exact FixedTargetExtension.inclusion_target h

/-- Zero addition has the actual biproduct zero-elimination row isomorphism. -/
def leftSumUnitIso (E : ExtensionCategory C) : leftSumObj (𝟙_ (Core C)) E ≅ E := by
  let h : fixedView (leftSumObj (𝟙_ (Core C)) E) ⟶ fixedView E :=
    { a := (isoZeroBiprod (X := (0 : C)) (Y := E.row.X₁) (isZero_zero C)).symm
      b := (isoZeroBiprod (X := (0 : C)) (Y := E.row.X₂) (isZero_zero C)).symm
      comm_i := by
        change biprod.map (𝟙 (0 : C)) E.row.f ≫ biprod.snd = biprod.snd ≫ E.row.f
        exact biprod.map_snd _ _
      comm_p := by
        change biprod.snd ≫ E.row.g = biprod.snd ≫ E.row.g
        rfl }
  exact fixedRowIso h

/-- The associator is the actual given-quotient biproduct associator on A/B. -/
def leftSumAssocIso (T U : Core C) (E : ExtensionCategory C) :
    leftSumObj (T ⊗ U) E ≅ leftSumObj T (leftSumObj U E) := by
  let h : fixedView (leftSumObj (T ⊗ U) E) ⟶
      fixedView (leftSumObj T (leftSumObj U E)) :=
    { a := biprod.associator T.of U.of E.row.X₁
      b := biprod.associator T.of U.of E.row.X₂
      comm_i := by
        change biprod.map (𝟙 (T.of ⊞ U.of)) E.row.f ≫
            (biprod.associator T.of U.of E.row.X₂).hom =
          (biprod.associator T.of U.of E.row.X₁).hom ≫
            biprod.map (𝟙 T.of) (biprod.map (𝟙 U.of) E.row.f)
        have hi : biprod.map (𝟙 T.of) (𝟙 U.of) = 𝟙 (T.of ⊞ U.of) := by
          apply biprod.hom_ext <;> simp
        simpa only [hi] using
          (biprod.associator_natural (𝟙 T.of) (𝟙 U.of) E.row.f)
      comm_p := by
        change (biprod.associator T.of U.of E.row.X₂).hom ≫
            (biprod.snd ≫ (biprod.snd ≫ E.row.g)) = biprod.snd ≫ E.row.g
        apply biprod.hom_ext'
        · apply biprod.hom_ext' <;> simp [biprod.associator]
        · simp [biprod.associator] }
  exact fixedRowIso h

/-- Middle component of the unit is the actual projection. -/
theorem leftSumUnitIso_beta (E : ExtensionCategory C) :
    (homNormalization (leftSumUnitIso E).hom).hom.2.hom =
      (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂) :=
  rfl

/-- Middle component of the associator is the actual biproduct associator. -/
theorem leftSumAssocIso_beta (T U : Core C) (E : ExtensionCategory C) :
    (homNormalization (leftSumAssocIso T U E).hom).hom.2.hom =
      (biprod.associator T.of U.of E.row.X₂).hom :=
  rfl

private theorem originalMiddleMap_unit (E : ExtensionCategory C) :
    originalMiddleMap (leftSumUnitIso E).hom =
      (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂) := leftSumUnitIso_beta E

private theorem originalMiddleMap_assoc (T U : Core C) (E : ExtensionCategory C) :
    originalMiddleMap (leftSumAssocIso T U E).hom =
      (biprod.associator T.of U.of E.row.X₂).hom := leftSumAssocIso_beta T U E

/-- Inverse middle component of the associator. -/
theorem leftSumAssocIso_inv_beta (T U : Core C) (E : ExtensionCategory C) :
    (homNormalization (leftSumAssocIso T U E).inv).hom.2.hom =
      (biprod.associator T.of U.of E.row.X₂).inv := by
  exact middle_inverse_of_iso (leftSumAssocIso T U E)
    (biprod.associator T.of U.of E.row.X₂) (leftSumAssocIso_beta T U E)

omit [ExactCategory C] in
private theorem core_whiskerLeft_hom (T : Core C) {U V : Core C} (f : U ⟶ V) :
    (T ◁ f).iso.hom = biprod.map (𝟙 T.of) f.iso.hom :=
  (coreBiprodTensorLeft_map_iso_hom T f).trans (coreLeftBiprodFunctor_map_iso_hom T.of f)

omit [ExactCategory C] in
private theorem core_whiskerRight_hom {U V : Core C} (f : U ⟶ V) (T : Core C) :
    (f ▷ T).iso.hom = biprod.map f.iso.hom (𝟙 T.of) := by
  rw [← tensorHom_id]
  exact (coreBiprodTensorHom_iso_hom f (𝟙 T)).trans
    (congrArg (biprod.map f.iso.hom) ((Core.inclusion C).map_id T))

/-- The lawful coherent action of the original core by adding a left summand. -/
@[instance_reducible]
def leftSumAction : MonoidalLeftAction (Core C) (ExtensionCategory C) where
  actionObj := leftSumObj
  actionHomLeft {T T'} f E := leftSumMap f (𝟙 E)
  actionHomRight T {E F} f := leftSumMap (𝟙 T) f
  actionHom {T T'} {E F} f g := leftSumMap f g
  actionAssocIso := leftSumAssocIso
  actionUnitIso := leftSumUnitIso
  actionHom_def {T T'} {E F} f g := by
    simpa only [Category.comp_id, Category.id_comp] using
      (leftSumMap_comp f (𝟙 _) (𝟙 _) g)
  actionHomRight_id T E := leftSumMap_id T E
  id_actionHomLeft T E := leftSumMap_id T E
  actionHom_comp {T T' T''} {E F G} f g h k := leftSumMap_comp f g h k
  actionAssocIso_hom_naturality {T T' U U'} {E F} f g h := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, leftSumAssocIso_beta,
      coreBiprodTensorHom_iso_hom]
    change biprod.map (biprod.map f.iso.hom g.iso.hom)
        (homNormalization h).hom.2.hom ≫ (biprod.associator _ _ _).hom =
      (biprod.associator _ _ _).hom ≫
        biprod.map f.iso.hom (biprod.map g.iso.hom (homNormalization h).hom.2.hom)
    exact biprod.associator_natural _ _ _
  actionUnitIso_hom_naturality {E F} f := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, leftSumUnitIso_beta]
    change biprod.snd ≫ (homNormalization f).hom.2.hom =
      biprod.map (𝟙 (0 : C)) (homNormalization f).hom.2.hom ≫ biprod.snd
    exact (biprod.map_snd _ _).symm
  whiskerLeft_actionHomLeft T {U V} f E := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, normalized_beta_id,
      leftSumAssocIso_beta, leftSumAssocIso_inv_beta, core_whiskerLeft_hom]
    change biprod.map (biprod.map (𝟙 T.of) f.iso.hom) (𝟙 E.row.X₂) =
      (biprod.associator _ _ _).hom ≫
        biprod.map (𝟙 T.of) (biprod.map f.iso.hom (𝟙 E.row.X₂)) ≫
          (biprod.associator _ _ _).inv
    apply (cancel_mono (biprod.associator T.of V.of E.row.X₂).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact biprod.associator_natural _ _ _
  whiskerRight_actionHomLeft {U V} T f E := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, normalized_beta_id,
      leftSumAssocIso_beta, leftSumAssocIso_inv_beta, core_whiskerRight_hom]
    change biprod.map (biprod.map f.iso.hom (𝟙 T.of)) (𝟙 E.row.X₂) =
      (biprod.associator _ _ _).hom ≫
        biprod.map f.iso.hom (𝟙 (T.of ⊞ E.row.X₂)) ≫
          (biprod.associator _ _ _).inv
    apply (cancel_mono (biprod.associator V.of T.of E.row.X₂).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hid : biprod.map (𝟙 T.of) (𝟙 E.row.X₂) = 𝟙 (T.of ⊞ E.row.X₂) := by
      apply biprod.hom_ext <;> simp
    simpa only [hid] using
      (biprod.associator_natural f.iso.hom (𝟙 T.of) (𝟙 E.row.X₂))
  associator_actionHom T U V E := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, normalized_beta_id,
      leftSumAssocIso_beta]
    change biprod.map (biprod.associator T.of U.of V.of).hom (𝟙 E.row.X₂) ≫
        (biprod.associator T.of (U.of ⊞ V.of) E.row.X₂).hom ≫
          biprod.map (𝟙 T.of) (biprod.associator U.of V.of E.row.X₂).hom =
      (biprod.associator (T.of ⊞ U.of) V.of E.row.X₂).hom ≫
        (biprod.associator T.of U.of (V.of ⊞ E.row.X₂)).hom
    exact (coreLeftBiprodBiprodIso_pentagon_component T.of U.of V.of E.row.X₂).symm
  leftUnitor_actionHom T E := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, normalized_beta_id,
      leftSumAssocIso_beta, leftSumUnitIso_beta]
    change biprod.map (biprod.snd : (0 : C) ⊞ T.of ⟶ T.of) (𝟙 E.row.X₂) =
      (biprod.associator (0 : C) T.of E.row.X₂).hom ≫ biprod.snd
    apply biprod.hom_ext <;> simp [biprod.associator]
  rightUnitor_actionHom T E := by
    apply AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle
    simp only [normalized_beta_comp, leftSumMap_beta, normalized_beta_id,
      leftSumAssocIso_beta, leftSumUnitIso_beta]
    change biprod.map (biprod.fst : T.of ⊞ (0 : C) ⟶ T.of) (𝟙 E.row.X₂) =
      (biprod.associator T.of (0 : C) E.row.X₂).hom ≫
        biprod.map (𝟙 T.of) (biprod.snd : (0 : C) ⊞ E.row.X₂ ⟶ E.row.X₂)
    exact (coreLeftBiprodBiprodIso_rightUnit_component T.of E.row.X₂).symm


/-- The action unitor preserves the literal given Quillen quotient. -/
theorem leftSumUnitIso_target (E : ExtensionCategory C) :
    (target (C := C)).map (leftSumUnitIso E).hom = 𝟙 ((target (C := C)).obj E) := by
  exact fixedRowIso_target_hom _

/-- The action associator preserves the literal given Quillen quotient. -/
theorem leftSumAssocIso_target (T U : Core C) (E : ExtensionCategory C) :
    (target (C := C)).map (leftSumAssocIso T U E).hom =
      𝟙 ((target (C := C)).obj E) := by
  exact fixedRowIso_target_hom _

end AlgebraicKTheory.ExtensionCategory

end


/-!
# The original Quillen target after the actual core-action localization

This section uses the existing positive-first `SInverse` category. Its
map sends a stabilized representative to the actual Quillen image of its
extension-row component. The stabilizer, denominator arrow and given
quotients are retained in the source category; the projection does not
replace the extension category or assume a fibration result.
-/

noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- The actual existing localization, with extension first and denominator second. -/
abbrev localizedExtensions :=
  MonoidalActionCategory.SInverse (Core C) (ExtensionCategory C)

private theorem quillen_id_comp {A B : QuillenQ C} (f : A ⟶ B) : 𝟙 A ≫ f = f :=
  @Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C)) A B f

private theorem localized_target_rel
    {E F : localizedExtensions (C := C)}
    {r s : MonoidalActionCategory.RawHom E F} (h : r.Rel s) :
    (target (C := C)).map (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1 =
      (target (C := C)).map (X := leftSumObj s.stabilizer E.of.1) (Y := F.of.1) s.hom.1 := by
  obtain ⟨e, he⟩ := h
  have hh : leftSumMap e.hom (𝟙 E.of.1) ≫ s.hom.1 = r.hom.1 :=
    congrArg (fun k : (r.stabilizer ⊙ₗ E.of) ⟶ F.of => k.1) he
  have hz : (target (C := C)).map (leftSumMap e.hom (𝟙 E.of.1)) =
      𝟙 ((target (C := C)).obj E.of.1) :=
    (leftSumMap_target e.hom (𝟙 E.of.1)).trans ((target (C := C)).map_id E.of.1)
  have hp := congrArg
    (fun k : leftSumObj r.stabilizer E.of.1 ⟶ F.of.1 => (target (C := C)).map k) hh
  exact hp.symm.trans (((target (C := C)).map_comp _ _).trans
    ((congrArg
      (· ≫ (target (C := C)).map (X := leftSumObj s.stabilizer E.of.1) (Y := F.of.1) s.hom.1)
      hz).trans
      (quillen_id_comp (A := (target (C := C)).obj E.of.1)
        (B := (target (C := C)).obj F.of.1)
        ((target (C := C)).map (X := leftSumObj s.stabilizer E.of.1)
          (Y := F.of.1) s.hom.1))))

private theorem localized_target_raw_id (E : localizedExtensions (C := C)) :
    (target (C := C)).map (MonoidalActionCategory.RawHom.id E).hom.1 =
      𝟙 ((target (C := C)).obj E.of.1) := by
  change (target (C := C)).map (leftSumUnitIso E.of.1).hom = _
  exact leftSumUnitIso_target E.of.1

private theorem localized_target_raw_comp
    {E F G : localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom E F) (s : MonoidalActionCategory.RawHom F G) :
    (target (C := C)).map (r.comp s).hom.1 =
      (target (C := C)).map (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1 ≫
        (target (C := C)).map (X := leftSumObj s.stabilizer F.of.1) (Y := G.of.1) s.hom.1 := by
  let a : leftSumObj (s.stabilizer ⊗ r.stabilizer) E.of.1 ⟶
      leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1) :=
    (leftSumAssocIso s.stabilizer r.stabilizer E.of.1).hom
  let b : leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1) ⟶
      leftSumObj s.stabilizer F.of.1 := leftSumMap (𝟙 s.stabilizer) r.hom.1
  let c : leftSumObj s.stabilizer F.of.1 ⟶ G.of.1 := s.hom.1
  have ha : (target (C := C)).map a = 𝟙 ((target (C := C)).obj E.of.1) :=
    leftSumAssocIso_target s.stabilizer r.stabilizer E.of.1
  have hb : (target (C := C)).map b =
      (target (C := C)).map (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1 :=
    leftSumMap_target (𝟙 s.stabilizer) r.hom.1
  let bc : leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1) ⟶ G.of.1 := b ≫ c
  let Q0 : QuillenQ C := (target (C := C)).obj E.of.1
  let Q1 : QuillenQ C := (target (C := C)).obj F.of.1
  let Q2 : QuillenQ C := (target (C := C)).obj G.of.1
  let qa : Q0 ⟶ Q0 := (target (C := C)).map
    (X := leftSumObj (s.stabilizer ⊗ r.stabilizer) E.of.1)
    (Y := leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1)) a
  let qb : Q0 ⟶ Q1 := (target (C := C)).map
    (X := leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1))
    (Y := leftSumObj s.stabilizer F.of.1) b
  let qc : Q1 ⟶ Q2 := (target (C := C)).map
    (X := leftSumObj s.stabilizer F.of.1) (Y := G.of.1) c
  let qr : Q0 ⟶ Q1 := (target (C := C)).map
    (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1
  let qbc : Q0 ⟶ Q2 := (target (C := C)).map
    (X := leftSumObj s.stabilizer (leftSumObj r.stabilizer E.of.1)) (Y := G.of.1) bc
  let qabc : Q0 ⟶ Q2 := (target (C := C)).map
    (X := leftSumObj (s.stabilizer ⊗ r.stabilizer) E.of.1) (Y := G.of.1) (a ≫ bc)
  have h1 : qabc = qa ≫ qbc := (target (C := C)).map_comp a bc
  have hqa : qa = 𝟙 Q0 := ha
  have h2 : qa ≫ qbc = qbc :=
    (congrArg (fun k : Q0 ⟶ Q0 => k ≫ qbc) hqa).trans
      (@Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
        Q0 Q2 qbc)
  have h3 : qbc = qb ≫ qc := (target (C := C)).map_comp b c
  have hqb : qb = qr := hb
  have h4 : qb ≫ qc = qr ≫ qc := congrArg (fun k : Q0 ⟶ Q1 => k ≫ qc) hqb
  exact h1.trans (h2.trans (h3.trans h4))

/-- Descend the actual extension component through stabilizer-isomorphism classes. -/
def localizedTargetMap {E F : localizedExtensions (C := C)} (f : E ⟶ F) :
    (target (C := C)).obj E.of.1 ⟶ (target (C := C)).obj F.of.1 :=
  Quotient.lift
    (fun r : MonoidalActionCategory.RawHom E F =>
      (target (C := C)).map (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1)
    (fun _ _ h => by exact localized_target_rel h) f

/-- A represented localized arrow maps to its literal original extension component. -/
theorem localizedTargetMap_mk {E F : localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom E F) :
    localizedTargetMap (MonoidalActionCategory.Hom.mk r) =
      (target (C := C)).map (X := leftSumObj r.stabilizer E.of.1) (Y := F.of.1) r.hom.1 := rfl

/-- The localized identity uses the original action unitor over the given quotient. -/
theorem localizedTargetMap_id (E : localizedExtensions (C := C)) :
    localizedTargetMap (𝟙 E) = 𝟙 ((target (C := C)).obj E.of.1) := by
  exact localized_target_raw_id E

/-- Composition descends with its actual later-times-earlier stabilizer. -/
theorem localizedTargetMap_comp {E F G : localizedExtensions (C := C)}
    (f : E ⟶ F) (g : F ⟶ G) :
    localizedTargetMap (f ≫ g) = localizedTargetMap f ≫ localizedTargetMap g := by
  refine Quotient.inductionOn₂ f g ?_
  intro r s
  exact localized_target_raw_comp r s

/-- The actual localized total extension category maps to the original Quillen Q. -/
def localizedTarget : localizedExtensions (C := C) ⥤ QuillenQ C where
  obj E := (target (C := C)).obj E.of.1
  map f := localizedTargetMap f
  map_id E := localizedTargetMap_id E
  map_comp f g := localizedTargetMap_comp f g

/-- The projection retains the given quotient of the positive extension row. -/
theorem localizedTarget_obj (E : localizedExtensions (C := C)) :
    (localizedTarget (C := C)).obj E = (⟨E.of.1.row.X₃⟩ : QuillenQ C) := rfl

private theorem localized_target_positive_map {E F : ExtensionCategory C} (f : E ⟶ F) :
    (localizedTarget (C := C)).map
        ((MonoidalActionCategory.SInverse.inclusion (Core C) (ExtensionCategory C)).map f) =
      (target (C := C)).map f := by
  change (target (C := C)).map ((leftSumUnitIso E).hom ≫ f) =
    (target (C := C)).map f
  exact ((target (C := C)).map_comp _ _).trans
    ((congrArg (· ≫ (target (C := C)).map f) (leftSumUnitIso_target E)).trans
      (quillen_id_comp (A := (target (C := C)).obj E)
        (B := (target (C := C)).obj F) ((target (C := C)).map f)))

/-- The original extension target is the positive-inclusion composite, on all objects/maps. -/
theorem localizedTarget_inclusion :
    MonoidalActionCategory.SInverse.inclusion (Core C) (ExtensionCategory C) ⋙
      localizedTarget = target := by
  let L : ExtensionCategory C ⥤ QuillenQ C :=
    MonoidalActionCategory.SInverse.inclusion (Core C) (ExtensionCategory C) ⋙ localizedTarget
  let R : ExtensionCategory C ⥤ QuillenQ C := target
  let hObj : ∀ E, L.obj E = R.obj E := fun E => rfl
  refine CategoryTheory.Functor.ext (F := L) (G := R) hObj ?_
  intro E F f
  let A : QuillenQ C := (target (C := C)).obj E
  let B : QuillenQ C := (target (C := C)).obj F
  let qf : A ⟶ B := (target (C := C)).map (X := E) (Y := F) f
  let α : A ⟶ A := eqToHom (hObj E)
  let β : B ⟶ B := eqToHom (hObj F).symm
  have hα : α = 𝟙 A := eqToHom_refl A _
  have hβ : β = 𝟙 B := eqToHom_refl B _
  have hMap : L.map f = qf := localized_target_positive_map f
  have hCast : α ≫ qf ≫ β = qf :=
    (congrArg₂ (fun (a : A ⟶ A) (b : B ⟶ B) => a ≫ qf ≫ b) hα hβ).trans
      ((congrArg (fun k : A ⟶ B => 𝟙 A ≫ k)
        (@Category.comp_id (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf)).trans
        (@Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf))
  exact hMap.trans hCast.symm

end AlgebraicKTheory.ExtensionCategory

end


/-!
# The direct core action on the original given-X extension rows

The fixed-target category is the existing given-quotient row groupoid.
Its summand and isomorphism-pair maps below are literal biproduct data.
They provide the source action for the strict localized-fiber comparison;
no equivalence or fibration is supplied as a premise.
-/

noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

/-- Two fixed-target extension morphisms agree when their forward middle maps agree. -/
theorem hom_ext_of_middle {F G : FixedTargetExtension C X} (f g : F ⟶ G)
    (hb : f.b.hom = g.b.hom) : f = g := by
  apply Hom.ext
  · apply Iso.ext
    let _ : Mono G.i := (isAdmissibleMono_f G.admissible).mono
    apply (cancel_mono G.i).mp
    exact f.comm_i.symm.trans ((congrArg (F.i ≫ ·) hb).trans g.comm_i)
  · exact Iso.ext hb

/-- Add the original summand on A/B and retain exactly the given quotient X. -/
def leftSumObj (T : Core C) (F : FixedTargetExtension C X) : FixedTargetExtension C X := by
  have w : biprod.map (𝟙 T.of) F.i ≫ (biprod.snd ≫ F.p) = 0 := by
    rw [← Category.assoc, biprod.map_snd, Category.assoc, F.zero, comp_zero]
  exact
    { A := T.of ⊞ F.A
      B := T.of ⊞ F.B
      i := biprod.map (𝟙 T.of) F.i
      p := biprod.snd ≫ F.p
      zero := w
      admissible := by
        exact AlgebraicKTheory.left_sum_exact T.of F.toExtension.row F.admissible w }

/-- Forgetting the fixed row gives the same original extension-row left sum. -/
theorem leftSumObj_toExtension (T : Core C) (F : FixedTargetExtension C X) :
    (leftSumObj T F).toExtension = ExtensionCategory.leftSumObj T F.toExtension := rfl

/-- The fixed-row maps are the actual forward biproduct isomorphism pairs. -/
def leftSumMap {T T' : Core C} (f : T ⟶ T') {F G : FixedTargetExtension C X}
    (g : F ⟶ G) : leftSumObj T F ⟶ leftSumObj T' G where
  a := biprod.mapIso f.iso g.a
  b := biprod.mapIso f.iso g.b
  comm_i := by
    change biprod.map (𝟙 T.of) F.i ≫ biprod.map f.iso.hom g.b.hom =
      biprod.map f.iso.hom g.a.hom ≫ biprod.map (𝟙 T'.of) G.i
    apply biprod.hom_ext <;> simp [Category.assoc, g.comm_i]
  comm_p := by
    change biprod.map f.iso.hom g.b.hom ≫ (biprod.snd ≫ G.p) = biprod.snd ≫ F.p
    rw [← Category.assoc, biprod.map_snd, Category.assoc, g.comm_p]

/-- The actual forward middle coordinate of a fixed-row sum map. -/
theorem leftSumMap_b_hom {T T' : Core C} (f : T ⟶ T')
    {F G : FixedTargetExtension C X} (g : F ⟶ G) :
    (leftSumMap f g).b.hom = biprod.map f.iso.hom g.b.hom := rfl

/-- The two original identities give the identity of the fixed-row left sum. -/
theorem leftSumMap_id (T : Core C) (F : FixedTargetExtension C X) :
    leftSumMap (𝟙 T) (𝟙 F) = 𝟙 (leftSumObj T F) := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  change biprod.map (𝟙 T.of) (𝟙 F.B) = 𝟙 (T.of ⊞ F.B)
  apply biprod.hom_ext <;> simp

/-- Composition keeps the actual forward core and forward row coordinates. -/
theorem leftSumMap_comp {T T' T'' : Core C} (f : T ⟶ T') (g : T' ⟶ T'')
    {F G H : FixedTargetExtension C X} (h : F ⟶ G) (k : G ⟶ H) :
    leftSumMap (f ≫ g) (h ≫ k) = leftSumMap f h ≫ leftSumMap g k := by
  apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
  change biprod.map (f.iso.hom ≫ g.iso.hom) (h.b.hom ≫ k.b.hom) =
    biprod.map f.iso.hom h.b.hom ≫ biprod.map g.iso.hom k.b.hom
  apply biprod.hom_ext <;> simp [Category.assoc]

/-- Package the actual given-X inverse pair, using the proved groupoid operations. -/
def pairIso {F G : FixedTargetExtension C X} (h : F ⟶ G) : F ≅ G where
  hom := h
  inv := Hom.symm h
  hom_inv_id := Groupoid.comp_inv h
  inv_hom_id := Groupoid.inv_comp h

/-- The fixed action unitor is the original zero-elimination pair on A/B. -/
def leftSumUnitIso (F : FixedTargetExtension C X) : leftSumObj (𝟙_ (Core C)) F ≅ F := by
  let h : leftSumObj (𝟙_ (Core C)) F ⟶ F :=
    { a := (isoZeroBiprod (X := (0 : C)) (Y := F.A) (isZero_zero C)).symm
      b := (isoZeroBiprod (X := (0 : C)) (Y := F.B) (isZero_zero C)).symm
      comm_i := by
        change biprod.map (𝟙 (0 : C)) F.i ≫ biprod.snd = biprod.snd ≫ F.i
        exact biprod.map_snd _ _
      comm_p := by
        change biprod.snd ≫ F.p = biprod.snd ≫ F.p
        rfl }
  exact pairIso h

/-- The fixed action associator is the original biproduct associator pair on A/B. -/
def leftSumAssocIso (T U : Core C) (F : FixedTargetExtension C X) :
    leftSumObj (T ⊗ U) F ≅ leftSumObj T (leftSumObj U F) := by
  let h : leftSumObj (T ⊗ U) F ⟶ leftSumObj T (leftSumObj U F) :=
    { a := biprod.associator T.of U.of F.A
      b := biprod.associator T.of U.of F.B
      comm_i := by
        change biprod.map (𝟙 (T.of ⊞ U.of)) F.i ≫
            (biprod.associator T.of U.of F.B).hom =
          (biprod.associator T.of U.of F.A).hom ≫
            biprod.map (𝟙 T.of) (biprod.map (𝟙 U.of) F.i)
        have hi : biprod.map (𝟙 T.of) (𝟙 U.of) = 𝟙 (T.of ⊞ U.of) := by
          apply biprod.hom_ext <;> simp
        simpa only [hi] using (biprod.associator_natural (𝟙 T.of) (𝟙 U.of) F.i)
      comm_p := by
        change (biprod.associator T.of U.of F.B).hom ≫
            (biprod.snd ≫ (biprod.snd ≫ F.p)) = biprod.snd ≫ F.p
        apply biprod.hom_ext'
        · apply biprod.hom_ext' <;> simp [biprod.associator]
        · simp [biprod.associator] }
  exact pairIso h

/-- The fixed unitor's middle coordinate is the actual projection. -/
theorem leftSumUnitIso_b_hom (F : FixedTargetExtension C X) :
    (leftSumUnitIso F).hom.b.hom = (biprod.snd : (0 : C) ⊞ F.B ⟶ F.B) := rfl

/-- The fixed associator's middle coordinate is the actual associator. -/
theorem leftSumAssocIso_b_hom (T U : Core C) (F : FixedTargetExtension C X) :
    (leftSumAssocIso T U F).hom.b.hom = (biprod.associator T.of U.of F.B).hom := rfl

/-- Its inverse uses the actual inverse associator, without an opaque chosen inverse. -/
theorem leftSumAssocIso_inv_b_hom (T U : Core C) (F : FixedTargetExtension C X) :
    (leftSumAssocIso T U F).inv.b.hom = (biprod.associator T.of U.of F.B).inv := rfl

/-- The direct coherent core action on the original rows ending at the same given X. -/
@[instance_reducible]
def leftSumAction (X : C) : MonoidalLeftAction (Core C) (FixedTargetExtension C X) where
  actionObj := leftSumObj
  actionHomLeft {T T'} f F := leftSumMap f (𝟙 F)
  actionHomRight T {F G} f := leftSumMap (𝟙 T) f
  actionHom {T T'} {F G} f g := leftSumMap f g
  actionAssocIso := leftSumAssocIso
  actionUnitIso := leftSumUnitIso
  actionHom_def {T T'} {F G} f g := by
    simpa only [Category.comp_id, Category.id_comp] using
      (leftSumMap_comp f (𝟙 _) (𝟙 _) g)
  actionHomRight_id T F := leftSumMap_id T F
  id_actionHomLeft T F := leftSumMap_id T F
  actionHom_comp {T T' T''} {F G H} f g h k := leftSumMap_comp f g h k
  actionAssocIso_hom_naturality {T T' U U'} {F G} f g h := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, leftSumAssocIso_b_hom]
    change biprod.map (biprod.map f.iso.hom g.iso.hom) h.b.hom ≫
        (biprod.associator _ _ _).hom =
      (biprod.associator _ _ _).hom ≫ biprod.map f.iso.hom (biprod.map g.iso.hom h.b.hom)
    exact biprod.associator_natural _ _ _
  actionUnitIso_hom_naturality {F G} f := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, leftSumUnitIso_b_hom]
    change biprod.snd ≫ f.b.hom = biprod.map (𝟙 (0 : C)) f.b.hom ≫ biprod.snd
    exact (biprod.map_snd _ _).symm
  whiskerLeft_actionHomLeft T {U V} f F := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, id_b, Iso.refl_hom,
      leftSumAssocIso_b_hom, leftSumAssocIso_inv_b_hom]
    change biprod.map (biprod.map (𝟙 T.of) f.iso.hom) (𝟙 F.B) =
      (biprod.associator _ _ _).hom ≫
        biprod.map (𝟙 T.of) (biprod.map f.iso.hom (𝟙 F.B)) ≫ (biprod.associator _ _ _).inv
    apply (cancel_mono (biprod.associator _ _ _).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact biprod.associator_natural _ _ _
  whiskerRight_actionHomLeft {U V} T f F := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, id_b, Iso.refl_hom,
      leftSumAssocIso_b_hom, leftSumAssocIso_inv_b_hom]
    change biprod.map (biprod.map f.iso.hom (𝟙 T.of)) (𝟙 F.B) =
      (biprod.associator _ _ _).hom ≫ biprod.map f.iso.hom (𝟙 (T.of ⊞ F.B)) ≫
        (biprod.associator _ _ _).inv
    apply (cancel_mono (biprod.associator _ _ _).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hid : biprod.map (𝟙 T.of) (𝟙 F.B) = 𝟙 (T.of ⊞ F.B) := by
      apply biprod.hom_ext <;> simp
    simpa only [hid] using (biprod.associator_natural f.iso.hom (𝟙 T.of) (𝟙 F.B))
  associator_actionHom T U V F := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, id_b, Iso.refl_hom,
      leftSumAssocIso_b_hom]
    change biprod.map (biprod.associator T.of U.of V.of).hom (𝟙 F.B) ≫
        (biprod.associator T.of (U.of ⊞ V.of) F.B).hom ≫
          biprod.map (𝟙 T.of) (biprod.associator U.of V.of F.B).hom =
      (biprod.associator (T.of ⊞ U.of) V.of F.B).hom ≫
        (biprod.associator T.of U.of (V.of ⊞ F.B)).hom
    exact (coreLeftBiprodBiprodIso_pentagon_component T.of U.of V.of F.B).symm
  leftUnitor_actionHom T F := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, id_b, Iso.refl_hom,
      leftSumAssocIso_b_hom, leftSumUnitIso_b_hom]
    change biprod.map (biprod.snd : (0 : C) ⊞ T.of ⟶ T.of) (𝟙 F.B) =
      (biprod.associator (0 : C) T.of F.B).hom ≫ biprod.snd
    apply biprod.hom_ext <;> simp [biprod.associator]
  rightUnitor_actionHom T F := by
    apply AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle
    simp only [comp_b, Iso.trans_hom, leftSumMap_b_hom, id_b, Iso.refl_hom,
      leftSumAssocIso_b_hom, leftSumUnitIso_b_hom]
    change biprod.map (biprod.fst : T.of ⊞ (0 : C) ⟶ T.of) (𝟙 F.B) =
      (biprod.associator T.of (0 : C) F.B).hom ≫
        biprod.map (𝟙 T.of) (biprod.snd : (0 : C) ⊞ F.B ⟶ F.B)
    exact (coreLeftBiprodBiprodIso_rightUnit_component T.of F.B).symm

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual localization of the original given-X rows, with denominator second. -/
abbrev localizedRows (X : C) :=
  MonoidalActionCategory.SInverse (Core C) (FixedTargetExtension C X)

/-- The actual original-row forgetful functor, through the existing strict fiber. -/
def forget (X : C) : FixedTargetExtension C X ⥤ ExtensionCategory C :=
  fiberInclusion X ⋙ Functor.Fiber.fiberInclusion

private theorem forget_beta {F G : FixedTargetExtension C X} (g : F ⟶ G) :
    (ExtensionCategory.homNormalization ((forget X).map g)).hom.2.hom = g.b.hom := by
  have h : (forget X).map g = ((fiberInclusion X).map g).val := rfl
  exact (congrArg (fun k : F.toExtension ⟶ G.toExtension =>
    (ExtensionCategory.homNormalization k).hom.2.hom) h).trans (inclusion_map_beta g)

private theorem original_eqToHom_beta {E F : ExtensionCategory C} (h : E = F) :
    (ExtensionCategory.homNormalization (eqToHom h)).hom.2.hom =
      eqToHom (congrArg (fun E : ExtensionCategory C => E.row.X₂) h) := by
  cases h
  simp only [eqToHom_refl, ExtensionCategory.homNormalization_id]
  rfl

private theorem fixed_middle_comp {F G H : FixedTargetExtension C X}
    (f : F ⟶ G) (g : G ⟶ H) : (f ≫ g).b.hom = f.b.hom ≫ g.b.hom :=
  congrArg Iso.hom (comp_b f g)

private theorem fixed_left_comp_middle {T U : Core C} (f : T ⟶ U)
    {F G : FixedTargetExtension C X} (g : leftSumObj U F ⟶ G) :
    (leftSumMap f (𝟙 F) ≫ g).b.hom =
      biprod.map f.iso.hom (𝟙 F.B) ≫ g.b.hom := by
  exact (fixed_middle_comp (leftSumMap f (𝟙 F)) g).trans
    (congrArg (· ≫ g.b.hom) (leftSumMap_b_hom f (𝟙 F)))

/-- Preserve the original fixed row and its actual denominator. -/
def localizedObject (a : localizedRows (C := C) X) :
    ExtensionCategory.localizedExtensions (C := C) :=
  ⟨(a.of.1.toExtension, a.of.2)⟩

/-- Forward a stabilized given-X arrow without changing stabilizer or denominator map. -/
def localizedRawMap {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (localizedObject a) (localizedObject b) where
  stabilizer := r.stabilizer
  hom :=
    (eqToHom (leftSumObj_toExtension r.stabilizer a.of.1).symm ≫
        ((forget X).map (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1 :
          (leftSumObj r.stabilizer a.of.1).toExtension ⟶ b.of.1.toExtension), r.hom.2)

private theorem localizedRawMap_positive {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedRawMap r).hom.1 =
      ((forget X).map (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1 :
        ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶ b.of.1.toExtension) := by
  let A : ExtensionCategory C := ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension
  let B : ExtensionCategory C := b.of.1.toExtension
  let f : A ⟶ B :=
    (forget X).map (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1
  have hc : (eqToHom (leftSumObj_toExtension r.stabilizer a.of.1).symm : A ⟶ A) =
      𝟙 A := eqToHom_refl _ _
  exact (congrArg (fun k : A ⟶ A => k ≫ f) hc).trans (Category.id_comp f)

/-- The forward original middle map is exactly the given fixed-row middle map. -/
theorem localizedRawMap_beta {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (ExtensionCategory.homNormalization (localizedRawMap r).hom.1).hom.2.hom =
      r.hom.1.b.hom := by
  let A : ExtensionCategory C := ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension
  let B : ExtensionCategory C := b.of.1.toExtension
  exact (congrArg (fun k : A ⟶ B => ExtensionCategory.originalMiddleMap k)
    (localizedRawMap_positive r)).trans (forget_beta r.hom.1)

/-- The denominator component is literally unchanged. -/
theorem localizedRawMap_denominator {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedRawMap r).hom.2 = r.hom.2 := rfl

/-- The stabilizer object is literally unchanged. -/
theorem localizedRawMap_stabilizer {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedRawMap r).stabilizer = r.stabilizer := rfl

private theorem original_raw_action_middle {a b : localizedRows (C := C) X}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ⟶ s.stabilizer) :
    ExtensionCategory.originalMiddleMap
        (ExtensionCategory.leftSumMap e (𝟙 a.of.1.toExtension) ≫
          ((localizedRawMap s).hom.1 :
            ExtensionCategory.leftSumObj s.stabilizer a.of.1.toExtension ⟶ b.of.1.toExtension)) =
      biprod.map e.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom := by
  let f : ExtensionCategory.leftSumObj s.stabilizer a.of.1.toExtension ⟶
      b.of.1.toExtension := (localizedRawMap s).hom.1
  exact (ExtensionCategory.original_left_comp_middle e f).trans
    (congrArg (biprod.map e.iso.hom (𝟙 a.of.1.B) ≫ ·) (localizedRawMap_beta s))

private theorem fixed_raw_action_middle {a b : localizedRows (C := C) X}
    (r s : MonoidalActionCategory.RawHom a b) (e : r.stabilizer ⟶ s.stabilizer) :
    (leftSumMap e (𝟙 a.of.1) ≫
        (s.hom.1 : leftSumObj s.stabilizer a.of.1 ⟶ b.of.1)).b.hom =
      biprod.map e.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom :=
  fixed_left_comp_middle e s.hom.1

private theorem localizedRawMap_rel {a b : localizedRows (C := C) X}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (localizedRawMap r).Rel (localizedRawMap s) := by
  obtain ⟨e, he⟩ := h
  let f : ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶
      b.of.1.toExtension :=
    ExtensionCategory.leftSumMap e.hom (𝟙 a.of.1.toExtension) ≫
      ((localizedRawMap s).hom.1 :
        ExtensionCategory.leftSumObj s.stabilizer a.of.1.toExtension ⟶ b.of.1.toExtension)
  let g : ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶
      b.of.1.toExtension := (localizedRawMap r).hom.1
  have hFixed : (leftSumMap e.hom (𝟙 a.of.1) ≫ s.hom.1).b.hom = r.hom.1.b.hom :=
    congrArg (fun k : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => k.1.b.hom) he
  have hBeta : biprod.map e.hom.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom =
      r.hom.1.b.hom := (fixed_raw_action_middle r s e.hom).symm.trans hFixed
  have hm : ExtensionCategory.originalMiddleMap f = ExtensionCategory.originalMiddleMap g :=
    (original_raw_action_middle r s e.hom).trans
      (hBeta.trans (localizedRawMap_beta r).symm)
  have hFirst : f = g := AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle f g hm
  have hDen := congrArg (fun k : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => k.2) he
  exact ⟨e, Prod.ext hFirst hDen⟩

private theorem original_raw_comp_middle {a b c : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    ExtensionCategory.originalMiddleMap (((localizedRawMap r).comp (localizedRawMap s)).hom.1) =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom := by
  let A : ExtensionCategory C :=
    ExtensionCategory.leftSumObj (s.stabilizer ⊗ r.stabilizer) a.of.1.toExtension
  let B : ExtensionCategory C := ExtensionCategory.leftSumObj s.stabilizer
    (ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension)
  let D : ExtensionCategory C := ExtensionCategory.leftSumObj s.stabilizer b.of.1.toExtension
  let E : ExtensionCategory C := c.of.1.toExtension
  let fa : A ⟶ B :=
    (ExtensionCategory.leftSumAssocIso s.stabilizer r.stabilizer a.of.1.toExtension).hom
  let fb : B ⟶ D := ExtensionCategory.leftSumMap (𝟙 s.stabilizer)
    ((localizedRawMap r).hom.1 :
      ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶ b.of.1.toExtension)
  let fc : D ⟶ E := (localizedRawMap s).hom.1
  have ha : ExtensionCategory.originalMiddleMap fa =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom :=
    ExtensionCategory.originalMiddleMap_assoc s.stabilizer r.stabilizer a.of.1.toExtension
  have hb : ExtensionCategory.originalMiddleMap fb =
      biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom :=
    (ExtensionCategory.originalMiddleMap_leftSum (𝟙 s.stabilizer)
      ((localizedRawMap r).hom.1 :
        ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶ b.of.1.toExtension)).trans
      (congrArg (biprod.map (𝟙 s.stabilizer.of)) (localizedRawMap_beta r))
  have hc : ExtensionCategory.originalMiddleMap fc = s.hom.1.b.hom := localizedRawMap_beta s
  have hbc : ExtensionCategory.originalMiddleMap (fb ≫ fc) =
      biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom :=
    (ExtensionCategory.originalMiddleMap_comp fb fc).trans
      (congrArg₂
        (fun (j : s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B) ⟶
            s.stabilizer.of ⊞ b.of.1.B) (k : s.stabilizer.of ⊞ b.of.1.B ⟶ c.of.1.B) => j ≫ k)
        hb hc)
  exact (ExtensionCategory.originalMiddleMap_comp fa (fb ≫ fc)).trans
    (congrArg₂
      (fun (j : (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.1.B ⟶
          s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B))
        (k : s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B) ⟶ c.of.1.B) => j ≫ k) ha hbc)

private theorem fixed_raw_comp_middle {a b c : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (r.comp s).hom.1.b.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom := by
  let A : FixedTargetExtension C X := leftSumObj (s.stabilizer ⊗ r.stabilizer) a.of.1
  let B : FixedTargetExtension C X := leftSumObj s.stabilizer (leftSumObj r.stabilizer a.of.1)
  let D : FixedTargetExtension C X := leftSumObj s.stabilizer b.of.1
  let E : FixedTargetExtension C X := c.of.1
  let fa : A ⟶ B := (leftSumAssocIso s.stabilizer r.stabilizer a.of.1).hom
  let fb : B ⟶ D := leftSumMap (𝟙 s.stabilizer) r.hom.1
  let fc : D ⟶ E := s.hom.1
  have ha : fa.b.hom = (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.B).hom :=
    leftSumAssocIso_b_hom s.stabilizer r.stabilizer a.of.1
  have hb : fb.b.hom = biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom :=
    leftSumMap_b_hom (𝟙 s.stabilizer) r.hom.1
  have hbc : (fb ≫ fc).b.hom =
      biprod.map (𝟙 s.stabilizer.of) r.hom.1.b.hom ≫ s.hom.1.b.hom :=
    (fixed_middle_comp fb fc).trans (congrArg (· ≫ s.hom.1.b.hom) hb)
  exact (fixed_middle_comp fa (fb ≫ fc)).trans
    (congrArg₂
      (fun (j : (s.stabilizer.of ⊞ r.stabilizer.of) ⊞ a.of.1.B ⟶
          s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B))
        (k : s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.B) ⟶ c.of.1.B) => j ≫ k) ha hbc)

private theorem localizedRawMap_id (a : localizedRows (C := C) X) :
    (localizedRawMap (MonoidalActionCategory.RawHom.id a)).Rel
      (MonoidalActionCategory.RawHom.id (localizedObject a)) := by
  let A : ExtensionCategory C :=
    ExtensionCategory.leftSumObj (𝟙_ (Core C)) a.of.1.toExtension
  let B : ExtensionCategory C := a.of.1.toExtension
  let f : A ⟶ B := (MonoidalActionCategory.RawHom.id (localizedObject a)).hom.1
  let g : A ⟶ B := (localizedRawMap (MonoidalActionCategory.RawHom.id a)).hom.1
  have hf : ExtensionCategory.originalMiddleMap f =
      (biprod.snd : (0 : C) ⊞ a.of.1.B ⟶ a.of.1.B) :=
    ExtensionCategory.originalMiddleMap_unit a.of.1.toExtension
  have hg : ExtensionCategory.originalMiddleMap g =
      (biprod.snd : (0 : C) ⊞ a.of.1.B ⟶ a.of.1.B) :=
    (localizedRawMap_beta (MonoidalActionCategory.RawHom.id a)).trans (leftSumUnitIso_b_hom a.of.1)
  have hFirst : f = g := AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle f g (hf.trans hg.symm)
  have hDen : (MonoidalActionCategory.RawHom.id (localizedObject a)).hom.2 =
      (localizedRawMap (MonoidalActionCategory.RawHom.id a)).hom.2 := rfl
  have hPair : (MonoidalActionCategory.RawHom.id (localizedObject a)).hom =
      (localizedRawMap (MonoidalActionCategory.RawHom.id a)).hom := Prod.ext hFirst hDen
  have hi : (𝟙 (𝟙_ (Core C)) ⊵ₗ (localizedObject a).of) =
      𝟙 ((𝟙_ (Core C)) ⊙ₗ (localizedObject a).of) :=
    MonoidalLeftAction.id_actionHomLeft (𝟙_ (Core C)) (localizedObject a).of
  have hLead : (𝟙 (𝟙_ (Core C)) ⊵ₗ (localizedObject a).of) ≫
      (MonoidalActionCategory.RawHom.id (localizedObject a)).hom =
        (MonoidalActionCategory.RawHom.id (localizedObject a)).hom :=
    (congrArg
      (fun k : ((𝟙_ (Core C)) ⊙ₗ (localizedObject a).of) ⟶
          ((𝟙_ (Core C)) ⊙ₗ (localizedObject a).of) =>
        k ≫ (MonoidalActionCategory.RawHom.id (localizedObject a)).hom) hi).trans
      (Category.id_comp _)
  exact ⟨Iso.refl (𝟙_ (Core C)), hLead.trans hPair⟩

private theorem localizedRawMap_comp {a b c : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    (localizedRawMap (r.comp s)).Rel ((localizedRawMap r).comp (localizedRawMap s)) := by
  let A : ExtensionCategory C :=
    ExtensionCategory.leftSumObj (s.stabilizer ⊗ r.stabilizer) a.of.1.toExtension
  let B : ExtensionCategory C := c.of.1.toExtension
  let f : A ⟶ B := ((localizedRawMap r).comp (localizedRawMap s)).hom.1
  let g : A ⟶ B := (localizedRawMap (r.comp s)).hom.1
  have hf := original_raw_comp_middle r s
  have hg := (localizedRawMap_beta (r.comp s)).trans (fixed_raw_comp_middle r s)
  have hFirst : f = g := AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle f g (hf.trans hg.symm)
  have hDen : ((localizedRawMap r).comp (localizedRawMap s)).hom.2 =
      (localizedRawMap (r.comp s)).hom.2 := rfl
  have hPair : ((localizedRawMap r).comp (localizedRawMap s)).hom =
      (localizedRawMap (r.comp s)).hom := Prod.ext hFirst hDen
  have hi : (𝟙 (s.stabilizer ⊗ r.stabilizer) ⊵ₗ (localizedObject a).of) =
      𝟙 ((s.stabilizer ⊗ r.stabilizer) ⊙ₗ (localizedObject a).of) :=
    MonoidalLeftAction.id_actionHomLeft (s.stabilizer ⊗ r.stabilizer) (localizedObject a).of
  have hLead : (𝟙 (s.stabilizer ⊗ r.stabilizer) ⊵ₗ (localizedObject a).of) ≫
      ((localizedRawMap r).comp (localizedRawMap s)).hom =
        ((localizedRawMap r).comp (localizedRawMap s)).hom :=
    (congrArg
      (fun k : ((s.stabilizer ⊗ r.stabilizer) ⊙ₗ (localizedObject a).of) ⟶
          ((s.stabilizer ⊗ r.stabilizer) ⊙ₗ (localizedObject a).of) =>
        k ≫ ((localizedRawMap r).comp (localizedRawMap s)).hom) hi).trans (Category.id_comp _)
  exact ⟨Iso.refl (s.stabilizer ⊗ r.stabilizer), hLead.trans hPair⟩

/-- The actual underlying localized row functor, preserving every denominator. -/
def localizedForget (X : C) : localizedRows (C := C) X ⥤
    ExtensionCategory.localizedExtensions (C := C) where
  obj := localizedObject
  map f := Quotient.map localizedRawMap (fun _ _ h => by exact localizedRawMap_rel h) f
  map_id a := by exact Quotient.sound (localizedRawMap_id a)
  map_comp f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    exact Quotient.sound (localizedRawMap_comp r s)

/-- Its represented arrows retain the literal stabilized map. -/
theorem localizedForget_map_mk {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (localizedForget X).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (localizedRawMap r) := rfl

/-- The localized forward object retains the exact original denominator. -/
theorem localizedForget_obj_denominator (a : localizedRows (C := C) X) :
    ((localizedForget X).obj a).of.2 = a.of.2 := rfl

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The literal strict fiber of the actual localized target at the same given X. -/
abbrev localizedFiber (X : C) :=
  Functor.Fiber (ExtensionCategory.localizedTarget (C := C)) (⟨X⟩ : QuillenQ C)

/-- The actual stock forgetful functor from that strict fiber. -/
def localizedFiberForget (X : C) : localizedFiber (C := C) X ⥤
    ExtensionCategory.localizedExtensions (C := C) := Functor.Fiber.fiberInclusion

private theorem localizedRawMap_target {a b : localizedRows (C := C) X}
    (r : MonoidalActionCategory.RawHom a b) :
    (ExtensionCategory.target (C := C)).map (localizedRawMap r).hom.1 =
      𝟙 (⟨X⟩ : QuillenQ C) := by
  let A : ExtensionCategory C := ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension
  let B : ExtensionCategory C := b.of.1.toExtension
  have hf : (ExtensionCategory.target (C := C)).map (X := A) (Y := B)
      ((forget X).map (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) r.hom.1 : A ⟶ B) =
        𝟙 (⟨X⟩ : QuillenQ C) := inclusion_target r.hom.1
  exact (congrArg
    (fun k : A ⟶ B => (ExtensionCategory.target (C := C)).map (X := A) (Y := B) k)
    (localizedRawMap_positive r)).trans hf

private theorem localizedForget_lift {a b : localizedRows (C := C) X} (f : a ⟶ b) :
    Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) ((localizedForget X).map f) := by
  have hmap : (ExtensionCategory.localizedTarget (C := C)).map ((localizedForget X).map f) =
      𝟙 (⟨X⟩ : QuillenQ C) := by
    refine Quotient.inductionOn f ?_
    intro r
    exact (congrArg
      (fun k : (localizedForget X).obj a ⟶ (localizedForget X).obj b =>
        (ExtensionCategory.localizedTarget (C := C)).map k)
      (localizedForget_map_mk r)).trans
        ((ExtensionCategory.localizedTargetMap_mk (localizedRawMap r)).trans
          (localizedRawMap_target r))
  have hCanon : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      ((ExtensionCategory.localizedTarget (C := C)).map ((localizedForget X).map f))
      ((localizedForget X).map f) := .map ((localizedForget X).map f)
  exact hmap ▸ hCanon

/-- Forward the actual localized given-X rows into the literal strict fiber. -/
def localizedFiberFunctor (X : C) : localizedRows (C := C) X ⥤ localizedFiber (C := C) X where
  obj a := ⟨(localizedForget X).obj a, rfl⟩
  map f := ⟨(localizedForget X).map f, by exact localizedForget_lift f⟩
  map_id a := by
    apply (Functor.Fiber.fiberInclusion : localizedFiber (C := C) X ⥤ _).map_injective
    exact (localizedForget X).map_id a
  map_comp f g := by
    apply (Functor.Fiber.fiberInclusion : localizedFiber (C := C) X ⥤ _).map_injective
    exact (localizedForget X).map_comp f g

/-- The fiber forward map is the actual stabilized row functor after forgetting. -/
theorem localizedFiberFunctor_forget :
    localizedFiberFunctor (C := C) X ⋙ localizedFiberForget X = localizedForget X := rfl

/-- It keeps the exact given quotient and the original denominator. -/
theorem localizedFiberFunctor_obj (a : localizedRows (C := C) X) :
    (localizedFiberForget X).obj ((localizedFiberFunctor X).obj a) =
      (⟨(a.of.1.toExtension, a.of.2)⟩ : ExtensionCategory.localizedExtensions (C := C)) := rfl

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

private theorem localizedRawMap_reflects_rel {a b : localizedRows (C := C) X}
    {r s : MonoidalActionCategory.RawHom a b}
    (h : (localizedRawMap r).Rel (localizedRawMap s)) : r.Rel s := by
  obtain ⟨e, he⟩ := h
  let A : ExtensionCategory C := ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension
  let B : ExtensionCategory C := b.of.1.toExtension
  have hh : ExtensionCategory.originalMiddleMap
      (ExtensionCategory.leftSumMap e.hom (𝟙 a.of.1.toExtension) ≫
        ((localizedRawMap s).hom.1 :
          ExtensionCategory.leftSumObj s.stabilizer a.of.1.toExtension ⟶ B)) =
        ExtensionCategory.originalMiddleMap ((localizedRawMap r).hom.1 : A ⟶ B) :=
    congrArg
      (fun k : (r.stabilizer ⊙ₗ (localizedObject a).of) ⟶ (localizedObject b).of =>
        ExtensionCategory.originalMiddleMap (k.1 : A ⟶ B)) he
  have hBeta : biprod.map e.hom.iso.hom (𝟙 a.of.1.B) ≫ s.hom.1.b.hom =
      r.hom.1.b.hom := (original_raw_action_middle r s e.hom).symm.trans
    (hh.trans (localizedRawMap_beta r))
  let f : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 :=
    leftSumMap e.hom (𝟙 a.of.1) ≫ (s.hom.1 : leftSumObj s.stabilizer a.of.1 ⟶ b.of.1)
  let g : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  have hFirst : f = g := AlgebraicKTheory.FixedTargetExtension.hom_ext_of_middle f g
    ((fixed_raw_action_middle r s e.hom).trans hBeta)
  have hDen := congrArg
    (fun k : (r.stabilizer ⊙ₗ (localizedObject a).of) ⟶ (localizedObject b).of => k.2) he
  exact ⟨e, Prod.ext hFirst hDen⟩

private theorem localizedForget_map_injective {a b : localizedRows (C := C) X}
    (f g : a ⟶ b) (h : (localizedForget X).map f = (localizedForget X).map g) : f = g := by
  revert h
  refine Quotient.inductionOn₂ f g ?_
  intro r s h
  apply Quotient.sound
  exact localizedRawMap_reflects_rel ((MonoidalActionCategory.Hom.mk_eq_mk_iff _ _).mp h)

private theorem localizedFiberFunctor_map_injective {a b : localizedRows (C := C) X}
    (f g : a ⟶ b) (h : (localizedFiberFunctor X).map f = (localizedFiberFunctor X).map g) :
    f = g := by
  apply localizedForget_map_injective f g
  exact congrArg
    (fun k : (localizedFiberFunctor X).obj a ⟶ (localizedFiberFunctor X).obj b =>
      (localizedFiberForget X).map k) h

private theorem localized_lift_heq
    {a b : ExtensionCategory.localizedExtensions (C := C)} {R S : QuillenQ C}
    (f : R ⟶ S) (φ : a ⟶ b)
    (h : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C)) f φ) :
    HEq ((ExtensionCategory.localizedTarget (C := C)).map φ) f := by
  cases h
  rfl

private theorem original_lift_heq {a b : ExtensionCategory C} {R S : QuillenQ C}
    (f : R ⟶ S) (φ : a ⟶ b)
    (h : Functor.IsHomLift (ExtensionCategory.target (C := C)) f φ) :
    HEq ((ExtensionCategory.target (C := C)).map φ) f := by
  cases h
  rfl

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

private theorem localizedFiberFunctor_map_surjective {a b : localizedRows (C := C) X}
    (h : (localizedFiberFunctor X).obj a ⟶ (localizedFiberFunctor X).obj b) :
    ∃ f : a ⟶ b, (localizedFiberFunctor X).map f = h := by
  let u : (localizedForget X).obj a ⟶ (localizedForget X).obj b :=
    (localizedFiberForget X).map h
  have hu : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) u := by
    change Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) h.val
    exact h.property
  obtain ⟨r, hr⟩ := MonoidalActionCategory.Hom.exists_rep u
  have hmap : (ExtensionCategory.target (C := C)).map r.hom.1 =
      𝟙 (⟨X⟩ : QuillenQ C) := by
    have hh : (ExtensionCategory.localizedTarget (C := C)).map u =
        𝟙 (⟨X⟩ : QuillenQ C) :=
      eq_of_heq (localized_lift_heq
        (a := (localizedForget X).obj a) (b := (localizedForget X).obj b)
        (R := (⟨X⟩ : QuillenQ C)) (S := (⟨X⟩ : QuillenQ C)) (𝟙 _) u hu)
    exact (ExtensionCategory.localizedTargetMap_mk r).symm.trans
      ((congrArg
        (fun k : (localizedForget X).obj a ⟶ (localizedForget X).obj b =>
          (ExtensionCategory.localizedTarget (C := C)).map k) hr).trans hh)
  let eObj := leftSumObj_toExtension r.stabilizer a.of.1
  let rawOriginal : ExtensionCategory.leftSumObj r.stabilizer a.of.1.toExtension ⟶
      b.of.1.toExtension := r.hom.1
  let ψ : (leftSumObj r.stabilizer a.of.1).toExtension ⟶ b.of.1.toExtension :=
    eqToHom eObj ≫ rawOriginal
  have hψmap : (ExtensionCategory.target (C := C)).map ψ =
      𝟙 (⟨X⟩ : QuillenQ C) := by
    have hc : (ExtensionCategory.target (C := C)).map (eqToHom eObj) =
        𝟙 (⟨X⟩ : QuillenQ C) := by
      rw [eqToHom_map]
      change eqToHom (show (⟨X⟩ : QuillenQ C) = (⟨X⟩ : QuillenQ C) from
        congrArg (ExtensionCategory.target (C := C)).obj eObj) = _
      exact eqToHom_refl _ _
    change (ExtensionCategory.target (C := C)).map (eqToHom eObj ≫ rawOriginal) = _
    rw [CategoryTheory.Functor.map_comp, hc]
    exact (congrArg (𝟙 (⟨X⟩ : QuillenQ C) ≫ ·) hmap).trans (Category.id_comp _)
  have hψ : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) ψ := by
    have hCanon : Functor.IsHomLift (ExtensionCategory.target (C := C))
        ((ExtensionCategory.target (C := C)).map ψ) ψ := .map ψ
    exact hψmap ▸ hCanon
  let v : (fiberInclusion X).obj (leftSumObj r.stabilizer a.of.1) ⟶
      (fiberInclusion X).obj b.of.1 := ⟨ψ, hψ⟩
  let γ := (homEquiv (leftSumObj r.stabilizer a.of.1) b.of.1).symm v
  have hγ : (forget X).map γ = ψ :=
    congrArg
      (fun k : (fiberInclusion X).obj (leftSumObj r.stabilizer a.of.1) ⟶
        (fiberInclusion X).obj b.of.1 => Functor.Fiber.fiberInclusion.map k)
      ((homEquiv (leftSumObj r.stabilizer a.of.1) b.of.1).apply_symm_apply v)
  let rf : MonoidalActionCategory.RawHom a b :=
    { stabilizer := r.stabilizer, hom := (γ, r.hom.2) }
  have hfirst : (localizedRawMap rf).hom.1 = r.hom.1 := by
    change eqToHom eObj.symm ≫ (forget X).map γ = r.hom.1
    rw [hγ]
    change eqToHom eObj.symm ≫ (eqToHom eObj ≫ rawOriginal) = rawOriginal
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hraw : localizedRawMap rf = r := by
    rcases r with ⟨T, k⟩
    apply congrArg
      (fun q : (T ⊙ₗ (localizedObject a).of) ⟶ (localizedObject b).of =>
        (⟨T, q⟩ : MonoidalActionCategory.RawHom (localizedObject a) (localizedObject b)))
    apply Prod.ext
    · exact hfirst
    · rfl
  refine ⟨MonoidalActionCategory.Hom.mk rf, ?_⟩
  apply Functor.Fiber.hom_ext
  exact (congrArg MonoidalActionCategory.Hom.mk hraw).trans hr

/-- The actual forward localized fiber functor has a constructed inverse on every hom-set. -/
def localizedFiberFullyFaithful (X : C) : (localizedFiberFunctor (C := C) X).FullyFaithful where
  preimage {a b} f := Classical.choose
    (show ∃ g : a ⟶ b, (localizedFiberFunctor X).map g = f from by
      exact localizedFiberFunctor_map_surjective f)
  map_preimage {a b} f := by
    exact Classical.choose_spec
      (show ∃ g : a ⟶ b, (localizedFiberFunctor X).map g = f from by
        exact localizedFiberFunctor_map_surjective f)
  preimage_map f := by
    apply localizedFiberFunctor_map_injective
    exact Classical.choose_spec
      (localizedFiberFunctor_map_surjective ((localizedFiberFunctor X).map f))

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Recover the original strict-fiber row, retaining its actual endpoint proof. -/
def originalFiberObject (b : localizedFiber (C := C) X) :
    Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) :=
  ⟨((localizedFiberForget X).obj b).of.1, b.property⟩

/-- The canonical inverse object uses the constructed original reverse row and same denominator. -/
def localizedInverseObject (b : localizedFiber (C := C) X) : localizedRows (C := C) X :=
  ⟨((fromFiber X).obj (originalFiberObject b), ((localizedFiberForget X).obj b).of.2)⟩

/-- The inverse object's denominator is exactly the given original denominator. -/
theorem localizedInverseObject_denominator (b : localizedFiber (C := C) X) :
    (localizedInverseObject b).of.2 = ((localizedFiberForget X).obj b).of.2 := rfl

/-- The reverse object keeps the actual original kernel object. -/
theorem localizedInverseObject_A (b : localizedFiber (C := C) X) :
    (localizedInverseObject b).of.1.A = ((localizedFiberForget X).obj b).of.1.row.X₁ :=
  fromFiberObj_A (originalFiberObject b)

/-- It keeps the original middle object. -/
theorem localizedInverseObject_B (b : localizedFiber (C := C) X) :
    (localizedInverseObject b).of.1.B = ((localizedFiberForget X).obj b).of.1.row.X₂ :=
  fromFiberObj_B (originalFiberObject b)

/-- It keeps the original admissible mono. -/
theorem localizedInverseObject_i (b : localizedFiber (C := C) X) :
    (localizedInverseObject b).of.1.i = ((localizedFiberForget X).obj b).of.1.row.f :=
  fromFiberObj_i (originalFiberObject b)

/-- Only the actual given quotient endpoint is transported to X. -/
theorem localizedInverseObject_p (b : localizedFiber (C := C) X) :
    (localizedInverseObject b).of.1.p = ((localizedFiberForget X).obj b).of.1.row.g ≫
      eqToHom (congrArg QuillenQ.obj (originalFiberObject b).property) :=
  fromFiberObj_p (originalFiberObject b)

private theorem pairInclusion_target {E F : ExtensionCategory C} {s t : Core C}
    (f : E ⟶ F) (d : s ⟶ t) :
    (ExtensionCategory.localizedTarget (C := C)).map
      ((MonoidalActionCategory.inclusion (Core C) (ExtensionCategory C × Core C)).map
        (X := (E, s)) (Y := (F, t)) (f, d)) =
      (ExtensionCategory.target (C := C)).map f := by
  change (ExtensionCategory.target (C := C)).map
    ((ExtensionCategory.leftSumUnitIso E).hom ≫ f) = _
  exact ((ExtensionCategory.target (C := C)).map_comp _ _).trans
    ((congrArg (· ≫ (ExtensionCategory.target (C := C)).map f)
      (ExtensionCategory.leftSumUnitIso_target E)).trans
      (ExtensionCategory.quillen_id_comp (A := (ExtensionCategory.target (C := C)).obj E)
        (B := (ExtensionCategory.target (C := C)).obj F)
        ((ExtensionCategory.target (C := C)).map f)))

/-- The canonical counit uses ordinary action-category inclusion at the GIVEN denominator.
Its raw denominator map is the actual left unitor of that denominator. -/
def localizedCounitComponent (b : localizedFiber (C := C) X) :
    (localizedFiberFunctor X).obj (localizedInverseObject b) ≅ b := by
  let o := originalFiberObject b
  let F := (fromFiber X).obj o
  let eOriginal : F.toExtension ≅ ((localizedFiberForget X).obj b).of.1 :=
    (Functor.Fiber.fiberInclusion :
      Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) ⥤ _).mapIso
        ((fiberCounit X).app o)
  let den := ((localizedFiberForget X).obj b).of.2
  let eLocal : (localizedForget X).obj (localizedInverseObject b) ≅
      (localizedFiberForget X).obj b :=
    (MonoidalActionCategory.inclusion (Core C) (ExtensionCategory C × Core C)).mapIso
      (eOriginal.prod (Iso.refl den))
  have hOriginal : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eOriginal.hom := by
    change Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) ((fiberCounit X).app o).hom.val
    exact ((fiberCounit X).app o).hom.property
  have hOriginalInv : Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eOriginal.inv := by
    change Functor.IsHomLift (ExtensionCategory.target (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) ((fiberCounit X).app o).inv.val
    exact ((fiberCounit X).app o).inv.property
  have hLocal : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eLocal.hom := by
    apply IsHomLift.of_fac' (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eLocal.hom
      ((localizedFiberFunctor X).obj (localizedInverseObject b)).property b.property
    exact (by
      exact (pairInclusion_target eOriginal.hom (𝟙 den)).trans
        (IsHomLift.fac' (ExtensionCategory.target (C := C)) (𝟙 _) eOriginal.hom))
  have hLocalInv : Functor.IsHomLift (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eLocal.inv := by
    apply IsHomLift.of_fac' (ExtensionCategory.localizedTarget (C := C))
      (𝟙 (⟨X⟩ : QuillenQ C)) eLocal.inv
      b.property ((localizedFiberFunctor X).obj (localizedInverseObject b)).property
    exact (by
      exact (pairInclusion_target eOriginal.inv (𝟙 den)).trans
        (IsHomLift.fac' (ExtensionCategory.target (C := C)) (𝟙 _) eOriginal.inv))
  exact
    { hom := ⟨eLocal.hom, hLocal⟩
      inv := ⟨eLocal.inv, hLocalInv⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact eLocal.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact eLocal.inv_hom_id }

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The inverse functor uses the actual reverse row and the derived raw-hom preimage. -/
def localizedFiberInverse (X : C) : localizedFiber (C := C) X ⥤ localizedRows (C := C) X where
  obj := localizedInverseObject
  map {a b} f := (localizedFiberFullyFaithful X).preimage
    ((localizedCounitComponent a).hom ≫ f ≫ (localizedCounitComponent b).inv)
  map_id a := by
    apply (localizedFiberFullyFaithful X).map_injective
    simp only [Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id]
  map_comp f g := by
    apply (localizedFiberFullyFaithful X).map_injective
    simp only [Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse object's denominator is the original one for every fiber object. -/
theorem localizedFiberInverse_obj_denominator (b : localizedFiber (C := C) X) :
    ((localizedFiberInverse X).obj b).of.2 = ((localizedFiberForget X).obj b).of.2 := rfl

/-- Its maps are the uniquely reconstructed actual fixed-row maps between the counit legs. -/
theorem localizedFiberInverse_map_forward {a b : localizedFiber (C := C) X} (f : a ⟶ b) :
    (localizedFiberFunctor X).map ((localizedFiberInverse X).map f) =
      (localizedCounitComponent a).hom ≫ f ≫ (localizedCounitComponent b).inv :=
  (localizedFiberFullyFaithful X).map_preimage _

/-- The actual old fiber counit, at the unchanged denominator, is natural on every map. -/
def localizedFiberCounit (X : C) :
    localizedFiberInverse X ⋙ localizedFiberFunctor X ≅ 𝟭 (localizedFiber (C := C) X) :=
  NatIso.ofComponents localizedCounitComponent (by
    intro a b f
    change (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
        ((localizedCounitComponent a).hom ≫ f ≫ (localizedCounitComponent b).inv)) ≫
        (localizedCounitComponent b).hom = (localizedCounitComponent a).hom ≫ f
    rw [Functor.FullyFaithful.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The unit is the uniquely reconstructed inverse counit on each original localized row. -/
def localizedFiberUnit (X : C) :
    𝟭 (localizedRows (C := C) X) ≅ localizedFiberFunctor X ⋙ localizedFiberInverse X :=
  NatIso.ofComponents
    (fun a => (localizedFiberFullyFaithful X).preimageIso
      (localizedCounitComponent ((localizedFiberFunctor X).obj a)).symm) (by
    intro a b f
    apply (localizedFiberFullyFaithful X).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change (localizedFiberFunctor X).map f ≫
        (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
          (localizedCounitComponent ((localizedFiberFunctor X).obj b)).inv) =
      (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
          (localizedCounitComponent ((localizedFiberFunctor X).obj a)).inv) ≫
        (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
          ((localizedCounitComponent ((localizedFiberFunctor X).obj a)).hom ≫
            (localizedFiberFunctor X).map f ≫
              (localizedCounitComponent ((localizedFiberFunctor X).obj b)).inv))
    rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
      Functor.FullyFaithful.map_preimage]
    simp only [Iso.inv_hom_id_assoc])

/-- The unit and counit satisfy the genuine equivalence triangle at every original row. -/
theorem localizedFiber_triangle (a : localizedRows (C := C) X) :
    (localizedFiberFunctor X).map ((localizedFiberUnit X).hom.app a) ≫
        (localizedFiberCounit X).hom.app ((localizedFiberFunctor X).obj a) =
      𝟙 ((localizedFiberFunctor X).obj a) := by
  change (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
      (localizedCounitComponent ((localizedFiberFunctor X).obj a)).inv) ≫
        (localizedCounitComponent ((localizedFiberFunctor X).obj a)).hom = _
  rw [Functor.FullyFaithful.map_preimage]
  exact (localizedCounitComponent ((localizedFiberFunctor X).obj a)).inv_hom_id

/-- The actual localization of the original given-X rows is equivalent to the literal
strict fiber of the actual localized Quillen target. No equivalence is a premise. -/
def localizedFiberEquivalence (X : C) :
    localizedRows (C := C) X ≌ localizedFiber (C := C) X where
  functor := localizedFiberFunctor X
  inverse := localizedFiberInverse X
  unitIso := localizedFiberUnit X
  counitIso := localizedFiberCounit X
  functor_unitIso_comp a := localizedFiber_triangle a

/-- Every original positive row and arbitrary denominator has its literal forward image. -/
theorem localizedFiberEquivalence_functor_obj (a : localizedRows (C := C) X) :
    (localizedFiberForget X).obj ((localizedFiberEquivalence X).functor.obj a) =
      (⟨(a.of.1.toExtension, a.of.2)⟩ : ExtensionCategory.localizedExtensions (C := C)) := rfl

/-- The inverse uses the original kernel/middle and only the necessary given-X quotient cast. -/
theorem localizedFiberEquivalence_inverse_obj (b : localizedFiber (C := C) X) :
    ((localizedFiberEquivalence X).inverse.obj b).of =
      ((fromFiber X).obj (originalFiberObject b), ((localizedFiberForget X).obj b).of.2) := rfl

end AlgebraicKTheory.FixedTargetExtension

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] {X : C}

attribute [local instance] ExtensionCategory.leftSumAction leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The unit's actual forward image is the inverse of the constructed counit. -/
theorem localizedFiberEquivalence_unit_forward (a : localizedRows (C := C) X) :
    (localizedFiberFunctor X).map ((localizedFiberEquivalence X).unitIso.hom.app a) =
      (localizedCounitComponent ((localizedFiberFunctor X).obj a)).inv := by
  change (localizedFiberFunctor X).map ((localizedFiberFullyFaithful X).preimage
      (localizedCounitComponent ((localizedFiberFunctor X).obj a)).inv) = _
  exact (localizedFiberFullyFaithful X).map_preimage _

/-- At every arbitrary denominator the counit has its actual unit-stabilizer representative.
Its denominator arrow is the left unitor at that denominator, not a reset to the unit. -/
theorem localizedFiberEquivalence_counit_representative (b : localizedFiber (C := C) X) :
    ∃ r : MonoidalActionCategory.RawHom
        ((localizedForget X).obj (localizedInverseObject b)) ((localizedFiberForget X).obj b),
      ∃ hT : r.stabilizer = 𝟙_ (Core C),
        MonoidalActionCategory.Hom.mk r =
          (localizedFiberForget X).map ((localizedFiberEquivalence X).counitIso.hom.app b) ∧
        eqToHom (congrArg
            (fun T : Core C => T ⊗ ((localizedForget X).obj (localizedInverseObject b)).of.2)
            hT.symm) ≫ r.hom.2 = (λ_ ((localizedFiberForget X).obj b).of.2).hom := by
  let o := originalFiberObject b
  let eOriginal :=
    (Functor.Fiber.fiberInclusion :
      Functor.Fiber (ExtensionCategory.target (C := C)) (⟨X⟩ : QuillenQ C) ⥤ _).mapIso
        ((fiberCounit X).app o)
  let den := ((localizedFiberForget X).obj b).of.2
  let r : MonoidalActionCategory.RawHom
      ((localizedForget X).obj (localizedInverseObject b)) ((localizedFiberForget X).obj b) :=
    MonoidalActionCategory.RawHom.ofMap (S := Core C) (eOriginal.hom, 𝟙 den)
  let hT : r.stabilizer = 𝟙_ (Core C) := rfl
  refine ⟨r, hT, rfl, ?_⟩
  let D : Core C := (𝟙_ (Core C)) ⊗ den
  let cast : D ⟶ D := eqToHom (congrArg
    (fun T : Core C => T ⊗ ((localizedForget X).obj (localizedInverseObject b)).of.2) hT.symm)
  have hc : cast = 𝟙 D := eqToHom_refl D _
  have hd : r.hom.2 = (λ_ den).hom ≫ 𝟙 den := rfl
  exact (congrArg (fun k : D ⟶ D => k ≫ r.hom.2) hc).trans
    ((@Category.id_comp (Core C) (inferInstance : Category.{v} (Core C)) D den r.hom.2).trans
      (hd.trans (Category.comp_id (λ_ den).hom)))

end AlgebraicKTheory.FixedTargetExtension

end

/-!
# Cartesian lifting for the actual localized extension target

The source is the existing positive-first SInverse category. A genuine
original row lift is included at the same denominator. Incoming stabilized
maps factor with their original stabilizer and denominator map. The
original target's proved strong cartesianness and monicity supply the
factorization and uniqueness; localized fiberedness is a result.
-/

noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- The direct core-action map remains strongly cartesian over the original target arrow. -/
theorem leftSumMap_isStronglyCartesian {T T' : Core C} (e : T ⟶ T')
    {R S : QuillenQ C} (f : R ⟶ S) {E F : ExtensionCategory C} (φ : E ⟶ F)
    [Functor.IsHomLift (target (C := C)) f φ] :
    Functor.IsStronglyCartesian (target (C := C)) f (leftSumMap e φ) := by
  have hE : (target (C := C)).obj E = R :=
    IsHomLift.domain_eq (a := E) (b := F) (target (C := C)) f φ
  have hF : (target (C := C)).obj F = S :=
    IsHomLift.codomain_eq (a := E) (b := F) (target (C := C)) f φ
  have hDomain : (target (C := C)).obj (leftSumObj T E) = R :=
    (leftSumObj_target T E).trans hE
  have hCodomain : (target (C := C)).obj (leftSumObj T' F) = S :=
    (leftSumObj_target T' F).trans hF
  let _ : Functor.IsHomLift (target (C := C)) f (leftSumMap e φ) := by
    apply IsHomLift.of_fac' (target (C := C)) f (leftSumMap e φ) hDomain hCodomain
    exact (leftSumMap_target e φ).trans
      (IsHomLift.fac' (a := E) (b := F) (target (C := C)) f φ)
  exact target_isStronglyCartesian f (leftSumMap e φ)

/-- Ordinary action-category inclusion preserves the actual pair and denominator. -/
def localizedPairInclusion : ExtensionCategory C × Core C ⥤ localizedExtensions (C := C) :=
  MonoidalActionCategory.inclusion (Core C) (ExtensionCategory C × Core C)

theorem localizedPairInclusion_target {E F : ExtensionCategory C} {s t : Core C}
    (φ : E ⟶ F) (d : s ⟶ t) :
    (localizedTarget (C := C)).map
      ((localizedPairInclusion (C := C)).map (X := (E, s)) (Y := (F, t)) (φ, d)) =
      (target (C := C)).map φ := by
  change (target (C := C)).map ((leftSumUnitIso E).hom ≫ φ) = _
  exact ((target (C := C)).map_comp _ _).trans
    ((congrArg (· ≫ (target (C := C)).map φ) (leftSumUnitIso_target E)).trans
      (quillen_id_comp (A := (target (C := C)).obj E)
        (B := (target (C := C)).obj F) ((target (C := C)).map φ)))

private theorem localizedPairInclusion_lift {E F : ExtensionCategory C} {s t : Core C}
    {R S : QuillenQ C} (f : R ⟶ S) (φ : E ⟶ F) (d : s ⟶ t)
    (h : Functor.IsHomLift (target (C := C)) f φ) :
    Functor.IsHomLift (localizedTarget (C := C)) f
      ((localizedPairInclusion (C := C)).map (X := (E, s)) (Y := (F, t)) (φ, d)) := by
  let _ : Functor.IsHomLift (target (C := C)) f (φ : E ⟶ F) := h
  have hE : (target (C := C)).obj E = R :=
    IsHomLift.domain_eq (a := E) (b := F) (target (C := C)) f φ
  have hF : (target (C := C)).obj F = S :=
    IsHomLift.codomain_eq (a := E) (b := F) (target (C := C)) f φ
  have hDomain : (localizedTarget (C := C)).obj
      ((localizedPairInclusion (C := C)).obj (E, s)) = R := hE
  have hCodomain : (localizedTarget (C := C)).obj
      ((localizedPairInclusion (C := C)).obj (F, t)) = S := hF
  apply IsHomLift.of_fac' (localizedTarget (C := C)) f
    ((localizedPairInclusion (C := C)).map (X := (E, s)) (Y := (F, t)) (φ, d))
    hDomain hCodomain
  exact (localizedPairInclusion_target φ d).trans
    (IsHomLift.fac' (a := E) (b := F) (target (C := C)) f φ)

private theorem originalLift_of_localizedRaw {a b : localizedExtensions (C := C)}
    {R S : QuillenQ C} (f : R ⟶ S) (r : MonoidalActionCategory.RawHom a b)
    (h : Functor.IsHomLift (localizedTarget (C := C)) f
      (MonoidalActionCategory.Hom.mk r)) :
    Functor.IsHomLift (target (C := C)) f
      (r.hom.1 : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1) := by
  let rawOriginal : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let _ : Functor.IsHomLift (localizedTarget (C := C)) f
      (MonoidalActionCategory.Hom.mk r) := h
  have hA : (target (C := C)).obj a.of.1 = R :=
    IsHomLift.domain_eq (a := a) (b := b) (localizedTarget (C := C)) f
      (MonoidalActionCategory.Hom.mk r)
  have hDomain : (target (C := C)).obj (leftSumObj r.stabilizer a.of.1) = R :=
    (leftSumObj_target r.stabilizer a.of.1).trans hA
  have hCodomain : (target (C := C)).obj b.of.1 = S :=
    IsHomLift.codomain_eq (a := a) (b := b) (localizedTarget (C := C)) f
      (MonoidalActionCategory.Hom.mk r)
  apply IsHomLift.of_fac' (target (C := C)) f rawOriginal hDomain hCodomain
  have hMap : (localizedTarget (C := C)).map (MonoidalActionCategory.Hom.mk r) =
      (target (C := C)).map
        (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) rawOriginal :=
    localizedTargetMap_mk r
  exact hMap.symm.trans
    (IsHomLift.fac' (localizedTarget (C := C)) f (MonoidalActionCategory.Hom.mk r))

private theorem localizedLift_of_originalRaw {a b : localizedExtensions (C := C)}
    {R S : QuillenQ C} (f : R ⟶ S) (r : MonoidalActionCategory.RawHom a b)
    (h : Functor.IsHomLift (target (C := C)) f
      (r.hom.1 : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1)) :
    Functor.IsHomLift (localizedTarget (C := C)) f (MonoidalActionCategory.Hom.mk r) := by
  let rawOriginal : leftSumObj r.stabilizer a.of.1 ⟶ b.of.1 := r.hom.1
  let _ : Functor.IsHomLift (target (C := C)) f rawOriginal := h
  have hOriginalDomain : (target (C := C)).obj (leftSumObj r.stabilizer a.of.1) = R :=
    IsHomLift.domain_eq (a := leftSumObj r.stabilizer a.of.1) (b := b.of.1)
      (target (C := C)) f rawOriginal
  have hOriginalCodomain : (target (C := C)).obj b.of.1 = S :=
    IsHomLift.codomain_eq (a := leftSumObj r.stabilizer a.of.1) (b := b.of.1)
      (target (C := C)) f rawOriginal
  have hDomain : (localizedTarget (C := C)).obj a = R :=
    (leftSumObj_target r.stabilizer a.of.1).symm.trans hOriginalDomain
  have hCodomain : (localizedTarget (C := C)).obj b = S := hOriginalCodomain
  apply IsHomLift.of_fac' (localizedTarget (C := C)) f
    (MonoidalActionCategory.Hom.mk r) hDomain hCodomain
  have hMap : (localizedTarget (C := C)).map (MonoidalActionCategory.Hom.mk r) =
      (target (C := C)).map
        (X := leftSumObj r.stabilizer a.of.1) (Y := b.of.1) rawOriginal :=
    localizedTargetMap_mk r
  exact hMap.trans (IsHomLift.fac' (target (C := C)) f rawOriginal)

private theorem raw_comp_ofMap_rel {a b c : localizedExtensions (C := C)}
    (r : MonoidalActionCategory.RawHom a b) (φ : b.of ⟶ c.of) :
    (r.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) φ)).Rel
      (⟨r.stabilizer, r.hom ≫ φ⟩ : MonoidalActionCategory.RawHom a c) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  dsimp only [MonoidalActionCategory.RawHom.comp, MonoidalActionCategory.RawHom.ofMap]
  rw [MonoidalLeftAction.leftUnitor_actionHom]
  simp only [Category.assoc]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

end AlgebraicKTheory.ExtensionCategory

end


noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.ExactCategory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] leftSumAction MonoidalActionCategory.diagonalAction

/-- An actual original row lift remains strongly cartesian after ordinary pair inclusion
at every given denominator. Incoming raw stabilizers and denominator maps are retained. -/
theorem localizedPairInclusion_isStronglyCartesian {R S : QuillenQ C} (f : R ⟶ S)
    {E F : ExtensionCategory C} (φ : E ⟶ F)
    [Functor.IsHomLift (target (C := C)) f φ] (den : Core C) :
    Functor.IsStronglyCartesian (localizedTarget (C := C)) f
      ((localizedPairInclusion (C := C)).map (X := (E, den)) (Y := (F, den)) (φ, 𝟙 den)) := by
  let hStrong : Functor.IsStronglyCartesian (target (C := C)) f φ :=
    target_isStronglyCartesian f φ
  have hLift : Functor.IsHomLift (localizedTarget (C := C)) f
      ((localizedPairInclusion (C := C)).map (X := (E, den)) (Y := (F, den)) (φ, 𝟙 den)) :=
    localizedPairInclusion_lift f φ (𝟙 den) (by infer_instance)
  refine
    { toIsHomLift := hLift
      universal_property' := ?_ }
  intro c g η hη
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep η
  let A : ExtensionCategory C := leftSumObj r.stabilizer c.of.1
  let rawOriginal : A ⟶ F := r.hom.1
  have hOriginal : Functor.IsHomLift (target (C := C)) (g ≫ f) rawOriginal :=
    originalLift_of_localizedRaw (g ≫ f) r hη
  obtain ⟨ζ, hζ, _⟩ :=
    @Functor.IsStronglyCartesian.universal_property
      (QuillenQ C) (ExtensionCategory C)
      _ _
      (target (C := C)) R S E F f φ hStrong
      ((localizedTarget (C := C)).obj c) A g (g ≫ f) rfl rawOriginal hOriginal
  let a := (localizedPairInclusion (C := C)).obj (E, den)
  let targetPair : localizedExtensions (C := C) :=
    (localizedPairInclusion (C := C)).obj (F, den)
  let pairArrow : a.of ⟶ targetPair.of := (φ, 𝟙 den)
  let χr : MonoidalActionCategory.RawHom c a :=
    { stabilizer := r.stabilizer, hom := (ζ, r.hom.2) }
  have hχ : Functor.IsHomLift (localizedTarget (C := C)) g
      (MonoidalActionCategory.Hom.mk χr) :=
    localizedLift_of_originalRaw g χr hζ.1
  have hNorm : (⟨r.stabilizer, χr.hom ≫ (φ, 𝟙 den)⟩ :
      MonoidalActionCategory.RawHom c ((localizedPairInclusion (C := C)).obj (F, den))) =
      r := by
    rcases r with ⟨T, k⟩
    apply congrArg
      (fun q : (T ⊙ₗ c.of) ⟶ (F, den) =>
        (⟨T, q⟩ : MonoidalActionCategory.RawHom c
          ((localizedPairInclusion (C := C)).obj (F, den))))
    apply Prod.ext
    · exact hζ.2
    · exact Category.comp_id _
  have hfac : MonoidalActionCategory.Hom.mk χr ≫
      (localizedPairInclusion (C := C)).map (X := (E, den)) (Y := (F, den)) (φ, 𝟙 den) =
        MonoidalActionCategory.Hom.mk r :=
    (Quotient.sound
      (raw_comp_ofMap_rel (a := c) (b := a) (c := targetPair) χr pairArrow)).trans
      (congrArg MonoidalActionCategory.Hom.mk hNorm)
  refine ⟨MonoidalActionCategory.Hom.mk χr, ⟨hχ, hfac⟩, ?_⟩
  intro σ hσ
  rcases hσ with ⟨_hσ, heq⟩
  revert heq
  refine Quotient.inductionOn σ ?_
  intro r' heq
  have hNormalizedEq :
      MonoidalActionCategory.Hom.mk
          (⟨r'.stabilizer, r'.hom ≫ (φ, 𝟙 den)⟩ :
            MonoidalActionCategory.RawHom c
              ((localizedPairInclusion (C := C)).obj (F, den))) =
        MonoidalActionCategory.Hom.mk r :=
    (Quotient.sound
      (raw_comp_ofMap_rel (a := c) (b := a) (c := targetPair) r' pairArrow)).symm.trans heq
  obtain ⟨e, he⟩ := (MonoidalActionCategory.Hom.mk_eq_mk_iff _ _).mp hNormalizedEq
  have hFirst : leftSumMap e.hom (𝟙 c.of.1) ≫ r.hom.1 = r'.hom.1 ≫ φ :=
    congrArg
      (fun q : (r'.stabilizer ⊙ₗ c.of) ⟶ (F, den) => q.1) he
  apply Quotient.sound
  refine ⟨e, ?_⟩
  apply Prod.ext
  · let _ : Mono φ := morphism_mono φ
    apply (cancel_mono φ).mp
    change (leftSumMap e.hom (𝟙 c.of.1) ≫ ζ) ≫ φ = r'.hom.1 ≫ φ
    exact (Category.assoc _ _ _).trans
      ((congrArg (leftSumMap e.hom (𝟙 c.of.1) ≫ ·) hζ.2).trans hFirst)
  · let D : Core C := r'.stabilizer ⊗ c.of.2
    have hDen : (e.hom ⊵ₗ c.of ≫ χr.hom).2 =
        (r'.hom.2 : D ⟶ den) ≫ 𝟙 den :=
      congrArg (fun q : (r'.stabilizer ⊙ₗ c.of) ⟶ (F, den) => q.2) he
    exact hDen.trans (Category.comp_id (r'.hom.2 : D ⟶ den))

/-- Every incoming original Q arrow has a localized strong cartesian lift with
exactly the given target denominator. -/
theorem localizedTarget_exists_strongLift (b : localizedExtensions (C := C))
    (R : QuillenQ C) (f : R ⟶ (localizedTarget (C := C)).obj b) :
    ∃ (a : localizedExtensions (C := C)) (φ : a ⟶ b),
      Functor.IsStronglyCartesian (localizedTarget (C := C)) f φ ∧ a.of.2 = b.of.2 := by
  let _ : Functor.IsPreFibered (target (C := C)) := target_isPreFibered
  obtain ⟨E, φ, hφ⟩ :=
    Functor.IsPreFibered.exists_isCartesian' (p := target (C := C))
      (a := b.of.1) f
  let _ : Functor.IsHomLift (target (C := C)) f (φ : E ⟶ b.of.1) := hφ.toIsHomLift
  exact
    ⟨(localizedPairInclusion (C := C)).obj (E, b.of.2),
      (localizedPairInclusion (C := C)).map
        (X := (E, b.of.2)) (Y := (b.of.1, b.of.2)) (φ, 𝟙 b.of.2),
      localizedPairInclusion_isStronglyCartesian f φ b.of.2, rfl⟩

/-- The actual localized target is fibered. The stock strong-lift constructor
proves composition closure from these constructed lifts. -/
theorem localizedTarget_isFibered : Functor.IsFibered (localizedTarget (C := C)) := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro b R f
  obtain ⟨a, φ, hφ, _hden⟩ := localizedTarget_exists_strongLift b R f
  exact ⟨a, φ, hφ⟩

end AlgebraicKTheory.ExtensionCategory

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.ExtensionCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The existing normalized middle-map inverse calculation for the actual extension Iso. -/
public theorem homNormalization_iso_inv_middle {E G : ExtensionCategory C} (e : E ≅ G)
    (b : E.row.X₂ ≅ G.row.X₂)
    (hb : (homNormalization e.hom).hom.2.hom = b.hom) :
    (homNormalization e.inv).hom.2.hom = b.inv :=
  middle_inverse_of_iso e b hb

end AlgebraicKTheory.ExtensionCategory

end

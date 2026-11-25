/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexFilteredColimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexQuotient
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Colimit stability of weak equivalences between Kan complexes

Weak equivalences between Kan complexes are stable under filtered colimits whose indexing-category
universes are no larger than the simplicial universe. For a well-ordered shape without a largest
element, this also gives stability under transfinite composition: the no-maximum hypothesis makes
every intermediate object Kan before an identity map is used.

The auxiliary varying-basepoint homotopy functors and the functor-category argument for cartesian
squares of types are deliberately private.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open scoped Simplicial

namespace SSet

namespace WColimitAux

variable {B : SSet.{u}} (A : B.Subcomplex)

private noncomputable def cylinderZero :
    A.quotient ⟶ (A.prod (⊤ : Δ[1].Subcomplex)).quotient :=
  A.descQuotient (ι₀ ≫ (A.prod ⊤).toQuotient) (A.prod ⊤).quotient₀ (by
    rw [← Category.assoc]
    apply (A.prod (⊤ : Δ[1].Subcomplex)).comp_toQuotient_eq_const
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, Subcomplex.image_comp, Subcomplex.image_top]
    rintro n b h
    simp only [Subfunctor.range_ι] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact ⟨ha, by simp⟩)

private noncomputable def cylinderOne :
    A.quotient ⟶ (A.prod (⊤ : Δ[1].Subcomplex)).quotient :=
  A.descQuotient (ι₁ ≫ (A.prod ⊤).toQuotient) (A.prod ⊤).quotient₀ (by
    rw [← Category.assoc]
    apply (A.prod (⊤ : Δ[1].Subcomplex)).comp_toQuotient_eq_const
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, Subcomplex.image_comp, Subcomplex.image_top]
    rintro n b h
    simp only [Subfunctor.range_ι] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact ⟨ha, by simp⟩)

@[reassoc (attr := simp)]
private lemma toQuotient_cylinderZero :
    A.toQuotient ≫ cylinderZero A = ι₀ ≫ (A.prod ⊤).toQuotient := by
  simp [cylinderZero]

@[reassoc (attr := simp)]
private lemma toQuotient_cylinderOne :
    A.toQuotient ≫ cylinderOne A = ι₁ ≫ (A.prod ⊤).toQuotient := by
  simp [cylinderOne]

@[simp]
private lemma cylinderZero_quotient₀ :
    (cylinderZero A).app _ A.quotient₀ = (A.prod ⊤).quotient₀ := by
  simp [cylinderZero]

@[simp]
private lemma cylinderOne_quotient₀ :
    (cylinderOne A).app _ A.quotient₀ = (A.prod ⊤).quotient₀ := by
  simp [cylinderOne]

private noncomputable def varyingπ : SSet.{u} ⥤ Type u :=
  coequalizer (coyoneda.map (cylinderZero A).op) (coyoneda.map (cylinderOne A).op)

private noncomputable def classMap :
    coyoneda.obj (op A.quotient) ⟶ varyingπ A :=
  coequalizer.π _ _

@[reassoc]
private lemma classMap_condition :
    coyoneda.map (cylinderZero A).op ≫ classMap A =
      coyoneda.map (cylinderOne A).op ≫ classMap A :=
  coequalizer.condition _ _

private noncomputable def varyingπCofork (X : SSet.{u}) :
    Cofork ((coyoneda.map (cylinderZero A).op).app X)
      ((coyoneda.map (cylinderOne A).op).app X) :=
  Cofork.ofπ (classMap A |>.app X) (congr_app (classMap_condition A) X)

private noncomputable def varyingπCoforkIsColimit (X : SSet.{u}) :
    IsColimit (varyingπCofork A X) :=
  isColimitCoforkMapOfIsColimit ((CategoryTheory.evaluation _ _).obj X) _
    (coequalizerIsCoequalizer _ _)

private lemma classMap_surjective {X : SSet.{u}} :
    Function.Surjective ((classMap A).app X) := by
  rw [← epi_iff_surjective]
  exact Cofork.IsColimit.epi (varyingπCoforkIsColimit A X)

private def zeroSimplexYoneda :
    coyoneda.obj (op Δ[0]) ⟶ SSet.evaluation.obj (op ⦋0⦌) where
  app X := ↾yonedaEquiv
  naturality X Y f := by
    ext g
    exact yonedaEquiv_comp g f

private noncomputable def basepointMap :
    varyingπ A ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  coequalizer.desc
    (coyoneda.map (const A.quotient₀ : Δ[0] ⟶ A.quotient).op ≫
      zeroSimplexYoneda)
    (by
      simp only [← Functor.map_comp_assoc, ← op_comp, const_comp,
        cylinderZero_quotient₀, cylinderOne_quotient₀])

@[simp]
private lemma basepointMap_classMap {X : SSet.{u}} (f : A.quotient ⟶ X) :
    (basepointMap A).app X ((classMap A).app X f) = f.app _ A.quotient₀ := by
  rw [← NatTrans.comp_app_apply]
  erw [Limits.coequalizer.π_desc]
  simp [zeroSimplexYoneda, yonedaEquiv_const]

private abbrev RelativeClass {X : SSet.{u}} (x : X _⦋0⦌) :=
  RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

private lemma relative_boundary_constant {X : SSet.{u}} {x : X _⦋0⦌}
    (p : RelativeMorphism A (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    A.ι ≫ p.map = const x := by
  simpa only [Subcomplex.ofSimplex_ι, comp_const] using p.comm

private lemma pointed_fac {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩ :
      A.toSSet ⟶ (Subcomplex.ofSimplex x : SSet)) ≫
        (const ⟨f.app _ x, Subcomplex.mem_ofSimplex_obj (f.app _ x)⟩ :
          (Subcomplex.ofSimplex x : SSet) ⟶
            (Subcomplex.ofSimplex (f.app _ x) : SSet)) =
      (const ⟨f.app _ x, Subcomplex.mem_ofSimplex_obj (f.app _ x)⟩ :
        A.toSSet ⟶ (Subcomplex.ofSimplex (f.app _ x) : SSet)) := by
  apply comp_const

private noncomputable def encodeRelative {X : SSet.{u}} (x : X _⦋0⦌) :
    RelativeClass A x → (varyingπ A).obj X :=
  Quot.lift
    (fun p ↦ (classMap A).app X
      (A.descQuotient p.map x (relative_boundary_constant A p)))
    (by
      rintro p q ⟨H⟩
      let descendedCylinder : (A.prod (⊤ : Δ[1].Subcomplex)).quotient ⟶ X :=
        (A.prod _).descQuotient H.h x (by
          rw [← cancel_epi (Subcomplex.prodIso A (⊤ : Δ[1].Subcomplex)).inv]
          have hι : (Subcomplex.prodIso A (⊤ : Δ[1].Subcomplex)).inv ≫
              Subcomplex.ι _ =
                (A.toSSet ◁ (⊤ : Δ[1].Subcomplex).ι) ≫
                  (A.ι ▷ Δ[1]) := rfl
          rw [reassoc_of% hι, H.rel]
          rfl)
      have hp : A.descQuotient p.map x (relative_boundary_constant A p) =
          cylinderZero A ≫ descendedCylinder := by
        apply A.quotient_hom_ext <;> simp [descendedCylinder]
      have hq : A.descQuotient q.map x (relative_boundary_constant A q) =
          cylinderOne A ≫ descendedCylinder := by
        apply A.quotient_hom_ext <;> simp [descendedCylinder]
      rw [hp, hq]
      exact ConcreteCategory.congr_hom (congr_app (classMap_condition A) X)
        descendedCylinder)

private lemma encodeRelative_mk {X : SSet.{u}} {x : X _⦋0⦌}
    (p : RelativeMorphism A (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    encodeRelative A x p.homotopyClass =
      (classMap A).app X
        (A.descQuotient p.map x (relative_boundary_constant A p)) := rfl

private noncomputable def encode {X : SSet.{u}} :
    (Σ x : X _⦋0⦌, RelativeClass A x) → (varyingπ A).obj X
  | ⟨x, p⟩ => encodeRelative A x p

private noncomputable def decodeRepresentative {X : SSet.{u}}
    (f : A.quotient ⟶ X) : Σ x : X _⦋0⦌, RelativeClass A x :=
  ⟨f.app _ A.quotient₀,
    RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩

private lemma decodeRepresentative_eq {X : SSet.{u}} (f : A.quotient ⟶ X)
    (x : X _⦋0⦌) (hx : f.app _ A.quotient₀ = x) :
    decodeRepresentative A f =
      ⟨x, RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩ := by
  subst x
  rfl

private noncomputable def decode (X : SSet.{u}) :
    (varyingπ A).obj X → Σ x : X _⦋0⦌, RelativeClass A x :=
  Cofork.IsColimit.desc (varyingπCoforkIsColimit A X) (↾decodeRepresentative A) (by
    apply ConcreteCategory.hom_ext
    intro f
    dsimp at f ⊢
    let x := f.app _ (A.prod (⊤ : Δ[1].Subcomplex)).quotient₀
    rw [decodeRepresentative_eq A _ x (by simp [x]),
      decodeRepresentative_eq A _ x (by simp [x])]
    simp only [toQuotient_cylinderZero_assoc, toQuotient_cylinderOne_assoc,
      Sigma.mk.injEq, heq_eq_eq, true_and, x]
    apply RelativeMorphism.Homotopy.eq
    exact
      { h := (A.prod (⊤ : Δ[1].Subcomplex)).toQuotient ≫ f
        h₀ := by simp
        h₁ := by simp
        rel := by
          have hι : (Subcomplex.prodIso A (⊤ : Δ[1].Subcomplex)).inv ≫
              Subcomplex.ι _ =
                (A.toSSet ◁ (⊤ : Δ[1].Subcomplex).ι) ≫
                  (A.ι ▷ Δ[1]) := rfl
          rw [← cancel_epi (A.toSSet ◁ (Subcomplex.topIso Δ[1]).hom),
            Subcomplex.topIso_hom, ← reassoc_of% hι]
          simp })

private lemma decode_classMap {X : SSet.{u}} (f : A.quotient ⟶ X)
    (x : X _⦋0⦌) (hx : f.app _ A.quotient₀ = x) :
    decode A X ((classMap A).app X f) =
      ⟨x, RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩ := by
  have hdesc : (classMap A).app X ≫ ↾(decode A X) = ↾(decodeRepresentative A) :=
    by
      dsimp [decode, varyingπCofork, classMap]
      exact Cofork.IsColimit.π_desc' (varyingπCoforkIsColimit A X) _ _
  exact (ConcreteCategory.congr_hom hdesc f).trans (decodeRepresentative_eq A f x hx)

@[simp]
private lemma encode_decode {X : SSet.{u}} (z : (varyingπ A).obj X) :
    encode A (decode A X z) = z := by
  obtain ⟨f, rfl⟩ := classMap_surjective A z
  rw [decode_classMap A f _ rfl, encode, encodeRelative_mk]
  congr 1
  apply A.quotient_hom_ext <;> simp

private noncomputable def varyingπEquiv (X : SSet.{u}) :
    (varyingπ A).obj X ≃ Σ x : X _⦋0⦌, RelativeClass A x where
  toFun := decode A X
  invFun := encode A
  left_inv := encode_decode A
  right_inv := by
    rintro ⟨x, p⟩
    obtain ⟨p, rfl⟩ := p.eq_homotopyClass
    rw [encode, encodeRelative_mk, decode_classMap A _ x (by simp)]
    simp

private lemma varyingπ_map_encode {X Y : SSet.{u}} {x : X _⦋0⦌}
    (a : RelativeClass A x) (f : X ⟶ Y) :
    (varyingπ A).map f (encode A ⟨x, a⟩) =
      encode A ⟨f.app _ x,
        a.postcomp (ψ := const ⟨f.app _ x, Subcomplex.mem_ofSimplex_obj _⟩)
          (RelativeMorphism.ofSimplex₀ f x (f.app _ x) rfl) (pointed_fac A f x)⟩ := by
  obtain ⟨p, rfl⟩ := a.eq_homotopyClass
  rw [encode, encodeRelative_mk]
  erw [RelativeMorphism.postcomp_homotopyClass]
  rw [encode, encodeRelative_mk]
  rw [← NatTrans.naturality_apply]
  congr 1
  change A.descQuotient p.map x _ ≫ f =
    A.descQuotient
      (p.comp (RelativeMorphism.ofSimplex₀ f x (f.app _ x) rfl)
        (pointed_fac A f x)).map (f.app _ x) _
  apply A.quotient_hom_ext
  · rw [← Category.assoc, A.toQuotient_descQuotient,
      A.toQuotient_descQuotient]
    rfl
  · simp

private lemma basepointMap_encode {X : SSet.{u}} {x : X _⦋0⦌}
    (a : RelativeClass A x) :
    (basepointMap A).app X (encode A ⟨x, a⟩) = x := by
  obtain ⟨p, rfl⟩ := a.eq_homotopyClass
  exact (basepointMap_classMap A
    (A.descQuotient p.map x (relative_boundary_constant A p))).trans (by simp)

private noncomputable def positiveπFunctor (n : ℕ) : SSet.{u} ⥤ Type u :=
  varyingπ (boundary (n + 1))

private noncomputable def positiveπEquiv (n : ℕ) (X : SSet.{u}) :
    (positiveπFunctor n).obj X ≃ Σ x : X _⦋0⦌, KanComplex.π (n + 1) X x :=
  varyingπEquiv _ X

private noncomputable def positiveπToVertices (n : ℕ) :
    positiveπFunctor.{u} n ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  basepointMap _

private lemma positiveπ_map_equiv_symm {n : ℕ} {X Y : SSet.{u}}
    {x : X _⦋0⦌} (a : KanComplex.π (n + 1) X x) (f : X ⟶ Y) :
    (positiveπFunctor n).map f ((positiveπEquiv n X).symm ⟨x, a⟩) =
      (positiveπEquiv n Y).symm
        ⟨f.app _ x, KanComplex.π.map (x := x) f rfl (n + 1) a⟩ := by
  exact varyingπ_map_encode _ a f

private lemma positiveπToVertices_equiv_symm {n : ℕ} {X : SSet.{u}}
    {x : X _⦋0⦌} (a : KanComplex.π (n + 1) X x) :
    (positiveπToVertices n).app X ((positiveπEquiv n X).symm ⟨x, a⟩) = x :=
  basepointMap_encode _ a

private noncomputable def positiveπArrow (n : ℕ) : SSet.{u} ⥤ Arrow (Type u) where
  obj X := Arrow.mk ((positiveπToVertices n).app X)
  map f := Arrow.homMk ((positiveπFunctor n).map f) (f.app _)

private noncomputable instance preservesColimitsProperty_closedUnderColimits
    {K K' D C : Type*} [Category* K] [Category* K'] [Category* D] [Category* C]
    [HasColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (ObjectProperty.preservesColimitsOfShape K : ObjectProperty (D ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesColimitsOfShape K h.diag.flip :=
      ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨evaluationJointlyReflectsColimits _
        (fun k' ↦ isColimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents (fun d ↦
        (colimit.isColimit (h.diag.flip.obj d)).coconePointUniqueUpToIso
          (isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj d) h.isColimit))
    exact preservesColimitsOfShape_of_natIso e

section FilteredFunctor

variable {J : Type u} [Category.{u} J] [IsFiltered J]

private noncomputable instance π₀Functor_preservesFiltered :
    PreservesColimitsOfShape J π₀Functor.{u} := by
  change (ObjectProperty.preservesColimitsOfShape J :
    ObjectProperty (SSet.{u} ⥤ Type u)) SSet.coforkπ₀Functor.{u}.pt
  apply (ObjectProperty.preservesColimitsOfShape J).prop_of_isColimit
    SSet.isColimitCoforkπ₀Functor.{u}
  rintro (_ | _) <;> dsimp <;> infer_instance

private noncomputable instance varyingπ_preservesFiltered [B.Finite] :
    PreservesColimitsOfShape J (varyingπ A) := by
  apply (ObjectProperty.preservesColimitsOfShape J).prop_of_isColimit
    (coequalizerIsCoequalizer
      (coyoneda.map (cylinderZero A).op) (coyoneda.map (cylinderOne A).op))
  rintro (_ | _) <;> dsimp <;> infer_instance

private noncomputable instance positiveπFunctor_preservesFiltered (n : ℕ) :
    PreservesColimitsOfShape J (positiveπFunctor.{u} n) := by
  dsimp only [positiveπFunctor]
  infer_instance

private noncomputable instance positiveπArrow_preservesFiltered (n : ℕ) :
    PreservesColimitsOfShape J (positiveπArrow.{u} n) where
  preservesColimit {F} := ⟨fun {c} hc ↦ ⟨by
    apply Comma.fstSndJointlyReflectColimit
    · exact isColimitOfPreserves (positiveπFunctor n) hc
    · exact isColimitOfPreserves (SSet.evaluation.obj (op ⦋0⦌)) hc⟩⟩

private def cartesianTypeArrows : MorphismProperty (Arrow (Type u)) :=
  fun X Y e ↦ IsPullback e.left X.hom Y.hom e.right

private noncomputable instance cartesianTypeArrows_stable :
    cartesianTypeArrows.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    let top : X₁ ⋙ Arrow.leftFunc ⟶ X₂ ⋙ Arrow.leftFunc :=
      Functor.whiskerRight f Arrow.leftFunc
    let left : X₁ ⋙ Arrow.leftFunc ⟶ X₁ ⋙ Arrow.rightFunc :=
      Functor.whiskerLeft X₁ Arrow.leftToRight
    let right : X₂ ⋙ Arrow.leftFunc ⟶ X₂ ⋙ Arrow.rightFunc :=
      Functor.whiskerLeft X₂ Arrow.leftToRight
    let bottom : X₁ ⋙ Arrow.rightFunc ⟶ X₂ ⋙ Arrow.rightFunc :=
      Functor.whiskerRight f Arrow.rightFunc
    have hsq : IsPullback top left right bottom := by
      apply IsPullback.of_forall_isPullback_app
      intro j
      change IsPullback (f.app j).left (X₁.obj j).hom
        (X₂.obj j).hom (f.app j).right
      exact hf j
    have hcol := hsq.map (colim : (J ⥤ Type u) ⥤ Type u)
    let e₁ : colimit (X₁ ⋙ Arrow.leftFunc) ≅ c₁.pt.left :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitOfPreserves Arrow.leftFunc hc₁)
    let e₂ : colimit (X₂ ⋙ Arrow.leftFunc) ≅ c₂.pt.left :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitOfPreserves Arrow.leftFunc hc₂)
    let e₃ : colimit (X₁ ⋙ Arrow.rightFunc) ≅ c₁.pt.right :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitOfPreserves Arrow.rightFunc hc₁)
    let e₄ : colimit (X₂ ⋙ Arrow.rightFunc) ≅ c₂.pt.right :=
      (colimit.isColimit _).coconePointUniqueUpToIso
        (isColimitOfPreserves Arrow.rightFunc hc₂)
    have he₁ (j : J) :
        colimit.ι (X₁ ⋙ Arrow.leftFunc) j ≫ e₁.hom = (c₁.ι.app j).left := by
      change (colimit.cocone (X₁ ⋙ Arrow.leftFunc)).ι.app j ≫
        ((colimit.isColimit _).coconePointUniqueUpToIso
          (isColimitOfPreserves Arrow.leftFunc hc₁)).hom =
        (Arrow.leftFunc.mapCocone c₁).ι.app j
      exact IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (X₁ ⋙ Arrow.leftFunc))
        (isColimitOfPreserves Arrow.leftFunc hc₁) j
    have he₂ (j : J) :
        colimit.ι (X₂ ⋙ Arrow.leftFunc) j ≫ e₂.hom = (c₂.ι.app j).left := by
      change (colimit.cocone (X₂ ⋙ Arrow.leftFunc)).ι.app j ≫
        ((colimit.isColimit _).coconePointUniqueUpToIso
          (isColimitOfPreserves Arrow.leftFunc hc₂)).hom =
        (Arrow.leftFunc.mapCocone c₂).ι.app j
      exact IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (X₂ ⋙ Arrow.leftFunc))
        (isColimitOfPreserves Arrow.leftFunc hc₂) j
    have he₃ (j : J) :
        colimit.ι (X₁ ⋙ Arrow.rightFunc) j ≫ e₃.hom = (c₁.ι.app j).right := by
      change (colimit.cocone (X₁ ⋙ Arrow.rightFunc)).ι.app j ≫
        ((colimit.isColimit _).coconePointUniqueUpToIso
          (isColimitOfPreserves Arrow.rightFunc hc₁)).hom =
        (Arrow.rightFunc.mapCocone c₁).ι.app j
      exact IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (X₁ ⋙ Arrow.rightFunc))
        (isColimitOfPreserves Arrow.rightFunc hc₁) j
    have he₄ (j : J) :
        colimit.ι (X₂ ⋙ Arrow.rightFunc) j ≫ e₄.hom = (c₂.ι.app j).right := by
      change (colimit.cocone (X₂ ⋙ Arrow.rightFunc)).ι.app j ≫
        ((colimit.isColimit _).coconePointUniqueUpToIso
          (isColimitOfPreserves Arrow.rightFunc hc₂)).hom =
        (Arrow.rightFunc.mapCocone c₂).ι.app j
      exact IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (X₂ ⋙ Arrow.rightFunc))
        (isColimitOfPreserves Arrow.rightFunc hc₂) j
    apply hcol.of_iso e₁ e₂ e₃ e₄
    · apply (colimit.isColimit (X₁ ⋙ Arrow.leftFunc)).hom_ext
      intro j
      change colimit.ι (X₁ ⋙ Arrow.leftFunc) j ≫ colim.map top ≫ e₂.hom =
        colimit.ι (X₁ ⋙ Arrow.leftFunc) j ≫ e₁.hom ≫ φ.left
      rw [colimit.ι_map_assoc]
      rw [he₂]
      conv_rhs => rw [← Category.assoc, he₁]
      change (f.app j).left ≫ (c₂.ι.app j).left =
        (c₁.ι.app j).left ≫ φ.left
      exact congrArg (fun k ↦ k.left) (hφ j).symm
    · apply (colimit.isColimit (X₁ ⋙ Arrow.leftFunc)).hom_ext
      intro j
      change colimit.ι (X₁ ⋙ Arrow.leftFunc) j ≫ colim.map left ≫ e₃.hom =
        colimit.ι (X₁ ⋙ Arrow.leftFunc) j ≫ e₁.hom ≫ c₁.pt.hom
      rw [colimit.ι_map_assoc, he₃]
      conv_rhs => rw [← Category.assoc, he₁]
      exact (c₁.ι.app j).w.symm
    · apply (colimit.isColimit (X₂ ⋙ Arrow.leftFunc)).hom_ext
      intro j
      change colimit.ι (X₂ ⋙ Arrow.leftFunc) j ≫ colim.map right ≫ e₄.hom =
        colimit.ι (X₂ ⋙ Arrow.leftFunc) j ≫ e₂.hom ≫ c₂.pt.hom
      rw [colimit.ι_map_assoc, he₄]
      conv_rhs => rw [← Category.assoc, he₂]
      exact (c₂.ι.app j).w.symm
    · apply (colimit.isColimit (X₁ ⋙ Arrow.rightFunc)).hom_ext
      intro j
      change colimit.ι (X₁ ⋙ Arrow.rightFunc) j ≫ colim.map bottom ≫ e₄.hom =
        colimit.ι (X₁ ⋙ Arrow.rightFunc) j ≫ e₃.hom ≫ φ.right
      rw [colimit.ι_map_assoc, he₄]
      conv_rhs => rw [← Category.assoc, he₃]
      change (f.app j).right ≫ (c₂.ι.app j).right =
        (c₁.ι.app j).right ≫ φ.right
      exact congrArg (fun k ↦ k.right) (hφ j).symm

private def naiveW : MorphismProperty SSet.{u} :=
  (MorphismProperty.isomorphisms _).inverseImage π₀Functor ⊓
    ⨅ n : ℕ, cartesianTypeArrows.inverseImage (positiveπArrow.{u} n)

private lemma W_iff_naiveW {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) : KanComplex.W f ↔ naiveW f := by
  rw [KanComplex.W_iff, naiveW, MorphismProperty.inf_iff,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    isIso_iff_bijective, MorphismProperty.iInf_iff]
  refine and_congr Iff.rfl (forall_congr' fun n ↦ ?_)
  rw [MorphismProperty.inverseImage_iff]
  change (∀ x : X _⦋0⦌,
      Function.Bijective (KanComplex.π.map (x := x) f rfl (n + 1))) ↔
    IsPullback ((positiveπFunctor n).map f) ((positiveπToVertices n).app X)
      ((positiveπToVertices n).app Y) (f.app _)
  rw [Types.isPullback_iff]
  constructor
  · intro hπ
    refine ⟨(positiveπToVertices n).naturality f, ?_, ?_⟩
    · intro a b hab
      obtain ⟨⟨x, p⟩, rfl⟩ := (positiveπEquiv n X).symm.surjective a
      obtain ⟨⟨y, q⟩, rfl⟩ := (positiveπEquiv n X).symm.surjective b
      have hxy : x = y := by
        simpa only [positiveπToVertices_equiv_symm] using hab.2
      subst y
      have hfun : (positiveπEquiv n Y).symm
          ⟨f.app _ x, KanComplex.π.map (x := x) f rfl (n + 1) p⟩ =
          (positiveπEquiv n Y).symm
            ⟨f.app _ x, KanComplex.π.map (x := x) f rfl (n + 1) q⟩ := by
        simpa only [positiveπ_map_equiv_symm] using hab.1
      have hsigma := (positiveπEquiv n Y).symm.injective hfun
      have hmaps : KanComplex.π.map (x := x) f rfl (n + 1) p =
          KanComplex.π.map (x := x) f rfl (n + 1) q := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hsigma
      have hpq : p = q := (hπ x).1 hmaps
      subst q
      rfl
    · intro p x hp
      obtain ⟨⟨y, q⟩, rfl⟩ := (positiveπEquiv n Y).symm.surjective p
      have hy : y = f.app _ x := by
        simpa only [positiveπToVertices_equiv_symm] using hp
      subst y
      obtain ⟨q', hq'⟩ := (hπ x).2 q
      refine ⟨(positiveπEquiv n X).symm ⟨x, q'⟩, ?_, ?_⟩
      · rw [positiveπ_map_equiv_symm]
        exact congrArg (fun z ↦ (positiveπEquiv n Y).symm ⟨f.app _ x, z⟩) hq'
      · exact positiveπToVertices_equiv_symm q'
  · rintro ⟨_, huniq, hlift⟩ x
    constructor
    · intro p q hpq
      have hfun : (positiveπEquiv n X).symm ⟨x, p⟩ =
          (positiveπEquiv n X).symm ⟨x, q⟩ := by
        apply huniq
        refine ⟨?_, ?_⟩
        · simpa only [positiveπ_map_equiv_symm] using
            congrArg (fun z ↦ (positiveπEquiv n Y).symm ⟨f.app _ x, z⟩) hpq
        · simp only [positiveπToVertices_equiv_symm]
      have hsigma := (positiveπEquiv n X).symm.injective hfun
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hsigma
    · intro p
      obtain ⟨q, hq, hbase⟩ := hlift
        ((positiveπEquiv n Y).symm ⟨f.app _ x, p⟩) x
        (positiveπToVertices_equiv_symm p)
      obtain ⟨⟨x', q'⟩, rfl⟩ := (positiveπEquiv n X).symm.surjective q
      have hxx' : x' = x := by
        simpa only [positiveπToVertices_equiv_symm] using hbase
      subst x'
      refine ⟨q', ?_⟩
      have hfun : (positiveπEquiv n Y).symm
          ⟨f.app _ x, KanComplex.π.map (x := x) f rfl (n + 1) q'⟩ =
          (positiveπEquiv n Y).symm ⟨f.app _ x, p⟩ := by
        simpa only [positiveπ_map_equiv_symm] using hq
      have hsigma := (positiveπEquiv n Y).symm.injective hfun
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hsigma

private noncomputable instance inverseImage_stableUnderColimits
    {C D : Type*} [Category* C] [Category* D]
    {P : MorphismProperty D} {G : C ⥤ D}
    [PreservesColimitsOfShape J G] [P.IsStableUnderColimitsOfShape J] :
    (P.inverseImage G).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    apply MorphismProperty.IsStableUnderColimitsOfShape.condition
      (X₁ ⋙ G) (X₂ ⋙ G) (G.mapCocone c₁) (G.mapCocone c₂)
      (isColimitOfPreserves G hc₁) (isColimitOfPreserves G hc₂)
      (Functor.whiskerRight f G) hf (G.map φ)
    intro j
    change G.map (c₁.ι.app j) ≫ G.map φ =
      G.map (f.app j) ≫ G.map (c₂.ι.app j)
    simpa only [Functor.map_comp] using G.congr_map (hφ j)

private noncomputable instance naiveW_stableUnderFilteredColimits :
    naiveW.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    have hf' (j : J) := hf j
    simp only [naiveW, MorphismProperty.inf_iff, MorphismProperty.iInf_iff] at hf' ⊢
    refine ⟨?_, fun n ↦ ?_⟩
    · exact MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j ↦ (hf' j).1) φ hφ
    · exact MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₁ X₂ c₁ c₂ hc₁ hc₂ f (fun j ↦ (hf' j).2 n) φ hφ

end FilteredFunctor

end WColimitAux

namespace KanComplex.W

private theorem stableUnderFilteredColimits_of_univLE
    (P : MorphismProperty SSet.{u}) [UnivLE.{w, u}] [UnivLE.{v, u}]
    [P.IsStableUnderFilteredColimits.{u, u}] :
    P.IsStableUnderFilteredColimits.{w, v} := by
  constructor
  intro J _ _
  let e := ((ShrinkHoms.equivalence.{u} J).trans <| Shrink.equivalence _).symm
  have := IsFiltered.of_equivalence e.symm
  rw [MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  rw [← P.colimitsOfShape_eq_of_equivalence e]
  exact MorphismProperty.colimitsOfShape_le (W := P)

/-- Weak equivalences between Kan complexes are stable under same-universe filtered colimits. -/
private theorem isStableUnderFilteredColimitsSelf :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (KanComplex.W : MorphismProperty SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    constructor
    intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
    let _ (j : J) : KanComplex (F₁.obj j) := (hf j).kanComplex_source
    let _ (j : J) : KanComplex (F₂.obj j) := (hf j).kanComplex_target
    let _ : KanComplex c₁.pt := KanComplex.ofIsFilteredColimit (fun _ ↦ inferInstance) hc₁
    let _ : KanComplex c₂.pt := KanComplex.ofIsFilteredColimit (fun _ ↦ inferInstance) hc₂
    apply (WColimitAux.W_iff_naiveW φ).2
    apply MorphismProperty.IsStableUnderColimitsOfShape.condition
      F₁ F₂ c₁ c₂ hc₁ hc₂ f
      (fun j ↦ (WColimitAux.W_iff_naiveW (f.app j)).1 (hf j)) φ hφ

/-- Weak equivalences between Kan complexes are stable under filtered colimits whose shape
object and morphism universes are no larger than the simplicial universe. -/
instance isStableUnderFilteredColimits [UnivLE.{w, u}] [UnivLE.{v, u}] :
    MorphismProperty.IsStableUnderFilteredColimits.{w, v}
      (KanComplex.W : MorphismProperty SSet.{u}) := by
  let _ : MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (KanComplex.W : MorphismProperty SSet.{u}) :=
    isStableUnderFilteredColimitsSelf
  exact stableUnderFilteredColimits_of_univLE.{u, v, w}
    (KanComplex.W : MorphismProperty SSet.{u})

private lemma stage_kan_of_noMax
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [NoMaxOrder J] {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : (KanComplex.W : MorphismProperty SSet.{u}).TransfiniteCompositionOfShape J f)
    (j : J) : KanComplex (h.F.obj j) :=
  (h.map_mem j (not_isMax j)).kanComplex_source

private lemma transfinite_map_from_bot
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [NoMaxOrder J] {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : (KanComplex.W : MorphismProperty SSet.{u}).TransfiniteCompositionOfShape J f)
    {j : J} (g : ⊥ ⟶ j) : KanComplex.W (h.F.map g) := by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl := hj.eq_bot
      let _ : KanComplex (h.F.obj ⊥) := stage_kan_of_noMax h ⊥
      simpa using (KanComplex.W.id (X := h.F.obj ⊥))
  | succ j hj ih =>
      rw [← homOfLE_comp bot_le (Order.le_succ j), h.F.map_comp]
      exact KanComplex.W.comp ih (h.map_mem j hj)
  | isSuccLimit j hj ih =>
      let _ : OrderBot (Set.Iio j) :=
        { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
          bot_le _ := bot_le }
      exact MorphismProperty.colimitsOfShape_le _
        (.of_isColimit (h.F.isColimitOfIsWellOrderContinuous j hj)
          (fun k ↦ ih _ k.2))

/-- A no-max well-ordered transfinite composition of Kan weak equivalences is again a Kan weak
equivalence. The no-max hypothesis ensures that every intermediate stage is Kan. -/
instance isStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [NoMaxOrder J] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (KanComplex.W : MorphismProperty SSet.{u}) J where
  le X Y f := by
    rintro ⟨h⟩
    let g : h.F.obj ⊥ ⟶ Y := h.incl.app ⊥
    have hg : KanComplex.W g := MorphismProperty.colimitsOfShape_le _
      (.of_isColimit h.isColimit (fun j ↦ transfinite_map_from_bot h _))
    let e : Arrow.mk f ≅ Arrow.mk g :=
      Arrow.isoMk h.isoBot.symm (Iso.refl _) (by simp [g, h.fac])
    exact (MorphismProperty.arrow_mk_iso_iff KanComplex.W e).2 hg

end KanComplex.W

end SSet

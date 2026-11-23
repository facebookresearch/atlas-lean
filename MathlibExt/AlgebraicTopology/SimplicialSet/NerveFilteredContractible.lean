/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakFilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The actual nerve of a filtered category is weakly contractible

The diagram c ↦ nerve (Over c) has the original nerve as its colimit.
An original simplex lifts to the over category of its last object. The
last arrow of an arbitrary over-simplex gives its relation to this
canonical lift. These actual representatives prove the colimit, with no
colimit isomorphism or contractibility premise supplied.

Each over category has its original identity terminal object. Full
filtered-colimit stability of realization weak equivalences then detects
the original terminal nerve map. A canonical index equivalence supplies
the working-small frame internally; original object and Hom universes
remain independent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

attribute [local instance] uliftCategory

universe uObj uHom

namespace NerveFiltered

variable (C : Type uObj) [Category.{uHom} C]

/-- The original over-category diagram, with its actual postcomposition maps. -/
public def overNerveDiagram : C ⥤ SSet.{max uObj uHom} :=
  Over.mapFunctor C ⋙ nerveFunctor

private def overNerveForget (c : C) :
    (overNerveDiagram C).obj c ⟶ (nerve C : SSet.{max uObj uHom}) where
  app Δ := ↾fun τ => τ ⋙ Over.forget c
  naturality {Δ Γ} f := by
    apply ConcreteCategory.hom_ext
    intro τ
    rfl

/-- The cocone forgets the original over-target in every simplex. -/
public def overNerveCocone : Cocone (overNerveDiagram C) where
  pt := nerve C
  ι.app c := overNerveForget C c
  ι.naturality {c d} f := by
    dsimp only [overNerveDiagram, overNerveForget]
    apply NatTrans.ext
    funext Δ
    apply ConcreteCategory.hom_ext
    intro τ
    let τ₀ : ComposableArrows (Over c) Δ.unop.len := τ
    change τ₀ ⋙ (Over.map f ⋙ Over.forget d) = τ₀ ⋙ Over.forget c
    exact congrArg (fun G : Over c ⥤ C => τ₀ ⋙ G) (Over.mapForget_eq f)

/-- The original diagram object is the nerve of the actual over category. -/
public theorem overNerveDiagram_obj (c : C) :
    (overNerveDiagram C).obj c = (nerve (Over c) : SSet.{max uObj uHom}) := by
  unfold overNerveDiagram
  rfl

/-- The displayed original cocone has the original nerve as its point. -/
public theorem overNerveCocone_pt :
    (overNerveCocone C).pt = (nerve C : SSet.{max uObj uHom}) := by
  unfold overNerveCocone
  rfl

/-- The original cocone leg, transported by its two proved object views. -/
public def overNerveCoconeLeg (c : C) :
    (nerve (Over c) : SSet.{max uObj uHom}) ⟶ nerve C := by
  let hS := overNerveDiagram_obj C c
  have hT : ((Functor.const C).obj (overNerveCocone C).pt).obj c = nerve C := by
    simpa only [Functor.const_obj_obj] using overNerveCocone_pt C
  exact eqToHom hS.symm ≫ (overNerveCocone C).ι.app c ≫ eqToHom hT

private def originalOverNerveMap (c : C) :
    (nerve (Over c) : SSet.{max uObj uHom}) ⟶ nerve C where
  app Δ := ↾fun τ => τ ⋙ Over.forget c
  naturality {Δ Γ} f := by
    apply ConcreteCategory.hom_ext
    intro τ
    rfl

/-- Compute the whole well-typed leg before taking any dependent applications. -/
private theorem overNerveCoconeLeg_eq_original (c : C) :
    overNerveCoconeLeg C c = originalOverNerveMap C c := by
  rfl

private theorem overNerveCoconeLeg_app_computed (c : C) (Δ : SimplexCategoryᵒᵖ)
    (τ : (nerve (Over c)).obj Δ) :
    (overNerveCoconeLeg C c).app Δ τ = τ ⋙ Over.forget c :=
  congrArg (fun k : (nerve (Over c) : SSet.{max uObj uHom}) ⟶ nerve C => k.app Δ τ)
    (overNerveCoconeLeg_eq_original C c)

/-- Every transported ORIGINAL cocone component forgets only the over-target. -/
public theorem overNerveCocone_app (c : C) (Δ : SimplexCategoryᵒᵖ)
    (τ : (nerve (Over c)).obj Δ) :
    (overNerveCoconeLeg C c).app Δ τ = τ ⋙ Over.forget c :=
  overNerveCoconeLeg_app_computed C c Δ τ

/-- The original simplex, lifted over its actual last object. -/
public def overLastSimplex {n : ℕ} (σ : ComposableArrows C n) :
    ComposableArrows (Over (σ.obj (Fin.last n))) n where
  obj i := Over.mk (σ.map (homOfLE (Fin.le_last i)))
  map {i j} f := Over.homMk (σ.map f) (by
    change σ.map f ≫ σ.map (homOfLE (Fin.le_last j)) =
      σ.map (homOfLE (Fin.le_last i))
    rw [← σ.map_comp]
    exact congrArg σ.map (Subsingleton.elim _ _))
  map_id i := by
    apply Over.OverMorphism.ext
    change σ.map (𝟙 i) = 𝟙 (σ.obj i)
    exact σ.map_id i
  map_comp f g := by
    apply Over.OverMorphism.ext
    change σ.map (f ≫ g) = σ.map f ≫ σ.map g
    exact σ.map_comp f g

private theorem overLastSimplex_forget {n : ℕ} (σ : ComposableArrows C n) :
    overLastSimplex C σ ⋙ Over.forget (σ.obj (Fin.last n)) = σ := by
  apply ComposableArrows.ext (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The canonical last-object representative has exactly the original image. -/
public theorem overNerveCocone_lastSimplex (Δ : SimplexCategoryᵒᵖ)
    (σ : (nerve C).obj Δ) :
    (overNerveCoconeLeg C (σ.obj (Fin.last Δ.unop.len))).app Δ
      (overLastSimplex C σ) = σ :=
  (overNerveCocone_app C _ Δ (overLastSimplex C σ)).trans (overLastSimplex_forget C σ)

private theorem overLastSimplex_relation {n : ℕ} {c : C}
    (τ : ComposableArrows (Over c) n) :
    overLastSimplex C (τ ⋙ Over.forget c) ⋙ Over.map (τ.obj (Fin.last n)).hom = τ := by
  let A := overLastSimplex C (τ ⋙ Over.forget c) ⋙ Over.map (τ.obj (Fin.last n)).hom
  have hObj (i : Fin (n + 1)) : A.obj i = τ.obj i := by
    have hA : A.obj i =
        Over.mk ((τ.map (homOfLE (Fin.le_last i))).left ≫ (τ.obj (Fin.last n)).hom) := by
      dsimp only [A, overLastSimplex, Functor.comp_obj]
      rfl
    exact hA.trans ((congrArg
      (fun h : (τ.obj i).left ⟶ c => Over.mk h)
      (Over.w (τ.map (homOfLE (Fin.le_last i))))).trans
        (CostructuredArrow.eq_mk (τ.obj i)).symm)
  have hForget : A ⋙ Over.forget c = τ ⋙ Over.forget c := by
    change overLastSimplex C (τ ⋙ Over.forget c) ⋙
        (Over.map (τ.obj (Fin.last n)).hom ⋙ Over.forget c) = τ ⋙ Over.forget c
    rw [Over.mapForget_eq]
    exact overLastSimplex_forget C (τ ⋙ Over.forget c)
  let e : A ≅ τ := NatIso.ofComponents (fun i => eqToIso (hObj i)) (by
    intro i j f
    apply (Over.forget c).map_injective
    simp only [eqToIso.hom, Functor.map_comp, eqToHom_map]
    change (A ⋙ Over.forget c).map f ≫ eqToHom (Functor.congr_obj hForget j) =
      eqToHom (Functor.congr_obj hForget i) ≫ (τ ⋙ Over.forget c).map f
    rw [Functor.congr_hom hForget f]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  exact Functor.ext_of_iso e hObj (fun _ => rfl)

private def overNerveDegreeIsColimit (Δ : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type (max uObj uHom))).obj Δ).mapCocone
      (overNerveCocone C)) where
  desc s := ↾fun σ =>
    s.ι.app (σ.obj (Fin.last Δ.unop.len)) (overLastSimplex C σ)
  fac s c := by
    dsimp only [overNerveCocone, overNerveDiagram, overNerveForget] at *
    apply ConcreteCategory.hom_ext
    intro τ
    let σ : ComposableArrows C Δ.unop.len := τ ⋙ Over.forget c
    let h : σ.obj (Fin.last Δ.unop.len) ⟶ c := (τ.obj (Fin.last Δ.unop.len)).hom
    have hRep :
        overLastSimplex C σ ⋙ Over.map h = τ :=
      overLastSimplex_relation C τ
    have hs := ConcreteCategory.congr_hom (s.w h) (overLastSimplex C σ)
    change s.ι.app c (overLastSimplex C σ ⋙ Over.map h) =
      s.ι.app (σ.obj (Fin.last Δ.unop.len)) (overLastSimplex C σ) at hs
    change s.ι.app (σ.obj (Fin.last Δ.unop.len)) (overLastSimplex C σ) = s.ι.app c τ
    exact hs.symm.trans (congrArg (fun ρ => s.ι.app c ρ) hRep)
  uniq s m hm := by
    dsimp only [overNerveCocone, overNerveDiagram, overNerveForget] at *
    apply ConcreteCategory.hom_ext
    intro σ
    have h := ConcreteCategory.congr_hom
      (hm (σ.obj (Fin.last Δ.unop.len))) (overLastSimplex C σ)
    change m (overLastSimplex C σ ⋙ Over.forget (σ.obj (Fin.last Δ.unop.len))) =
      s.ι.app (σ.obj (Fin.last Δ.unop.len)) (overLastSimplex C σ) at h
    change m σ = s.ι.app (σ.obj (Fin.last Δ.unop.len)) (overLastSimplex C σ)
    exact (congrArg (fun ρ => m ρ) (overLastSimplex_forget C σ)).symm.trans h

/-- The actual last-object representatives and last-arrow relations give the colimit. -/
public def overNerveCoconeIsColimit : IsColimit (overNerveCocone C) :=
  evaluationJointlyReflectsColimits _ (overNerveDegreeIsColimit C)

public instance overNerveDiagramHasColimit : HasColimit (overNerveDiagram C) where
  exists_colimit := ⟨{ cocone := overNerveCocone C, isColimit := overNerveCoconeIsColimit C }⟩

/-- The colimit isomorphism is derived from the original displayed cocone. -/
public def overNerveColimitIso :
    colimit (overNerveDiagram C) ≅ (nerve C : SSet.{max uObj uHom}) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (overNerveDiagram C))
    (overNerveCoconeIsColimit C)

private def pointCocone :
    Cocone ((Functor.const C).obj (⊤_ SSet.{max uObj uHom})) where
  pt := ⊤_ SSet.{max uObj uHom}
  ι.app _ := 𝟙 _
  ι.naturality _ := by simp

private def filteredIndex [IsFiltered C] : C :=
  Classical.choice (IsFiltered.nonempty (C := C))

private def pointCoconeIsColimit [IsFiltered C] :
    IsColimit (pointCocone C) where
  desc s := s.ι.app (filteredIndex C)
  fac s c := by
    change s.ι.app (filteredIndex C) = s.ι.app c
    have hl :
        (s.ι.app (IsFiltered.max c (filteredIndex C)) : (⊤_ SSet.{max uObj uHom}) ⟶ s.pt) =
          (s.ι.app c : (⊤_ SSet.{max uObj uHom}) ⟶ s.pt) := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] using
        s.w (IsFiltered.leftToMax c (filteredIndex C))
    have hr :
        (s.ι.app (IsFiltered.max c (filteredIndex C)) : (⊤_ SSet.{max uObj uHom}) ⟶ s.pt) =
          (s.ι.app (filteredIndex C) : (⊤_ SSet.{max uObj uHom}) ⟶ s.pt) := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] using
        s.w (IsFiltered.rightToMax c (filteredIndex C))
    exact hr.symm.trans hl
  uniq s m hm := by
    have h := hm (filteredIndex C)
    change (𝟙 (⊤_ SSet.{max uObj uHom})) ≫ m = s.ι.app (filteredIndex C) at h
    exact (Category.id_comp m).symm.trans h

private def overNerveToPoint :
    overNerveDiagram C ⟶ (Functor.const C).obj (⊤_ SSet.{max uObj uHom}) where
  app c := terminal.from _
  naturality {X Y} f := by
    change (overNerveDiagram C).map f ≫ terminal.from ((overNerveDiagram C).obj Y) =
      terminal.from ((overNerveDiagram C).obj X) ≫ 𝟙 (⊤_ SSet.{max uObj uHom})
    exact Subsingleton.elim _ _

/-- A filtered category's original terminal nerve map is a realization weak equivalence.
Only the legitimate filtered-category hypothesis is supplied; the colimit,
over-category contractions and working-small transport are derived internally. -/
public theorem nerve_to_terminal_mem_realizationWeakEquivalences_of_isFiltered
    [IsFiltered C] :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max uObj uHom})) := by
  let L := ULiftHom.{max uObj uHom} (ULift.{max uObj uHom} C)
  let E : L ≌ C :=
    (ULiftHomULiftCategory.equiv.{max uObj uHom, max uObj uHom, uHom, uObj} C).symm
  let : IsFiltered L := IsFiltered.of_equivalence E.symm
  let : MorphismProperty.IsStableUnderFilteredColimits.{max uObj uHom, max uObj uHom}
      (SSet.realizationWeakEquivalences : MorphismProperty SSet.{max uObj uHom}) :=
    SSet.realizationWeakEquivalences_stableUnderFilteredColimits
  let F := E.functor ⋙ overNerveDiagram C
  let G := E.functor ⋙ (Functor.const C).obj (⊤_ SSet.{max uObj uHom})
  let cF := (overNerveCocone C).whisker E.functor
  let cG := (pointCocone C).whisker E.functor
  let α := Functor.whiskerLeft E.functor (overNerveToPoint C)
  have hF : IsColimit cF := (overNerveCoconeIsColimit C).whiskerEquivalence E
  have hG : IsColimit cG := (pointCoconeIsColimit C).whiskerEquivalence E
  have hα : ∀ l : L, SSet.realizationWeakEquivalences (α.app l) := by
    intro l
    exact NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
      (C := Over (E.functor.obj l)) Over.mkIdTerminal
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition F G cF cG hF hG α hα
    (terminal.from (nerve C : SSet.{max uObj uHom})) (by
      intro l
      have hPt : cG.pt = (⊤_ SSet.{max uObj uHom}) := by
        dsimp only [cG, Cocone.whisker, pointCocone]
      apply (cancel_mono (eqToHom hPt)).1
      exact Subsingleton.elim _ _)

end NerveFiltered

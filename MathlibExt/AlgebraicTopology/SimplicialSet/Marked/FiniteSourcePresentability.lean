/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ColimitMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Presentability of actual sources with finitely many selected edges

A native simplicial source that is κ-presentable remains κ-presentable
after adjoining a finite set of original edge markings. Underlying maps
factor through a stage. Each selected marked image comes from an original
marked stage edge, and filtered equality moves the factor to a common
stage. Finite induction retains all previous marks and the entire original
map. Equality detection uses the original underlying presentability.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- A finite collection of actual marked images can be realized by one original stage factorization. -/
theorem exists_hom_of_isColimit_with_finite_marking {X : SSet.{u}} (E : Set (X _⦋1⦌))
    (hE : E.Finite) (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalPresentable X κ]
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
    {F : J ⥤ Marked.{u}} {c : Cocone F} (hc : IsColimit c)
    (g : X ⟶ c.pt.toSSet) (hg : ∀ e ∈ E, g.app (op ⦋1⦌) e ∈ c.pt.marking) :
    ∃ (j : J) (f : X ⟶ (F.obj j).toSSet),
      f ≫ (c.ι.app j).hom = g ∧ ∀ e ∈ E, f.app (op ⦋1⦌) e ∈ (F.obj j).marking := by
  classical
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let U := F ⋙ forget
  let cU := forget.mapCocone c
  have hcU : IsColimit cU := isColimitOfPreserves forget hc
  let _ : PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
    preservesColimitsOfShape_of_isCardinalPresentable X κ J
  revert hg
  induction E, hE using Set.Finite.induction_on with
  | empty =>
      intro hg
      obtain ⟨j, f, hf⟩ := exists_hom_of_preservesColimit_coyoneda hcU g
      exact ⟨j, f, hf, fun _ h => False.elim h⟩
  | @insert e E he hE ih =>
      intro hg
      obtain ⟨j, f, hf, hm⟩ := ih (fun a ha => hg a (Set.mem_insert_of_mem e ha))
      obtain ⟨k, b, hb, hbg⟩ := (mem_marking_of_isColimit_iff hc _).mp (hg e (Set.mem_insert e E))
      let ev := (evaluation (SimplexCategoryᵒᵖ) (Type u)).obj (op ⦋1⦌)
      have hc₁ := isColimitOfPreserves ev hcU
      have hfg : (c.ι.app j).hom.app (op ⦋1⦌) (f.app (op ⦋1⦌) e) =
          (c.ι.app k).hom.app (op ⦋1⦌) b :=
        (ConcreteCategory.congr_hom (congr_app hf (op ⦋1⦌)) e).trans hbg.symm
      obtain ⟨l, a, b', hab⟩ := (Types.FilteredColimit.isColimit_eq_iff (U ⋙ ev) hc₁).mp hfg
      refine ⟨l, f ≫ (F.map a).hom, ?_, ?_⟩
      · have hnat : (F.map a).hom ≫ (c.ι.app l).hom = (c.ι.app j).hom := by
          have h := congrArg Hom.hom (c.ι.naturality a)
          exact h.trans (Category.comp_id _)
        exact (Category.assoc _ _ _).trans ((congrArg (fun t => f ≫ t) hnat).trans hf)
      · intro z hz
        rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          change (F.map a).hom.app (op ⦋1⦌) (f.app (op ⦋1⦌) e) ∈ (F.obj l).marking
          exact hab.symm ▸ (F.map b').preserve hb
        · exact (F.map a).preserve (hm z hz)

/-- Adjoining finite original edge markings preserves native κ-presentability at the original value universe. -/
theorem withEdges_isCardinalPresentable (X : SSet.{u}) (E : Set (X _⦋1⦌)) (hE : E.Finite)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalPresentable X κ] :
    IsCardinalPresentable (withEdges X E) κ := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let U := F ⋙ forget
  let cU := forget.mapCocone c
  have hcU : IsColimit cU := isColimitOfPreserves forget hc
  let _ : PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
    preservesColimitsOfShape_of_isCardinalPresentable X κ J
  constructor
  · intro g
    let G : X ⟶ c.pt.toSSet := g.hom
    obtain ⟨j, f, hf, hm⟩ := exists_hom_of_isColimit_with_finite_marking E hE κ hc G
      (fun e he => g.preserve (Or.inr he))
    exact ⟨j, ofWithEdges f hm, Hom.ext hf⟩
  · intro j f₁ f₂ h
    let f : X ⟶ (F.obj j).toSSet := f₁.hom
    let g : X ⟶ (F.obj j).toSSet := f₂.hom
    have h' : f ≫ (c.ι.app j).hom = g ≫ (c.ι.app j).hom := congrArg Hom.hom h
    obtain ⟨k, a, ha⟩ := exists_eq_of_preservesColimit_coyoneda_self hcU f g h'
    exact ⟨k, a, Hom.ext ha⟩

end SSet.Marked

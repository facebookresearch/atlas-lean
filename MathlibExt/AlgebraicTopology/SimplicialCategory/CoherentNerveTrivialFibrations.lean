/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveInnerFibration
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveDwyerKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-!
# Actual trivial-fibration coherent nerves at locally Kan targets

The original Hom maps are genuine scalar trivial fibrations and the
original object map is surjective. A genuinely locally Kan target makes
the source locally Kan through those actual fibrations. The proved
relative horn lifting, same-map DK recognition and strict ordinary
isofibration then give genuine boundary RLP of the nerve. No Bergner
model, source-cofibrancy or categorical-equivalence outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.NerveTrivialFibrations
open SimplicialEnrichment

variable {C D : Carrier.{u}} (F : C ⟶ D)

private theorem source_hom_kan
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hF : ∀ x y : C, Fibration (F.map x y)) (x y : C) :
    SSet.KanComplex (x ⟶[SSet.{u}] y) := by
  let _ := hD (F.obj x) (F.obj y)
  let _ := hF x y
  exact isFibrant_of_fibration (F.map x y)

private theorem vertices_surjective (hObj : Function.Surjective F.obj) :
    Function.Surjective ((coherentNerveFunctor.map F).app (op ⦋0⦌)) := by
  intro σ
  obtain ⟨x, hx⟩ := hObj (verticesEquiv D σ)
  refine ⟨(verticesEquiv C).symm x, ?_⟩
  apply (verticesEquiv D).injective
  exact (verticesEquiv_map C D F _).trans
    ((congrArg F.obj ((verticesEquiv C).apply_symm_apply x)).trans hx)

private theorem ordinary_objects_surjective (hObj : Function.Surjective F.obj) :
    Function.Surjective (SSet.mapHomotopyCategory (coherentNerveFunctor.map F)).obj := by
  intro y
  cases y using SSet.HomotopyCategory.rec with
  | mk y =>
    obtain ⟨x, hx⟩ := vertices_surjective F hObj y
    exact ⟨SSet.HomotopyCategory.mk x, congrArg SSet.HomotopyCategory.mk hx⟩

/-- Original object surjectivity and genuine Hom trivial fibrations give categorical weakness of the same
  nerve map at a locally Kan target. -/
theorem categoricalEquivalence
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y)) :
    SSet.categoricalEquivalences (coherentNerveFunctor.map F) :=
  NerveDwyerKan.nerve_categoricalEquivalence_of_surjective_objects F
    (source_hom_kan F hD (fun x y => (hHom x y).1)) hD hObj (fun x y => (hHom x y).2)

/-- The actual nerve is a genuine categorical fibration, using derived inner lifting and the strict ordinary
  isofibration on original objects. -/
theorem categoricalFibration
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y)) :
    SSet.categoricalFibrations (coherentNerveFunctor.map F) := by
  let _ := coherentNerve_quasicategory C (source_hom_kan F hD (fun x y => (hHom x y).1))
  let _ := coherentNerve_quasicategory D hD
  let _ := (categoricalEquivalence F hD hObj hHom).isEquivalence_mapHomotopyCategory
  have hIso : (SSet.mapHomotopyCategory (coherentNerveFunctor.map F)).IsIsofibration :=
    Functor.isIsofibration_of_isEquivalence_of_surjective _ (ordinary_objects_surjective F hObj)
  exact (SSet.categoricalFibrations_iff_innerFibration_and_hoIsofibration _).mpr
    ⟨NerveInnerFibration.innerFibration F (fun x y => (hHom x y).1), hIso⟩

/-- The same original coherent-nerve map has genuine full boundary RLP under the proved original
  trivial-fibration hypotheses. -/
theorem boundaryRLP
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y)) :
    SSet.modelCategoryQuillen.I.rlp (coherentNerveFunctor.map F) :=
  (SSet.categoricalFibrations_and_categoricalEquivalences_iff _).mp
    ⟨categoricalFibration F hD hObj hHom, categoricalEquivalence F hD hObj hHom⟩

/-- Every actual monomorphic simplicial map lifts against the same original nerve map, with no categorical
  outcome supplied as an input. -/
theorem hasLiftingProperty_mono
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (coherentNerveFunctor.map F) := by
  have h := boundaryRLP F hD hObj hHom
  rw [← SSet.rlp_monomorphisms] at h
  exact h i (show Mono i from inferInstance)

/-- An actual prescribed enriched simplex and its whole original boundary lift through the same map in every
  degree, including zero. -/
theorem exists_enriched_boundary_lift
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y))
    (n : ℕ) (f : (∂Δ[n] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
    (σ : coherentSimplex.{u} ⦋n⦌ ⟶ D)
    (sq : CommSq f (∂Δ[n]).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ)) :
    ∃ τ : coherentSimplex.{u} ⦋n⦌ ⟶ C,
      (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm τ = f ∧ τ ≫ F = σ := by
  let _ := hasLiftingProperty_mono F hD hObj hHom (∂Δ[n]).ι
  let l := sq.lift
  let τ : coherentSimplex.{u} ⦋n⦌ ⟶ C := SSet.yonedaEquiv l
  have hτ : SSet.yonedaEquiv.symm τ = l := Equiv.symm_apply_apply _ _
  refine ⟨τ, (congrArg (fun t => (∂Δ[n]).ι ≫ t) hτ).trans sq.fac_left, ?_⟩
  exact (SSet.yonedaEquiv_comp l (coherentNerveFunctor.map F)).symm.trans
    ((congrArg SSet.yonedaEquiv sq.fac_right).trans (Equiv.apply_symm_apply _ _))

end CategoryTheory.CoherentRealization.NerveTrivialFibrations

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerLocalClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerHomFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationComponentVertexLifting

/-!
# The actual original equivalence-vertex lifting condition

Under the original full Hom Kan fibrations, component-isomorphism
lifting equals exact lifting of every supplied original equivalence
vertex. The scalar correction stays in the supplied original source
component and recovers the SAME original target vertex. Object and
coefficient universes are independent, and no local Kan target is used.
This matches Bergner's F2 condition in Theorem 1.1 (Section 1), rather
than replacing the supplied equivalence by another representative.
-/

noncomputable section
universe u v w
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner

variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]

/-- Exact lifting of each SAME original equivalence vertex, retaining the entire original Hom map and its actual
endpoint equality. -/
def equivalenceVertexLifting (F : EnrichedFunctor SSet.{u} C D) : Prop :=
  ∀ (x : C) (d : D) (e : (F.obj x ⟶[SSet.{u}] d) _⦋0⦌),
    IsIso (ComponentCategory.arrowOf D e) →
      ∃ (y : C) (hy : F.obj y = d) (f : (x ⟶[SSet.{u}] y) _⦋0⦌),
        IsIso (ComponentCategory.arrowOf C f) ∧
          (F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hy)).app _ f = e

/-- The SAME whole original codomain Hom transport induces the literal component-category endpoint transport. -/
theorem component_codomain_transport {x y z : D} (h : y = z)
    (a : ComponentCategory.objectOf.{u} D x ⟶ ComponentCategory.objectOf.{u} D y) :
    SSet.mapπ₀ (eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) rfl h)) a =
      a ≫ eqToHom (congrArg (ComponentCategory.objectOf.{u} D) h) := by
  cases h
  change SSet.mapπ₀ (𝟙 (x ⟶[SSet.{u}] y)) a = a ≫ 𝟙 (ComponentCategory.objectOf.{u} D y)
  exact (SSet.mapπ₀_id_apply a).trans (Category.comp_id a).symm

/-- With genuine full Hom fibrations, the same component-isomorphism lift corrects to the EXACT supplied original
equivalence vertex. -/
theorem componentIsofibration_iff_equivalenceVertexLifting (F : EnrichedFunctor SSet.{u} C D)
    (hF : ∀ x y, Fibration (F.map x y)) :
    (ComponentCategory.mapFunctor F).IsIsofibration ↔ equivalenceVertexLifting F := by
  constructor
  · intro h
    let _ : (ComponentCategory.mapFunctor F).IsIsofibration := h
    intro x d e he
    let eIso : ComponentCategory.objectOf.{u} D (F.obj x) ≅ ComponentCategory.objectOf.{u} D d :=
      @asIso _ _ _ _ (ComponentCategory.arrowOf D e) he
    obtain ⟨y, l, hy, hl⟩ := (ComponentCategory.mapFunctor F).exists_iso_lift
      eIso
    have hy' : F.obj y = d := hy
    let p : (x ⟶[SSet.{u}] y) ⟶ (F.obj x ⟶[SSet.{u}] d) :=
      F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hy')
    have hclass : SSet.mapπ₀ p l.hom = SSet.π₀.mk e := by
      have hhom : (ComponentCategory.mapFunctor F).map l.hom ≫ eqToHom hy = eIso.hom :=
        congrArg Iso.hom hl
      exact (SSet.mapπ₀_comp_apply _ _ l.hom).trans
        ((component_codomain_transport hy' ((ComponentCategory.mapFunctor F).map l.hom)).trans hhom)
    let _ : Fibration (F.map x y) := hF x y
    let _ : Fibration p := by dsimp [p]; infer_instance
    obtain ⟨f, hf, hcomponent⟩ :=
      SSet.fibration_exists_vertex_lift_of_component p l.hom e hclass
    refine ⟨y, hy', f, ?_, hf⟩
    · have hcomponent' : ComponentCategory.arrowOf C f = l.hom := hcomponent
      rw [hcomponent']
      exact l.isIso_hom
  · intro h
    refine ⟨fun {x d} g => ?_⟩
    obtain ⟨e, he⟩ := SSet.π₀.mk_surjective (X := F.obj x ⟶[SSet.{u}] d) g.hom
    have heIso : IsIso (ComponentCategory.arrowOf D e) := by
      have harrow : ComponentCategory.arrowOf D e = g.hom := he
      rw [harrow]
      exact g.isIso_hom
    obtain ⟨y, hy, f, hfIso, hfe⟩ := h x d e heIso
    let l : ComponentCategory.objectOf.{u} C x ≅ ComponentCategory.objectOf.{u} C y :=
      @asIso _ _ _ _ (ComponentCategory.arrowOf C f) hfIso
    let hObj : (ComponentCategory.mapFunctor F).obj (ComponentCategory.objectOf.{u} C y) = d :=
      congrArg (ComponentCategory.objectOf.{u} D) hy
    refine ⟨ComponentCategory.objectOf.{u} C y, l, hObj, ?_⟩
    apply Iso.ext
    have hclass : SSet.mapπ₀
        (F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hy))
          (SSet.π₀.mk f) = g.hom :=
      (congrArg SSet.π₀.mk hfe).trans he
    have hhom : (ComponentCategory.mapFunctor F).map l.hom ≫ eqToHom hObj = g.hom :=
      ((component_codomain_transport hy ((ComponentCategory.mapFunctor F).map l.hom)).symm.trans
        (SSet.mapπ₀_comp_apply _ _ (SSet.π₀.mk f)).symm).trans hclass
    exact hhom

/-- The original global local-fibration predicate is exactly full original Hom fibrations and the literal supplied
equivalence-vertex lifts, for arbitrary targets. -/
theorem localFibrations_original_vertex_iff {A B : Carrier.{u}} (F : A ⟶ B) :
    localFibrations F ↔ homFibrations F ∧ equivalenceVertexLifting F :=
  and_congr_right (fun hF => componentIsofibration_iff_equivalenceVertexLifting F hF)

end CategoryTheory.SimplicialEnrichment.Bergner

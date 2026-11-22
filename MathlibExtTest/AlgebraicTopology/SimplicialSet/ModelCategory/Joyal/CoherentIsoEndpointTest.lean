/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint

/-!
# The endpoint inclusion into `coherentIso` is categorical: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint`:
the unconditional main theorem
`SSet.categoricalEquivalences.coherentIso_endpointInclusion` and its
unpacking through `categoricalEquivalences.mem_iff`, the two discharged
prism-extension properties for quasicategories, the Bool pattern
maps on prisms over `coherentIso` and their face/composition formulas,
and the contraction edges (`etaEdge`, `etaInvEdge`) with their point
relation, endpoint evaluations, and naturality.
-/

@[expose] public section

open CategoryTheory MonoidalClosed MonoidalCategory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CoherentIsoEndpointTest

section MainTheorem

/-- The endpoint inclusion is a categorical equivalence,
unconditionally, at a variable universe and at universe `0`. -/
example : SSet.categoricalEquivalences.{u}
    SSet.coherentIso.endpointInclusion :=
  SSet.categoricalEquivalences.coherentIso_endpointInclusion

example : SSet.categoricalEquivalences.{0}
    SSet.coherentIso.endpointInclusion :=
  SSet.categoricalEquivalences.coherentIso_endpointInclusion

/-- Scope separation for the endpoint choice: the endpoint inclusion
selects the source vertex, not the target vertex. Applying Yoneda
reduces this to `x₀ ≠ x₁`, decided by their `Bool` tags. -/
example : SSet.coherentIso.endpointInclusion.{u} ≠
    SSet.const SSet.coherentIso.x₁ := by
  intro h
  have hx : SSet.coherentIso.x₀.{u} = SSet.coherentIso.x₁ := by
    have h0 : SSet.yonedaEquiv SSet.coherentIso.endpointInclusion.{u} =
        SSet.coherentIso.x₀ :=
      Equiv.apply_symm_apply _ _
    rw [h, SSet.yonedaEquiv_const] at h0
    exact h0.symm
  have hBool := congrArg
    (fun v => SSet.coherentIso.vertexBool v 0) hx
  exact Bool.false_ne_true hBool

/-- The map in the main theorem is exactly the endpoint inclusion of
`CoherentIsoCategorical` (the Yoneda map of the source vertex). -/
example : SSet.categoricalEquivalences.{u}
    (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) :=
  SSet.categoricalEquivalences.coherentIso_endpointInclusion

/-- Unpacked through `mem_iff`, endpoint evaluation into every
quasicategory is an equivalence of ordinary categories. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        C)).toFunctor.IsEquivalence :=
  (SSet.categoricalEquivalences.mem_iff
      SSet.coherentIso.endpointInclusion).1
    SSet.categoricalEquivalences.coherentIso_endpointInclusion C
    inferInstance

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        C)).toFunctor.IsEquivalence :=
  SSet.coherentIso.hoPre_endpointInclusion_isEquivalence C

/-- In particular, endpoint evaluation is full, faithful, and
essentially surjective for every quasicategory. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        C)).toFunctor.Full :=
  (SSet.coherentIso.hoPre_endpointInclusion_isEquivalence C).full

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        C)).toFunctor.Faithful :=
  (SSet.coherentIso.hoPre_endpointInclusion_isEquivalence C).faithful

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        C)).toFunctor.EssSurj :=
  (SSet.coherentIso.hoPre_endpointInclusion_isEquivalence C).essSurj

/-- A concrete quasicategory target: `coherentIso` itself (a nerve). -/
example :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        SSet.coherentIso.{u})).toFunctor.IsEquivalence :=
  SSet.coherentIso.hoPre_endpointInclusion_isEquivalence _

/-- Composing the endpoint inclusion with an identity or with its
strict retraction-and-reinclusion stays inside categorical
equivalences, by the general calculus. -/
example : SSet.categoricalEquivalences.{u}
    (SSet.coherentIso.endpointInclusion ≫ 𝟙 SSet.coherentIso.{u}) :=
  MorphismProperty.comp_mem _ _ _
    SSet.categoricalEquivalences.coherentIso_endpointInclusion
    (MorphismProperty.id_mem _ _)

example : SSet.categoricalEquivalences.{u}
    ((SSet.coherentIso.endpointInclusion ≫
      SSet.coherentIso.toDeltaZero) ≫
        SSet.coherentIso.endpointInclusion) := by
  rw [SSet.coherentIso.endpointInclusion_comp_toDeltaZero,
    Category.id_comp]
  exact SSet.categoricalEquivalences.coherentIso_endpointInclusion

/-- The unconditional theorem is also what the the supporting result conditional
assembly produces from the two discharged extension properties. -/
example : SSet.categoricalEquivalences.{u}
    SSet.coherentIso.endpointInclusion :=
  SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions
    fun C hC => by
      have := hC
      exact ⟨SSet.coherentIso.edgeExtensionProperty_of_quasicategory C,
        SSet.coherentIso.compExtensionProperty_of_quasicategory C⟩

end MainTheorem

section ExtensionProperties

variable (C : SSet.{u}) [SSet.Quasicategory C]

/-- The edge extension property holds for every quasicategory. -/
example : SSet.coherentIso.edgeExtensionProperty C :=
  SSet.coherentIso.edgeExtensionProperty_of_quasicategory C

/-- The composition extension property holds for every
quasicategory. -/
example : SSet.coherentIso.compExtensionProperty C :=
  SSet.coherentIso.compExtensionProperty_of_quasicategory C

/-- Unpacked edge extension: every evaluated edge is, up to the
homotopy category, the evaluation of an edge upstairs. -/
example {a a' : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε' : SSet.Edge
      (((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a)
      (((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a')) :
    ∃ ε : SSet.Edge a a',
      (ε.map ((pre SSet.coherentIso.endpointInclusion).app C)).toHoHom =
        ε'.toHoHom :=
  SSet.coherentIso.edgeExtensionProperty_of_quasicategory C ε'

/-- Unpacked composition extension: composition relations of
evaluated edges lift to composition relations upstairs. -/
example {a b c : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    {ε₁ : SSet.Edge a b} {ε₂ : SSet.Edge b c} {ε₁₂ : SSet.Edge a c}
    (h : Nonempty (SSet.Edge.CompStruct
      (ε₁.map ((pre SSet.coherentIso.endpointInclusion).app C))
      (ε₂.map ((pre SSet.coherentIso.endpointInclusion).app C))
      (ε₁₂.map ((pre SSet.coherentIso.endpointInclusion).app C)))) :
    Nonempty (SSet.Edge.CompStruct ε₁ ε₂ ε₁₂) :=
  SSet.coherentIso.compExtensionProperty_of_quasicategory C h

end ExtensionProperties

section PatternMaps

/-- Pattern simplices have the prescribed vertices. -/
example {n : ℕ} (P : Bool → Fin (n + 1) → Bool)
    {Δ : SimplexCategoryᵒᵖ} (s : SSet.coherentIso.{u}.obj Δ)
    (t : (Δ[n] : SSet.{u}).obj Δ) (k : Fin (Δ.unop.len + 1)) :
    SSet.coherentIso.vertexBool (SSet.cohPatternSimplex P s t) k =
      P (SSet.coherentIso.vertexBool s k)
        ((SSet.stdSimplex.asOrderHom t) k) :=
  SSet.vertexBool_cohPatternSimplex P s t k

/-- Faces of pattern maps and of prism pattern maps are the
restricted pattern maps. -/
example {n : ℕ} (P : Bool → Fin (n + 2) → Bool) (i : Fin (n + 2)) :
    (SSet.coherentIso.{u} ◁ SSet.stdSimplex.δ i) ≫
        SSet.cohPatternMap P =
      SSet.cohPatternMap
        (fun b j => P b ((SimplexCategory.δ i).toOrderHom j)) :=
  SSet.whiskerLeft_δ_cohPatternMap P i

example {n m : ℕ} (P : Bool → Fin (n + 2) → Bool)
    (Q : Fin (n + 2) →o Fin (m + 1)) (i : Fin (n + 2)) :
    (SSet.coherentIso.{u} ◁ SSet.stdSimplex.δ i) ≫
        SSet.prismPatternMap P Q =
      SSet.prismPatternMap
        (fun b j => P b ((SimplexCategory.δ i).toOrderHom j))
        (Q.comp (SimplexCategory.δ i).toOrderHom) :=
  SSet.whiskerLeft_δ_prismPatternMap P Q i

/-- Prism pattern maps compose patternwise, and the identity
patterns give identities and first projections. -/
example {n m l : ℕ} (P : Bool → Fin (n + 1) → Bool)
    (Q : Fin (n + 1) →o Fin (m + 1)) (P' : Bool → Fin (m + 1) → Bool)
    (Q' : Fin (m + 1) →o Fin (l + 1)) :
    SSet.prismPatternMap P Q ≫ SSet.prismPatternMap P' Q' =
      SSet.prismPatternMap (fun b j => P' (P b j) (Q j)) (Q'.comp Q) :=
  SSet.prismPatternMap_comp P Q P' Q'

example {n : ℕ} :
    SSet.prismPatternMap (fun b _ => b) OrderHom.id =
      𝟙 (SSet.coherentIso.{u} ⊗ Δ[n]) :=
  SSet.prismPatternMap_id

example {n : ℕ} :
    SSet.cohPatternMap (fun b _ => b) =
      (CartesianMonoidalCategory.fst SSet.coherentIso Δ[n] :
        SSet.coherentIso.{u} ⊗ Δ[n] ⟶ SSet.coherentIso.{u}) :=
  SSet.cohPatternMap_id_bool

example {n : ℕ} :
    SSet.prismPatternMap (fun _ _ => false) OrderHom.id =
      SSet.const SSet.coherentIso.x₀ ▷ Δ[n] :=
  SSet.prismPatternMap_constFalse_id

/-- Sections at vertices compute componentwise, and restricting a
pattern map along a section gives a Bool endomap. -/
example {X : SSet.{u}} {m : ℕ} (κ : Fin (m + 1))
    {Δ : SimplexCategoryᵒᵖ} (s : X.obj Δ) :
    ((SSet.prismSectionAt X κ).app Δ s).1 = s :=
  SSet.prismSectionAt_app_fst X κ s

example {n : ℕ} (P : Bool → Fin (n + 1) → Bool) (κ : Fin (n + 1)) :
    SSet.prismSectionAt SSet.coherentIso.{u} κ ≫ SSet.cohPatternMap P =
      SSet.cohBoolEndo (fun b => P b κ) :=
  SSet.prismSectionAt_comp_cohPatternMap P κ

example : SSet.cohBoolEndo.{u} id = 𝟙 SSet.coherentIso.{u} :=
  SSet.cohBoolEndo_id

example : SSet.cohBoolEndo.{u} (fun _ => false) =
    SSet.const SSet.coherentIso.x₀ :=
  SSet.cohBoolEndo_const_false

example (X : SSet.{u}) :
    SSet.prismSectionZero X ≫ (X ◁ SSet.stdSimplex.δ 1) =
      SSet.prismSectionAt X 0 :=
  SSet.prismSectionZero_whiskerLeft_δ_one X

example (X : SSet.{u}) :
    SSet.prismSectionZero X ≫ (X ◁ SSet.stdSimplex.δ 0) =
      SSet.prismSectionAt X 1 :=
  SSet.prismSectionZero_whiskerLeft_δ_zero X

end PatternMaps

section ContractionEdges

variable (C : SSet.{u})

/-- The constant vertex is evaluation followed by the constant
section, it is classified by the constant map, and its own
evaluation is the original evaluation. -/
example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    SSet.coherentIso.endpointConstVertex C a =
      ((pre SSet.coherentIso.toDeltaZero).app C).app (op ⦋0⦌)
        (((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a) :=
  rfl

example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    SSet.coherentIso.endpointConstVertex C a =
      SSet.ihomVertexEquiv SSet.coherentIso C
        (SSet.const SSet.coherentIso.x₀ ≫
          (SSet.ihomVertexEquiv SSet.coherentIso C).symm a) :=
  SSet.coherentIso.endpointConstVertex_eq C a

example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    ((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌)
        (SSet.coherentIso.endpointConstVertex C a) =
      ((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a :=
  SSet.coherentIso.endpoint_app_endpointConstVertex C a

/-- The contraction edges have the expected endpoints and underlying
pattern prism simplices. -/
noncomputable example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    SSet.Edge a (SSet.coherentIso.endpointConstVertex C a) :=
  SSet.coherentIso.etaEdge C a

noncomputable example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    SSet.Edge (SSet.coherentIso.endpointConstVertex C a) a :=
  SSet.coherentIso.etaInvEdge C a

example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    (SSet.coherentIso.etaEdge C a).edge =
      SSet.ihomSimplexOfPrism
        (SSet.cohPatternMap SSet.coherentIso.etaPattern ≫
          (SSet.ihomVertexEquiv SSet.coherentIso C).symm a) :=
  rfl

/-- The contraction edge and its reverse compose to the identity,
witnessed by an explicit `CompStruct` and in the homotopy category. -/
noncomputable example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    SSet.Edge.CompStruct (SSet.coherentIso.etaEdge C a)
      (SSet.coherentIso.etaInvEdge C a) (SSet.Edge.id a) :=
  SSet.coherentIso.etaCompStruct C a

example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    (SSet.coherentIso.etaEdge C a).toHoHom ≫
        (SSet.coherentIso.etaInvEdge C a).toHoHom =
      𝟙 (SSet.HomotopyCategory.mk a :
        SSet.hoFunctor.obj ((ihom SSet.coherentIso.{u}).obj C)) :=
  SSet.coherentIso.eta_toHoHom_comp_etaInv C a

/-- The contraction edges evaluate to equality morphisms at the
endpoint. -/
example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    ((SSet.coherentIso.etaEdge C a).map
        ((pre SSet.coherentIso.endpointInclusion).app C)).toHoHom =
      eqToHom (congrArg SSet.HomotopyCategory.mk
        (SSet.coherentIso.endpoint_app_endpointConstVertex C a).symm) :=
  SSet.coherentIso.etaEdge_map_endpoint_toHoHom C a

example (a : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌) :
    ((SSet.coherentIso.etaInvEdge C a).map
        ((pre SSet.coherentIso.endpointInclusion).app C)).toHoHom =
      eqToHom (congrArg SSet.HomotopyCategory.mk
        (SSet.coherentIso.endpoint_app_endpointConstVertex C a)) :=
  SSet.coherentIso.etaInvEdge_map_endpoint_toHoHom C a

/-- Naturality of the contraction edge, and the prism description
of the constant-section image of an evaluated edge. -/
example {a b : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε : SSet.Edge a b) :
    ε.toHoHom ≫ (SSet.coherentIso.etaEdge C b).toHoHom =
      (SSet.coherentIso.etaEdge C a).toHoHom ≫
        (SSet.coherentIso.gfEdge C ε).toHoHom :=
  SSet.coherentIso.eta_natural C ε

example {a b : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε : SSet.Edge a b) :
    (SSet.coherentIso.gfEdge C ε).toHoHom =
      ((ε.map ((pre SSet.coherentIso.endpointInclusion).app C)).map
        ((pre SSet.coherentIso.toDeltaZero).app C)).toHoHom :=
  SSet.coherentIso.gfEdge_toHoHom C ε

example {a b : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε : SSet.Edge a b) :
    ((ε.map ((pre SSet.coherentIso.endpointInclusion).app C)).map
        ((pre SSet.coherentIso.toDeltaZero).app C)).edge =
      SSet.ihomSimplexOfPrism
        ((SSet.const SSet.coherentIso.x₀ ▷ Δ[1]) ≫
          SSet.ihomPrismOfSimplex ε.edge) :=
  SSet.coherentIso.map_endpoint_map_toDeltaZero_edge C ε

/-- The endpoint restrictions of the prism of an edge are its
classifying maps at the two ends. -/
example {a b : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε : SSet.Edge a b) :
    SSet.prismSectionAt SSet.coherentIso.{u} 0 ≫
        SSet.ihomPrismOfSimplex ε.edge =
      (SSet.ihomVertexEquiv SSet.coherentIso C).symm a :=
  SSet.coherentIso.prismSectionAt_zero_comp_ihomPrism_edge C ε

example {a b : ((ihom SSet.coherentIso.{u}).obj C) _⦋0⦌}
    (ε : SSet.Edge a b) :
    SSet.prismSectionAt SSet.coherentIso.{u} 1 ≫
        SSet.ihomPrismOfSimplex ε.edge =
      (SSet.ihomVertexEquiv SSet.coherentIso C).symm b :=
  SSet.coherentIso.prismSectionAt_one_comp_ihomPrism_edge C ε

end ContractionEdges

end CoherentIsoEndpointTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

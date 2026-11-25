/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoCategorical

/-! # The endpoint inclusion into `coherentIso`: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoCategorical`:
the endpoint inclusion `Δ[0] ⟶ SSet.coherentIso` and its strict retraction,
the internal-hom vertex dictionary `SSet.ihomVertexEquiv` and its
compatibility with precomposition, the evaluation-at-a-vertex formulas
for the canonical evaluations `(MonoidalClosed.unitIsoSelf C).hom` and
`(SSet.evalDeltaZeroIso C).hom`, the object-level evaluation formula and
the unconditional essential surjectivity of endpoint evaluation, the
equivalence edge attached to a map out of `SSet.coherentIso`, and the
conditional assembly
from the two prism-extension properties (fullness, faithfulness, the
`IsEquivalence` conclusion, the categorical-equivalence conclusion, and
both directions of the full-and-faithful criterion). These tests cover
only this module's conditional assembly; the unconditional categorical
equivalence is proved downstream in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint`
and tested there.
-/

@[expose] public section

open CategoryTheory MonoidalClosed MonoidalCategory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CoherentIsoCategoricalTest

section EndpointInclusion

/-- The endpoint inclusion is the Yoneda map of the source vertex, and
equivalently the constant map at that vertex, at a variable universe and at
universe `0`. -/
example : SSet.coherentIso.endpointInclusion.{u} =
    SSet.yonedaEquiv.symm SSet.coherentIso.x₀ :=
  rfl

example : SSet.coherentIso.endpointInclusion.{u} =
    SSet.const SSet.coherentIso.x₀ :=
  SSet.coherentIso.endpointInclusion_eq_const

example : SSet.coherentIso.endpointInclusion.{0} =
    SSet.const SSet.coherentIso.x₀ :=
  SSet.coherentIso.endpointInclusion_eq_const

/-- The endpoint inclusion classifies the source vertex under
`SSet.yonedaEquiv`. -/
example : SSet.yonedaEquiv SSet.coherentIso.endpointInclusion.{u} =
    SSet.coherentIso.x₀ :=
  Equiv.apply_symm_apply _ _

/-- The endpoint inclusion is a strict section of the terminal map. -/
example : SSet.coherentIso.endpointInclusion.{u} ≫
      SSet.coherentIso.toDeltaZero = 𝟙 (Δ[0] : SSet.{u}) :=
  SSet.coherentIso.endpointInclusion_comp_toDeltaZero

/-- The terminal map is the unique map to `Δ[0]`: it agrees with any other
map `SSet.coherentIso ⟶ Δ[0]`, for instance the constant one. -/
example : SSet.coherentIso.toDeltaZero.{u} =
    SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end EndpointInclusion

section VertexDictionary

variable {A B C : SSet.{u}}

/-- Precomposition on vertices is precomposition of classifying maps. -/
example (f : B ⟶ A) (g : A ⟶ C) :
    ((pre f).app C).app (op ⦋0⦌) (SSet.ihomVertexEquiv A C g) =
      SSet.ihomVertexEquiv B C (f ≫ g) :=
  SSet.ihomVertexEquiv_pre_app f g

/-- Specialised to the endpoint inclusion: evaluating the vertex classified
by `g` gives the vertex classified by the constant map at the source
vertex of `g`. -/
example (g : SSet.coherentIso.{u} ⟶ C) :
    ((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv SSet.coherentIso C g) =
      SSet.ihomVertexEquiv (Δ[0]) C
        (SSet.const (g.app (op ⦋0⦌) SSet.coherentIso.x₀)) := by
  rw [SSet.ihomVertexEquiv_pre_app, SSet.coherentIso.endpointInclusion_eq_const,
    SSet.const_comp]

/-- The same evaluation formula after passage to homotopy categories. -/
example (g : SSet.coherentIso.{u} ⟶ C) :
    (SSet.hoFunctor.map
        ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv SSet.coherentIso C g)) =
      SSet.HomotopyCategory.mk
        (SSet.ihomVertexEquiv (Δ[0]) C
          (SSet.const (g.app (op ⦋0⦌) SSet.coherentIso.x₀))) :=
  SSet.coherentIso.hoPre_endpointInclusion_obj_mk_ihomVertexEquiv C g

end VertexDictionary

section EssentialSurjectivity

/-- Endpoint evaluation is essentially surjective for every simplicial set,
with no quasicategory hypothesis. -/
example (C : SSet.{u}) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.EssSurj :=
  SSet.coherentIso.hoPre_endpointInclusion_essSurj C

example :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app
        (Δ[2] : SSet.{u}))).toFunctor.EssSurj :=
  SSet.coherentIso.hoPre_endpointInclusion_essSurj _

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.EssSurj :=
  SSet.coherentIso.hoPre_endpointInclusion_essSurj C

example (C : SSet.{0}) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.EssSurj :=
  SSet.coherentIso.hoPre_endpointInclusion_essSurj C

/-- Unpacked essential surjectivity: every object of `h Fun(Δ[0], C)` is
isomorphic to an evaluated object. -/
example (C : SSet.{u})
    (b : SSet.hoFunctor.obj ((ihom (Δ[0] : SSet.{u})).obj C)) :
    ∃ a, Nonempty
      ((SSet.hoFunctor.map
          ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.obj a ≅
        b) :=
  (SSet.coherentIso.hoPre_endpointInclusion_essSurj C).mem_essImage b

end EssentialSurjectivity

section EquivalenceEdges

variable {C : SSet.{u}}

/-- Every map out of `SSet.coherentIso` sends the forward edge to an
equivalence edge. -/
example (g : SSet.coherentIso.{u} ⟶ C) :
    (SSet.coherentIso.hom.map g).IsEquivalence :=
  SSet.coherentIso.isEquivalence_hom_map g

/-- For a constant map, the resulting equivalence edge is an identity edge
up to the edge equivalence itself: it is the identity edge at the
constant vertex. -/
example (c : C _⦋0⦌) :
    (SSet.coherentIso.hom.map (SSet.const c :
      SSet.coherentIso.{u} ⟶ C)).IsEquivalence :=
  SSet.coherentIso.isEquivalence_hom_map _

/-- The backward edge behaves the same way, through its own inverse
structure (with inverse the forward edge) and preservation of equivalences
under maps. -/
example (g : SSet.coherentIso.{u} ⟶ C) :
    (SSet.coherentIso.inv.map g).IsEquivalence :=
  ({ inv := SSet.coherentIso.hom
     homInvId := SSet.coherentIso.invHomId
     invHomId := SSet.coherentIso.homInvId } :
    SSet.coherentIso.inv.InvStruct).isEquivalence.map g

end EquivalenceEdges

section ExtensionProperties

variable (C : SSet.{u})

/-- The edge extension property unfolds to its defining lifting statement. -/
example : SSet.coherentIso.edgeExtensionProperty C ↔
    ∀ {a a' : ((ihom SSet.coherentIso).obj C) _⦋0⦌}
      (ε' : SSet.Edge
        (((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a)
        (((pre SSet.coherentIso.endpointInclusion).app C).app (op ⦋0⦌) a')),
      ∃ ε : SSet.Edge a a',
        (SSet.HomotopyCategory.homMk (ε.map ((pre SSet.coherentIso.endpointInclusion).app C))) =
          (SSet.HomotopyCategory.homMk ε') :=
  Iff.rfl

/-- The composition extension property unfolds to its defining lifting
statement. -/
example : SSet.coherentIso.compExtensionProperty C ↔
    ∀ {a b c : ((ihom SSet.coherentIso).obj C) _⦋0⦌}
      {ε₁ : SSet.Edge a b} {ε₂ : SSet.Edge b c} {ε₁₂ : SSet.Edge a c},
      Nonempty (SSet.Edge.CompStruct
          (ε₁.map ((pre SSet.coherentIso.endpointInclusion).app C))
          (ε₂.map ((pre SSet.coherentIso.endpointInclusion).app C))
          (ε₁₂.map ((pre SSet.coherentIso.endpointInclusion).app C))) →
        Nonempty (SSet.Edge.CompStruct ε₁ ε₂ ε₁₂) :=
  Iff.rfl

end ExtensionProperties

section ConditionalAssembly

variable (C : SSet.{u}) [SSet.Quasicategory C]

/-- Fullness from the edge extension property. -/
example (h : SSet.coherentIso.edgeExtensionProperty C) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.Full :=
  SSet.coherentIso.hoPre_endpointInclusion_full_of_edgeExtensionProperty C h

/-- Faithfulness from the composition extension property. -/
example (h : SSet.coherentIso.compExtensionProperty C) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.Faithful :=
  SSet.coherentIso.hoPre_endpointInclusion_faithful_of_compExtensionProperty C h

/-- The evaluation functor is an equivalence under both extension
properties. -/
example (hE : SSet.coherentIso.edgeExtensionProperty C)
    (hC : SSet.coherentIso.compExtensionProperty C) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.IsEquivalence :=
  SSet.coherentIso.hoPre_endpointInclusion_isEquivalence_of_extensions C hE hC

/-- The conditional main theorem: extension properties for all
quasicategories give the categorical equivalence. -/
example (h : ∀ (K : SSet.{u}), SSet.Quasicategory K →
      SSet.coherentIso.edgeExtensionProperty K ∧
        SSet.coherentIso.compExtensionProperty K) :
    SSet.categoricalEquivalences.{u} SSet.coherentIso.endpointInclusion :=
  SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions h

/-- The categorical conclusion unpacks, through `mem_iff`, to the
`IsEquivalence` statement for a chosen quasicategory. -/
example (h : ∀ (K : SSet.{u}), SSet.Quasicategory K →
      SSet.coherentIso.edgeExtensionProperty K ∧
        SSet.coherentIso.compExtensionProperty K) :
    (SSet.hoFunctor.map
      ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.IsEquivalence :=
  (SSet.categoricalEquivalences.mem_iff
      SSet.coherentIso.endpointInclusion).1
    (SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions h)
    C inferInstance

/-- Both directions of the full-and-faithful criterion. -/
example (h : SSet.categoricalEquivalences.{u}
      SSet.coherentIso.endpointInclusion) :
    (SSet.hoFunctor.map
        ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.Full ∧
      (SSet.hoFunctor.map
        ((pre SSet.coherentIso.endpointInclusion).app C)).toFunctor.Faithful :=
  SSet.categoricalEquivalences_coherentIso_endpointInclusion_iff.1 h C
    inferInstance

example (h : ∀ (K : SSet.{u}), SSet.Quasicategory K →
      (SSet.hoFunctor.map
          ((pre SSet.coherentIso.endpointInclusion).app K)).toFunctor.Full ∧
        (SSet.hoFunctor.map
          ((pre SSet.coherentIso.endpointInclusion).app K)).toFunctor.Faithful) :
    SSet.categoricalEquivalences.{u} SSet.coherentIso.endpointInclusion :=
  SSet.categoricalEquivalences_coherentIso_endpointInclusion_iff.2 h

/-- Composing the conditional endpoint result with an identity stays inside
categorical equivalences, by the composition closure from the formal
calculus. -/
example (h : ∀ (K : SSet.{u}), SSet.Quasicategory K →
      SSet.coherentIso.edgeExtensionProperty K ∧
        SSet.coherentIso.compExtensionProperty K) :
    SSet.categoricalEquivalences.{u}
      (SSet.coherentIso.endpointInclusion ≫ 𝟙 SSet.coherentIso.{u}) :=
  MorphismProperty.comp_mem _ _ _
    (SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions h)
    (MorphismProperty.id_mem _ _)

end ConditionalAssembly

end CoherentIsoCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeGeneral

/-! # Cobase change into general quasicategories (packet T34): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeGeneral`:
vertex evaluations of equivalence edges and core membership of
equivalence edges in functor objects, sub-claim (i) for vertices
lifting to `Fun(A, core C)` (in particular for maps factoring
through the core on the nose), the formal failure of sub-claim
(ii) (abstractly for any non-equivalence edge, and concretely for
the non-isomorphism `0 ⟶ 1` in `nerve (Fin 2)`), fullness of
precomposition with a cobase change along a monomorphism
(abstractly, for nerves as targets, and for the pushout of the
inner horn inclusion `Λ[2, 1].ι` along itself), the prism strict
extension property, isofibration, and raw inner/isofibration membership along
`∂Δ[0].ι` into a general quasicategory (at a variable universe,
at universe `0`, into a nerve, and into a core), the
raw inner/isofibration form of the prism reduction with inputs
from the boundary-zero and Kan cases, essential surjectivity plus
fullness of a cobase change granted the isofibration input (from
the inner anodyne case and from the boundary-zero case), and the
assembly of cobase-change stability from the (A) isofibration and
faithfulness inputs, with (A) supplied by the inner anodyne case
and by the boundary-zero case so that in each instance only
faithfulness remains as a hypothesis.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CobaseChangeGeneralTest

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

section PointwiseCore

/-- Vertex evaluations of an equivalence edge are equivalences in
`C`: abstractly, at universe `0`, and for the identity edge. -/
example (C : SSet.{u}) {a₀ a₁ : ((ihom A).obj C) _⦋0⦌}
    {e : SSet.Edge a₀ a₁} (he : e.IsEquivalence)
    (v : (Δ[0] : SSet.{u}) ⟶ A) :
    ((e.map ((MonoidalClosed.pre v).app C)).map
      (SSet.evalDeltaZeroIso C).hom).IsEquivalence :=
  he.eval_vertex v

example (C : SSet.{0}) {a₀ a₁ : ((ihom Δ[2]).obj C) _⦋0⦌}
    {e : SSet.Edge a₀ a₁} (he : e.IsEquivalence)
    (v : (Δ[0] : SSet.{0}) ⟶ (Δ[2] : SSet.{0})) :
    ((e.map ((MonoidalClosed.pre v).app C)).map
      (SSet.evalDeltaZeroIso C).hom).IsEquivalence :=
  he.eval_vertex v

example (C : SSet.{u}) (a : ((ihom A).obj C) _⦋0⦌)
    (v : (Δ[0] : SSet.{u}) ⟶ A) :
    (((SSet.Edge.id a).map ((MonoidalClosed.pre v).app C)).map
      (SSet.evalDeltaZeroIso C).hom).IsEquivalence :=
  (SSet.Edge.isEquivalence_id a).eval_vertex v

/-- An equivalence edge of `Fun(A, C)` is a `1`-simplex of
`core (Fun(A, C))`, and conversely through
`SSet.mem_core_obj_one_iff`. -/
example (C : SSet.{u}) {a₀ a₁ : ((ihom A).obj C) _⦋0⦌}
    {e : SSet.Edge a₀ a₁} (he : e.IsEquivalence) :
    e.edge ∈ (SSet.core ((ihom A).obj C)).obj (Opposite.op ⦋1⦌) :=
  he.mem_core_edge_ihom

example (C : SSet.{u}) {a₀ a₁ : ((ihom A).obj C) _⦋0⦌}
    {e : SSet.Edge a₀ a₁}
    (hmem : e.edge ∈ (SSet.core ((ihom A).obj C)).obj (Opposite.op ⦋1⦌)) :
    e.IsEquivalence :=
  (SSet.mem_core_obj_one_iff.mp hmem).of_edge_eq rfl

/-- Sub-claim (i): vertices lifting to `Fun(A, core C)` have all
edge images equivalences; in particular this holds for a map
factoring through the core on the nose. -/
example (C : SSet.{u}) {g : A ⟶ C}
    (hlift : ∃ bt : ((ihom A).obj (SSet.core C : SSet.{u})) _⦋0⦌,
      ((ihom A).map (SSet.core C).ι).app (Opposite.op ⦋0⦌) bt =
        SSet.ihomVertexEquiv A C g)
    (s : A _⦋1⦌) :
    (SSet.Edge.mk' (g.app (Opposite.op ⦋1⦌) s)).IsEquivalence :=
  SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core hlift s

example (C : SSet.{u}) (G : A ⟶ (SSet.core C : SSet.{u}))
    (s : A _⦋1⦌) :
    (SSet.Edge.mk'
      ((G ≫ (SSet.core C).ι).app (Opposite.op ⦋1⦌) s)).IsEquivalence :=
  SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core
    ⟨SSet.ihomVertexEquiv A (SSet.core C : SSet.{u}) G,
      SSet.ihomVertexEquiv_ihom_map G (SSet.core C).ι⟩ s

/-- Failure of sub-claim (ii), abstractly: from any
non-equivalence edge, an equivalence (identity) edge in
`Fun(Δ[1], C)` whose endpoint does not lift to `Fun(Δ[1], core C)`. -/
example {C : SSet.{u}} {x₀ x₁ : C _⦋0⦌} (e₀ : SSet.Edge x₀ x₁)
    (h₀ : ¬ e₀.IsEquivalence) :
    ∃ b : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌,
      (SSet.Edge.id b).IsEquivalence ∧
        ¬ ∃ bt : ((ihom (Δ[1] : SSet.{u})).obj
              (SSet.core C : SSet.{u})) _⦋0⦌,
          ((ihom (Δ[1] : SSet.{u})).map (SSet.core C).ι).app
              (Opposite.op ⦋0⦌) bt = b :=
  SSet.exists_equivalence_edge_endpoint_not_lift_core e₀ h₀

/-- Failure of sub-claim (ii), concretely at `C = nerve (Fin 2)`
and the non-isomorphism `0 ⟶ 1`. -/
example :
    ∃ b : ((ihom (Δ[1] : SSet.{0})).obj
          (CategoryTheory.nerve (Fin 2))) _⦋0⦌,
      (SSet.Edge.id b).IsEquivalence ∧
        ¬ ∃ bt : ((ihom (Δ[1] : SSet.{0})).obj
              (SSet.core (CategoryTheory.nerve (Fin 2)) : SSet.{0})) _⦋0⦌,
          ((ihom (Δ[1] : SSet.{0})).map
              (SSet.core (CategoryTheory.nerve (Fin 2))).ι).app
              (Opposite.op ⦋0⦌) bt = b := by
  have hnoniso : ¬ IsIso (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) := by
    intro h
    have h10 : (1 : Fin 2) ≤ 0 :=
      leOfHom (inv (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
    exact absurd h10 (by decide)
  exact SSet.exists_equivalence_edge_endpoint_not_lift_core
    (CategoryTheory.nerve.edgeMk (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
    (fun he => hnoniso ((SSet.Edge.isEquivalence_nerve_edgeMk_iff _).1 he))

end PointwiseCore

section Fullness

/-- Fullness of precomposition with a cobase change along a
monomorphism, for a variable quasicategory target and for nerves. -/
example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f) (C : SSet.{u})
    [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre f').app C)).toFunctor.Full :=
  SSet.hoFunctor_pre_full_of_isPushout sq hf C

example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f) (D : Type u) [Category.{u} D] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f').app
      (CategoryTheory.nerve D))).toFunctor.Full :=
  SSet.hoFunctor_pre_full_of_isPushout sq hf _

/-- For the concrete pushout of the inner horn inclusion
`Λ[2, 1].ι` along itself, at a variable universe and at `0`. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app
        C)).toFunctor.Full :=
  SSet.hoFunctor_pre_full_of_isPushout
    (IsPushout.of_hasPushout Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) C

example (C : SSet.{0}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app
        C)).toFunctor.Full :=
  SSet.hoFunctor_pre_full_of_isPushout
    (IsPushout.of_hasPushout Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) C

/-- In surjectivity form: every morphism downstairs is the image
of a morphism upstairs. -/
example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f) (C : SSet.{u})
    [SSet.Quasicategory C]
    {P Q : SSet.hoFunctor.obj ((ihom Y).obj C)}
    (φ : (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.obj P ⟶
      (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.obj Q) :
    ∃ ψ : P ⟶ Q,
      (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.map ψ =
        φ := by
  have := SSet.hoFunctor_pre_full_of_isPushout sq hf C
  exact (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.map_surjective φ

end Fullness

section BoundaryZero

/-- The prism strict extension property along `∂Δ[0].ι` needs
no hypothesis on the target in dimension `0`; in particular it
holds into a general quasicategory, at a variable universe, at
`0`, into a nerve, and into a core. -/
example (C : SSet.{u}) :
    SSet.HoPrePrismStrictExtension ∂Δ[0].ι C :=
  SSet.hoPrePrismStrictExtension_boundary_zero C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.HoPrePrismStrictExtension ∂Δ[0].ι C :=
  SSet.hoPrePrismStrictExtension_boundary_zero C

example (C : SSet.{0}) [SSet.Quasicategory C] :
    SSet.HoPrePrismStrictExtension ∂Δ[0].ι C :=
  SSet.hoPrePrismStrictExtension_boundary_zero C

example (D : Type u) [Category.{u} D] :
    SSet.HoPrePrismStrictExtension ∂Δ[0].ι (CategoryTheory.nerve D) :=
  SSet.hoPrePrismStrictExtension_boundary_zero _

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.HoPrePrismStrictExtension ∂Δ[0].ι (SSet.core C : SSet.{u}) :=
  SSet.hoPrePrismStrictExtension_boundary_zero _

/-- The isofibration and raw inner/isofibration forms along
`∂Δ[0].ι`, including through the membership characterization of
raw inner/isofibration membership. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre ∂Δ[0].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_boundary_zero C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre ∂Δ[0].ι).app C) :=
  SSet.innerIsoFibrations_pre_app_boundary_zero C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.innerFibrations ((MonoidalClosed.pre ∂Δ[0].ι).app C) ∧
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre ∂Δ[0].ι).app C)).toFunctor.IsIsofibration :=
  (SSet.innerIsoFibrations.mem_iff _).1
    (SSet.innerIsoFibrations_pre_app_boundary_zero C)

/-- The raw inner/isofibration form of the prism reduction, with
the prism input from the boundary-zero case and from the Kan
complex case of packet T31. -/
example [Mono i] (C : SSet.{u}) [SSet.Quasicategory C]
    (h : SSet.HoPrePrismStrictExtension i C) :
    SSet.innerIsoFibrations ((MonoidalClosed.pre i).app C) :=
  SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension C h

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre ∂Δ[0].ι).app C) :=
  SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension C
    (SSet.hoPrePrismStrictExtension_boundary_zero C)

example [Mono i] (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre i).app C) :=
  SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension C
    (SSet.hoPrePrismStrictExtension_of_kanComplex i C)

end BoundaryZero

section Assembly

/-- Essential surjectivity plus fullness of a cobase change,
granted the isofibration input at one target; with the input from
the inner anodyne case for the concrete horn pushout. -/
example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f) (C : SSet.{u})
    [SSet.Quasicategory C]
    (hIso : (SSet.hoFunctor.map
      ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration) :
    (SSet.hoFunctor.map
        ((MonoidalClosed.pre f').app C)).toFunctor.EssSurj ∧
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre f').app C)).toFunctor.Full :=
  SSet.hoFunctor_pre_essSurj_full_of_isPushout_of_isIsofibration sq hf C hIso

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
        (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app
          C)).toFunctor.EssSurj ∧
      (SSet.hoFunctor.map ((MonoidalClosed.pre
        (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app
          C)).toFunctor.Full :=
  SSet.hoFunctor_pre_essSurj_full_of_isPushout_of_isIsofibration
    (IsPushout.of_hasPushout Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) C
    (SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
      (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C)

/-- Cobase change of a categorical equivalence along a
monomorphism, granted the (A) isofibration and faithfulness
inputs (fullness is supplied by the module under test). -/
example (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.categoricalEquivalences f)
    (hIso : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration)
    (hFaith : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre f').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    sq hf hIso hFaith

/-- With (A) supplied by the landed inner anodyne case, so that
only faithfulness remains as a hypothesis. -/
example (sq : IsPushout i f f' j) [Mono i]
    (hi : SSet.innerAnodyneExtensions i)
    (hf : SSet.categoricalEquivalences f)
    (hFaith : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre f').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    sq hf
    (fun C _ =>
      SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)
    hFaith

/-- With (A) supplied by the boundary-zero case of this packet:
cobase change along `∂Δ[0].ι`, granted only faithfulness. -/
example {X₀ Y₀ : SSet.{u}} {f₀ : (∂Δ[0] : SSet.{u}) ⟶ X₀}
    {f₀' : (Δ[0] : SSet.{u}) ⟶ Y₀} {j₀ : X₀ ⟶ Y₀}
    (sq : IsPushout ∂Δ[0].ι f₀ f₀' j₀)
    (hf : SSet.categoricalEquivalences f₀)
    (hFaith : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map
        ((MonoidalClosed.pre f₀').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f₀' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    sq hf
    (fun C _ => SSet.hoFunctor_pre_isIsofibration_boundary_zero C)
    hFaith

end Assembly

end CobaseChangeGeneralTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

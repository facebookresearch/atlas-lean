/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChange
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint
public import MathlibExt.CategoryTheory.MorphismProperty.Limits

/-! # Cobase-change stability of categorical equivalences: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChange`:
precomposition with a monomorphism is an inner fibration, precomposition
with an inner anodyne extension induces an isofibration on homotopy
categories (in particular for inner horn inclusions and for nerves as
targets), the characterization of that isofibration property by lifting
of equivalence edges and its strict simplex-level sufficient condition,
and the proved cobase-change cases — inner anodyne top leg, inner
anodyne left leg (including the packaged
`IsStableUnderCobaseChangeAgainst` instance and its `of_isPushout`
client form), and isomorphism left leg, with the concrete gate example
of the coherent-isomorphism endpoint inclusion pushed out along an
identity.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CobaseChangeTest

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

section InnerFibration

/-- Precomposition with a monomorphism into a quasicategory is an inner
fibration, at a variable universe and at universe `0`. -/
example [Mono i] (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.InnerFibration ((MonoidalClosed.pre i).app C) :=
  SSet.innerFibration_pre_app_of_mono i C

example (C : SSet.{0}) [SSet.Quasicategory C] (n : ℕ) :
    SSet.InnerFibration ((MonoidalClosed.pre ∂Δ[n].ι).app C) :=
  SSet.innerFibration_pre_app_of_mono ∂Δ[n].ι C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.InnerFibration ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app C) :=
  SSet.innerFibration_pre_app_of_mono Λ[2, (1 : Fin 3)].ι C

end InnerFibration

section IsofibrationInnerAnodyne

/-- Precomposition with an inner anodyne extension induces an isofibration
on homotopy categories of functor objects. -/
example (hi : SSet.innerAnodyneExtensions i) (C : SSet.{u})
    [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C

/-- The concrete inner horns `Λ[2, 1]` and `Λ[3, 1]`. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C

example (C : SSet.{0}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre Λ[3, (1 : Fin 4)].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C

/-- Target a nerve: nerves are quasicategories, so precomposition with an
inner horn into a nerve induces an isofibration on homotopy categories. -/
example (D : Type u) [Category.{u} D] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app
      (CategoryTheory.nerve D))).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) _

/-- The same isofibration rephrased through the membership form for
`innerIsoFibrations`: precomposition with an inner horn is an inner
fibration (previous section) and an isofibration on homotopy categories. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app C) := by
  rw [SSet.innerIsoFibrations.mem_iff]
  exact ⟨(SSet.innerFibration_iff _).1 (SSet.innerFibration_pre_app_of_mono _ C),
    SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
      (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C⟩

end IsofibrationInnerAnodyne

section EdgeLifting

/-- The isofibration property on `hFun` is equivalent to lifting of
equivalence edges, in both directions. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration ↔
      SSet.HoPreEquivalenceEdgeLifting i C :=
  SSet.hoFunctor_pre_isIsofibration_iff C

example (C : SSet.{u}) [SSet.Quasicategory C]
    (h : (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration) :
    SSet.HoPreEquivalenceEdgeLifting i C :=
  (SSet.hoFunctor_pre_isIsofibration_iff C).1 h

example (C : SSet.{u}) [SSet.Quasicategory C]
    (h : SSet.HoPreEquivalenceEdgeLifting i C) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  (SSet.hoFunctor_pre_isIsofibration_iff C).2 h

/-- Equivalence edges lift along precomposition with an inner horn,
by combining the inner anodyne isofibration theorem with the
characterization. -/
example (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.HoPreEquivalenceEdgeLifting Λ[2, (1 : Fin 3)].ι C :=
  (SSet.hoFunctor_pre_isIsofibration_iff C).1
    (SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
      (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C)

/-- Strict simplex-level lifts of equivalence edges give the lifting
property, for an arbitrary target (no quasicategory assumption). -/
example (C : SSet.{u})
    (h : ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
      (e : SSet.Edge (((MonoidalClosed.pre i).app C).app _ b) a'),
        e.IsEquivalence →
          ∃ (b' : ((ihom B).obj C) _⦋0⦌)
            (_hb' : ((MonoidalClosed.pre i).app C).app _ b' = a')
            (e' : SSet.Edge b b'),
            e'.IsEquivalence ∧ (e'.map ((MonoidalClosed.pre i).app C)).edge = e.edge) :
    SSet.HoPreEquivalenceEdgeLifting i C :=
  SSet.hoPreEquivalenceEdgeLifting_of_strict_lift (C := C) h

end EdgeLifting

section CobaseCases

/-- Cobase change of an inner anodyne extension along any map. -/
example (sq : IsPushout i f f' j) (hf : SSet.innerAnodyneExtensions f) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_innerAnodyneExtensions sq hf

/-- Cobase change of a categorical equivalence along an inner anodyne
extension, pointwise and through the packaged stability instance. -/
example (sq : IsPushout i f f' j) (hi : SSet.innerAnodyneExtensions i)
    (hf : SSet.categoricalEquivalences f) : SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_along_innerAnodyneExtensions sq hi hf

example :
    SSet.categoricalEquivalences.{u}.IsStableUnderCobaseChangeAgainst
      SSet.innerAnodyneExtensions.{u} :=
  inferInstance

example :
    SSet.categoricalEquivalences.{0}.IsStableUnderCobaseChangeAgainst
      SSet.innerAnodyneExtensions.{0} :=
  inferInstance

example (sq : IsPushout i f f' j) (hi : SSet.innerAnodyneExtensions i)
    (hf : SSet.categoricalEquivalences f) : SSet.categoricalEquivalences f' :=
  MorphismProperty.IsStableUnderCobaseChangeAgainst.of_isPushout
    (inferInstance :
      SSet.categoricalEquivalences.IsStableUnderCobaseChangeAgainst
        SSet.innerAnodyneExtensions) sq hi hf

example (hi : SSet.innerAnodyneExtensions i) :
    SSet.categoricalEquivalences.IsStableUnderCobaseChangeAlong i :=
  (inferInstance :
      SSet.categoricalEquivalences.IsStableUnderCobaseChangeAgainst
        SSet.innerAnodyneExtensions).isStableUnderCobaseChangeAlong i hi

/-- Cobase change along an isomorphism. -/
example (sq : IsPushout i f f' j) [IsIso i]
    (hf : SSet.categoricalEquivalences f) : SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_along_isIso sq hf

end CobaseCases

section ConcretePushouts

/-- The pushout of the inner horn inclusion `Λ[2, 1].ι` along itself is a
categorical equivalence, by both the inner-anodyne-top-leg and the
inner-anodyne-left-leg theorems. -/
example : SSet.categoricalEquivalences.{u}
    (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι) :=
  SSet.categoricalEquivalences.of_isPushout_of_innerAnodyneExtensions
    (IsPushout.of_hasPushout _ _)
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide))

example : SSet.categoricalEquivalences.{u}
    (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι) :=
  SSet.categoricalEquivalences.of_isPushout_along_innerAnodyneExtensions
    (IsPushout.of_hasPushout _ _)
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide))

/-- Gate example: the coherent-isomorphism endpoint inclusion
`Δ[0] ⟶ SSet.coherentIso` (categorical by packet T22) pushed out along
the identity of `Δ[0]` is categorical. -/
example : SSet.categoricalEquivalences.{u}
    (pushout.inl (𝟙 (Δ[0] : SSet.{u}))
      SSet.coherentIso.endpointInclusion) :=
  SSet.categoricalEquivalences.of_isPushout_along_isIso
    (IsPushout.of_hasPushout _ _)
    SSet.categoricalEquivalences.coherentIso_endpointInclusion

example : SSet.categoricalEquivalences.{0}
    (pushout.inl (𝟙 (Δ[0] : SSet.{0}))
      SSet.coherentIso.endpointInclusion) :=
  SSet.categoricalEquivalences.of_isPushout_along_isIso
    (IsPushout.of_hasPushout _ _)
    SSet.categoricalEquivalences.coherentIso_endpointInclusion

end ConcretePushouts

end CobaseChangeTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

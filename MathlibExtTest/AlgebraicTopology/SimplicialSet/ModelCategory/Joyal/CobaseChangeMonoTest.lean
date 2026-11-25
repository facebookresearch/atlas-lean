/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeMono

/-! # Cobase change along monomorphisms (packet T31): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeMono`:
strict edge lifting along precomposition with a monomorphism into a
Kan complex with prescribed source or target vertex (including the
boundary inclusions `∂Δ[n].ι` and the horn inclusion `Λ[2, 1].ι`),
the prism strict extension property and the isofibration on homotopy
categories it implies for Kan targets at a variable universe and at
universe `0`, precomposition into a Kan complex as a categorical
fibration, essential surjectivity of a cobase change into a Kan
complex, closure of the prism extension and isofibration properties
under composition (with inputs supplied by the Kan, inner anodyne,
and isomorphism cases), and edge correction through an inner
fibration, in particular through precomposition with a monomorphism
into a quasicategory.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CobaseChangeMonoTest

variable {A B D X Y E B' : SSet.{u}} {i : A ⟶ B} {j : B ⟶ D}
  {f : A ⟶ X} {f' : B ⟶ Y} {k : X ⟶ Y}

section KanLifts

/-- Strict edge lifting into a Kan complex with prescribed source,
for a variable monomorphism. -/
example [Mono i] (C : SSet.{u}) [SSet.KanComplex C]
    {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
    (e : SSet.Edge (((MonoidalClosed.pre i).app C).app _ b) a') :
    ∃ (b' : ((ihom B).obj C) _⦋0⦌)
      (_hb' : ((MonoidalClosed.pre i).app C).app _ b' = a')
      (e' : SSet.Edge b b'), e'.IsEquivalence ∧
        (e'.map ((MonoidalClosed.pre i).app C)).edge = e.edge :=
  SSet.exists_strict_edge_lift_src_of_kanComplex i C e

/-- With prescribed target. -/
example [Mono i] (C : SSet.{u}) [SSet.KanComplex C]
    {b' : ((ihom B).obj C) _⦋0⦌} {a : ((ihom A).obj C) _⦋0⦌}
    (e : SSet.Edge a (((MonoidalClosed.pre i).app C).app _ b')) :
    ∃ (b : ((ihom B).obj C) _⦋0⦌)
      (_hb : ((MonoidalClosed.pre i).app C).app _ b = a)
      (e' : SSet.Edge b b'), e'.IsEquivalence ∧
        (e'.map ((MonoidalClosed.pre i).app C)).edge = e.edge :=
  SSet.exists_strict_edge_lift_tgt_of_kanComplex i C e

/-- For the boundary inclusion `∂Δ[2].ι` and for the inner horn
inclusion `Λ[2, 1].ι`, at universe `0`. -/
example (C : SSet.{0}) [SSet.KanComplex C]
    {b : ((ihom Δ[2]).obj C) _⦋0⦌} {a' : ((ihom (∂Δ[2] : SSet.{0})).obj C) _⦋0⦌}
    (e : SSet.Edge (((MonoidalClosed.pre ∂Δ[2].ι).app C).app _ b) a') :
    ∃ (b' : ((ihom Δ[2]).obj C) _⦋0⦌)
      (_hb' : ((MonoidalClosed.pre ∂Δ[2].ι).app C).app _ b' = a')
      (e' : SSet.Edge b b'), e'.IsEquivalence ∧
        (e'.map ((MonoidalClosed.pre ∂Δ[2].ι).app C)).edge = e.edge :=
  SSet.exists_strict_edge_lift_src_of_kanComplex ∂Δ[2].ι C e

example (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.HoPrePrismStrictExtension Λ[2, (1 : Fin 3)].ι C :=
  SSet.hoPrePrismStrictExtension_of_kanComplex Λ[2, (1 : Fin 3)].ι C

example [Mono i] (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.HoPrePrismStrictExtension i C :=
  SSet.hoPrePrismStrictExtension_of_kanComplex i C

end KanLifts

section KanIsofibration

/-- TODO(T26-A) for Kan targets: a variable monomorphism, universe
`0`, and the identity. -/
example [Mono i] (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex i C

example (C : SSet.{0}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre ∂Δ[3].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex ∂Δ[3].ι C

example (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (𝟙 A)).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex (𝟙 A) C

/-- The boundary case, named, for every `n` and at `n = 0, 2`. -/
example (n : ℕ) (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre ∂Δ[n].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex n C

example (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre ∂Δ[0].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex 0 C

example (C : SSet.{0}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre ∂Δ[2].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex 2 C

/-- Precomposition with a monomorphism into a Kan complex satisfies
`innerIsoFibrations`; through the membership form its homotopy
functor is the isofibration above. -/
example [Mono i] (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre i).app C) :=
  SSet.innerIsoFibrations_pre_app_of_mono_kanComplex i C

example [Mono i] (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.innerFibrations ((MonoidalClosed.pre i).app C) ∧
      (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  (SSet.innerIsoFibrations.mem_iff _).1
    (SSet.innerIsoFibrations_pre_app_of_mono_kanComplex i C)

end KanIsofibration

section KanEssSurj

/-- Essential surjectivity of a cobase change into a Kan complex. -/
example (sq : IsPushout i f f' k) [Mono i]
    (hf : SSet.categoricalEquivalences f) (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_kanComplex sq hf C

/-- For the concrete pushout of the inner horn inclusion
`Λ[2, 1].ι` along itself. -/
example (C : SSet.{u}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_kanComplex
    (IsPushout.of_hasPushout Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) C

end KanEssSurj

section CompClosure

/-- Prism strict extension is closed under composition; with the
inputs supplied by the Kan case this is again the Kan case for the
composite monomorphism `i ≫ j`. -/
example [Mono i] [Mono j] (C : SSet.{u}) [SSet.KanComplex C] :
    SSet.HoPrePrismStrictExtension (i ≫ j) C :=
  SSet.HoPrePrismStrictExtension.comp C
    (SSet.hoPrePrismStrictExtension_of_kanComplex i C)
    (SSet.hoPrePrismStrictExtension_of_kanComplex j C)

/-- The isofibration conclusion is closed under composition with
no hypothesis on the target at all: abstractly, from the two
isofibration inputs alone. -/
example (C : SSet.{u})
    (hi : (SSet.hoFunctor.map
      ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration)
    (hj : (SSet.hoFunctor.map
      ((MonoidalClosed.pre j).app C)).toFunctor.IsIsofibration) :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (i ≫ j)).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_comp C hi hj

/-- The isofibration conclusion is closed under composition, with
inputs from the inner anodyne and Kan cases and from the inner
anodyne and isomorphism cases. -/
example (hi : SSet.innerAnodyneExtensions i) (C : SSet.{u})
    [SSet.KanComplex C] [Mono j] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (i ≫ j)).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_comp C
    (SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)
    (SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex j C)

example (hi : SSet.innerAnodyneExtensions i) [IsIso j] (C : SSet.{u})
    [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (i ≫ j)).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_comp C
    (SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)
    (SSet.hoFunctor_pre_isIsofibration_of_isIso C)

example (C : SSet.{0}) [SSet.KanComplex C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (Λ[2, (1 : Fin 3)].ι ≫ 𝟙 Δ[2])).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_comp C
    (SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
      (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide)) C)
    (SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex (𝟙 Δ[2]) C)

end CompClosure

section EdgeCorrection

/-- Edge correction through a general inner fibration. -/
example (p : E ⟶ B') (hp : SSet.InnerFibration p) [SSet.Quasicategory B']
    {x₀ x₁ : E _⦋0⦌} (u : SSet.Edge x₀ x₁)
    (w : SSet.Edge (p.app _ x₀) (p.app _ x₁))
    (h : (SSet.HomotopyCategory.homMk w) = (SSet.HomotopyCategory.homMk (u.map p))) :
    ∃ u' : SSet.Edge x₀ x₁, (SSet.HomotopyCategory.homMk u') = (SSet.HomotopyCategory.homMk u) ∧
      (u'.map p).edge = w.edge :=
  SSet.exists_edge_correction_of_innerFibration p hp u w h

/-- Through precomposition with a monomorphism into a quasicategory:
the correction step of TODO(T26-B) fullness. -/
example [Mono i] (C : SSet.{u}) [SSet.Quasicategory C]
    {x₀ x₁ : ((ihom B).obj C) _⦋0⦌} (u : SSet.Edge x₀ x₁)
    (w : SSet.Edge (((MonoidalClosed.pre i).app C).app _ x₀)
      (((MonoidalClosed.pre i).app C).app _ x₁))
    (h : (SSet.HomotopyCategory.homMk w) = (SSet.HomotopyCategory.homMk (u.map
        ((MonoidalClosed.pre i).app C)))) :
    ∃ u' : SSet.Edge x₀ x₁, (SSet.HomotopyCategory.homMk u') = (SSet.HomotopyCategory.homMk u) ∧
      (u'.map ((MonoidalClosed.pre i).app C)).edge = w.edge :=
  SSet.exists_edge_correction_of_innerFibration ((MonoidalClosed.pre i).app C)
    (SSet.innerFibration_pre_app_of_mono i C) u w h

/-- For the boundary inclusion `∂Δ[2].ι` into a quasicategory, at
universe `0`, correcting to the identity edge when the homotopy
classes agree. -/
example (C : SSet.{0}) [SSet.Quasicategory C]
    {x₀ x₁ : ((ihom Δ[2]).obj C) _⦋0⦌} (u : SSet.Edge x₀ x₁)
    (w : SSet.Edge (((MonoidalClosed.pre ∂Δ[2].ι).app C).app _ x₀)
      (((MonoidalClosed.pre ∂Δ[2].ι).app C).app _ x₁))
    (h : (SSet.HomotopyCategory.homMk w) = (SSet.HomotopyCategory.homMk (u.map
        ((MonoidalClosed.pre ∂Δ[2].ι).app C)))) :
    ∃ u' : SSet.Edge x₀ x₁, (SSet.HomotopyCategory.homMk u') = (SSet.HomotopyCategory.homMk u) ∧
      (u'.map ((MonoidalClosed.pre ∂Δ[2].ι).app C)).edge = w.edge :=
  SSet.exists_edge_correction_of_innerFibration
    ((MonoidalClosed.pre ∂Δ[2].ι).app C)
    (SSet.innerFibration_pre_app_of_mono ∂Δ[2].ι C) u w h

end EdgeCorrection

end CobaseChangeMonoTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

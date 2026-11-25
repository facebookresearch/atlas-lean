/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeComplete

/-! # Cobase-change completion (packet T30): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeComplete`:
precomposition sends pushouts to pullbacks (including the
commutativity of the square and the gluing interface at `Δ[0]`,
`Δ[1]` and a variable source), precomposition with an isomorphism
induces an isofibration on homotopy categories (in particular for
identities, for maps from isomorphisms, and for nerves as
targets), essential surjectivity of precomposition with a cobase
change granted the isofibration property and unconditionally along
inner anodyne extensions, the prism form of strict
equivalence-edge lifting and the isofibration it implies, and the
assembly of cobase-change stability from the (A) isofibration and
(B) full-and-faithful inputs, with the (A) input supplied by the
landed inner anodyne and isomorphism cases.
-/

@[expose] public section

open CategoryTheory Limits MonoidalClosed MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace CobaseChangeCompleteTest

variable {A B X Y W : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

section Pullback

/-- Precomposition sends a pushout square to a pullback square of
functor objects, for an arbitrary target, at a variable universe
and at universe `0`. -/
example (sq : IsPushout i f f' j) (C : SSet.{u}) :
    IsPullback ((MonoidalClosed.pre f').app C) ((MonoidalClosed.pre j).app C)
      ((MonoidalClosed.pre i).app C) ((MonoidalClosed.pre f).app C) :=
  SSet.isPullback_pre_app_of_isPushout sq C

example {A₀ B₀ X₀ Y₀ : SSet.{0}} {i₀ : A₀ ⟶ B₀} {f₀ : A₀ ⟶ X₀}
    {f'₀ : B₀ ⟶ Y₀} {j₀ : X₀ ⟶ Y₀} (sq : IsPushout i₀ f₀ f'₀ j₀) (C : SSet.{0}) :
    IsPullback ((MonoidalClosed.pre f'₀).app C) ((MonoidalClosed.pre j₀).app C)
      ((MonoidalClosed.pre i₀).app C) ((MonoidalClosed.pre f₀).app C) :=
  SSet.isPullback_pre_app_of_isPushout sq C

/-- The pullback square commutes, and its target may be a nerve. -/
example (sq : IsPushout i f f' j) (C : SSet.{u}) :
    ((MonoidalClosed.pre f').app C) ≫ ((MonoidalClosed.pre i).app C) =
      ((MonoidalClosed.pre j).app C) ≫ ((MonoidalClosed.pre f).app C) :=
  (SSet.isPullback_pre_app_of_isPushout sq C).w

example (sq : IsPushout i f f' j) (D : Type u) [Category.{u} D] :
    IsPullback ((MonoidalClosed.pre f').app (CategoryTheory.nerve D))
      ((MonoidalClosed.pre j).app (CategoryTheory.nerve D))
      ((MonoidalClosed.pre i).app (CategoryTheory.nerve D))
      ((MonoidalClosed.pre f).app (CategoryTheory.nerve D)) :=
  SSet.isPullback_pre_app_of_isPushout sq _

/-- The pushout of the inner horn inclusion `Λ[2, 1].ι` along itself
becomes a pullback after precomposition. -/
example (C : SSet.{u}) :
    IsPullback
      ((MonoidalClosed.pre (pushout.inl Λ[2, (1 : Fin 3)].ι
        Λ[2, (1 : Fin 3)].ι)).app C)
      ((MonoidalClosed.pre (pushout.inr Λ[2, (1 : Fin 3)].ι
        Λ[2, (1 : Fin 3)].ι)).app C)
      ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app C)
      ((MonoidalClosed.pre Λ[2, (1 : Fin 3)].ι).app C) :=
  SSet.isPullback_pre_app_of_isPushout (IsPushout.of_hasPushout _ _) C

/-- Gluing: agreeing pairs of maps into `Fun(B, C)` and `Fun(X, C)`
lift to `Fun(Y, C)`, for a variable source and at `Δ[0]` and
`Δ[1]`. -/
example (sq : IsPushout i f f' j) (C : SSet.{u})
    (u : W ⟶ (ihom B).obj C) (v : W ⟶ (ihom X).obj C)
    (h : u ≫ (MonoidalClosed.pre i).app C = v ≫ (MonoidalClosed.pre f).app C) :
    ∃ w : W ⟶ (ihom Y).obj C, w ≫ (MonoidalClosed.pre f').app C = u ∧
      w ≫ (MonoidalClosed.pre j).app C = v :=
  SSet.exists_pre_lift_of_isPushout sq C u v h

example (sq : IsPushout i f f' j) (C : SSet.{u})
    (u : Δ[0] ⟶ (ihom B).obj C) (v : Δ[0] ⟶ (ihom X).obj C)
    (h : u ≫ (MonoidalClosed.pre i).app C = v ≫ (MonoidalClosed.pre f).app C) :
    ∃ w : (Δ[0] : SSet.{u}) ⟶ (ihom Y).obj C,
      w ≫ (MonoidalClosed.pre f').app C = u ∧
        w ≫ (MonoidalClosed.pre j).app C = v :=
  SSet.exists_pre_lift_of_isPushout sq C u v h

example (sq : IsPushout i f f' j) (C : SSet.{u})
    (u : Δ[1] ⟶ (ihom B).obj C) (v : Δ[1] ⟶ (ihom X).obj C)
    (h : u ≫ (MonoidalClosed.pre i).app C = v ≫ (MonoidalClosed.pre f).app C) :
    ∃ w : (Δ[1] : SSet.{u}) ⟶ (ihom Y).obj C,
      w ≫ (MonoidalClosed.pre f').app C = u ∧
        w ≫ (MonoidalClosed.pre j).app C = v :=
  SSet.exists_pre_lift_of_isPushout sq C u v h

end Pullback

section IsofibrationIsIso

/-- Precomposition with an isomorphism induces an isofibration on
homotopy categories of functor objects. -/
example [IsIso i] (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_isIso C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre (𝟙 A)).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_isIso C

example (e : A ≅ B) (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre e.hom).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_isIso C

example (C : SSet.{0}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map
      ((MonoidalClosed.pre (𝟙 (Δ[0] : SSet.{0}))).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_isIso C

/-- Target a nerve: precomposition with the identity of `Δ[0]` into
a nerve induces an isofibration on homotopy categories. -/
example (D : Type u) [Category.{u} D] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre (𝟙 (Δ[0] : SSet.{u}))).app
      (CategoryTheory.nerve D))).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_isIso _

/-- Through the membership form for `innerIsoFibrations`:
precomposition with an isomorphism has raw inner/isofibration membership. -/
example [IsIso i] (C : SSet.{u}) [SSet.Quasicategory C] :
    SSet.innerIsoFibrations ((MonoidalClosed.pre i).app C) := by
  rw [SSet.innerIsoFibrations.mem_iff]
  exact ⟨(SSet.innerFibration_iff _).1 (SSet.innerFibration_pre_app_of_mono _ C),
    SSet.hoFunctor_pre_isIsofibration_of_isIso C⟩

end IsofibrationIsIso

section EssSurj

/-- Essential surjectivity of precomposition with a cobase change,
granted the isofibration property of the left leg. -/
example (sq : IsPushout i f f' j) (hf : SSet.categoricalEquivalences f)
    (C : SSet.{u}) [SSet.Quasicategory C]
    (hIso : (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C hIso

/-- With the isofibration input supplied by the isomorphism case
of (A). -/
example (sq : IsPushout i f f' j) [IsIso i] (hf : SSet.categoricalEquivalences f)
    (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C
    (SSet.hoFunctor_pre_isIsofibration_of_isIso C)

/-- Unconditionally along an inner anodyne extension, at a variable
universe and for the concrete pushout of `Λ[2, 1].ι` along itself. -/
example (sq : IsPushout i f f' j) (hi : SSet.innerAnodyneExtensions i)
    (hf : SSet.categoricalEquivalences f) (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_along_innerAnodyneExtensions sq hi hf C

example (C : SSet.{u}) [SSet.Quasicategory C] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app C)).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_along_innerAnodyneExtensions
    (IsPushout.of_hasPushout _ _)
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) C

example (D : Type u) [Category.{u} D] :
    (SSet.hoFunctor.map ((MonoidalClosed.pre
      (pushout.inl Λ[2, (1 : Fin 3)].ι Λ[2, (1 : Fin 3)].ι)).app
        (CategoryTheory.nerve D))).toFunctor.EssSurj :=
  SSet.hoFunctor_pre_essSurj_of_isPushout_along_innerAnodyneExtensions
    (IsPushout.of_hasPushout _ _)
    (SSet.innerAnodyneExtensions.horn_ι (by decide) (by decide))
    (SSet.categoricalEquivalences.horn_ι (by decide) (by decide)) _

end EssSurj

section PrismExtension

/-- The prism strict extension property is equivalent to the
strict simplex-level lifting property, and implies the
isofibration property into a quasicategory. -/
example (C : SSet.{u}) :
    SSet.HoPrePrismStrictExtension i C ↔
      ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
        (e : SSet.Edge (((MonoidalClosed.pre i).app C).app _ b) a'),
          e.IsEquivalence →
            ∃ (b' : ((ihom B).obj C) _⦋0⦌)
              (_hb' : ((MonoidalClosed.pre i).app C).app _ b' = a')
              (e' : SSet.Edge b b'),
              e'.IsEquivalence ∧ (e'.map ((MonoidalClosed.pre i).app C)).edge = e.edge :=
  SSet.hoPrePrismStrictExtension_iff_strict_lift C

example (C : SSet.{u}) [SSet.Quasicategory C]
    (h : SSet.HoPrePrismStrictExtension i C) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension C h

example (C : SSet.{0}) [SSet.Quasicategory C]
    (h : SSet.HoPrePrismStrictExtension ∂Δ[2].ι C) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre ∂Δ[2].ι).app C)).toFunctor.IsIsofibration :=
  SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension C h

end PrismExtension

section Assembly

/-- Cobase change of a categorical equivalence along a
monomorphism, granted the (A) isofibration and (B)
full-and-faithful inputs. -/
example (sq : IsPushout i f f' j) [Mono i] (hf : SSet.categoricalEquivalences f)
    (hIso : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration)
    (hFF : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Full ∧
        (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    sq hf hIso hFF

/-- With the (A) input supplied by the landed inner anodyne case,
so that only (B) remains as a hypothesis, and similarly with the
isomorphism case. -/
example (sq : IsPushout i f f' j) [Mono i] (hi : SSet.innerAnodyneExtensions i)
    (hf : SSet.categoricalEquivalences f)
    (hFF : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Full ∧
        (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    sq hf (fun C _ => SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)
    hFF

example (sq : IsPushout i f f' j) [IsIso i] (hf : SSet.categoricalEquivalences f)
    (hFF : ∀ (C : SSet.{u}) [SSet.Quasicategory C],
      (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Full ∧
        (SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor.Faithful) :
    SSet.categoricalEquivalences f' :=
  SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    sq hf (fun C _ => SSet.hoFunctor_pre_isIsofibration_of_isIso C) hFF

end Assembly

end CobaseChangeCompleteTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

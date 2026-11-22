/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerFibrationCategorical

/-!
# Boundary lifting, slice comparison, and descent data: client tests

The tests exercise dimension-zero boundary lifting, genuine pullback transport,
the slice comparison and its projections, pointwise mapping-space triviality,
and pre-fibrant descent data. Universe-zero checks use the same valid APIs.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace InnerFibrationCategoricalTest

section BoundaryLifting

variable {X S : SSet.{u}} {p : X ⟶ S}

example : SSet.modelCategoryQuillen.I.rlp p ↔
    ∀ n : ℕ, HasLiftingProperty (SSet.boundary n).ι p :=
  SSet.modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary p

example (hp : SSet.modelCategoryQuillen.I.rlp p) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι p :=
  (SSet.modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary p).mp hp n

example (h : Function.Surjective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (SSet.boundary 0).ι p :=
  SSet.hasLiftingProperty_boundary_zero_of_surjective_app_zero h

example (h : Function.Bijective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (SSet.boundary 0).ι p :=
  SSet.hasLiftingProperty_boundary_zero_of_bijective_app_zero h

example (h : Function.Bijective (p.app (op ⦋0⦌))) :
    SSet.modelCategoryQuillen.I.rlp p ↔
      ∀ n : ℕ, 1 ≤ n → HasLiftingProperty (SSet.boundary n).ι p :=
  SSet.modelCategoryQuillen_I_rlp_iff_of_bijective_app_zero h

example : HasLiftingProperty (SSet.boundary 0).ι (𝟙 X) :=
  SSet.hasLiftingProperty_boundary_zero_of_surjective_app_zero (p := 𝟙 X)
    (fun b ↦ ⟨b, by simp⟩)

end BoundaryLifting

section DescentTransport

variable {X Y S T : SSet.{u}} {p : X ⟶ S} {f : S ⟶ T} {q : Y ⟶ T}
  {g : X ⟶ Y} (sq : IsPullback g p q f)

example (hq : SSet.modelCategoryQuillen.I.rlp q) :
    SSet.modelCategoryQuillen.I.rlp p :=
  SSet.modelCategoryQuillen_I_rlp_of_isPullback sq hq

example (hg : SSet.categoricalEquivalences g)
    (hf : SSet.categoricalEquivalences f)
    (hp : SSet.categoricalEquivalences p) :
    SSet.categoricalEquivalences q :=
  SSet.categoricalEquivalences_right_of_isPullback sq hg hf hp

example (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    Function.Bijective (g.app (op ⦋0⦌)) :=
  SSet.bijective_app_zero_fst_of_isPullback sq hf

example (hf : Function.Bijective (f.app (op ⦋0⦌)))
    (hp : Function.Bijective (p.app (op ⦋0⦌))) :
    Function.Bijective (q.app (op ⦋0⦌)) :=
  SSet.bijective_app_zero_right_of_isPullback sq hf hp

example (hgi : SSet.innerAnodyneExtensions g)
    (hfi : SSet.innerAnodyneExtensions f)
    (hp : SSet.categoricalEquivalences p) :
    SSet.categoricalEquivalences q :=
  SSet.categoricalEquivalences_right_of_isPullback sq
    (SSet.categoricalEquivalences.of_innerAnodyneExtensions hgi)
    (SSet.categoricalEquivalences.of_innerAnodyneExtensions hfi) hp

end DescentTransport

section SliceComparison

variable {X S : SSet.{u}} {p : X ⟶ S} (x : (Δ[0] : SSet.{u}) ⟶ X)

example : SSet.sliceUnder X x ⟶
    pullback (SSet.sliceUnder.proj S (x ≫ p)) p :=
  SSet.sliceUnderComparison (p := p) x

example : SSet.sliceUnderComparison (p := p) x ≫
      pullback.fst (SSet.sliceUnder.proj S (x ≫ p)) p =
    SSet.sliceUnder.map X x p :=
  SSet.sliceUnderComparison_fst x

example : SSet.sliceUnderComparison (p := p) x ≫
      pullback.snd (SSet.sliceUnder.proj S (x ≫ p)) p =
    SSet.sliceUnder.proj X x :=
  SSet.sliceUnderComparison_snd x

end SliceComparison

section MappingSpacePredicate

variable {X S T : SSet.{u}} {p : X ⟶ S} {q : S ⟶ T}

example (a b : (Δ[0] : SSet.{u}) ⟶ X) : Prop :=
  SSet.modelCategoryQuillen.I.rlp (SSet.mappingSpaceLeft.map X a b p)

example : SSet.MappingSpaceLeftTrivialFibration (𝟙 X) :=
  SSet.mappingSpaceLeftTrivialFibration_id

example (hp : SSet.MappingSpaceLeftTrivialFibration p)
    (hq : SSet.MappingSpaceLeftTrivialFibration q) :
    SSet.MappingSpaceLeftTrivialFibration (p ≫ q) :=
  hp.comp hq

example (hp : SSet.MappingSpaceLeftTrivialFibration p)
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Surjective
      ((SSet.mappingSpaceLeft.map X a b p).app (op ⦋0⦌)) :=
  hp.surjective_app_zero a b

example (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Surjective
      ((SSet.mappingSpaceLeft.map X a b (𝟙 X)).app (op ⦋0⦌)) :=
  SSet.mappingSpaceLeftTrivialFibration_id.surjective_app_zero a b

end MappingSpacePredicate

section PiZeroShadow

variable {X S : SSet.{u}} {f : X ⟶ S}

example [SSet.Quasicategory X] (hf : SSet.categoricalEquivalences f)
    {x y : X _⦋0⦌}
    (e' : SSet.Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : SSet.Edge x y, (e.map f).toHoHom = e'.toHoHom :=
  hf.exists_edge_map_toHoHom_eq e'

example (hf : SSet.categoricalEquivalences f) {x y : X _⦋0⦌}
    {e₁ e₂ : SSet.Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  hf.edge_map_toHoHom_injective h

example [SSet.Quasicategory X] {x y : X _⦋0⦌}
    (e' : SSet.Edge x y) :
    ∃ e : SSet.Edge x y, (e.map (𝟙 X)).toHoHom = e'.toHoHom :=
  (SSet.categoricalEquivalences.of_isIso (𝟙 X)).exists_edge_map_toHoHom_eq e'

end PiZeroShadow

section PreFibrantDescentData

variable {X S : SSet.{u}} {p : X ⟶ S}

example : Prop := SSet.HasPreFibrantDescentDatum p

example : Prop := SSet.PreFibrantDescentReplacementExists.{u}

example [SSet.InnerFibration p] [SSet.IsPreFibrant S] :
    SSet.HasPreFibrantDescentDatum p :=
  SSet.hasPreFibrantDescentDatum_of_isPreFibrant

example (h : SSet.PreFibrantDescentReplacementExists.{u})
    [SSet.InnerFibration p] : SSet.HasPreFibrantDescentDatum p :=
  SSet.HasPreFibrantDescentDatum.of_replacementExists h

end PreFibrantDescentData

section UniverseZero

variable {X S : SSet.{0}} {p : X ⟶ S}

example (h : Function.Bijective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (SSet.boundary 0).ι p :=
  SSet.hasLiftingProperty_boundary_zero_of_bijective_app_zero h

example : SSet.MappingSpaceLeftTrivialFibration (𝟙 (Δ[1] : SSet.{0})) :=
  SSet.mappingSpaceLeftTrivialFibration_id

end UniverseZero

end InnerFibrationCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end

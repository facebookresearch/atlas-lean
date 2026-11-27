/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Equivalence
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Stability of minimal Kan fibrations

A minimal Kan fibration is a horn-lifting simplicial map whose fiberwise homotopic simplices
with equal base and boundary are equal. This morphism property contains identities and is
invariant under isomorphisms and retracts in the arrow category.

It is also stable under arbitrary exhibited base change. Thus both chosen pullback projections,
with the minimal map in the appropriate cospan position, are minimal fibrations. All statements
use an arbitrary simplicial-set universe u.

Mathematical source: Joël Riou's minimal-fibration construction, following Goerss–Jardine,
Simplicial Homotopy Theory, Chapter I, Section 10.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial SSet HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet
namespace MinimalFibration

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. These maps define the morphism property of
minimal fibrations. -/
def minimalFibrations : MorphismProperty SSet.{u} :=
  fun _ _ p => IsMinimalFibration p

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. Membership in the minimal-fibration
morphism property is equivalent to the explicit minimal-fibration predicate. -/
lemma minimalFibrations_iff {E B : SSet.{u}} {p : E ⟶ B} :
    minimalFibrations p ↔ IsMinimalFibration p :=
  Iff.rfl

/-- For a simplicial map f:E→E′, equality of the boundary restrictions of n-simplices x,y in E
implies equality of the boundaries of f(x),f(y). -/
private lemma boundary_eq_map {E E' : SSet.{u}} {n : ℕ}
    (f : E ⟶ E') {x y : E _⦋n⦌}
    (h : (boundary n).ι ≫ yonedaEquiv.symm x =
      (boundary n).ι ≫ yonedaEquiv.symm y) :
    (boundary n).ι ≫ yonedaEquiv.symm (f.app _ x) =
      (boundary n).ι ≫ yonedaEquiv.symm (f.app _ y) := by
  have h' := congrArg (fun k => k ≫ f) h
  simpa only [Category.assoc, SSet.yonedaEquiv_symm_comp] using h'

/-- In a pullback square of sets, two elements of the pullback are equal if their images under both
projections are equal. -/
private lemma isPullback_types_ext {A B C D : Type u} {t : A ⟶ B}
    {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (h : IsPullback t l r b) {x y : A}
    (h₁ : t x = t y) (h₂ : l x = l y) : x = y := by
  apply (PullbackCone.IsLimit.equivPullbackObj h.isLimit).injective
  ext <;> assumption

/-- For any simplicial set B, the identity B→B is a minimal Kan fibration. -/
theorem isMinimalFibration_id (B : SSet.{u}) :
    IsMinimalFibration (𝟙 B) := by
  refine ⟨inferInstance, ?_⟩
  intro n x y hbase _ _
  simpa using hbase

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. If p is a retract of a minimal fibration p′
in the arrow category, then p is a minimal fibration. -/
theorem isMinimalFibration_of_retract
    {E B E' B' : SSet.{u}} {p : E ⟶ B} {p' : E' ⟶ B'}
    (h : RetractArrow p p') (hp' : IsMinimalFibration p') :
    IsMinimalFibration p := by
  have hp_fibration : Fibration p := by
    have hp'_fibration : Fibration p' := hp'.1
    rw [HomotopicalAlgebra.fibration_iff] at hp'_fibration ⊢
    exact (fibrations SSet.{u}).of_retract h hp'_fibration
  refine ⟨hp_fibration, ?_⟩
  intro n x y _ hboundary hxy
  obtain ⟨Hxy⟩ := hxy
  let Hxy' := Hxy.map h.i
  have hboundary' := boundary_eq_map h.i.left hboundary
  have hi : h.i.left.app _ x = h.i.left.app _ y :=
    hp'.2 _ _ Hxy'.base_app_eq hboundary' ⟨Hxy'⟩
  have hret (a : E _⦋n⦌) : h.r.left.app _ (h.i.left.app _ a) = a := by
    change (h.i.left ≫ h.r.left).app (op ⦋n⦌) a =
      (𝟙 E : E ⟶ E).app (op ⦋n⦌) a
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app h.left.retract (op ⦋n⦌)) a
  calc
    x = h.r.left.app _ (h.i.left.app _ x) := (hret x).symm
    _ = h.r.left.app _ (h.i.left.app _ y) := congrArg (h.r.left.app _) hi
    _ = y := hret y

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. An isomorphism of arrows p≅p′ transports
minimal-fibration structure from p′ to p. -/
theorem isMinimalFibration_of_arrow_iso
    {E B E' B' : SSet.{u}} {p : E ⟶ B} {p' : E' ⟶ B'}
    (e : Arrow.mk p ≅ Arrow.mk p') (hp' : IsMinimalFibration p') :
    IsMinimalFibration p :=
  isMinimalFibration_of_retract (Retract.ofIso e) hp'

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. Isomorphic arrows p,p′ are minimal
fibrations simultaneously. -/
theorem isMinimalFibration_iff_of_arrow_iso
    {E B E' B' : SSet.{u}} {p : E ⟶ B} {p' : E' ⟶ B'}
    (e : Arrow.mk p ≅ Arrow.mk p') :
    IsMinimalFibration p ↔ IsMinimalFibration p' :=
  ⟨isMinimalFibration_of_arrow_iso e.symm,
    isMinimalFibration_of_arrow_iso e⟩

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. In any exhibited pullback square with maps
t:E′→E, p′:E′→B′, p:E→B and b:B′→B, minimality of p implies minimality of p′. -/
theorem isMinimalFibration_of_isPullback
    {E' E B' B : SSet.{u}} {t : E' ⟶ E} {p' : E' ⟶ B'}
    {p : E ⟶ B} {b : B' ⟶ B} (sq : IsPullback t p' p b)
    (hp : IsMinimalFibration p) : IsMinimalFibration p' := by
  have hp'_fibration : Fibration p' := by
    have hp_fibration : Fibration p := hp.1
    rw [SSet.modelCategoryQuillen.fibration_iff] at hp_fibration ⊢
    exact MorphismProperty.of_isPullback sq hp_fibration
  refine ⟨hp'_fibration, ?_⟩
  intro n x y hbase hboundary hxy
  let f : Arrow.mk p' ⟶ Arrow.mk p := Arrow.homMk t b sq.w
  obtain ⟨Hxy⟩ := hxy
  let Hxy' := Hxy.map f
  have hboundary' := boundary_eq_map t hboundary
  have ht : t.app _ x = t.app _ y :=
    hp.2 _ _ Hxy'.base_app_eq hboundary' ⟨Hxy'⟩
  exact isPullback_types_ext
    (sq.map ((evaluation _ _).obj (op ⦋n⦌))) ht hbase

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. For p:E→B minimal and f:A→B arbitrary, the
second projection E×_B A→A is a minimal fibration. -/
theorem isMinimalFibration_pullback_snd {E B A : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (hp : IsMinimalFibration p) :
    IsMinimalFibration (pullback.snd p f) :=
  isMinimalFibration_of_isPullback (IsPullback.of_hasPullback p f) hp

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. For p:E→B minimal and f:A→B arbitrary, the
first projection A×_B E→A is a minimal fibration. -/
theorem isMinimalFibration_pullback_fst {E B A : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (hp : IsMinimalFibration p) :
    IsMinimalFibration (pullback.fst f p) :=
  isMinimalFibration_of_isPullback (IsPullback.of_hasPullback f p).flip hp

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. The minimal-fibration morphism property
contains every identity. -/
instance minimalFibrations_containsIdentities :
    minimalFibrations.{u}.ContainsIdentities where
  id_mem B := isMinimalFibration_id B

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. The minimal-fibration morphism property is
stable under retracts in the arrow category. -/
instance minimalFibrations_isStableUnderRetracts :
    minimalFibrations.{u}.IsStableUnderRetracts where
  of_retract h hp := isMinimalFibration_of_retract h hp

/-- A simplicial map is a minimal Kan fibration when it has horn lifting and identifies fiberwise
homotopic simplices with the same base and boundary. The minimal-fibration morphism property is
stable under arbitrary pullback squares. -/
instance minimalFibrations_isStableUnderBaseChange :
    minimalFibrations.{u}.IsStableUnderBaseChange where
  of_isPullback sq hp := isMinimalFibration_of_isPullback sq hp

end MinimalFibration
end SSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Kan-complex weak equivalences

`KanComplex.W` is the class of maps between Kan complexes inducing an equivalence
of fundamental groupoids and bijections on every pointed homotopy group, together
with identity and composition stability and postcomposition-cancellation
(`HasOfPostcompProperty` and `postcomp_iff`) infrastructure.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial HomotopicalAlgebra MorphismProperty
open SSet.modelCategoryQuillen

namespace SSet

private lemma mapFundamentalGroupoid_id (X : SSet) :
    SSet.mapFundamentalGroupoid (𝟙 X) = 𝟭 (SSet.FundamentalGroupoid X) := by
  unfold SSet.mapFundamentalGroupoid
  have h1 : (truncation (2 : ℕ)).map (𝟙 X) = 𝟙 ((truncation (2 : ℕ)).obj X) := by simp
  rw [h1]
  exact SSet.Truncated.mapFundamentalGroupoid_id ((truncation (2 : ℕ)).obj X)

private lemma mapFundamentalGroupoid_comp {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.mapFundamentalGroupoid (f ≫ g) =
      SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g := by
  unfold SSet.mapFundamentalGroupoid
  have h1 : (truncation (2 : ℕ)).map (f ≫ g) =
      (truncation (2 : ℕ)).map f ≫ (truncation (2 : ℕ)).map g := by simp
  rw [h1]
  exact SSet.Truncated.mapFundamentalGroupoid_comp ((truncation (2 : ℕ)).map f)
    ((truncation (2 : ℕ)).map g)

namespace KanComplex

/-- Weak equivalences between Kan complexes for the Kan–Quillen model structure.

A morphism `f : X ⟶ Y` lies in `W` when `X` and `Y` are Kan complexes,
the induced functor `SSet.mapFundamentalGroupoid f` is an equivalence of
groupoids, and every based homotopy-group map
`KanComplex.π.map f rfl n : π n X x → π n Y (f.app _ x)` is bijective.
This is the structural predicate used by the identity, composition,
cancellation, and retract results; the precomposition proof uses the
fundamental-groupoid action to transport homotopy-group bijectivity from
image points to arbitrary basepoints. -/
def W : MorphismProperty SSet.{u} := fun {X Y} f =>
  KanComplex X ∧ KanComplex Y ∧
    (SSet.mapFundamentalGroupoid (X := X) (Y := Y) f).IsEquivalence ∧
    ∀ (n : ℕ) (x : X _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (X := X) (Y := Y) f rfl (n := n) (x := x))

/-- Constructor for `W`. -/
theorem W.mk {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : KanComplex X) (hY : KanComplex Y)
    (hEquiv : (SSet.mapFundamentalGroupoid f).IsEquivalence)
    (hBij : ∀ (n : ℕ) (x : X _⦋0⦌), Function.Bijective (KanComplex.π.map f rfl (n := n) (x := x))) :
    W f :=
  ⟨hX, hY, hEquiv, hBij⟩

/-- If `W f` then the source is Kan (fibrant). -/
theorem W.kanComplex_source {X Y : SSet.{u}} {f : X ⟶ Y} (hf : W f) : KanComplex X :=
  hf.1

/-- If `W f` then the target is Kan (fibrant). -/
theorem W.kanComplex_target {X Y : SSet.{u}} {f : X ⟶ Y} (hf : W f) : KanComplex Y :=
  hf.2.1

/-- The fundamental-groupoid functor induced by a weak equivalence is an
equivalence. -/
theorem W.isEquivalence_mapFundamentalGroupoid {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : W f) : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  hf.2.2.1

/-- Every based homotopy-group map induced by a weak equivalence is
bijective. -/
theorem W.bijective_piMap {X Y : SSet.{u}} {f : X ⟶ Y} (hf : W f)
    (n : ℕ) (x : X _⦋0⦌) :
    Function.Bijective (KanComplex.π.map f rfl (n := n) (x := x)) :=
  hf.2.2.2 n x

/-- Identity morphisms of Kan complexes are weak equivalences. -/
theorem W.id {X : SSet.{u}} [KanComplex X] : W (𝟙 X) := by
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · have h : SSet.mapFundamentalGroupoid (𝟙 X : X ⟶ X) = 𝟭 (SSet.FundamentalGroupoid X) :=
      SSet.mapFundamentalGroupoid_id X
    rw [h]
    infer_instance
  · intro n x
    have h_eq : KanComplex.π.map (𝟙 X : X ⟶ X) (rfl : (𝟙 X : X ⟶ X).app _ x = x) (n := n) =
        (fun q => q) := by
      funext q
      exact KanComplex.π.map_id_apply q
    rw [h_eq]
    exact Function.bijective_id

/-- Composition of weak equivalences is a weak equivalence. -/
theorem W.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) : W (f ≫ g) := by
  obtain ⟨hX, _hY, hEquivF, hBijF⟩ := hf
  obtain ⟨_hY', hZ, hEquivG, hBijG⟩ := hg
  refine ⟨hX, hZ, ?_, ?_⟩
  · have h_comp : SSet.mapFundamentalGroupoid (f ≫ g) =
        SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g :=
      SSet.mapFundamentalGroupoid_comp f g
    rw [h_comp]
    have : (SSet.mapFundamentalGroupoid f).IsEquivalence := hEquivF
    have : (SSet.mapFundamentalGroupoid g).IsEquivalence := hEquivG
    infer_instance
  · intro n x
    have h_eq : KanComplex.π.map (f ≫ g) (rfl : (f ≫ g).app _ x = (f ≫ g).app _ x) (n := n) =
        (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) ∘
          (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n)) := by
      funext q
      have h1 := KanComplex.π.map_comp (f := f) (g := g) (hx := rfl) (hy := rfl) (n := n) (x := x) q
      simp only at h1
      exact h1
    rw [h_eq]
    exact Function.Bijective.comp (hBijG n (f.app _ x)) (hBijF n x)

/-- Left cancellation: if `g` and `f ≫ g` are weak equivalences, so is `f`. -/
theorem W.of_postcomp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : W g) (hfg : W (f ≫ g)) : W f := by
  obtain ⟨hY, hZ, hEquivG, hBijG⟩ := hg
  obtain ⟨hX, _hZ', hEquivFG, hBijFG⟩ := hfg
  refine ⟨hX, hY, ?_, ?_⟩
  · have h_comp : SSet.mapFundamentalGroupoid (f ≫ g) =
        SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g :=
      SSet.mapFundamentalGroupoid_comp f g
    have hG : (SSet.mapFundamentalGroupoid g).IsEquivalence := hEquivG
    have hFG : (SSet.mapFundamentalGroupoid (f ≫ g)).IsEquivalence := hEquivFG
    rw [h_comp] at hFG
    have : (SSet.mapFundamentalGroupoid g).IsEquivalence := hG
    have : (SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g).IsEquivalence := hFG
    exact Functor.isEquivalence_of_comp_right (SSet.mapFundamentalGroupoid f)
      (SSet.mapFundamentalGroupoid g)
  · intro n x
    have hBijG_n := hBijG n (f.app _ x)
    have hBijFG_n := hBijFG n x
    have h_eq : KanComplex.π.map (f ≫ g) (rfl : (f ≫ g).app _ x = (f ≫ g).app _ x) (n := n) =
        (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) ∘
          (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n)) := by
      funext q
      have h1 := KanComplex.π.map_comp (f := f) (g := g) (hx := rfl) (hy := rfl) (n := n) (x := x) q
      simp only at h1
      exact h1
    have hBijComp : Function.Bijective
        ((KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) ∘
          (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n))) := by
      rw [← h_eq]
      exact hBijFG_n
    exact
      (Function.Bijective.of_comp_iff' hBijG_n
          (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n))).mp
        hBijComp

/-- `W` is stable under composition. -/
instance W.isStableUnderComposition : W.IsStableUnderComposition where
  comp_mem _ _ hf hg := W.comp hf hg

/-- `W` has the left-cancellation property (if `g` and `f ≫ g` are in `W`, so is `f`). -/
instance W.hasOfPostcompProperty : W.HasOfPostcompProperty W where
  of_postcomp _ _ hg hfg := W.of_postcomp hg hfg

/-- If `W g` then `W (f ≫ g) ↔ W f`. -/
theorem W.postcomp_iff {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : W g) : W (f ≫ g) ↔ W f :=
  ⟨fun hfg => W.of_postcomp hg hfg, fun hf => W.comp hf hg⟩
section RespectsIso

private lemma isEquivalence_mapFundamentalGroupoid_of_iso {X Y : SSet.{u}} (e : X ≅ Y) :
    (SSet.mapFundamentalGroupoid e.hom).IsEquivalence :=
  SSet.isEquivalence_mapFundamentalGroupoid e.hom
    (hf := by
      have h_eq :
          (truncation (2 : ℕ)).map e.hom =
            ((truncation (2 : ℕ)).mapIso e).hom := rfl
      rw [h_eq]
      infer_instance)

private lemma kanComplex_of_iso {X Y : SSet.{u}} (e : X ≅ Y) [KanComplex X] :
    KanComplex Y :=
  HomotopicalAlgebra.isFibrant_of_fibration e.inv

/-- Isomorphisms between Kan complexes are weak equivalences. -/
theorem W.ofIso {X Y : SSet.{u}} (e : X ≅ Y) [KanComplex X] [KanComplex Y] :
    W e.hom := by
  refine
    ⟨inferInstance, inferInstance, isEquivalence_mapFundamentalGroupoid_of_iso e,
      fun n x => ?_⟩
  exact (KanComplex.π.equivOfIso e rfl n).bijective

instance W.respectsIso : W.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk (P := W)
  · intro X Y Z e f hf
    have hY : KanComplex Y := hf.1
    have hZ : KanComplex Z := hf.2.1
    have hX : KanComplex X := kanComplex_of_iso e.symm
    have h_iso : W e.hom := @W.ofIso _ _ e hX hY
    exact W.comp h_iso hf
  · intro X Y Z e f hf
    have hX : KanComplex X := hf.1
    have hY : KanComplex Y := hf.2.1
    have hZ : KanComplex Z := kanComplex_of_iso e
    have h_iso : W e.hom := @W.ofIso _ _ e hY hZ
    exact W.comp hf h_iso

end RespectsIso

end KanComplex

end SSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Realization of pullbacks along a monomorphism

Geometric realization preserves the pullback of a simplicial cospan when its
left leg is a monomorphism. The realized pullback comparison is a bijection
on underlying points and an embedding, hence a topological isomorphism.
The corresponding simplicial pullback square therefore remains a pullback
square of topological spaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace SSet

private def preimageComparison {X Y : SSet.{u}} (B : Y.Subcomplex) (f : X ⟶ Y) :
    SSet.toTop.obj (B.preimage f : SSet.{u}) ⟶
      pullback (SSet.toTop.map B.ι) (SSet.toTop.map f) :=
  pullback.lift (SSet.toTop.map (B.fromPreimage f))
    (SSet.toTop.map (B.preimage f).ι) (by
      simpa only [← SSet.toTop.map_comp] using
        congrArg SSet.toTop.map (Subcomplex.fromPreimage_ι B f))

@[reassoc]
private lemma preimageComparison_fst {X Y : SSet.{u}}
    (B : Y.Subcomplex) (f : X ⟶ Y) :
    preimageComparison B f ≫
        pullback.fst (SSet.toTop.map B.ι) (SSet.toTop.map f) =
      SSet.toTop.map (B.fromPreimage f) := by
  unfold preimageComparison
  apply pullback.lift_fst

@[reassoc]
private lemma preimageComparison_snd {X Y : SSet.{u}}
    (B : Y.Subcomplex) (f : X ⟶ Y) :
    preimageComparison B f ≫
        pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f) =
      SSet.toTop.map (B.preimage f).ι := by
  unfold preimageComparison
  apply pullback.lift_snd

private theorem preservesLimit_cospan_ι {X Y : SSet.{u}}
    (B : Y.Subcomplex) (f : X ⟶ Y) :
    PreservesLimit (cospan B.ι f) SSet.toTop := by
  let sqS : IsPullback (B.fromPreimage f) (B.preimage f).ι B.ι f :=
    (Subcomplex.preimage_isPullback B f).flip
  let φ := preimageComparison B f
  have hSource : IsPullback
      ((forget TopCat).map (SSet.toTop.map (B.fromPreimage f)))
      ((forget TopCat).map (SSet.toTop.map (B.preimage f).ι))
      ((forget TopCat).map (SSet.toTop.map B.ι))
      ((forget TopCat).map (SSet.toTop.map f)) :=
    sqS.map (SSet.toTop ⋙ forget TopCat)
  have hTarget : IsPullback
      ((forget TopCat).map
        (pullback.fst (SSet.toTop.map B.ι) (SSet.toTop.map f)))
      ((forget TopCat).map
        (pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f)))
      ((forget TopCat).map (SSet.toTop.map B.ι))
      ((forget TopCat).map (SSet.toTop.map f)) :=
    (IsPullback.of_hasPullback (SSet.toTop.map B.ι)
      (SSet.toTop.map f)).map (forget TopCat)
  have hbij : Function.Bijective φ.hom := by
    constructor
    · intro x y hxy
      apply Types.ext_of_isPullback hSource
      · calc
          (SSet.toTop.map (B.fromPreimage f)) x =
              pullback.fst (SSet.toTop.map B.ι) (SSet.toTop.map f) (φ x) :=
            (ConcreteCategory.congr_hom
              (preimageComparison_fst B f) x).symm
          _ = pullback.fst (SSet.toTop.map B.ι)
              (SSet.toTop.map f) (φ y) := congrArg _ hxy
          _ = (SSet.toTop.map (B.fromPreimage f)) y :=
            ConcreteCategory.congr_hom (preimageComparison_fst B f) y
      · calc
          (SSet.toTop.map (B.preimage f).ι) x =
              pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f) (φ x) :=
            (ConcreteCategory.congr_hom
              (preimageComparison_snd B f) x).symm
          _ = pullback.snd (SSet.toTop.map B.ι)
              (SSet.toTop.map f) (φ y) := congrArg _ hxy
          _ = (SSet.toTop.map (B.preimage f).ι) y :=
            ConcreteCategory.congr_hom (preimageComparison_snd B f) y
    · intro z
      obtain ⟨x, hx₁, hx₂⟩ := Types.exists_of_isPullback hSource
        (((forget TopCat).map
          (pullback.fst (SSet.toTop.map B.ι) (SSet.toTop.map f))) z)
        (((forget TopCat).map
          (pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f))) z)
        (ConcreteCategory.congr_hom hTarget.w z)
      refine ⟨x, ?_⟩
      apply Types.ext_of_isPullback hTarget
      · calc
          pullback.fst (SSet.toTop.map B.ι) (SSet.toTop.map f) (φ x) =
              (SSet.toTop.map (B.fromPreimage f)) x :=
            ConcreteCategory.congr_hom (preimageComparison_fst B f) x
          _ = pullback.fst (SSet.toTop.map B.ι)
              (SSet.toTop.map f) z := hx₁
      · calc
          pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f) (φ x) =
              (SSet.toTop.map (B.preimage f).ι) x :=
            ConcreteCategory.congr_hom (preimageComparison_snd B f) x
          _ = pullback.snd (SSet.toTop.map B.ι)
              (SSet.toTop.map f) z := hx₂
  have hEmbedding : Topology.IsEmbedding φ.hom := by
    apply Topology.IsEmbedding.of_comp φ.hom.continuous
      (pullback.snd (SSet.toTop.map B.ι)
        (SSet.toTop.map f)).hom.continuous
    change Topology.IsEmbedding
      (φ ≫ pullback.snd (SSet.toTop.map B.ι) (SSet.toTop.map f)).hom
    rw [preimageComparison_snd]
    exact
      (SSet.closedT1Embeddings_toTop_map_of_mono (B.preimage f).ι).isEmbedding
  have hHomeomorph : IsHomeomorph φ.hom :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hEmbedding, hbij.2⟩
  let _ : IsIso φ := (TopCat.isIso_iff_isHomeomorph φ).mpr hHomeomorph
  have hTop : IsPullback
      (SSet.toTop.map (B.fromPreimage f))
      (SSet.toTop.map (B.preimage f).ι)
      (SSet.toTop.map B.ι) (SSet.toTop.map f) :=
    IsPullback.of_iso_pullback (SSet.toTop.map_commSq sqS.toCommSq)
      (asIso φ) (preimageComparison_fst B f) (preimageComparison_snd B f)
  exact sqS.preservesLimit_cospan_iff.mpr hTop

/--
For a cospan whose left leg is a simplicial monomorphism, geometric realization
preserves its pullback limit.
-/
noncomputable instance preservesLimit_cospan_toTop_of_mono
    {X₁ X₂ S : SSet.{u}} (i : X₁ ⟶ S) [Mono i] (p : X₂ ⟶ S) :
    PreservesLimit (cospan i p) SSet.toTop := by
  let e : X₁ ≅ (Subcomplex.range i : SSet.{u}) :=
    asIso (Subcomplex.toRange i)
  let dIso : cospan (Subcomplex.range i).ι p ≅ cospan i p :=
    cospanExt e.symm (Iso.refl _) (Iso.refl _)
      (by
        dsimp [e]
        apply (cancel_epi (Subcomplex.toRange i)).1
        simp)
      (by simp)
  let _ : PreservesLimit (cospan (Subcomplex.range i).ι p) SSet.toTop :=
    preservesLimit_cospan_ι (Subcomplex.range i) p
  exact preservesLimit_of_iso_diagram SSet.toTop dIso

end SSet

namespace CategoryTheory.IsPullback

/--
A simplicial pullback square maps to a topological pullback square under
realization when the left cospan leg is a monomorphism.
-/
theorem map_toTop_of_mono
    {P X₁ X₂ S : SSet.{u}}
    {fst : P ⟶ X₁} {snd : P ⟶ X₂} {i : X₁ ⟶ S} {p : X₂ ⟶ S}
    (sq : IsPullback fst snd i p) [Mono i] :
    IsPullback (SSet.toTop.map fst) (SSet.toTop.map snd)
      (SSet.toTop.map i) (SSet.toTop.map p) :=
  sq.map SSet.toTop

end CategoryTheory.IsPullback

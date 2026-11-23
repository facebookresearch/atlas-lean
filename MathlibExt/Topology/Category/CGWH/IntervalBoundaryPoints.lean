/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.RealizedInterval
public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The two actual points of the whole native interval boundary

The existing simplicial boundary Iso and realization adjunction prove that
the two ORIGINAL zero-face maps form a topological coproduct. Consequently
every native boundary point is an actual endpoint. This also identifies
restriction of a native internal-Hom map by BOTH complete endpoint maps;
no boundary chart or fixed-endpoint witness is supplied.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

universe u v

namespace CGWH

private def boundaryOneFaceCofanIsColimit :
    IsColimit (BinaryCofan.mk
      (SSet.boundary.ι (0 : Fin 2) : (Δ[0] : SSet.{v}) ⟶ ∂Δ[1])
      (SSet.boundary.ι (1 : Fin 2))) := by
  apply (coprodIsCoprod (Δ[0] : SSet.{v}) (Δ[0] : SSet.{v})).ofIsoColimit
  refine Cocone.ext SSet.boundaryOneIsoTwoPoints.symm ?_
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact SSet.boundaryOneIsoTwoPoints_inl_inv
  · exact SSet.boundaryOneIsoTwoPoints_inr_inv

private def realizedBoundaryOneFaceCofanIsColimit :
    IsColimit (BinaryCofan.mk
      (SSet.toTop.map (SSet.boundary.ι (0 : Fin 2) : (Δ[0] : SSet.{v}) ⟶ ∂Δ[1]))
      (SSet.toTop.map (SSet.boundary.ι (1 : Fin 2)))) :=
  mapIsColimitOfPreservesOfIsColimit SSet.toTop _ _ boundaryOneFaceCofanIsColimit

/-- Every point of the ORIGINAL whole native interval boundary is the
image of one of its two ORIGINAL zero-face endpoint maps. -/
public theorem nativeIntervalBoundary_point_cases
    (b : SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v})) :
    ∃ (ε : Fin 2) (a : 𝟙_ CGWH.{u, v}), nativeIntervalBoundaryEndpoint.{u, v} ε a = b := by
  classical
  let c := BinaryCofan.mk
    (SSet.toTop.map (SSet.boundary.ι (0 : Fin 2) : (Δ[0] : SSet.{v}) ⟶ ∂Δ[1]))
    (SSet.toTop.map (SSet.boundary.ι (1 : Fin 2)))
  have hc := (TopCat.binaryCofan_isColimit_iff c).mp ⟨realizedBoundaryOneFaceCofanIsColimit⟩
  have hor : b ∈ Set.range c.inl ∨ b ∈ Set.range c.inr := by
    rw [eq_compl_iff_isCompl.mpr hc.2.2.symm]
    exact or_not
  let Z : CGWH.{u, v} := SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v})
  let B : CGWH.{u, v} := SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v})
  let e : Z ≅ 𝟙_ CGWH.{u, v} := nativeZeroTensorUnitIso.{u, v}
  let i₀ : Z ⟶ B := SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))
  let i₁ : Z ⟶ B := SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2))
  rcases hor with ⟨z, hz⟩ | ⟨z, hz⟩
  · let z₀ : Z := z
    have hz₀ : i₀ z₀ = b := hz
    have he : e.inv (e.hom z₀) = z₀ := e.hom_inv_id_apply z₀
    refine ⟨1, e.hom z₀, ?_⟩
    change i₀ (e.inv (e.hom z₀)) = b
    exact (congrArg (fun q : Z => i₀ q) he).trans hz₀
  · let z₁ : Z := z
    have hz₁ : i₁ z₁ = b := hz
    have he : e.inv (e.hom z₁) = z₁ := e.hom_inv_id_apply z₁
    refine ⟨0, e.hom z₁, ?_⟩
    change i₁ (e.inv (e.hom z₁)) = b
    exact (congrArg (fun q : Z => i₁ q) he).trans hz₁

/-- Both complete endpoint equations determine restriction along the
ACTUAL whole boundary, for arbitrary source and target native spaces. -/
public theorem nativeIntervalBoundary_pre_ext
    {A M : CGWH.{u, v}} (s t : A ⟶ (ihom nativeInterval.{u, v}).obj M)
    (h₀ : (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ MonoidalClosed.uncurry s =
      (nativeIntervalEndpoint.{u, v} 0 ▷ A) ≫ MonoidalClosed.uncurry t)
    (h₁ : (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ MonoidalClosed.uncurry s =
      (nativeIntervalEndpoint.{u, v} 1 ▷ A) ≫ MonoidalClosed.uncurry t) :
    s ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M =
      t ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M := by
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_pre_app]
  apply ConcreteCategory.hom_ext
  intro z
  let b := CartesianMonoidalCategory.fst
    (SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v})) A z
  let a := CartesianMonoidalCategory.snd
    (SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v})) A z
  have hz : tensorMk b a = z := tensorMk_fst_snd z
  obtain ⟨ε, q, hq⟩ := nativeIntervalBoundary_point_cases.{u, v} b
  have hc : nativeIntervalBoundary.{u, v} (nativeIntervalBoundaryEndpoint.{u, v} ε q) =
      nativeIntervalEndpoint.{u, v} ε q := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (nativeIntervalBoundaryEndpoint_comp.{u, v} ε) q
  have hb : nativeIntervalBoundary.{u, v} b = nativeIntervalEndpoint.{u, v} ε q :=
    (congrArg nativeIntervalBoundary.{u, v} hq).symm.trans hc
  have he : (nativeIntervalEndpoint.{u, v} ε ▷ A) ≫ MonoidalClosed.uncurry s =
      (nativeIntervalEndpoint.{u, v} ε ▷ A) ≫ MonoidalClosed.uncurry t := by
    fin_cases ε
    · exact h₀
    · exact h₁
  have hv := ConcreteCategory.congr_hom he (tensorMk q a)
  simp only [ConcreteCategory.comp_apply, tensorMk_whiskerRight] at hv
  have hs : ((nativeIntervalBoundary.{u, v} ▷ A) ≫ MonoidalClosed.uncurry s) z =
      MonoidalClosed.uncurry s (tensorMk (nativeIntervalEndpoint.{u, v} ε q) a) :=
    (congrArg (fun x => ((nativeIntervalBoundary.{u, v} ▷ A) ≫
      MonoidalClosed.uncurry s) x) hz.symm).trans
        (by rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight, hb])
  have ht : ((nativeIntervalBoundary.{u, v} ▷ A) ≫ MonoidalClosed.uncurry t) z =
      MonoidalClosed.uncurry t (tensorMk (nativeIntervalEndpoint.{u, v} ε q) a) :=
    (congrArg (fun x => ((nativeIntervalBoundary.{u, v} ▷ A) ≫
      MonoidalClosed.uncurry t) x) hz.symm).trans
        (by rw [ConcreteCategory.comp_apply, tensorMk_whiskerRight, hb])
  exact hs.trans (hv.trans ht.symm)

end CGWH

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.LastVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Realization
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Geometric subdivision and iterated last vertex

The canonical realization homeomorphism from an iterated subdivision of a
standard simplex and the realization of the iterated last-vertex map are not
equal.  This file constructs their straight-line homotopy in barycentric
coordinates.  The homotopy is natural for every codimension-one face, so a
boundary face remains in that same face throughout.

Postcomposition and the realization--singular adjunction give a simplicial
homotopy between the geometric subdivision adjunct used by mesh estimates
and the literal iterated-last-vertex endpoint used by the Ex tower.

No subordinate-cover weakness, Ex-infinity weakness, model-category
instance, or TopCat left-properness assertion is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial Topology MonoidalCategory
open scoped Simplicial unitInterval

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private noncomputable def geometricEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom

private noncomputable def lastVertexEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  SSet.toTop.map (sdIterLastVertex (Δ[n] : SSet.{u}) k)

/-- Straight-line barycentric homotopy from the canonical geometric
subdivision homeomorphism to realization of iterated last vertex. -/
noncomputable def toTopSdIterLastVertexHomotopy (n k : ℕ) :
    TopCat.Homotopy
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom
      (SSet.toTop.map (sdIterLastVertex (Δ[n] : SSet.{u}) k)) := by
  let φ := (⦋n⦌.toTopHomeo.{u} :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ
      Convexity.StdSimplex ℝ (Fin (n + 1)))
  let p : C(SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (⟨φ, φ.continuous⟩ : C(_, _)).comp (geometricEndpoint n k).hom
  let q : C(SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (⟨φ, φ.continuous⟩ : C(_, _)).comp (lastVertexEndpoint n k).hom
  exact
    { toFun := fun z => φ.symm
        (Convexity.convexCombPair (R := ℝ)
          (unitInterval.symm z.1 : ℝ)
          (1 - (unitInterval.symm z.1 : ℝ))
          (unitInterval.symm z.1).property.1
          (by simpa using (unitInterval.symm z.1).property.2)
          (by ring) (p z.2) (q z.2))
      continuous_toFun := by
        apply φ.symm.continuous.comp
        rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
          (Fin (n + 1))).continuous_iff]
        unfold Function.comp
        refine continuous_pi (fun i => ?_)
        have hp : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (p z.2).weights i) :=
          (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
            (p.continuous.comp continuous_snd)
        have hq : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (q z.2).weights i) :=
          (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
            (q.continuous.comp continuous_snd)
        have h1 : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (unitInterval.symm z.1 : ℝ)) :=
          continuous_subtype_val.comp
            (unitInterval.continuous_symm.comp continuous_fst)
        have h2 : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            1 - (unitInterval.symm z.1 : ℝ)) :=
          continuous_const.sub h1
        have hEq : (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (Convexity.convexCombPair (R := ℝ)
              (unitInterval.symm z.1 : ℝ)
              (1 - (unitInterval.symm z.1 : ℝ))
              (unitInterval.symm z.1).property.1
              (by simpa using (unitInterval.symm z.1).property.2)
              (by ring) (p z.2) (q z.2)).weights i) =
          (fun z => (unitInterval.symm z.1 : ℝ) * (p z.2).weights i +
            (1 - (unitInterval.symm z.1 : ℝ)) * (q z.2).weights i) := by
          funext z
          simp [Convexity.StdSimplex.weights_convexCombPair, smul_eq_mul]
        rw [hEq]
        exact (h1.mul hp).add (h2.mul hq)
      map_zero_left := by
        intro x
        simp [p, φ, geometricEndpoint]
      map_one_left := by
        intro x
        simp [q, φ, lastVertexEndpoint] }

private theorem toTopSdIterLastVertexHomotopy_toTopHomeo_apply
    (n k : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    (⦋n⦌.toTopHomeo.{u})
        (toTopSdIterLastVertexHomotopy n k (t, x)) =
      Convexity.convexCombPair (R := ℝ)
        (unitInterval.symm t : ℝ)
        (1 - (unitInterval.symm t : ℝ))
        (unitInterval.symm t).property.1
        (by simpa using (unitInterval.symm t).property.2)
        (by ring)
        ((⦋n⦌.toTopHomeo.{u}) (geometricEndpoint n k x))
        ((⦋n⦌.toTopHomeo.{u}) (lastVertexEndpoint n k x)) := by
  change (⦋n⦌.toTopHomeo.{u})
      ((⦋n⦌.toTopHomeo.{u}).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem geometricEndpoint_naturality_of_mono
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)] (k : ℕ) :
    SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ≫
        geometricEndpoint.{u} n k =
      geometricEndpoint.{u} m k ≫
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) :=
  SSet.toTopSdIterIso_hom_naturality_of_mono
    (SSet.stdSimplex.{u}.map f) k

set_option backward.isDefEq.respectTransparency false in
private theorem lastVertexEndpoint_naturality
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (k : ℕ) :
    SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ≫
        lastVertexEndpoint.{u} n k =
      lastVertexEndpoint.{u} m k ≫
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) := by
  unfold lastVertexEndpoint
  rw [← SSet.toTop.map_comp, sdIterLastVertex_naturality,
    SSet.toTop.map_comp]

private theorem toTopSdIterLastVertexHomotopy_naturality_of_mono
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)] (k : ℕ)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[m] : SSet.{u}))) :
    toTopSdIterLastVertexHomotopy n k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) x) =
      SSet.toTop.map (SSet.stdSimplex.{u}.map f)
        (toTopSdIterLastVertexHomotopy m k (t, x)) := by
  have hGeom := ConcreteCategory.congr_hom
    (geometricEndpoint_naturality_of_mono f k) x
  have hLast := ConcreteCategory.congr_hom
    (lastVertexEndpoint_naturality f k) x
  have hGeomBary := congrArg (⦋n⦌.toTopHomeo.{u}) hGeom
  have hLastBary := congrArg (⦋n⦌.toTopHomeo.{u}) hLast
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hGeomBary hLastBary
  rw [SimplexCategory.toTopHomeo_naturality_apply] at hGeomBary hLastBary
  apply (⦋n⦌.toTopHomeo.{u}).injective
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [toTopSdIterLastVertexHomotopy_toTopHomeo_apply,
    toTopSdIterLastVertexHomotopy_toTopHomeo_apply]
  rw [hGeomBary, hLastBary]
  exact ((Convexity.StdSimplex.isAffineMap_map ℝ f).map_convexCombPair
    (unitInterval.symm t).property.1
    (by simpa using (unitInterval.symm t).property.2)
    (by ring)
    ((⦋m⦌.toTopHomeo.{u}) (geometricEndpoint m k x))
    ((⦋m⦌.toTopHomeo.{u}) (lastVertexEndpoint m k x))).symm

/-- Every codimension-one face is preserved throughout the barycentric
homotopy. -/
theorem toTopSdIterLastVertexHomotopy_face
    (n k : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    toTopSdIterLastVertexHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x) =
      SSet.toTop.map (SSet.stdSimplex.δ i)
        (toTopSdIterLastVertexHomotopy n k (t, x)) := by
  let _ : Mono (SSet.stdSimplex.{u}.map (SimplexCategory.δ i)) := by
    change Mono (SSet.stdSimplex.δ i)
    infer_instance
  exact toTopSdIterLastVertexHomotopy_naturality_of_mono
    (SimplexCategory.δ i) k t x

/-- Simplicial homotopy between the geometric Mesh adjunct and the literal
iterated-last-vertex endpoint used by subdivision--Ex promotion. -/
noncomputable def geometricSubdivisionAdjunctRelativeHomotopy
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    SSet.Homotopy
      (sSetTopAdj.homEquiv _ _
        ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b))
      (sdIterLastVertex (Δ[n] : SSet.{u}) k ≫
        sSetTopAdj.homEquiv _ _ b) := by
  let hTop : TopCat.Homotopy
      (geometricEndpoint n k ≫ b)
      (lastVertexEndpoint n k ≫ b) :=
    TopCat.Homotopy.comp (TopCat.Homotopy.refl b)
      (toTopSdIterLastVertexHomotopy n k)
  let hSing := TopCat.Homotopy.toSSet hTop
  refine
    { h := ((sSetTopAdj.unit.app
          ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h
      h₀ := ?_
      h₁ := ?_
      rel := ?_ }
  · calc
      SSet.ι₀ ≫
          ((sSetTopAdj.unit.app
              ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h =
        sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ≫
          TopCat.toSSet.map (geometricEndpoint n k ≫ b) := by
            simp [hSing]
      _ = sSetTopAdj.homEquiv _ _ (geometricEndpoint n k ≫ b) := by
        rw [Adjunction.homEquiv_unit]
  · calc
      SSet.ι₁ ≫
          ((sSetTopAdj.unit.app
              ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h =
        sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ≫
          TopCat.toSSet.map (lastVertexEndpoint n k ≫ b) := by
            simp [hSing]
      _ = sSetTopAdj.homEquiv _ _ (lastVertexEndpoint n k ≫ b) := by
        rw [Adjunction.homEquiv_unit]
      _ = sdIterLastVertex (Δ[n] : SSet.{u}) k ≫
          sSetTopAdj.homEquiv _ _ b := by
        unfold lastVertexEndpoint
        rw [sSetTopAdj.homEquiv_naturality_left]
  · ext _ ⟨⟨_, ⟨⟩⟩, _⟩

end SSet

end

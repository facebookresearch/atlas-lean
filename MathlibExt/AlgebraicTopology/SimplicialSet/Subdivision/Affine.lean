/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import MathlibExt.Analysis.Convex.StdSimplex
public import MathlibExt.AlgebraicTopology.LinearSimplexFaceChain
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationStdSimplex
public import MathlibExt.Topology.MetricSpace.StdSimplex
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Affine cells of categorical simplex subdivision

A degree-`d` simplex of the categorical subdivision of a standard simplex is a
monotone chain of nonempty faces. Map each vertex of the chain to the uniform
barycenter of its face and extend by barycentric combination to obtain an affine
cell map.

For source weights `t_j`, the resulting coordinate is
`∑_j t_j * barycenter(F_j)_i`. Restriction by any simplex operator commutes with
the cell map; maps of the ambient standard simplex require injectivity for the
barycenter comparison. Each cell's diameter is bounded by the ambient factor
`n / (n + 1)` times the diameter of the standard `n`-simplex.
-/

@[expose] public section

open CategoryTheory Simplicial Opposite Topology
open scoped Simplicial

noncomputable section

universe u

namespace SimplexCategory

/-- The finite ambient face at one vertex of a subdivision simplex. -/
private noncomputable def sdFace
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) : Finset (Fin (n.len + 1)) :=
  (σ.obj j).finset.image (fun x => x.down)

private theorem sdFace_nonempty
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) : (sdFace σ j).Nonempty := by
  exact (σ.obj j).nonempty.image _

private theorem sdFace_monotone
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d))) :
    Monotone (sdFace σ) := by
  intro i j hij
  apply Finset.image_mono
  exact (σ.map (homOfLE hij)).le

private theorem sdFace_restrict
    {n : SimplexCategory} {d e : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (f : SimplexCategory.mk e ⟶ SimplexCategory.mk d)
    (j : Fin (e + 1)) :
    sdFace ((SimplexCategory.sd.{u}.obj n).map f.op σ) j =
      sdFace σ (f j) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem sdFace_map
    {m n : SimplexCategory} (f : m ⟶ n) {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj m).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) :
    sdFace ((SimplexCategory.sd.{u}.map f).app _ σ) j =
      (sdFace σ j).image f := by
  classical
  unfold sdFace
  dsimp [SimplexCategory.sd, PartOrd.nonemptyFiniteChainsFunctor,
    PartOrd.nerveFunctor, CategoryTheory.nerveMap,
    CategoryTheory.Functor.mapComposableArrows,
    PartialOrder.NonemptyFiniteChains.orderHomMap,
    PartialOrder.NonemptyFiniteChains.map]
  ext y
  simp only [Finset.mem_image]
  aesop

private theorem subBarycenter_weights_apply_of_mem
    {M : Type*} (S : Finset M) (hS : S.Nonempty)
    {x : M} (hx : x ∈ S) :
    (Convexity.StdSimplex.subBarycenter (K := ℝ) S hS).weights x =
      (S.card : ℝ)⁻¹ := by
  classical
  rw [Convexity.StdSimplex.weights_subBarycenter,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single x]
  · simp
  · intro b hb hne
    simp [hne]
  · exact fun h => (h hx).elim

private theorem map_subBarycenter_of_injective
    {M N : Type*} [DecidableEq N]
    (f : M → N) (hf : Function.Injective f)
    (S : Finset M) (hS : S.Nonempty) :
    Convexity.StdSimplex.map f
        (Convexity.StdSimplex.subBarycenter (K := ℝ) S hS) =
      Convexity.StdSimplex.subBarycenter
        (S.image f) (hS.image f) := by
  classical
  ext y
  by_cases hy : y ∈ S.image f
  · obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    rw [Convexity.StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective hf]
    rw [subBarycenter_weights_apply_of_mem S hS hxS,
      subBarycenter_weights_apply_of_mem (S.image f) (hS.image f)
        (Finset.mem_image.mpr ⟨x, hxS, rfl⟩),
      Finset.card_image_of_injective _ hf]
  · rw [Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero _ _ _ hy,
      Convexity.StdSimplex.weights_map]
    by_cases hyr : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hyr
      rw [Finsupp.mapDomain_apply_of_injective hf]
      apply Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero
      intro hxS
      exact hy (Finset.mem_image.mpr ⟨x, hxS, rfl⟩)
    · exact Finsupp.mapDomain_of_notMem_range _ _ hyr

private theorem subBarycenter_congr
    {M : Type*} {S T : Finset M} (h : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    Convexity.StdSimplex.subBarycenter (K := ℝ) S hS =
      Convexity.StdSimplex.subBarycenter T hT := by
  subst T
  rfl

private noncomputable def sdFaceBarycenter
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) :
    Convexity.StdSimplex ℝ (Fin (n.len + 1)) :=
  Convexity.StdSimplex.subBarycenter
    (sdFace σ j) (sdFace_nonempty σ j)

private theorem sdFaceBarycenter_restrict
    {n : SimplexCategory} {d e : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (f : SimplexCategory.mk e ⟶ SimplexCategory.mk d)
    (j : Fin (e + 1)) :
    sdFaceBarycenter ((SimplexCategory.sd.{u}.obj n).map f.op σ) j =
      sdFaceBarycenter σ (f j) := by
  apply subBarycenter_congr (sdFace_restrict σ f j)

private theorem sdFaceBarycenter_map_mono
    {m n : SimplexCategory} (f : m ⟶ n) [Mono f] {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj m).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) :
    sdFaceBarycenter ((SimplexCategory.sd.{u}.map f).app _ σ) j =
      Convexity.StdSimplex.map f (sdFaceBarycenter σ j) := by
  have hface := sdFace_map f σ j
  calc
    sdFaceBarycenter ((SimplexCategory.sd.{u}.map f).app _ σ) j =
        Convexity.StdSimplex.subBarycenter
          ((sdFace σ j).image f) ((sdFace_nonempty σ j).image f) :=
      subBarycenter_congr hface _ _
    _ = Convexity.StdSimplex.map f (sdFaceBarycenter σ j) :=
      (map_subBarycenter_of_injective f
        (SimplexCategory.mono_iff_injective.mp inferInstance)
        (sdFace σ j) (sdFace_nonempty σ j)).symm

/--
The continuous affine map from the standard `d`-simplex to the ambient standard
simplex, taking the vertices of a subdivision simplex to the barycenters of its
nested nonempty faces.
-/
noncomputable def sdCellMap
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d))) :
    C(Convexity.StdSimplex ℝ (Fin (d + 1)),
      Convexity.StdSimplex ℝ (Fin (n.len + 1))) where
  toFun x := x.iConvexComb (fun j =>
    Convexity.StdSimplex.subBarycenter
      ((σ.obj j).finset.image
        (fun a => (a.down : Fin (n.len + 1))))
      (by
        apply Finset.Nonempty.image
        exact (σ.obj j).nonempty))
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n.len + 1))).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro i
    simp only [Function.comp_apply,
      Convexity.StdSimplex.weights_iConvexComb_apply]
    fun_prop

private theorem sdCellMap_apply_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    sdCellMap σ x = x.iConvexComb (sdFaceBarycenter σ) := by
  change x.iConvexComb (fun j =>
      Convexity.StdSimplex.subBarycenter
        ((σ.obj j).finset.image
          (fun a => (a.down : Fin (n.len + 1)))) _) = _
  unfold sdFaceBarycenter sdFace
  rfl

open Classical in
/--
At coordinate `i`, the affine cell map is the weighted sum
`∑_j x_j * barycenter(F_j)_i` of the uniform barycenter coordinates of the chain faces.
-/
theorem sdCellMap_weights_apply
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (x : Convexity.StdSimplex ℝ (Fin (d + 1)))
    (i : Fin (n.len + 1)) :
    (sdCellMap σ x).weights i =
      ∑ j, x.weights j *
        (Convexity.StdSimplex.subBarycenter
          ((σ.obj j).finset.image
            (fun a => (a.down : Fin (n.len + 1))))
          (by
            apply Finset.Nonempty.image
            exact (σ.obj j).nonempty)).weights i := by
  rw [sdCellMap_apply_eq]
  rw [Convexity.StdSimplex.weights_iConvexComb_apply]
  apply Finset.sum_congr rfl
  intro j _
  unfold sdFaceBarycenter sdFace
  rfl

/--
Restricting an affine subdivision cell along any simplex operator equals the
affine cell map of the corresponding restricted subdivision simplex.
-/
theorem sdCellMap_face
    {n : SimplexCategory} {d e : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (f : SimplexCategory.mk e ⟶ SimplexCategory.mk d) :
    (sdCellMap σ).comp (SSet.stdSimplex.toTopMap f).hom =
      sdCellMap ((SimplexCategory.sd.{u}.obj n).map f.op σ) := by
  apply ContinuousMap.ext
  intro x
  change sdCellMap σ (Convexity.StdSimplex.map f x) =
    sdCellMap ((SimplexCategory.sd.{u}.obj n).map f.op σ) x
  rw [sdCellMap_apply_eq, sdCellMap_apply_eq]
  change (Convexity.StdSimplex.map f x).iConvexComb
      (sdFaceBarycenter σ) =
    x.iConvexComb
      (sdFaceBarycenter ((SimplexCategory.sd.{u}.obj n).map f.op σ))
  rw [Convexity.iConvexComb_map]
  apply Convexity.iConvexComb_congr
  intro j _
  exact (sdFaceBarycenter_restrict σ f j).symm

/--
For an injective map of ambient standard simplices, mapping a subdivision simplex
then evaluating its affine cell equals evaluating the original cell and applying
the ambient affine simplex map.
-/
theorem sdCellMap_natural_mono
    {m n : SimplexCategory} (f : m ⟶ n) [Mono f] {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj m).obj (op (SimplexCategory.mk d))) :
    sdCellMap ((SimplexCategory.sd.{u}.map f).app _ σ) =
      (SSet.stdSimplex.toTopMap f).hom.comp (sdCellMap σ) := by
  apply ContinuousMap.ext
  intro x
  change sdCellMap ((SimplexCategory.sd.{u}.map f).app _ σ) x =
    Convexity.StdSimplex.map f (sdCellMap σ x)
  rw [sdCellMap_apply_eq, sdCellMap_apply_eq]
  change x.iConvexComb
      (sdFaceBarycenter ((SimplexCategory.sd.{u}.map f).app _ σ)) =
    Convexity.StdSimplex.map f (x.iConvexComb (sdFaceBarycenter σ))
  rw [Convexity.map_iConvexComb]
  apply Convexity.iConvexComb_congr
  intro j _
  exact sdFaceBarycenter_map_mono f σ j

private theorem sdCellMap_weights_eq
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((sdCellMap σ x).weights : Fin (n.len + 1) → ℝ) =
      x.iConvexComb (fun j =>
        ((sdFaceBarycenter σ j).weights : Fin (n.len + 1) → ℝ)) := by
  rw [sdCellMap_apply_eq]
  ext i
  rw [Convexity.StdSimplex.weights_iConvexComb_apply,
    Convexity.iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem sdCellMap_weights_mem_convexHull_aux
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((sdCellMap σ x).weights : Fin (n.len + 1) → ℝ) ∈
      convexHull ℝ (Set.range (fun j =>
        ((sdFaceBarycenter σ j).weights : Fin (n.len + 1) → ℝ))) := by
  rw [sdCellMap_weights_eq]
  rw [Convexity.iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  convert affineCombination_mem_convexHull
    (s := Finset.univ)
    (v := fun j =>
      ((sdFaceBarycenter σ j).weights : Fin (n.len + 1) → ℝ))
    (w := fun j => x.weights j)
    (fun j _ => x.weights_nonneg j) x.total_of_fintype using 1
  rw [Finset.affineCombination_eq_linear_combination]
  exact x.total_of_fintype

/--
The weight vector of a point in an affine subdivision cell lies in the convex
hull of the weight vectors of the images of that cell's vertices.
-/
theorem sdCellMap_weights_mem_convexHull
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((sdCellMap σ x).weights : Fin (n.len + 1) → ℝ) ∈
      convexHull ℝ (Set.range fun j : Fin (d + 1) =>
        ((sdCellMap σ (Convexity.StdSimplex.single (R := ℝ) j)).weights :
          Fin (n.len + 1) → ℝ)) := by
  have hvertex (j : Fin (d + 1)) :
      ((sdCellMap σ (Convexity.StdSimplex.single (R := ℝ) j)).weights :
        Fin (n.len + 1) → ℝ) =
        ((sdFaceBarycenter σ j).weights : Fin (n.len + 1) → ℝ) := by
    rw [sdCellMap_apply_eq]
    simp
  simpa only [hvertex] using sdCellMap_weights_mem_convexHull_aux σ x

private theorem sdFaceBarycenter_weights_eq_centroid
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d)))
    (j : Fin (d + 1)) :
    ((sdFaceBarycenter σ j).weights : Fin (n.len + 1) → ℝ) =
      (sdFace σ j).centroid ℝ
        (fun i => ((Convexity.StdSimplex.single (R := ℝ) i).weights :
          Fin (n.len + 1) → ℝ)) := by
  unfold sdFaceBarycenter
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
  · ext k
    simp [Convexity.StdSimplex.weights_subBarycenter,
      Finset.centroidWeights_apply, Finsupp.single_apply]
  · exact (sdFace σ j).sum_centroidWeights_eq_one_of_nonempty ℝ
      (sdFace_nonempty σ j)

/--
For ambient dimension `n`, the diameter of an affine subdivision cell is at most
`n / (n + 1)` times the diameter of the entire ambient real standard simplex.
-/
theorem diam_range_sdCellMap_le
    {n : SimplexCategory} {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj (op (SimplexCategory.mk d))) :
    Metric.diam (Set.range (sdCellMap σ)) ≤
      (n.len : ℝ) / ((n.len : ℝ) + 1) *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n.len + 1)))) := by
  let vertices : Fin (n.len + 1) → (Fin (n.len + 1) → ℝ) :=
    fun i => (Convexity.StdSimplex.single (R := ℝ) i).weights
  have hfaces :
      (fun j => (sdFace σ j).centroid ℝ vertices) =
        (fun j => ((sdFaceBarycenter σ j).weights :
          Fin (n.len + 1) → ℝ)) := by
    funext j
    simpa [vertices] using
      (sdFaceBarycenter_weights_eq_centroid σ j).symm
  have hcard : (sdFace σ (Fin.last d)).card ≤ n.len + 1 := by
    simpa using Finset.card_le_univ (sdFace σ (Fin.last d))
  have hG := AlgebraicTopology.diam_faceBarycenters_chain_le_of_card_le
    (faces := sdFace σ) (fun j => sdFace_nonempty σ j)
    (sdFace_monotone σ) hcard vertices
  rw [hfaces] at hG
  let weightsMap : Convexity.StdSimplex ℝ (Fin (n.len + 1)) →
      (Fin (n.len + 1) → ℝ) := fun x => x.weights
  have hweightsIsometry : Isometry weightsMap :=
    Isometry.of_dist_eq Convexity.StdSimplex.dist_eq_weights
  have hmax : Metric.diam
      (vertices '' (sdFace σ (Fin.last d) : Set (Fin (n.len + 1)))) ≤
      Metric.diam (Set.range weightsMap) := by
    apply Metric.diam_mono
    · rintro _ ⟨i, _, rfl⟩
      exact ⟨Convexity.StdSimplex.single (R := ℝ) i, rfl⟩
    · exact (isCompact_range hweightsIsometry.continuous).isBounded
  have hfactor : 0 ≤ (n.len : ℝ) / ((n.len : ℝ) + 1) := by
    positivity
  have hfaceDiam : Metric.diam
      (Set.range (fun j => ((sdFaceBarycenter σ j).weights :
        Fin (n.len + 1) → ℝ))) ≤
      (n.len : ℝ) / ((n.len : ℝ) + 1) *
        Metric.diam (Set.range weightsMap) :=
    hG.trans (mul_le_mul_of_nonneg_left hmax hfactor)
  have hcell : Metric.diam (Set.range (sdCellMap σ)) ≤
      Metric.diam (Set.range (fun j => ((sdFaceBarycenter σ j).weights :
        Fin (n.len + 1) → ℝ))) := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [Convexity.StdSimplex.dist_eq_weights]
    simpa only [convexHull_diam] using
      Metric.dist_le_diam_of_mem
        (isBounded_convexHull.mpr
          (Set.finite_range (fun j => ((sdFaceBarycenter σ j).weights :
            Fin (n.len + 1) → ℝ))).isBounded)
        (sdCellMap_weights_mem_convexHull_aux σ x)
        (sdCellMap_weights_mem_convexHull_aux σ y)
  rw [← hweightsIsometry.diam_range]
  exact hcell.trans hfaceDiam

end SimplexCategory

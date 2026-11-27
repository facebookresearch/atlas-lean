/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Realization
public import MathlibExt.Topology.MetricSpace.StdSimplex
public import Mathlib.Topology.Sets.OpenCover

/-!
# Mesh bounds for iterated simplicial subdivision

For an `n`-simplex, each cell of its `k`-fold subdivision has diameter at most
`(n / (n + 1))^k * D_n`, where `D_n` is the diameter of the entire real standard
simplex. This applies to every simplex mapping into the subdivision, including
degenerate simplices.

Consequently, for a continuous map from the realized standard simplex to a space
`B` and any open cover of `B`, sufficiently many subdivisions make every realized
cell image lie in one cover member. The cover-index universe is independent of
the space and simplicial-set universe.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial Topology
open scoped Simplicial

noncomputable section

universe u v

namespace SSet

private noncomputable def meshStdToRealization (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)),
      SSet.toTop.obj (Δ[n] : SSet.{u})) :=
  ⟨fun z => (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm z,
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm.continuous⟩

/--
The continuous map from the real standard `d`-simplex to the real standard
`n`-simplex associated to `σ : Δ[d] → sd^k Δ[n]`, using the iterated
subdivision-realization comparison.
-/
noncomputable def sdIterCellMap
    (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1))) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  TopCat.ofHom
    ((show C(SSet.toTop.obj (Δ[n] : SSet.{u}),
        Convexity.StdSimplex ℝ (Fin (n + 1))) from
      SimplexCategory.toTopHomeo.{u} ⦋n⦌).comp
        ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom.hom.comp
          ((SSet.toTop.map σ).hom.comp
            (show C(Convexity.StdSimplex ℝ (Fin (d + 1)),
                SSet.toTop.obj (Δ[d] : SSet.{u})) from
              (SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm))))

private theorem sdIterCellMap_u0_compat
    (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{0}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{0})) :
    SSet.sdIterCellMap n k σ =
      (SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map σ ≫
        (SSet.toTopSdIterIso (Δ[n] : SSet.{0}) k).hom ≫
        (SSet.stdSimplex.toTopIso ⦋n⦌).hom := by
  apply TopCat.ext
  intro z
  rfl

private noncomputable def meshFace {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (j : Fin (d + 1)) : Finset (Fin (r + 1)) :=
  (τ.obj j).finset.image (fun a => a.down)

private theorem meshFace_nonempty {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (j : Fin (d + 1)) : (meshFace τ j).Nonempty :=
  (τ.obj j).nonempty.image _

private theorem meshFace_monotone {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌) :
    Monotone (meshFace τ) := by
  intro i j hij
  apply Finset.image_mono
  exact (τ.map (homOfLE hij)).le

private noncomputable def meshFaceBarycenter {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (j : Fin (d + 1)) :
    Convexity.StdSimplex ℝ (Fin (r + 1)) :=
  Convexity.StdSimplex.subBarycenter
    (meshFace τ j) (meshFace_nonempty τ j)

private theorem sdCellMap_apply_eq_iConvexComb {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    SimplexCategory.sdCellMap τ z =
      z.iConvexComb (meshFaceBarycenter τ) := by
  change z.iConvexComb (fun j =>
      Convexity.StdSimplex.subBarycenter
        ((τ.obj j).finset.image
          (fun a => (a.down : Fin (r + 1)))) _) = _
  unfold meshFaceBarycenter meshFace
  rfl

private theorem sdCellMap_isAffine {r d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌) :
    Convexity.IsAffineMap ℝ (SimplexCategory.sdCellMap τ) := by
  constructor
  intro s
  calc
    SimplexCategory.sdCellMap τ s.sConvexComb =
        s.sConvexComb.iConvexComb (meshFaceBarycenter τ) :=
      sdCellMap_apply_eq_iConvexComb τ _
    _ = (s.map (fun z =>
          z.iConvexComb (meshFaceBarycenter τ))).sConvexComb :=
      (Convexity.sConvexComb_map_iConvexComb
        (meshFaceBarycenter τ) s).symm
    _ = (s.map (SimplexCategory.sdCellMap τ)).sConvexComb := by
      congr 2

private theorem comp_meshFaceBarycenter_eq_iConvexComb
    {r n d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (g : C(Convexity.StdSimplex ℝ (Fin (r + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hg : Convexity.IsAffineMap ℝ g) (j : Fin (d + 1)) :
    g (meshFaceBarycenter τ j) =
      (meshFaceBarycenter τ j).iConvexComb
        (g ∘ Convexity.StdSimplex.single) := by
  calc
    g (meshFaceBarycenter τ j) =
        g ((meshFaceBarycenter τ j).iConvexComb
          Convexity.StdSimplex.single) := by
      rw [Convexity.StdSimplex.iConvexComb_single]
    _ = (meshFaceBarycenter τ j).iConvexComb
          (g ∘ Convexity.StdSimplex.single) :=
      hg.map_iConvexComb _ _

private theorem comp_meshFaceBarycenter_weights_eq_centroid
    {r n d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (g : C(Convexity.StdSimplex ℝ (Fin (r + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hg : Convexity.IsAffineMap ℝ g) (j : Fin (d + 1)) :
    ((g (meshFaceBarycenter τ j)).weights : Fin (n + 1) → ℝ) =
      (meshFace τ j).centroid ℝ
        (fun i => ((g (Convexity.StdSimplex.single i)).weights :
          Fin (n + 1) → ℝ)) := by
  rw [comp_meshFaceBarycenter_eq_iConvexComb τ g hg j]
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination]
  · ext k
    rw [Convexity.StdSimplex.weights_iConvexComb_apply]
    unfold meshFaceBarycenter
    simp [Convexity.StdSimplex.weights_subBarycenter,
      Finset.centroidWeights_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply]
  · exact (meshFace τ j).sum_centroidWeights_eq_one_of_nonempty ℝ
      (meshFace_nonempty τ j)

private theorem comp_sdCellMap_apply_eq_iConvexComb
    {r n d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (g : C(Convexity.StdSimplex ℝ (Fin (r + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hg : Convexity.IsAffineMap ℝ g)
    (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    g (SimplexCategory.sdCellMap τ z) =
      z.iConvexComb (fun j => g (meshFaceBarycenter τ j)) := by
  rw [sdCellMap_apply_eq_iConvexComb]
  exact hg.map_iConvexComb _ _

private theorem comp_sdCellMap_weights_eq_iConvexComb
    {r n d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (g : C(Convexity.StdSimplex ℝ (Fin (r + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hg : Convexity.IsAffineMap ℝ g)
    (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((g (SimplexCategory.sdCellMap τ z)).weights :
        Fin (n + 1) → ℝ) =
      z.iConvexComb (fun j =>
        ((g (meshFaceBarycenter τ j)).weights :
          Fin (n + 1) → ℝ)) := by
  rw [comp_sdCellMap_apply_eq_iConvexComb τ g hg z]
  ext i
  rw [Convexity.StdSimplex.weights_iConvexComb_apply,
    Convexity.iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem diam_range_comp_sdCellMap_le
    {r n d : ℕ}
    (τ : (SimplexCategory.sd.{u}.obj ⦋r⦌) _⦋d⦌)
    (g : C(Convexity.StdSimplex ℝ (Fin (r + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hg : Convexity.IsAffineMap ℝ g) :
    Metric.diam
        (Set.range (g.comp (SimplexCategory.sdCellMap τ))) ≤
      (r : ℝ) / ((r : ℝ) + 1) * Metric.diam (Set.range g) := by
  let vertices : Fin (r + 1) → (Fin (n + 1) → ℝ) :=
    fun i => (g (Convexity.StdSimplex.single i)).weights
  let weightsMap : Convexity.StdSimplex ℝ (Fin (n + 1)) →
      (Fin (n + 1) → ℝ) := fun x => x.weights
  have hweightsIsometry : Isometry weightsMap :=
    Isometry.of_dist_eq Convexity.StdSimplex.dist_eq_weights
  have hcentroids :
      (fun j => (meshFace τ j).centroid ℝ vertices) =
        (fun j => ((g (meshFaceBarycenter τ j)).weights :
          Fin (n + 1) → ℝ)) := by
    funext j
    exact (comp_meshFaceBarycenter_weights_eq_centroid τ g hg j).symm
  have hcard : (meshFace τ (Fin.last d)).card ≤ r + 1 := by
    simpa using Finset.card_le_univ (meshFace τ (Fin.last d))
  have hG := AlgebraicTopology.diam_faceBarycenters_chain_le_of_card_le
    (faces := meshFace τ) (fun j => meshFace_nonempty τ j)
    (meshFace_monotone τ) hcard vertices
  rw [hcentroids] at hG
  let wg : Convexity.StdSimplex ℝ (Fin (r + 1)) →
      (Fin (n + 1) → ℝ) := fun z => weightsMap (g z)
  have hwgCompact : IsCompact (Set.range wg) := by
    exact isCompact_range (hweightsIsometry.continuous.comp g.continuous)
  have hmax : Metric.diam
      (vertices '' (meshFace τ (Fin.last d) : Set (Fin (r + 1)))) ≤
      Metric.diam (Set.range wg) := by
    apply Metric.diam_mono
    · rintro _ ⟨i, _, rfl⟩
      exact ⟨Convexity.StdSimplex.single i, rfl⟩
    · exact hwgCompact.isBounded
  have hvertexBounded : Bornology.IsBounded
      (Set.range (fun j => ((g (meshFaceBarycenter τ j)).weights :
        Fin (n + 1) → ℝ))) :=
    (Set.finite_range _).isBounded
  have hmem (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
      ((g (SimplexCategory.sdCellMap τ z)).weights :
          Fin (n + 1) → ℝ) ∈
        convexHull ℝ (Set.range (fun j =>
          ((g (meshFaceBarycenter τ j)).weights :
            Fin (n + 1) → ℝ))) := by
    rw [comp_sdCellMap_weights_eq_iConvexComb τ g hg]
    rw [Convexity.iConvexComb_eq_sum,
      Finsupp.sum_fintype _ _ (fun _ => by simp)]
    convert affineCombination_mem_convexHull
      (s := Finset.univ)
      (v := fun j => ((g (meshFaceBarycenter τ j)).weights :
        Fin (n + 1) → ℝ))
      (w := fun j => z.weights j)
      (fun j _ => z.weights_nonneg j) z.total_of_fintype using 1
    rw [Finset.affineCombination_eq_linear_combination]
    exact z.total_of_fintype
  have hcell : Metric.diam
      (Set.range (g.comp (SimplexCategory.sdCellMap τ))) ≤
      Metric.diam (Set.range (fun j =>
        ((g (meshFaceBarycenter τ j)).weights :
          Fin (n + 1) → ℝ))) := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    change dist
      (g (SimplexCategory.sdCellMap τ x))
      (g (SimplexCategory.sdCellMap τ y)) ≤ _
    rw [Convexity.StdSimplex.dist_eq_weights]
    simpa only [convexHull_diam] using
      Metric.dist_le_diam_of_mem
        (isBounded_convexHull.mpr hvertexBounded)
        (hmem x) (hmem y)
  have hfactor : 0 ≤ (r : ℝ) / ((r : ℝ) + 1) := by
    positivity
  have hdiamWg : Metric.diam (Set.range wg) =
      Metric.diam (Set.range g) := by
    have himage : Set.range wg = weightsMap '' Set.range g := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨g z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [himage, hweightsIsometry.diam_image]
  calc
    Metric.diam (Set.range (g.comp (SimplexCategory.sdCellMap τ))) ≤
        Metric.diam (Set.range (fun j =>
          ((g (meshFaceBarycenter τ j)).weights :
            Fin (n + 1) → ℝ))) := hcell
    _ ≤ (r : ℝ) / ((r : ℝ) + 1) *
        Metric.diam (Set.range wg) :=
      hG.trans (mul_le_mul_of_nonneg_left hmax hfactor)
    _ = (r : ℝ) / ((r : ℝ) + 1) *
        Metric.diam (Set.range g) := by rw [hdiamWg]

private theorem nondegenerate_dim_le_sdIter_stdSimplex
    (n k : ℕ)
    (x : ((SSet.sdIter k).obj (Δ[n] : SSet.{u})).N) :
    x.dim ≤ n := by
  induction k with
  | zero =>
      have hx : x.simplex ∈
          (Δ[n] : SSet.{u}).nonDegenerate x.dim := x.nonDegenerate
      let _ : Mono (SSet.stdSimplex.objEquiv x.simplex) :=
        (SSet.stdSimplex.mem_nonDegenerate_iff_mono x.simplex).mp hx
      simpa using SimplexCategory.len_le_of_mono
        (SSet.stdSimplex.objEquiv x.simplex)
  | succ k ih =>
      let X := (SSet.sdIter k).obj (Δ[n] : SSet.{u})
      change (SSet.sd.obj X).N at x
      let e := SSet.sdIsoNondegenerateNerve X
      let c : (SSet.nondegenerateNerve.obj X) _⦋x.dim⦌ :=
        e.hom.app _ x.simplex
      have hcNon : c ∈
          (SSet.nondegenerateNerve.obj X).nonDegenerate x.dim := by
        exact (SSet.nonDegenerate_iff_of_mono e.hom x.simplex).mpr
          x.nonDegenerate
      have hcStrict : StrictMono c.obj :=
        (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono c).mp hcNon
      let a : X.N := c.obj (Fin.last x.dim)
      have hdimStrict : StrictMono (fun i => (c.obj i).dim) := by
        intro i j hij
        exact SSet.N.dim_lt_of_lt (hcStrict hij)
      let emb : Fin (x.dim + 1) ↪ Fin (a.dim + 1) :=
        { toFun := fun i =>
            ⟨(c.obj i).dim, Nat.lt_succ_of_le
              (SSet.N.dim_le_of_le
                (c.monotone (Fin.le_last i)))⟩
          inj' := by
            intro i j hij
            apply hdimStrict.injective
            exact congrArg Fin.val hij }
      have hcard := Fintype.card_le_of_injective emb emb.injective
      have hxa : x.dim ≤ a.dim := by
        simpa using hcard
      exact hxa.trans (ih a)

private theorem meshN_map_le_iff_of_mono {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] (x y : X.N) :
    SSet.N.map f x ≤ SSet.N.map f y ↔ x ≤ y := by
  rw [SSet.N.le_iff, SSet.N.le_iff,
    SSet.N.map_subcomplex, SSet.N.map_subcomplex,
    SSet.Subcomplex.image_le_image_iff]

private noncomputable def meshFaceOfLE {X : SSet.{u}} [X.Nonsingular]
    {x a : X.N} (h : x ≤ a) :
    (Δ[a.dim] : SSet.{u}).N := by
  let f := SSet.N.monoOfLE h
  have hf : Mono f := by
    dsimp [f]
    infer_instance
  have hf' : Mono
      (SSet.stdSimplex.objEquiv.{u}
        (SSet.stdSimplex.objEquiv.{u}.symm f)) := by
    change Mono f
    exact hf
  exact SSet.N.mk (SSet.stdSimplex.objEquiv.symm f)
    ((SSet.stdSimplex.mem_nonDegenerate_iff_mono _).2 hf')

private theorem map_meshFaceOfLE {X : SSet.{u}} [X.Nonsingular]
    {x a : X.N} (h : x ≤ a) :
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex)
      (meshFaceOfLE h) = x := by
  let f := SSet.N.monoOfLE h
  have himage :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (SSet.stdSimplex.objEquiv.symm f) = x.simplex := by
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact SSet.N.map_monoOfLE h
  have hnon :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (meshFaceOfLE h).simplex ∈
        X.nonDegenerate (meshFaceOfLE h).dim := by
    change (SSet.yonedaEquiv.symm a.simplex).app _
        (SSet.stdSimplex.objEquiv.symm f) ∈
          X.nonDegenerate x.dim
    rw [himage]
    exact x.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  change SSet.S.mk
      ((SSet.yonedaEquiv.symm a.simplex).app _
        (SSet.stdSimplex.objEquiv.symm f)) = x.toS
  rw [himage]

private noncomputable def meshLiftChain
    {X : SSet.{u}} [X.Nonsingular] {d : ℕ}
    (c : (CategoryTheory.nerve X.N) _⦋d⦌) :
    (SSet.nondegenerateNerve.obj
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u})) _⦋d⦌ :=
  (show Fin (d + 1) →o
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u}).N from
    { toFun := fun j =>
        meshFaceOfLE (c.monotone (Fin.le_last j))
      monotone' := fun i j hij => by
        let y := SSet.yonedaEquiv.symm
          (c.obj (Fin.last d)).simplex
        let _ : Mono y := SSet.Nonsingular.mono'
          (c.obj (Fin.last d)).simplex
          (c.obj (Fin.last d)).nonDegenerate
        rw [← meshN_map_le_iff_of_mono y,
          map_meshFaceOfLE, map_meshFaceOfLE]
        exact c.monotone hij }).monotone.functor

private theorem map_meshLiftChain
    {X : SSet.{u}} [X.Nonsingular] {d : ℕ}
    (c : (CategoryTheory.nerve X.N) _⦋d⦌) :
    (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm
        (c.obj (Fin.last d)).simplex)).app _
      (meshLiftChain c) = c := by
  apply ComposableArrows.ext
    (h := fun j => by
      change SSet.N.map
        (SSet.yonedaEquiv.symm
          (c.obj (Fin.last d)).simplex)
        (meshFaceOfLE
          (c.monotone (Fin.le_last j))) = c.obj j
      exact map_meshFaceOfLE _)
    (w := by
      intro i hi
      subsingleton)

private theorem exists_successor_representative
    {X : SSet.{u}} [X.Nonsingular]
    (y : (SSet.sd.obj X).N) :
    ∃ (x : X.N)
      (τ : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋y.dim⦌),
      SSet.yonedaEquiv.symm y.simplex =
        SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ) ≫
          SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) := by
  let eX := SSet.sdIsoNondegenerateNerve X
  let c : (SSet.nondegenerateNerve.obj X) _⦋y.dim⦌ :=
    eX.hom.app _ y.simplex
  have hcNon : c ∈
      (SSet.nondegenerateNerve.obj X).nonDegenerate y.dim := by
    exact (SSet.nonDegenerate_iff_of_mono eX.hom y.simplex).mpr
      y.nonDegenerate
  let x : X.N := c.obj (Fin.last y.dim)
  let localChain := meshLiftChain c
  let eR := SSet.sdIsoNondegenerateNerve
    (Δ[x.dim] : SSet.{u})
  let τ : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋y.dim⦌ :=
    (SSet.stdSimplex.sdIso.hom.app ⦋x.dim⦌).app _
      (eR.inv.app _ localChain)
  refine ⟨x, τ, ?_⟩
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
  apply CategoryTheory.injective_of_mono (eX.hom.app _)
  have hnat := SSet.sdToNondegenerateNerve.naturality
    (SSet.yonedaEquiv.symm x.simplex)
  rw [← SSet.sdIsoNondegenerateNerve_hom X,
    ← SSet.sdIsoNondegenerateNerve_hom
      (Δ[x.dim] : SSet.{u})] at hnat
  change SSet.sd.map (SSet.yonedaEquiv.symm x.simplex) ≫ eX.hom =
    eR.hom ≫
      SSet.nondegenerateNerve.map
        (SSet.yonedaEquiv.symm x.simplex) at hnat
  have happ := congrArg (fun q => q.app _
      ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ)) hnat
  change eX.hom.app _
      ((SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app _
        ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ)) =
    (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm x.simplex)).app _
        (eR.hom.app _
          ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ)) at happ
  rw [happ]
  change c = (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm x.simplex)).app _
        (eR.hom.app _
          ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ))
  have htau :
      (SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ =
        eR.inv.app _ localChain := by
    dsimp [τ]
    change ((SSet.stdSimplex.sdIso.hom.app ⦋x.dim⦌).app _ ≫
      (SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _)
        (eR.inv.app _ localChain) = eR.inv.app _ localChain
    have hid := congr_app
      (Iso.hom_inv_id_app SSet.stdSimplex.sdIso ⦋x.dim⦌)
      (op ⦋y.dim⦌)
    exact ConcreteCategory.congr_hom
      hid (eR.inv.app _ localChain)
  rw [htau]
  change c = (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm x.simplex)).app _
        (eR.hom.app _ (eR.inv.app _ localChain))
  have hcancel : eR.hom.app _ (eR.inv.app _ localChain) =
      localChain := by
    change (eR.inv.app _ ≫ eR.hom.app _) localChain = localChain
    exact ConcreteCategory.congr_hom (Iso.inv_hom_id_app eR _) localChain
  rw [hcancel]
  exact (map_meshLiftChain c).symm

private theorem sdIterCellMap_precomp
    (n k : ℕ) {d e : ℕ}
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u}))
    (p : ⦋e⦌ ⟶ ⦋d⦌) :
    SSet.sdIterCellMap n k (SSet.stdSimplex.map p ≫ σ) =
      SSet.stdSimplex.toTopMap p ≫ SSet.sdIterCellMap n k σ := by
  apply TopCat.ext
  intro z
  change (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom
        (SSet.toTop.map (SSet.stdSimplex.map p ≫ σ)
          ((SimplexCategory.toTopHomeo.{u} ⦋e⦌).symm z))) =
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom
        (SSet.toTop.map σ
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm
            (Convexity.StdSimplex.map p z))))
  rw [SSet.toTop.map_comp]
  have h := SimplexCategory.toTopHomeo_symm_naturality_apply
    p z
  exact congrArg (fun q =>
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom
        (SSet.toTop.map σ q))) h.symm

private theorem sdIterCellMap_zero_eq_toTopMap
    (n : ℕ) {d : ℕ} (σ : (Δ[d] : SSet.{u}) ⟶ Δ[n]) :
    SSet.sdIterCellMap n 0 σ =
      SSet.stdSimplex.toTopMap
        (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv σ)) := by
  let p := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv σ)
  change SSet.sdIterCellMap n 0 σ = SSet.stdSimplex.toTopMap p
  have hσ : σ = SSet.stdSimplex.map p := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_map]
    exact (SSet.stdSimplex.objEquiv.symm_apply_apply _).symm
  apply TopCat.ext
  intro z
  rw [hσ]
  change (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) 0).hom
        (SSet.toTop.map (SSet.stdSimplex.map p)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z))) =
    Convexity.StdSimplex.map p z
  have hid :
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) 0).hom
          (SSet.toTop.map (SSet.stdSimplex.map p)
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z)) =
        SSet.toTop.map (SSet.stdSimplex.map p)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z) := by
    rw [SSet.toTopSdIterIso_zero]
    rfl
  rw [hid]
  have h := SimplexCategory.toTopHomeo_naturality_apply
    p ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z)
  simpa only [Homeomorph.apply_symm_apply] using h

private theorem sdIterCellMap_succ_nondegenerate
    (n k : ℕ)
    (y : (SSet.sd.obj
      ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))).N)
    (x : ((SSet.sdIter k).obj (Δ[n] : SSet.{u})).N)
    (τ : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋y.dim⦌)
    (hy : SSet.yonedaEquiv.symm y.simplex =
      SSet.yonedaEquiv.symm
          ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ) ≫
        SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) :
    SSet.sdIterCellMap n (k + 1)
        (SSet.yonedaEquiv.symm y.simplex) =
      TopCat.ofHom (SimplexCategory.sdCellMap τ) ≫
        SSet.sdIterCellMap n k
          (SSet.yonedaEquiv.symm x.simplex) := by
  let σy : (Δ[y.dim] : SSet.{u}) ⟶
      (SSet.sdIter (k + 1)).obj (Δ[n] : SSet.{u}) := by
    change (Δ[y.dim] : SSet.{u}) ⟶
      SSet.sd.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))
    exact SSet.yonedaEquiv.symm y.simplex
  let σrep : (Δ[y.dim] : SSet.{u}) ⟶
      (SSet.sdIter (k + 1)).obj (Δ[n] : SSet.{u}) := by
    change (Δ[y.dim] : SSet.{u}) ⟶
      SSet.sd.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))
    exact SSet.yonedaEquiv.symm
        ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ) ≫
      SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)
  have hσ : σy = σrep := by
    dsimp [σy, σrep]
    exact hy
  change SSet.sdIterCellMap n (k + 1) σy = _
  rw [hσ]
  have hmap : SSet.toTop.map σrep =
      SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ τ)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) := by
    dsimp [σrep]
    exact SSet.toTop.map_comp _ _
  apply TopCat.ext
  intro z
  have hcell := SSet.toTopSdIso_hom_cell_apply
    ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) x τ z
  simp only [SSet.sdIterCellMap]
  rw [hmap, SSet.toTopSdIterIso_succ]
  exact congrArg (fun q =>
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom q)) hcell

private theorem sdIterCellMap_affine_and_diam
    (n k : ℕ) : ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      Convexity.IsAffineMap ℝ (SSet.sdIterCellMap n k σ).hom ∧
      Metric.diam (Set.range (SSet.sdIterCellMap n k σ).hom) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
          Metric.diam (Set.univ : Set
            (Convexity.StdSimplex ℝ (Fin (n + 1)))) := by
  induction k with
  | zero =>
      intro d σ
      let p := SSet.stdSimplex.objEquiv (SSet.yonedaEquiv σ)
      have hcell := sdIterCellMap_zero_eq_toTopMap n σ
      constructor
      · rw [hcell]
        change Convexity.IsAffineMap ℝ
          (Convexity.StdSimplex.map p)
        exact Convexity.StdSimplex.isAffineMap_map ℝ p
      · simp only [pow_zero, one_mul]
        apply Metric.diam_mono (Set.subset_univ _)
        exact isCompact_univ.isBounded
  | succ k ih =>
      intro d σ
      let T := (SSet.sdIter (k + 1)).obj (Δ[n] : SSet.{u})
      let s : T _⦋d⦌ := SSet.yonedaEquiv σ
      obtain ⟨e, p, hp, y, hs⟩ := SSet.exists_nonDegenerate T s
      let σy : (Δ[e] : SSet.{u}) ⟶ T :=
        SSet.yonedaEquiv.symm y.1
      have hσ : σ = SSet.stdSimplex.map p ≫ σy := by
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
        change s = T.map p.op y.1
        exact hs
      have hrange : Set.range (SSet.sdIterCellMap n (k + 1) σ).hom ⊆
          Set.range (SSet.sdIterCellMap n (k + 1) σy).hom := by
        rw [hσ, sdIterCellMap_precomp]
        rintro _ ⟨z, rfl⟩
        exact ⟨SSet.stdSimplex.toTopMap p z, rfl⟩
      have hcarrierBounded : Bornology.IsBounded
          (Set.range (SSet.sdIterCellMap n (k + 1) σy).hom) :=
        (isCompact_range
          (SSet.sdIterCellMap n (k + 1) σy).hom.continuous).isBounded
      have hdiamSub : Metric.diam
          (Set.range (SSet.sdIterCellMap n (k + 1) σ).hom) ≤
          Metric.diam
            (Set.range (SSet.sdIterCellMap n (k + 1) σy).hom) :=
        Metric.diam_mono hrange hcarrierBounded
      obtain ⟨x, τ, hy⟩ := exists_successor_representative
        (X := (SSet.sdIter k).obj (Δ[n] : SSet.{u}))
        (SSet.N.mk y.1 y.2)
      have hsucc := sdIterCellMap_succ_nondegenerate n k
        (SSet.N.mk y.1 y.2) x τ hy
      change SSet.sdIterCellMap n (k + 1)
        (SSet.yonedaEquiv.symm y.1) = _ at hsucc
      obtain ⟨hgAffine, hgDiam⟩ := ih (SSet.yonedaEquiv.symm x.simplex)
      have hcarrierAffine : Convexity.IsAffineMap ℝ
          (SSet.sdIterCellMap n (k + 1) σy).hom := by
        dsimp [σy]
        rw [hsucc]
        change Convexity.IsAffineMap ℝ
          ((SSet.sdIterCellMap n k
            (SSet.yonedaEquiv.symm x.simplex)).hom ∘
              SimplexCategory.sdCellMap τ)
        exact hgAffine.comp (sdCellMap_isAffine τ)
      have hcontract := diam_range_comp_sdCellMap_le τ
        (SSet.sdIterCellMap n k
          (SSet.yonedaEquiv.symm x.simplex)).hom hgAffine
      have hcarrierDiam : Metric.diam
          (Set.range (SSet.sdIterCellMap n (k + 1) σy).hom) ≤
          (x.dim : ℝ) / ((x.dim : ℝ) + 1) *
            Metric.diam (Set.range (SSet.sdIterCellMap n k
              (SSet.yonedaEquiv.symm x.simplex)).hom) := by
        dsimp [σy]
        rw [hsucc]
        exact hcontract
      have hxn : x.dim ≤ n :=
        nondegenerate_dim_le_sdIter_stdSimplex n k x
      have hfactor : (x.dim : ℝ) / ((x.dim : ℝ) + 1) ≤
          (n : ℝ) / ((n : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hxnR : (x.dim : ℝ) ≤ n := by exact_mod_cast hxn
        nlinarith
      have hq : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
        positivity
      have hcarrierFinal : Metric.diam
          (Set.range (SSet.sdIterCellMap n (k + 1) σy).hom) ≤
          ((n : ℝ) / ((n : ℝ) + 1)) ^ (k + 1) *
            Metric.diam (Set.univ : Set
              (Convexity.StdSimplex ℝ (Fin (n + 1)))) := by
        calc
          Metric.diam
              (Set.range (SSet.sdIterCellMap n (k + 1) σy).hom) ≤
              (x.dim : ℝ) / ((x.dim : ℝ) + 1) *
                Metric.diam (Set.range (SSet.sdIterCellMap n k
                  (SSet.yonedaEquiv.symm x.simplex)).hom) := hcarrierDiam
          _ ≤ (n : ℝ) / ((n : ℝ) + 1) *
                Metric.diam (Set.range (SSet.sdIterCellMap n k
                  (SSet.yonedaEquiv.symm x.simplex)).hom) :=
            mul_le_mul_of_nonneg_right hfactor Metric.diam_nonneg
          _ ≤ (n : ℝ) / ((n : ℝ) + 1) *
              (((n : ℝ) / ((n : ℝ) + 1)) ^ k *
                Metric.diam (Set.univ : Set
                  (Convexity.StdSimplex ℝ (Fin (n + 1))))) :=
            mul_le_mul_of_nonneg_left hgDiam hq
          _ = ((n : ℝ) / ((n : ℝ) + 1)) ^ (k + 1) *
                Metric.diam (Set.univ : Set
                  (Convexity.StdSimplex ℝ (Fin (n + 1)))) := by
            rw [pow_succ]
            ring
      constructor
      · rw [hσ, sdIterCellMap_precomp]
        change Convexity.IsAffineMap ℝ
          ((SSet.sdIterCellMap n (k + 1) σy).hom ∘
            Convexity.StdSimplex.map p)
        exact hcarrierAffine.comp
          (Convexity.StdSimplex.isAffineMap_map ℝ p)
      · exact hdiamSub.trans hcarrierFinal

/--
Every cell of the `k`-fold subdivision of an `n`-simplex has diameter at most
`(n / (n + 1))^k` times the diameter of the entire standard `n`-simplex.
-/
theorem diam_range_sdIterCellMap_le
    (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    Metric.diam (Set.range (SSet.sdIterCellMap n k σ).hom) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n + 1)))) :=
  (sdIterCellMap_affine_and_diam n k σ).2

private theorem image_range_sdIterCellMap_eq
    {B : TopCat.{u}} {n k d : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ B)
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    (b.hom.comp (meshStdToRealization.{u} n)) ''
        Set.range (SSet.sdIterCellMap n k σ).hom =
      Set.range
        (SSet.toTop.map σ ≫
          (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm x, ?_⟩
    simp [SSet.sdIterCellMap, meshStdToRealization]
  · rintro ⟨x, rfl⟩
    refine ⟨SSet.sdIterCellMap n k σ
        (SimplexCategory.toTopHomeo.{u} ⦋d⦌ x), ?_, ?_⟩
    · exact ⟨SimplexCategory.toTopHomeo.{u} ⦋d⦌ x, rfl⟩
    · simp [SSet.sdIterCellMap, meshStdToRealization]

/--
For a continuous map `|Δ[n]| → B` and an open cover of `B` with an independently
sized index type, there is a subdivision depth `k` such that every realized simplex
of `sd^k Δ[n]` maps into some cover member.
-/
theorem exists_sdIter_simplex_range_subset
    {B : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ k : ℕ, ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom ⊆
          (U i : Set B) := by
  let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), B) :=
    b.hom.comp (meshStdToRealization.{u} n)
  obtain ⟨k, hk⟩ :=
    Convexity.StdSimplex.exists_iterate_diam_subordinate n g
      (fun i ↦ (U i : Set B)) (fun i ↦ (U i).isOpen) (by
        simp [hU.iSup_set_eq_univ])
  refine ⟨k, ?_⟩
  intro d σ
  obtain ⟨i, hi⟩ := hk
    (Set.range (SSet.sdIterCellMap n k σ).hom)
    (Set.range_nonempty _)
    (SSet.diam_range_sdIterCellMap_le n k σ)
  refine ⟨i, ?_⟩
  rw [← image_range_sdIterCellMap_eq b σ]
  simpa [g] using hi

end SSet

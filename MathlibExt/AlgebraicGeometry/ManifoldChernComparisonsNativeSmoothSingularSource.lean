/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.KahlerClassGeometry
public import MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finsupp.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Continuous

/-!
# Native smooth singular source

The native simplex affine maps preserve the smooth extension predicate:
precomposing a smooth native singular simplex with a native simplex map
keeps a smooth extension on a neighborhood of the parameter simplex. This
proves the `native_smooth_singular_source` target of Wanted native
singular/de Rham and rational Chern comparisons: every source operation
uses the actual smooth simplex, native chain/dual cochain map, fixed
parameter integral, actual coefficient inclusion or the fixed curvature
determinant.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open scoped Simplicial Manifold ContDiff BigOperators

/-- The affine tail-coordinate map induced by a vertex map between simplices. -/
private def affineSimplexMap (a b : ℕ) (g : Fin (b + 1) → Fin (a + 1))
    (t : SimplexCoordinates b) : SimplexCoordinates a :=
  WithLp.toLp 2 fun j : Fin a =>
    (if g 0 = j.succ then (1 - ∑ k : Fin b, t k) else 0) +
      ∑ k : Fin b, (if g k.succ = j.succ then t k else 0)

/-- Coordinates of the affine tail-coordinate map. -/
private theorem affineSimplexMap_apply (a b : ℕ)
    (g : Fin (b + 1) → Fin (a + 1)) (t : SimplexCoordinates b) (j : Fin a) :
    (affineSimplexMap a b g t) j =
      (if g 0 = j.succ then (1 - ∑ k : Fin b, t k) else 0) +
        ∑ k : Fin b, (if g k.succ = j.succ then t k else 0) := rfl

/-- The affine tail-coordinate map is smooth. -/
private theorem contDiff_affineSimplexMap (a b : ℕ)
    (g : Fin (b + 1) → Fin (a + 1)) :
    ContDiff ℝ ∞ (affineSimplexMap a b g) := by
  have hcoord : ∀ k : Fin b, ContDiff ℝ ∞ fun t : SimplexCoordinates b => t k := by
    intro k
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff
  have hsum : ContDiff ℝ ∞ fun t : SimplexCoordinates b => ∑ k : Fin b, t k := by
    refine ContDiff.sum fun k _ => ?_
    exact hcoord k
  refine (contDiff_piLp 2).2 fun j => ?_
  change ContDiff ℝ ∞ fun t : SimplexCoordinates b =>
    (affineSimplexMap a b g t) j
  simp only [affineSimplexMap_apply]
  refine ContDiff.add ?_ (ContDiff.sum fun k _ => ?_)
  · by_cases h0 : g 0 = j.succ
    · simp only [ite_eq_left h0]
      exact contDiff_const.sub hsum
    · simp only [ite_eq_right h0]
      exact contDiff_const
  · by_cases hk : g k.succ = j.succ
    · simp only [ite_eq_left hk]
      exact hcoord k
    · simp only [ite_eq_right hk]
      exact contDiff_const

/-- A fiber sum over successor indices detects whether the vertex is zero. -/
private theorem sum_ite_succ_eq (a : ℕ) (h : Fin (a + 1)) (c : ℝ) :
    (∑ j : Fin a, (if h = j.succ then c else 0)) = (if h = 0 then 0 else c) := by
  by_cases hh : h = 0
  · subst hh
    rw [ite_eq_left rfl]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact ite_eq_right (Ne.symm (Fin.succ_ne_zero j))
  · obtain ⟨j₀, hj₀⟩ := Fin.eq_succ_of_ne_zero hh
    subst hj₀
    have h₀ : ∀ b : Fin a, b ∈ Finset.univ → b ≠ j₀ →
        (if j₀.succ = b.succ then c else 0) = 0 := by
      intro b _ hbne
      exact ite_eq_right fun he => hbne ((Fin.succ_injective _) he.symm)
    have h₁ : j₀ ∉ Finset.univ → (if j₀.succ = j₀.succ then c else 0) = 0 :=
      fun hcon => absurd (Finset.mem_univ j₀) hcon
    rw [ite_eq_right (Fin.succ_ne_zero j₀), Finset.sum_eq_single j₀ h₀ h₁,
      ite_eq_left rfl]

/-- The affine tail-coordinate map preserves the parameter domain. -/
private theorem affineSimplexMap_mem (a b : ℕ)
    (g : Fin (b + 1) → Fin (a + 1)) (t : SimplexCoordinates b)
    (ht : t ∈ standardParameterDomain b) :
    affineSimplexMap a b g t ∈ standardParameterDomain a := by
  simp only [standardParameterDomain, Set.mem_ofPred_eq] at ht ⊢
  obtain ⟨hnn, hsum⟩ := ht
  constructor
  · intro j
    rw [affineSimplexMap_apply]
    refine add_nonneg ?_ (Finset.sum_nonneg fun k _ => ?_)
    · split_ifs
      · exact sub_nonneg.mpr hsum
      · exact le_rfl
    · split_ifs
      · exact hnn k
      · exact le_rfl
  · have key : ∀ (h : Fin (a + 1)) (c : ℝ),
        (∑ j : Fin a, (if h = j.succ then c else 0)) = (if h = 0 then 0 else c) :=
      sum_ite_succ_eq a
    have hdecomp : (∑ j : Fin a, (affineSimplexMap a b g t) j)
        = (if g 0 = 0 then (0 : ℝ) else (1 - ∑ k : Fin b, t k)) +
          ∑ k : Fin b, (if g k.succ = 0 then 0 else t k) := by
      simp only [affineSimplexMap_apply, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp only [key]
    rw [hdecomp]
    have hw0 : 0 ≤ (1 : ℝ) - ∑ k : Fin b, t k := sub_nonneg.mpr hsum
    have h1 : (if g 0 = 0 then (0 : ℝ) else (1 - ∑ k : Fin b, t k)) ≤
        1 - ∑ k : Fin b, t k := by
      split_ifs
      · exact hw0
      · exact le_rfl
    have h2 : (∑ k : Fin b, (if g k.succ = 0 then (0 : ℝ) else t k)) ≤
        ∑ k : Fin b, t k := by
      refine Finset.sum_le_sum fun k _ => ?_
      split_ifs
      · exact hnn k
      · exact le_rfl
    calc (if g 0 = 0 then (0 : ℝ) else (1 - ∑ k : Fin b, t k)) +
            ∑ k : Fin b, (if g k.succ = 0 then 0 else t k)
        ≤ (1 - ∑ k : Fin b, t k) + ∑ k : Fin b, t k := add_le_add h1 h2
      _ = 1 := sub_add_cancel _ _

/-- The affine map intertwines tail coordinates with native simplex maps. -/
private theorem affineSimplexMap_commute (a b : ℕ)
    (g : Fin (b + 1) → Fin (a + 1))
    (w : Convexity.StdSimplex ℝ (Fin (b + 1))) (t : SimplexCoordinates b)
    (h0 : w.weights 0 = 1 - ∑ k : Fin b, t k)
    (htail : ∀ k : Fin b, w.weights k.succ = t k) (j : Fin a) :
    (Convexity.StdSimplex.map g w).weights j.succ =
      (affineSimplexMap a b g t) j := by
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finsupp.add_apply, Fin.sum_univ_succ, h0, htail, affineSimplexMap_apply]

/-- The native simplex affine maps preserve this exact smooth extension predicate. -/
theorem native_smooth_singular_source {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] :
    SmoothSingularSource (n := n) (M := M) := by
  refine ⟨fun p q f σ hσ => ?_⟩
  obtain ⟨S⟩ := hσ
  refine ⟨?_⟩
  refine SmoothSimplexModel.mk
    ((affineSimplexMap p.unop.len q.unop.len ⇑f.unop) ⁻¹' S.neighborhood) ?_ ?_
    (S.map ∘ affineSimplexMap p.unop.len q.unop.len ⇑f.unop) ?_ ?_
  · exact IsOpen.preimage (contDiff_affineSimplexMap _ _ _).continuous
      S.open_neighborhood
  · intro t ht
    exact S.contains (affineSimplexMap_mem _ _ _ _ ht)
  · exact S.smooth.comp
      (contDiff_affineSimplexMap _ _ _).contDiffOn.contMDiffOn subset_rfl
  · intro x
    have hτ : ((nativeSingularSet (M := M)).map f σ).down =
        SimplexCategory.toTop.map f.unop ≫ σ.down := rfl
    have hS := S.normalized ((SimplexCategory.toTop.map f.unop).hom x)
    have hcomp : (show SimplexCategory.toTop.obj ⦋q.unop.len⦌ ⟶ TopCat.of M from
          SimplexCategory.toTop.map f.unop ≫ σ.down).hom x =
        (show SimplexCategory.toTop.obj ⦋p.unop.len⦌ ⟶ TopCat.of M from σ.down).hom
          ((SimplexCategory.toTop.map f.unop).hom x) := rfl
    have hz : (((SimplexCategory.toTop.map f.unop).hom x).down) =
        Convexity.StdSimplex.map ⇑f.unop x.down := rfl
    have htail : ∀ k : Fin q.unop.len, x.down.weights k.succ =
        (simplexCoordinates q.unop.len x) k := fun k => rfl
    have htot := x.down.total_of_fintype
    rw [Fin.sum_univ_succ] at htot
    simp only [htail] at htot
    have h0 : x.down.weights 0 =
        1 - ∑ k : Fin q.unop.len, (simplexCoordinates q.unop.len x) k := by
      have h2 := congrArg
        (fun s : ℝ => s - ∑ k : Fin q.unop.len, (simplexCoordinates q.unop.len x) k)
        htot
      rwa [add_sub_cancel_right] at h2
    rw [hτ, hcomp]
    refine hS.trans ?_
    simp only [Function.comp_apply]
    congr 1
    refine PiLp.ext fun j => ?_
    change (((SimplexCategory.toTop.map f.unop).hom x).down).weights j.succ =
      (affineSimplexMap p.unop.len q.unop.len ⇑f.unop
        (simplexCoordinates q.unop.len x)) j
    rw [hz]
    exact affineSimplexMap_commute p.unop.len q.unop.len ⇑f.unop x.down
      (simplexCoordinates q.unop.len x) h0 htail j

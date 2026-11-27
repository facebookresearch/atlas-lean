/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornLocusPolymorphic
public import MathlibExt.Topology.Convenient.StdSimplexHornLocus
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SingularSet

/-!
# Kan singular complexes in every universe

The singular complex of every topological space is a Kan complex. Realized
positive-dimensional horns retract from their realized standard simplices;
transport through the realization–singular adjunction gives horn fillers.
The realization identifications use lifted affine simplices and horn loci,
so the statements apply to spaces in every universe. See Goerss–Jardine,
Simplicial Homotopy Theory, I.3.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace TopCat

/--
The topological isomorphism from the realization of a standard simplex in
universe `u` to the universe lift of its real affine simplex.
-/
noncomputable def realizedSimplexIsoUlift (n : ℕ) :
    SSet.toTop.{u}.obj (Δ[n] : SSet.{u}) ≅
      TopCat.uliftFunctor.obj
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))) :=
  TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo
    (SimplexCategory.mk n)).trans
    (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).uliftFunctorObjHomeo)

/--
For a positive dimension, the map from the realized standard simplex to the
realized horn obtained from the lifted affine horn retraction.
-/
noncomputable def realizedHornRetractU (n : ℕ) (k : Fin (n + 1))
    (hn : 0 < n) :
    SSet.toTop.{u}.obj (Δ[n] : SSet.{u}) ⟶
      SSet.toTop.{u}.obj (SSet.horn.{u} n k) :=
  (realizedSimplexIsoUlift n).hom ≫
    TopCat.uliftFunctor.map
      (TopCat.ofHom (hornRetractMap k hn)) ≫
    (realizedHornIsoUliftHornLocus n k hn).inv

/--
The realized horn inclusion followed by its categorical retraction fixes
every realized horn point.
-/
theorem realizedHornRetractU_ι (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (y : SSet.toTop.{u}.obj (SSet.horn.{u} n k)) :
    realizedHornRetractU n k hn
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) = y := by
  have himg : (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) ∈
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
        Set.range (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι) :=
    ⟨_, Set.mem_range.mpr ⟨y, rfl⟩, rfl⟩
  rw [hornRange_image_eq_locus_u n k hn] at himg
  obtain ⟨j₀, hj₀k, hj₀0⟩ := himg
  have hmem : (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) ∈ hornLocus k hn :=
    ⟨j₀, hj₀k, hj₀0⟩
  have hfix := hornRetractMap_fix k hn
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y))
    hmem
  have hS : ((realizedSimplexIsoUlift (n := n)).hom
      (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y)).down =
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) := rfl
  have hH : ((realizedHornIsoUliftHornLocus n k hn).hom y).down.val =
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y) := rfl
  have hloc : (hornRetractMap k hn
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y))) =
      ((realizedHornIsoUliftHornLocus n k hn).hom y).down := by
    apply Subtype.ext
    have hfixVal : ((hornRetractMap k hn
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y))).val :
        Convexity.StdSimplex ℝ (Fin (n + 1))) =
      ((realizedHornIsoUliftHornLocus n k hn).hom y).down.val := by
      rw [hfix, hH]
    exact hfixVal
  have hU : (TopCat.uliftFunctor.map
      (TopCat.ofHom (hornRetractMap k hn))
      ((realizedSimplexIsoUlift n).hom
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y))).down =
      hornRetractMap k hn
        (((realizedSimplexIsoUlift n).hom
          (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y)).down) := rfl
  have heq : TopCat.uliftFunctor.map
        (TopCat.ofHom (hornRetractMap k hn))
        ((realizedSimplexIsoUlift n).hom
          (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y)) =
      (realizedHornIsoUliftHornLocus n k hn).hom y := by
    apply ULift.down_injective
    rw [hU, hS]
    exact hloc
  have hinv : (realizedHornIsoUliftHornLocus n k hn).inv
      ((realizedHornIsoUliftHornLocus n k hn).hom y) = y := by
    have h := ConcreteCategory.congr_hom
      (Iso.hom_inv_id (realizedHornIsoUliftHornLocus n k hn)) y
    rw [ConcreteCategory.comp_apply, CategoryTheory.id_apply] at h
    exact h
  change (realizedHornIsoUliftHornLocus n k hn).inv
    (TopCat.uliftFunctor.map (TopCat.ofHom (hornRetractMap k hn))
      ((realizedSimplexIsoUlift n).hom
        (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι y))) = y
  rw [heq]
  exact hinv

/--
For a topological space in any universe, its singular simplicial set is a
Kan complex.
-/
theorem toSSet_obj_kanComplex (X : TopCat.{u}) :
    SSet.KanComplex (TopCat.toSSet.obj X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  obtain ⟨g, hdesc⟩ := hf.exists_desc
  let gTop : SSet.toTop.{u}.obj (Λ[n + 1, i] : SSet.{u}) ⟶ X :=
    (sSetTopAdj.homEquiv _ _).symm g
  let r : SSet.toTop.{u}.obj (Δ[n + 1] : SSet.{u}) ⟶
      SSet.toTop.{u}.obj (Λ[n + 1, i] : SSet.{u}) :=
    realizedHornRetractU (n + 1) i (Nat.succ_pos n)
  have hret : SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι ≫ r = 𝟙 _ := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    simpa using realizedHornRetractU_ι (n + 1) i (Nat.succ_pos n) y
  have hface : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      SSet.toTop.{u}.map (SSet.stdSimplex.δ j) ≫ r =
        SSet.toTop.{u}.map (SSet.horn.ι i j hj) := by
    intro j hj
    have hδ : SSet.toTop.{u}.map (SSet.stdSimplex.δ j) =
        SSet.toTop.{u}.map (SSet.horn.ι i j hj) ≫
          SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι := by
      rw [← Functor.map_comp, SSet.horn.ι_ι]
    rw [hδ, Category.assoc, hret, Category.comp_id]
  refine ⟨sSetTopAdj.homEquiv _ _ (r ≫ gTop), fun j hj => ?_⟩
  have e1 : SSet.stdSimplex.δ j ≫ sSetTopAdj.homEquiv _ _ (r ≫ gTop) =
      sSetTopAdj.homEquiv _ _
        (SSet.toTop.{u}.map (SSet.stdSimplex.δ j) ≫ (r ≫ gTop)) := by
    rw [Adjunction.homEquiv_naturality_left]
  rw [e1, ← Category.assoc, hface j hj]
  have e2 : sSetTopAdj.homEquiv _ _
      (SSet.toTop.{u}.map (SSet.horn.ι i j hj) ≫ gTop) =
      SSet.horn.ι i j hj ≫ sSetTopAdj.homEquiv _ _ gTop := by
    rw [Adjunction.homEquiv_naturality_left]
  rw [e2]
  have hsymm : sSetTopAdj.homEquiv _ _ gTop = g :=
    Equiv.apply_symm_apply _ _
  rw [hsymm]
  exact hdesc j hj

end TopCat

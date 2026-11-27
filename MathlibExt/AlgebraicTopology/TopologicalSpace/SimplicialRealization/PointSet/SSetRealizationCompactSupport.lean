/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteSubcomplexCells
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteGeneratedSubcomplex
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellCover
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellInjective
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationSubcomplexCarrier
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import MathlibExt.Topology.Convenient.StdSimplexMinimalFace
public import Mathlib.Topology.Order

/-!
# Finite simplicial support of compact realization subsets

Every compact subset of the geometric realization of a simplicial set is contained
in the realized image of a finite subcomplex. Here finiteness refers to finitely
many nondegenerate simplices of the subcomplex. The ambient simplicial set need
not be finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- Carriers whose interior cell meets `K`. -/
private def MeetsCarrier (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (s : Y.N) : Prop :=
  ∃ p : Convexity.StdSimplex ℝ (Fin (s.dim + 1)),
    (∀ i, 0 < p.weights i) ∧ SSet.sigmaToTop Y ⟨s, p⟩ ∈ K

/-- Chosen interior point for a meeting carrier. -/
private noncomputable def selPoint (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (s : Y.N) (h : MeetsCarrier Y K s) :
    Convexity.StdSimplex ℝ (Fin (s.dim + 1)) :=
  Classical.choose h

private theorem selPoint_pos (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (s : Y.N) (h : MeetsCarrier Y K s) :
    ∀ i, 0 < (selPoint Y K s h).weights i :=
  (Classical.choose_spec h).1

private theorem selPoint_mem (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (s : Y.N) (h : MeetsCarrier Y K s) :
    SSet.sigmaToTop Y ⟨s, selPoint Y K s h⟩ ∈ K :=
  (Classical.choose_spec h).2

/-- Selector image in the realization. -/
private noncomputable def selImg (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (a : { s : Y.N // MeetsCarrier Y K s }) : SSet.toTop.obj Y :=
  SSet.sigmaToTop Y ⟨a.val, selPoint Y K a.val a.property⟩

private theorem selImg_mem (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y))
    (a : { s : Y.N // MeetsCarrier Y K s }) : selImg Y K a ∈ K :=
  selPoint_mem Y K a.val a.property

/-- The selector map is injective by carrier uniqueness. -/
private theorem selImg_injective (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y)) :
    Function.Injective (selImg Y K) := by
  intro a b hab
  have hcar : a.val = b.val :=
    SSet.carrier_eq_of_sigmaToTop_eq_of_interior Y a.val b.val _ _
      (selPoint_pos Y K a.val a.property)
      (selPoint_pos Y K b.val b.property) hab
  exact Subtype.ext hcar

/-- `sigmaToTop` agrees with the interior-presentation map (`toTopHomeo` form). -/
private theorem sigmaToTop_eq_interior_map (T : SSet.{u}) (n : ℕ)
    (s : T _⦋n⦌) (hs : s ∈ T.nonDegenerate n)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    SSet.sigmaToTop T ⟨SSet.N.mk s hs, q⟩ =
      SSet.toTop.map (SSet.yonedaEquiv.symm s)
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm q) := rfl

/-- Every subset of the selector image is closed in the realization. -/
private theorem isClosed_of_subset_range (Y : SSet.{u})
    (K : Set (SSet.toTop.obj Y)) (V : Set (SSet.toTop.obj Y))
    (hV : V ⊆ Set.range (selImg Y K)) : IsClosed V := by
  have hTop : IsColimit (SSet.toTop.mapCocone Y.coconeN) :=
    isColimitOfPreserves SSet.toTop Y.isColimitCoconeN
  refine (TopCat.isClosed_iff_of_isColimit _ hTop V).mpr fun S => ?_
  have hleg : (SSet.toTop.mapCocone Y.coconeN).ι.app S =
      SSet.toTop.map S.subcomplex.ι := rfl
  rw [hleg]
  have hSfin : SSet.Finite (S.subcomplex : SSet.{u}) := inferInstance
  have hex : ∀ y : SSet.toTop.obj (S.subcomplex : SSet.{u}),
      ∃ t : (S.subcomplex : SSet.{u}).N,
      ∃ q : Convexity.StdSimplex ℝ (Fin (t.dim + 1)),
        (∀ i, 0 < q.weights i) ∧ SSet.sigmaToTop _ ⟨t, q⟩ = y := by
    intro y
    obtain ⟨n, s, hs, q, hq, hx⟩ :=
      SSet.exists_nonDegenerate_interior_presentation (S.subcomplex : SSet.{u}) y
    refine ⟨SSet.N.mk s hs, q, hq, ?_⟩
    rw [sigmaToTop_eq_interior_map]
    exact hx
  choose tfn qfn hpos heq using hex
  have hVV : ∀ w : ↥V,
      ∃ c : { s : Y.N // MeetsCarrier Y K s }, selImg Y K c = w.val :=
    fun w => hV w.property
  choose cfn hc using hVV
  have hembed : Function.Injective (SSet.toTop.map S.subcomplex.ι) :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι S.subcomplex).isEmbedding.injective
  have hmem : ∀ w : ↥(SSet.toTop.map S.subcomplex.ι ⁻¹' V),
      (SSet.Subcomplex.mapCarrier S.subcomplex (tfn w.val)).subcomplex ≤
        S.subcomplex := by
    intro w
    rw [SSet.Subcomplex.mem_ambientCells_iff]
    have hrfl : (SSet.Subcomplex.mapCarrier S.subcomplex (tfn w.val)).simplex =
        S.subcomplex.ι.app _ (tfn w.val).simplex := rfl
    rw [hrfl]
    exact (tfn w.val).simplex.property
  have hconn : ∀ w : ↥(SSet.toTop.map S.subcomplex.ι ⁻¹' V),
      SSet.Subcomplex.mapCarrier S.subcomplex (tfn w.val) =
        (cfn ⟨SSet.toTop.map S.subcomplex.ι w.val, w.property⟩).val := by
    intro w
    have e1 : SSet.sigmaToTop Y
          ⟨SSet.Subcomplex.mapCarrier S.subcomplex (tfn w.val), qfn w.val⟩ =
        SSet.toTop.map S.subcomplex.ι w.val := by
      have hmap := SSet.Subcomplex.sigmaToTop_mapCarrier S.subcomplex
        (tfn w.val) (qfn w.val)
      rw [heq w.val] at hmap
      exact hmap
    have e2 : SSet.toTop.map S.subcomplex.ι w.val =
        selImg Y K
          (cfn ⟨SSet.toTop.map S.subcomplex.ι w.val, w.property⟩) :=
      (hc ⟨SSet.toTop.map S.subcomplex.ι w.val, w.property⟩).symm
    exact SSet.carrier_eq_of_sigmaToTop_eq_of_interior Y _ _ _ _
      (hpos w.val) (selPoint_pos Y K _ _) (e1.trans e2)
  let F : ↥(SSet.toTop.map S.subcomplex.ι ⁻¹' V) →
      SSet.Subcomplex.AmbientCells S.subcomplex :=
    fun w => ⟨SSet.Subcomplex.mapCarrier S.subcomplex (tfn w.val), hmem w⟩
  have hFinj : Function.Injective F := by
    intro w₁ w₂ h12
    have hcar : SSet.Subcomplex.mapCarrier S.subcomplex (tfn w₁.val) =
        SSet.Subcomplex.mapCarrier S.subcomplex (tfn w₂.val) :=
      Subtype.ext_iff.mp h12
    have hccval :
        (cfn ⟨SSet.toTop.map S.subcomplex.ι w₁.val, w₁.property⟩).val =
        (cfn ⟨SSet.toTop.map S.subcomplex.ι w₂.val, w₂.property⟩).val :=
      (hconn w₁).symm.trans (hcar.trans (hconn w₂))
    have hcc := Subtype.ext hccval
    have hsel : selImg Y K
          (cfn ⟨SSet.toTop.map S.subcomplex.ι w₁.val, w₁.property⟩) =
        selImg Y K
          (cfn ⟨SSet.toTop.map S.subcomplex.ι w₂.val, w₂.property⟩) :=
      congrArg _ hcc
    rw [hc _, hc _] at hsel
    have hval : w₁.val = w₂.val := hembed hsel
    exact Subtype.ext hval
  have hfinT : Finite ↥(SSet.toTop.map S.subcomplex.ι ⁻¹' V) :=
    Finite.of_injective F hFinj
  have hfin : (SSet.toTop.map S.subcomplex.ι ⁻¹' V).Finite :=
    Set.finite_coe_iff.mpr hfinT
  exact hfin.isClosed

/--
For any simplicial set `Y` and compact subset `K ⊆ |Y|`, there is a finite
subcomplex `A ⊆ Y` whose realized inclusion image contains `K`.
-/
theorem exists_finite_subcomplex_of_isCompact
    (Y : SSet.{u}) (K : Set (SSet.toTop.obj Y)) (hK : IsCompact K) :
    ∃ (A : Y.Subcomplex) (_ : SSet.Finite (A : SSet.{u})),
      K ⊆ Set.range (SSet.toTop.map A.ι) := by
  classical
  have hclosed : ∀ V : Set (SSet.toTop.obj Y),
      V ⊆ Set.range (selImg Y K) → IsClosed V :=
    isClosed_of_subset_range Y K
  have hTclosed : IsClosed (Set.range (selImg Y K)) :=
    hclosed _ (fun x hx => hx)
  have hsub : Set.range (selImg Y K) ⊆ K := by
    rintro _ ⟨a, rfl⟩
    exact selImg_mem Y K a
  have hdisc : DiscreteTopology ↥(Set.range (selImg Y K)) :=
    discreteTopology_iff_forall_isClosed.mpr (fun U => by
      have hU : U = Subtype.val ⁻¹' (Subtype.val '' U) :=
        (Set.preimage_image_eq U Subtype.val_injective).symm
      rw [hU]
      refine IsClosed.preimage continuous_subtype_val (hclosed _ (fun x hx => ?_))
      obtain ⟨y, _, rfl⟩ := hx
      exact y.property)
  have hTcomp : IsCompact (Set.range (selImg Y K)) :=
    hK.of_isClosed_subset hTclosed hsub
  have hTfin : (Set.range (selImg Y K)).Finite :=
    hTcomp.finite (isDiscrete_iff_discreteTopology.mpr hdisc)
  have hidx : Finite { s : Y.N // MeetsCarrier Y K s } := by
    have h1 : Finite ↥(Set.range (selImg Y K)) :=
      Set.finite_coe_iff.mp hTfin
    exact (Equiv.finite_iff
      (Equiv.ofInjective (selImg Y K) (selImg_injective Y K))).mpr h1
  have hidxI := hidx
  let sfn : { s : Y.N // MeetsCarrier Y K s } → Σ n, Y _⦋n⦌ :=
    fun i => ⟨i.val.dim, i.val.simplex⟩
  let A : Y.Subcomplex :=
    ⨆ i, SSet.Subcomplex.ofSimplex (sfn i).2
  have hAfin : SSet.Finite (A : SSet.{u}) :=
    SSet.Subcomplex.finite_iSup_ofSimplex Y sfn
  refine ⟨A, hAfin, ?_⟩
  intro x hxK
  obtain ⟨n, s, hs, q, hq, hx⟩ :=
    SSet.exists_nonDegenerate_interior_presentation Y x
  have hmeet : MeetsCarrier Y K (SSet.N.mk s hs) := by
    refine ⟨q, hq, ?_⟩
    rw [sigmaToTop_eq_interior_map]
    rw [hx]
    exact hxK
  let ic : { s : Y.N // MeetsCarrier Y K s } := ⟨SSet.N.mk s hs, hmeet⟩
  have hle : SSet.Subcomplex.ofSimplex s ≤ A := by
    change SSet.Subcomplex.ofSimplex s ≤
      ⨆ i, SSet.Subcomplex.ofSimplex (sfn i).2
    exact le_iSup (fun i => SSet.Subcomplex.ofSimplex (sfn i).2) ic
  have hfac : (SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle) ≫
      A.ι = SSet.yonedaEquiv.symm s := by
    calc (SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle) ≫ A.ι
        = SSet.Subcomplex.toOfSimplex s ≫
          (SSet.Subcomplex.homOfLE hle ≫ A.ι) := by rw [Category.assoc]
      _ = SSet.Subcomplex.toOfSimplex s ≫ (SSet.Subcomplex.ofSimplex s).ι := by
          rw [SSet.Subcomplex.homOfLE_ι]
      _ = SSet.yonedaEquiv.symm s := SSet.Subcomplex.toOfSimplex_ι s
  refine ⟨SSet.toTop.map
    (SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle)
    ((SimplexCategory.toTopHomeo ⦋n⦌).symm q), ?_⟩
  have hmap : SSet.toTop.map
      ((SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle) ≫ A.ι)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm q) = x := by
    rw [hfac]
    exact hx
  have hfold : SSet.toTop.map
      ((SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle) ≫ A.ι)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm q) =
      SSet.toTop.map A.ι (SSet.toTop.map
        (SSet.Subcomplex.toOfSimplex s ≫ SSet.Subcomplex.homOfLE hle)
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm q)) := by
    rw [Functor.map_comp]
    rfl
  rw [hfold] at hmap
  exact hmap

end SSet

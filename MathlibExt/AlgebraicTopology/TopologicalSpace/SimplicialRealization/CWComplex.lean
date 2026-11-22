/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.CWComplex.Abstract.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic
public import MathlibExt.Topology.CWComplex.CharacteristicDiskMap
public import MathlibExt.Topology.Category.TopPair.ClosedBall
public import MathlibExt.Topology.Category.TopPair.NDRCofibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedNullhomotopy
import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
import Mathlib.Analysis.Convex.GaugeRescale
import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellInjective
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex

/-!
# Cellular geometry of simplicial realization

Transport the actual nondegenerate-simplex skeleta, attachments, and colimit
through geometric realization, then identify each realized simplex boundary
with the boundary of a Euclidean disk. This constructs genuine categorical
`TopCat.CWComplex` data on the actual realization. The distinguished vertex
has closed cylinder-retraction data derived from the homotopy extension property.

The classical `Topology.CWComplex` structure is constructed directly from the
actual nondegenerate characteristic maps, their embedded interiors, finite
boundary support, and the realization quotient's weak topology. The selected
vertex is identified with its actual zero cell in both structures.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology Convexity
open scoped Simplicial

universe u

namespace SSet

/-- The actual realized relative cell complex of a simplicial monomorphism,
with its dimension-indexed nondegenerate simplex attachments. -/
@[expose]
def realizationRelativeCellComplexOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{u}
      (fun (n : ℕ) (_ : Unit) => toTop.map (boundary n).ι) (toTop.map i) := by
  let c := relativeCellComplexOfMono i
  let _ : PreservesWellOrderContinuousOfShape ℕ toTop.{u} :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  let hMap := c.toTransfiniteCompositionOfShape.map toTop
  exact
    { toTransfiniteCompositionOfShape := hMap
      attachCells n hn := by
        let a := c.attachCells n hn
        exact
          { ι := a.ι
            π := a.π
            cofan₁ := Cofan.mk (toTop.obj a.cofan₁.pt)
              (fun j => toTop.map (a.cofan₁.inj j))
            cofan₂ := Cofan.mk (toTop.obj a.cofan₂.pt)
              (fun j => toTop.map (a.cofan₂.inj j))
            isColimit₁ := by
              let e := Discrete.compNatIsoDiscrete
                (fun j : a.ι => ((boundary n).toSSet : SSet.{u})) toTop
              refine (IsColimit.precomposeHomEquiv e _).1 ?_
              exact IsColimit.ofIsoColimit (isColimitOfPreserves toTop a.isColimit₁)
                (Cocone.ext (Iso.refl _) (by intro j; rfl))
            isColimit₂ := by
              let e := Discrete.compNatIsoDiscrete
                (fun j : a.ι => (Δ[n] : SSet.{u})) toTop
              refine (IsColimit.precomposeHomEquiv e _).1 ?_
              exact IsColimit.ofIsoColimit (isColimitOfPreserves toTop a.isColimit₂)
                (Cocone.ext (Iso.refl _) (by intro j; rfl))
            m := toTop.map a.m
            hm j := by
              change toTop.map (a.cofan₁.inj j) ≫ toTop.map a.m =
                toTop.map (boundary n).ι ≫ toTop.map (a.cofan₂.inj j)
              simpa only [Functor.map_comp] using congrArg toTop.map (a.hm j)
            g₁ := toTop.map a.g₁
            g₂ := toTop.map a.g₂
            isPushout := a.isPushout.map toTop } }

private def cellRegion (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

private def dropCoordinate (n : ℕ) (w : StdSimplex ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => w.weights i.castSucc)

private theorem dropCoordinate_mem (n : ℕ) (w : StdSimplex ℝ (Fin (n + 1))) :
    dropCoordinate n w ∈ cellRegion n := by
  refine ⟨fun i => w.weights_nonneg i.castSucc, ?_⟩
  have h := w.total_of_fintype
  rw [Fin.sum_univ_castSucc] at h
  have hn := w.weights_nonneg (Fin.last n)
  change ∑ i : Fin n, w.weights i.castSucc ≤ 1
  linarith

private def appendCoordinate (n : ℕ) (x : cellRegion n) :
    StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm
    (Fin.lastCases (1 - ∑ i, x.1 i) (fun i => x.1 i))
  nonneg := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using sub_nonneg.mpr x.2.2
    · simpa using x.2.1 i
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_castSucc]
    simp

private def regionEquiv (n : ℕ) : StdSimplex ℝ (Fin (n + 1)) ≃ cellRegion n where
  toFun w := ⟨dropCoordinate n w, dropCoordinate_mem n w⟩
  invFun := appendCoordinate n
  left_inv w := by
    apply StdSimplex.ext
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have h := w.total_of_fintype
      rw [Fin.sum_univ_castSucc] at h
      simp only [appendCoordinate, Finsupp.coe_equivFunOnFinite_symm, Fin.lastCases_last,
        dropCoordinate, PiLp.toLp_apply]
      linarith
    · simp [appendCoordinate, dropCoordinate]
  right_inv x := by
    apply Subtype.ext
    ext i
    simp [appendCoordinate, dropCoordinate]

private theorem continuous_dropCoordinate (n : ℕ) : Continuous (dropCoordinate n) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi fun i : Fin n => StdSimplex.continuous_weights_apply ℝ i.castSucc)

private def regionHomeomorph (n : ℕ) : StdSimplex ℝ (Fin (n + 1)) ≃ₜ cellRegion n :=
  Continuous.homeoOfEquivCompactToT2 (f := regionEquiv n)
    ((continuous_dropCoordinate n).subtype_mk (dropCoordinate_mem n))

private theorem isCompact_cellRegion (n : ℕ) : IsCompact (cellRegion n) := by
  have h : Set.range (dropCoordinate n) = cellRegion n := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact dropCoordinate_mem n w
    · intro hx
      exact ⟨appendCoordinate n ⟨x, hx⟩,
        congrArg Subtype.val ((regionEquiv n).apply_symm_apply ⟨x, hx⟩)⟩
  rw [← h, ← Set.image_univ]
  exact isCompact_univ.image (continuous_dropCoordinate n)

private theorem convex_cellRegion (n : ℕ) : Convex ℝ (cellRegion n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa using hab

private def regionOpen (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

private theorem isOpen_regionOpen (n : ℕ) : IsOpen (regionOpen n) := by
  have h : regionOpen n =
      (⋂ i : Fin n, (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Set.Ioi 0) ∩
        (fun x => ∑ i, x i) ⁻¹' Set.Iio 1 := by
    ext x
    simp only [regionOpen, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ioi, Set.mem_Iio, Set.mem_ofPred_eq]
  rw [h]
  have hc (i : Fin n) : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    fun_prop
  refine (isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage (hc i)).inter ?_
  apply isOpen_Iio.preimage
  fun_prop

private theorem regionOpen_subset_interior (n : ℕ) :
    regionOpen n ⊆ interior (cellRegion n) := by
  apply interior_maximal _ (isOpen_regionOpen n)
  intro x hx
  exact ⟨fun i => (hx.1 i).le, hx.2.le⟩

private theorem interior_subset_regionOpen (n : ℕ) :
    interior (cellRegion n) ⊆ regionOpen n := by
  intro x hx
  refine ⟨fun i => ?_, ?_⟩
  · have h : cellRegion n ⊆ (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Set.Ici 0 :=
      fun y hy => hy.1 i
    have hi := interior_mono h hx
    have ho := PiLp.isOpenMap_apply 2 (fun _ : Fin n => ℝ) i
    rw [← ho.preimage_interior_eq_interior_preimage (by fun_prop), interior_Ici] at hi
    exact hi
  · cases n with
    | zero => simp
    | succ n =>
      let s : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
        ∑ i, PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) i
      have hs (y : EuclideanSpace ℝ (Fin (n + 1))) : s y = ∑ i, y i := by
        simp [s]
      have hsurj : Function.Surjective s := by
        intro r
        refine ⟨PiLp.single 2 (0 : Fin (n + 1)) r, ?_⟩
        rw [hs]
        simp
      have ho : IsOpenMap s :=
        LinearMap.isOpenMap_of_finiteDimensional s.toLinearMap hsurj
      have h : cellRegion (n + 1) ⊆ s ⁻¹' Set.Iic 1 := by
        intro y hy
        simpa only [Set.mem_preimage, Set.mem_Iic, hs] using hy.2
      have hi := interior_mono h hx
      rw [← ho.preimage_interior_eq_interior_preimage s.continuous, interior_Iic] at hi
      simpa only [Set.mem_preimage, Set.mem_Iio, hs] using hi

private theorem interior_cellRegion (n : ℕ) :
    interior (cellRegion n) = regionOpen n :=
  Set.Subset.antisymm (interior_subset_regionOpen n) (regionOpen_subset_interior n)

private theorem cellRegion_interior_nonempty (n : ℕ) :
    (interior (cellRegion n)).Nonempty := by
  rw [interior_cellRegion]
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => 1 / ((n : ℝ) + 1)), ?_⟩
  have hn : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨fun i => by change 0 < 1 / ((n : ℝ) + 1); positivity, ?_⟩
  change ∑ _ : Fin n, (1 / ((n : ℝ) + 1)) < 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one hn]
  linarith

private theorem dropCoordinate_mem_frontier_iff (n : ℕ)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    dropCoordinate n w ∈ frontier (cellRegion n) ↔ ∃ j, w.weights j = 0 := by
  rw [frontier, (isCompact_cellRegion n).isClosed.closure_eq, interior_cellRegion]
  constructor
  · rintro ⟨_, hnot⟩
    by_contra hzero
    have hpos (j : Fin (n + 1)) : 0 < w.weights j := by
      have hn := w.weights_nonneg j
      have hne : w.weights j ≠ 0 := fun hj => hzero ⟨j, hj⟩
      exact lt_of_le_of_ne hn hne.symm
    apply hnot
    refine ⟨fun i => hpos i.castSucc, ?_⟩
    have ht := w.total_of_fintype
    rw [Fin.sum_univ_castSucc] at ht
    have hl := hpos (Fin.last n)
    change ∑ i : Fin n, w.weights i.castSucc < 1
    linarith
  · rintro ⟨j, hj⟩
    refine ⟨dropCoordinate_mem n w, ?_⟩
    intro hopen
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hi := hopen.1 i
      change 0 < w.weights i.castSucc at hi
      rw [hj] at hi
      exact lt_irrefl _ hi
    · have ht := w.total_of_fintype
      rw [Fin.sum_univ_castSucc, hj, add_zero] at ht
      have hs := hopen.2
      change ∑ i : Fin n, w.weights i.castSucc < 1 at hs
      linarith

private def cellGauge (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_cellRegion n) (cellRegion_interior_nonempty n)
    (isCompact_cellRegion n).isBounded).choose

private theorem cellGauge_image_region (n : ℕ) :
    cellGauge n '' cellRegion n = Metric.closedBall 0 1 := by
  have h := (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_cellRegion n) (cellRegion_interior_nonempty n)
    (isCompact_cellRegion n).isBounded).choose_spec
  simpa only [cellGauge, (isCompact_cellRegion n).isClosed.closure_eq] using h.2.1

private theorem cellGauge_image_frontier (n : ℕ) :
    cellGauge n '' frontier (cellRegion n) = Metric.sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_cellRegion n) (cellRegion_interior_nonempty n)
    (isCompact_cellRegion n).isBounded).choose_spec.2.2

private theorem cellGauge_mem_sphere_iff (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    cellGauge n x ∈ Metric.sphere 0 1 ↔ x ∈ frontier (cellRegion n) := by
  rw [← cellGauge_image_frontier]
  constructor
  · rintro ⟨y, hy, heq⟩
    rwa [(cellGauge n).injective heq] at hy
  · intro hx
    exact Set.mem_image_of_mem _ hx

private def regionDiskHomeomorph (n : ℕ) :
    cellRegion n ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ((cellGauge n).image (cellRegion n)).trans
    (Homeomorph.setCongr (cellGauge_image_region n))

private def simplexDiskHomeomorph (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ TopCat.disk.{u} n :=
  (SimplexCategory.toTopHomeo ⦋n⦌).trans
    ((regionHomeomorph n).trans ((regionDiskHomeomorph n).trans Homeomorph.ulift.symm))

private theorem simplexDiskHomeomorph_boundary_iff (n : ℕ)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
      (simplexDiskHomeomorph n x).down.1 ∈ Metric.sphere 0 1 := by
  have hzero : x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
      ∃ j, ((SimplexCategory.toTopHomeo ⦋n⦌) x).weights j = 0 := by
    constructor
    · exact SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange n x
    · rintro ⟨j, hj⟩
      simpa only [Homeomorph.symm_apply_apply] using
        SSet.mem_realizedBoundary_of_zeroCoord.{u} n
          ((SimplexCategory.toTopHomeo ⦋n⦌) x) j hj
  rw [hzero]
  change _ ↔ cellGauge n (dropCoordinate n ((SimplexCategory.toTopHomeo ⦋n⦌) x)) ∈ _
  rw [cellGauge_mem_sphere_iff, dropCoordinate_mem_frontier_iff]

private def diskBoundarySubspaceHomeomorph (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ
      {y : TopCat.disk.{u} n // y.down.1 ∈ Metric.sphere 0 1} where
  toFun x := ⟨TopCat.diskBoundaryInclusion n x, x.down.2⟩
  invFun y := ⟨⟨y.1.down.1, y.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  continuous_toFun := (TopCat.diskBoundaryInclusion n).hom.continuous.subtype_mk _
  continuous_invFun := by
    fun_prop

private def boundaryDiskHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ≃ₜ TopCat.diskBoundary.{u} n := by
  let h := TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.closedT1Embeddings_toTop_map_of_mono (SSet.boundary.{u} n).ι)
  exact h.isEmbedding.toHomeomorph.trans
    (((simplexDiskHomeomorph n).subtype (simplexDiskHomeomorph_boundary_iff n)).trans
      (diskBoundarySubspaceHomeomorph n).symm)

private theorem boundaryDiskHomeomorph_inclusion (n : ℕ)
    (x : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u})) :
    TopCat.diskBoundaryInclusion n (boundaryDiskHomeomorph n x) =
      simplexDiskHomeomorph n (SSet.toTop.map (SSet.boundary.{u} n).ι x) := rfl

/-- A chosen disk identification of the actual realized standard simplex. -/
def stdSimplex.toTopDiskIso (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≅ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo (simplexDiskHomeomorph n)

/-- The matching disk-boundary identification of the actual realized simplex boundary. -/
def boundary.toTopDiskBoundaryIso (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ≅ TopCat.diskBoundary.{u} n :=
  TopCat.isoOfHomeo (boundaryDiskHomeomorph n)

/-- The two disk identifications carry the actual boundary inclusion to the disk inclusion. -/
@[reassoc]
theorem boundary.toTopDiskBoundaryIso_hom_comp_inclusion (n : ℕ) :
    (boundary.toTopDiskBoundaryIso.{u} n).hom ≫ TopCat.diskBoundaryInclusion n =
      SSet.toTop.map (SSet.boundary.{u} n).ι ≫ (stdSimplex.toTopDiskIso n).hom := by
  ext x
  exact boundaryDiskHomeomorph_inclusion n x

/-- A chosen arrow isomorphism from the actual realized boundary inclusion to a disk boundary. -/
def boundary.toTopDiskArrowIso (n : ℕ) :
    Arrow.mk (SSet.toTop.map (SSet.boundary.{u} n).ι) ≅
      Arrow.mk (TopCat.diskBoundaryInclusion.{u} n) :=
  Arrow.isoMk (boundary.toTopDiskBoundaryIso n) (stdSimplex.toTopDiskIso n)
    (boundary.toTopDiskBoundaryIso_hom_comp_inclusion n).symm

/-- The actual realization of a simplicial monomorphism, with its dimension-indexed
Euclidean disk attachments. -/
@[expose]
def realizationRelativeCWComplexOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.RelativeCWComplex (SSet.toTop.map i) := by
  let c := SSet.realizationRelativeCellComplexOfMono i
  exact
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
      attachCells n hn :=
        (c.attachCells n hn).reindexCellTypes (TopCat.RelativeCWComplex.basicCell n)
          id (fun _ => boundary.toTopDiskArrowIso n) }

/-- Genuine categorical CW data on the actual realization, obtained from its
nondegenerate-simplex skeleta and the chosen disk-boundary identifications. -/
@[expose]
def realizationCWComplex (X : SSet.{u}) : TopCat.CWComplex (SSet.toTop.obj X) := by
  let c := realizationRelativeCWComplexOfMono (⊥ : X.Subcomplex).ι
  let h : IsInitial (SSet.toTop.obj (⊥ : X.Subcomplex).toSSet) :=
    (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj (G := SSet.toTop)
  let e : Arrow.mk (SSet.toTop.map (⊥ : X.Subcomplex).ι) ≅
      Arrow.mk (initial.to (SSet.toTop.obj X)) :=
    Arrow.isoMk (h.uniqueUpToIso initialIsInitial) (Iso.refl _) (by
      exact h.hom_ext _ _)
  exact
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofArrowIso e
      attachCells n hn := c.attachCells n hn }


/-- The cells of the actual realization CW structure are its nondegenerate simplices.
This preserves the index dictionary of `relativeCellComplexCellsEquiv`. -/
@[expose]
def realizationCWComplexCellsEquiv (X : SSet.{u}) : (realizationCWComplex X).Cells ≃ X.N where
  toFun c := N.mk c.k.simplex c.k.nonDegenerate
  invFun s :=
    { j := s.dim
      hj := by simp
      k := { simplex := s.simplex, nonDegenerate := s.nonDegenerate, notMem := by simp } }
  left_inv c := by cases c; rfl
  right_inv s := by cases s; rfl

/-- The simplex label of a CW cell has the dimension of its attachment. -/
@[simp]
theorem realizationCWComplexCellsEquiv_dim (X : SSet.{u})
    (c : (realizationCWComplex X).Cells) :
    (realizationCWComplexCellsEquiv X c).dim = c.j := rfl

/-- Each characteristic disk map is the actual nondegenerate-simplex map in disk coordinates. -/
theorem realizationCWComplex_cell_ι (X : SSet.{u}) (c : (realizationCWComplex X).Cells) :
    c.ι = (stdSimplex.toTopDiskIso c.j).inv ≫
      toTop.map (yonedaEquiv.symm (realizationCWComplexCellsEquiv X c).simplex) := by
  let k : relativeCellComplexOfMono.Cell (⊥ : X.Subcomplex).ι c.j := c.k
  change (stdSimplex.toTopDiskIso c.j).inv ≫ toTop.map k.ιSigmaStdSimplex ≫
      toTop.map (relativeCellComplexOfMono.b (⊥ : X.Subcomplex).ι c.j) ≫
      toTop.map (Subcomplex.ι _) ≫ 𝟙 _ = (stdSimplex.toTopDiskIso c.j).inv ≫ toTop.map k.map
  rw [Category.comp_id, ← toTop.map_comp, ← toTop.map_comp]
  rw [relativeCellComplexOfMono.Cell.ι_b_ι k]

/-- The actual zero cell of the realization CW structure selected by the given vertex. -/
abbrev realizationCWVertexCell {X : SSet.{u}} (v : X _⦋0⦌) :
    (realizationCWComplex X).Cells :=
  { j := 0, hj := by simp,
    k := { simplex := v, nonDegenerate := by simp, notMem := by simp } }

/-- The selected vertex cell is zero dimensional. -/
@[simp]
theorem realizationCWVertexCell_j {X : SSet.{u}} (v : X _⦋0⦌) :
    (realizationCWVertexCell v).j = 0 := rfl

/-- The selected zero cell is precisely the specified realized vertex. -/
theorem realizationCWVertexCell_ι_apply {X : SSet.{u}} (v : X _⦋0⦌)
    (x : TopCat.disk.{u} 0) : (realizationCWVertexCell v).ι x = realizedVertex v := by
  rw [realizationCWComplex_cell_ι]
  change toTop.map (yonedaEquiv.symm v) ((stdSimplex.toTopDiskIso 0).inv x) = realizedVertex v
  unfold realizedVertex
  congr 1
  exact Subsingleton.elim _ _

private theorem realizationTarget_isFibrant (B : TopCat.{u}) :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    IsFibrant B := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : CategoryWithFibrations SSet.{u} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  rw [isFibrant_iff, fibration_iff]
  change TopCat.realizedHornInclusions.{u}.rlp (terminal.from B)
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff]
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
  exact TopCat.toSSet_obj_kanComplex B

private theorem pathEvalZero_fibration (B : TopCat.{u}) :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    Fibration (TopCat.pathEvalZero B) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : IsFibrant B := realizationTarget_isFibrant B
  let _ : Fibration (TopCat.pathEndpoints B) :=
    TopCat.modelCategory.pathEndpoints_fibration B
  have h : Fibration
      (TopCat.pathEndpoints B ≫ (prod.fst : B ⨯ B ⟶ B)) := inferInstance
  simpa only [TopCat.pathEndpoints, prod.lift_fst] using h

/-- Realization of every simplicial monomorphism has the homotopy extension property. -/
theorem toTop_map_isHurewiczCofibration {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.IsHurewiczCofibration (SSet.toTop.map i) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : Cofibration (SSet.toTop.map i) :=
    (cofibration_iff _).mpr (SSet.toTop_map_mem_realizedBoundaryLLP i)
  intro Z instZ f H h0
  let B : TopCat.{u} := TopCat.of Z
  let _ : Fibration (TopCat.pathEvalZero B) := pathEvalZero_fibration B
  let _ : WeakEquivalence (TopCat.pathEvalZero B) :=
    (weakEquivalence_iff _).mpr (TopCat.pathEvalZero_mem_weakHomotopyEquivalences B)
  let _ : HasLiftingProperty (SSet.toTop.map i) (TopCat.pathEvalZero B) :=
    ModelCategory.cm4b _ _
  let ht : C((SSet.toTop.obj X) × TopCat.I.{u}, Z) :=
    H.comp
      { toFun := fun z => (TopCat.I.homeomorph.{u} z.2, z.1)
        continuous_toFun :=
          (TopCat.I.homeomorph.{u}.continuous.comp continuous_snd).prodMk continuous_fst }
  let a : SSet.toTop.obj X ⟶ TopCat.pathObject B := TopCat.ofHom ht.curry
  let b : SSet.toTop.obj Y ⟶ B := TopCat.ofHom f
  have sq : CommSq a (SSet.toTop.map i) (TopCat.pathEvalZero B) b := by
    constructor
    apply TopCat.ext
    intro x
    change H (TopCat.I.homeomorph.{u} 0, x) = f (SSet.toTop.map i x)
    rw [TopCat.I.homeomorph_zero.{u}]
    exact h0 x
  let L := sq.lift
  let extension : C(unitInterval × (SSet.toTop.obj Y), Z) :=
    { toFun := fun z => L z.2 (TopCat.I.homeomorph.{u}.symm z.1)
      continuous_toFun := by fun_prop }
  refine ⟨{ extension := extension, extension_zero := ?_, extension_subspace := ?_ }⟩
  · intro x
    have hL := ConcreteCategory.congr_hom sq.fac_right x
    change L x 0 = f x at hL
    change L x (TopCat.I.homeomorph.{u}.symm 0) = f x
    have hzero : TopCat.I.homeomorph.{u}.symm 0 = (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.{u}.injective
      simp
    rw [hzero]
    exact hL
  · intro t x
    have hL := ConcreteCategory.congr_hom sq.fac_left x
    change L (SSet.toTop.map i x) = ht.curry x at hL
    change L (SSet.toTop.map i x) (TopCat.I.homeomorph.{u}.symm t) = H (t, x)
    rw [hL]
    change H (TopCat.I.homeomorph.{u} (TopCat.I.homeomorph.{u}.symm t), x) = H (t, x)
    rw [Homeomorph.apply_symm_apply]

private theorem mono_const_vertex {X : SSet.{u}} (v : X _⦋0⦌) :
    Mono (SSet.const (X := Δ[0]) v) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _
  apply SSet.stdSimplex.objEquiv.injective
  subsingleton

private theorem realizedVertex_closedHEP (X : SSet.{u}) (v : X _⦋0⦌) :
    IsClosedEmbedding (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex v)).hom ∧
      TopCat.IsHurewiczCofibration
        (TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex v)) := by
  let i : (Δ[0] : SSet.{u}) ⟶ X := SSet.const v
  let _ : Mono i := mono_const_vertex v
  let e : TopCat.of PUnit ≅ SSet.toTop.obj (Δ[0] : SSet.{u}) :=
    TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique _ _)
  have hcomp : e.hom ≫ SSet.toTop.map i =
      TopCat.const (X := TopCat.of PUnit) (SSet.realizedVertex v) := by
    apply TopCat.ext
    intro x
    exact DFunLike.congr_fun (SSet.toTop_map_const_hom (A := Δ[0]) v) (e.hom x)
  have hclosed : IsClosedEmbedding (e.hom ≫ SSet.toTop.map i).hom :=
    (TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (SSet.closedT1Embeddings_toTop_map_of_mono i)).comp (TopCat.homeoOfIso e).isClosedEmbedding
  have hHEP : TopCat.IsHurewiczCofibration (e.hom ≫ SSet.toTop.map i) :=
    TopCat.hurewiczCofibrations_comp e.hom (SSet.toTop.map i)
      (TopCat.hurewiczCofibrations_iso e) (toTop_map_isHurewiczCofibration i)
  rw [hcomp] at hclosed hHEP
  exact ⟨hclosed, hHEP⟩

/-- The inclusion of the actual distinguished vertex is a closed embedding. -/
theorem realizedVertex_isClosedEmbedding {X : SSet.{u}} (v : X _⦋0⦌) :
    IsClosedEmbedding (TopCat.const (X := TopCat.of PUnit) (realizedVertex v)).hom :=
  (realizedVertex_closedHEP X v).1

/-- The actual distinguished vertex has the homotopy extension property. -/
theorem realizedVertex_isHurewiczCofibration {X : SSet.{u}} (v : X _⦋0⦌) :
    TopCat.IsHurewiczCofibration
      (TopCat.const (X := TopCat.of PUnit) (realizedVertex v)) :=
  (realizedVertex_closedHEP X v).2

/-- The embedded topological pair consisting of the actual realization and its selected vertex. -/
abbrev realizedVertexPair {X : SSet.{u}} (v : X _⦋0⦌) : TopPair.{u} :=
  TopPair.of (TopCat.const (X := TopCat.of PUnit) (realizedVertex v))
    (realizedVertex_isClosedEmbedding v).isEmbedding

/-- The map of the vertex pair is the inclusion of the specified realized vertex. -/
@[simp]
theorem realizedVertexPair_map {X : SSet.{u}} (v : X _⦋0⦌) :
    (realizedVertexPair v).map =
      TopCat.const (X := TopCat.of PUnit) (realizedVertex v) := rfl

/-- Chosen closed cylinder-retraction data for the actual distinguished vertex pair. -/
def realizedVertexHurewiczCofibrationData {X : SSet.{u}} (v : X _⦋0⦌) :
    TopPair.HurewiczCofibrationData (realizedVertexPair v) :=
  TopPair.HurewiczCofibrationData.ofIsClosedEmbeddingOfHEP
    (realizedVertex_isClosedEmbedding v) (realizedVertex_isHurewiczCofibration v)

/-- Standard NDR control and deformation for the actual distinguished vertex. -/
def realizedVertexStandardNDRData {X : SSet.{u}} (v : X _⦋0⦌) :
    TopPair.StandardNDRData (realizedVertexPair v) :=
  (realizedVertexHurewiczCofibrationData v).toStandardNDRData


namespace realizationClassical

open scoped Classical

private def euclideanPiHomeomorph (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) := PiLp.homeomorph 2 _

private def normChangeRegion (n : ℕ) : Set (Fin n → ℝ) :=
  euclideanPiHomeomorph n '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

private theorem convex_normChangeRegion (n : ℕ) : Convex ℝ (normChangeRegion n) :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).linear_image
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap

private theorem isCompact_normChangeRegion (n : ℕ) : IsCompact (normChangeRegion n) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).image (euclideanPiHomeomorph n).continuous

private theorem normChangeRegion_interior_nonempty (n : ℕ) :
    (interior (normChangeRegion n)).Nonempty := by
  change (interior (euclideanPiHomeomorph n '' Metric.closedBall 0 1)).Nonempty
  rw [← Homeomorph.image_interior]
  exact ⟨euclideanPiHomeomorph n 0,
    ⟨0, Metric.ball_subset_interior_closedBall (by simp), rfl⟩⟩

private def normGauge (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_normChangeRegion n) (normChangeRegion_interior_nonempty n)
    (isCompact_normChangeRegion n).isBounded).choose

private theorem normGauge_image_region (n : ℕ) :
    normGauge n '' normChangeRegion n = Metric.closedBall 0 1 := by
  have h := (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_normChangeRegion n) (normChangeRegion_interior_nonempty n)
    (isCompact_normChangeRegion n).isBounded).choose_spec
  simpa only [normGauge, (isCompact_normChangeRegion n).isClosed.closure_eq] using h.2.1

private theorem normGauge_image_frontier (n : ℕ) :
    normGauge n '' frontier (normChangeRegion n) = Metric.sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_normChangeRegion n) (normChangeRegion_interior_nonempty n)
    (isCompact_normChangeRegion n).isBounded).choose_spec.2.2

private theorem normGauge_image_interior (n : ℕ) :
    normGauge n '' interior (normChangeRegion n) = Metric.ball 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_normChangeRegion n) (normChangeRegion_interior_nonempty n)
    (isCompact_normChangeRegion n).isBounded).choose_spec.1

private def normChangeHomeomorph (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ) :=
  (euclideanPiHomeomorph n).trans (normGauge n)

private theorem normChangeHomeomorph_image_closedBall (n : ℕ) :
    normChangeHomeomorph n '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  change (fun x => normGauge n (euclideanPiHomeomorph n x)) '' Metric.closedBall 0 1 = _
  rw [← Set.image_image]
  exact normGauge_image_region n

private theorem normChangeHomeomorph_image_sphere (n : ℕ) :
    normChangeHomeomorph n '' Metric.sphere 0 1 = Metric.sphere 0 1 := by
  change (fun x => normGauge n (euclideanPiHomeomorph n x)) '' Metric.sphere 0 1 = _
  rw [← Set.image_image]
  have h : frontier (normChangeRegion n) =
      euclideanPiHomeomorph n '' Metric.sphere 0 1 := by
    rw [normChangeRegion, ← Homeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
  rw [← h]
  exact normGauge_image_frontier n

private theorem normChangeHomeomorph_image_ball (n : ℕ) :
    normChangeHomeomorph n '' Metric.ball 0 1 = Metric.ball 0 1 := by
  change (fun x => normGauge n (euclideanPiHomeomorph n x)) '' Metric.ball 0 1 = _
  rw [← Set.image_image]
  have h : interior (normChangeRegion n) =
      euclideanPiHomeomorph n '' Metric.ball 0 1 := by
    rw [normChangeRegion, ← Homeomorph.image_interior, interior_closedBall _ one_ne_zero]
  rw [← h]
  exact normGauge_image_interior n

private def euclideanPiDiskHomeomorph (n : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.closedBall (0 : Fin n → ℝ) 1 :=
  ((normChangeHomeomorph n).image (Metric.closedBall 0 1)).trans
    (Homeomorph.setCongr (normChangeHomeomorph_image_closedBall n))

private theorem euclideanPiDiskHomeomorph_boundary_iff (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (euclideanPiDiskHomeomorph n x).1 ∈ Metric.sphere 0 1 ↔ x.1 ∈ Metric.sphere 0 1 := by
  change normChangeHomeomorph n x.1 ∈ Metric.sphere 0 1 ↔ _
  rw [← normChangeHomeomorph_image_sphere]
  constructor
  · rintro ⟨y, hy, heq⟩
    rwa [(normChangeHomeomorph n).injective heq] at hy
  · intro hx
    exact Set.mem_image_of_mem _ hx

private def diskPiHomeomorph (n : ℕ) :
    TopCat.disk.{u} n ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
  Homeomorph.ulift.trans (euclideanPiDiskHomeomorph n)

private theorem mem_range_of_arrowIso {A B C D : TopCat.{u}} {f : A ⟶ B} {g : C ⟶ D}
    (e : Arrow.mk f ≅ Arrow.mk g) (x : B) :
    x ∈ Set.range f.hom ↔ (Arrow.rightFunc.mapIso e).hom x ∈ Set.range g.hom := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(Arrow.leftFunc.mapIso e).hom y, ?_⟩
    exact ConcreteCategory.congr_hom e.hom.w y
  · rintro ⟨y, hy⟩
    refine ⟨(Arrow.leftFunc.mapIso e).inv y, ?_⟩
    have hw := ConcreteCategory.congr_hom e.inv.w y
    change f ((Arrow.leftFunc.mapIso e).inv y) = (Arrow.rightFunc.mapIso e).inv (g y) at hw
    rw [hw, hy]
    exact (TopCat.homeoOfIso (Arrow.rightFunc.mapIso e)).symm_apply_apply x

private theorem mem_range_diskBoundaryInclusion (n : ℕ) (x : TopCat.disk.{u} n) :
    x ∈ Set.range (TopCat.diskBoundaryInclusion n).hom ↔ x.down.1 ∈ Metric.sphere 0 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.down.2
  · intro hx
    exact ⟨⟨⟨x.down.1, hx⟩⟩, rfl⟩

private def stdPiDiskHomeomorph (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 :=
  (TopCat.homeoOfIso (SSet.stdSimplex.toTopDiskIso n)).trans (diskPiHomeomorph n)

private theorem stdPiDiskHomeomorph_boundary_iff (n : ℕ)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
      (stdPiDiskHomeomorph n x).1 ∈ Metric.sphere 0 1 := by
  have h₁ := mem_range_of_arrowIso (SSet.boundary.toTopDiskArrowIso n) x
  change x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
    (SSet.stdSimplex.toTopDiskIso n).hom x ∈ Set.range (TopCat.diskBoundaryInclusion n).hom at h₁
  rw [h₁, mem_range_diskBoundaryInclusion]
  exact (euclideanPiDiskHomeomorph_boundary_iff n
    ((SSet.stdSimplex.toTopDiskIso n).hom x).down).symm

private theorem closedBall_mem_ball_iff_not_mem_sphere {n : ℕ}
    (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    x.1 ∈ Metric.ball 0 1 ↔ x.1 ∉ Metric.sphere 0 1 := by
  rw [Metric.mem_ball, Metric.mem_sphere]
  have hx := x.2
  change dist x.1 0 ≤ 1 at hx
  constructor
  · exact ne_of_lt
  · intro h
    exact lt_of_le_of_ne hx h

private theorem stdPiDiskHomeomorph_ball_iff (n : ℕ)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (stdPiDiskHomeomorph n x).1 ∈ Metric.ball 0 1 ↔
      x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom := by
  rw [closedBall_mem_ball_iff_not_mem_sphere, ← stdPiDiskHomeomorph_boundary_iff]

namespace Stages

private def cofanIso {ι : Type u} (B : TopCat.{u})
    (c : Cofan (fun _ : ι => B)) (hc : IsColimit c) :
    TopCat.of (Σ _ : ι, B) ≅ c.pt :=
  (TopCat.sigmaCofanIsColimit (fun _ : ι => B)).coconePointUniqueUpToIso hc

private theorem cofanIso_hom_ι {ι : Type u} (B : TopCat.{u})
    (c : Cofan (fun _ : ι => B)) (hc : IsColimit c) (k : ι) (x : B) :
    (cofanIso B c hc).hom ⟨k, x⟩ = c.inj k x :=
  ConcreteCategory.congr_hom
    ((TopCat.sigmaCofanIsColimit (fun _ : ι => B)).comp_coconePointUniqueUpToIso_hom
      hc ⟨k⟩) x

private theorem cofanIso_inv_ι {ι : Type u} (B : TopCat.{u})
    (c : Cofan (fun _ : ι => B)) (hc : IsColimit c) (k : ι) (x : B) :
    (cofanIso B c hc).inv (c.inj k x) = ⟨k, x⟩ := by
  have h := (TopCat.homeoOfIso (cofanIso B c hc)).symm_apply_apply ⟨k, x⟩
  change (cofanIso B c hc).inv ((cofanIso B c hc).hom ⟨k, x⟩) = ⟨k, x⟩ at h
  rw [cofanIso_hom_ι] at h
  exact h

private theorem cofan_inj_isEmbedding {ι : Type u} (B : TopCat.{u})
    (c : Cofan (fun _ : ι => B)) (hc : IsColimit c) (k : ι) :
    IsEmbedding (c.inj k).hom := by
  have h : IsEmbedding (fun x : B => (cofanIso B c hc).hom ⟨k, x⟩) :=
    (TopCat.homeoOfIso (cofanIso B c hc)).isEmbedding.comp IsEmbedding.sigmaMk
  have heq : (fun x : B => (cofanIso B c hc).hom ⟨k, x⟩) = (c.inj k).hom :=
    funext (cofanIso_hom_ι B c hc k)
  rw [heq] at h
  exact h

variable {A B X Y : TopCat.{u}} {i : A ⟶ B} {f : X ⟶ Y}
  (a : AttachCells.{u} (fun _ : Unit => i) f)

private theorem mem_range_m_iff (k : a.ι) (x : B) :
    a.cofan₂.inj k x ∈ Set.range a.m.hom ↔ x ∈ Set.range i.hom := by
  constructor
  · rintro ⟨y, hy⟩
    let hc := isColimitOfPreserves (forget TopCat) a.isColimit₁
    obtain ⟨⟨l⟩, z, hz⟩ := Types.jointly_surjective_of_isColimit hc y
    change a.cofan₁.inj l z = y at hz
    have hm := ConcreteCategory.congr_hom (a.hm l) z
    change a.m (a.cofan₁.inj l z) = a.cofan₂.inj l (i z) at hm
    rw [hz] at hm
    have heq := congrArg (cofanIso B a.cofan₂ a.isColimit₂).inv (hm.symm.trans hy)
    rw [cofanIso_inv_ι, cofanIso_inv_ι] at heq
    exact ⟨z, congrArg (fun p : Σ _ : a.ι, B => p.2) heq⟩
  · rintro ⟨z, rfl⟩
    exact ⟨a.cofan₁.inj k z, ConcreteCategory.congr_hom (a.hm k) z⟩

private theorem attachInterior_isEmbedding (hf : IsClosed (Set.range f.hom)) (k : a.ι) :
    IsEmbedding (fun x : {x : B // x ∉ Set.range i.hom} => a.cell k x.1) := by
  let U : Set Y := (Set.range f.hom)ᶜ
  have hU : IsOpen U := hf.isOpen_compl
  have hr : f ⁻¹' U = ∅ := by
    ext x
    constructor
    · intro hx
      exact hx ⟨x, rfl⟩
    · intro hx
      exact hx.elim
  have hl : a.g₂ ⁻¹' U ⊆ (Set.range a.m.hom)ᶜ := by
    intro x hx hm
    rcases hm with ⟨z, rfl⟩
    have hw := ConcreteCategory.congr_hom a.isPushout.w z
    exact hx ⟨a.g₁ z, hw⟩
  have hh := TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout a.isPushout hU hr hl
  have hpoint (x : {x : B // x ∉ Set.range i.hom}) : a.cofan₂.inj k x.1 ∈ a.g₂ ⁻¹' U := by
    have hnot : a.cofan₂.inj k x.1 ∉ Set.range a.m.hom := by
      intro h
      exact x.2 ((mem_range_m_iff a k x.1).mp h)
    intro h
    rcases h with ⟨z, hz⟩
    have hne := Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit
      (a.isPushout.map (forget TopCat)).isColimit (z := z)
      (x := a.cofan₂.inj k x.1) hnot
    exact hne hz
  let ψ : {x : B // x ∉ Set.range i.hom} → a.g₂ ⁻¹' U :=
    fun x => ⟨a.cofan₂.inj k x.1, hpoint x⟩
  have hψ : IsEmbedding ψ :=
    ((cofan_inj_isEmbedding B a.cofan₂ a.isColimit₂ k).comp IsEmbedding.subtypeVal).codRestrict
      _ hpoint
  exact IsEmbedding.subtypeVal.comp (hh.isEmbedding.comp hψ)

private theorem realizedCellInterior_isEmbedding (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    IsEmbedding (fun x : {x : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom} =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s.1) x.1) := by
  let i := (⊥ : T.Subcomplex).ι
  let c := SSet.realizationRelativeCellComplexOfMono i
  let a := c.attachCells n (by simp)
  let k : SSet.relativeCellComplexOfMono.Cell i n :=
    { simplex := s.1, nonDegenerate := s.2, notMem := by simp [i] }
  have hf : IsClosed (Set.range (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)).hom) :=
    (SSet.closedT1Embeddings_toTop_map_of_mono
      (SSet.relativeCellComplexOfMono.r i n)).isClosed_range
  have h₁ := attachInterior_isEmbedding a hf k
  let j := (SSet.skeletonOfMono i (n + 1)).ι
  have hj : IsEmbedding (SSet.toTop.map j).hom :=
    (SSet.closedT1Embeddings_toTop_map_of_mono j).isEmbedding
  have h₂ := hj.comp h₁
  have hw : a.cell k ≫ SSet.toTop.map j = SSet.toTop.map k.map := by
    change SSet.toTop.map k.ιSigmaStdSimplex ≫
      SSet.toTop.map (SSet.relativeCellComplexOfMono.b i n) ≫ SSet.toTop.map j = _
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
    exact congrArg SSet.toTop.map (SSet.relativeCellComplexOfMono.Cell.ι_b_ι k)
  have heq : (fun x : {x : SSet.toTop.obj (Δ[n] : SSet.{u}) //
        x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom} =>
        SSet.toTop.map j (a.cell k x.1)) =
      (fun x => SSet.toTop.map (SSet.yonedaEquiv.symm s.1) x.1) := by
    funext x
    exact ConcreteCategory.congr_hom hw x.1
  change IsEmbedding (fun x : {x : SSet.toTop.obj (Δ[n] : SSet.{u}) //
    x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom} =>
      SSet.toTop.map j (a.cell k x.1)) at h₂
  rw [heq] at h₂
  exact h₂


end Stages

private def openBallToClosedBall (n : ℕ) :
    C(Metric.ball (0 : Fin n → ℝ) 1, Metric.closedBall (0 : Fin n → ℝ) 1) where
  toFun x := ⟨x.1, Metric.ball_subset_closedBall x.2⟩
  continuous_toFun := by fun_prop

private def inverseOnOpen (n : ℕ) : Metric.ball (0 : Fin n → ℝ) 1 →
    {x : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom} :=
  fun x => ⟨(stdPiDiskHomeomorph n).symm (openBallToClosedBall n x),
    (stdPiDiskHomeomorph_ball_iff n _).mp (by
      rw [Homeomorph.apply_symm_apply]
      exact x.2)⟩

private theorem inverseOnOpen_isEmbedding (n : ℕ) : IsEmbedding (inverseOnOpen.{u} n) := by
  have hi : IsEmbedding (openBallToClosedBall n) :=
    IsEmbedding.subtypeVal.codRestrict _ (fun x => Metric.ball_subset_closedBall x.2)
  have h := (stdPiDiskHomeomorph.{u} n).symm.isEmbedding.comp hi
  exact h.codRestrict _ (fun x => (inverseOnOpen n x).2)

private def closedCellMap (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    C(Metric.closedBall (0 : Fin n → ℝ) 1, SSet.toTop.obj T) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm s.1)).hom.comp
    { toFun := (stdPiDiskHomeomorph n).symm,
      continuous_toFun := (stdPiDiskHomeomorph n).symm.continuous }

private def openCellMap (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    C(Metric.ball (0 : Fin n → ℝ) 1, SSet.toTop.obj T) :=
  (closedCellMap T s).comp (openBallToClosedBall n)

private theorem openCellMap_isEmbedding (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    IsEmbedding (openCellMap T s) := by
  change IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
    SSet.toTop.map (SSet.yonedaEquiv.symm s.1)
      ((stdPiDiskHomeomorph n).symm (openBallToClosedBall n x)))
  exact (Stages.realizedCellInterior_isEmbedding T s).comp (inverseOnOpen_isEmbedding n)

private def cellMapTotal (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (x : Fin n → ℝ) : SSet.toTop.obj T :=
  closedCellMap T s (if hx : x ∈ Metric.closedBall 0 1 then ⟨x, hx⟩ else ⟨0, by simp⟩)

private theorem cellMapTotal_apply_of_mem (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (x : Fin n → ℝ) (hx : x ∈ Metric.closedBall 0 1) :
    cellMapTotal T s x = closedCellMap T s ⟨x, hx⟩ := by
  simp only [cellMapTotal, hx, ↓reduceDIte]

private theorem cellMapTotal_apply_of_ball (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (x : Fin n → ℝ) (hx : x ∈ Metric.ball 0 1) :
    cellMapTotal T s x = openCellMap T s ⟨x, hx⟩ :=
  cellMapTotal_apply_of_mem T s x (Metric.ball_subset_closedBall hx)

private def cellInverse (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (y : SSet.toTop.obj T) : Fin n → ℝ :=
  if hy : y ∈ Set.range (openCellMap T s) then
    ((openCellMap_isEmbedding T s).toHomeomorph.symm ⟨y, hy⟩).1 else 0

private def cellPartialEquiv (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    PartialEquiv (Fin n → ℝ) (SSet.toTop.obj T) where
  toFun := cellMapTotal T s
  invFun := cellInverse T s
  source := Metric.ball 0 1
  target := Set.range (openCellMap T s)
  map_source' {x} hx := ⟨⟨x, hx⟩, (cellMapTotal_apply_of_ball T s x hx).symm⟩
  map_target' {y} hy := by
    simp only [cellInverse, hy, ↓reduceDIte]
    exact ((openCellMap_isEmbedding T s).toHomeomorph.symm ⟨y, hy⟩).2
  left_inv' {x} hx := by
    rw [cellMapTotal_apply_of_ball T s x hx]
    simp only [cellInverse, Set.mem_range_self, ↓reduceDIte]
    exact congrArg Subtype.val
      ((openCellMap_isEmbedding T s).toHomeomorph.symm_apply_apply ⟨x, hx⟩)
  right_inv' {y} hy := by
    simp only [cellInverse, hy, ↓reduceDIte]
    rw [cellMapTotal_apply_of_ball T s _
      ((openCellMap_isEmbedding T s).toHomeomorph.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val
      ((openCellMap_isEmbedding T s).toHomeomorph.apply_symm_apply ⟨y, hy⟩)

private theorem cellPartialEquiv_source_eq (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    (cellPartialEquiv T s).source = Metric.ball 0 1 := rfl

private theorem cellPartialEquiv_continuousOn (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    ContinuousOn (cellPartialEquiv T s) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : (Metric.closedBall 0 1).domRestrict (cellPartialEquiv T s) = closedCellMap T s := by
    funext x
    exact cellMapTotal_apply_of_mem T s x.1 x.2
  rw [h]
  exact (closedCellMap T s).continuous

private theorem cellPartialEquiv_continuousOn_symm (T : SSet.{u}) {n : ℕ}
    (s : T.nonDegenerate n) :
    ContinuousOn (cellPartialEquiv T s).symm (cellPartialEquiv T s).target := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous fun y : Set.range (openCellMap T s) => cellInverse T s y.1
  have h : (fun y : Set.range (openCellMap T s) => cellInverse T s y.1) =
      fun y => ((openCellMap_isEmbedding T s).toHomeomorph.symm y).1 := by
    funext y
    simp only [cellInverse, y.2, ↓reduceDIte]
  rw [h]
  exact continuous_subtype_val.comp (openCellMap_isEmbedding T s).toHomeomorph.symm.continuous

private theorem cellPartialEquiv_image_closedBall (T : SSet.{u}) {n : ℕ}
    (s : T.nonDegenerate n) :
    cellPartialEquiv T s '' Metric.closedBall 0 1 = Set.range (closedCellMap T s) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (cellMapTotal_apply_of_mem T s x hx).symm.trans hxy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, cellMapTotal_apply_of_mem T s x.1 x.2⟩

private theorem cellPartialEquiv_image_ball (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    cellPartialEquiv T s '' Metric.ball 0 1 = Set.range (openCellMap T s) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (cellMapTotal_apply_of_ball T s x hx).symm.trans hxy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, cellMapTotal_apply_of_ball T s x.1 x.2⟩

private theorem mem_closedCell_of_stdPoint (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s.1) x ∈
      cellPartialEquiv T s '' Metric.closedBall 0 1 := by
  let p := stdPiDiskHomeomorph n x
  refine ⟨p.1, p.2, ?_⟩
  change cellMapTotal T s p.1 = _
  rw [cellMapTotal_apply_of_mem T s p.1 p.2]
  change SSet.toTop.map (SSet.yonedaEquiv.symm s.1) ((stdPiDiskHomeomorph n).symm p) = _
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm s.1))
    ((stdPiDiskHomeomorph n).symm_apply_apply x)

private theorem cellPartialEquiv_union (T : SSet.{u}) :
    (⋃ (n : ℕ) (s : T.nonDegenerate n), cellPartialEquiv T s '' Metric.closedBall 0 1) =
      Set.univ := by
  ext x
  constructor
  · intro
    trivial
  · intro
    obtain ⟨n, s, hs, y, hy⟩ := SSet.exists_nonDegenerate_toTop_presentation T x
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨⟨s, hs⟩,
      hy ▸ mem_closedCell_of_stdPoint T ⟨s, hs⟩ y⟩⟩

private theorem cellPartialEquiv_closed (T : SSet.{u}) (A : Set (SSet.toTop.obj T))
    (hA : ∀ (n : ℕ) (s : T.nonDegenerate n),
      IsClosed (A ∩ cellPartialEquiv T s '' Metric.closedBall 0 1)) : IsClosed A := by
  apply (SSet.isQuotientMap_sigmaToTop T).isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  intro s
  let g : C(Convexity.StdSimplex ℝ (Fin (s.dim + 1)), SSet.toTop.obj T) :=
    (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.comp
      { toFun := (SimplexCategory.toTopHomeo ⦋s.dim⦌).symm,
        continuous_toFun := (SimplexCategory.toTopHomeo ⦋s.dim⦌).symm.continuous }
  have hg (x) : g x ∈ cellPartialEquiv T ⟨s.simplex, s.nonDegenerate⟩ '' Metric.closedBall 0 1 :=
    mem_closedCell_of_stdPoint T ⟨s.simplex, s.nonDegenerate⟩ _
  have h : g ⁻¹' A = g ⁻¹'
      (A ∩ cellPartialEquiv T ⟨s.simplex, s.nonDegenerate⟩ '' Metric.closedBall 0 1) := by
    ext x
    exact ⟨fun hx => ⟨hx, hg x⟩, fun hx => hx.1⟩
  change IsClosed (g ⁻¹' A)
  rw [h]
  exact (hA s.dim ⟨s.simplex, s.nonDegenerate⟩).preimage g.continuous

private theorem stdPoint_positive {n : ℕ}
    (x : SSet.toTop.obj (Δ[n] : SSet.{u}))
    (hx : x ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom) :
    ∀ i, 0 < ((SimplexCategory.toTopHomeo ⦋n⦌) x).weights i := by
  intro i
  have hnonneg := ((SimplexCategory.toTopHomeo ⦋n⦌) x).weights_nonneg i
  have hne : ((SimplexCategory.toTopHomeo ⦋n⦌) x).weights i ≠ 0 := by
    intro hzero
    apply hx
    simpa only [Homeomorph.symm_apply_apply] using
      SSet.mem_realizedBoundary_of_zeroCoord.{u} n ((SimplexCategory.toTopHomeo ⦋n⦌) x) i hzero
  exact lt_of_le_of_ne hnonneg hne.symm

private theorem sigmaNDMk_injective (T : SSet.{u}) :
    Function.Injective (fun x : Σ n, T.nonDegenerate n => SSet.N.mk x.2.1 x.2.2) := by
  rintro ⟨n, s⟩ ⟨m, t⟩ h
  have hd : n = m := congrArg (fun z : T.N => z.dim) h
  cases hd
  have hs : s.1 = t.1 := (SSet.S.ext_iff _ _).mp ((SSet.N.ext_iff _ _).mp h)
  cases Subtype.ext hs
  rfl

private theorem cellPartialEquiv_pairwiseDisjoint (T : SSet.{u}) :
    (Set.univ : Set (Σ n, T.nonDegenerate n)).PairwiseDisjoint
      (fun x => cellPartialEquiv T x.2 '' Metric.ball 0 1) := by
  intro s₁ _ s₂ _ hne
  change Disjoint (cellPartialEquiv T s₁.2 '' Metric.ball 0 1)
    (cellPartialEquiv T s₂.2 '' Metric.ball 0 1)
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rw [cellPartialEquiv_image_ball] at hx₁ hx₂
  rcases hx₁ with ⟨p, hp⟩
  rcases hx₂ with ⟨q, hq⟩
  let y₁ := (stdPiDiskHomeomorph s₁.1).symm (openBallToClosedBall s₁.1 p)
  let y₂ := (stdPiDiskHomeomorph s₂.1).symm (openBallToClosedBall s₂.1 q)
  have hy₁ : y₁ ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} s₁.1).ι).hom :=
    (inverseOnOpen s₁.1 p).2
  have hy₂ : y₂ ∉ Set.range (SSet.toTop.map (SSet.boundary.{u} s₂.1).ι).hom :=
    (inverseOnOpen s₂.1 q).2
  have heq : SSet.sigmaToTop T
      ⟨SSet.N.mk s₁.2.1 s₁.2.2, (SimplexCategory.toTopHomeo ⦋s₁.1⦌) y₁⟩ =
      SSet.sigmaToTop T
        ⟨SSet.N.mk s₂.2.1 s₂.2.2, (SimplexCategory.toTopHomeo ⦋s₂.1⦌) y₂⟩ := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s₁.2.1)
        ((SimplexCategory.toTopHomeo ⦋s₁.1⦌).symm ((SimplexCategory.toTopHomeo ⦋s₁.1⦌) y₁)) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s₂.2.1)
        ((SimplexCategory.toTopHomeo ⦋s₂.1⦌).symm ((SimplexCategory.toTopHomeo ⦋s₂.1⦌) y₂))
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    exact hp.trans hq.symm
  have h := SSet.carrier_eq_of_sigmaToTop_eq_of_interior T _ _ _ _
    (stdPoint_positive y₁ hy₁) (stdPoint_positive y₂ hy₂) heq
  exact hne (sigmaNDMk_injective T h)

private abbrev boundaryImage (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) : T.Subcomplex :=
  SSet.Subcomplex.range ((SSet.boundary.{u} n).ι ≫ SSet.yonedaEquiv.symm s.1)

private def boundaryCellIndices (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) (m : ℕ) :
    Finset (T.nonDegenerate m) := by
  let _ := Fintype.ofFinite ((boundaryImage T s).toSSet.nonDegenerate m)
  exact Finset.univ.image (fun q : (boundaryImage T s).toSSet.nonDegenerate m =>
    (⟨q.1.1, (SSet.Subcomplex.mem_nonDegenerate_iff
      (boundaryImage T s) q.1).mp q.2⟩ : T.nonDegenerate m))

private theorem mem_boundaryImage_of_sphere (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n)
    (x : Fin n → ℝ) (hx : x ∈ Metric.sphere 0 1) :
    cellPartialEquiv T s x ∈ Set.range
      (SSet.toTop.map ((SSet.boundary.{u} n).ι ≫ SSet.yonedaEquiv.symm s.1)).hom := by
  let p : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x, Metric.sphere_subset_closedBall hx⟩
  have hp : (stdPiDiskHomeomorph n).symm p ∈
      Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
    (stdPiDiskHomeomorph_boundary_iff n _).mpr (by
      rw [Homeomorph.apply_symm_apply]
      exact hx)
  rcases hp with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [SSet.toTop.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm s.1)
      (SSet.toTop.map (SSet.boundary.{u} n).ι y) = cellMapTotal T s x
  rw [hy, cellMapTotal_apply_of_mem T s x (Metric.sphere_subset_closedBall hx)]
  rfl

private theorem cellPartialEquiv_mapsTo (T : SSet.{u}) {n : ℕ} (s : T.nonDegenerate n) :
    Set.MapsTo (cellPartialEquiv T s) (Metric.sphere 0 1)
      (⋃ (m < n) (q ∈ boundaryCellIndices T s m),
        cellPartialEquiv T q '' Metric.closedBall 0 1) := by
  intro x hx
  have h := mem_boundaryImage_of_sphere T s x hx
  rw [SSet.range_toTop_map_eq_range_toTop_map_range_ι] at h
  rcases h with ⟨b, hb⟩
  obtain ⟨m, t, ht, z, hz⟩ :=
    SSet.exists_nonDegenerate_toTop_presentation (boundaryImage T s).toSSet b
  have hm : m < n := SSet.dim_lt_of_nonDegenerate (X := (boundaryImage T s).toSSet) ⟨t, ht⟩ n
  let q : T.nonDegenerate m :=
    ⟨t.1, (SSet.Subcomplex.mem_nonDegenerate_iff (boundaryImage T s) t).mp ht⟩
  let _ := Fintype.ofFinite ((boundaryImage T s).toSSet.nonDegenerate m)
  have hq : q ∈ boundaryCellIndices T s m := by
    change q ∈ Finset.univ.image _
    exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩
  have hY : SSet.yonedaEquiv.symm t ≫ (boundaryImage T s).ι = SSet.yonedaEquiv.symm q.1 := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hpoint : SSet.toTop.map (SSet.yonedaEquiv.symm q.1) z = cellPartialEquiv T s x := by
    rw [← hY, SSet.toTop.map_comp]
    change SSet.toTop.map (boundaryImage T s).ι
      (SSet.toTop.map (SSet.yonedaEquiv.symm t) z) = _
    rw [hz]
    exact hb
  have hmem : cellPartialEquiv T s x ∈ cellPartialEquiv T q '' Metric.closedBall 0 1 := by
    rw [← hpoint]
    exact mem_closedCell_of_stdPoint T q z
  simp only [Set.mem_iUnion]
  exact ⟨m, hm, q, hq, hmem⟩

end realizationClassical

/-- Classical CW data on the actual realization, with its nondegenerate characteristic cells. -/
@[instance_reducible]
def realizationClassicalCWComplex (T : SSet.{u}) :
    Topology.CWComplex (Set.univ : Set (SSet.toTop.obj T)) where
  cell n := T.nonDegenerate n
  map _ s := realizationClassical.cellPartialEquiv T s
  source_eq _ s := realizationClassical.cellPartialEquiv_source_eq T s
  continuousOn _ s := realizationClassical.cellPartialEquiv_continuousOn T s
  continuousOn_symm _ s := realizationClassical.cellPartialEquiv_continuousOn_symm T s
  pairwiseDisjoint' := realizationClassical.cellPartialEquiv_pairwiseDisjoint T
  mapsTo' _ s :=
    ⟨realizationClassical.boundaryCellIndices T s, realizationClassical.cellPartialEquiv_mapsTo T s⟩
  closed' A _ h := realizationClassical.cellPartialEquiv_closed T A h
  union' := realizationClassical.cellPartialEquiv_union T

/-- The actual geometric realization has the classical characteristic-map CW structure. -/
noncomputable instance instCWComplexToTop (T : SSet.{u}) :
    Topology.CWComplex (Set.univ : Set (toTop.obj T)) :=
  realizationClassicalCWComplex T

/-- The specified realized vertex is an actual zero cell of the classical CW structure. -/
theorem realizedVertex_is_classical_zeroCell {T : SSet.{u}} (v : T _⦋0⦌) :
    ∃ j : Topology.CWComplex.cell (Set.univ : Set (toTop.obj T)) 0,
      ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = realizedVertex v := by
  change ∃ j : T.nonDegenerate 0,
    ∀ x : Fin 0 → ℝ, realizationClassical.cellPartialEquiv T j x = realizedVertex v
  refine ⟨⟨v, by simp⟩, ?_⟩
  intro x
  change realizationClassical.cellMapTotal T ⟨v, by simp⟩ x = realizedVertex v
  have hx : x ∈ Metric.closedBall 0 1 := by
    have h : x = 0 := Subsingleton.elim _ _
    rw [h]
    simp
  rw [realizationClassical.cellMapTotal_apply_of_mem T ⟨v, by simp⟩ x hx]
  change toTop.map (yonedaEquiv.symm v)
    ((realizationClassical.stdPiDiskHomeomorph 0).symm ⟨x, hx⟩) = realizedVertex v
  unfold realizedVertex
  congr 1
  exact Subsingleton.elim _ _

end SSet

end

public section

noncomputable section

universe u

open scoped Simplicial

namespace SSet.stdSimplex

/-- The actual realized standard simplex has the chosen classical max-norm
disk identification used by its existing characteristic cells. -/
def toClassicalDiskHomeomorph (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ
      Metric.closedBall (0 : Fin n → ℝ) 1 :=
  SSet.realizationClassical.stdPiDiskHomeomorph.{u} n

/-- The actual realized simplex-boundary image is exactly the literal
classical sphere under the unchanged chosen disk identification. -/
theorem toClassicalDiskHomeomorph_boundary_iff (n : ℕ)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
      (toClassicalDiskHomeomorph.{u} n x).val ∈
        Metric.sphere (0 : Fin n → ℝ) 1 :=
  SSet.realizationClassical.stdPiDiskHomeomorph_boundary_iff.{u} n x

end SSet.stdSimplex

end

/- Proposed insertion in the existing CWComplex owner. All helpers stay
private in that SAME module, using its actual canonical characteristic maps.
The sole public constructor has no supplied CW, subcomplex or inverse input. -/

public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SSet

namespace realizationClassical

private theorem classicalMonoClosedDiskLaw {T U : SSet.{u}} (i : T ⟶ U) [Mono i]
    {n : ℕ} (j : T.nonDegenerate n) (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    SSet.toTop.map i (cellPartialEquiv T j x.val) =
      cellPartialEquiv U (SSet.nonDegenerateEmbeddingOfMono i n j) x.val := by
  change SSet.toTop.map i (cellMapTotal T j x.val) =
    cellMapTotal U (SSet.nonDegenerateEmbeddingOfMono i n j) x.val
  rw [cellMapTotal_apply_of_mem T j x.val x.property,
    cellMapTotal_apply_of_mem U (SSet.nonDegenerateEmbeddingOfMono i n j) x.val x.property]
  have hmap : SSet.yonedaEquiv.symm j.val ≫ i =
      SSet.yonedaEquiv.symm (SSet.nonDegenerateEmbeddingOfMono i n j).val := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp only [SSet.nonDegenerateEmbeddingOfMono_apply]
  change SSet.toTop.map i
      (SSet.toTop.map (SSet.yonedaEquiv.symm j.val) ((stdPiDiskHomeomorph n).symm x)) =
    SSet.toTop.map (SSet.yonedaEquiv.symm (SSet.nonDegenerateEmbeddingOfMono i n j).val)
      ((stdPiDiskHomeomorph n).symm x)
  rw [← hmap, SSet.toTop.map_comp]
  rfl

private theorem classicalMonoOpenCellImage {T U : SSet.{u}} (i : T ⟶ U) [Mono i]
    (n : ℕ) (j : T.nonDegenerate n) :
    (SSet.toTop.map i).hom ''
        Topology.CWComplex.openCell (C := (Set.univ : Set (SSet.toTop.obj T))) n j =
      Topology.CWComplex.openCell (C := (Set.univ : Set (SSet.toTop.obj U))) n
        (SSet.nonDegenerateEmbeddingOfMono i n j) := by
  change (SSet.toTop.map i).hom '' (cellPartialEquiv T j '' Metric.ball (0 : Fin n → ℝ) 1) =
    cellPartialEquiv U (SSet.nonDegenerateEmbeddingOfMono i n j) '' Metric.ball (0 : Fin n → ℝ) 1
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (classicalMonoClosedDiskLaw i j
      ⟨x, Metric.ball_subset_closedBall hx⟩).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨cellPartialEquiv T j x, ⟨x, hx, rfl⟩,
      classicalMonoClosedDiskLaw i j ⟨x, Metric.ball_subset_closedBall hx⟩⟩

private def classicalMonoSubcomplex {T U : SSet.{u}} (i : T ⟶ U) [Mono i] :
    Topology.CWComplex.Subcomplex (Set.univ : Set (SSet.toTop.obj U)) where
  carrier := Set.range (SSet.toTop.map i).hom
  I n := Set.range (SSet.nonDegenerateEmbeddingOfMono i n)
  closed' := (SSet.closedT1Embeddings_toTop_map_of_mono i).isClosed_range
  union' := by
    rw [Set.empty_union]
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨j, hj⟩
      rcases j.property with ⟨k, hk⟩
      have h : z ∈ Topology.CWComplex.openCell
          (C := (Set.univ : Set (SSet.toTop.obj U))) n
            (SSet.nonDegenerateEmbeddingOfMono i n k) := by
        rw [hk]
        exact hj
      rw [← classicalMonoOpenCellImage i n k] at h
      rcases h with ⟨x, _, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ (n : ℕ)
          (j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n),
          Topology.CWComplex.openCell (C := (Set.univ : Set (SSet.toTop.obj T))) n j := by
        have hcover :
            (⋃ (n : ℕ) (j : T.nonDegenerate n),
              Topology.CWComplex.openCell
                (C := (Set.univ : Set (SSet.toTop.obj T))) n j) = Set.univ :=
          Topology.CWComplex.iUnion_openCell_eq_complex
            (C := (Set.univ : Set (SSet.toTop.obj T)))
        exact hcover.symm ▸ Set.mem_univ x
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨j, hj⟩
      have htarget : SSet.toTop.map i x ∈
          Topology.CWComplex.openCell (C := (Set.univ : Set (SSet.toTop.obj U))) n
            (SSet.nonDegenerateEmbeddingOfMono i n j) := by
        rw [← classicalMonoOpenCellImage i n j]
        exact ⟨x, hj, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨⟨SSet.nonDegenerateEmbeddingOfMono i n j, ⟨j, rfl⟩⟩, htarget⟩⟩

end realizationClassical

/-- A realized simplicial monomorphism is a classical closed subcomplex of
the actual canonical realization CW structure. The constructed cell labels
are dimension preserving and the original realized map intertwines their
entire original closed-disk characteristic maps. -/
def realizationClassicalCWSubcomplexOfMono {T U : SSet.{u}} (i : T ⟶ U) [Mono i] :
    Σ κ : ∀ n,
      Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n ↪
        Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj U)) n,
      {A : Topology.CWComplex.Subcomplex (Set.univ : Set (SSet.toTop.obj U)) //
        (A : Set (SSet.toTop.obj U)) = Set.range (SSet.toTop.map i).hom ∧
        (∀ n, A.I n = Set.range (κ n)) ∧
        ∀ (n : ℕ)
          (j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n)
          (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
          SSet.toTop.map i
              (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj T))) n j x.down.val) =
            Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj U)))
              n (κ n j) x.down.val} := by
  refine ⟨SSet.nonDegenerateEmbeddingOfMono i,
    ⟨realizationClassical.classicalMonoSubcomplex i, rfl, ?_, ?_⟩⟩
  · intro n
    rfl
  · intro n j x
    exact realizationClassical.classicalMonoClosedDiskLaw i j x.down

/-- The canonical whole characteristic-disk maps commute with the original
realized monomorphism and the constructed dimension-preserving cell labels. -/
theorem realizationClassicalCWSubcomplexOfMono_characteristicDiskMap
    {T U : SSet.{u}} (i : T ⟶ U) [Mono i] (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n) :
    Topology.CWComplex.characteristicDiskMap
        (X := SSet.toTop.obj T) n j ≫ SSet.toTop.map i =
      Topology.CWComplex.characteristicDiskMap
        (X := SSet.toTop.obj U) n
        ((realizationClassicalCWSubcomplexOfMono i).fst n j) := by
  ext x
  simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
    (realizationClassicalCWSubcomplexOfMono i).snd.property.2.2 n j x

end SSet

end

public section

noncomputable section

universe u

namespace SSet

/-- The actual degree-n classical realization cells are indexed by the
actual nondegenerate degree-n simplices of the same simplicial set. -/
def realizationClassicalCWCellEquivNonDegenerate (T : SSet.{u}) (n : ℕ) :
    Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n ≃ T.nonDegenerate n := by
  change T.nonDegenerate n ≃ T.nonDegenerate n
  exact Equiv.refl _

end SSet

end

/-!
## Matched classical disk-boundary coordinates
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open scoped Simplicial

namespace SSet.classicalCellDiskBoundary

private theorem realizedBoundary_closed (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι) :=
  TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.closedT1Embeddings_toTop_map_of_mono (SSet.boundary.{u} n).ι)

private def simplexDiskHomeomorph (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ (classicalCellDiskPair.{u} n).fst :=
  (SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n).trans Homeomorph.ulift.symm

private theorem simplexDiskHomeomorph_boundary_range (n : ℕ)
    (z : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    z ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι) ↔
      simplexDiskHomeomorph n z ∈ Set.range (classicalCellDiskPair.{u} n).map := by
  rw [SSet.stdSimplex.toClassicalDiskHomeomorph_boundary_iff]
  change (SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n z).val ∈
      Metric.sphere (0 : Fin n → ℝ) 1 ↔
    ULift.up (SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n z) ∈
      Set.range (classicalCellDiskPair.{u} n).map
  constructor
  · intro hz
    refine ⟨ULift.up ⟨(SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n z).val, hz⟩, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    rfl
  · rintro ⟨a, ha⟩
    have hval := congrArg (fun q : (classicalCellDiskPair.{u} n).fst => q.down.val) ha
    exact hval ▸ a.down.property

private def simplexBoundaryHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n).toSSet ≃ₜ (classicalCellDiskPair.{u} n).snd :=
  (realizedBoundary_closed n).isEmbedding.toHomeomorph.trans
    (((simplexDiskHomeomorph n).subtype
      (simplexDiskHomeomorph_boundary_range n)).trans
        (isClosedEmbedding_classicalCellDiskPair_map (n := n)).isEmbedding.toHomeomorph.symm)

private theorem simplexBoundaryHomeomorph_comm (n : ℕ)
    (z : SSet.toTop.obj (SSet.boundary.{u} n).toSSet) :
    (classicalCellDiskPair.{u} n).map (simplexBoundaryHomeomorph n z) =
      simplexDiskHomeomorph n (SSet.toTop.map (SSet.boundary.{u} n).ι z) := by
  let hD := simplexDiskHomeomorph n
  let hb := (realizedBoundary_closed n).isEmbedding
  let hj := (isClosedEmbedding_classicalCellDiskPair_map (n := n)).isEmbedding
  let z' : Set.range (classicalCellDiskPair.{u} n).map :=
    (hD.subtype (simplexDiskHomeomorph_boundary_range n)) (hb.toHomeomorph z)
  change (classicalCellDiskPair.{u} n).map (hj.toHomeomorph.symm z') =
    hD (SSet.toTop.map (SSet.boundary.{u} n).ι z)
  exact congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply z')

private theorem simplexBoundaryHomeomorph_inv_comm (n : ℕ)
    (z : (classicalCellDiskPair.{u} n).snd) :
    SSet.toTop.map (SSet.boundary.{u} n).ι ((simplexBoundaryHomeomorph n).symm z) =
      (simplexDiskHomeomorph n).symm ((classicalCellDiskPair.{u} n).map z) := by
  apply (simplexDiskHomeomorph n).injective
  rw [(simplexDiskHomeomorph n).apply_symm_apply]
  have h := simplexBoundaryHomeomorph_comm n ((simplexBoundaryHomeomorph n).symm z)
  rw [(simplexBoundaryHomeomorph n).apply_symm_apply] at h
  exact h.symm

end SSet.classicalCellDiskBoundary

/-- The exact classical disk identification used for the whole realized standard simplex. -/
public def SSet.stdSimplex.toClassicalCellDiskIso (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≅ (classicalCellDiskPair.{u} n).fst :=
  TopCat.isoOfHomeo (SSet.classicalCellDiskBoundary.simplexDiskHomeomorph n)

/-- The matching classical boundary identification, restricted from the same disk map. -/
public def SSet.boundary.toClassicalCellBoundaryIso (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n).toSSet ≅ (classicalCellDiskPair.{u} n).snd :=
  TopCat.isoOfHomeo (SSet.classicalCellDiskBoundary.simplexBoundaryHomeomorph n)

/-- The exact chosen disk and boundary maps intertwine the whole boundary inclusion. -/
public theorem SSet.boundary.toClassicalCellDiskIso_comm (n : ℕ) :
    SSet.toTop.map (SSet.boundary.{u} n).ι ≫ (SSet.stdSimplex.toClassicalCellDiskIso n).hom =
      (SSet.boundary.toClassicalCellBoundaryIso n).hom ≫ (classicalCellDiskPair.{u} n).map := by
  apply TopCat.ext
  intro z
  exact (SSet.classicalCellDiskBoundary.simplexBoundaryHomeomorph_comm n z).symm

/-- Their inverse maps retain the same boundary equation on every classical boundary point. -/
public theorem SSet.boundary.toClassicalCellDiskIso_inv_comm (n : ℕ) :
    (SSet.boundary.toClassicalCellBoundaryIso n).inv ≫ SSet.toTop.map (SSet.boundary.{u} n).ι =
      (classicalCellDiskPair.{u} n).map ≫ (SSet.stdSimplex.toClassicalCellDiskIso n).inv := by
  apply TopCat.ext
  intro z
  exact SSet.classicalCellDiskBoundary.simplexBoundaryHomeomorph_inv_comm n z

/-- The actual matched classical disk-boundary Arrow Iso, with the unchanged disk
parametrization. -/
public def SSet.boundary.toClassicalCellDiskArrowIso (n : ℕ) :
    Arrow.mk (SSet.toTop.map (SSet.boundary.{u} n).ι) ≅
      Arrow.mk (classicalCellDiskPair.{u} n).map :=
  Arrow.isoMk' _ _ (SSet.boundary.toClassicalCellBoundaryIso n)
    (SSet.stdSimplex.toClassicalCellDiskIso n) (SSet.boundary.toClassicalCellDiskIso_comm n).symm

/-- Its boundary component is the same restriction of the chosen disk map. -/
public theorem SSet.boundary.toClassicalCellDiskArrowIso_hom_left (n : ℕ) :
    (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).hom.left =
      (SSet.boundary.toClassicalCellBoundaryIso n).hom := by
  rfl

/-- Its disk component is the same chosen classical disk map. -/
public theorem SSet.boundary.toClassicalCellDiskArrowIso_hom_right (n : ℕ) :
    (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).hom.right =
      (SSet.stdSimplex.toClassicalCellDiskIso n).hom := by
  rfl

/-- The inverse boundary component is the same inverse restriction. -/
public theorem SSet.boundary.toClassicalCellDiskArrowIso_inv_left (n : ℕ) :
    (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).inv.left =
      (SSet.boundary.toClassicalCellBoundaryIso n).inv := by
  rfl

/-- The inverse disk component is the same inverse disk map. -/
public theorem SSet.boundary.toClassicalCellDiskArrowIso_inv_right (n : ℕ) :
    (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).inv.right =
      (SSet.stdSimplex.toClassicalCellDiskIso n).inv := by
  rfl

/-- Every point retains the existing classical disk homeomorphism followed by its literal lift. -/
public theorem SSet.boundary.toClassicalCellDiskArrowIso_hom_right_apply (n : ℕ)
    (z : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (SSet.boundary.toClassicalCellDiskArrowIso.{u} n).hom.right z =
      ULift.up (SSet.stdSimplex.toClassicalDiskHomeomorph.{u} n z) := by
  rfl

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.ClassicalCellAttachments
public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization
public import Mathlib.Topology.Homotopy.Basic

/-!
# The actual common zero skeleton

The polyhedron is the existing bottom abstract simplicial complex on ALL actual
classical zero-cell identifiers. Its weak realization is identified with the
original strict-bound-one skeleton by the original dimension-zero characteristic
attachment quotient. Empty and infinite zero-cell sets are permitted.

The common initial space is the original zero skeleton, with both end images
identified with the whole space. The two returned homotopies are stationary
relative to that entire actual space. No common successor or global retraction
is supplied or asserted here. This construction supplies the initial common stage.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology Set Function
open scoped unitInterval

universe u

namespace CommonZeroSkeletonConstruction

private abbrev discretePolyhedron (J : Type u) : PreAbstractSimplicialComplex J :=
  (⊥ : AbstractSimplicialComplex J).toPreAbstractSimplicialComplex

private theorem discrete_singleton (J : Type u) (j : J) :
    {j} ∈ discretePolyhedron J :=
  (⊥ : AbstractSimplicialComplex J).singleton_mem j

private def pointLabel {J : Type u} (x : (discretePolyhedron J).Realization) : J :=
  Classical.choose (show ∃ j, x.point.weights.support = {j} from x.support_mem)

private theorem pointLabel_support {J : Type u} (x : (discretePolyhedron J).Realization) :
    x.point.weights.support = {pointLabel x} :=
  Classical.choose_spec (show ∃ j, x.point.weights.support = {j} from x.support_mem)

private theorem point_eq_vertex {J : Type u} (x : (discretePolyhedron J).Realization) :
    x = PreAbstractSimplicialComplex.Realization.vertex (discretePolyhedron J)
      (pointLabel x) (discrete_singleton J (pointLabel x)) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  exact Convexity.StdSimplex.support_weights_eq_singleton.mp (pointLabel_support x)

private theorem pointLabel_vertex {J : Type u} (j : J) :
    pointLabel (PreAbstractSimplicialComplex.Realization.vertex (discretePolyhedron J)
      j (discrete_singleton J j)) = j := by
  apply Convexity.StdSimplex.single_injective (R := ℝ)
  exact (congrArg PreAbstractSimplicialComplex.Realization.point
    (point_eq_vertex (PreAbstractSimplicialComplex.Realization.vertex
      (discretePolyhedron J) j (discrete_singleton J j)))).symm

private theorem pointLabel_face {J : Type u}
    (s : PreAbstractSimplicialComplex.Face (discretePolyhedron J)) (j : J)
    (hs : s.val = {j}) (q : Convexity.StdSimplex ℝ s.val) :
    pointLabel
      (PreAbstractSimplicialComplex.Realization.faceMap (discretePolyhedron J) s q) = j := by
  have hsub := PreAbstractSimplicialComplex.Realization.support_map_subtype_subset s.val q
  have hlabel := pointLabel_support
    (PreAbstractSimplicialComplex.Realization.faceMap (discretePolyhedron J) s q)
  change (q.map (Subtype.val : s.val → J)).weights.support = _ at hlabel
  rw [hlabel, hs] at hsub
  exact Finset.mem_singleton.mp (hsub (Finset.mem_singleton_self _))

private def vertexHomeomorph (J : Type u) :
    letI : TopologicalSpace J := ⊥
    J ≃ₜ (discretePolyhedron J).Realization := by
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  refine
    { toFun j := PreAbstractSimplicialComplex.Realization.vertex
        (discretePolyhedron J) j (discrete_singleton J j)
      invFun := pointLabel
      left_inv := pointLabel_vertex
      right_inv := fun x => (point_eq_vertex x).symm
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := ?_ }
  rw [PreAbstractSimplicialComplex.Realization.continuous_iff]
  intro s
  obtain ⟨j, hj⟩ := (show ∃ j, s.val = {j} from s.property)
  have heq : (pointLabel ∘
      PreAbstractSimplicialComplex.Realization.faceMap (discretePolyhedron J) s) =
      fun _ => j := funext (pointLabel_face s j hj)
  rw [heq]
  exact continuous_const

private theorem realizationDiscrete (J : Type u) :
    DiscreteTopology (discretePolyhedron J).Realization := by
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  exact (vertexHomeomorph J).discreteTopology

private def zeroDisk : (Topology.CWComplex.classicalCellDiskPair.{u} 0).fst :=
  ULift.up ⟨0, by simp⟩

private theorem zeroDisk_eq
    (d : (Topology.CWComplex.classicalCellDiskPair.{u} 0).fst) :
    d = zeroDisk.{u} := by
  apply ULift.ext
  apply Subtype.ext
  exact Subsingleton.elim _ _

private theorem emptyZeroSkeleton (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    IsEmpty (Topology.CWComplex.skeletonTop X 0) :=
  ⟨fun x => by
    have hx := x.property
    change x.val ∈ (Topology.CWComplex.skeletonLT
      (Set.univ : Set X) (0 : ℕ∞) : Set X) at hx
    rw [Topology.CWComplex.skeletonLT_zero_eq_empty] at hx
    exact hx⟩

private def labelDiskHomeomorph (X : TopCat.{u})
    [Topology.CWComplex (Set.univ : Set X)] :
    letI : TopologicalSpace (Topology.CWComplex.cell (Set.univ : Set X) 0) := ⊥
    Topology.CWComplex.cell (Set.univ : Set X) 0 ≃ₜ
      Topology.CWComplex.CellDisksAt X 0 := by
  letI : TopologicalSpace (Topology.CWComplex.cell (Set.univ : Set X) 0) := ⊥
  letI : DiscreteTopology (Topology.CWComplex.cell (Set.univ : Set X) 0) := ⟨rfl⟩
  refine
    { toFun j := ⟨j, zeroDisk⟩
      invFun := Sigma.fst
      left_inv := fun _ => rfl
      right_inv := ?_
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_sigma (fun _ => continuous_const) }
  rintro ⟨j, d⟩
  have hd : d = zeroDisk := zeroDisk_eq d
  subst d
  rfl

/-- Descend the ORIGINAL attachment quotient after removing its empty old summand. -/
private theorem diskSum_quotient (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    IsQuotientMap (Topology.CWComplex.diskSumToSkeleton X 0) := by
  let := emptyZeroSkeleton X
  let fold : Topology.CWComplex.skeletonTop X 0 ⊕ Topology.CWComplex.CellDisksAt X 0 →
      Topology.CWComplex.CellDisksAt X 0 := Sum.elim (fun x => isEmptyElim x) id
  have hold : Continuous (fun x : Topology.CWComplex.skeletonTop X 0 =>
      (isEmptyElim x : Topology.CWComplex.CellDisksAt X 0)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact isEmptyElim x
  have hfold : Continuous fold := hold.sumElim continuous_id
  have heq : (Topology.CWComplex.diskSumToSkeleton X 0) ∘ fold =
      Topology.CWComplex.skeletonAttachmentQuotient X 0 := by
    funext z
    cases z with
    | inl x => exact isEmptyElim x
    | inr x => rfl
  apply IsQuotientMap.of_comp hfold (Topology.CWComplex.diskSumToSkeleton X 0).hom.continuous
  rw [heq]
  exact Topology.CWComplex.isQuotientMap_skeletonAttachmentQuotient X 0

private theorem diskSum_injective (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    Function.Injective (Topology.CWComplex.diskSumToSkeleton X 0) := by
  rintro ⟨j, d⟩ ⟨k, e⟩ h
  have hd : d = zeroDisk := zeroDisk_eq d
  have he : e = zeroDisk := zeroDisk_eq e
  subst d
  subst e
  have hp := congrArg Subtype.val h
  change Topology.CWComplex.map 0 j (0 : Fin 0 → ℝ) =
    Topology.CWComplex.map 0 k (0 : Fin 0 → ℝ) at hp
  have hjk : j = k := Topology.RelCWComplex.injective_map_zero
    (D := (∅ : Set X)) (Set.univ : Set X) (by
      change Topology.CWComplex.map 0 j ![] = Topology.CWComplex.map 0 k ![]
      simpa only [Matrix.zero_empty] using hp)
  subst k
  rfl

private def diskZeroHomeomorph (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    Topology.CWComplex.CellDisksAt X 0 ≃ₜ Topology.CWComplex.skeletonTop X 1 :=
  (Equiv.ofBijective (Topology.CWComplex.diskSumToSkeleton X 0)
    ⟨diskSum_injective X, (diskSum_quotient X).surjective⟩).toHomeomorphOfContinuousOpen
      (Topology.CWComplex.diskSumToSkeleton X 0).hom.continuous
      ((diskSum_quotient X).isCoinducing.isOpenMap_of_injective (diskSum_injective X))

private def polyhedralZeroHomeomorph (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    (discretePolyhedron (Topology.CWComplex.cell (Set.univ : Set X) 0)).Realization ≃ₜ
      Topology.CWComplex.skeletonTop X 1 := by
  letI : TopologicalSpace (Topology.CWComplex.cell (Set.univ : Set X) 0) := ⊥
  exact ((vertexHomeomorph (Topology.CWComplex.cell (Set.univ : Set X) 0)).symm.trans
    (labelDiskHomeomorph X)).trans (diskZeroHomeomorph X)

private theorem polyhedralZeroHomeomorph_vertex (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    (polyhedralZeroHomeomorph X (PreAbstractSimplicialComplex.Realization.vertex
      (discretePolyhedron (Topology.CWComplex.cell (Set.univ : Set X) 0)) j
      (discrete_singleton _ j))).val = Topology.CWComplex.map 0 j (0 : Fin 0 → ℝ) := by
  change (Topology.CWComplex.diskSumToSkeleton X 0
    ⟨pointLabel (PreAbstractSimplicialComplex.Realization.vertex
      (discretePolyhedron (Topology.CWComplex.cell (Set.univ : Set X) 0)) j
      (discrete_singleton _ j)), zeroDisk⟩).val = _
  rw [pointLabel_vertex]
  rfl

private theorem zeroSkeletonDiscrete (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    DiscreteTopology (Topology.CWComplex.skeletonTop X 1) := by
  let := realizationDiscrete (Topology.CWComplex.cell (Set.univ : Set X) 0)
  exact (polyhedralZeroHomeomorph X).discreteTopology

end CommonZeroSkeletonConstruction

public section

namespace Topology.CWComplex

/-- The actual zero-skeleton comparison, with both stationary initial retractions.
The zero-cell labels, weak polyhedron and original characteristic points are literal. -/
structure CommonZeroSkeletonData (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] where
  /-- The entire bottom-complex realization is the original strict-bound-one skeleton. -/
  homeomorph : ((⊥ : AbstractSimplicialComplex
      (cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex).Realization ≃ₜ
    skeletonTop X 1
  /-- The initial original-space retraction is relative to the entire zero skeleton. -/
  initialHomotopy : ContinuousMap.HomotopyRel (ContinuousMap.id (skeletonTop X 1))
    (ContinuousMap.id (skeletonTop X 1)) (Set.univ : Set (skeletonTop X 1))
  /-- The polyhedral-end retraction uses the actual comparison and its actual inverse. -/
  polyhedronHomotopy : ContinuousMap.HomotopyRel (ContinuousMap.id (skeletonTop X 1))
    ((homeomorph : C(((⊥ : AbstractSimplicialComplex
      (cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex).Realization,
      skeletonTop X 1)).comp
      (homeomorph.symm : C(skeletonTop X 1, ((⊥ : AbstractSimplicialComplex
        (cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex).Realization)))
    (Set.univ : Set (skeletonTop X 1))
  /-- Every actual vertex is its original characteristic zero-cell point. -/
  homeomorph_vertex (j : cell (Set.univ : Set X) 0) :
    (homeomorph (PreAbstractSimplicialComplex.Realization.vertex
      ((⊥ : AbstractSimplicialComplex
        (cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex) j
      ((⊥ : AbstractSimplicialComplex (cell (Set.univ : Set X) 0)).singleton_mem j))).val =
      map 0 j (0 : Fin 0 → ℝ)
  /-- The whole original-space family is stationary at every time and every point. -/
  initialHomotopy_stationary (t : unitInterval) (z : skeletonTop X 1) :
    initialHomotopy (t, z) = z
  /-- The whole polyhedral-end family is stationary at every time and every point. -/
  polyhedronHomotopy_stationary (t : unitInterval) (z : skeletonTop X 1) :
    polyhedronHomotopy (t, z) = z
  /-- A derived instance, usable locally as `letI := d.discreteTopology`. -/
  discreteTopology : DiscreteTopology (skeletonTop X 1)
  /-- Classical CW data on the original zero skeleton are a conclusion. -/
  nonempty_cwComplex : Nonempty (CWComplex (Set.univ : Set (skeletonTop X 1)))

namespace CommonZeroSkeletonData

variable {X : TopCat.{u}} [T2Space X] [CWComplex (Set.univ : Set X)]

/-- The comparison determines all returned data, since both families are stationary. -/
@[ext]
theorem ext {d e : CommonZeroSkeletonData X} (h : d.homeomorph = e.homeomorph) : d = e := by
  cases d with
  | mk dh dH₀ dH₁ dhv dh₀ dh₁ dd dc =>
    cases e with
    | mk eh eH₀ eH₁ ehv eh₀ eh₁ ed ec =>
      change dh = eh at h
      subst eh
      have h₀ : dH₀ = eH₀ := DFunLike.ext _ _ fun z =>
        (dh₀ z.1 z.2).trans (eh₀ z.1 z.2).symm
      have h₁ : dH₁ = eH₁ := DFunLike.ext _ _ fun z =>
        (dh₁ z.1 z.2).trans (eh₁ z.1 z.2).symm
      cases h₀
      cases h₁
      rfl

end CommonZeroSkeletonData

/-- Construct the literal polyhedron/zero-skeleton comparison and both stationary
initial common-space retractions, from the original CW characteristic quotient. -/
def commonZeroSkeleton (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    CommonZeroSkeletonData X := by
  let h := CommonZeroSkeletonConstruction.polyhedralZeroHomeomorph X
  let H₀ := ContinuousMap.HomotopyRel.refl (ContinuousMap.id (skeletonTop X 1))
    (Set.univ : Set (skeletonTop X 1))
  let H₁ := H₀.cast rfl (Homeomorph.toContinuousMap_comp_symm h).symm
  letI := CommonZeroSkeletonConstruction.zeroSkeletonDiscrete X
  exact
    { homeomorph := h
      initialHomotopy := H₀
      polyhedronHomotopy := H₁
      homeomorph_vertex := CommonZeroSkeletonConstruction.polyhedralZeroHomeomorph_vertex X
      initialHomotopy_stationary := fun t z => H₀.eq_fst t (Set.mem_univ z)
      polyhedronHomotopy_stationary := fun t z => H₁.eq_fst t (Set.mem_univ z)
      discreteTopology := inferInstance
      nonempty_cwComplex := ⟨inferInstance⟩ }

end Topology.CWComplex

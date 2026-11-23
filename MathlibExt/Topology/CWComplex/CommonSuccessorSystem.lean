/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.ClassicalCellAttachments
public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder
public import MathlibExt.AlgebraicTopology.SimplicialComplex.SphereTriangulation
public import MathlibExt.AlgebraicTopology.SimplicialComplex.SimplicialApproximation
public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization.ClassicalCellEmbedding
import MathlibExt.Topology.CWComplex.CommonZeroSkeleton
import MathlibExt.Topology.CWComplex.MatchedAmalgam
import MathlibExt.Topology.CWComplex.DiskCone
import MathlibExt.Topology.CWComplex.DiskCylinder
import MathlibExt.Topology.Category.TopPair.IntervalDiskPairIso
import MathlibExt.AlgebraicTopology.SimplicialComplex.FamilyMappingCylinder
import MathlibExt.Topology.Category.TopCat.QuotientPushout
import MathlibExt.Topology.Category.TopCat.BinaryClosedGlue
import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Sigma.Basic

/-!
# Actual finite common successor CW system

The original-X recursion and all private construction proofs are colocated
in this module. The three public declarations expose
the full constructed data; their types contain no private stage alias.
-/

noncomputable section

set_option autoImplicit false

open Topology CategoryTheory PreAbstractSimplicialComplex
open scoped Classical unitInterval

universe v w

namespace CommonSuccessorSmallCylinderConstruction

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder

variable {V : Type v} {W : Type w}
variable {P : PreAbstractSimplicialComplex V} {Q : PreAbstractSimplicialComplex W}

private theorem actualSphere_face_card_le (d : ℕ)
    (s : Face (SphereTriangulation.complex d)) :
    s.val.card ≤ d := by
  have hs : s.val.Nonempty ∧ s.val ≠ Finset.univ := s.property
  have hsub : s.val ⊆ (Finset.univ : Finset (Fin (d + 1))) := Finset.subset_univ _
  have hle : s.val.card ≤ d + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  have hne : s.val.card ≠ d + 1 := by
    intro h
    exact hs.2 (Finset.eq_of_subset_of_card_le hsub (by
      simpa only [Finset.card_univ, Fintype.card_fin, h] using le_refl (d + 1)))
  omega

/-- Every actual finite P2 subdivision of the sphere has the same derived
dimension bound; no uniform family bound is supplied as a premise. -/
private theorem actualSphere_subdivision_face_card_le (d r : ℕ)
    (s : Face (subdivisionIter (SphereTriangulation.complex d) r)) :
    s.val.card ≤ d :=
  card_subdivisionIter_face_le (SphereTriangulation.complex d) d
    (actualSphere_face_card_le d) r s

private def actualSphereSmallDeformation (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallCylinder f).Realization)
      ((smallOldTarget f).comp (smallRetraction f)) (Set.range (smallOldTarget f)) :=
  boundedSmallDeformation f d (actualSphere_subdivision_face_card_le d r)

/- Same-module fragment. The old target and copied barycentric domain keep
their actual labels and closed embeddings. The final copied-domain map is
the existing original simplicial map, including all folding multiplicities. -/

private theorem actualSphereSmallDeformation_old (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (t : unitInterval) (y : Q.Realization) :
    actualSphereSmallDeformation d r f (t, smallOldTarget f y) = smallOldTarget f y :=
  (actualSphereSmallDeformation d r f).eq_fst t (Set.mem_range_self y)

private theorem actualSphereSmallDeformation_copied_terminal (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (x : (barycentricSubdivision (subdivisionIter (SphereTriangulation.complex d) r)).Realization) :
    actualSphereSmallDeformation d r f (1, smallCopiedDomain f x) =
      smallOldTarget f
        (f.realization (barycentricHomeomorph (subdivisionIter (SphereTriangulation.complex d) r) x)) := by
  rw [(actualSphereSmallDeformation d r f).apply_one, ContinuousMap.comp_apply, smallRetraction_copied]

/- Same-module fragment. The associated cone uses the unchanged actual
copied domain and ordinary cone, including its retained apex when the
domain is empty. The actual ordinary pushout is derived from the weak
subcomplex intersection and the existing ordinary cone homeomorphism.
No cone retraction onto the old target is asserted. -/

private theorem actualSphere_small_mixed_face_card_le (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (s : Face (smallCylinder f)) (hc : s.val.toLeft.Nonempty) :
    s.val.card ≤ d + 1 :=
  small_mixed_face_card_le f d (actualSphere_subdivision_face_card_le d r) s hc

private theorem actualSphere_copiedCone_face_card_le (d r : ℕ)
    (s : Face (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W))) :
    s.val.card ≤ d + 1 :=
  copiedCone_face_card_le d (actualSphere_subdivision_face_card_le d r) s

private theorem actualSphere_small_cone_face_card_le (d r N : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (hQ : ∀ a : Face Q, a.val.card ≤ N) (s : Face (smallAssociatedCone f)) :
    s.val.card ≤ max (d + 1) N :=
  smallAssociatedCone_face_card_le f d N (actualSphere_subdivision_face_card_le d r) hQ s

/- Same-module fragment. A finite carrier for a whole face trajectory is
constructed directly from its original copied faces and their image hull.
This does not infer finite support for arbitrary compact subsets of a strong
metric realization, and it assumes no global finite target or countability. -/

private theorem actualSphereSmallDeformation_face_support (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (s : Face (smallCylinder f)) (t : unitInterval) (q : Convexity.StdSimplex ℝ s.val) :
    (actualSphereSmallDeformation d r f
      (t, Realization.faceMap (smallCylinder f) s q)).point.weights.support ⊆ controlHalo f s.val :=
  boundedSmallDeformation_support_in_controlHalo f d (actualSphere_subdivision_face_card_le d r)
    s.val t _ ((Realization.support_map_subtype_subset s.val q).trans (controlHalo_contains f s.val))

/- The smaller-cylinder family and its constructed cardinality-transfer
deformation retain the old target, copied domains, literal cones and apices,
ordinary family quotient topology and both pushout presentations.
No CW, contraction, inverse, chart or family-cardinality restriction is
assumed for this construction. -/

universe u


end CommonSuccessorSmallCylinderConstruction

end

/- Fresh family scope: the scalar V/P are closed, and the index name I
is kept free of the unitInterval notation. All time types remain explicit. -/



/-!
Private chart primitives for the actual matching-subcomplex CW
amalgam. Existing CW data are internal stage data; no conditional generic
theorem in this file replaces the X-only successor target. There is no new
public helper or instance. All matching amalgam CW fields are assembled below.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace RealizedMonoMatchedAmalgamApplication

open Topology.CWComplex.MatchedAmalgam

/- Actual realized monomorphism-span application. All matching data are
constructed from the canonical realization cell API. The full arbitrary
classical-CW common-stage construction retains its original hypotheses. -/

section ActualRealizedMonoSpan

private def realizedMonoMatching {S T U : SSet.{u}} (f : S ⟶ T) [Mono f] (g : S ⟶ U) [Mono g] :
    MatchingCharacteristicData (SSet.toTop.map f) (SSet.toTop.map g) where
  leftLabels := (SSet.realizationClassicalCWSubcomplexOfMono f).fst
  rightLabels := (SSet.realizationClassicalCWSubcomplexOfMono g).fst
  leftLaw n j x := (SSet.realizationClassicalCWSubcomplexOfMono f).snd.property.2.2 n j (ULift.up x)
  rightLaw n j x := (SSet.realizationClassicalCWSubcomplexOfMono g).snd.property.2.2 n j (ULift.up x)

private def realizedMonoSpanClassicalCW {S T U : SSet.{u}}
    (f : S ⟶ T) [Mono f] (g : S ⟶ U) [Mono g] :
    Topology.CWComplex (Set.univ : Set ((pushout (SSet.toTop.map f) (SSet.toTop.map g) : TopCat.{u}))) :=
  Topology.CWComplex.MatchedAmalgam.classicalCWComplex (realizedMonoMatching f g)
    (SSet.closedT1Embeddings_toTop_map_of_mono f).isClosedEmbedding
    (SSet.closedT1Embeddings_toTop_map_of_mono g).isClosedEmbedding

example {S T U : SSet.{u}} (f : S ⟶ T) [Mono f] (g : S ⟶ U) [Mono g] :
    Topology.CWComplex (Set.univ : Set ((pushout (SSet.toTop.map f) (SSet.toTop.map g) : TopCat.{u}))) :=
  realizedMonoSpanClassicalCW f g

example {S T U : SSet.{u}} (f : S ⟶ T) [Mono f] (g : S ⟶ U) [Mono g]
    (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj T)) n)
    (x : Fin n → ℝ) :
    letI := realizedMonoSpanClassicalCW f g
    Topology.CWComplex.map
        (C := (Set.univ : Set ((pushout (SSet.toTop.map f) (SSet.toTop.map g) : TopCat.{u})))) n (Sum.inl a) x =
      pushout.inl (SSet.toTop.map f) (SSet.toTop.map g)
        (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj T))) n a x) :=
  left_characteristic (realizedMonoMatching f g) _ _ n a x

example {S T U : SSet.{u}} (f : S ⟶ T) [Mono f] (g : S ⟶ U) [Mono g]
    (n : ℕ)
    (b : {b : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj U)) n //
      b ∉ Set.range ((SSet.realizationClassicalCWSubcomplexOfMono g).fst n)})
    (x : Fin n → ℝ) :
    letI := realizedMonoSpanClassicalCW f g
    Topology.CWComplex.map
        (C := (Set.univ : Set ((pushout (SSet.toTop.map f) (SSet.toTop.map g) : TopCat.{u})))) n (Sum.inr b) x =
      pushout.inr (SSet.toTop.map f) (SSet.toTop.map g)
        (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj U))) n b.val x) :=
  newRight_characteristic (realizedMonoMatching f g) _ _ n b x

end ActualRealizedMonoSpan


end RealizedMonoMatchedAmalgamApplication

end

/-!
# CW data on the actual original strict skeleton

The selected cells and their whole closed disks are the original characteristic
cells. A per-cell center defines the otherwise irrelevant value of a partial
equivalence outside that closed disk. No point of an empty skeleton is chosen.
The actual successor attachment square is the original characteristic pushout.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology Set Metric

universe u

namespace OriginalStrictSkeletonCWConstruction47

variable {X : TopCat.{u}} [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]

/-- The set/subtype comparison as partial data, with a supplied point used only
outside the set. The principal construction derives that point from each cell. -/
private def toSubtypePartial (A : Set X) (a : A) : PartialEquiv X A := by
  classical
  exact
    { toFun := fun x => if hx : x ∈ A then ⟨x, hx⟩ else a
      invFun := Subtype.val
      source := A
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun x _ => x.property
      left_inv' := fun x hx => by simp only [dite_eq_left hx]
      right_inv' := fun x _ => by
        apply Subtype.ext
        simp only [dite_eq_left x.property] }

omit [T2Space X] [Topology.CWComplex (Set.univ : Set X)] in
private theorem toSubtypePartial_apply (A : Set X) (a : A) (x : X) (hx : x ∈ A) :
    toSubtypePartial A a x = ⟨x, hx⟩ := by
  simp only [toSubtypePartial, dite_eq_left hx]

/-- Every selected closed-disk point already lies in the actual subcomplex. -/
private theorem originalCell_mem_subcomplex
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n)
    (x : Fin n → ℝ) (hx : x ∈ Metric.closedBall 0 1) :
    Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val x ∈ E :=
  E.closedCell_subset_of_mem j.property ⟨x, hx, rfl⟩

private def cellCenter
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    (E : Set X) :=
  ⟨Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val 0,
    originalCell_mem_subcomplex E n j 0 (by simp)⟩

/-- The original characteristic partial equivalence, corestricted to the
actual subtype. Its entire closed disk retains the original values. -/
private def subcomplexCellMap
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    PartialEquiv (Fin n → ℝ) (E : Set X) :=
  (Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val).trans
    (toSubtypePartial (E : Set X) (cellCenter E n j))

private theorem subcomplexCellMap_val
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n)
    (x : Fin n → ℝ) (hx : x ∈ Metric.closedBall 0 1) :
    (subcomplexCellMap E n j x).val =
      Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val x := by
  unfold subcomplexCellMap
  rw [PartialEquiv.trans_apply,
    toSubtypePartial_apply _ _ _ (originalCell_mem_subcomplex E n j x hx)]

private theorem subcomplexCellMap_source
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    (subcomplexCellMap E n j).source = Metric.ball 0 1 := by
  rw [subcomplexCellMap, PartialEquiv.trans_source,
    Topology.RelCWComplex.source_eq (C := (Set.univ : Set X)) n j.val]
  change Metric.ball (0 : Fin n → ℝ) 1 ∩
    (Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val) ⁻¹' (E : Set X) =
      Metric.ball 0 1
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    exact ⟨hx, originalCell_mem_subcomplex E n j x (Metric.ball_subset_closedBall hx)⟩

private theorem subcomplexCellMap_target
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    (subcomplexCellMap E n j).target =
      Subtype.val ⁻¹' (Topology.RelCWComplex.map
        (C := (Set.univ : Set X)) n j.val).target := by
  simp only [subcomplexCellMap, PartialEquiv.trans_target, toSubtypePartial,
    PartialEquiv.coe_symm_mk, Set.univ_inter]

/-- This equality includes the whole closed disk and, by restriction, the
whole open cell and whole frontier. -/
private theorem subcomplexCellMap_image
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ Metric.closedBall 0 1) :
    subcomplexCellMap E n j '' S = Subtype.val ⁻¹'
      (Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val '' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (subcomplexCellMap_val E n j x (hS hx)).symm⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, Subtype.ext ((subcomplexCellMap_val E n j x (hS hx)).trans he)⟩

private theorem subcomplexCellMap_continuousOn
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    ContinuousOn (subcomplexCellMap E n j) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  change Continuous (fun x : Metric.closedBall (0 : Fin n → ℝ) 1 =>
    (subcomplexCellMap E n j x.val).val)
  have he : (fun x : Metric.closedBall (0 : Fin n → ℝ) 1 =>
      (subcomplexCellMap E n j x.val).val) =
      (fun x : Metric.closedBall (0 : Fin n → ℝ) 1 =>
        Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val x.val) :=
    funext fun x => subcomplexCellMap_val E n j x.val x.property
  rw [he]
  exact (Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X)) n j.val).domRestrict

private theorem subcomplexCellMap_continuousOn_symm
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) (j : E.I n) :
    ContinuousOn (subcomplexCellMap E n j).symm (subcomplexCellMap E n j).target := by
  rw [subcomplexCellMap_target]
  change ContinuousOn
    ((Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val).symm ∘ Subtype.val)
    (Subtype.val ⁻¹'
      (Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val).target)
  exact (Topology.RelCWComplex.continuousOn_symm
    (C := (Set.univ : Set X)) n j.val).comp
    continuous_subtype_val.continuousOn (fun _ hz => hz)

/-- Transfer the canonical CW data of the closed subset to its actual subtype.
Only values on original closed characteristic disks enter the CW axioms. -/
@[instance_reducible]
private def subcomplexSubtypeCW
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set X)) :
    Topology.CWComplex (Set.univ : Set (E : Set X)) where
  cell n := E.I n
  map n j := subcomplexCellMap E n j
  source_eq n j := subcomplexCellMap_source E n j
  continuousOn n j := subcomplexCellMap_continuousOn E n j
  continuousOn_symm n j := subcomplexCellMap_continuousOn_symm E n j
  pairwiseDisjoint' := by
    let : Topology.CWComplex (E : Set X) :=
      Topology.CWComplex.Subcomplex.instCWComplex E
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    have h := @Topology.CWComplex.pairwiseDisjoint' X _ (E : Set X) _
      ⟨n, i⟩ (Set.mem_univ _) ⟨m, j⟩ (Set.mem_univ _) hne
    simp only [← Topology.CWComplex.map_def,
      Topology.CWComplex.Subcomplex.map_def E] at h
    change Disjoint (subcomplexCellMap E n i '' Metric.ball 0 1)
      (subcomplexCellMap E m j '' Metric.ball 0 1)
    rw [subcomplexCellMap_image E n i _ Metric.ball_subset_closedBall,
      subcomplexCellMap_image E m j _ Metric.ball_subset_closedBall]
    exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp h hz hz'
  mapsTo' := by
    classical
    let : Topology.CWComplex (E : Set X) :=
      Topology.CWComplex.Subcomplex.instCWComplex E
    intro n j
    obtain ⟨F, hF⟩ := Topology.CWComplex.mapsTo' (C := (E : Set X)) n j
    refine ⟨F, ?_⟩
    have he : (⋃ (m < n) (i ∈ F m), subcomplexCellMap E m i '' Metric.closedBall 0 1) =
        Subtype.val ⁻¹' (⋃ (m < n) (i ∈ F m),
          Topology.RelCWComplex.map (C := (Set.univ : Set X)) m i.val ''
            Metric.closedBall 0 1) := by
      simp only [Set.preimage_iUnion,
        subcomplexCellMap_image E _ _ _ (fun _ hx => hx)]
    erw [he]
    intro x hx
    rw [Set.mem_preimage]
    rw [subcomplexCellMap_val E n j x (Metric.sphere_subset_closedBall hx)]
    simpa only [← Topology.CWComplex.map_def,
      Topology.CWComplex.Subcomplex.map_def E] using! hF hx
  closed' := by
    let : Topology.CWComplex (E : Set X) :=
      Topology.CWComplex.Subcomplex.instCWComplex E
    intro A _ hA
    let B : Set X := Subtype.val '' A
    have hBE : B ⊆ (E : Set X) := by
      rintro _ ⟨z, _, rfl⟩
      exact z.property
    have hOld : ∀ (n : ℕ) (j : E.I n),
        IsClosed (B ∩ (Topology.RelCWComplex.map
          (C := (Set.univ : Set X)) n j.val '' Metric.closedBall 0 1)) := by
      intro n j
      have h := E.closed.isClosedMap_subtype_val _ (hA n j)
      rw [subcomplexCellMap_image E n j _ (fun _ hx => hx), Set.image_inter_preimage] at h
      exact h
    have hB : IsClosed B := by
      apply Topology.CWComplex.closed' (C := (E : Set X)) B hBE
      intro n j
      simpa only [← Topology.CWComplex.map_def,
        Topology.CWComplex.Subcomplex.map_def E] using! (hOld n j)
    have he : Subtype.val ⁻¹' B = A := by
      ext z
      constructor
      · rintro ⟨w, hw, he⟩
        exact (Subtype.val_injective he) ▸ hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [← he]
    exact hB.preimage continuous_subtype_val
  union' := by
    let : Topology.CWComplex (E : Set X) :=
      Topology.CWComplex.Subcomplex.instCWComplex E
    calc
      (⋃ (n : ℕ) (j : E.I n), subcomplexCellMap E n j '' Metric.closedBall 0 1) =
          Subtype.val ⁻¹' (⋃ (n : ℕ) (j : E.I n),
            Topology.RelCWComplex.map (C := (Set.univ : Set X)) n j.val ''
              Metric.closedBall 0 1) := by
        simp only [Set.preimage_iUnion,
          subcomplexCellMap_image E _ _ _ (fun _ hx => hx)]
      _ = Subtype.val ⁻¹' (E : Set X) := by
        congr 1
        simpa only [← Topology.CWComplex.map_def,
          Topology.CWComplex.Subcomplex.map_def E] using!
          (Topology.CWComplex.union' (C := (E : Set X)))
      _ = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        exact z.property

@[instance_reducible]
private def originalStageCW (k : ℕ) :
    Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X k)) :=
  subcomplexSubtypeCW (Topology.CWComplex.skeletonLT
    (Set.univ : Set X) (k : ℕ∞))

private theorem originalStageT2 (k : ℕ) : T2Space (Topology.CWComplex.skeletonTop X k) :=
  inferInstance

private theorem originalZeroStage_isEmpty :
    IsEmpty (Topology.CWComplex.skeletonTop X 0) :=
  ⟨fun x => by
    have hx := x.property
    change x.val ∈ (Topology.CWComplex.skeletonLT
      (Set.univ : Set X) (0 : ℕ∞) : Set X) at hx
    rw [Topology.CWComplex.skeletonLT_zero_eq_empty] at hx
    exact hx⟩

private def originalStageLabels (k : ℕ) :
    letI := originalStageCW (X := X) k
    ∀ n, Topology.RelCWComplex.cell (Set.univ : Set (Topology.CWComplex.skeletonTop X k)) n ↪
      Topology.RelCWComplex.cell (Set.univ : Set X) n := by
  letI := originalStageCW (X := X) k
  intro n
  change (Topology.CWComplex.skeletonLT (Set.univ : Set X) (k : ℕ∞)).I n ↪ _
  exact ⟨Subtype.val, Subtype.val_injective⟩

private theorem originalStageLabels_range (k n : ℕ) :
    letI := originalStageCW (X := X) k
    Set.range (originalStageLabels (X := X) k n) =
      {j : Topology.RelCWComplex.cell (Set.univ : Set X) n | (n : ℕ∞) < (k : ℕ∞)} := by
  let := originalStageCW (X := X) k
  change Set.range (Subtype.val :
    (Topology.CWComplex.skeletonLT (Set.univ : Set X) (k : ℕ∞)).I n → _) = _
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    simpa only [Topology.CWComplex.skeletonLT_I] using i.property
  · intro hn
    refine ⟨⟨j, ?_⟩, rfl⟩
    simpa only [Topology.CWComplex.skeletonLT_I] using hn

private theorem originalStage_closedDisk (k n : ℕ)
    (j : (Topology.CWComplex.skeletonLT (Set.univ : Set X) (k : ℕ∞)).I n)
    (d : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    letI := originalStageCW (X := X) k
    Topology.CWComplex.skeletonInclusion X k
        (Topology.CWComplex.characteristicDiskMap
          (X := Topology.CWComplex.skeletonTop X k) n j d) =
      Topology.CWComplex.characteristicDiskMap (X := X) n j.val d := by
  let := originalStageCW (X := X) k
  exact subcomplexCellMap_val
    (Topology.CWComplex.skeletonLT (Set.univ : Set X) (k : ℕ∞)) n j
    d.down.val d.down.property

/-- No CW, label, inverse or point witness is an input to the actual stage package. -/
private def originalStrictSkeletonCWPackage (k : ℕ) :
    Σ cw : Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X k)),
      letI := cw
      {κ : ∀ n,
          Topology.RelCWComplex.cell (Set.univ : Set (Topology.CWComplex.skeletonTop X k)) n ↪
            Topology.RelCWComplex.cell (Set.univ : Set X) n //
        (∀ n, Set.range (κ n) =
          {j : Topology.RelCWComplex.cell (Set.univ : Set X) n | (n : ℕ∞) < (k : ℕ∞)}) ∧
        (∀ (n : ℕ)
          (j : Topology.RelCWComplex.cell
            (Set.univ : Set (Topology.CWComplex.skeletonTop X k)) n)
          (d : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
          Topology.CWComplex.skeletonInclusion X k
              (Topology.CWComplex.characteristicDiskMap
                (X := Topology.CWComplex.skeletonTop X k) n j d) =
            Topology.CWComplex.characteristicDiskMap (X := X) n (κ n j) d) ∧
        T2Space (Topology.CWComplex.skeletonTop X k)} := by
  refine ⟨originalStageCW (X := X) k, ?_⟩
  letI := originalStageCW (X := X) k
  refine ⟨originalStageLabels (X := X) k, ?_, ?_, originalStageT2 (X := X) k⟩
  · exact originalStageLabels_range (X := X) k
  · intro n j d
    exact originalStage_closedDisk (X := X) k n j d

/-- The k-cells of the actual original successor stage have exactly the
original k-cell identifiers. This includes k=0 and an empty identifier type. -/
private def originalSuccessorCellEquiv (k : ℕ) :
    letI := originalStageCW (X := X) (k + 1)
    Topology.RelCWComplex.cell
      (Set.univ : Set (Topology.CWComplex.skeletonTop X (k + 1))) k ≃
      Topology.RelCWComplex.cell (Set.univ : Set X) k := by
  letI := originalStageCW (X := X) (k + 1)
  change (Topology.CWComplex.skeletonLT (Set.univ : Set X) ((k + 1 : ℕ) : ℕ∞)).I k ≃ _
  refine
    { toFun := Subtype.val
      invFun := fun j => ⟨j, ?_⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  have hk : (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self k
  simpa only [Topology.CWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hk

private theorem originalSuccessorCellEquiv_disk (k : ℕ)
    (j : Topology.RelCWComplex.cell (Set.univ : Set X) k)
    (d : (Topology.CWComplex.classicalCellDiskPair.{u} k).fst) :
    letI := originalStageCW (X := X) (k + 1)
    Topology.CWComplex.characteristicDiskMap
        (X := Topology.CWComplex.skeletonTop X (k + 1)) k
        ((originalSuccessorCellEquiv (X := X) k).symm j) d =
      Topology.CWComplex.characteristicDiskToSkeleton (X := X) k j d := by
  let := originalStageCW (X := X) (k + 1)
  apply Subtype.ext
  have h := originalStage_closedDisk (X := X) (k + 1) k
    ((originalSuccessorCellEquiv (X := X) k).symm j) d
  have he : ((originalSuccessorCellEquiv (X := X) k).symm j).val = j := by
    simpa only [originalSuccessorCellEquiv] using!
      (originalSuccessorCellEquiv (X := X) k).apply_symm_apply j
  change (Topology.CWComplex.characteristicDiskMap
    (X := Topology.CWComplex.skeletonTop X (k + 1)) k
      ((originalSuccessorCellEquiv (X := X) k).symm j) d).val = _ at h ⊢
  rw [he] at h
  exact h

/-- The actual attachment cocone and its maps remain the original ones. -/
private theorem originalSuccessorPushout (k : ℕ) :
    IsPushout (Topology.CWComplex.sphereSumToSkeleton X k)
      (Topology.CWComplex.sphereSumToDiskSum X k)
      (Topology.CWComplex.skeletonTransition X k)
      (Topology.CWComplex.diskSumToSkeleton X k) :=
  Topology.CWComplex.isPushout_skeletonAttachment X k


end OriginalStrictSkeletonCWConstruction47


end

/- Same-module private literal sphere/disk application of the smaller scalar
construction. The copied finite sphere, actual original max-norm disk pair,
ordinary cone and whole boundary/zero maps are retained. The actual original
sphere→disk attachment square is derived as an ordinary pushout. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe w

namespace CommonSuccessorSmallCylinderConstruction

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder

variable {W : Type w} {Q : PreAbstractSimplicialComplex W}

private def actualSphereSubdivisionFiniteFaces (d r : ℕ) :
    Finite (Face (subdivisionIter (SphereTriangulation.complex d) r)) := by
  let : Finite (Face (SphereTriangulation.complex d)) := SphereTriangulation.finite_faces d
  exact finiteFaces_subdivisionIter (SphereTriangulation.complex d) r

private def copiedDomainSphereHomeomorph (d r : ℕ) :
    (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization ≃ₜ
      (Topology.CWComplex.classicalCellDiskPair.{w} d).snd :=
  (MappingCylinder.relabelHomeomorph
      (barycentricSubdivision (subdivisionIter (SphereTriangulation.complex d) r))
      (Function.Embedding.inl : Face (subdivisionIter (SphereTriangulation.complex d) r) ↪
        Face (subdivisionIter (SphereTriangulation.complex d) r) ⊕ W)).symm.trans
    ((barycentricHomeomorph (subdivisionIter (SphereTriangulation.complex d) r)).trans
      ((iteratedHomeomorph (SphereTriangulation.complex d) r).trans
        ((SphereTriangulation.sphereHomeomorph d).trans (Homeomorph.ulift.{w, 0}).symm)))

private def originalSphereToCopiedDomain (d r : ℕ) :
    (Topology.CWComplex.classicalCellDiskPair.{w} d).snd ≃ₜ
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization :=
  (copiedDomainSphereHomeomorph (W := W) d r).symm

private def originalDiskToSmallCopiedCone (d r : ℕ) :
    (Topology.CWComplex.classicalCellDiskPair.{w} d).fst ≃ₜ
      TopCat.cone (TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization) :=
  (Topology.CWComplex.classicalDiskConeHomeomorph.{w} d).trans
    (TopCat.homeoOfIso (TopCat.coneFunctor.mapIso
      (TopCat.isoOfHomeo
      (X := (Topology.CWComplex.classicalCellDiskPair.{w} d).snd)
      (Y := TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
      (originalSphereToCopiedDomain (W := W) d r))))

private theorem originalDiskToSmallCopiedCone_boundary (d r : ℕ)
    (x : (Topology.CWComplex.classicalCellDiskPair.{w} d).snd) :
    originalDiskToSmallCopiedCone (W := W) d r
        ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x) =
      TopCat.coneBase (TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
          (originalSphereToCopiedDomain (W := W) d r x) := by
  change TopCat.coneMap (TopCat.isoOfHomeo
      (X := (Topology.CWComplex.classicalCellDiskPair.{w} d).snd)
      (Y := TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
      (originalSphereToCopiedDomain (W := W) d r)).hom
    (Topology.CWComplex.classicalDiskConeHomeomorph.{w} d
      ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x)) = _
  rw [Topology.CWComplex.classicalDiskConeHomeomorph_boundary]
  exact ConcreteCategory.congr_hom
    (TopCat.coneBase_naturality (TopCat.isoOfHomeo
      (X := (Topology.CWComplex.classicalCellDiskPair.{w} d).snd)
      (Y := TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
      (originalSphereToCopiedDomain (W := W) d r)).hom) x

private theorem originalDiskToSmallCopiedCone_zero (d r : ℕ) :
    originalDiskToSmallCopiedCone (W := W) d r
      (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩ : (Topology.CWComplex.classicalCellDiskPair.{w} d).fst) =
        TopCat.conePoint (TopCat.of
          (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
            PUnit.unit := by
  change TopCat.coneMap (TopCat.isoOfHomeo
      (X := (Topology.CWComplex.classicalCellDiskPair.{w} d).snd)
      (Y := TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
      (originalSphereToCopiedDomain (W := W) d r)).hom
    (Topology.CWComplex.classicalDiskConeHomeomorph.{w} d
      (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩)) = _
  rw [Topology.CWComplex.classicalDiskConeHomeomorph_zero]
  exact ConcreteCategory.congr_hom
    (TopCat.conePoint_naturality (TopCat.isoOfHomeo
      (X := (Topology.CWComplex.classicalCellDiskPair.{w} d).snd)
      (Y := TopCat.of
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W).Realization)
      (originalSphereToCopiedDomain (W := W) d r)).hom) PUnit.unit

private def originalSphereIntoSmall (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    C((Topology.CWComplex.classicalCellDiskPair.{w} d).snd, (smallCylinder f).Realization) :=
  (domainIntoSmall f).comp (originalSphereToCopiedDomain (W := W) d r : C(_, _))

private def originalDiskIntoSmallCone (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    C((Topology.CWComplex.classicalCellDiskPair.{w} d).fst, (smallAssociatedCone f).Realization) := by
  letI := actualSphereSubdivisionFiniteFaces d r
  exact (smallOrdinaryConeAttachment f).comp (originalDiskToSmallCopiedCone (W := W) d r : C(_, _))

private theorem originalDiskIntoSmallCone_closed (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    IsClosedEmbedding (originalDiskIntoSmallCone d r f) := by
  let := actualSphereSubdivisionFiniteFaces d r
  exact (smallOrdinaryConeAttachment_closed f).comp
    (originalDiskToSmallCopiedCone (W := W) d r).isClosedEmbedding

private theorem originalDiskIntoSmallCone_boundary (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (x : (Topology.CWComplex.classicalCellDiskPair.{w} d).snd) :
    originalDiskIntoSmallCone d r f ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x) =
      smallIntoCone f (originalSphereIntoSmall d r f x) := by
  let := actualSphereSubdivisionFiniteFaces d r
  change smallOrdinaryConeAttachment f
    (originalDiskToSmallCopiedCone (W := W) d r
      ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x)) = _
  rw [originalDiskToSmallCopiedCone_boundary]
  exact smallOrdinaryConeAttachment_base f (originalSphereToCopiedDomain (W := W) d r x)

private theorem originalDiskIntoSmallCone_zero (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    originalDiskIntoSmallCone d r f
      (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩ : (Topology.CWComplex.classicalCellDiskPair.{w} d).fst) =
        Realization.vertex (smallAssociatedCone f) (smallConeApex f).val (smallConeApex f).property := by
  let := actualSphereSubdivisionFiniteFaces d r
  change smallOrdinaryConeAttachment f
    (originalDiskToSmallCopiedCone (W := W) d r (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩)) = _
  rw [originalDiskToSmallCopiedCone_zero]
  exact smallOrdinaryConeAttachment_apex f

private theorem originalSphereDiskSmallCone_isPushout (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    IsPushout (TopCat.ofHom (originalSphereIntoSmall d r f))
      (Topology.CWComplex.classicalCellDiskPair.{w} d).map
      (TopCat.ofHom (smallIntoCone f)) (TopCat.ofHom (originalDiskIntoSmallCone d r f)) := by
  let := actualSphereSubdivisionFiniteFaces d r
  let e1 : (Topology.CWComplex.classicalCellDiskPair.{w} d).snd ≅
      TopCat.of (MappingCylinder.domainComplex
        (subdivisionIter (SphereTriangulation.complex d) r) W).Realization :=
    TopCat.isoOfHomeo (originalSphereToCopiedDomain (W := W) d r)
  let e2 := Iso.refl (TopCat.of (smallCylinder f).Realization)
  let e3 : (Topology.CWComplex.classicalCellDiskPair.{w} d).fst ≅
      TopCat.cone (TopCat.of (MappingCylinder.domainComplex
        (subdivisionIter (SphereTriangulation.complex d) r) W).Realization) :=
    TopCat.isoOfHomeo (originalDiskToSmallCopiedCone (W := W) d r)
  let e4 := Iso.refl (TopCat.of (smallAssociatedCone f).Realization)
  refine (smallOrdinaryConeAttachment_isPushout f).of_iso' e1 e2 e3 e4 ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro x
    rfl
  · apply ConcreteCategory.hom_ext
    intro x
    exact (originalDiskToSmallCopiedCone_boundary (W := W) d r x).symm
  · rfl
  · apply ConcreteCategory.hom_ext
    intro x
    rfl

example (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    IsClosedEmbedding (originalDiskIntoSmallCone d r f) := originalDiskIntoSmallCone_closed d r f

example (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q)
    (x : (Topology.CWComplex.classicalCellDiskPair.{w} d).snd) :
    originalDiskIntoSmallCone d r f ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x) =
      smallIntoCone f (originalSphereIntoSmall d r f x) := originalDiskIntoSmallCone_boundary d r f x

example (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    IsPushout (TopCat.ofHom (originalSphereIntoSmall d r f))
      (Topology.CWComplex.classicalCellDiskPair.{w} d).map
      (TopCat.ofHom (smallIntoCone f)) (TopCat.ofHom (originalDiskIntoSmallCone d r f)) :=
  originalSphereDiskSmallCone_isPushout d r f

example (d r : ℕ)
    (f : Morphism (subdivisionIter (SphereTriangulation.complex d) r) Q) :
    originalDiskIntoSmallCone d r f
      (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩ : (Topology.CWComplex.classicalCellDiskPair.{w} d).fst) =
        Realization.vertex (smallAssociatedCone f) (smallConeApex f).val (smallConeApex f).property :=
  originalDiskIntoSmallCone_zero d r f


end CommonSuccessorSmallCylinderConstruction

end

/- Dimension bounds for the weak CW cells. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped Simplicial

universe u

namespace WeakClassicalCWDimensionConstruction47

private theorem weakCWCell_dimension_bound {V : Type u} (P : PreAbstractSimplicialComplex V)
    (M : ℕ) (hP : ∀ a : Face P, a.val.card ≤ M) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n) : n < M := by
  let σ : (faceNerve P).nonDegenerate n :=
    SSet.realizationClassicalCWCellEquivNonDegenerate (faceNerve P) n j
  have hσ : StrictMono σ.val.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono σ.val).mp σ.property
  let f : Fin (n + 1) → ℕ := fun i => (σ.val.obj i).val.card
  have hf : StrictMono f := by
    intro i k hik
    exact Finset.card_lt_card (hσ hik)
  have hlow (i : Fin (n + 1)) : i.val + 1 ≤ f i := by
    refine Fin.induction ?_ ?_ i
    · have hpos : 0 < f 0 :=
        Finset.card_pos.mpr (P.isRelLowerSet_faces (σ.val.obj 0).property).1
      simpa only [Fin.val_zero, zero_add] using Nat.succ_le_of_lt hpos
    · intro k hk
      have hstep := hf (Fin.castSucc_lt_succ (i := k))
      change k.val + 1 ≤ f k.castSucc at hk
      change k.val + 2 ≤ f k.succ
      omega
  have hlast := hlow (Fin.last n)
  have hhigh := hP (σ.val.obj (Fin.last n))
  change n + 1 ≤ f (Fin.last n) at hlast
  change f (Fin.last n) ≤ M at hhigh
  omega

end WeakClassicalCWDimensionConstruction47

end

/- Same-module private refined top-cone geometry. The ACTUAL original disk
is identified with the canonical finite cone complex on its copied sphere,
not with a new single-cell CW model. All original boundary/zero maps and the
derived bound on its canonical characteristic cells are retained. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe w

namespace CommonSuccessorSmallCylinderConstruction

variable {W : Type w}

private def originalDiskToCopiedConeComplex (d r : ℕ) :
    (Topology.CWComplex.classicalCellDiskPair.{w} d).fst ≃ₜ
      (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).Realization := by
  letI := actualSphereSubdivisionFiniteFaces d r
  letI := MappingCylinder.finiteFaces_domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W
  exact (originalDiskToSmallCopiedCone (W := W) d r).trans
    (MappingCylinder.ordinaryConeHomeomorph
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W))

private theorem originalDiskToCopiedConeComplex_boundary (d r : ℕ)
    (x : (Topology.CWComplex.classicalCellDiskPair.{w} d).snd) :
    originalDiskToCopiedConeComplex (W := W) d r
        ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x) =
      (MappingCylinder.coneBaseMorphism
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).realization
          (originalSphereToCopiedDomain (W := W) d r x) := by
  let := actualSphereSubdivisionFiniteFaces d r
  let := MappingCylinder.finiteFaces_domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W
  change MappingCylinder.ordinaryConeHomeomorph _
    (originalDiskToSmallCopiedCone (W := W) d r
      ((Topology.CWComplex.classicalCellDiskPair.{w} d).map x)) = _
  rw [originalDiskToSmallCopiedCone_boundary, MappingCylinder.ordinaryConeHomeomorph_base]

private theorem originalDiskToCopiedConeComplex_zero (d r : ℕ) :
    originalDiskToCopiedConeComplex (W := W) d r
        (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩ : (Topology.CWComplex.classicalCellDiskPair.{w} d).fst) =
      Realization.vertex
        (MappingCylinder.coneComplex
          (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W))
        (MappingCylinder.coneApex
          (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).val
        (MappingCylinder.coneApex
          (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).property := by
  let := actualSphereSubdivisionFiniteFaces d r
  let := MappingCylinder.finiteFaces_domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W
  change MappingCylinder.ordinaryConeHomeomorph _
    (originalDiskToSmallCopiedCone (W := W) d r (ULift.up ⟨(0 : Fin d → ℝ), by simp⟩)) = _
  rw [originalDiskToSmallCopiedCone_zero, MappingCylinder.ordinaryConeHomeomorph_apex]

private abbrev refinedTopConeCell (d r n : ℕ) : Type w :=
  Topology.CWComplex.cell (Set.univ : Set
    (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).Realization) n

private def refinedTopConeDiskCharacteristic (d r n : ℕ)
    (j : refinedTopConeCell (W := W) d r n) :
    C((Topology.CWComplex.classicalCellDiskPair.{w} n).fst,
      (Topology.CWComplex.classicalCellDiskPair.{w} d).fst) :=
  ((originalDiskToCopiedConeComplex (W := W) d r).symm : C(_, _)).comp
    ⟨fun x => Topology.CWComplex.map n j x.down.val,
      (Topology.CWComplex.continuousOn n j).domRestrict.comp continuous_uliftDown⟩

private theorem refinedTopConeDiskCharacteristic_whole (d r n : ℕ)
    (j : refinedTopConeCell (W := W) d r n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{w} n).fst) :
    originalDiskToCopiedConeComplex (W := W) d r
      (refinedTopConeDiskCharacteristic (W := W) d r n j x) =
        Topology.CWComplex.map n j x.down.val :=
  (originalDiskToCopiedConeComplex (W := W) d r).apply_symm_apply _

private theorem refinedTopConeCell_dimension_bound (d r n : ℕ)
    (j : refinedTopConeCell (W := W) d r n) : n ≤ d := by
  have h := WeakClassicalCWDimensionConstruction47.weakCWCell_dimension_bound
    (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W))
    (d + 1) (actualSphere_copiedCone_face_card_le d r) n j
  omega


end CommonSuccessorSmallCylinderConstruction

end

/- Same-module private ACTUAL arbitrary-family tube-side pushout and its
refined characteristic maps. H is the internally constructed whole sphere
family; it is not a final X-only constructor premise. The top maps use the
actual canonical finite-cone cells, the bottom uses the original disk, and
the tube uses the literal interval/disk homeomorphism. No CW result on the
new carrier is assumed or asserted by these map definitions. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

variable {I W : Type u} {A : TopCat.{u}}

private abbrev sideSum (d : ℕ) : TopCat.{u} :=
  TopCat.of (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval)

private abbrev cylinderSum (d : ℕ) : TopCat.{u} :=
  TopCat.of (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)

private def sideInclusion (d : ℕ) : sideSum (I := I) d ⟶ cylinderSum (I := I) d :=
  TopCat.ofHom
    ⟨fun z => ⟨z.fst, ((Topology.CWComplex.classicalCellDiskPair.{u} d).map z.snd.1, z.snd.2)⟩,
      by
        change Continuous
          (Sigma.map (id : I → I)
            (fun _ : I => fun p : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval =>
              ((Topology.CWComplex.classicalCellDiskPair.{u} d).map p.1, p.2)) :
            (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) →
              (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval))
        exact Continuous.sigma_map (fun _ =>
          ((Topology.CWComplex.classicalCellDiskPair.{u} d).map.hom.continuous.comp
            continuous_fst).prodMk continuous_snd)⟩

private abbrev refinedTubeSpace (d : ℕ) (H : C(sideSum (I := I) d, A)) : TopCat.{u} :=
  pushout (TopCat.ofHom H) (sideInclusion (I := I) d)

private def oldIntoTubeSpace (d : ℕ) (H : C(sideSum (I := I) d, A)) :
    C(A, refinedTubeSpace d H) := (pushout.inl (TopCat.ofHom H) (sideInclusion (I := I) d)).hom

private def originalCylinderMap (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval, refinedTubeSpace d H) :=
  (pushout.inr (TopCat.ofHom H) (sideInclusion (I := I) d)).hom.comp
    ({ toFun := fun x =>
         (⟨i, x⟩ : Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)
       continuous_toFun := by
         change Continuous (@Sigma.mk I
           (fun _ : I => (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) i :
           (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval →
             (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval))
         exact continuous_sigmaMk } :
      C((Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval,
        cylinderSum (I := I) d))

private theorem originalCylinderMap_whole_side (d : ℕ) (H : C(sideSum (I := I) d, A))
    (i : I) (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : unitInterval) :
    originalCylinderMap d H i ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x, t) =
      oldIntoTubeSpace d H (H ⟨i, (x, t)⟩) := by
  have h := ConcreteCategory.congr_hom (pushout.condition (f := TopCat.ofHom H)
    (g := sideInclusion (I := I) d)) ⟨i, (x, t)⟩
  simpa only [TopCat.comp_app, originalCylinderMap, oldIntoTubeSpace,
    sideInclusion, ContinuousMap.comp_apply] using! h.symm

private def bottomDiskCharacteristic (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).fst, refinedTubeSpace d H) :=
  (originalCylinderMap d H i).comp ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

private def originalCylinderDiskHomeomorph (d : ℕ) :
    (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval ≃ₜ
      (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst :=
  ((Homeomorph.refl _).prodCongr ((TopCat.I.homeomorph.{u}).symm)).trans
    ((Homeomorph.prodComm _ _).trans (Topology.CWComplex.intervalDiskPairHomeomorph.{u} d))

private def wholeTubeCharacteristic (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst, refinedTubeSpace d H) :=
  (originalCylinderMap d H i).comp ((originalCylinderDiskHomeomorph.{u} d).symm : C(_, _))

private theorem wholeTubeCharacteristic_coordinates (d : ℕ) (H : C(sideSum (I := I) d, A))
    (i : I) (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) (t : unitInterval) :
    wholeTubeCharacteristic d H i (originalCylinderDiskHomeomorph.{u} d (x, t)) =
      originalCylinderMap d H i (x, t) :=
  congrArg (originalCylinderMap d H i) ((originalCylinderDiskHomeomorph.{u} d).symm_apply_apply (x, t))

private theorem wholeTubeCharacteristic_range (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    Set.range (wholeTubeCharacteristic d H i) = Set.range (originalCylinderMap d H i) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(originalCylinderDiskHomeomorph.{u} d).symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨originalCylinderDiskHomeomorph.{u} d x,
      wholeTubeCharacteristic_coordinates d H i x.1 x.2⟩

private def topConeCharacteristic (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) (n : ℕ)
    (j : refinedTopConeCell (W := W) d (r i) n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} n).fst, refinedTubeSpace d H) :=
  (originalCylinderMap d H i).comp
    ⟨fun x => (refinedTopConeDiskCharacteristic (W := W) d (r i) n j x, 1),
      (refinedTopConeDiskCharacteristic (W := W) d (r i) n j).continuous.prodMk continuous_const⟩

private theorem topConeCharacteristic_whole (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) (n : ℕ)
    (j : refinedTopConeCell (W := W) d (r i) n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    topConeCharacteristic d r H i n j x = originalCylinderMap d H i
      (refinedTopConeDiskCharacteristic (W := W) d (r i) n j x, 1) := rfl

private theorem bottomDiskCharacteristic_whole (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    bottomDiskCharacteristic d H i x = originalCylinderMap d H i (x, 0) := rfl

private def newTopConeCell (d r n : ℕ) : Type u :=
  {j : refinedTopConeCell (W := W) d r n //
    Disjoint (Topology.CWComplex.openCell
      (C := (Set.univ : Set (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).Realization)) n j)
      (Set.range (MappingCylinder.coneBaseMorphism
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).realization)}

/- These are candidate CW LABELS, not a supplied CW structure on the actual
new space. The copied-base exclusion is the actual geometric carrier of
the canonical cone base; matching subcomplex laws identify it with the
required canonical label exclusion before recursive admission. -/
private abbrev refinedTubeCellLabels (d : ℕ) (r : I → ℕ)
    [Topology.CWComplex (Set.univ : Set A)] (n : ℕ) : Type u :=
  Topology.CWComplex.cell (Set.univ : Set A) n ⊕
    ({i : I // n = d} ⊕
      ((Σ i : I, newTopConeCell (W := W) d (r i) n) ⊕ {i : I // n = d + 1}))

/- The remaining full tube chart uses the existing private literal
disk×interval closed-ball homeomorphism in the actual stage packet.
The original CW source may not be substituted by a supplied replacement.
No full new-carrier CW construction or inverse packet is claimed here. -/

example (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : unitInterval) :
    originalCylinderMap d H i ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x, t) =
      oldIntoTubeSpace d H (H ⟨i, (x, t)⟩) := originalCylinderMap_whole_side d H i x t


end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private derivation of the actual arbitrary-family tube
side closed embedding and every J_i embedding off that side. This covers
bottom, top and open tube interiors without a supplied chart hypothesis. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def sideProductMap (d : ℕ) :
    (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval →
      (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval :=
  fun x => ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.1, x.2)

private theorem sideProductMap_closed (d : ℕ) : IsClosedEmbedding (sideProductMap.{u} d) :=
  (Topology.CWComplex.isClosedEmbedding_classicalCellDiskPair_map (n := d)).prodMap
    IsClosedEmbedding.id

private theorem sideInclusion_closed (d : ℕ) : IsClosedEmbedding (sideInclusion (I := I) d) := by
  have he : IsEmbedding (sideInclusion (I := I) d) := by
    have he' : IsEmbedding
        (Sigma.map (id : I → I) (fun _ : I => sideProductMap.{u} d) :
          (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) →
            (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)) :=
      (Topology.isEmbedding_sigmaMap Function.injective_id).mpr
        (fun _ => (sideProductMap_closed d).isEmbedding)
    simpa only [sideInclusion, sideProductMap] using! he'
  have hr : IsClosed (Set.range (sideInclusion (I := I) d)) := by
    change IsClosed (Set.range
      (Sigma.map (id : I → I) (fun _ : I => sideProductMap.{u} d) :
        (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) →
          (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)))
    rw [isClosed_sigma_iff]
    intro i
    have h : (Sigma.mk i) ⁻¹' Set.range
        (Sigma.map (id : I → I) (fun _ : I => sideProductMap.{u} d) :
          (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) →
            (Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)) =
        Set.range (sideProductMap.{u} d) := by
      ext x
      constructor
      · rintro ⟨⟨j, y⟩, h⟩
        change (⟨j, sideProductMap.{u} d y⟩ :
          Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) = ⟨i, x⟩ at h
        have hij : j = i := (Sigma.mk.inj_iff.mp h).1
        subst j
        exact ⟨y, eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
      · rintro ⟨y, rfl⟩
        exact ⟨⟨i, y⟩, rfl⟩
    rw [h]
    exact (sideProductMap_closed d).isClosed_range
  exact ⟨he, hr⟩

private theorem oldIntoTubeSpace_closed (d : ℕ) (H : C(sideSum (I := I) d, A)) :
    IsClosedEmbedding (oldIntoTubeSpace d H) :=
  TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)).flip
    (sideInclusion_closed d)

private def cylinderOffSide (d : ℕ) : Set
    ((Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) :=
  {x | x.1 ∉ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map}

private theorem originalCylinderMap_offSide_isEmbedding (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) :
    IsEmbedding (fun x : cylinderOffSide.{u} d => originalCylinderMap d H i x.val) := by
  let U : Set (refinedTubeSpace d H) := (Set.range (oldIntoTubeSpace d H))ᶜ
  have hU : IsOpen U := (oldIntoTubeSpace_closed d H).isClosed_range.isOpen_compl
  let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  have hOld : (oldIntoTubeSpace d H) ⁻¹' U = ∅ := by
    ext x
    exact iff_false_intro (fun hx => hx (Set.mem_range_self x))
  let J := pushout.inr (TopCat.ofHom H) (sideInclusion (I := I) d)
  have hSide : J ⁻¹' U ⊆ (Set.range (sideInclusion (I := I) d))ᶜ := by
    rintro x hx ⟨s, rfl⟩
    exact hx ⟨H s, ConcreteCategory.congr_hom sq.w s⟩
  let hh := TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout sq hU hOld hSide
  let γ : cylinderOffSide.{u} d → cylinderSum (I := I) d := fun x => ⟨i, x.val⟩
  have hγ : IsEmbedding γ := IsEmbedding.sigmaMk.comp IsEmbedding.subtypeVal
  have hγU (x : cylinderOffSide.{u} d) : γ x ∈ J ⁻¹' U := by
    rintro ⟨a, ha⟩
    let hflip := sq.flip.map (forget TopCat)
    obtain ⟨s, hs, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hflip.isColimit
        (sideInclusion_closed d).injective (γ x) a).mp ha.symm
    rcases s with ⟨j, y⟩
    change (⟨j, sideProductMap.{u} d y⟩ :
      Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) = ⟨i, x.val⟩ at hs
    have hij : j = i := (Sigma.mk.inj_iff.mp hs).1
    subst j
    have hxy : sideProductMap.{u} d y = x.val :=
      eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    exact x.property ⟨y.1, congrArg Prod.fst hxy⟩
  let ψ : cylinderOffSide.{u} d → J ⁻¹' U := fun x => ⟨γ x, hγU x⟩
  have hψ : IsEmbedding ψ := hγ.codRestrict _ hγU
  simpa only [ψ, γ, J, originalCylinderMap, Function.comp_def] using!
    IsEmbedding.subtypeVal.comp (hh.isEmbedding.comp hψ)


end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private bottom original-disk open chart. Its embedding is
derived from the actual J_i off-side embedding and the literal disk ball.
No embedding or new CW witness is supplied in a final constructor. -/

noncomputable section

open CategoryTheory Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def openBallToOriginalDisk (d : ℕ) :
    Metric.ball (0 : Fin d → ℝ) 1 → (Topology.CWComplex.classicalCellDiskPair.{u} d).fst :=
  fun x => ULift.up ⟨x.val, Metric.ball_subset_closedBall x.property⟩

private theorem openBallToOriginalDisk_embedding (d : ℕ) :
    IsEmbedding (openBallToOriginalDisk.{u} d) :=
  Homeomorph.ulift.symm.isEmbedding.comp
    (IsEmbedding.subtypeVal.codRestrict _ (fun x => Metric.ball_subset_closedBall x.property))

private theorem openBallToOriginalDisk_not_side (d : ℕ)
    (x : Metric.ball (0 : Fin d → ℝ) 1) :
    openBallToOriginalDisk.{u} d x ∉ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map := by
  rintro ⟨s, hs⟩
  have heq : s.down.val = x.val :=
    congrArg (fun y : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst => y.down.val) hs
  have hdist : dist x.val (0 : Fin d → ℝ) = 1 := by
    have h := s.down.property
    change dist s.down.val (0 : Fin d → ℝ) = 1 at h
    rwa [heq] at h
  exact (ne_of_lt x.property) hdist

private theorem bottomOriginalDiskOpenChart_embedding (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) :
    IsEmbedding (fun x : Metric.ball (0 : Fin d → ℝ) 1 =>
      bottomDiskCharacteristic d H i (openBallToOriginalDisk.{u} d x)) := by
  let γ : Metric.ball (0 : Fin d → ℝ) 1 →
      (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval :=
    fun x => (openBallToOriginalDisk.{u} d x, 0)
  have hγ : IsEmbedding γ :=
    (isEmbedding_graph (f := fun _ : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst =>
      (0 : unitInterval)) continuous_const).comp (openBallToOriginalDisk_embedding d)
  have hnot (x : Metric.ball (0 : Fin d → ℝ) 1) : γ x ∈ cylinderOffSide.{u} d :=
    openBallToOriginalDisk_not_side d x
  let ψ : Metric.ball (0 : Fin d → ℝ) 1 → cylinderOffSide.{u} d := fun x => ⟨γ x, hnot x⟩
  have hψ : IsEmbedding ψ := hγ.codRestrict _ hnot
  exact (originalCylinderMap_offSide_isEmbedding d H i).comp hψ


end ActualRefinedTubeCharacteristicConstruction47

end
/- Same-module private whole tube interior chart. Its no-side condition is
derived from the ACTUAL full interval/disk pair boundary, and its embedding
is the actual J_i off-side embedding. No geometric inverse or chart is supplied. -/

noncomputable section

open CategoryTheory Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private theorem originalCylinderDiskHomeomorph_open_not_side (d : ℕ)
    (x : Metric.ball (0 : Fin (d + 1) → ℝ) 1) :
    ((originalCylinderDiskHomeomorph.{u} d).symm (openBallToOriginalDisk.{u} (d + 1) x)).1 ∉
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map := by
  let y := openBallToOriginalDisk.{u} (d + 1) x
  have hy : y ∉ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map :=
    openBallToOriginalDisk_not_side (d + 1) x
  let p := (originalCylinderDiskHomeomorph.{u} d).symm y
  intro hp
  let q : (Topology.CWComplex.intervalDiskPair.{u} d).fst :=
    ((TopCat.I.homeomorph.{u}).symm p.2, p.1)
  have hq : q ∈ Set.range (Topology.CWComplex.intervalDiskPair.{u} d).map :=
    (Topology.CWComplex.mem_range_intervalDiskPair_map_iff d q).mpr (Or.inr hp)
  have hBoundary : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q ∈
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map := by
    change q ∈ (Topology.CWComplex.intervalDiskPairHomeomorph.{u} d) ⁻¹'
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map
    rw [Topology.CWComplex.intervalDiskPairHomeomorph_preimage_range,
      ← Topology.CWComplex.range_intervalDiskPair_map]
    exact hq
  change originalCylinderDiskHomeomorph.{u} d p ∈
    Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map at hBoundary
  rw [Homeomorph.apply_symm_apply] at hBoundary
  exact hy hBoundary

private theorem wholeTubeOpenChart_embedding (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) :
    IsEmbedding (fun x : Metric.ball (0 : Fin (d + 1) → ℝ) 1 =>
      wholeTubeCharacteristic d H i (openBallToOriginalDisk.{u} (d + 1) x)) := by
  let γ : Metric.ball (0 : Fin (d + 1) → ℝ) 1 →
      (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval :=
    fun x => (originalCylinderDiskHomeomorph.{u} d).symm (openBallToOriginalDisk.{u} (d + 1) x)
  have hγ : IsEmbedding γ :=
    (originalCylinderDiskHomeomorph.{u} d).symm.isEmbedding.comp
      (openBallToOriginalDisk_embedding (d + 1))
  have hnot (x : Metric.ball (0 : Fin (d + 1) → ℝ) 1) : γ x ∈ cylinderOffSide.{u} d :=
    originalCylinderDiskHomeomorph_open_not_side d x
  let ψ : Metric.ball (0 : Fin (d + 1) → ℝ) 1 → cylinderOffSide.{u} d :=
    fun x => ⟨γ x, hnot x⟩
  have hψ : IsEmbedding ψ := hγ.codRestrict _ hnot
  exact (originalCylinderMap_offSide_isEmbedding d H i).comp hψ


end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private actual refined top-cone open chart. The selected
cone cells avoid the exact copied-base carrier. The original disk/cone
boundary law then places their entire open charts off the actual tube side. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction Topology.CWComplex.MatchedAmalgam

variable {I W : Type u} {A : TopCat.{u}}

private theorem originalDiskToConeComplex_range_boundary (d r : ℕ)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    originalDiskToCopiedConeComplex (W := W) d r x ∈
        Set.range (MappingCylinder.coneBaseMorphism
          (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)).realization ↔
      x ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map := by
  constructor
  · rintro ⟨y, hy⟩
    let s := (originalSphereToCopiedDomain (W := W) d r).symm y
    refine ⟨s, (originalDiskToCopiedConeComplex (W := W) d r).injective ?_⟩
    rw [originalDiskToCopiedConeComplex_boundary]
    rw [(originalSphereToCopiedDomain (W := W) d r).apply_symm_apply]
    exact hy
  · rintro ⟨s, rfl⟩
    exact ⟨originalSphereToCopiedDomain (W := W) d r s,
      (originalDiskToCopiedConeComplex_boundary (W := W) d r s).symm⟩

private theorem newTopConeDisk_open_not_side (d r n : ℕ)
    (j : newTopConeCell (W := W) d r n) (x : Metric.ball (0 : Fin n → ℝ) 1) :
    refinedTopConeDiskCharacteristic (W := W) d r n j.val
        (openBallToOriginalDisk.{u} n x) ∉
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map := by
  intro h
  have hb := (originalDiskToConeComplex_range_boundary (W := W) d r _).mpr h
  rw [refinedTopConeDiskCharacteristic_whole] at hb
  exact j.property.notMem_of_mem_left ⟨x.val, x.property, rfl⟩ hb

private theorem newTopConeOpenChart_embedding (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I) (n : ℕ)
    (j : newTopConeCell (W := W) d (r i) n) :
    IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
      topConeCharacteristic d r H i n j.val (openBallToOriginalDisk.{u} n x)) := by
  let c := MappingCylinder.coneComplex
    (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) (r i)) W)
  let e := originalDiskToCopiedConeComplex (W := W) d (r i)
  let v : Metric.ball (0 : Fin n → ℝ) 1 → (Topology.CWComplex.classicalCellDiskPair.{u} d).fst :=
    fun x => e.symm (Topology.CWComplex.map (C := (Set.univ : Set c.Realization)) n j.val x.val)
  have hv : IsEmbedding v := e.symm.isEmbedding.comp (openCellMap_isEmbedding n j.val)
  let γ : Metric.ball (0 : Fin n → ℝ) 1 →
      (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval := fun x => (v x, 1)
  have hγ : IsEmbedding γ :=
    (isEmbedding_graph (f := fun _ : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst =>
      (1 : unitInterval)) continuous_const).comp hv
  have hnot (x : Metric.ball (0 : Fin n → ℝ) 1) : γ x ∈ cylinderOffSide.{u} d :=
    newTopConeDisk_open_not_side d (r i) n j x
  let ψ : Metric.ball (0 : Fin n → ℝ) 1 → cylinderOffSide.{u} d := fun x => ⟨γ x, hnot x⟩
  have hψ : IsEmbedding ψ := hγ.codRestrict _ hnot
  exact (originalCylinderMap_offSide_isEmbedding d H i).comp hψ


end ActualRefinedTubeCharacteristicConstruction47

end



/-!
Private finite-carrier proof for classical Hausdorff CW
spaces. Every subset of the selected one-point-per-open-cell set is closed,
by closure finiteness and the original CW weak topology. Compactness then
forces only finitely many meeting cells. No countability, local finiteness
or supplied finite-carrier hypothesis is used. This result is not applied
to a strong metric realization before its CW construction.
-/

noncomputable section
set_option autoImplicit false

open Topology

universe u

namespace ClassicalCWCompactCarrierConstruction47

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable [Topology.CWComplex (Set.univ : Set X)]

private abbrev CellIndex := Σ n, Topology.CWComplex.cell (Set.univ : Set X) n

private def meetsOpenCell (K : Set X) (c : CellIndex (X := X)) : Prop :=
  ∃ x, x ∈ K ∧ x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) c.fst c.snd

private def selectedPoint (K : Set X) (c : CellIndex (X := X)) : X := by
  classical
  exact if h : meetsOpenCell K c then Classical.choose h
    else Topology.CWComplex.map (C := (Set.univ : Set X)) c.fst c.snd 0

omit [T2Space X] in
private theorem selectedPoint_spec (K : Set X) (c : CellIndex (X := X))
    (hc : meetsOpenCell K c) :
    selectedPoint K c ∈ K ∧
      selectedPoint K c ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) c.fst c.snd := by
  classical
  rw [selectedPoint, dite_eq_left hc]
  exact Classical.choose_spec hc

private def selectedImage (K : Set X) : Set X :=
  Set.range (fun c : {c : CellIndex (X := X) // meetsOpenCell K c} => selectedPoint K c.val)

omit [T2Space X] in
private theorem selectedPoint_injective (K : Set X) :
    Function.Injective (fun c : {c : CellIndex (X := X) // meetsOpenCell K c} => selectedPoint K c.val) := by
  intro c d h
  apply Subtype.ext
  by_contra hne
  have hc := (selectedPoint_spec K c.val c.property).2
  have hd := (selectedPoint_spec K d.val d.property).2
  dsimp only at h
  rw [← h] at hd
  exact (Topology.CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left hc hd

omit [T2Space X] in
private theorem closedCell_finite_open_carrier (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    ∃ J : Finset (CellIndex (X := X)),
      Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j ⊆
        ⋃ c ∈ J, Topology.CWComplex.openCell (C := (Set.univ : Set X)) c.fst c.snd := by
  classical
  obtain ⟨I, hI⟩ := Topology.CWComplex.cellFrontier_subset_finite_openCell
    (C := (Set.univ : Set X)) n j
  let J : Finset (CellIndex (X := X)) :=
    insert ⟨n, j⟩ ((Finset.range n).biUnion (fun m => (I m).image (Sigma.mk m)))
  refine ⟨J, ?_⟩
  intro x hx
  rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell
    (C := (Set.univ : Set X)) n j] at hx
  rcases hx with hx | hx
  · have h := hI hx
    simp only [Set.mem_iUnion] at h ⊢
    rcases h with ⟨m, hm, a, ha, hxa⟩
    refine ⟨⟨m, a⟩, ?_, hxa⟩
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨m, Finset.mem_range.mpr hm, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)
  · exact Set.mem_iUnion.mpr ⟨⟨n, j⟩,
      Set.mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hx⟩⟩

omit [T2Space X] in
private theorem subsetSelected_inter_closedCell_finite (K S : Set X)
    (hS : S ⊆ selectedImage K) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set X) n) :
    (S ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j).Finite := by
  classical
  obtain ⟨J, hJ⟩ := closedCell_finite_open_carrier n j
  apply (J.finite_toSet.image (selectedPoint K)).subset
  rintro x ⟨hxS, hxCell⟩
  rcases hS hxS with ⟨c, hc⟩
  dsimp only at hc
  have h := hJ hxCell
  simp only [Set.mem_iUnion] at h
  rcases h with ⟨a, ha, hxa⟩
  have hca : c.val = a := by
    by_contra hne
    have hxc := (selectedPoint_spec K c.val c.property).2
    rw [hc] at hxc
    exact (Topology.CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left hxc hxa
  exact ⟨c.val, by rw [hca]; exact ha, hc⟩

private theorem subsetSelected_isClosed (K S : Set X) (hS : S ⊆ selectedImage K) : IsClosed S :=
  Topology.CWComplex.closed' (C := (Set.univ : Set X)) S (Set.subset_univ _)
    (fun n j => (subsetSelected_inter_closedCell_finite K S hS n j).isClosed)

omit [T2Space X] in
private theorem selectedImage_subset (K : Set X) : selectedImage K ⊆ K := by
  rintro x ⟨c, rfl⟩
  exact (selectedPoint_spec K c.val c.property).1

private theorem compact_meeting_cells_finite (K : Set X) (hK : IsCompact K) :
    {c : CellIndex (X := X) | meetsOpenCell K c}.Finite := by
  classical
  have hclosed : IsClosed (selectedImage K) := subsetSelected_isClosed K _ (fun _ hx => hx)
  have hdisc : DiscreteTopology (selectedImage K) :=
    discreteTopology_iff_forall_isClosed.mpr (fun U => by
      have hU : U = Subtype.val ⁻¹' (Subtype.val '' U) :=
        (Set.preimage_image_eq U Subtype.val_injective).symm
      rw [hU]
      apply IsClosed.preimage continuous_subtype_val
      apply subsetSelected_isClosed K
      rintro x ⟨y, _, rfl⟩
      exact y.property)
  have hcompact : IsCompact (selectedImage K) :=
    hK.of_isClosed_subset hclosed (selectedImage_subset K)
  have hfinite : (selectedImage K).Finite :=
    hcompact.finite (isDiscrete_iff_discreteTopology.mpr hdisc)
  have : Finite (selectedImage K) := Set.finite_coe_iff.mp hfinite
  let e : {c : CellIndex (X := X) // meetsOpenCell K c} → selectedImage K :=
    fun c => ⟨selectedPoint K c.val, Set.mem_range_self c⟩
  have he : Function.Injective e := by
    intro c d h
    exact selectedPoint_injective K (congrArg Subtype.val h)
  exact Set.finite_coe_iff.mpr (Finite.of_injective e he)

private theorem compact_classical_finite_carrier (K : Set X) (hK : IsCompact K) :
    ∃ J : Finset (CellIndex (X := X)),
      K ⊆ ⋃ c ∈ J, Topology.CWComplex.closedCell (C := (Set.univ : Set X)) c.fst c.snd := by
  classical
  let J := (compact_meeting_cells_finite K hK).toFinset
  refine ⟨J, ?_⟩
  intro x hx
  have h : x ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n),
      Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
    simpa only using!
      (Eq.mpr (congrArg (fun S : Set X => x ∈ S)
        (Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))))
        (Set.mem_univ x))
  simp only [Set.mem_iUnion] at h
  rcases h with ⟨n, j, hxj⟩
  refine Set.mem_iUnion.mpr ⟨⟨n, j⟩, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact (compact_meeting_cells_finite K hK).mem_toFinset.mpr ⟨x, hx, hxj⟩
  · exact Topology.CWComplex.openCell_subset_closedCell
      (C := (Set.univ : Set X)) n j hxj

private theorem compactDomain_classical_finite_carrier {D : Type*} [TopologicalSpace D]
    [CompactSpace D] (f : C(D, X)) :
    ∃ J : Finset (CellIndex (X := X)),
      Set.range f ⊆ ⋃ c ∈ J,
        Topology.CWComplex.closedCell (C := (Set.univ : Set X)) c.fst c.snd :=
  compact_classical_finite_carrier (Set.range f) (isCompact_range f.continuous)

example {D : Type*} [TopologicalSpace D] [CompactSpace D] (f : C(D, X)) :
    ∃ J : Finset (CellIndex (X := X)),
      Set.range f ⊆ ⋃ c ∈ J,
        Topology.CWComplex.closedCell (C := (Set.univ : Set X)) c.fst c.snd :=
  compactDomain_classical_finite_carrier f


end ClassicalCWCompactCarrierConstruction47

end

/- Same-module private fragment after immutable compact-carrier route15.
The actual canonical cone is homeomorphic to the ORIGINAL finite disk.
Compactness of a Hausdorff classical CW space then gives finitely many
actual cell labels. This does not identify a classical cell with a nerve
simplex and does not use route16's opaque cell-alias conversion.
It does not assert the separate dimension bound. -/

noncomputable section

open Topology PreAbstractSimplicialComplex

universe u

namespace ClassicalCWCompactCarrierConstruction47

private theorem compact_classical_all_cell_labels_finite
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [Topology.CWComplex (Set.univ : Set X)] :
    _root_.Finite (CellIndex (X := X)) := by
  classical
  have hmeet (c : CellIndex (X := X)) : meetsOpenCell (Set.univ : Set X) c := by
    refine ⟨Topology.CWComplex.map (C := (Set.univ : Set X)) c.fst c.snd 0,
      Set.mem_univ _, ?_⟩
    exact ⟨0, by simp, rfl⟩
  have hfinite := compact_meeting_cells_finite (Set.univ : Set X) isCompact_univ
  let : _root_.Finite {c : CellIndex (X := X) // meetsOpenCell (Set.univ : Set X) c} :=
    Set.finite_coe_iff.mp hfinite
  let f : CellIndex (X := X) →
      {c : CellIndex (X := X) // meetsOpenCell (Set.univ : Set X) c} := fun c => ⟨c, hmeet c⟩
  exact _root_.Finite.of_injective f (fun _ _ h => congrArg Subtype.val h)

end ClassicalCWCompactCarrierConstruction47

namespace CommonSuccessorSmallCylinderConstruction

private def finiteRefinedTopConeCellsViaCompactness {W : Type u} (d r : ℕ) :
    _root_.Finite (Σ n, refinedTopConeCell (W := W) d r n) := by
  let : T2Space (Topology.CWComplex.classicalCellDiskPair.{u} d).fst := by
    change T2Space (ULift.{u} (Metric.closedBall (0 : Fin d → ℝ) 1))
    infer_instance
  let c := MappingCylinder.coneComplex
    (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W)
  let e := originalDiskToCopiedConeComplex (W := W) d r
  let : CompactSpace c.Realization := e.compactSpace
  let : T2Space c.Realization := e.t2Space
  exact ClassicalCWCompactCarrierConstruction47.compact_classical_all_cell_labels_finite
    (X := c.Realization)

example {W : Type u} (d r : ℕ) :
    _root_.Finite (Σ n, refinedTopConeCell (W := W) d r n) :=
  finiteRefinedTopConeCellsViaCompactness (W := W) d r

end CommonSuccessorSmallCylinderConstruction

end

/- Same-module private source continuation of immutable control-route26.
It constructs the actual full characteristic functions and their partial
equivalences. It assumes no CW structure on the new tube carrier and no
chart, embedding, contraction or finite-frontier witness. The CW structure
on A is the internally constructed previous/intermediate stage. This is
not yet the final X-only successor constructor. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u


namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction Topology.CWComplex.MatchedAmalgam

variable {I W : Type u} {A : TopCat.{u}}

private def extendClosedDiskMap {Y : Type u} (n : ℕ)
    (f : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst → Y)
    (x : Fin n → ℝ) : Y := by
  classical
  exact if hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 then f (ULift.up ⟨x, hx⟩)
    else f (ULift.up ⟨0, by simp [Metric.mem_closedBall]⟩)

private theorem extendClosedDiskMap_on_closed {Y : Type u} (n : ℕ)
    (f : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst → Y)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    extendClosedDiskMap n f x.down.val = f x := by
  rw [extendClosedDiskMap, dite_eq_left x.down.property]
  rfl

private def oldCellClosedCharacteristic
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set A) n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} n).fst, refinedTubeSpace d H) :=
  { toFun := fun x => oldIntoTubeSpace d H
      (Topology.CWComplex.map (C := (Set.univ : Set A)) n j x.down.val)
    continuous_toFun := (oldIntoTubeSpace d H).continuous.comp
      ((Topology.CWComplex.continuousOn (C := (Set.univ : Set A)) n j).domRestrict.comp
        Homeomorph.ulift.continuous) }

private def refinedTubeClosedCharacteristic
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} n).fst, refinedTubeSpace d H) := by
  rcases j with a | (a | (a | a))
  · exact oldCellClosedCharacteristic d H n a
  · rcases a with ⟨i, hn⟩
    subst n
    exact bottomDiskCharacteristic d H i
  · rcases a with ⟨i, j⟩
    exact topConeCharacteristic d r H i n j.val
  · rcases a with ⟨i, hn⟩
    subst n
    exact wholeTubeCharacteristic d H i

/- The old and canonical cone characteristic functions are preserved on
ALL vectors, including outside the closed ball. New bottom/tube functions
extend their actual closed-disk maps by their actual central value. -/
private def refinedTubeCellTotal
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    (Fin n → ℝ) → refinedTubeSpace d H := by
  rcases j with a | (a | (a | a))
  · exact fun x => oldIntoTubeSpace d H
      (Topology.CWComplex.map (C := (Set.univ : Set A)) n a x)
  · rcases a with ⟨i, hn⟩
    subst n
    exact extendClosedDiskMap d (bottomDiskCharacteristic d H i)
  · rcases a with ⟨i, j⟩
    let c := MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) (r i)) W)
    exact fun x => originalCylinderMap d H i
      ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm
        (Topology.CWComplex.map (C := (Set.univ : Set c.Realization)) n j.val x), 1)
  · rcases a with ⟨i, hn⟩
    subst n
    exact extendClosedDiskMap (d + 1) (wholeTubeCharacteristic d H i)

private theorem refinedTubeCellTotal_closed_characteristic
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    refinedTubeCellTotal d r H n j x.down.val = refinedTubeClosedCharacteristic d r H n j x := by
  rcases j with a | (a | (a | a))
  · rfl
  · rcases a with ⟨i, hn⟩
    subst n
    exact extendClosedDiskMap_on_closed d (bottomDiskCharacteristic d H i) x
  · rcases a with ⟨i, j⟩
    let c := MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) (r i)) W)
    change originalCylinderMap d H i
      ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm
        (Topology.CWComplex.map (C := (Set.univ : Set c.Realization)) n j.val x.down.val), 1) =
      originalCylinderMap d H i
        (refinedTopConeDiskCharacteristic (W := W) d (r i) n j.val x, 1)
    apply congrArg (fun y => originalCylinderMap d H i (y, 1))
    apply (originalDiskToCopiedConeComplex (W := W) d (r i)).injective
    rw [Homeomorph.apply_symm_apply, refinedTopConeDiskCharacteristic_whole]
  · rcases a with ⟨i, hn⟩
    subst n
    exact extendClosedDiskMap_on_closed (d + 1) (wholeTubeCharacteristic d H i) x

private theorem refinedTubeCellTotal_open_isEmbedding
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => refinedTubeCellTotal (W := W) d r H n j x.val) := by
  rcases j with a | (a | (a | a))
  · exact (oldIntoTubeSpace_closed d H).isEmbedding.comp
      (openCellMap_isEmbedding (X := A) n a)
  · rcases a with ⟨i, hn⟩
    subst n
    have heq : (fun x : Metric.ball (0 : Fin d → ℝ) 1 =>
        refinedTubeCellTotal (W := W) d r H d (Sum.inr (Sum.inl ⟨i, rfl⟩)) x.val) =
      (fun x => bottomDiskCharacteristic d H i (openBallToOriginalDisk.{u} d x)) := by
      funext x
      exact refinedTubeCellTotal_closed_characteristic (W := W) d r H d _
        (openBallToOriginalDisk.{u} d x)
    rw [heq]
    exact bottomOriginalDiskOpenChart_embedding d H i
  · rcases a with ⟨i, j⟩
    have heq : (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
        refinedTubeCellTotal (W := W) d r H n (Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩))) x.val) =
      (fun x => topConeCharacteristic d r H i n j.val (openBallToOriginalDisk.{u} n x)) := by
      funext x
      exact refinedTubeCellTotal_closed_characteristic (W := W) d r H n _
        (openBallToOriginalDisk.{u} n x)
    rw [heq]
    exact newTopConeOpenChart_embedding d r H i n j
  · rcases a with ⟨i, hn⟩
    subst n
    have heq : (fun x : Metric.ball (0 : Fin (d + 1) → ℝ) 1 =>
        refinedTubeCellTotal (W := W) d r H (d + 1) (Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩))) x.val) =
      (fun x => wholeTubeCharacteristic d H i (openBallToOriginalDisk.{u} (d + 1) x)) := by
      funext x
      exact refinedTubeCellTotal_closed_characteristic (W := W) d r H (d + 1) _
        (openBallToOriginalDisk.{u} (d + 1) x)
    rw [heq]
    exact wholeTubeOpenChart_embedding d H i

private def refinedTubeCellPartialEquiv
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    PartialEquiv (Fin n → ℝ) (refinedTubeSpace d H) :=
  cellPartialEquivOfEmbedding n (refinedTubeCellTotal d r H n j)
    (refinedTubeCellTotal_open_isEmbedding d r H n j)

private theorem refinedTubeCellPartialEquiv_source
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    (refinedTubeCellPartialEquiv d r H n j).source = Metric.ball (0 : Fin n → ℝ) 1 := rfl

private theorem refinedTubeCellPartialEquiv_closed_characteristic
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    refinedTubeCellPartialEquiv d r H n j x.down.val = refinedTubeClosedCharacteristic d r H n j x :=
  refinedTubeCellTotal_closed_characteristic d r H n j x

private theorem refinedTubeCellPartialEquiv_continuousOn
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    ContinuousOn (refinedTubeCellPartialEquiv d r H n j) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun x : Metric.closedBall (0 : Fin n → ℝ) 1 =>
      refinedTubeClosedCharacteristic d r H n j (ULift.up x)) :=
    (refinedTubeClosedCharacteristic d r H n j).continuous.comp Homeomorph.ulift.symm.continuous
  exact hc.congr (fun x => (refinedTubeCellPartialEquiv_closed_characteristic d r H n j
    (ULift.up x)).symm)

private theorem refinedTubeCellPartialEquiv_continuousOn_symm
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    ContinuousOn (refinedTubeCellPartialEquiv d r H n j).symm
      (refinedTubeCellPartialEquiv d r H n j).target :=
  cellPartialEquivOfEmbedding_continuousOn_symm n (refinedTubeCellTotal d r H n j)
    (refinedTubeCellTotal_open_isEmbedding d r H n j)

example [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    refinedTubeCellPartialEquiv d r H n j x.down.val = refinedTubeClosedCharacteristic d r H n j x :=
  refinedTubeCellPartialEquiv_closed_characteristic d r H n j x

end ActualRefinedTubeCharacteristicConstruction47

end

/- The closed tube chart covers the ENTIRE original disk×interval. Its
preimage law gives the actual pushout weak topology directly. Neither
TopCat adhesive nor an assumed CW structure on the new carrier is used. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I W : Type u} {A : TopCat.{u}}

private theorem refinedTubeCellPartialEquiv_closed_range
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : refinedTubeCellLabels (A := A) (W := W) d r n) :
    refinedTubeCellPartialEquiv d r H n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      Set.range (refinedTubeClosedCharacteristic d r H n j) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨ULift.up ⟨x, hx⟩,
      (refinedTubeCellPartialEquiv_closed_characteristic d r H n j
        (ULift.up ⟨x, hx⟩)).symm.trans hxy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.down.val, x.down.property,
      refinedTubeCellPartialEquiv_closed_characteristic d r H n j x⟩

private theorem refinedTubeOldCell_closed_image
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set A) n) :
    refinedTubeCellPartialEquiv (W := W) d r H n (Sum.inl j) '' Metric.closedBall 0 1 =
      oldIntoTubeSpace d H '' Topology.CWComplex.closedCell (C := (Set.univ : Set A)) n j := by
  change ((oldIntoTubeSpace d H) ∘ Topology.CWComplex.map (C := (Set.univ : Set A)) n j) '' Metric.closedBall 0 1 =
    oldIntoTubeSpace d H '' (Topology.CWComplex.map (C := (Set.univ : Set A)) n j '' Metric.closedBall 0 1)
  simp only [Set.image_image, Function.comp_def]

private theorem refinedTubeCell_closed_of_intersections
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (S : Set (refinedTubeSpace d H))
    (hS : ∀ (n : ℕ) (j : refinedTubeCellLabels (A := A) (W := W) d r n),
      IsClosed (S ∩ (refinedTubeCellPartialEquiv d r H n j '' Metric.closedBall 0 1))) :
    IsClosed S := by
  have hA : IsClosed ((oldIntoTubeSpace d H) ⁻¹' S) :=
    Topology.CWComplex.closed' (C := (Set.univ : Set A)) _ (Set.subset_univ _) (by
      intro n j
      have h := (hS n (Sum.inl j)).preimage (oldIntoTubeSpace d H).continuous
      rw [refinedTubeOldCell_closed_image] at h
      have hpre : (oldIntoTubeSpace d H) ⁻¹'
          (S ∩ (oldIntoTubeSpace d H '' Topology.CWComplex.closedCell (C := (Set.univ : Set A)) n j)) =
        (oldIntoTubeSpace d H) ⁻¹' S ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set A)) n j := by
        ext x
        constructor
        · rintro ⟨hxS, y, hy, hxy⟩
          refine ⟨hxS, ?_⟩
          rw [← (oldIntoTubeSpace_closed d H).injective hxy]
          exact hy
        · rintro ⟨hxS, hxC⟩
          exact ⟨hxS, x, hxC, rfl⟩
      rw [hpre] at h
      exact h)
  let J := pushout.inr (TopCat.ofHom H) (sideInclusion (I := I) d)
  have hJ : IsClosed (J ⁻¹' S) := by
    rw [isClosed_sigma_iff]
    intro i
    have h := hS (d + 1) (Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩)))
    rw [refinedTubeCellPartialEquiv_closed_range] at h
    change IsClosed (S ∩ Set.range (wholeTubeCharacteristic d H i)) at h
    rw [wholeTubeCharacteristic_range] at h
    have hp := h.preimage (originalCylinderMap d H i).continuous
    have hpre : (originalCylinderMap d H i) ⁻¹'
        (S ∩ Set.range (originalCylinderMap d H i)) =
      (originalCylinderMap d H i) ⁻¹' S := by
      ext p
      exact ⟨fun h => h.1, fun h => ⟨h, Set.mem_range_self p⟩⟩
    rw [hpre] at hp
    exact hp
  let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  apply (TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit S).mpr
  rintro (_ | _ | _)
  · change IsClosed (H ⁻¹' ((oldIntoTubeSpace d H) ⁻¹' S))
    exact hA.preimage H.continuous
  · exact hA
  · exact hJ

private theorem refinedTubeCell_union
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) :
    (⋃ (n : ℕ) (j : refinedTubeCellLabels (A := A) (W := W) d r n),
      refinedTubeCellPartialEquiv d r H n j '' Metric.closedBall 0 1) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
    rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with hz | hz
    · rcases hz with ⟨a, rfl⟩
      have ha : a ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set A) n),
          Topology.CWComplex.map n j '' Metric.closedBall 0 1 := by
        rw [Topology.CWComplex.union']
        exact Set.mem_univ a
      simp only [Set.mem_iUnion, Set.mem_image] at ha ⊢
      rcases ha with ⟨n, j, x, hx, hxa⟩
      exact ⟨n, Sum.inl j, x, hx, congrArg (oldIntoTubeSpace d H) hxa⟩
    · rcases hz with ⟨⟨i, p⟩, rfl⟩
      let x := originalCylinderDiskHomeomorph.{u} d p
      simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨d + 1, Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩)), x.down.val, x.down.property, ?_⟩
      exact (refinedTubeCellPartialEquiv_closed_characteristic d r H (d + 1) _ x).trans
        (wholeTubeCharacteristic_coordinates d H i p.1 p.2)

end ActualRefinedTubeCharacteristicConstruction47

end

/- This comparison uses the whole original interval/disk pair boundary.
The top whole-disk map here is a range/coverage utility; it is NOT a
replacement for the canonical top-cone CW cell family retained by
refinedTubeCellLabels. -/

noncomputable section

open CategoryTheory Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def topOriginalDiskMap (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).fst, refinedTubeSpace d H) :=
  (originalCylinderMap d H i).comp
    ⟨fun x => (x, 1), continuous_id.prodMk continuous_const⟩

private theorem wholeTubeBoundary_decomposition (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst)
    (hx : x ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map) :
    wholeTubeCharacteristic d H i x ∈
      Set.range (oldIntoTubeSpace d H) ∪
        (Set.range (bottomDiskCharacteristic d H i) ∪ Set.range (topOriginalDiskMap d H i)) := by
  let p := (originalCylinderDiskHomeomorph.{u} d).symm x
  let q : (Topology.CWComplex.intervalDiskPair.{u} d).fst :=
    ((TopCat.I.homeomorph.{u}).symm p.2, p.1)
  have hqx : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q = x := by
    change originalCylinderDiskHomeomorph.{u} d
      ((originalCylinderDiskHomeomorph.{u} d).symm x) = x
    exact Homeomorph.apply_symm_apply _ _
  have hq : q ∈ Set.range (Topology.CWComplex.intervalDiskPair.{u} d).map := by
    have h : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q ∈
        Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map := by
      rw [hqx]
      exact hx
    change q ∈ (Topology.CWComplex.intervalDiskPairHomeomorph.{u} d) ⁻¹'
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map at h
    rw [Topology.CWComplex.intervalDiskPairHomeomorph_preimage_range,
      ← Topology.CWComplex.range_intervalDiskPair_map] at h
    exact h
  have hparts := (Topology.CWComplex.mem_range_intervalDiskPair_map_iff d q).mp hq
  change originalCylinderMap d H i p ∈ _
  rcases hparts with (hzero | hone) | hside
  · have ht : p.2 = (0 : unitInterval) := by
      calc
        p.2 = (TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm p.2) :=
          ((TopCat.I.homeomorph.{u}).apply_symm_apply p.2).symm
        _ = (TopCat.I.homeomorph.{u}) (0 : TopCat.I.{u}) :=
          congrArg (TopCat.I.homeomorph.{u}) hzero
        _ = 0 := by simp
    refine Or.inr (Or.inl ⟨p.1, ?_⟩)
    change originalCylinderMap d H i (p.1, 0) = originalCylinderMap d H i p
    rw [← ht]
  · have ht : p.2 = (1 : unitInterval) := by
      calc
        p.2 = (TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm p.2) :=
          ((TopCat.I.homeomorph.{u}).apply_symm_apply p.2).symm
        _ = (TopCat.I.homeomorph.{u}) (1 : TopCat.I.{u}) :=
          congrArg (TopCat.I.homeomorph.{u}) hone
        _ = 1 := by simp
    refine Or.inr (Or.inr ⟨p.1, ?_⟩)
    change originalCylinderMap d H i (p.1, 1) = originalCylinderMap d H i p
    rw [← ht]
  · rcases hside with ⟨s, hs⟩
    refine Or.inl ⟨H ⟨i, (s, p.2)⟩, ?_⟩
    exact (originalCylinderMap_whole_side d H i s p.2).symm.trans
      (congrArg (fun y => originalCylinderMap d H i (y, p.2)) hs)

example (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst)
    (hx : x ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map) :
    wholeTubeCharacteristic d H i x ∈
      Set.range (oldIntoTubeSpace d H) ∪
        (Set.range (bottomDiskCharacteristic d H i) ∪ Set.range (topOriginalDiskMap d H i)) :=
  wholeTubeBoundary_decomposition d H i x hx

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after immutable26/27. The ENTIRE arbitrary
sigma family is embedded off its literal side. The old attaching homotopy
need not be injective. The full interval/disk boundary also forces the
open tube chart away from BOTH endpoint faces. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def wholeOffSideCylinderMap (d : ℕ) (H : C(sideSum (I := I) d, A)) :
    (Σ _ : I, cylinderOffSide.{u} d) → refinedTubeSpace d H :=
  fun x => originalCylinderMap d H x.fst x.snd.val

private theorem wholeOffSideCylinderMap_not_old (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (x : Σ _ : I, cylinderOffSide.{u} d) :
    wholeOffSideCylinderMap d H x ∉ Set.range (oldIntoTubeSpace d H) := by
  rintro ⟨a, ha⟩
  let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  let hflip := sq.flip.map (forget TopCat)
  have heq : hflip.cocone.inl (Sigma.mk x.fst x.snd.val) = hflip.cocone.inr a := by
    simpa only [hflip, sq, wholeOffSideCylinderMap, originalCylinderMap, oldIntoTubeSpace] using!
      ha.symm
  obtain ⟨s, hs, _⟩ :=
    (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hflip.isColimit
      (sideInclusion_closed d).injective (Sigma.mk x.fst x.snd.val) a).mp heq
  rcases s with ⟨j, y⟩
  change (⟨j, sideProductMap.{u} d y⟩ :
    Σ _ : I, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) =
      ⟨x.fst, x.snd.val⟩ at hs
  have hij : j = x.fst := (Sigma.mk.inj_iff.mp hs).1
  subst j
  have hxy : sideProductMap.{u} d y = x.snd.val := eq_of_heq ((Sigma.mk.inj_iff.mp hs).2)
  exact x.snd.property ⟨y.1, congrArg Prod.fst hxy⟩

private theorem wholeOffSideCylinderMap_isEmbedding (d : ℕ)
    (H : C(sideSum (I := I) d, A)) : IsEmbedding (wholeOffSideCylinderMap d H) := by
  let U : Set (refinedTubeSpace d H) := (Set.range (oldIntoTubeSpace d H))ᶜ
  have hU : IsOpen U := (oldIntoTubeSpace_closed d H).isClosed_range.isOpen_compl
  let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  let J := pushout.inr (TopCat.ofHom H) (sideInclusion (I := I) d)
  have hOld : (oldIntoTubeSpace d H) ⁻¹' U = ∅ := by
    ext x
    exact iff_false_intro (fun hx => hx (Set.mem_range_self x))
  have hSide : J ⁻¹' U ⊆ (Set.range (sideInclusion (I := I) d))ᶜ := by
    rintro x hx ⟨s, rfl⟩
    exact hx ⟨H s, ConcreteCategory.congr_hom sq.w s⟩
  let hh := TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout sq hU hOld hSide
  let γ : (Σ _ : I, cylinderOffSide.{u} d) → cylinderSum (I := I) d :=
    Sigma.map (id : I → I) (fun _ => Subtype.val)
  have hγ : IsEmbedding γ :=
    (Topology.isEmbedding_sigmaMap Function.injective_id).mpr (fun _ => IsEmbedding.subtypeVal)
  have hγU (x : Σ _ : I, cylinderOffSide.{u} d) : γ x ∈ J ⁻¹' U := by
    simpa only [γ, J, U, wholeOffSideCylinderMap, originalCylinderMap] using!
      wholeOffSideCylinderMap_not_old d H x
  let ψ : (Σ _ : I, cylinderOffSide.{u} d) → J ⁻¹' U := fun x => ⟨γ x, hγU x⟩
  have hψ : IsEmbedding ψ := hγ.codRestrict _ hγU
  simpa only [ψ, γ, J, wholeOffSideCylinderMap, originalCylinderMap, Function.comp_def] using!
    IsEmbedding.subtypeVal.comp (hh.isEmbedding.comp hψ)

private theorem originalCylinderMap_offSide_coordinates_eq (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i j : I)
    (x y : cylinderOffSide.{u} d)
    (h : originalCylinderMap d H i x.val = originalCylinderMap d H j y.val) :
    (⟨i, x⟩ : Σ _ : I, cylinderOffSide.{u} d) = ⟨j, y⟩ :=
  (wholeOffSideCylinderMap_isEmbedding d H).injective h

private theorem originalCylinderDiskHomeomorph_open_time_ne_endpoints (d : ℕ)
    (x : Metric.ball (0 : Fin (d + 1) → ℝ) 1) :
    ((originalCylinderDiskHomeomorph.{u} d).symm
      (openBallToOriginalDisk.{u} (d + 1) x)).2 ≠ (0 : unitInterval) ∧
    ((originalCylinderDiskHomeomorph.{u} d).symm
      (openBallToOriginalDisk.{u} (d + 1) x)).2 ≠ (1 : unitInterval) := by
  let y := openBallToOriginalDisk.{u} (d + 1) x
  let p := (originalCylinderDiskHomeomorph.{u} d).symm y
  let q : (Topology.CWComplex.intervalDiskPair.{u} d).fst :=
    ((TopCat.I.homeomorph.{u}).symm p.2, p.1)
  have hy : y ∉ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map :=
    openBallToOriginalDisk_not_side (d + 1) x
  have hq : q ∉ Set.range (Topology.CWComplex.intervalDiskPair.{u} d).map := by
    intro h
    have h' : q ∈ (Set.range (TopPair.intervalBoundaryPair.{u}).map).unionProd
        (Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map) := by
      rw [← Topology.CWComplex.range_intervalDiskPair_map]
      exact h
    have hb : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q ∈
        Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map := by
      change q ∈ (Topology.CWComplex.intervalDiskPairHomeomorph.{u} d) ⁻¹'
        Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map
      rw [Topology.CWComplex.intervalDiskPairHomeomorph_preimage_range]
      exact h'
    change originalCylinderDiskHomeomorph.{u} d p ∈
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map at hb
    rw [Homeomorph.apply_symm_apply] at hb
    exact hy hb
  constructor
  · intro h0
    apply hq
    apply (Topology.CWComplex.mem_range_intervalDiskPair_map_iff d q).mpr
    left
    left
    change (TopCat.I.homeomorph.{u}).symm p.2 = (0 : TopCat.I.{u})
    rw [h0]
    apply (TopCat.I.homeomorph.{u}).injective
    simp
  · intro h1
    apply hq
    apply (Topology.CWComplex.mem_range_intervalDiskPair_map_iff d q).mpr
    left
    right
    change (TopCat.I.homeomorph.{u}).symm p.2 = (1 : TopCat.I.{u})
    rw [h1]
    apply (TopCat.I.homeomorph.{u}).injective
    simp

example (d : ℕ) (H : C(sideSum (I := I) d, A)) (i j : I)
    (x y : cylinderOffSide.{u} d)
    (h : originalCylinderMap d H i x.val = originalCylinderMap d H j y.val) : i = j :=
  congrArg Sigma.fst (originalCylinderMap_offSide_coordinates_eq d H i j x y h)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after immutable26/27 and the whole off-side
geometry fragment. The full open-cell family is pairwise disjoint using
actual original disk/time coordinates and the canonical cone CW cells.
No CW structure on the new carrier or supplied disjointness is assumed. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

variable {I W : Type u} {A : TopCat.{u}}

private abbrev refinedTubeNewCellLabels (d : ℕ) (r : I → ℕ) (n : ℕ) : Type u :=
  {i : I // n = d} ⊕ ((Σ i : I, newTopConeCell (W := W) d (r i) n) ⊕ {i : I // n = d + 1})

private def newOpenCoordinates (d : ℕ) (r : I → ℕ) (n : ℕ)
    (j : refinedTubeNewCellLabels (W := W) d r n)
    (x : Metric.ball (0 : Fin n → ℝ) 1) : Σ _ : I, cylinderOffSide.{u} d := by
  rcases j with a | (a | a)
  · rcases a with ⟨i, hn⟩
    subst n
    exact ⟨i, ⟨(openBallToOriginalDisk.{u} d x, 0), openBallToOriginalDisk_not_side d x⟩⟩
  · rcases a with ⟨i, j⟩
    exact ⟨i, ⟨(refinedTopConeDiskCharacteristic (W := W) d (r i) n j.val
      (openBallToOriginalDisk.{u} n x), 1), newTopConeDisk_open_not_side d (r i) n j x⟩⟩
  · rcases a with ⟨i, hn⟩
    subst n
    exact ⟨i, ⟨(originalCylinderDiskHomeomorph.{u} d).symm
      (openBallToOriginalDisk.{u} (d + 1) x), originalCylinderDiskHomeomorph_open_not_side d x⟩⟩

private theorem newOpenCoordinates_value
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ) (n : ℕ)
    (H : C(sideSum (I := I) d, A))
    (j : refinedTubeNewCellLabels (W := W) d r n)
    (x : Metric.ball (0 : Fin n → ℝ) 1) :
    refinedTubeCellPartialEquiv d r H n (Sum.inr j) x.val =
      wholeOffSideCylinderMap d H (newOpenCoordinates d r n j x) := by
  rcases j with a | (a | a)
  · rcases a with ⟨i, hn⟩
    subst n
    exact refinedTubeCellPartialEquiv_closed_characteristic d r H d _
      (openBallToOriginalDisk.{u} d x)
  · rcases a with ⟨i, j⟩
    exact refinedTubeCellPartialEquiv_closed_characteristic d r H n _
      (openBallToOriginalDisk.{u} n x)
  · rcases a with ⟨i, hn⟩
    subst n
    exact refinedTubeCellPartialEquiv_closed_characteristic d r H (d + 1) _
      (openBallToOriginalDisk.{u} (d + 1) x)

private theorem cwCellIndex_eq_of_open_coordinates_eq
    {X : Type u} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (n m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n)
    (k : Topology.CWComplex.cell (Set.univ : Set X) m)
    (x : Metric.ball (0 : Fin n → ℝ) 1) (y : Metric.ball (0 : Fin m → ℝ) 1)
    (h : Topology.CWComplex.map n j x.val = Topology.CWComplex.map m k y.val) :
    (⟨n, j⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n) = ⟨m, k⟩ := by
  by_contra hne
  have hx : Topology.CWComplex.map (C := (Set.univ : Set X)) n j x.val ∈
      Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
    refine ⟨x.val, x.property, ?_⟩
    simp only [Topology.CWComplex.map_def]
  have hy : Topology.CWComplex.map (C := (Set.univ : Set X)) n j x.val ∈
      Topology.CWComplex.openCell (C := (Set.univ : Set X)) m k := by
    refine ⟨y.val, y.property, ?_⟩
    simpa only [Topology.CWComplex.map_def] using h.symm
  exact (Topology.CWComplex.disjoint_openCell_of_ne hne).notMem_of_mem_left hx hy

private theorem newOpenCoordinates_label_eq (d : ℕ) (r : I → ℕ) (n m : ℕ)
    (a : refinedTubeNewCellLabels (W := W) d r n)
    (b : refinedTubeNewCellLabels (W := W) d r m)
    (x : Metric.ball (0 : Fin n → ℝ) 1) (y : Metric.ball (0 : Fin m → ℝ) 1)
    (h : newOpenCoordinates d r n a x = newOpenCoordinates d r m b y) :
    (⟨n, a⟩ : Σ n, refinedTubeNewCellLabels (W := W) d r n) = ⟨m, b⟩ := by
  have htime := congrArg (fun z : Σ _ : I, cylinderOffSide.{u} d => z.snd.val.2) h
  have hindex := congrArg Sigma.fst h
  rcases a with a | (a | a)
  · rcases a with ⟨i, hn⟩
    subst n
    rcases b with b | (b | b)
    · rcases b with ⟨j, hm⟩
      subst m
      change i = j at hindex
      subst j
      rfl
    · rcases b with ⟨j, b⟩
      change (0 : unitInterval) = 1 at htime
      exact False.elim (zero_ne_one htime)
    · rcases b with ⟨j, hm⟩
      subst m
      change (0 : unitInterval) =
        ((originalCylinderDiskHomeomorph.{u} d).symm
          (openBallToOriginalDisk.{u} (d + 1) y)).2 at htime
      exact False.elim ((originalCylinderDiskHomeomorph_open_time_ne_endpoints d y).1 htime.symm)
  · rcases a with ⟨i, a⟩
    rcases b with b | (b | b)
    · rcases b with ⟨j, hm⟩
      subst m
      change (1 : unitInterval) = 0 at htime
      exact False.elim (zero_ne_one htime.symm)
    · rcases b with ⟨j, b⟩
      change i = j at hindex
      subst j
      let c := MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) (r i)) W)
      have hspace := congrArg (fun z : Σ _ : I, cylinderOffSide.{u} d => z.snd.val.1) h
      change refinedTopConeDiskCharacteristic (W := W) d (r i) n a.val
          (openBallToOriginalDisk.{u} n x) =
        refinedTopConeDiskCharacteristic (W := W) d (r i) m b.val
          (openBallToOriginalDisk.{u} m y) at hspace
      have hcell := congrArg (originalDiskToCopiedConeComplex (W := W) d (r i)) hspace
      rw [refinedTopConeDiskCharacteristic_whole, refinedTopConeDiskCharacteristic_whole] at hcell
      have hlabels : (⟨n, a.val⟩ : Σ n, refinedTopConeCell (W := W) d (r i) n) = ⟨m, b.val⟩ :=
        cwCellIndex_eq_of_open_coordinates_eq (X := c.Realization) n m a.val b.val x y hcell
      have hnm : n = m := congrArg Sigma.fst hlabels
      subst m
      have hab : a.val = b.val := eq_of_heq (Sigma.mk.inj_iff.mp hlabels).2
      have hab' : a = b := Subtype.ext hab
      subst b
      rfl
    · rcases b with ⟨j, hm⟩
      subst m
      change (1 : unitInterval) =
        ((originalCylinderDiskHomeomorph.{u} d).symm
          (openBallToOriginalDisk.{u} (d + 1) y)).2 at htime
      exact False.elim ((originalCylinderDiskHomeomorph_open_time_ne_endpoints d y).2 htime.symm)
  · rcases a with ⟨i, hn⟩
    subst n
    rcases b with b | (b | b)
    · rcases b with ⟨j, hm⟩
      subst m
      change ((originalCylinderDiskHomeomorph.{u} d).symm
        (openBallToOriginalDisk.{u} (d + 1) x)).2 = (0 : unitInterval) at htime
      exact False.elim ((originalCylinderDiskHomeomorph_open_time_ne_endpoints d x).1 htime)
    · rcases b with ⟨j, b⟩
      change ((originalCylinderDiskHomeomorph.{u} d).symm
        (openBallToOriginalDisk.{u} (d + 1) x)).2 = (1 : unitInterval) at htime
      exact False.elim ((originalCylinderDiskHomeomorph_open_time_ne_endpoints d x).2 htime)
    · rcases b with ⟨j, hm⟩
      subst m
      change i = j at hindex
      subst j
      rfl

private theorem refinedTubeOpenCoordinates_label_eq
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n m : ℕ)
    (a : refinedTubeCellLabels (A := A) (W := W) d r n)
    (b : refinedTubeCellLabels (A := A) (W := W) d r m)
    (x : Metric.ball (0 : Fin n → ℝ) 1) (y : Metric.ball (0 : Fin m → ℝ) 1)
    (h : refinedTubeCellPartialEquiv d r H n a x.val =
      refinedTubeCellPartialEquiv d r H m b y.val) :
    (⟨n, a⟩ : Σ n, refinedTubeCellLabels (A := A) (W := W) d r n) = ⟨m, b⟩ := by
  rcases a with a | a
  · rcases b with b | b
    · change oldIntoTubeSpace d H (Topology.CWComplex.map n a x.val) =
        oldIntoTubeSpace d H (Topology.CWComplex.map m b y.val) at h
      have hp := (oldIntoTubeSpace_closed d H).injective h
      have hi := cwCellIndex_eq_of_open_coordinates_eq n m a b x y hp
      have hnm : n = m := congrArg Sigma.fst hi
      subst m
      have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.mp hi).2
      subst b
      rfl
    · have hb := newOpenCoordinates_value d r m H b y
      have hmem : wholeOffSideCylinderMap d H (newOpenCoordinates d r m b y) ∈
          Set.range (oldIntoTubeSpace d H) := by
        refine ⟨Topology.CWComplex.map n a x.val, ?_⟩
        exact h.trans hb
      exact False.elim (wholeOffSideCylinderMap_not_old d H _ hmem)
  · rcases b with b | b
    · have ha := newOpenCoordinates_value d r n H a x
      have hmem : wholeOffSideCylinderMap d H (newOpenCoordinates d r n a x) ∈
          Set.range (oldIntoTubeSpace d H) := by
        refine ⟨Topology.CWComplex.map m b y.val, ?_⟩
        exact h.symm.trans ha
      exact False.elim (wholeOffSideCylinderMap_not_old d H _ hmem)
    · have ha := newOpenCoordinates_value d r n H a x
      have hb := newOpenCoordinates_value d r m H b y
      have hcoord : newOpenCoordinates d r n a x = newOpenCoordinates d r m b y :=
        (wholeOffSideCylinderMap_isEmbedding d H).injective (ha.symm.trans (h.trans hb))
      have hi := newOpenCoordinates_label_eq d r n m a b x y hcoord
      have hnm : n = m := congrArg Sigma.fst hi
      subst m
      have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.mp hi).2
      subst b
      rfl

private theorem refinedTubeCell_pairwiseDisjoint
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) :
    (Set.univ : Set (Σ n, refinedTubeCellLabels (A := A) (W := W) d r n)).PairwiseDisjoint
      (fun c => refinedTubeCellPartialEquiv d r H c.fst c.snd '' Metric.ball 0 1) := by
  intro c _ e _ hne
  change Disjoint
    (refinedTubeCellPartialEquiv (W := W) d r H c.fst c.snd '' Metric.ball 0 1)
    (refinedTubeCellPartialEquiv (W := W) d r H e.fst e.snd '' Metric.ball 0 1)
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  exact hne (refinedTubeOpenCoordinates_label_eq d r H c.fst e.fst c.snd e.snd
    ⟨x, hx⟩ ⟨y, hy⟩ (hxz.trans hyz.symm))

end ActualRefinedTubeCharacteristicConstruction47

end

/- The cone base uses the neutral canonical relabeling and inclusion packages.
Surjectivity of relabeling identifies its complete canonical cell-label range,
and the package preserves every whole original closed characteristic disk. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u



namespace ActualConeBaseClassicalSubcomplexConstruction47


variable {V : Type u}

private theorem coneBase_as_relabel_inclusion (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) :
    Realization.inclusion (MappingCylinder.cone_base_le P)
        (MappingCylinder.relabelHomeomorph P Function.Embedding.inl x) =
      (MappingCylinder.coneBaseMorphism P).realization x := by
  apply Realization.ext
  change (MappingCylinder.relabelHomeomorph P Function.Embedding.inl x).point =
    ((MappingCylinder.coneBaseMorphism P).realization x).point
  exact (MappingCylinder.relabelMorphism_point P Function.Embedding.inl x).trans
    (MappingCylinder.coneBaseMorphism_point P x).symm

private def coneBaseClassicalSubcomplex (P : PreAbstractSimplicialComplex V) :
    Σ κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set (MappingCylinder.coneComplex P).Realization) n,
      {A : Topology.CWComplex.Subcomplex (Set.univ : Set (MappingCylinder.coneComplex P).Realization) //
        (A : Set (MappingCylinder.coneComplex P).Realization) =
          Set.range (MappingCylinder.coneBaseMorphism P).realization ∧
        (∀ n, A.I n = Set.range (κ n)) ∧
        ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
          (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
          (MappingCylinder.coneBaseMorphism P).realization
              (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
            Topology.CWComplex.map
              (C := (Set.univ : Set (MappingCylinder.coneComplex P).Realization)) n (κ n j) x.down.val} := by
  let r := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabel P
    (Function.Embedding.inl : V ↪ V ⊕ PUnit.{u + 1})
  let i := PreAbstractSimplicialComplex.Realization.classicalSubcomplexOfInclusion (MappingCylinder.cone_base_le P)
  let κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set (MappingCylinder.coneComplex P).Realization) n :=
    fun n => (r.fst n).trans (i.fst n)
  refine ⟨κ, ⟨i.snd.val, ?_, ?_, ?_⟩⟩
  · rw [i.snd.property.1]
    ext z
    constructor
    · rintro ⟨y, hy⟩
      let R := MappingCylinder.relabelHomeomorph P
        (Function.Embedding.inl : V ↪ V ⊕ PUnit.{u + 1})
      refine ⟨R.symm y, ?_⟩
      exact (coneBase_as_relabel_inclusion P (R.symm y)).symm.trans
        ((congrArg (Realization.inclusion (MappingCylinder.cone_base_le P))
          (R.apply_symm_apply y)).trans hy)
    · rintro ⟨x, hx⟩
      exact ⟨MappingCylinder.relabelHomeomorph P Function.Embedding.inl x,
        (coneBase_as_relabel_inclusion P x).trans hx⟩
  · intro n
    rw [i.snd.property.2.1 n]
    ext j
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabel_surjective P
        (Function.Embedding.inl : V ↪ V ⊕ PUnit.{u + 1}) n a
      refine ⟨b, ?_⟩
      change i.fst n (r.fst n b) = j
      rw [hb]
      exact ha
    · rintro ⟨b, hb⟩
      exact ⟨r.fst n b, hb⟩
  · intro n j x
    calc
      _ = Realization.inclusion (MappingCylinder.cone_base_le P)
          (MappingCylinder.relabelHomeomorph P Function.Embedding.inl
            (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val)) :=
        (coneBase_as_relabel_inclusion P _).symm
      _ = Realization.inclusion (MappingCylinder.cone_base_le P)
          (Topology.CWComplex.map
            (C := (Set.univ : Set (MappingCylinder.relabelComplex P
              (Function.Embedding.inl : V ↪ V ⊕ PUnit.{u + 1})).Realization)) n (r.fst n j) x.down.val) :=
        congrArg (Realization.inclusion (MappingCylinder.cone_base_le P)) (r.snd n j x)
      _ = _ := i.snd.property.2.2 n (r.fst n j) x

example (P : PreAbstractSimplicialComplex V) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    let d := coneBaseClassicalSubcomplex P
    (MappingCylinder.coneBaseMorphism P).realization
        (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
      Topology.CWComplex.map
        (C := (Set.univ : Set (MappingCylinder.coneComplex P).Realization)) n (d.fst n j) x.down.val :=
  (coneBaseClassicalSubcomplex P).snd.property.2.2 n j x

end ActualConeBaseClassicalSubcomplexConstruction47

end

/- Same-module private source after26/27/28 and the actual cone-base
package. g, κg, hg and htop are the INTERNALLY CONSTRUCTED copied-domain
embedding, its exact closed-disk labels and the endpoint of the original
three-piece attaching homotopy. They are not final X-only premises.
No frontier or CW structure on the new tube carrier is supplied. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction ActualConeBaseClassicalSubcomplexConstruction47

variable {I W : Type u} {A : TopCat.{u}}

private abbrev copiedSphereDomain (d r : ℕ) :=
  MappingCylinder.domainComplex (subdivisionIter (SphereTriangulation.complex d) r) W

private def actualTopBaseData (d r : ℕ) :=
  coneBaseClassicalSubcomplex (copiedSphereDomain (W := W) d r)

private def topCellTransfer
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ) (i : I)
    (κg : ∀ n, Topology.CWComplex.cell
        (Set.univ : Set (copiedSphereDomain (W := W) d (r i)).Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set A) n)
    (n : ℕ) (j : refinedTopConeCell (W := W) d (r i) n) :
    refinedTubeCellLabels (A := A) (W := W) d r n := by
  classical
  let B := actualTopBaseData (W := W) d (r i)
  exact if h : j ∈ Set.range (B.fst n) then Sum.inl (κg n (Classical.choose h))
  else Sum.inr (Sum.inr (Sum.inl
    ⟨i, ⟨j, by
      have hj : j ∉ B.snd.val.I n := by
        rw [B.snd.property.2.1 n]
        exact h
      have hdis := B.snd.val.disjoint_openCell_subcomplex_of_notMem hj
      rw [B.snd.property.1] at hdis
      exact hdis⟩⟩))

private theorem topCellTransfer_closed_characteristic
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ) (i : I)
    (H : C(sideSum (I := I) d, A))
    (g : C((copiedSphereDomain (W := W) d (r i)).Realization, A))
    (κg : ∀ n, Topology.CWComplex.cell
        (Set.univ : Set (copiedSphereDomain (W := W) d (r i)).Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set A) n)
    (hg : ∀ n j (q : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
      g (Topology.CWComplex.map n j q.down.val) = Topology.CWComplex.map n (κg n j) q.down.val)
    (htop : ∀ s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd,
      H ⟨i, (s, 1)⟩ = g (originalSphereToCopiedDomain (W := W) d (r i) s))
    (n : ℕ) (j : refinedTopConeCell (W := W) d (r i) n)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst) :
    refinedTubeCellPartialEquiv (W := W) d r H n (topCellTransfer (W := W) d r i κg n j) q.down.val =
      originalCylinderMap d H i
        (refinedTopConeDiskCharacteristic (W := W) d (r i) n j q, 1) := by
  classical
  let B := actualTopBaseData (W := W) d (r i)
  rw [refinedTubeCellPartialEquiv_closed_characteristic (W := W)]
  dsimp only [topCellTransfer]
  by_cases hj : j ∈ Set.range (B.fst n)
  · let b := Classical.choose hj
    have hb : B.fst n b = j := Classical.choose_spec hj
    let y := Topology.CWComplex.map
      (C := (Set.univ : Set (copiedSphereDomain (W := W) d (r i)).Realization)) n b q.down.val
    let s := (originalSphereToCopiedDomain (W := W) d (r i)).symm y
    have hs : originalSphereToCopiedDomain (W := W) d (r i) s = y :=
      (originalSphereToCopiedDomain (W := W) d (r i)).apply_symm_apply y
    have hbase : (MappingCylinder.coneBaseMorphism
        (copiedSphereDomain (W := W) d (r i))).realization y =
      Topology.CWComplex.map
        (C := (Set.univ : Set (MappingCylinder.coneComplex
          (copiedSphereDomain (W := W) d (r i))).Realization)) n j q.down.val := by
      have h := B.snd.property.2.2 n b q
      rw [hb] at h
      exact h
    have he : originalDiskToCopiedConeComplex (W := W) d (r i)
        ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s) =
      Topology.CWComplex.map
        (C := (Set.univ : Set (MappingCylinder.coneComplex
          (copiedSphereDomain (W := W) d (r i))).Realization)) n j q.down.val :=
      (originalDiskToCopiedConeComplex_boundary (W := W) d (r i) s).trans
        ((congrArg (MappingCylinder.coneBaseMorphism
          (copiedSphereDomain (W := W) d (r i))).realization hs).trans hbase)
    have hp : (Topology.CWComplex.classicalCellDiskPair.{u} d).map s =
        refinedTopConeDiskCharacteristic (W := W) d (r i) n j q :=
      (originalDiskToCopiedConeComplex (W := W) d (r i)).injective
        (he.trans (refinedTopConeDiskCharacteristic_whole (W := W) d (r i) n j q).symm)
    have ht : H ⟨i, (s, 1)⟩ = g y := (htop s).trans (congrArg g hs)
    dsimp only [B] at hj
    simp only [dite_eq_left hj, refinedTubeClosedCharacteristic, oldCellClosedCharacteristic]
    change oldIntoTubeSpace d H
      (Topology.CWComplex.map (C := (Set.univ : Set A)) n (κg n b) q.down.val) = _
    calc
      _ = oldIntoTubeSpace d H (g y) := congrArg (oldIntoTubeSpace d H) (hg n b q).symm
      _ = oldIntoTubeSpace d H (H ⟨i, (s, 1)⟩) := congrArg (oldIntoTubeSpace d H) ht.symm
      _ = originalCylinderMap d H i ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, 1) :=
        (originalCylinderMap_whole_side d H i s 1).symm
      _ = _ := congrArg (fun x => originalCylinderMap d H i (x, 1)) hp
  · dsimp only [B] at hj
    simp only [dite_eq_right hj, refinedTubeClosedCharacteristic, topConeCharacteristic,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk]

private theorem newTopCell_mapsTo_finite_lower
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ) (i : I)
    (H : C(sideSum (I := I) d, A))
    (g : C((copiedSphereDomain (W := W) d (r i)).Realization, A))
    (κg : ∀ n, Topology.CWComplex.cell
        (Set.univ : Set (copiedSphereDomain (W := W) d (r i)).Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set A) n)
    (hg : ∀ n j (q : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
      g (Topology.CWComplex.map n j q.down.val) = Topology.CWComplex.map n (κg n j) q.down.val)
    (htop : ∀ s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd,
      H ⟨i, (s, 1)⟩ = g (originalSphereToCopiedDomain (W := W) d (r i) s))
    (n : ℕ) (j : newTopConeCell (W := W) d (r i) n) :
    ∃ J : ∀ m, Finset (refinedTubeCellLabels (A := A) (W := W) d r m),
      Set.MapsTo
        (refinedTubeCellPartialEquiv d r H n (Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩))))
        (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (a ∈ J m), refinedTubeCellPartialEquiv d r H m a '' Metric.closedBall 0 1) := by
  classical
  let c := MappingCylinder.coneComplex (copiedSphereDomain (W := W) d (r i))
  obtain ⟨J, hJ⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set c.Realization)) n j.val
  refine ⟨fun m => (J m).image (topCellTransfer d r i κg m), ?_⟩
  intro x hx
  have hm := hJ hx
  simp only [Set.mem_iUnion, Set.mem_image] at hm ⊢
  rcases hm with ⟨m, hmn, a, ha, y, hy, hxy⟩
  refine ⟨m, hmn, topCellTransfer d r i κg m a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, y, hy, ?_⟩
  have hlow := topCellTransfer_closed_characteristic d r i H g κg hg htop m a (ULift.up ⟨y, hy⟩)
  change refinedTubeCellPartialEquiv d r H m (topCellTransfer d r i κg m a) y =
    originalCylinderMap d H i
      ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm
        (Topology.CWComplex.map (C := (Set.univ : Set c.Realization)) n j.val x), 1)
  exact hlow.trans (congrArg (fun z : c.Realization => originalCylinderMap d H i
    ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm z, 1)) hxy)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after26–29. This retains which OLD points
come from the actual individual compact side slice H_i. The arbitrary
sigma family is not assumed compact. This stronger boundary carrier is
needed for finite tube frontiers; the whole old-stage range alone is too
large for that purpose. -/

noncomputable section

open CategoryTheory Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def tubeSideSlice (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval, A) :=
  ⟨fun p => H ⟨i, p⟩, H.continuous.comp continuous_sigmaMk⟩

private theorem wholeTubeBoundary_compact_side_carrier (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst)
    (hx : x ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map) :
    wholeTubeCharacteristic d H i x ∈
      (oldIntoTubeSpace d H '' Set.range (tubeSideSlice d H i)) ∪
        (Set.range (bottomDiskCharacteristic d H i) ∪ Set.range (topOriginalDiskMap d H i)) := by
  let p := (originalCylinderDiskHomeomorph.{u} d).symm x
  let q : (Topology.CWComplex.intervalDiskPair.{u} d).fst :=
    ((TopCat.I.homeomorph.{u}).symm p.2, p.1)
  have hqx : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q = x := by
    change originalCylinderDiskHomeomorph.{u} d
      ((originalCylinderDiskHomeomorph.{u} d).symm x) = x
    exact Homeomorph.apply_symm_apply _ _
  have hq : q ∈ Set.range (Topology.CWComplex.intervalDiskPair.{u} d).map := by
    have h : Topology.CWComplex.intervalDiskPairHomeomorph.{u} d q ∈
        Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map := by
      rw [hqx]
      exact hx
    change q ∈ (Topology.CWComplex.intervalDiskPairHomeomorph.{u} d) ⁻¹'
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map at h
    rw [Topology.CWComplex.intervalDiskPairHomeomorph_preimage_range,
      ← Topology.CWComplex.range_intervalDiskPair_map] at h
    exact h
  change originalCylinderMap d H i p ∈ _
  rcases (Topology.CWComplex.mem_range_intervalDiskPair_map_iff d q).mp hq with
    (hzero | hone) | hside
  · have ht : p.2 = (0 : unitInterval) := by
      calc
        p.2 = (TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm p.2) :=
          ((TopCat.I.homeomorph.{u}).apply_symm_apply p.2).symm
        _ = (TopCat.I.homeomorph.{u}) (0 : TopCat.I.{u}) :=
          congrArg (TopCat.I.homeomorph.{u}) hzero
        _ = 0 := by simp
    refine Or.inr (Or.inl ⟨p.1, ?_⟩)
    change originalCylinderMap d H i (p.1, 0) = originalCylinderMap d H i p
    rw [← ht]
  · have ht : p.2 = (1 : unitInterval) := by
      calc
        p.2 = (TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm p.2) :=
          ((TopCat.I.homeomorph.{u}).apply_symm_apply p.2).symm
        _ = (TopCat.I.homeomorph.{u}) (1 : TopCat.I.{u}) :=
          congrArg (TopCat.I.homeomorph.{u}) hone
        _ = 1 := by simp
    refine Or.inr (Or.inr ⟨p.1, ?_⟩)
    change originalCylinderMap d H i (p.1, 1) = originalCylinderMap d H i p
    rw [← ht]
  · rcases hside with ⟨s, hs⟩
    refine Or.inl ⟨H ⟨i, (s, p.2)⟩, ⟨(s, p.2), rfl⟩, ?_⟩
    exact (originalCylinderMap_whole_side d H i s p.2).symm.trans
      (congrArg (fun y => originalCylinderMap d H i (y, p.2)) hs)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after15-source-variant and26–30. The
individual compact side image, one original bottom disk and ALL canonical
top-cone cells give a finite tube frontier. The old-stage bound is the
recursively constructed common/intermediate bound, not a new final X-only
premise. Canonical cone dimensions use the actual derived sphere face bound.
No global family compactness, countability or supplied frontier is used. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction ClassicalCWCompactCarrierConstruction47

variable {I W : Type u} {A : TopCat.{u}}

private theorem finiteDegreeFiber {C : ℕ → Type u} (J : Finset (Σ n, C n)) (n : ℕ) :
    ((Sigma.mk n) ⁻¹' (J : Set (Σ n, C n))).Finite :=
  Set.Finite.preimage (f := Sigma.mk n)
    (by intro a _ b _ h; exact sigma_mk_injective h) J.finite_toSet

private def degreeFinset {C : ℕ → Type u} (J : Finset (Σ n, C n)) (n : ℕ) : Finset (C n) :=
  (finiteDegreeFiber J n).toFinset

private theorem mem_degreeFinset {C : ℕ → Type u} (J : Finset (Σ n, C n)) (n : ℕ) (a : C n) :
    a ∈ degreeFinset J n ↔ (⟨n, a⟩ : Σ n, C n) ∈ J :=
  (finiteDegreeFiber J n).mem_toFinset

private theorem wholeTube_mapsTo_finite_lower
    [Topology.CWComplex (Set.univ : Set A)] [T2Space A]
    (d : ℕ) (r : I → ℕ) (i : I) (H : C(sideSum (I := I) d, A))
    (g : C((copiedSphereDomain (W := W) d (r i)).Realization, A))
    (κg : ∀ n, Topology.CWComplex.cell
        (Set.univ : Set (copiedSphereDomain (W := W) d (r i)).Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set A) n)
    (hg : ∀ n j (q : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
      g (Topology.CWComplex.map n j q.down.val) = Topology.CWComplex.map n (κg n j) q.down.val)
    (htop : ∀ s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd,
      H ⟨i, (s, 1)⟩ = g (originalSphereToCopiedDomain (W := W) d (r i) s))
    (hbound : ∀ n (a : Topology.CWComplex.cell (Set.univ : Set A) n), n ≤ d) :
    ∃ F : ∀ m, Finset (refinedTubeCellLabels (A := A) (W := W) d r m),
      Set.MapsTo
        (refinedTubeCellPartialEquiv (W := W) d r H (d + 1) (Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩))))
        (Metric.sphere (0 : Fin (d + 1) → ℝ) 1)
        (⋃ (m < d + 1) (a ∈ F m), refinedTubeCellPartialEquiv (W := W) d r H m a '' Metric.closedBall 0 1) := by
  classical
  let : CompactSpace ((Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) := by
    change CompactSpace (ULift.{u} (Metric.sphere (0 : Fin d → ℝ) 1) × unitInterval)
    infer_instance
  obtain ⟨JS, hJS⟩ := compactDomain_classical_finite_carrier (X := A) (tubeSideSlice d H i)
  let : _root_.Finite (Σ n, refinedTopConeCell (W := W) d (r i) n) :=
    finiteRefinedTopConeCellsViaCompactness (W := W) d (r i)
  let : Fintype (Σ n, refinedTopConeCell (W := W) d (r i) n) := Fintype.ofFinite _
  let oldTag : (Σ n, Topology.CWComplex.cell (Set.univ : Set A) n) →
      (Σ n, refinedTubeCellLabels (A := A) (W := W) d r n) := fun c => ⟨c.fst, Sum.inl c.snd⟩
  let topTag : (Σ n, refinedTopConeCell (W := W) d (r i) n) →
      (Σ n, refinedTubeCellLabels (A := A) (W := W) d r n) :=
    fun c => ⟨c.fst, topCellTransfer d r i κg c.fst c.snd⟩
  let bottom : (Σ n, refinedTubeCellLabels (A := A) (W := W) d r n) :=
    ⟨d, Sum.inr (Sum.inl ⟨i, rfl⟩)⟩
  let JT := Finset.univ.image topTag
  let J : Finset (Σ n, refinedTubeCellLabels (A := A) (W := W) d r n) :=
    JS.image oldTag ∪ insert bottom JT
  have hdim : ∀ c ∈ J, c.fst < d + 1 := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_image.mp hc with ⟨a, _, rfl⟩
      exact Nat.lt_succ_of_le (hbound a.fst a.snd)
    · rcases Finset.mem_insert.mp hc with h | h
      · subst c
        exact Nat.lt_succ_self d
      · rcases Finset.mem_image.mp h with ⟨a, _, rfl⟩
        exact Nat.lt_succ_of_le (refinedTopConeCell_dimension_bound d (r i) a.fst a.snd)
  have hcarrier : Set.MapsTo
      (refinedTubeCellPartialEquiv (W := W) d r H (d + 1) (Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩))))
      (Metric.sphere (0 : Fin (d + 1) → ℝ) 1)
      (⋃ c ∈ J, refinedTubeCellPartialEquiv (W := W) d r H c.fst c.snd '' Metric.closedBall 0 1) := by
    intro x hx
    let q : (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).fst :=
      ULift.up ⟨x, Metric.sphere_subset_closedBall hx⟩
    have hq : q ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} (d + 1)).map :=
      ⟨ULift.up ⟨x, hx⟩, rfl⟩
    have hval : refinedTubeCellPartialEquiv (W := W) d r H (d + 1)
        (Sum.inr (Sum.inr (Sum.inr ⟨i, rfl⟩))) x = wholeTubeCharacteristic d H i q :=
      refinedTubeCellPartialEquiv_closed_characteristic d r H (d + 1) _ q
    rw [hval]
    rcases wholeTubeBoundary_compact_side_carrier d H i q hq with hside | (hbottom | htopDisk)
    · rcases hside with ⟨y, hy, hyz⟩
      have h := hJS hy
      simp only [Set.mem_iUnion] at h
      rcases h with ⟨a, ha, hya⟩
      rcases hya with ⟨z, hz, hzy⟩
      refine Set.mem_iUnion.mpr ⟨oldTag a, Set.mem_iUnion.mpr ⟨?_, z, hz, ?_⟩⟩
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
      · exact (congrArg (oldIntoTubeSpace d H) hzy).trans hyz
    · rcases hbottom with ⟨y, hy⟩
      refine Set.mem_iUnion.mpr ⟨bottom, Set.mem_iUnion.mpr ⟨?_, y.down.val, y.down.property, ?_⟩⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _))
      · exact (refinedTubeCellPartialEquiv_closed_characteristic d r H d _ y).trans hy
    · rcases htopDisk with ⟨y, hy⟩
      let c := MappingCylinder.coneComplex (copiedSphereDomain (W := W) d (r i))
      let e := originalDiskToCopiedConeComplex (W := W) d (r i)
      have he : e y ∈ ⋃ (n : ℕ) (a : Topology.CWComplex.cell (Set.univ : Set c.Realization) n),
          Topology.CWComplex.map n a '' Metric.closedBall 0 1 := by
        rw [Topology.CWComplex.union']
        exact Set.mem_univ _
      simp only [Set.mem_iUnion, Set.mem_image] at he
      rcases he with ⟨n, a, z, hz, hza⟩
      refine Set.mem_iUnion.mpr ⟨topTag ⟨n, a⟩, Set.mem_iUnion.mpr ⟨?_, z, hz, ?_⟩⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨⟨n, a⟩, Finset.mem_univ _, rfl⟩)))
      · have hp : refinedTopConeDiskCharacteristic (W := W) d (r i) n a (ULift.up ⟨z, hz⟩) = y :=
          e.injective ((refinedTopConeDiskCharacteristic_whole
            (W := W) d (r i) n a (ULift.up ⟨z, hz⟩)).trans hza)
        exact (topCellTransfer_closed_characteristic d r i H g κg hg htop n a
          (ULift.up ⟨z, hz⟩)).trans
          ((congrArg (fun p => originalCylinderMap d H i (p, 1)) hp).trans hy)
  refine ⟨degreeFinset J, ?_⟩
  intro x hx
  have h := hcarrier hx
  simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
  rcases h with ⟨⟨m, a⟩, ha, y, hy, hyx⟩
  exact ⟨m, hdim ⟨m, a⟩ ha, a, (mem_degreeFinset J m a).mpr ha, y, hy, hyx⟩

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after26–30. The bottom frontier is derived
from the GIVEN ORIGINAL CW cell and its literal attaching map to the
original strict skeleton. g0/κ0 and their whole-disk equations are the
internally constructed original end embedding into the intermediate stage;
the final X-only construction must construct them, not assume them. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {W : Type u} {X A : TopCat.{u}}

private def originalLowerDiskToSkeleton [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    (d m : ℕ) (hm : m < d) (j : Topology.CWComplex.cell (Set.univ : Set X) m) :
    (classicalCellDiskPair.{u} m).fst ⟶ skeletonTop X d := by
  have hsk : (skeletonLT (Set.univ : Set X) ((m + 1 : ℕ) : ℕ∞) : Set X) ⊆
      (skeletonLT (Set.univ : Set X) (d : ℕ∞) : Set X) :=
    skeletonLT_mono (C := (Set.univ : Set X)) (n := (d : ℕ∞))
      (m := ((m + 1 : ℕ) : ℕ∞)) (by exact_mod_cast Nat.succ_le_iff.mpr hm)
  exact TopCat.ofHom
    { toFun := fun q => ⟨characteristicDiskMap m j q,
        hsk (closedCell_subset_skeletonLT m j ⟨q.down.val, q.down.property, rfl⟩)⟩
      continuous_toFun := (characteristicDiskMap m j).hom.continuous.subtype_mk _ }

private theorem oldCell_mapsTo_finite_lower {I : Type u}
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set A) n) :
    ∃ F : ∀ m, Finset (refinedTubeCellLabels (A := A) (W := W) d r m),
      Set.MapsTo (refinedTubeCellPartialEquiv (W := W) d r H n (Sum.inl j))
        (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (a ∈ F m), refinedTubeCellPartialEquiv (W := W) d r H m a '' Metric.closedBall 0 1) := by
  classical
  obtain ⟨F, hF⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set A)) n j
  refine ⟨fun m => (F m).image Sum.inl, ?_⟩
  intro x hx
  have h := hF hx
  simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
  rcases h with ⟨m, hmn, a, ha, y, hy, hyx⟩
  exact ⟨m, hmn, Sum.inl a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
    y, hy, congrArg (oldIntoTubeSpace d H) hyx⟩

private theorem originalBottomCell_mapsTo_finite_lower
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex (Set.univ : Set A)] (d : ℕ)
    (r : Topology.CWComplex.cell (Set.univ : Set X) d → ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (i : Topology.CWComplex.cell (Set.univ : Set X) d)
    (g0 : C(skeletonTop X d, A))
    (κ0 : ∀ m, m < d → Topology.CWComplex.cell (Set.univ : Set X) m ↪
      Topology.CWComplex.cell (Set.univ : Set A) m)
    (hg0 : ∀ m (hm : m < d) j (q : (classicalCellDiskPair.{u} m).fst),
      g0 (originalLowerDiskToSkeleton d m hm j q) =
        Topology.CWComplex.map m (κ0 m hm j) q.down.val)
    (hstart : ∀ s : (classicalCellDiskPair.{u} d).snd,
      H ⟨i, (s, 0)⟩ = g0 (characteristicSphereToSkeleton d i s)) :
    ∃ F : ∀ m, Finset (refinedTubeCellLabels (A := A) (W := W) d r m),
      Set.MapsTo (refinedTubeCellPartialEquiv (W := W) d r H d (Sum.inr (Sum.inl ⟨i, rfl⟩)))
        (Metric.sphere (0 : Fin d → ℝ) 1)
        (⋃ (m < d) (a ∈ F m), refinedTubeCellPartialEquiv (W := W) d r H m a '' Metric.closedBall 0 1) := by
  classical
  obtain ⟨F, hF⟩ := Topology.CWComplex.mapsTo' (C := (Set.univ : Set X)) d i
  refine ⟨fun m => if hm : m < d then
    (F m).image (fun j => Sum.inl (κ0 m hm j)) else ∅, ?_⟩
  intro x hx
  have h := hF hx
  simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
  rcases h with ⟨m, hmd, j, hj, y, hy, hyx⟩
  refine ⟨m, hmd, Sum.inl (κ0 m hmd j), ?_, y, hy, ?_⟩
  · rw [dite_eq_left hmd]
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  · let s : (classicalCellDiskPair.{u} d).snd := ULift.up ⟨x, hx⟩
    let q : (classicalCellDiskPair.{u} m).fst := ULift.up ⟨y, hy⟩
    have hs : characteristicSphereToSkeleton d i s = originalLowerDiskToSkeleton d m hmd j q := by
      apply Subtype.ext
      change Topology.CWComplex.map d i x = Topology.CWComplex.map m j y
      exact hyx.symm
    have hvalue : refinedTubeCellPartialEquiv (W := W) d r H d (Sum.inr (Sum.inl ⟨i, rfl⟩)) x =
        oldIntoTubeSpace d H (g0 (originalLowerDiskToSkeleton d m hmd j q)) := by
      calc
        _ = bottomDiskCharacteristic d H i ((classicalCellDiskPair.{u} d).map s) :=
          refinedTubeCellPartialEquiv_closed_characteristic d r H d _
            ((classicalCellDiskPair.{u} d).map s)
        _ = oldIntoTubeSpace d H (H ⟨i, (s, 0)⟩) := originalCylinderMap_whole_side d H i s 0
        _ = oldIntoTubeSpace d H (g0 (characteristicSphereToSkeleton d i s)) :=
          congrArg (oldIntoTubeSpace d H) (hstart s)
        _ = _ := congrArg (fun z => oldIntoTubeSpace d H (g0 z)) hs
    change oldIntoTubeSpace d H (Topology.CWComplex.map m (κ0 m hmd j) y) = _
    exact (hvalue.trans (congrArg (oldIntoTubeSpace d H) (hg0 m hmd j q))).symm

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after26–31. The original successor end map
is CONSTRUCTED from the original CW attaching pushout and the actual zero
endpoint of the original sphere homotopy. No comparison map, inverse,
replacement or new CW structure is supplied for the successor end. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {X A : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def originalSuccessorBottomDisks (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A)) :
    TopCat.of (CellDisksAt X d) ⟶ refinedTubeSpace d H :=
  TopCat.ofHom
    ⟨fun p => bottomDiskCharacteristic d H p.1 p.2,
      continuous_sigma (fun i => (bottomDiskCharacteristic d H i).continuous)⟩

private theorem originalSuccessorEnd_square (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (g0 : C(skeletonTop X d, A))
    (hstart : ∀ (i : Topology.CWComplex.cell (Set.univ : Set X) d)
        (s : (classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 0)⟩ = g0 (characteristicSphereToSkeleton d i s)) :
    sphereSumToSkeleton X d ≫ TopCat.ofHom ((oldIntoTubeSpace d H).comp g0) =
      sphereSumToDiskSum X d ≫ originalSuccessorBottomDisks d H := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨i, s⟩
  change oldIntoTubeSpace d H (g0 (characteristicSphereToSkeleton d i s)) =
    originalCylinderMap d H i ((classicalCellDiskPair.{u} d).map s, 0)
  exact ((originalCylinderMap_whole_side d H i s 0).trans
    (congrArg (oldIntoTubeSpace d H) (hstart i s))).symm

private def originalSuccessorEndMap (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (g0 : C(skeletonTop X d, A))
    (hstart : ∀ (i : Topology.CWComplex.cell (Set.univ : Set X) d)
        (s : (classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 0)⟩ = g0 (characteristicSphereToSkeleton d i s)) :
    C(skeletonTop X (d + 1), refinedTubeSpace d H) :=
  ((isPushout_skeletonAttachment X d).desc
    (TopCat.ofHom ((oldIntoTubeSpace d H).comp g0))
    (originalSuccessorBottomDisks d H) (originalSuccessorEnd_square d H g0 hstart)).hom

private theorem originalSuccessorEndMap_old (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (g0 : C(skeletonTop X d, A)) (hstart)
    (x : skeletonTop X d) :
    originalSuccessorEndMap d H g0 hstart (skeletonTransition X d x) =
      oldIntoTubeSpace d H (g0 x) :=
  ConcreteCategory.congr_hom ((isPushout_skeletonAttachment X d).inl_desc
    (TopCat.ofHom ((oldIntoTubeSpace d H).comp g0))
    (originalSuccessorBottomDisks d H) (originalSuccessorEnd_square d H g0 hstart)) x

private theorem originalSuccessorEndMap_disk (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (g0 : C(skeletonTop X d, A)) (hstart)
    (i : Topology.CWComplex.cell (Set.univ : Set X) d)
    (q : (classicalCellDiskPair.{u} d).fst) :
    originalSuccessorEndMap d H g0 hstart (characteristicDiskToSkeleton d i q) =
      originalCylinderMap d H i (q, 0) :=
  ConcreteCategory.congr_hom ((isPushout_skeletonAttachment X d).inr_desc
    (TopCat.ofHom ((oldIntoTubeSpace d H).comp g0))
    (originalSuccessorBottomDisks d H) (originalSuccessorEnd_square d H g0 hstart)) ⟨i, q⟩

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source after26–32. The new polyhedral end is the
ACTUAL associated small cylinder/cone family on the independently chosen
sphere subdivisions. Its end map is constructed from its original ordinary
cone pushout. Each whole original disk is identified with its actual copied
cone; no polyhedral end map, inverse or CW comparison is supplied. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

variable {I W : Type u} {A : TopCat.{u}}

private abbrev successorSpherePolyhedron (d : ℕ) (r : I → ℕ) (i : I) :=
  subdivisionIter (SphereTriangulation.complex d) (r i)

private def actualConeToTopDisk (d : ℕ) (r : I → ℕ) (i : I) :
    C(TopCat.cone (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization),
      (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) := by
  letI := actualSphereSubdivisionFiniteFaces d (r i)
  letI := MappingCylinder.finiteFaces_domainComplex
    (successorSpherePolyhedron d r i) W
  exact ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm :
      C((MappingCylinder.coneComplex (copiedSphereDomain (W := W) d (r i))).Realization,
        (Topology.CWComplex.classicalCellDiskPair.{u} d).fst)).comp
    (MappingCylinder.ordinaryConeHomeomorph (copiedSphereDomain (W := W) d (r i)) :
      C(TopCat.cone (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization),
        (MappingCylinder.coneComplex (copiedSphereDomain (W := W) d (r i))).Realization))

private theorem actualConeToTopDisk_base (d : ℕ) (r : I → ℕ) (i : I)
    (x : (copiedSphereDomain (W := W) d (r i)).Realization) :
    actualConeToTopDisk d r i
        (TopCat.coneBase (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization) x) =
      (Topology.CWComplex.classicalCellDiskPair.{u} d).map
        ((originalSphereToCopiedDomain (W := W) d (r i)).symm x) := by
  let := actualSphereSubdivisionFiniteFaces d (r i)
  let := MappingCylinder.finiteFaces_domainComplex (successorSpherePolyhedron d r i) W
  apply (originalDiskToCopiedConeComplex (W := W) d (r i)).injective
  change originalDiskToCopiedConeComplex (W := W) d (r i)
      ((originalDiskToCopiedConeComplex (W := W) d (r i)).symm
        (MappingCylinder.ordinaryConeHomeomorph (copiedSphereDomain (W := W) d (r i))
          (TopCat.coneBase (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization) x))) = _
  rw [Homeomorph.apply_symm_apply, MappingCylinder.ordinaryConeHomeomorph_base,
    originalDiskToCopiedConeComplex_boundary,
    (originalSphereToCopiedDomain (W := W) d (r i)).apply_symm_apply]

private def polyhedralSuccessorConeLeg (d : ℕ) (r : I → ℕ)
    (H : C(sideSum (I := I) d, A)) :
    TopCat.of (Σ i : I, TopCat.cone
      (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization)) ⟶ refinedTubeSpace d H :=
  TopCat.ofHom
    ⟨fun p => originalCylinderMap d H p.1 (actualConeToTopDisk d r p.1 p.2, 1),
      continuous_sigma (fun i => (originalCylinderMap d H i).continuous.comp
        ((actualConeToTopDisk d r i).continuous.prodMk continuous_const))⟩

private theorem polyhedralSuccessorEnd_square (d : ℕ) (r : I → ℕ)
    (Q : PreAbstractSimplicialComplex W)
    (f : ∀ i, Morphism (successorSpherePolyhedron d r i) Q)
    (H : C(sideSum (I := I) d, A))
    (gB : C((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization, A))
    (htop : ∀ i (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 1)⟩ = gB
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (successorSpherePolyhedron d r) Q f
            ⟨i, originalSphereToCopiedDomain (W := W) d (r i) s⟩)) :
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
        (successorSpherePolyhedron d r) Q f ≫
          TopCat.ofHom ((oldIntoTubeSpace d H).comp gB) =
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCones
        (successorSpherePolyhedron d r) ≫ polyhedralSuccessorConeLeg d r H := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  let source : TopCat.{u} :=
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
      (successorSpherePolyhedron d r) W
  let q : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd :=
    (originalSphereToCopiedDomain (W := W) d (r i)).symm x
  have hq : originalSphereToCopiedDomain (W := W) d (r i) q = x :=
    (originalSphereToCopiedDomain (W := W) d (r i)).apply_symm_apply x
  have hsource :
      (⟨i, originalSphereToCopiedDomain (W := W) d (r i) q⟩ : source) =
        (⟨i, x⟩ : source) :=
    congrArg (fun y : (copiedSphereDomain (W := W) d (r i)).Realization =>
      (⟨i, y⟩ : source)) hq
  have htopPoint : H ⟨i, (q, 1)⟩ =
      gB (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
        (successorSpherePolyhedron d r) Q f (⟨i, x⟩ : source)) :=
    (htop i q).trans
      (congrArg (fun z : source =>
        gB (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (successorSpherePolyhedron d r) Q f z)) hsource)
  have hbase : actualConeToTopDisk d r i
      (TopCat.coneBase (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization) x) =
        (Topology.CWComplex.classicalCellDiskPair.{u} d).map q :=
    actualConeToTopDisk_base d r i x
  have hbasePoint : originalCylinderMap d H i
      (actualConeToTopDisk d r i
        (TopCat.coneBase (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization) x), 1) =
        originalCylinderMap d H i
          ((Topology.CWComplex.classicalCellDiskPair.{u} d).map q, 1) :=
    congrArg (fun y : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst =>
      originalCylinderMap d H i (y, 1)) hbase
  have hpoint : oldIntoTubeSpace d H
      (gB (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
        (successorSpherePolyhedron d r) Q f (⟨i, x⟩ : source))) =
        originalCylinderMap d H i
          (actualConeToTopDisk d r i
            (TopCat.coneBase
              (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization) x), 1) :=
    (congrArg (fun y : A => oldIntoTubeSpace d H y) htopPoint).symm.trans
      ((originalCylinderMap_whole_side d H i q 1).symm.trans hbasePoint.symm)
  change oldIntoTubeSpace d H
      (gB (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
        (successorSpherePolyhedron d r) Q f ⟨i, x⟩)) =
    polyhedralSuccessorConeLeg d r H
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCones
        (successorSpherePolyhedron d r) ⟨i, x⟩)
  rw [PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCones_apply]
  exact hpoint

private def polyhedralSuccessorEndMap (d : ℕ) (r : I → ℕ)
    (Q : PreAbstractSimplicialComplex W)
    (f : ∀ i, Morphism (successorSpherePolyhedron d r i) Q)
    (H : C(sideSum (I := I) d, A))
    (gB : C((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization, A)) (htop : ∀ i (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 1)⟩ = gB
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (successorSpherePolyhedron d r) Q f
            ⟨i, originalSphereToCopiedDomain (W := W) d (r i) s⟩)) :
    C((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Cone.associatedFamily
      (successorSpherePolyhedron d r) Q f).Realization, refinedTubeSpace d H) :=
  ((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.ordinaryConeFamily_isPushout
      (successorSpherePolyhedron d r) Q f
        (fun i => actualSphereSubdivisionFiniteFaces d (r i))).desc
    (TopCat.ofHom ((oldIntoTubeSpace d H).comp gB))
    (polyhedralSuccessorConeLeg (A := A) d r H) (polyhedralSuccessorEnd_square (A := A) d r Q f H gB htop)).hom

private theorem polyhedralSuccessorEndMap_cylinder (d : ℕ) (r : I → ℕ)
    (Q : PreAbstractSimplicialComplex W)
    (f : ∀ i, Morphism (successorSpherePolyhedron d r i) Q)
    (H : C(sideSum (I := I) d, A))
    (gB : C((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization, A)) (htop : ∀ i (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 1)⟩ = gB
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (successorSpherePolyhedron d r) Q f
            ⟨i, originalSphereToCopiedDomain (W := W) d (r i) s⟩))
    (x : (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization) :
    polyhedralSuccessorEndMap (A := A) d r Q f H gB htop
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
          (successorSpherePolyhedron d r) Q f x) =
      oldIntoTubeSpace d H (gB x) := by
  let sq := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.ordinaryConeFamily_isPushout
    (successorSpherePolyhedron d r) Q f
      (fun j => actualSphereSubdivisionFiniteFaces d (r j))
  let L : TopCat.of (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization ⟶ refinedTubeSpace d H :=
    TopCat.ofHom ((oldIntoTubeSpace d H).comp gB)
  let R : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
      (successorSpherePolyhedron d r) W ⟶ refinedTubeSpace d H :=
    polyhedralSuccessorConeLeg (A := A) d r H
  let hc := polyhedralSuccessorEnd_square (A := A) d r Q f H gB htop
  have hm : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
      (successorSpherePolyhedron d r) Q f
        ≫ sq.desc L R hc = L :=
    sq.inl_desc L R hc
  have hp := congrArg (fun k : TopCat.of (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization ⟶ refinedTubeSpace d H =>
    k.hom x) hm
  simpa only [sq, L, R, hc, polyhedralSuccessorEndMap, TopCat.hom_comp,
    TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_apply,
    ContinuousMap.coe_mk] using! hp

private theorem polyhedralSuccessorEndMap_cone (d : ℕ) (r : I → ℕ)
    (Q : PreAbstractSimplicialComplex W)
    (f : ∀ i, Morphism (successorSpherePolyhedron d r i) Q)
    (H : C(sideSum (I := I) d, A))
    (gB : C((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization, A)) (htop : ∀ i (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 1)⟩ = gB
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (successorSpherePolyhedron d r) Q f
            ⟨i, originalSphereToCopiedDomain (W := W) d (r i) s⟩))
    (i : I) (x : TopCat.cone (TopCat.of (copiedSphereDomain (W := W) d (r i)).Realization)) :
    polyhedralSuccessorEndMap (A := A) d r Q f H gB htop
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (successorSpherePolyhedron d r) Q f
            (fun i => actualSphereSubdivisionFiniteFaces d (r i)) ⟨i, x⟩) =
      originalCylinderMap d H i (actualConeToTopDisk d r i x, 1) := by
  let sq := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.ordinaryConeFamily_isPushout
    (successorSpherePolyhedron d r) Q f
      (fun j => actualSphereSubdivisionFiniteFaces d (r j))
  let L : TopCat.of (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
      (successorSpherePolyhedron d r) Q f).Realization ⟶ refinedTubeSpace d H :=
    TopCat.ofHom ((oldIntoTubeSpace d H).comp gB)
  let R : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
      (successorSpherePolyhedron d r) W ⟶ refinedTubeSpace d H :=
    polyhedralSuccessorConeLeg (A := A) d r H
  let hc := polyhedralSuccessorEnd_square (A := A) d r Q f H gB htop
  have hm : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
      (successorSpherePolyhedron d r) Q f (fun j => actualSphereSubdivisionFiniteFaces d (r j))
        ≫ sq.desc L R hc = R :=
    sq.inr_desc L R hc
  have hp := congrArg (fun k : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
      (successorSpherePolyhedron d r) W ⟶ refinedTubeSpace d H =>
    k.hom (⟨i, x⟩ : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
      (successorSpherePolyhedron d r) W)) hm
  simpa only [sq, L, R, hc, polyhedralSuccessorEndMap, TopCat.hom_comp,
    TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_apply,
    ContinuousMap.coe_mk, polyhedralSuccessorConeLeg] using! hp

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private literal-rim source reused EXACTLY from immutable core47. No Stage witness is imported or supplied; this section constructs both entire rim collapses from the actual boundary map. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval
universe u
namespace ActualCommonSuccessorConstruction

private abbrev LiteralCylinder (d : ℕ) :=
  (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × TopCat.I.{u}

private def selectedHeight (top : Bool) : TopCat.I.{u} := if top then 1 else 0

private def rimSet (d : ℕ) (top : Bool) : Set (LiteralCylinder.{u} d) :=
  (Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map).unionProd
    ({selectedHeight.{u} top} : Set TopCat.I.{u})

private abbrev LiteralRim (d : ℕ) (top : Bool) := ↥(rimSet.{u} d top)

private def rimInclusion (d : ℕ) (top : Bool) :
    C(LiteralRim.{u} d top, LiteralCylinder.{u} d) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def rimRetraction (d : ℕ) (top : Bool) :
    C(LiteralCylinder.{u} d, LiteralRim.{u} d top) := by
  cases top
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).bottomRetraction
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).topRetraction

private theorem rimRetraction_inclusion (d : ℕ) (top : Bool)
    (x : LiteralRim.{u} d top) :
    rimRetraction d top (rimInclusion d top x) = x := by
  cases top
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).bottom_inclusion_retraction x
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).top_inclusion_retraction x

private def rimHomotopy (d : ℕ) (top : Bool) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (LiteralCylinder.{u} d))
      ((rimInclusion d top).comp (rimRetraction d top))
      (Set.range (rimInclusion d top)) := by
  cases top
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).bottomHomotopy
  · exact (Topology.CWComplex.classicalDiskCylinderCollapseData.{u} d).topHomotopy

private def rimSide (d : ℕ) (top : Bool) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).snd × TopCat.I.{u},
      LiteralRim.{u} d top) where
  toFun x := ⟨((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.1, x.2),
    Set.mem_unionProd.mpr (Or.inl (Set.mem_range_self x.1))⟩
  continuous_toFun :=
    (((Topology.CWComplex.classicalCellDiskPair.{u} d).map.hom.continuous.comp
      continuous_fst).prodMk continuous_snd).subtype_mk _

private theorem rimRetraction_side (d : ℕ) (top : Bool)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × TopCat.I.{u}) :
    rimRetraction d top
      ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.1, x.2) =
        rimSide d top x :=
  rimRetraction_inclusion d top (rimSide d top x)

private theorem rimHomotopy_side (d : ℕ) (top : Bool) (t : unitInterval)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × TopCat.I.{u}) :
    rimHomotopy d top
      (t, ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.1, x.2)) =
        ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.1, x.2) :=
  (rimHomotopy d top).eq_fst t (Set.mem_range_self (rimSide d top x))

section WholeRimFamily

variable {J : Type u} (d : ℕ)

private abbrev LiteralSphereFamily :=
  Σ _ : J, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × TopCat.I.{u}

private abbrev LiteralCylinderFamily := Σ _ : J, LiteralCylinder.{u} d

private abbrev LiteralRimFamily (top : Bool) := Σ _ : J, LiteralRim.{u} d top

private def rimFamilySide (top : Bool) :
    C(LiteralSphereFamily (J := J) d, LiteralRimFamily (J := J) d top) where
  toFun x := ⟨x.1, rimSide d top x.2⟩
  continuous_toFun := continuous_sigma fun j => continuous_sigmaMk.comp (rimSide d top).continuous

private def rimFamilyInclusion (top : Bool) :
    C(LiteralRimFamily (J := J) d top, LiteralCylinderFamily (J := J) d) where
  toFun x := ⟨x.1, rimInclusion d top x.2⟩
  continuous_toFun := continuous_sigma fun j =>
    continuous_sigmaMk.comp (rimInclusion d top).continuous

private def rimFamilyRetraction (top : Bool) :
    C(LiteralCylinderFamily (J := J) d, LiteralRimFamily (J := J) d top) where
  toFun x := ⟨x.1, rimRetraction d top x.2⟩
  continuous_toFun := continuous_sigma fun j =>
    continuous_sigmaMk.comp (rimRetraction d top).continuous

private theorem rimFamilyRetraction_inclusion (top : Bool)
    (x : LiteralRimFamily (J := J) d top) :
    rimFamilyRetraction d top (rimFamilyInclusion d top x) = x := by
  rcases x with ⟨j, x⟩
  exact congrArg (Sigma.mk j) (rimRetraction_inclusion d top x)

private theorem rimSet_closed (top : Bool) :
    IsClosed (rimSet.{u} d top) := by
  let : T1Space TopCat.I.{u} := (TopCat.I.homeomorph.{u}).symm.t1Space
  have hsets : rimSet.{u} d top =
      (fun z : LiteralCylinder.{u} d => z.1) ⁻¹'
          Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map ∪
        (fun z : LiteralCylinder.{u} d => z.2) ⁻¹'
          ({selectedHeight.{u} top} : Set TopCat.I.{u}) := by
    ext z
    exact Set.mem_unionProd
  have hs : IsClosed ((fun z : LiteralCylinder.{u} d => z.1) ⁻¹'
      Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map) :=
    (Topology.CWComplex.isClosedEmbedding_classicalCellDiskPair_map.{u}
      (n := d)).isClosed_range.preimage continuous_fst
  have ht : IsClosed ((fun z : LiteralCylinder.{u} d => z.2) ⁻¹'
      ({selectedHeight.{u} top} : Set TopCat.I.{u})) :=
    isClosed_singleton.preimage continuous_snd
  exact hsets.symm ▸ hs.union ht

private theorem rimFamilyInclusion_closed (top : Bool) :
    IsClosedEmbedding (rimFamilyInclusion (J := J) d top) := by
  have hr : IsClosedEmbedding (rimInclusion.{u} d top) :=
    IsClosedEmbedding.subtypeVal (rimSet_closed d top)
  have hσ : IsEmbedding
      (Sigma.map (id : J → J) (fun _ : J => (rimInclusion.{u} d top :
        LiteralRim.{u} d top → LiteralCylinder.{u} d)) :
        (Σ _ : J, LiteralRim.{u} d top) → (Σ _ : J, LiteralCylinder.{u} d)) :=
    (Topology.isEmbedding_sigmaMap Function.injective_id).mpr
      (fun _ => hr.isEmbedding)
  have hf : IsEmbedding (rimFamilyInclusion (J := J) d top) := by
    simpa only [rimFamilyInclusion] using! hσ
  refine ⟨hf, ?_⟩
  rw [isClosed_sigma_iff]
  intro j
  have heq : (Sigma.mk j) ⁻¹' Set.range (rimFamilyInclusion (J := J) d top) =
      Set.range (rimInclusion.{u} d top) := by
    ext x
    constructor
    · rintro ⟨⟨k, a⟩, ha⟩
      change (⟨k, rimInclusion d top a⟩ : LiteralCylinderFamily (J := J) d) =
        ⟨j, x⟩ at ha
      have hk : k = j := (Sigma.mk.inj_iff.mp ha).1
      subst k
      exact ⟨a, eq_of_heq (Sigma.mk.inj_iff.mp ha).2⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨j, a⟩, rfl⟩
  rw [heq]
  exact hr.isClosed_range

/-- Joint continuity over the arbitrary family is obtained by currying over
the compact interval, descending through the actual coproduct, and evaluating.
There is no whole-family compactness or finite-index premise. -/
private def rimFamilyHomotopy (top : Bool) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (LiteralCylinderFamily (J := J) d))
      ((rimFamilyInclusion d top).comp (rimFamilyRetraction d top))
      (Set.range (rimFamilyInclusion d top)) := by
  let row (j : J) : C(LiteralCylinder.{u} d,
      C(unitInterval, LiteralCylinderFamily (J := J) d)) :=
    (⟨fun p : LiteralCylinder.{u} d × unitInterval =>
      ⟨j, rimHomotopy d top (p.2, p.1)⟩,
      continuous_sigmaMk.comp
        ((rimHomotopy d top).continuous.comp continuous_swap)⟩ :
      C(LiteralCylinder.{u} d × unitInterval, LiteralCylinderFamily (J := J) d)).curry
  let rows : C(LiteralCylinderFamily (J := J) d,
      C(unitInterval, LiteralCylinderFamily (J := J) d)) :=
    ⟨fun p => row p.1 p.2, continuous_sigma fun j => (row j).continuous⟩
  let F : C(unitInterval × LiteralCylinderFamily (J := J) d,
      LiteralCylinderFamily (J := J) d) :=
    rows.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  refine
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · rintro ⟨j, x⟩
    exact congrArg (Sigma.mk j) ((rimHomotopy d top).apply_zero x)
  · rintro ⟨j, x⟩
    exact congrArg (Sigma.mk j) ((rimHomotopy d top).apply_one x)
  · intro t x hx
    rcases hx with ⟨⟨j, b⟩, rfl⟩
    exact congrArg (Sigma.mk j) ((rimHomotopy d top).eq_fst t (Set.mem_range_self b))

private theorem rimFamilyHomotopy_value (top : Bool) (t : unitInterval)
    (j : J) (x : LiteralCylinder.{u} d) :
    rimFamilyHomotopy (J := J) d top (t, ⟨j, x⟩) =
      ⟨j, rimHomotopy d top (t, x)⟩ := rfl

private def literalFamilySide :
    C(LiteralSphereFamily (J := J) d, LiteralCylinderFamily (J := J) d) where
  toFun x := ⟨x.1, ((Topology.CWComplex.classicalCellDiskPair.{u} d).map x.2.1, x.2.2)⟩
  continuous_toFun := continuous_sigma fun j => continuous_sigmaMk.comp
    (((Topology.CWComplex.classicalCellDiskPair.{u} d).map.hom.continuous.comp
      continuous_fst).prodMk continuous_snd)

private theorem rimFamilySide_comp_inclusion (top : Bool) :
    (rimFamilyInclusion (J := J) d top).comp (rimFamilySide d top) =
      literalFamilySide (J := J) d := by
  apply ContinuousMap.ext
  rintro ⟨j, x⟩
  rfl

private theorem literalFamilySide_comp_retraction (top : Bool) :
    (rimFamilyRetraction d top).comp (literalFamilySide (J := J) d) =
      rimFamilySide d top := by
  apply ContinuousMap.ext
  rintro ⟨j, x⟩
  exact congrArg (Sigma.mk j) (rimRetraction_side d top x)

variable {W : TopCat.{u}}
variable (h : C(LiteralSphereFamily (J := J) d, W))

private abbrev literalAttachment : TopCat.{u} :=
  pushout (TopCat.ofHom h) (TopCat.ofHom (literalFamilySide (J := J) d))

private abbrev rimAttachment (top : Bool) : TopCat.{u} :=
  pushout (TopCat.ofHom h) (TopCat.ofHom (rimFamilySide (J := J) d top))

private def literalOld : W ⟶ literalAttachment d h := pushout.inl _ _

private def literalDisks :
    TopCat.of (LiteralCylinderFamily (J := J) d) ⟶ literalAttachment d h :=
  pushout.inr _ _

private def rimOld (top : Bool) : W ⟶ rimAttachment d h top := pushout.inl _ _

private def rimDisks (top : Bool) :
    TopCat.of (LiteralRimFamily (J := J) d top) ⟶ rimAttachment d h top :=
  pushout.inr _ _

private theorem includedRim_commutes (top : Bool) :
    TopCat.ofHom h ≫ literalOld d h =
      TopCat.ofHom (rimFamilySide (J := J) d top) ≫
        (TopCat.ofHom (rimFamilyInclusion d top) ≫ literalDisks d h) := by
  apply TopCat.ext
  intro x
  change literalOld d h (h x) =
    literalDisks d h (rimFamilyInclusion d top (rimFamilySide d top x))
  change literalOld d h (h x) = literalDisks d h (literalFamilySide d x)
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom h) (g := TopCat.ofHom (literalFamilySide (J := J) d))) x

private theorem retractedRim_commutes (top : Bool) :
    TopCat.ofHom h ≫ rimOld d h top =
      TopCat.ofHom (literalFamilySide (J := J) d) ≫
        (TopCat.ofHom (rimFamilyRetraction d top) ≫ rimDisks d h top) := by
  apply TopCat.ext
  intro x
  change rimOld d h top (h x) =
    rimDisks d h top (rimFamilyRetraction d top (literalFamilySide d x))
  rw [show rimFamilyRetraction d top (literalFamilySide d x) = rimFamilySide d top x from
    congrArg (fun F : C(_, _) => F x) (literalFamilySide_comp_retraction d top)]
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom h)
      (g := TopCat.ofHom (rimFamilySide (J := J) d top))) x

private def includeRimAttachment (top : Bool) :
    rimAttachment d h top ⟶ literalAttachment d h :=
  pushout.desc (literalOld d h)
    (TopCat.ofHom (rimFamilyInclusion d top) ≫ literalDisks d h)
    (includedRim_commutes d h top)

private def retractToRimAttachment (top : Bool) :
    literalAttachment d h ⟶ rimAttachment d h top :=
  pushout.desc (rimOld d h top)
    (TopCat.ofHom (rimFamilyRetraction d top) ≫ rimDisks d h top)
    (retractedRim_commutes d h top)

private theorem includeRimAttachment_old (top : Bool) (w : W) :
    includeRimAttachment d h top (rimOld d h top w) = literalOld d h w :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) w

private theorem includeRimAttachment_rim (top : Bool)
    (x : LiteralRimFamily (J := J) d top) :
    includeRimAttachment d h top (rimDisks d h top x) =
      literalDisks d h (rimFamilyInclusion d top x) := by
  have hm : pushout.inr (TopCat.ofHom h) (TopCat.ofHom (rimFamilySide (J := J) d top)) ≫
      pushout.desc (literalOld d h) (TopCat.ofHom (rimFamilyInclusion d top) ≫ literalDisks d h) (includedRim_commutes d h top) = (TopCat.ofHom (rimFamilyInclusion d top) ≫ literalDisks d h) :=
    pushout.inr_desc (literalOld d h) (TopCat.ofHom (rimFamilyInclusion d top) ≫ literalDisks d h) (includedRim_commutes d h top)
  have hp := congrArg (fun k : TopCat.of (LiteralRimFamily (J := J) d top) ⟶ literalAttachment d h => k.hom x) hm
  simpa only [includeRimAttachment, rimDisks, TopCat.hom_comp, TopCat.hom_ofHom,
    ContinuousMap.comp_apply, ContinuousMap.coe_apply, ContinuousMap.coe_mk] using! hp

private theorem retractToRimAttachment_old (top : Bool) (w : W) :
    retractToRimAttachment d h top (literalOld d h w) = rimOld d h top w :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) w

private theorem retractToRimAttachment_cylinder (top : Bool)
    (x : LiteralCylinderFamily (J := J) d) :
    retractToRimAttachment d h top (literalDisks d h x) =
      rimDisks d h top (rimFamilyRetraction d top x) := by
  have hm : pushout.inr (TopCat.ofHom h) (TopCat.ofHom (literalFamilySide (J := J) d)) ≫
      pushout.desc (rimOld d h top) (TopCat.ofHom (rimFamilyRetraction d top) ≫ rimDisks d h top) (retractedRim_commutes d h top) = (TopCat.ofHom (rimFamilyRetraction d top) ≫ rimDisks d h top) :=
    pushout.inr_desc (rimOld d h top) (TopCat.ofHom (rimFamilyRetraction d top) ≫ rimDisks d h top) (retractedRim_commutes d h top)
  have hp := congrArg (fun k : TopCat.of (LiteralCylinderFamily (J := J) d) ⟶ rimAttachment d h top => k.hom x) hm
  simpa only [retractToRimAttachment, literalDisks, TopCat.hom_comp, TopCat.hom_ofHom,
    ContinuousMap.comp_apply, ContinuousMap.coe_apply, ContinuousMap.coe_mk] using! hp

private theorem retractToRimAttachment_inclusion (top : Bool)
    (x : rimAttachment d h top) :
    retractToRimAttachment d h top (includeRimAttachment d h top x) = x := by
  let hs := IsPushout.of_hasPushout (TopCat.ofHom h)
    (TopCat.ofHom (rimFamilySide (J := J) d top))
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨w, rfl⟩
    change retractToRimAttachment d h top
      (includeRimAttachment d h top (rimOld d h top w)) = rimOld d h top w
    exact (congrArg (retractToRimAttachment d h top)
      (includeRimAttachment_old d h top w)).trans
        (retractToRimAttachment_old d h top w)
  · rcases hx with ⟨b, rfl⟩
    change retractToRimAttachment d h top
      (includeRimAttachment d h top (rimDisks d h top b)) = rimDisks d h top b
    exact (congrArg (retractToRimAttachment d h top)
      (includeRimAttachment_rim d h top b)).trans
        ((retractToRimAttachment_cylinder d h top (rimFamilyInclusion d top b)).trans
          (congrArg (rimDisks d h top) (rimFamilyRetraction_inclusion d top b)))

private theorem includeRimAttachment_closed (top : Bool) :
    IsClosedEmbedding (includeRimAttachment d h top) := by
  have hside :
      TopCat.ofHom (rimFamilySide (J := J) d top) ≫
        TopCat.ofHom (rimFamilyInclusion d top) =
          TopCat.ofHom (literalFamilySide (J := J) d) := by
    apply TopCat.ext
    intro x
    rfl
  have hold :
      rimOld d h top ≫ includeRimAttachment d h top = literalOld d h :=
    pushout.inl_desc _ _ _
  have hcomm :
      TopCat.ofHom (rimFamilyInclusion (J := J) d top) ≫ literalDisks d h =
        rimDisks d h top ≫ includeRimAttachment d h top :=
    (pushout.inr_desc _ _ _).symm
  have houter :
      IsPushout
        (TopCat.ofHom (rimFamilySide (J := J) d top) ≫
          TopCat.ofHom (rimFamilyInclusion d top))
        (TopCat.ofHom h) (literalDisks d h)
        (rimOld d h top ≫ includeRimAttachment d h top) := by
    rw [hside, hold]
    exact (IsPushout.of_hasPushout (TopCat.ofHom h)
      (TopCat.ofHom (literalFamilySide (J := J) d))).flip
  have hleft :=
    (IsPushout.of_hasPushout (TopCat.ofHom h)
      (TopCat.ofHom (rimFamilySide (J := J) d top))).flip
  exact TopCat.isClosedEmbedding_of_isPushout
    (houter.of_left hcomm hleft) (rimFamilyInclusion_closed d top)

private def includedFamilyHomotopy (top : Bool) :
    ContinuousMap.Homotopy (literalDisks d h).hom
      ((literalDisks d h).hom.comp
        ((rimFamilyInclusion d top).comp (rimFamilyRetraction d top))) :=
  (ContinuousMap.Homotopy.refl (literalDisks d h).hom).comp
    (rimFamilyHomotopy d top).toHomotopy

private theorem includedFamilyHomotopy_compatible (top : Bool)
    (t : unitInterval) (x : LiteralSphereFamily (J := J) d) :
    ContinuousMap.Homotopy.refl (literalOld d h).hom (t, h x) =
      includedFamilyHomotopy d h top (t, literalFamilySide d x) := by
  change literalOld d h (h x) =
    literalDisks d h (rimFamilyHomotopy d top (t, literalFamilySide d x))
  have hfix := (rimFamilyHomotopy d top).eq_fst t
    (Set.mem_range_self (rimFamilySide d top x))
  change rimFamilyHomotopy d top (t, literalFamilySide d x) = literalFamilySide d x at hfix
  rw [hfix]
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom h) (g := TopCat.ofHom (literalFamilySide (J := J) d))) x

private theorem includedFamilyHomotopy_initial_commutes :
    TopCat.ofHom h ≫ literalOld d h =
      TopCat.ofHom (literalFamilySide (J := J) d) ≫ literalDisks d h :=
  pushout.condition (f := TopCat.ofHom h)
    (g := TopCat.ofHom (literalFamilySide (J := J) d))

private theorem includedFamilyHomotopy_terminal_commutes (top : Bool) :
    TopCat.ofHom h ≫ literalOld d h =
      TopCat.ofHom (literalFamilySide (J := J) d) ≫
        TopCat.ofHom ((literalDisks d h).hom.comp
          ((rimFamilyInclusion d top).comp (rimFamilyRetraction d top))) := by
  apply TopCat.ext
  intro x
  exact (includedFamilyHomotopy_compatible d h top 1 x).trans
    ((includedFamilyHomotopy d h top).apply_one (literalFamilySide d x))

private def rawRimAttachmentHomotopy (top : Bool) :
    ContinuousMap.Homotopy
      (pushout.desc (literalOld d h) (literalDisks d h)
        (includedFamilyHomotopy_initial_commutes d h)).hom
      (pushout.desc (literalOld d h)
        (TopCat.ofHom ((literalDisks d h).hom.comp
          ((rimFamilyInclusion d top).comp (rimFamilyRetraction d top))))
        (includedFamilyHomotopy_terminal_commutes d h top)).hom :=
  TopCat.Homotopy.pushoutDesc
    (ContinuousMap.Homotopy.refl (literalOld d h).hom)
    (includedFamilyHomotopy d h top)
    (includedFamilyHomotopy_initial_commutes d h)
    (includedFamilyHomotopy_terminal_commutes d h top)
    (includedFamilyHomotopy_compatible d h top)

private theorem rawRimAttachmentHomotopy_old (top : Bool)
    (t : unitInterval) (w : W) :
    rawRimAttachmentHomotopy d h top (t, literalOld d h w) = literalOld d h w :=
  TopCat.Homotopy.pushoutDesc_apply_inl _ _ _ _ _ t w

private theorem rawRimAttachmentHomotopy_cylinder (top : Bool)
    (t : unitInterval) (x : LiteralCylinderFamily (J := J) d) :
    rawRimAttachmentHomotopy d h top (t, literalDisks d h x) =
      literalDisks d h (rimFamilyHomotopy d top (t, x)) := by
  have hp := TopCat.Homotopy.pushoutDesc_apply_inr
    (X := TopCat.of (LiteralSphereFamily (J := J) d)) (Y := W)
    (Z := TopCat.of (LiteralCylinderFamily (J := J) d)) (W := literalAttachment d h)
    (f := TopCat.ofHom h) (g := TopCat.ofHom (literalFamilySide (J := J) d))
    (y₀ := literalOld d h) (y₁ := literalOld d h) (z₀ := literalDisks d h)
    (z₁ := TopCat.ofHom ((literalDisks d h).hom.comp
      ((rimFamilyInclusion d top).comp (rimFamilyRetraction d top))))
    (ContinuousMap.Homotopy.refl (literalOld d h).hom)
    (includedFamilyHomotopy d h top)
    (includedFamilyHomotopy_initial_commutes d h)
    (includedFamilyHomotopy_terminal_commutes d h top)
    (includedFamilyHomotopy_compatible d h top) t x
  simpa only [rawRimAttachmentHomotopy, includedFamilyHomotopy,
    ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply] using! hp

/-- The whole ordinary pushout homotopy fixes the entire included rim target,
including every old common-stage point, at every deformation time. -/
private def rimAttachmentHomotopy (top : Bool) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (literalAttachment d h))
      ((includeRimAttachment d h top).hom.comp (retractToRimAttachment d h top).hom)
      (Set.range (includeRimAttachment d h top)) := by
  let H := rawRimAttachmentHomotopy d h top
  have h₀ : (fun x : literalAttachment d h => H (0, x)) = id := by
    funext x
    let hs := IsPushout.of_hasPushout (TopCat.ofHom h)
      (TopCat.ofHom (literalFamilySide (J := J) d))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
    · rcases hx with ⟨w, rfl⟩
      change rawRimAttachmentHomotopy d h top (0, literalOld d h w) = literalOld d h w
      exact rawRimAttachmentHomotopy_old d h top 0 w
    · rcases hx with ⟨b, rfl⟩
      change rawRimAttachmentHomotopy d h top (0, literalDisks d h b) = literalDisks d h b
      exact (rawRimAttachmentHomotopy_cylinder d h top 0 b).trans
        (congrArg (literalDisks d h) ((rimFamilyHomotopy d top).toHomotopy.apply_zero b))
  have h₁ : ∀ x, H (1, x) =
      includeRimAttachment d h top (retractToRimAttachment d h top x) := by
    intro x
    let hs := IsPushout.of_hasPushout (TopCat.ofHom h)
      (TopCat.ofHom (literalFamilySide (J := J) d))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
    · rcases hx with ⟨w, rfl⟩
      change rawRimAttachmentHomotopy d h top (1, literalOld d h w) =
        includeRimAttachment d h top (retractToRimAttachment d h top (literalOld d h w))
      have hr := (congrArg (includeRimAttachment d h top)
        (retractToRimAttachment_old d h top w)).trans (includeRimAttachment_old d h top w)
      exact (rawRimAttachmentHomotopy_old d h top 1 w).trans hr.symm
    · rcases hx with ⟨b, rfl⟩
      change rawRimAttachmentHomotopy d h top (1, literalDisks d h b) =
        includeRimAttachment d h top (retractToRimAttachment d h top (literalDisks d h b))
      have hl := (rawRimAttachmentHomotopy_cylinder d h top 1 b).trans
        (congrArg (literalDisks d h) ((rimFamilyHomotopy d top).toHomotopy.apply_one b))
      have hr := (congrArg (includeRimAttachment d h top)
        (retractToRimAttachment_cylinder d h top b)).trans
          (includeRimAttachment_rim d h top (rimFamilyRetraction d top b))
      exact hl.trans hr.symm
  refine
    { toFun := H
      continuous_toFun := H.continuous
      map_zero_left := fun x => congrFun h₀ x
      map_one_left := h₁
      prop' := ?_ }
  intro t x hx
  change H (t, x) = x
  rcases hx with ⟨y, rfl⟩
  let hs := IsPushout.of_hasPushout (TopCat.ofHom h)
    (TopCat.ofHom (rimFamilySide (J := J) d top))
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) y with hy | hy
  · rcases hy with ⟨w, rfl⟩
    change rawRimAttachmentHomotopy d h top
      (t, includeRimAttachment d h top (rimOld d h top w)) =
        includeRimAttachment d h top (rimOld d h top w)
    have hi := includeRimAttachment_old d h top w
    exact (congrArg (fun z => rawRimAttachmentHomotopy d h top (t, z)) hi).trans
      ((rawRimAttachmentHomotopy_old d h top t w).trans hi.symm)
  · rcases hy with ⟨b, rfl⟩
    change rawRimAttachmentHomotopy d h top
      (t, includeRimAttachment d h top (rimDisks d h top b)) =
        includeRimAttachment d h top (rimDisks d h top b)
    have hi := includeRimAttachment_rim d h top b
    exact (congrArg (fun z => rawRimAttachmentHomotopy d h top (t, z)) hi).trans
      ((rawRimAttachmentHomotopy_cylinder d h top t (rimFamilyInclusion d top b)).trans
        ((congrArg (literalDisks d h)
          ((rimFamilyHomotopy d top).eq_fst t (Set.mem_range_self b))).trans hi.symm))

private theorem rimAttachmentHomotopy_old_fixed (top : Bool)
    (t : unitInterval) (w : W) :
    rimAttachmentHomotopy d h top (t, literalOld d h w) = literalOld d h w :=
  rawRimAttachmentHomotopy_old d h top t w

end WholeRimFamily

end ActualCommonSuccessorConstruction
end

/- Same-module private source after26–32 and the exact literal-rim reuse.
Explicit interval homeomorphisms normalize the ACTUAL unit-interval tube
pushout to that literal disk-cylinder attachment. Both derived rim
retractions and full relative homotopies are transported back. The entire
old/intermediate stage is fixed at every time. No inverse is a premise. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open ActualCommonSuccessorConstruction

variable {I : Type u} {A : TopCat.{u}}

private def sphereIntervalFamilyHomeomorph (d : ℕ) :
    sideSum (I := I) d ≃ₜ LiteralSphereFamily (J := I) d :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph
    (fun _ : I => (Homeomorph.refl _).prodCongr (TopCat.I.homeomorph.{u}).symm)

private def diskIntervalFamilyHomeomorph (d : ℕ) :
    cylinderSum (I := I) d ≃ₜ LiteralCylinderFamily (J := I) d :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph
    (fun _ : I => (Homeomorph.refl _).prodCongr (TopCat.I.homeomorph.{u}).symm)

private def normalizedLiteralBoundary (d : ℕ) (H : C(sideSum (I := I) d, A)) :
    C(LiteralSphereFamily (J := I) d, A) :=
  H.comp ((sphereIntervalFamilyHomeomorph (I := I) d).symm :
    C(LiteralSphereFamily (J := I) d, sideSum (I := I) d))

private theorem literalAttachment_as_unit_pushout (d : ℕ)
    (H : C(sideSum (I := I) d, A)) :
    IsPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
      (literalOld d (normalizedLiteralBoundary d H))
      (TopCat.ofHom (diskIntervalFamilyHomeomorph (I := I) d :
        C(cylinderSum (I := I) d, LiteralCylinderFamily (J := I) d)) ≫
        literalDisks d (normalizedLiteralBoundary d H)) := by
  let e₁ : sideSum (I := I) d ≅ TopCat.of (LiteralSphereFamily (J := I) d) :=
    TopCat.isoOfHomeo (sphereIntervalFamilyHomeomorph (I := I) d)
  let e₃ : cylinderSum (I := I) d ≅ TopCat.of (LiteralCylinderFamily (J := I) d) :=
    TopCat.isoOfHomeo (diskIntervalFamilyHomeomorph (I := I) d)
  refine (IsPushout.of_hasPushout
    (TopCat.ofHom (normalizedLiteralBoundary d H))
    (TopCat.ofHom (literalFamilySide (J := I) d))).of_iso'
      e₁ (Iso.refl A) e₃ (Iso.refl _) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro x
    change H ((sphereIntervalFamilyHomeomorph (I := I) d).symm
      (sphereIntervalFamilyHomeomorph (I := I) d x)) = H x
    rw [Homeomorph.symm_apply_apply]
  · apply ConcreteCategory.hom_ext
    rintro ⟨i, s, t⟩
    change literalFamilySide (J := I) d
        (sphereIntervalFamilyHomeomorph (I := I) d ⟨i, (s, t)⟩) =
      diskIntervalFamilyHomeomorph (I := I) d
        ⟨i, ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t)⟩
    simp only [sphereIntervalFamilyHomeomorph, diskIntervalFamilyHomeomorph,
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply]
    rfl
  · rfl
  · rfl

private def unitLiteralAttachmentIso (d : ℕ) (H : C(sideSum (I := I) d, A)) :
    refinedTubeSpace d H ≅ literalAttachment d (normalizedLiteralBoundary d H) :=
  (literalAttachment_as_unit_pushout d H).isoPushout.symm

private theorem unitLiteralAttachmentIso_old (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (a : A) :
    (unitLiteralAttachmentIso d H).inv (literalOld d (normalizedLiteralBoundary d H) a) =
      oldIntoTubeSpace d H a :=
  ConcreteCategory.congr_hom (literalAttachment_as_unit_pushout d H).inl_isoPushout_hom a

private def unitRimInclude (d : ℕ) (H : C(sideSum (I := I) d, A)) (top : Bool) :
    rimAttachment d (normalizedLiteralBoundary d H) top ⟶ refinedTubeSpace d H :=
  includeRimAttachment d (normalizedLiteralBoundary d H) top ≫ (unitLiteralAttachmentIso d H).inv

private def unitRimRetraction (d : ℕ) (H : C(sideSum (I := I) d, A)) (top : Bool) :
    refinedTubeSpace d H ⟶ rimAttachment d (normalizedLiteralBoundary d H) top :=
  (unitLiteralAttachmentIso d H).hom ≫ retractToRimAttachment d (normalizedLiteralBoundary d H) top

private theorem unitRimRetraction_include (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool)
    (x : rimAttachment d (normalizedLiteralBoundary d H) top) :
    unitRimRetraction d H top (unitRimInclude d H top x) = x := by
  change retractToRimAttachment d (normalizedLiteralBoundary d H) top
    ((unitLiteralAttachmentIso d H).hom
      ((unitLiteralAttachmentIso d H).inv
        (includeRimAttachment d (normalizedLiteralBoundary d H) top x))) = x
  have hi := ConcreteCategory.congr_hom (unitLiteralAttachmentIso d H).inv_hom_id
    (includeRimAttachment d (normalizedLiteralBoundary d H) top x)
  exact (congrArg (retractToRimAttachment d (normalizedLiteralBoundary d H) top) hi).trans
    (retractToRimAttachment_inclusion d (normalizedLiteralBoundary d H) top x)

private def unitRimRelativeHomotopy (d : ℕ) (H : C(sideSum (I := I) d, A)) (top : Bool) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (refinedTubeSpace d H))
      ((unitRimInclude d H top).hom.comp (unitRimRetraction d H top).hom)
      (Set.range (unitRimInclude d H top)) := by
  let e := unitLiteralAttachmentIso d H
  let L := rimAttachmentHomotopy d (normalizedLiteralBoundary d H) top
  let K := (ContinuousMap.Homotopy.refl e.inv.hom).comp
    (L.toHomotopy.compContinuousMap e.hom.hom)
  have hzero : e.inv.hom.comp e.hom.hom = ContinuousMap.id (refinedTubeSpace d H) := by
    apply ContinuousMap.ext
    intro x
    exact ConcreteCategory.congr_hom e.hom_inv_id x
  let K' := K.cast hzero rfl
  refine { toHomotopy := K', prop' := ?_ }
  intro t x hx
  rcases hx with ⟨y, rfl⟩
  change e.inv (L (t, e.hom (e.inv (includeRimAttachment d (normalizedLiteralBoundary d H) top y)))) =
    e.inv (includeRimAttachment d (normalizedLiteralBoundary d H) top y)
  have hi : e.hom (e.inv (includeRimAttachment d (normalizedLiteralBoundary d H) top y)) =
      includeRimAttachment d (normalizedLiteralBoundary d H) top y := by
    simpa only [TopCat.comp_app, TopCat.id_app] using!
      ConcreteCategory.congr_hom e.inv_hom_id
        (includeRimAttachment d (normalizedLiteralBoundary d H) top y)
  exact (congrArg (fun z => e.inv (L (t, z))) hi).trans
    (congrArg e.inv (L.eq_fst t (Set.mem_range_self y)))

private theorem unitRimInclude_old (d : ℕ) (H : C(sideSum (I := I) d, A))
    (top : Bool) (a : A) :
    unitRimInclude d H top (rimOld d (normalizedLiteralBoundary d H) top a) =
      oldIntoTubeSpace d H a := by
  change (unitLiteralAttachmentIso d H).inv
    (includeRimAttachment d (normalizedLiteralBoundary d H) top
      (rimOld d (normalizedLiteralBoundary d H) top a)) = _
  rw [includeRimAttachment_old, unitLiteralAttachmentIso_old]

private theorem unitRimRelativeHomotopy_old_fixed (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (t : unitInterval) (a : A) :
    unitRimRelativeHomotopy d H top (t, oldIntoTubeSpace d H a) = oldIntoTubeSpace d H a :=
  (unitRimRelativeHomotopy d H top).eq_fst t
    ⟨rimOld d (normalizedLiteralBoundary d H) top a, unitRimInclude_old d H top a⟩

private theorem unitRimInclude_closed (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) : IsClosedEmbedding (unitRimInclude d H top) :=
  (TopCat.homeoOfIso (unitLiteralAttachmentIso d H).symm).isClosedEmbedding.comp
    (includeRimAttachment_closed d (normalizedLiteralBoundary d H) top)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private source following33.
The rim attachment and the selected-disk attachment both retain the SAME W.
This constructs an Iso between those two presentations, fixing every W point.
It does not identify W with either original or polyhedral recursive end.

Owning-module import proposal: MathlibExt.Topology.Category.TopCat.BinaryClosedGlue.
All maps and the closed two-piece cover are constructed below. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {J : Type u} {W : TopCat.{u}}

private abbrev EndpointSphereFamily (d : ℕ) :=
  Σ _ : J, (Topology.CWComplex.classicalCellDiskPair.{u} d).snd

private abbrev EndpointDiskFamily (d : ℕ) :=
  Σ _ : J, (Topology.CWComplex.classicalCellDiskPair.{u} d).fst

private def endpointSide (d : ℕ) (top : Bool) :
    C(EndpointSphereFamily (J := J) d, LiteralSphereFamily (J := J) d) where
  toFun x := ⟨x.1, (x.2, selectedHeight.{u} top)⟩
  continuous_toFun := continuous_sigma fun _ =>
    continuous_sigmaMk.comp (continuous_id.prodMk continuous_const)

private def endpointSphereInclusion (d : ℕ) :
    C(EndpointSphereFamily (J := J) d, EndpointDiskFamily (J := J) d) where
  toFun x := ⟨x.1, (Topology.CWComplex.classicalCellDiskPair.{u} d).map x.2⟩
  continuous_toFun := continuous_sigma fun _ => continuous_sigmaMk.comp
    (Topology.CWComplex.classicalCellDiskPair.{u} d).map.hom.continuous

private def rimEndPoint (d : ℕ) (top : Bool)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    LiteralRim.{u} d top :=
  ⟨(q, selectedHeight.{u} top),
    Set.mem_unionProd.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))⟩

private def endpointRimFamily (d : ℕ) (top : Bool) :
    C(EndpointDiskFamily (J := J) d, LiteralRimFamily (J := J) d top) where
  toFun x := ⟨x.1, rimEndPoint d top x.2⟩
  continuous_toFun := continuous_sigma fun _ =>
    continuous_sigmaMk.comp ((continuous_id.prodMk continuous_const).subtype_mk _)

private theorem endpointRimFamily_sphere (d : ℕ) (top : Bool) :
    (endpointRimFamily (J := J) d top).comp (endpointSphereInclusion d) =
      (rimFamilySide d top).comp (endpointSide (J := J) d top) := by
  apply ContinuousMap.ext
  rintro ⟨j, x⟩
  rfl

private def endpointBoundary (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    C(EndpointSphereFamily (J := J) d, W) :=
  h.comp (endpointSide d top)

/-- The entire old/intermediate W is retained in this actual pushout. -/
private abbrev diskEndAttachment (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) : TopCat.{u} :=
  pushout (TopCat.ofHom (endpointBoundary d h top))
    (TopCat.ofHom (endpointSphereInclusion (J := J) d))

private def diskEndOld (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    W ⟶ diskEndAttachment d h top :=
  pushout.inl _ _

private def diskEndDisks (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    TopCat.of (EndpointDiskFamily (J := J) d) ⟶ diskEndAttachment d h top :=
  pushout.inr _ _

private def rimSideRegion (d : ℕ) (top : Bool) : Set (LiteralRim.{u} d top) :=
  {r | r.val.1 ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map}

private def rimEndRegion (d : ℕ) (top : Bool) : Set (LiteralRim.{u} d top) :=
  {r | r.val.2 ∈ ({selectedHeight.{u} top} : Set TopCat.I.{u})}

private theorem rimSideRegion_closed (d : ℕ) (top : Bool) :
    IsClosed (rimSideRegion.{u} d top) :=
  Topology.CWComplex.isClosedEmbedding_classicalCellDiskPair_map.isClosed_range.preimage
    (continuous_fst.comp continuous_subtype_val)

private theorem rimEndRegion_closed (d : ℕ) (top : Bool) :
    IsClosed (rimEndRegion.{u} d top) := by
  let : T1Space TopCat.I.{u} := (TopCat.I.homeomorph.{u}).symm.t1Space
  exact isClosed_singleton.preimage (continuous_snd.comp continuous_subtype_val)

private theorem rimRegion_cover (d : ℕ) (top : Bool) :
    rimSideRegion.{u} d top ∪ rimEndRegion d top = Set.univ := by
  ext r
  constructor
  · intro _
    exact Set.mem_univ r
  · intro _
    change r.val.1 ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map ∨
      r.val.2 ∈ ({selectedHeight.{u} top} : Set TopCat.I.{u})
    exact Set.mem_unionProd.mp r.property

/-- Recover the actual lifted boundary sphere point from its disk inclusion.
Only the defining coordinate and the derived sphere membership are used. -/
private def rimSideRegionSphere (d : ℕ) (top : Bool) :
    C(rimSideRegion.{u} d top,
      (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) where
  toFun z := ULift.up ⟨z.val.val.1.down.val, by
    rcases z.property with ⟨s, hs⟩
    have heq : s.down.val = z.val.val.1.down.val :=
      congrArg
        (fun q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst => q.down.val) hs
    exact heq ▸ s.down.property⟩
  continuous_toFun := by
    have h₁ : Continuous (fun z : rimSideRegion.{u} d top =>
        (z.val : LiteralRim.{u} d top)) := continuous_subtype_val
    have h₂ : Continuous (fun z : rimSideRegion.{u} d top => z.val.val) :=
      (show Continuous (Subtype.val : LiteralRim.{u} d top → LiteralCylinder.{u} d)
        from continuous_subtype_val).comp h₁
    have h₃ : Continuous (fun z : rimSideRegion.{u} d top => z.val.val.1) :=
      continuous_fst.comp h₂
    have h₄ : Continuous (fun z : rimSideRegion.{u} d top => z.val.val.1.down) :=
      continuous_uliftDown.comp h₃
    have hv : Continuous (fun z : rimSideRegion.{u} d top => z.val.val.1.down.val) :=
      continuous_subtype_val.comp h₄
    have hm (z : rimSideRegion.{u} d top) :
        z.val.val.1.down.val ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
      rcases z.property with ⟨q, hq⟩
      have heq : q.down.val = z.val.val.1.down.val :=
        congrArg (fun p : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst =>
          p.down.val) hq
      exact heq ▸ q.down.property
    exact continuous_uliftUp.comp (hv.subtype_mk hm)

private theorem rimSideRegionSphere_inclusion (d : ℕ) (top : Bool)
    (z : rimSideRegion.{u} d top) :
    (Topology.CWComplex.classicalCellDiskPair.{u} d).map
        (rimSideRegionSphere d top z) = z.val.val.1 := by
  apply ULift.ext
  apply Subtype.ext
  rfl

private theorem rimSideRegionSphere_side (d : ℕ) (top : Bool)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : TopCat.I.{u}) :
    rimSideRegionSphere d top
        ⟨rimSide d top (s, t), Set.mem_range_self s⟩ = s := by
  apply ULift.ext
  apply Subtype.ext
  rfl

private def sideRegionToFamily (d : ℕ) (top : Bool) (i : J) :
    C(rimSideRegion.{u} d top, LiteralSphereFamily (J := J) d) where
  toFun z := ⟨i, (rimSideRegionSphere d top z, z.val.val.2)⟩
  continuous_toFun := continuous_sigmaMk.comp
    ((rimSideRegionSphere d top).continuous.prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))

private def endRegionToFamily (d : ℕ) (top : Bool) (i : J) :
    C(rimEndRegion.{u} d top, EndpointDiskFamily (J := J) d) where
  toFun z := ⟨i, z.val.val.1⟩
  continuous_toFun := continuous_sigmaMk.comp
    (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))

private def rimSidePieceMap (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J) :
    C(rimSideRegion.{u} d top, diskEndAttachment d h top) :=
  (diskEndOld d h top).hom.comp (h.comp (sideRegionToFamily d top i))

private def rimEndPieceMap (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J) :
    C(rimEndRegion.{u} d top, diskEndAttachment d h top) :=
  (diskEndDisks d h top).hom.comp (endRegionToFamily d top i)

private theorem rimPieceMaps_agree (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J)
    (r : LiteralRim.{u} d top)
    (hs : r ∈ rimSideRegion d top) (he : r ∈ rimEndRegion d top) :
    rimSidePieceMap d h top i ⟨r, hs⟩ =
      rimEndPieceMap d h top i ⟨r, he⟩ := by
  have ht : r.val.2 = selectedHeight.{u} top := Set.mem_singleton_iff.mp he
  let s := rimSideRegionSphere d top ⟨r, hs⟩
  change diskEndOld d h top
      (h ⟨i, (s, r.val.2)⟩) =
    diskEndDisks d h top ⟨i, r.val.1⟩
  calc
    diskEndOld d h top (h ⟨i, (s, r.val.2)⟩) =
        diskEndOld d h top (h ⟨i, (s, selectedHeight.{u} top)⟩) :=
      congrArg (fun t : TopCat.I.{u} => diskEndOld d h top (h ⟨i, (s, t)⟩)) ht
    _ = diskEndDisks d h top
        ⟨i, (Topology.CWComplex.classicalCellDiskPair.{u} d).map s⟩ :=
      ConcreteCategory.congr_hom
        (pushout.condition
          (f := TopCat.ofHom (endpointBoundary d h top))
          (g := TopCat.ofHom (endpointSphereInclusion (J := J) d))) ⟨i, s⟩
    _ = diskEndDisks d h top ⟨i, r.val.1⟩ :=
      congrArg
        (fun q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst =>
          diskEndDisks d h top ⟨i, q⟩)
        (rimSideRegionSphere_inclusion d top ⟨r, hs⟩)

private theorem rimCellToEnd_exists (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J) :
    ∃ F : C(LiteralRim.{u} d top, diskEndAttachment d h top),
      F.restrict (rimSideRegion d top) = rimSidePieceMap d h top i ∧
        F.restrict (rimEndRegion d top) = rimEndPieceMap d h top i :=
  TopCat.exists_continuousMap_glue_of_closed_cover
    (X := TopCat.of (LiteralRim.{u} d top))
    (rimSideRegion_closed d top) (rimEndRegion_closed d top) (rimRegion_cover d top)
    (rimSidePieceMap d h top i) (rimEndPieceMap d h top i)
    (rimPieceMaps_agree d h top i)

private def rimCellToEnd (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J) :
    C(LiteralRim.{u} d top, diskEndAttachment d h top) :=
  Classical.choose (rimCellToEnd_exists d h top i)

private theorem rimCellToEnd_side_region (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J)
    (z : rimSideRegion.{u} d top) :
    rimCellToEnd d h top i z.val = rimSidePieceMap d h top i z := by
  have hpoint := congrArg
    (fun F : C(rimSideRegion.{u} d top, diskEndAttachment d h top) => F z)
    (Classical.choose_spec (rimCellToEnd_exists d h top i)).1
  simpa only [rimCellToEnd, ContinuousMap.restrict_apply] using! hpoint

private theorem rimCellToEnd_end_region (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J)
    (z : rimEndRegion.{u} d top) :
    rimCellToEnd d h top i z.val = rimEndPieceMap d h top i z := by
  have hpoint := congrArg
    (fun F : C(rimEndRegion.{u} d top, diskEndAttachment d h top) => F z)
    (Classical.choose_spec (rimCellToEnd_exists d h top i)).2
  simpa only [rimCellToEnd, ContinuousMap.restrict_apply] using! hpoint

private theorem rimCellToEnd_side (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : TopCat.I.{u}) :
    rimCellToEnd d h top i (rimSide d top (s, t)) =
      diskEndOld d h top (h ⟨i, (s, t)⟩) := by
  have hpoint := rimCellToEnd_side_region d h top i
    ⟨rimSide d top (s, t), Set.mem_range_self s⟩
  change rimCellToEnd d h top i (rimSide d top (s, t)) =
    diskEndOld d h top
      (h ⟨i, (rimSideRegionSphere d top
        ⟨rimSide d top (s, t), Set.mem_range_self s⟩, t)⟩) at hpoint
  rw [rimSideRegionSphere_side] at hpoint
  exact hpoint

private theorem rimCellToEnd_end (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (i : J)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    rimCellToEnd d h top i (rimEndPoint d top q) =
      diskEndDisks d h top ⟨i, q⟩ :=
  rimCellToEnd_end_region d h top i
    ⟨rimEndPoint d top q, Set.mem_singleton_iff.mpr rfl⟩

/-- Coproduct continuity preserves arbitrary and empty index families. -/
private def rimFamilyToEnd (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    C(LiteralRimFamily (J := J) d top, diskEndAttachment d h top) where
  toFun x := rimCellToEnd d h top x.1 x.2
  continuous_toFun := continuous_sigma fun i => (rimCellToEnd d h top i).continuous

private theorem rimToEnd_square (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    TopCat.ofHom h ≫ diskEndOld d h top =
      TopCat.ofHom (rimFamilySide (J := J) d top) ≫
        TopCat.ofHom (rimFamilyToEnd d h top) := by
  apply TopCat.ext
  rintro ⟨i, s, t⟩
  exact (rimCellToEnd_side d h top i s t).symm

private def rimToEndAttachment (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    rimAttachment d h top ⟶ diskEndAttachment d h top :=
  pushout.desc (diskEndOld d h top) (TopCat.ofHom (rimFamilyToEnd d h top))
    (rimToEnd_square d h top)

private theorem endToRim_square (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    TopCat.ofHom (endpointBoundary d h top) ≫ rimOld d h top =
      TopCat.ofHom (endpointSphereInclusion (J := J) d) ≫
        (TopCat.ofHom (endpointRimFamily d top) ≫ rimDisks d h top) := by
  apply TopCat.ext
  rintro ⟨i, s⟩
  exact ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom h)
      (g := TopCat.ofHom (rimFamilySide (J := J) d top)))
    ⟨i, (s, selectedHeight.{u} top)⟩

private def endToRimAttachment (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    diskEndAttachment d h top ⟶ rimAttachment d h top :=
  pushout.desc (rimOld d h top)
    (TopCat.ofHom (endpointRimFamily d top) ≫ rimDisks d h top)
    (endToRim_square d h top)

private theorem rimToEndAttachment_old (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (w : W) :
    rimToEndAttachment d h top (rimOld d h top w) = diskEndOld d h top w :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) w

private theorem rimToEndAttachment_rim (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (r : LiteralRimFamily (J := J) d top) :
    rimToEndAttachment d h top (rimDisks d h top r) = rimFamilyToEnd d h top r := by
  have hm : pushout.inr (TopCat.ofHom h) (TopCat.ofHom (rimFamilySide (J := J) d top)) ≫
      pushout.desc (diskEndOld d h top) (TopCat.ofHom (rimFamilyToEnd d h top)) (rimToEnd_square d h top) = (TopCat.ofHom (rimFamilyToEnd d h top)) :=
    pushout.inr_desc (diskEndOld d h top) (TopCat.ofHom (rimFamilyToEnd d h top)) (rimToEnd_square d h top)
  have hp := congrArg (fun k : TopCat.of (LiteralRimFamily (J := J) d top) ⟶ diskEndAttachment d h top => k.hom r) hm
  simpa only [rimToEndAttachment, rimDisks, TopCat.hom_comp, TopCat.hom_ofHom,
    ContinuousMap.comp_apply, ContinuousMap.coe_apply, ContinuousMap.coe_mk] using! hp

private theorem endToRimAttachment_old (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (w : W) :
    endToRimAttachment d h top (diskEndOld d h top w) = rimOld d h top w :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) w

private theorem endToRimAttachment_disk (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (q : EndpointDiskFamily (J := J) d) :
    endToRimAttachment d h top (diskEndDisks d h top q) =
      rimDisks d h top (endpointRimFamily d top q) := by
  have hm : pushout.inr (TopCat.ofHom (endpointBoundary d h top)) (TopCat.ofHom (endpointSphereInclusion (J := J) d)) ≫
      pushout.desc (rimOld d h top) (TopCat.ofHom (endpointRimFamily d top) ≫ rimDisks d h top) (endToRim_square d h top) = (TopCat.ofHom (endpointRimFamily d top) ≫ rimDisks d h top) :=
    pushout.inr_desc (rimOld d h top) (TopCat.ofHom (endpointRimFamily d top) ≫ rimDisks d h top) (endToRim_square d h top)
  have hp := congrArg (fun k : TopCat.of (EndpointDiskFamily (J := J) d) ⟶ rimAttachment d h top => k.hom q) hm
  simpa only [endToRimAttachment, diskEndDisks, TopCat.hom_comp, TopCat.hom_ofHom,
    ContinuousMap.comp_apply, ContinuousMap.coe_apply, ContinuousMap.coe_mk] using! hp

private theorem endToRim_rimToEnd (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (x : rimAttachment d h top) :
    endToRimAttachment d h top (rimToEndAttachment d h top x) = x := by
  let hs := IsPushout.of_hasPushout (TopCat.ofHom h)
    (TopCat.ofHom (rimFamilySide (J := J) d top))
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨w, rfl⟩
    change endToRimAttachment d h top
      (rimToEndAttachment d h top (rimOld d h top w)) = rimOld d h top w
    exact (congrArg (endToRimAttachment d h top)
      (rimToEndAttachment_old d h top w)).trans (endToRimAttachment_old d h top w)
  · rcases hx with ⟨⟨i, ⟨⟨q, t⟩, hr⟩⟩, rfl⟩
    change endToRimAttachment d h top
      (rimToEndAttachment d h top (rimDisks d h top ⟨i, ⟨(q, t), hr⟩⟩)) =
        rimDisks d h top ⟨i, ⟨(q, t), hr⟩⟩
    have hcell : endToRimAttachment d h top
        (rimCellToEnd d h top i ⟨(q, t), hr⟩) = rimDisks d h top ⟨i, ⟨(q, t), hr⟩⟩ := by
      rcases Set.mem_unionProd.mp hr with hb | he
      · rcases hb with ⟨v, rfl⟩
        change endToRimAttachment d h top
          (rimCellToEnd d h top i (rimSide d top (v, t))) =
            rimDisks d h top (rimFamilySide d top ⟨i, (v, t)⟩)
        have hc : rimOld d h top (h ⟨i, (v, t)⟩) =
            rimDisks d h top (rimFamilySide d top ⟨i, (v, t)⟩) := by
          simpa only [rimOld, rimDisks, TopCat.comp_app, TopCat.hom_ofHom] using!
            ConcreteCategory.congr_hom
              (pushout.condition (f := TopCat.ofHom h)
                (g := TopCat.ofHom (rimFamilySide (J := J) d top))) ⟨i, (v, t)⟩
        exact (congrArg (endToRimAttachment d h top) (rimCellToEnd_side d h top i v t)).trans
          ((endToRimAttachment_old d h top (h ⟨i, (v, t)⟩)).trans hc)
      · have ht : t = selectedHeight.{u} top := Set.mem_singleton_iff.mp he
        subst t
        change endToRimAttachment d h top (rimCellToEnd d h top i (rimEndPoint d top q)) =
          rimDisks d h top (endpointRimFamily d top ⟨i, q⟩)
        exact (congrArg (endToRimAttachment d h top) (rimCellToEnd_end d h top i q)).trans
          (endToRimAttachment_disk d h top ⟨i, q⟩)
    have hi : rimToEndAttachment d h top (rimDisks d h top ⟨i, ⟨(q, t), hr⟩⟩) =
        rimCellToEnd d h top i ⟨(q, t), hr⟩ := by
      simpa only [rimFamilyToEnd, ContinuousMap.coe_mk] using!
        rimToEndAttachment_rim d h top ⟨i, ⟨(q, t), hr⟩⟩
    exact (congrArg (endToRimAttachment d h top) hi).trans hcell

private theorem rimToEnd_endToRim (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (x : diskEndAttachment d h top) :
    rimToEndAttachment d h top (endToRimAttachment d h top x) = x := by
  let hs := IsPushout.of_hasPushout (TopCat.ofHom (endpointBoundary d h top))
    (TopCat.ofHom (endpointSphereInclusion (J := J) d))
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨w, rfl⟩
    change rimToEndAttachment d h top
      (endToRimAttachment d h top (diskEndOld d h top w)) = diskEndOld d h top w
    exact (congrArg (rimToEndAttachment d h top)
      (endToRimAttachment_old d h top w)).trans (rimToEndAttachment_old d h top w)
  · rcases hx with ⟨⟨i, q⟩, rfl⟩
    change rimToEndAttachment d h top
      (endToRimAttachment d h top (diskEndDisks d h top ⟨i, q⟩)) =
        diskEndDisks d h top ⟨i, q⟩
    have hc : rimToEndAttachment d h top
        (rimDisks d h top (endpointRimFamily d top ⟨i, q⟩)) =
          rimCellToEnd d h top i (rimEndPoint d top q) := by
      simpa only [rimFamilyToEnd, endpointRimFamily, ContinuousMap.coe_mk] using!
        rimToEndAttachment_rim d h top (endpointRimFamily d top ⟨i, q⟩)
    exact (congrArg (rimToEndAttachment d h top) (endToRimAttachment_disk d h top ⟨i, q⟩)).trans
      (hc.trans (rimCellToEnd_end d h top i q))

private def rimDiskEndPresentationIso (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) :
    rimAttachment d h top ≅ diskEndAttachment d h top where
  hom := rimToEndAttachment d h top
  inv := endToRimAttachment d h top
  hom_inv_id := by
    apply TopCat.ext
    intro x
    exact endToRim_rimToEnd d h top x
  inv_hom_id := by
    apply TopCat.ext
    intro x
    exact rimToEnd_endToRim d h top x

private theorem rimDiskEndPresentationIso_hom_old (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (w : W) :
    (rimDiskEndPresentationIso d h top).hom (rimOld d h top w) =
      diskEndOld d h top w :=
  rimToEndAttachment_old d h top w

private theorem rimDiskEndPresentationIso_inv_old (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool) (w : W) :
    (rimDiskEndPresentationIso d h top).inv (diskEndOld d h top w) =
      rimOld d h top w :=
  endToRimAttachment_old d h top w

private theorem rimDiskEndPresentationIso_hom_end_disk (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (q : EndpointDiskFamily (J := J) d) :
    (rimDiskEndPresentationIso d h top).hom
        (rimDisks d h top (endpointRimFamily d top q)) =
      diskEndDisks d h top q := by
  rw [show (rimDiskEndPresentationIso d h top).hom = rimToEndAttachment d h top from rfl,
    rimToEndAttachment_rim]
  exact rimCellToEnd_end d h top q.1 q.2

private theorem rimDiskEndPresentationIso_inv_end_disk (d : ℕ)
    (h : C(LiteralSphereFamily (J := J) d, W)) (top : Bool)
    (q : EndpointDiskFamily (J := J) d) :
    (rimDiskEndPresentationIso d h top).inv (diskEndDisks d h top q) =
      rimDisks d h top (endpointRimFamily d top q) :=
  endToRimAttachment_disk d h top q

end ActualCommonSuccessorConstruction

end

/- Same-module private source after33 and the rim/disk-end presentation Iso.
Both targets retain the entire same intermediate A. The elementary tube
collapse fixes all A at every time. Retraction of A to an original/polyhedral
recursive end is a separate remaining construction. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open ActualCommonSuccessorConstruction

variable {I : Type u} {A : TopCat.{u}}

private def unitSelectedHeight (top : Bool) : unitInterval :=
  if top then 1 else 0

private theorem normalizedSelectedHeight (top : Bool) :
    (TopCat.I.homeomorph.{u}) (selectedHeight.{u} top) = unitSelectedHeight top := by
  cases top
  · exact TopCat.I.homeomorph_zero.{u}
  · exact TopCat.I.homeomorph_one.{u}

private theorem unitLiteralAttachmentIso_cylinder_point (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (i : I)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) (t : TopCat.I.{u}) :
    (unitLiteralAttachmentIso d H).inv
        (literalDisks d (normalizedLiteralBoundary d H) ⟨i, (q, t)⟩) =
      originalCylinderMap d H i (q, (TopCat.I.homeomorph.{u}) t) := by
  have hx := ConcreteCategory.congr_hom
    (literalAttachment_as_unit_pushout d H).inr_isoPushout_hom
    ⟨i, (q, (TopCat.I.homeomorph.{u}) t)⟩
  change (unitLiteralAttachmentIso d H).inv
      (literalDisks d (normalizedLiteralBoundary d H)
        (diskIntervalFamilyHomeomorph (I := I) d
          ⟨i, (q, (TopCat.I.homeomorph.{u}) t)⟩)) =
    originalCylinderMap d H i (q, (TopCat.I.homeomorph.{u}) t) at hx
  simp only [diskIntervalFamilyHomeomorph,
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply] at hx
  change (unitLiteralAttachmentIso d H).inv
      (literalDisks d (normalizedLiteralBoundary d H)
        ⟨i, (q, (TopCat.I.homeomorph.{u}).symm ((TopCat.I.homeomorph.{u}) t))⟩) =
    originalCylinderMap d H i (q, (TopCat.I.homeomorph.{u}) t) at hx
  rw [Homeomorph.symm_apply_apply] at hx
  exact hx

private abbrev unitDiskEndSpace (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) : TopCat.{u} :=
  diskEndAttachment d (normalizedLiteralBoundary d H) top

private def unitDiskEndInclude (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) :
    unitDiskEndSpace d H top ⟶ refinedTubeSpace d H :=
  (rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv ≫
    unitRimInclude d H top

private def unitDiskEndRetraction (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) :
    refinedTubeSpace d H ⟶ unitDiskEndSpace d H top :=
  unitRimRetraction d H top ≫
    (rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).hom

private theorem unitDiskEndRetraction_include (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool)
    (x : unitDiskEndSpace d H top) :
    unitDiskEndRetraction d H top (unitDiskEndInclude d H top x) = x := by
  let e := rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top
  change e.hom (unitRimRetraction d H top (unitRimInclude d H top (e.inv x))) = x
  rw [unitRimRetraction_include]
  exact ConcreteCategory.congr_hom e.inv_hom_id x

private theorem unitDiskEndInclude_old (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (a : A) :
    unitDiskEndInclude d H top
        (diskEndOld d (normalizedLiteralBoundary d H) top a) =
      oldIntoTubeSpace d H a := by
  change unitRimInclude d H top
      ((rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv
        (diskEndOld d (normalizedLiteralBoundary d H) top a)) = _
  rw [rimDiskEndPresentationIso_inv_old, unitRimInclude_old]

/-- The entire actual selected disk is mapped by the original tube map. -/
private theorem unitDiskEndInclude_disk (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (i : I)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    unitDiskEndInclude d H top
        (diskEndDisks d (normalizedLiteralBoundary d H) top ⟨i, q⟩) =
      originalCylinderMap d H i (q, unitSelectedHeight top) := by
  change unitRimInclude d H top
      ((rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv
        (diskEndDisks d (normalizedLiteralBoundary d H) top ⟨i, q⟩)) = _
  rw [rimDiskEndPresentationIso_inv_end_disk]
  change (unitLiteralAttachmentIso d H).inv
      (includeRimAttachment d (normalizedLiteralBoundary d H) top
        (rimDisks d (normalizedLiteralBoundary d H) top
          (endpointRimFamily d top ⟨i, q⟩))) = _
  rw [includeRimAttachment_rim]
  change (unitLiteralAttachmentIso d H).inv
      (literalDisks d (normalizedLiteralBoundary d H)
        ⟨i, (q, selectedHeight.{u} top)⟩) = _
  rw [unitLiteralAttachmentIso_cylinder_point, normalizedSelectedHeight]

private theorem unitDiskEndRetraction_old (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (a : A) :
    unitDiskEndRetraction d H top (oldIntoTubeSpace d H a) =
      diskEndOld d (normalizedLiteralBoundary d H) top a := by
  rw [← unitDiskEndInclude_old d H top a, unitDiskEndRetraction_include]

private theorem unitDiskEndInclude_closed (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) :
    IsClosedEmbedding (unitDiskEndInclude d H top) :=
  (unitRimInclude_closed d H top).comp
    (TopCat.homeoOfIso
      (rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top)).symm.isClosedEmbedding

private theorem unitDiskEnd_composite (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) :
    (unitRimInclude d H top).hom.comp (unitRimRetraction d H top).hom =
      (unitDiskEndInclude d H top).hom.comp (unitDiskEndRetraction d H top).hom := by
  let e := rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top
  apply ContinuousMap.ext
  intro x
  change unitRimInclude d H top (unitRimRetraction d H top x) =
    unitRimInclude d H top (e.inv (e.hom (unitRimRetraction d H top x)))
  exact (congrArg (unitRimInclude d H top)
    (ConcreteCategory.congr_hom e.hom_inv_id (unitRimRetraction d H top x))).symm

private def unitDiskEndRelativeHomotopy (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (refinedTubeSpace d H))
      ((unitDiskEndInclude d H top).hom.comp (unitDiskEndRetraction d H top).hom)
      (Set.range (unitDiskEndInclude d H top)) := by
  let K := unitRimRelativeHomotopy d H top
  refine
    { toHomotopy := K.toHomotopy.cast rfl (unitDiskEnd_composite d H top)
      prop' := ?_ }
  intro t x hx
  rcases hx with ⟨y, rfl⟩
  change K
      (t, unitRimInclude d H top
        ((rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv y)) =
    unitRimInclude d H top
      ((rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv y)
  exact K.eq_fst t (Set.mem_range_self
    ((rimDiskEndPresentationIso d (normalizedLiteralBoundary d H) top).inv y))

private theorem unitDiskEndRelativeHomotopy_old_fixed (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (t : unitInterval) (a : A) :
    unitDiskEndRelativeHomotopy d H top
        (t, oldIntoTubeSpace d H a) = oldIntoTubeSpace d H a :=
  (unitDiskEndRelativeHomotopy d H top).eq_fst t
    ⟨diskEndOld d (normalizedLiteralBoundary d H) top a,
      unitDiskEndInclude_old d H top a⟩

private theorem unitDiskEndRelativeHomotopy_disk_fixed (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (t : unitInterval) (i : I)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst) :
    unitDiskEndRelativeHomotopy d H top
        (t, originalCylinderMap d H i (q, unitSelectedHeight top)) =
      originalCylinderMap d H i (q, unitSelectedHeight top) :=
  (unitDiskEndRelativeHomotopy d H top).eq_fst t
    ⟨diskEndDisks d (normalizedLiteralBoundary d H) top ⟨i, q⟩,
      unitDiskEndInclude_disk d H top i q⟩

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module PRIVATE successor proof component.
The input retraction/homotopy is the PREVIOUS constructed recursive output.
The attaching boundary factors through its fixed included old end.
All extended maps and both full pushout identities are constructed.

This generic internal recipe still has to be instantiated by the actual
previous-stage and small-family outputs; it is not the final X-only theorem. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace StationaryAttachmentRetractionConstruction47

variable {S V D A : TopCat.{u}}

private abbrev selectedAttachment (f : S ⟶ V) (g : S ⟶ D) : TopCat.{u} :=
  pushout f g

private abbrev retainedAttachment (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) : TopCat.{u} :=
  pushout (f ≫ i) g

private abbrev selectedOld (f : S ⟶ V) (g : S ⟶ D) : V ⟶ selectedAttachment f g :=
  pushout.inl _ _

private abbrev selectedDisks (f : S ⟶ V) (g : S ⟶ D) : D ⟶ selectedAttachment f g :=
  pushout.inr _ _

private abbrev retainedOld (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) :
    A ⟶ retainedAttachment f g i :=
  pushout.inl _ _

private abbrev retainedDisks (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) :
    D ⟶ retainedAttachment f g i :=
  pushout.inr _ _

private theorem attachmentInclude_square (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) :
    f ≫ (i ≫ retainedOld f g i) = g ≫ retainedDisks f g i :=
  (Category.assoc f i (retainedOld f g i)).symm.trans
    (pushout.condition (f := f ≫ i) (g := g))

private def attachmentInclude (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) :
    selectedAttachment f g ⟶ retainedAttachment f g i :=
  pushout.desc (i ≫ retainedOld f g i) (retainedDisks f g i)
    (attachmentInclude_square f g i)

private theorem attachmentRetraction_square (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V) :
    (f ≫ i) ≫ (r ≫ selectedOld f g) = g ≫ selectedDisks f g := by
  apply TopCat.ext
  intro s
  change selectedOld f g (r (i (f s))) = selectedDisks f g (g s)
  exact (congrArg (selectedOld f g) (ConcreteCategory.congr_hom hir (f s))).trans
    (ConcreteCategory.congr_hom (pushout.condition (f := f) (g := g)) s)

private def attachmentRetraction (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V) :
    retainedAttachment f g i ⟶ selectedAttachment f g :=
  pushout.desc (r ≫ selectedOld f g) (selectedDisks f g)
    (attachmentRetraction_square f g i r hir)

private theorem attachmentInclude_old (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) (v : V) :
    attachmentInclude f g i (selectedOld f g v) = retainedOld f g i (i v) :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) v

private theorem attachmentInclude_disk (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) (d : D) :
    attachmentInclude f g i (selectedDisks f g d) = retainedDisks f g i d :=
  ConcreteCategory.congr_hom (pushout.inr_desc _ _ _) d

private theorem attachmentRetraction_old (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V) (a : A) :
    attachmentRetraction f g i r hir (retainedOld f g i a) =
      selectedOld f g (r a) :=
  ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) a

private theorem attachmentRetraction_disk (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V) (d : D) :
    attachmentRetraction f g i r hir (retainedDisks f g i d) =
      selectedDisks f g d :=
  ConcreteCategory.congr_hom (pushout.inr_desc _ _ _) d

private theorem attachmentRetraction_include (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V)
    (x : selectedAttachment f g) :
    attachmentRetraction f g i r hir (attachmentInclude f g i x) = x := by
  let hs := IsPushout.of_hasPushout f g
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨v, rfl⟩
    change attachmentRetraction f g i r hir
      (attachmentInclude f g i (selectedOld f g v)) = selectedOld f g v
    exact (congrArg (attachmentRetraction f g i r hir)
      (attachmentInclude_old f g i v)).trans
        ((attachmentRetraction_old f g i r hir (i v)).trans
          (congrArg (selectedOld f g) (ConcreteCategory.congr_hom hir v)))
  · rcases hx with ⟨d, rfl⟩
    change attachmentRetraction f g i r hir
      (attachmentInclude f g i (selectedDisks f g d)) = selectedDisks f g d
    exact (congrArg (attachmentRetraction f g i r hir)
      (attachmentInclude_disk f g i d)).trans
        (attachmentRetraction_disk f g i r hir d)

/-- Closedness of the previously constructed old end propagates through the
actual attaching pushout, using the ordinary pushout pasting theorem. -/
private theorem attachmentInclude_closed (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A)
    (hi : IsClosedEmbedding i) : IsClosedEmbedding (attachmentInclude f g i) := by
  have hbottom : selectedDisks f g ≫ attachmentInclude f g i = retainedDisks f g i :=
    pushout.inr_desc _ _ _
  have hcomm : i ≫ retainedOld f g i = selectedOld f g ≫ attachmentInclude f g i :=
    (pushout.inl_desc _ _ _).symm
  have houter : IsPushout (f ≫ i) g (retainedOld f g i)
      (selectedDisks f g ≫ attachmentInclude f g i) := by
    rw [hbottom]
    exact IsPushout.of_hasPushout (f ≫ i) g
  have hleft : IsPushout f g (selectedOld f g) (selectedDisks f g) :=
    IsPushout.of_hasPushout f g
  exact TopCat.isClosedEmbedding_of_isPushout
    (houter.of_left hcomm hleft) hi

variable (f : S ⟶ V) (g : S ⟶ D) (i : V ⟶ A) (r : A ⟶ V)
  (hir : i ≫ r = 𝟙 V)
  (H : ContinuousMap.HomotopyRel (ContinuousMap.id A)
    (i.hom.comp r.hom) (Set.range i))

private def attachedOldHomotopy :
    TopCat.Homotopy (retainedOld f g i) (r ≫ i ≫ retainedOld f g i) :=
  (ContinuousMap.Homotopy.refl (retainedOld f g i).hom).comp H.toHomotopy

private theorem attachedHomotopy_initial_square :
    (f ≫ i) ≫ retainedOld f g i = g ≫ retainedDisks f g i :=
  pushout.condition (f := f ≫ i) (g := g)

include hir in
private theorem attachedHomotopy_terminal_square :
    (f ≫ i) ≫ (r ≫ i ≫ retainedOld f g i) = g ≫ retainedDisks f g i := by
  apply TopCat.ext
  intro s
  change retainedOld f g i (i (r (i (f s)))) = retainedDisks f g i (g s)
  exact (congrArg (fun v : V => retainedOld f g i (i v))
    (ConcreteCategory.congr_hom hir (f s))).trans
      (ConcreteCategory.congr_hom (pushout.condition (f := f ≫ i) (g := g)) s)

private theorem attachedHomotopy_compatible (t : unitInterval) (s : S) :
    attachedOldHomotopy f g i r H (t, (f ≫ i) s) =
      TopCat.Homotopy.refl (retainedDisks f g i) (t, g s) := by
  change retainedOld f g i (H (t, i (f s))) = retainedDisks f g i (g s)
  exact (congrArg (retainedOld f g i)
    (H.eq_fst t (Set.mem_range_self (f s)))).trans
      (ConcreteCategory.congr_hom (pushout.condition (f := f ≫ i) (g := g)) s)

private def rawAttachedHomotopy :
    TopCat.Homotopy
      (pushout.desc (retainedOld f g i) (retainedDisks f g i)
        (attachedHomotopy_initial_square f g i))
      (pushout.desc (r ≫ i ≫ retainedOld f g i) (retainedDisks f g i)
        (attachedHomotopy_terminal_square f g i r hir)) :=
  TopCat.Homotopy.pushoutDesc
    (attachedOldHomotopy f g i r H)
    (TopCat.Homotopy.refl (retainedDisks f g i))
    (attachedHomotopy_initial_square f g i)
    (attachedHomotopy_terminal_square f g i r hir)
    (attachedHomotopy_compatible f g i r H)

private theorem rawAttachedHomotopy_old (t : unitInterval) (a : A) :
    rawAttachedHomotopy f g i r hir H (t, retainedOld f g i a) =
      retainedOld f g i (H (t, a)) :=
  TopCat.Homotopy.pushoutDesc_apply_inl _ _ _ _ _ t a

private theorem rawAttachedHomotopy_disk (t : unitInterval) (d : D) :
    rawAttachedHomotopy f g i r hir H (t, retainedDisks f g i d) =
      retainedDisks f g i d :=
  TopCat.Homotopy.pushoutDesc_apply_inr _ _ _ _ _ t d

/-- The entire selected pushout is fixed: both the old included end and every
attached disk point. Its maps use the previous actual stationary retraction. -/
private def attachedStationaryRetractionHomotopy :
    ContinuousMap.HomotopyRel (ContinuousMap.id (retainedAttachment f g i))
      ((attachmentInclude f g i).hom.comp (attachmentRetraction f g i r hir).hom)
      (Set.range (attachmentInclude f g i)) := by
  let K := rawAttachedHomotopy f g i r hir H
  have hzero : ∀ x, K (0, x) = x := by
    intro x
    let hs := IsPushout.of_hasPushout (f ≫ i) g
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
    · rcases hx with ⟨a, rfl⟩
      change rawAttachedHomotopy f g i r hir H (0, retainedOld f g i a) = retainedOld f g i a
      exact (rawAttachedHomotopy_old f g i r hir H 0 a).trans
        (congrArg (retainedOld f g i) (H.toHomotopy.apply_zero a))
    · rcases hx with ⟨d, rfl⟩
      change rawAttachedHomotopy f g i r hir H (0, retainedDisks f g i d) = retainedDisks f g i d
      exact rawAttachedHomotopy_disk f g i r hir H 0 d
  have hone : ∀ x, K (1, x) =
      attachmentInclude f g i (attachmentRetraction f g i r hir x) := by
    intro x
    let hs := IsPushout.of_hasPushout (f ≫ i) g
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
    · rcases hx with ⟨a, rfl⟩
      change rawAttachedHomotopy f g i r hir H (1, retainedOld f g i a) =
        attachmentInclude f g i (attachmentRetraction f g i r hir (retainedOld f g i a))
      have hleft : rawAttachedHomotopy f g i r hir H (1, retainedOld f g i a) =
          retainedOld f g i (i (r a)) :=
        (rawAttachedHomotopy_old f g i r hir H 1 a).trans
          (congrArg (retainedOld f g i) (H.toHomotopy.apply_one a))
      have hright : attachmentInclude f g i
          (attachmentRetraction f g i r hir (retainedOld f g i a)) =
            retainedOld f g i (i (r a)) :=
        (congrArg (attachmentInclude f g i) (attachmentRetraction_old f g i r hir a)).trans
          (attachmentInclude_old f g i (r a))
      exact hleft.trans hright.symm
    · rcases hx with ⟨d, rfl⟩
      change rawAttachedHomotopy f g i r hir H (1, retainedDisks f g i d) =
        attachmentInclude f g i (attachmentRetraction f g i r hir (retainedDisks f g i d))
      exact (rawAttachedHomotopy_disk f g i r hir H 1 d).trans
        ((congrArg (attachmentInclude f g i) (attachmentRetraction_disk f g i r hir d)).trans
          (attachmentInclude_disk f g i d)).symm
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := ?_ }
  intro t x hx
  change K (t, x) = x
  rcases hx with ⟨y, rfl⟩
  let hs := IsPushout.of_hasPushout f g
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) y with hy | hy
  · rcases hy with ⟨v, rfl⟩
    change rawAttachedHomotopy f g i r hir H
      (t, attachmentInclude f g i (selectedOld f g v)) =
        attachmentInclude f g i (selectedOld f g v)
    have hi := attachmentInclude_old f g i v
    exact (congrArg (fun z => rawAttachedHomotopy f g i r hir H (t, z)) hi).trans
      ((rawAttachedHomotopy_old f g i r hir H t (i v)).trans
        ((congrArg (retainedOld f g i) (H.eq_fst t (Set.mem_range_self v))).trans hi.symm))
  · rcases hy with ⟨d, rfl⟩
    change rawAttachedHomotopy f g i r hir H
      (t, attachmentInclude f g i (selectedDisks f g d)) =
        attachmentInclude f g i (selectedDisks f g d)
    have hi := attachmentInclude_disk f g i d
    exact (congrArg (fun z => rawAttachedHomotopy f g i r hir H (t, z)) hi).trans
      ((rawAttachedHomotopy_disk f g i r hir H t d).trans hi.symm)

private theorem attachedStationaryRetractionHomotopy_disk_fixed
    (t : unitInterval) (d : D) :
    attachedStationaryRetractionHomotopy f g i r hir H
        (t, retainedDisks f g i d) = retainedDisks f g i d :=
  (attachedStationaryRetractionHomotopy f g i r hir H).eq_fst t
    ⟨selectedDisks f g d, attachmentInclude_disk f g i d⟩

private theorem attachedStationaryRetractionHomotopy_old_end_fixed
    (t : unitInterval) (v : V) :
    attachedStationaryRetractionHomotopy f g i r hir H
        (t, retainedOld f g i (i v)) = retainedOld f g i (i v) :=
  (attachedStationaryRetractionHomotopy f g i r hir H).eq_fst t
    ⟨selectedOld f g v, attachmentInclude_old f g i v⟩

end StationaryAttachmentRetractionConstruction47

end

/- Same-module private source after34.
The boundary of the actual retained-stage disk attachment is identified
with the actual original sphere map followed by the previous constructed end.
This supplies the concrete span required by the stationary pushout lift. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open ActualCommonSuccessorConstruction

variable {I : Type u} {A : TopCat.{u}}

private theorem normalizedEndpointBoundary_value (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (i : I)
    (s : (classicalCellDiskPair.{u} d).snd) :
    endpointBoundary d (normalizedLiteralBoundary d H) top ⟨i, s⟩ =
      H ⟨i, (s, unitSelectedHeight top)⟩ := by
  change H ((sphereIntervalFamilyHomeomorph (I := I) d).symm
      ⟨i, (s, selectedHeight.{u} top)⟩) = H ⟨i, (s, unitSelectedHeight top)⟩
  simp only [sphereIntervalFamilyHomeomorph,
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_symm_apply]
  change H ⟨i, (s, (TopCat.I.homeomorph.{u}) (selectedHeight.{u} top))⟩ =
    H ⟨i, (s, unitSelectedHeight top)⟩
  rw [normalizedSelectedHeight]

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem originalDiskEnd_boundary_factorization (d : ℕ)
    (H : C(sideSum (I := Topology.CWComplex.cell (Set.univ : Set X) d) d, A))
    (g0 : C(skeletonTop X d, A))
    (hstart : ∀ (i : Topology.CWComplex.cell (Set.univ : Set X) d)
        (s : (classicalCellDiskPair.{u} d).snd),
      H ⟨i, (s, 0)⟩ = g0 (characteristicSphereToSkeleton d i s)) :
    TopCat.ofHom (endpointBoundary d (normalizedLiteralBoundary d H) false) =
      sphereSumToSkeleton X d ≫ TopCat.ofHom g0 := by
  apply TopCat.ext
  rintro ⟨i, s⟩
  change endpointBoundary d (normalizedLiteralBoundary d H) false ⟨i, s⟩ =
    g0 (characteristicSphereToSkeleton d i s)
  exact (normalizedEndpointBoundary_value d H false i s).trans (hstart i s)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module private finite-stage and actual approximation prefix.
The initializer now uses the accepted named CommonZeroSkeletonData.
Both prior Ret/H fields are recursive outputs, never final user premises.
The actual finite sphere approximations are chosen from the proved P2 API.
Compatible CW/T2/end labels remain additional outputs to construct.

This replaces the pre-family prefix of immutable core47 in the future
owning module; the old large-family attachment body is not copied. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

/-- Internal finite-stage state. Its two homotopies are to be constructed by
the same recursion; they are not premises of the eventual X-only export. -/
private structure Stage (n : ℕ) where
  vertices : Type u
  polyhedron : PreAbstractSimplicialComplex vertices
  space : TopCat.{u}
  original : C(Topology.CWComplex.skeletonTop X (n + 1), space)
  polyhedral : C(polyhedron.Realization, space)
  retractOriginal : C(space, Topology.CWComplex.skeletonTop X (n + 1))
  retractPolyhedral : C(space, polyhedron.Realization)
  original_retraction :
    ∀ x, retractOriginal (original x) = x
  polyhedral_retraction :
    ∀ y, retractPolyhedral (polyhedral y) = y
  originalDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id space)
    (original.comp retractOriginal) (Set.range original)
  polyhedralDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id space)
    (polyhedral.comp retractPolyhedral) (Set.range polyhedral)

/-- The actual initial state uses the original strict-bound1 skeleton and
both whole-space stationary families returned by commonZeroSkeleton. -/
private def initialStage : Stage X 0 := by
  let d := Topology.CWComplex.commonZeroSkeleton X
  let h := d.homeomorph
  refine
    { vertices := Topology.CWComplex.cell (Set.univ : Set X) 0
      polyhedron := (⊥ : AbstractSimplicialComplex
        (Topology.CWComplex.cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex
      space := Topology.CWComplex.skeletonTop X 1
      original := ContinuousMap.id _
      polyhedral := (h : C(_, _))
      retractOriginal := ContinuousMap.id _
      retractPolyhedral := (h.symm : C(_, _))
      original_retraction := fun _ => rfl
      polyhedral_retraction := fun y => h.symm_apply_apply y
      originalDeformation :=
        { toHomotopy := d.initialHomotopy.toHomotopy
          prop' := fun t x _ => d.initialHomotopy.eq_fst t (Set.mem_univ x) }
      polyhedralDeformation :=
        { toHomotopy := d.polyhedronHomotopy.toHomotopy
          prop' := fun t x _ => d.polyhedronHomotopy.eq_fst t (Set.mem_univ x) } }

private theorem initialStage_characteristic
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ((initialStage X).polyhedral
      (Realization.vertex (initialStage X).polyhedron j
        ((⊥ : AbstractSimplicialComplex
          (Topology.CWComplex.cell (Set.univ : Set X) 0)).singleton_mem j))).val =
      Topology.CWComplex.map 0 j (0 : Fin 0 → ℝ) :=
  (Topology.CWComplex.commonZeroSkeleton X).homeomorph_vertex j

/-- The actual finite weak sphere is transported only by the canonical lift
of its existing classical max-norm sphere comparison. -/
private def liftedSphereComparison (n : ℕ) :
    (SphereTriangulation.complex n).Realization ≃ₜ
      (Topology.CWComplex.classicalCellDiskPair.{u} n).snd :=
  (SphereTriangulation.sphereHomeomorph n).trans
    (Homeomorph.ulift.{u, 0}).symm

private theorem liftedSphereComparison_coordinate (n : ℕ)
    (x : (SphereTriangulation.complex n).Realization) :
    (liftedSphereComparison.{u} n x).down.val =
      (SphereTriangulation.sphereHomeomorph n x).val := rfl

/-- Complete chosen finite approximation data, retaining its actual carrier
formula and all prescribed literal vertex values. -/
private structure Approximation
    {V : Type u} (Q : PreAbstractSimplicialComplex V) (n : ℕ)
    (b : C((SphereTriangulation.complex n).Realization, Q.Realization)) where
  subdivisions : ℕ
  map : Morphism (subdivisionIter (SphereTriangulation.complex n) subdivisions) Q
  carrier : ContinuousMap.Homotopy
    (b.comp (subdivisionRealizationMap (SphereTriangulation.complex n) subdivisions))
    map.realization
  support : ∀ x, (map.realization x).point.weights.support ⊆
    (b (iteratedHomeomorph (SphereTriangulation.complex n) subdivisions x)).point.weights.support
  coordinate : ∀ t x, (carrier (t, x)).point = Realization.segmentPoint t
    (b (iteratedHomeomorph (SphereTriangulation.complex n) subdivisions x)).point
    (map.realization x).point
  vertices_fixed :
    ∀ a : Vertex (SphereTriangulation.complex n), ∀ c : Vertex Q,
      b (Realization.vertex (SphereTriangulation.complex n) a.val a.property) =
          Realization.vertex Q c.val c.property →
        map.vertexMap (persistentVertex (SphereTriangulation.complex n) subdivisions a) = c ∧
          ∀ t : unitInterval,
            carrier (t, Realization.vertex
              (subdivisionIter (SphereTriangulation.complex n) subdivisions)
              (persistentVertex (SphereTriangulation.complex n) subdivisions a).val
              (persistentVertex (SphereTriangulation.complex n) subdivisions a).property) =
                b (Realization.vertex (SphereTriangulation.complex n) a.val a.property)

private def chooseApproximation {V : Type u} (Q : PreAbstractSimplicialComplex V)
    (n : ℕ) (b : C((SphereTriangulation.complex n).Realization, Q.Realization)) :
    Approximation Q n b := by
  letI : Finite (Face (SphereTriangulation.complex n)) :=
    SphereTriangulation.finite_faces n
  exact Classical.choice (show Nonempty (Approximation Q n b) from by
    obtain ⟨k, g, H, hs, hc, hv⟩ :=
      exists_simplicialApproximation_onSubdivision (SphereTriangulation.complex n) Q b
    exact ⟨⟨k, g, H, hs, hc, hv⟩⟩)

variable {X}

private abbrev CellIndex (n : ℕ) := Topology.CWComplex.cell (Set.univ : Set X) (n + 1)

/-- The exact characteristic attaching map into the preceding common stage,
before any polyhedral approximation is performed. -/
private def originalBoundary {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd, S.space) :=
  S.original.comp (Topology.CWComplex.characteristicSphereToSkeleton (n + 1) j).hom

private def polyhedralBoundary {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C((SphereTriangulation.complex (n + 1)).Realization, S.polyhedron.Realization) :=
  S.retractPolyhedral.comp
    ((originalBoundary S j).comp (liftedSphereComparison.{u} (n + 1) : C(_, _)))

private def cellApproximation {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    Approximation S.polyhedron (n + 1) (polyhedralBoundary S j) :=
  chooseApproximation S.polyhedron (n + 1) (polyhedralBoundary S j)

private abbrev CellVertexType {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :=
  subdivisionVertexType (SphereTriangulation.complex (n + 1))
    (cellApproximation S j).subdivisions

private def cellPolyhedron {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    PreAbstractSimplicialComplex (CellVertexType S j) :=
  subdivisionIter (SphereTriangulation.complex (n + 1))
    (cellApproximation S j).subdivisions

private def cellMap {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    Morphism (cellPolyhedron S j) S.polyhedron :=
  (cellApproximation S j).map

private def cellFiniteFaces {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    Finite (Face (cellPolyhedron S j)) := by
  let : Finite (Face (SphereTriangulation.complex (n + 1))) :=
    SphereTriangulation.finite_faces (n + 1)
  exact finiteFaces_subdivisionIter (SphereTriangulation.complex (n + 1))
    (cellApproximation S j).subdivisions

end ActualCommonSuccessorConstruction

end

/- Same-module private composition of CONSTRUCTED finite collapses.
Isos are used only for genuine presentations of the same attachment.
The full CW/recursion constructor remains a separate unfinished assembly. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualCommonSuccessorConstruction

private structure FiniteCollapse (Y Z : TopCat.{u}) where
  «include» : Z ⟶ Y
  retract : Y ⟶ Z
  retraction : «include» ≫ retract = 𝟙 Z
  deformation : ContinuousMap.HomotopyRel (ContinuousMap.id Y)
    («include».hom.comp retract.hom) (Set.range «include»)

private theorem finiteCollapse_retraction {Y Z : TopCat.{u}}
    (D : FiniteCollapse Y Z) (z : Z) :
    D.retract (D.include z) = z :=
  ConcreteCategory.congr_hom D.retraction z

private def finiteCollapseOfIso {Y Z : TopCat.{u}} (e : Y ≅ Z) :
    FiniteCollapse Y Z where
  «include» := e.inv
  retract := e.hom
  retraction := e.inv_hom_id
  deformation :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) (Set.range e.inv)).cast
      rfl (by
        apply ContinuousMap.ext
        intro y
        exact (ConcreteCategory.congr_hom e.hom_inv_id y).symm)

private def composeFiniteCollapses {Y Z W : TopCat.{u}}
    (D₁ : FiniteCollapse Y Z) (D₂ : FiniteCollapse Z W) :
    FiniteCollapse Y W := by
  let included := D₂.include ≫ D₁.include
  let retracted := D₁.retract ≫ D₂.retract
  have hret : included ≫ retracted = 𝟙 W := by
    apply TopCat.ext
    intro w
    exact (congrArg D₂.retract (finiteCollapse_retraction D₁ (D₂.include w))).trans
      (finiteCollapse_retraction D₂ w)
  let first :
      ContinuousMap.HomotopyRel (ContinuousMap.id Y)
        (D₁.include.hom.comp D₁.retract.hom) (Set.range included) :=
    { toHomotopy := D₁.deformation.toHomotopy
      prop' := by
        intro t y hy
        rcases hy with ⟨w, rfl⟩
        exact D₁.deformation.eq_fst t (Set.mem_range_self (D₂.include w)) }
  let secondOrdinary :=
    (ContinuousMap.Homotopy.refl D₁.include.hom).comp
      (D₂.deformation.toHomotopy.compContinuousMap D₁.retract.hom)
  let second :
      ContinuousMap.HomotopyRel (D₁.include.hom.comp D₁.retract.hom)
        (D₁.include.hom.comp
          ((D₂.include.hom.comp D₂.retract.hom).comp D₁.retract.hom))
        (Set.range included) :=
    { toHomotopy := secondOrdinary
      prop' := by
        intro t y hy
        rcases hy with ⟨w, rfl⟩
        change D₁.include
            (D₂.deformation (t, D₁.retract (D₁.include (D₂.include w)))) =
          D₁.include (D₁.retract (D₁.include (D₂.include w)))
        rw [finiteCollapse_retraction D₁]
        exact congrArg D₁.include (D₂.deformation.eq_fst t (Set.mem_range_self w)) }
  refine
    { «include» := included
      retract := retracted
      retraction := hret
      deformation := (first.trans second).cast rfl ?_ }
  apply ContinuousMap.ext
  intro y
  rfl

private def liftedAttachingCollapse
    {S V D A : TopCat.{u}} (f : S ⟶ V) (g : S ⟶ D)
    (i : V ⟶ A) (r : A ⟶ V) (hir : i ≫ r = 𝟙 V)
    (H : ContinuousMap.HomotopyRel (ContinuousMap.id A)
      (i.hom.comp r.hom) (Set.range i)) :
    FiniteCollapse
      (StationaryAttachmentRetractionConstruction47.retainedAttachment f g i)
      (StationaryAttachmentRetractionConstruction47.selectedAttachment f g) where
  «include» := StationaryAttachmentRetractionConstruction47.attachmentInclude f g i
  retract := StationaryAttachmentRetractionConstruction47.attachmentRetraction f g i r hir
  retraction := by
    apply TopCat.ext
    intro x
    exact StationaryAttachmentRetractionConstruction47.attachmentRetraction_include
      f g i r hir x
  deformation :=
    StationaryAttachmentRetractionConstruction47.attachedStationaryRetractionHomotopy
      f g i r hir H

private def elementaryTubeCollapse {I : Type u} {A : TopCat.{u}}
    (d : ℕ) (H : C(ActualRefinedTubeCharacteristicConstruction47.sideSum (I := I) d, A))
    (top : Bool) :
    FiniteCollapse
      (ActualRefinedTubeCharacteristicConstruction47.refinedTubeSpace d H)
      (ActualRefinedTubeCharacteristicConstruction47.unitDiskEndSpace d H top) where
  «include» := ActualRefinedTubeCharacteristicConstruction47.unitDiskEndInclude d H top
  retract := ActualRefinedTubeCharacteristicConstruction47.unitDiskEndRetraction d H top
  retraction := by
    apply TopCat.ext
    intro x
    exact ActualRefinedTubeCharacteristicConstruction47.unitDiskEndRetraction_include
      d H top x
  deformation :=
    ActualRefinedTubeCharacteristicConstruction47.unitDiskEndRelativeHomotopy d H top

end ActualCommonSuccessorConstruction

end

/- Same-module private successor context from the PREVIOUS recursive Stage.
The finite approximations are the actual chosen P2 outputs. The small family
is constructed from those maps, with its actual old/copied maps and collapse.
The older large-family record is not a supplied successor witness. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

private abbrev smallFamilyComplex {n : ℕ} (S : Stage X n) :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.cylinderFamily
    (cellPolyhedron S) S.polyhedron (cellMap S)

private def smallFamilyOld {n : ℕ} (S : Stage X n) :
    C(S.polyhedron.Realization, (smallFamilyComplex S).Realization) :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).old

private abbrev CopiedSphere {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :=
  (barycentricSubdivision (cellPolyhedron S j)).Realization

private def smallFamilyCopied {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C(CopiedSphere S j, (smallFamilyComplex S).Realization) :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).copied j

private def smallFamilyRetraction {n : ℕ} (S : Stage X n) :
    C((smallFamilyComplex S).Realization, S.polyhedron.Realization) :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).retraction

private theorem smallFamilyRetraction_old {n : ℕ} (S : Stage X n)
    (y : S.polyhedron.Realization) :
    smallFamilyRetraction S (smallFamilyOld S y) = y :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).retraction_old y

private theorem smallFamilyRetraction_copied {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) (x : CopiedSphere S j) :
    smallFamilyRetraction S (smallFamilyCopied S j x) =
      (cellMap S j).realization (barycentricHomeomorph (cellPolyhedron S j) x) :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).retraction_copied j x

private def smallFamilyDeformation {n : ℕ} (S : Stage X n) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallFamilyComplex S).Realization)
      ((smallFamilyOld S).comp (smallFamilyRetraction S)) (Set.range (smallFamilyOld S)) :=
  (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
    (cellMap S) (cellFiniteFaces S)).deformation

private def copiedSphereComparison {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) :
    CopiedSphere S j ≃ₜ (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd :=
  (barycentricHomeomorph (cellPolyhedron S j)).trans
    ((iteratedHomeomorph (SphereTriangulation.complex (n + 1))
      (cellApproximation S j).subdivisions).trans (liftedSphereComparison.{u} (n + 1)))

private abbrev smallIntermediate {n : ℕ} (S : Stage X n) : TopCat.{u} :=
  pushout (TopCat.ofHom S.polyhedral) (TopCat.ofHom (smallFamilyOld S))

private abbrev smallIntermediateOld {n : ℕ} (S : Stage X n) :
    C(S.space, smallIntermediate S) :=
  (pushout.inl (TopCat.ofHom S.polyhedral) (TopCat.ofHom (smallFamilyOld S))).hom

private abbrev smallIntermediateFamily {n : ℕ} (S : Stage X n) :
    C((smallFamilyComplex S).Realization, smallIntermediate S) :=
  (pushout.inr (TopCat.ofHom S.polyhedral) (TopCat.ofHom (smallFamilyOld S))).hom

private def smallIntermediatePolyhedron {n : ℕ} (S : Stage X n) :
    C(S.polyhedron.Realization, smallIntermediate S) :=
  (smallIntermediateOld S).comp S.polyhedral

private theorem smallIntermediate_identification {n : ℕ} (S : Stage X n)
    (y : S.polyhedron.Realization) :
    smallIntermediateOld S (S.polyhedral y) =
      smallIntermediateFamily S (smallFamilyOld S y) :=
  ConcreteCategory.congr_hom
    (pushout.condition (f := TopCat.ofHom S.polyhedral) (g := TopCat.ofHom (smallFamilyOld S))) y

private theorem smallIntermediateOld_closed {n : ℕ} (S : Stage X n) :
    IsClosedEmbedding (smallIntermediateOld S) :=
  TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))).flip
    (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.oldInclusion_isClosedEmbedding
      (cellPolyhedron S) S.polyhedron (cellMap S))

end ActualCommonSuccessorConstruction

end

/- Same-module actual three-piece attaching family.
The old-stage HomotopyRel is the previous recursive output; the carrier is
the chosen P2 approximation; the last piece is the constructed SMALL family
deformation. All original sphere maps are retained. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
universe u
namespace ActualCommonSuccessorConstruction
variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def boundaryNodeZero {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C(CopiedSphere S j, smallIntermediate S) :=
  (smallIntermediateOld S).comp
    ((originalBoundary S j).comp (copiedSphereComparison S j :
        C(CopiedSphere S j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd)))

private def boundaryNodeOne {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C(CopiedSphere S j, smallIntermediate S) :=
  (smallIntermediatePolyhedron S).comp
    (S.retractPolyhedral.comp
      ((originalBoundary S j).comp (copiedSphereComparison S j :
        C(CopiedSphere S j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd))))

private def boundaryNodeTwo {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C(CopiedSphere S j, smallIntermediate S) :=
  (smallIntermediatePolyhedron S).comp
    ((cellMap S j).realization.comp (barycentricHomeomorph (cellPolyhedron S j) :
        C(CopiedSphere S j, (cellPolyhedron S j).Realization)))

private def boundaryNodeThree {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    C(CopiedSphere S j, smallIntermediate S) :=
  (smallIntermediateFamily S).comp (smallFamilyCopied S j)

/-- First piece: the already constructed finite old-stage deformation,
precomposed by the actual original characteristic sphere map. -/
private def firstBoundaryPiece {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    ContinuousMap.Homotopy (boundaryNodeZero S j) (boundaryNodeOne S j) := by
  let H := (ContinuousMap.Homotopy.refl (smallIntermediateOld S)).comp
    (S.polyhedralDeformation.toHomotopy.compContinuousMap
      ((originalBoundary S j).comp (copiedSphereComparison S j :
        C(CopiedSphere S j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd))))
  exact H.cast (by ext x; rfl) (by ext x; rfl)

/-- Second piece: the actual P2 carrier, on the constructed subdivision and
copied barycentric domain, included through the whole old polyhedral end. -/
private def carrierBoundaryPiece {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    ContinuousMap.Homotopy (boundaryNodeOne S j) (boundaryNodeTwo S j) := by
  let H := (ContinuousMap.Homotopy.refl (smallIntermediatePolyhedron S)).comp
    ((cellApproximation S j).carrier.compContinuousMap
      (barycentricHomeomorph (cellPolyhedron S j) :
        C(CopiedSphere S j, (cellPolyhedron S j).Realization)))
  exact H.cast (by ext x; rfl) (by ext x; rfl)

/-- Third piece: reverse the actual family-cylinder deformation on its copied
domain. Its endpoint is obtained from the whole-path family retraction law,
not a supplied endpoint dictionary. -/
private def reversedCylinderBoundaryPiece {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n) :
    ContinuousMap.Homotopy (boundaryNodeTwo S j) (boundaryNodeThree S j) := by
  let H := (ContinuousMap.Homotopy.refl (smallIntermediateFamily S)).comp
    (((smallFamilyDeformation S).toHomotopy.compContinuousMap (smallFamilyCopied S j)).symm)
  refine H.cast ?_ (by ext x; rfl)
  ext x
  change smallIntermediateFamily S
    (smallFamilyOld S (smallFamilyRetraction S (smallFamilyCopied S j x))) =
      smallIntermediateOld S (S.polyhedral
        ((cellMap S j).realization (barycentricHomeomorph (cellPolyhedron S j) x)))
  rw [smallFamilyRetraction_copied S]
  exact (smallIntermediate_identification S _).symm

/-- The three pieces are composed by the existing continuous concatenation:
the old-stage piece occupies [0,1/2], then carrier and reversed-cylinder
pieces occupy [1/2,3/4] and [3/4,1]. -/
private def copiedBoundaryHomotopy {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n) :
    ContinuousMap.Homotopy (boundaryNodeZero S j) (boundaryNodeThree S j) :=
  (firstBoundaryPiece S j).trans
    ((carrierBoundaryPiece S j).trans (reversedCylinderBoundaryPiece S j))

private theorem firstBoundaryPiece_value {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) (t : unitInterval) (x : CopiedSphere S j) :
    firstBoundaryPiece S j (t, x) =
      smallIntermediateOld S (S.polyhedralDeformation
        (t, originalBoundary S j (copiedSphereComparison S j x))) := rfl

private theorem carrierBoundaryPiece_value {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) (t : unitInterval) (x : CopiedSphere S j) :
    carrierBoundaryPiece S j (t, x) =
      smallIntermediatePolyhedron S ((cellApproximation S j).carrier
        (t, barycentricHomeomorph (cellPolyhedron S j) x)) := rfl

private theorem reversedCylinderBoundaryPiece_value {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) (t : unitInterval) (x : CopiedSphere S j) :
    reversedCylinderBoundaryPiece S j (t, x) =
      smallIntermediateFamily S (smallFamilyDeformation S
        (unitInterval.symm t, smallFamilyCopied S j x)) := rfl

private def originalBoundaryInIntermediate {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd, smallIntermediate S) :=
  (smallIntermediateOld S).comp (originalBoundary S j)

private def copiedBoundaryInIntermediate {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd, smallIntermediate S) :=
  (boundaryNodeThree S j).comp ((copiedSphereComparison S j).symm :
      C((Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd, CopiedSphere S j))

/-- The constructed attaching homotopy on the literal original boundary
sphere, rather than an unspecified homotopic map on another sphere. -/
private def originalSphereHomotopy {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n) :
    ContinuousMap.Homotopy (originalBoundaryInIntermediate S j)
      (copiedBoundaryInIntermediate S j) := by
  let H := (copiedBoundaryHomotopy S j).compContinuousMap
    ((copiedSphereComparison S j).symm :
      C((Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd, CopiedSphere S j))
  refine H.cast ?_ rfl
  ext x
  change smallIntermediateOld S
    (originalBoundary S j
      (copiedSphereComparison S j ((copiedSphereComparison S j).symm x))) =
        smallIntermediateOld S (originalBoundary S j x)
  rw [Homeomorph.apply_symm_apply]

private theorem originalSphereHomotopy_zero {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    originalSphereHomotopy S j (0, x) =
      smallIntermediateOld S (S.original
        (Topology.CWComplex.characteristicSphereToSkeleton (n + 1) j x)) :=
  (originalSphereHomotopy S j).apply_zero x

private theorem originalSphereHomotopy_one {n : ℕ}
    (S : Stage X n) (j : CellIndex (X := X) n)
    (x : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    originalSphereHomotopy S j (1, x) =
      smallIntermediateFamily S (smallFamilyCopied S j ((copiedSphereComparison S j).symm x)) :=
  (originalSphereHomotopy S j).apply_one x

private def smallSuccessorBoundary {n : ℕ} (S : Stage X n) :
    C(ActualRefinedTubeCharacteristicConstruction47.sideSum
      (I := CellIndex (X := X) n) (n + 1), smallIntermediate S) where
  toFun p := originalSphereHomotopy S p.1 (p.2.2, p.2.1)
  continuous_toFun := continuous_sigma fun j =>
    (originalSphereHomotopy S j).continuous.comp continuous_swap

private def smallIntermediateOriginal {n : ℕ} (S : Stage X n) :
    C(Topology.CWComplex.skeletonTop X (n + 1), smallIntermediate S) :=
  (smallIntermediateOld S).comp S.original

private theorem smallSuccessorBoundary_zero {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    smallSuccessorBoundary S ⟨j, (s, 0)⟩ =
      smallIntermediateOriginal S
        (Topology.CWComplex.characteristicSphereToSkeleton (n + 1) j s) :=
  originalSphereHomotopy_zero S j s

private theorem smallSuccessorBoundary_one {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    smallSuccessorBoundary S ⟨j, (s, 1)⟩ =
      smallIntermediateFamily S
        (smallFamilyCopied S j ((copiedSphereComparison S j).symm s)) :=
  originalSphereHomotopy_one S j s

end ActualCommonSuccessorConstruction
end

/- Same-module actual intermediate collapses.
A is the computed pushout of the PREVIOUS Stage's polyhedral inclusion and
the constructed small-family old inclusion. No A retraction or A homotopy
is supplied. Both are computed from the previous recursive data and the
actual small-family collapse. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem intermediateToOld_square {n : ℕ} (S : Stage X n) :
    TopCat.ofHom S.polyhedral ≫ 𝟙 S.space =
      TopCat.ofHom (smallFamilyOld S) ≫
        TopCat.ofHom (S.polyhedral.comp (smallFamilyRetraction S)) := by
  apply TopCat.ext
  intro y
  change S.polyhedral y = S.polyhedral (smallFamilyRetraction S (smallFamilyOld S y))
  exact (congrArg S.polyhedral (smallFamilyRetraction_old S y)).symm

private def intermediateToOld {n : ℕ} (S : Stage X n) :
    smallIntermediate S ⟶ S.space :=
  pushout.desc (𝟙 S.space)
    (TopCat.ofHom (S.polyhedral.comp (smallFamilyRetraction S)))
    (intermediateToOld_square S)

private theorem intermediateToOld_old {n : ℕ} (S : Stage X n) (z : S.space) :
    intermediateToOld S (smallIntermediateOld S z) = z :=
  ConcreteCategory.congr_hom
    (pushout.inl_desc (f := TopCat.ofHom S.polyhedral)
      (g := TopCat.ofHom (smallFamilyOld S)) (𝟙 S.space)
      (TopCat.ofHom (S.polyhedral.comp (smallFamilyRetraction S)))
      (intermediateToOld_square S)) z

private theorem intermediateToOld_family {n : ℕ} (S : Stage X n)
    (b : (smallFamilyComplex S).Realization) :
    intermediateToOld S (smallIntermediateFamily S b) =
      S.polyhedral (smallFamilyRetraction S b) :=
  ConcreteCategory.congr_hom
    (pushout.inr_desc (f := TopCat.ofHom S.polyhedral)
      (g := TopCat.ofHom (smallFamilyOld S)) (𝟙 S.space)
      (TopCat.ofHom (S.polyhedral.comp (smallFamilyRetraction S)))
      (intermediateToOld_square S)) b

private def familyIntoIntermediateHomotopy {n : ℕ} (S : Stage X n) :
    ContinuousMap.Homotopy (smallIntermediateFamily S)
      ((smallIntermediateFamily S).comp
        ((smallFamilyOld S).comp (smallFamilyRetraction S))) :=
  (ContinuousMap.Homotopy.refl (smallIntermediateFamily S)).comp
    (smallFamilyDeformation S).toHomotopy

private theorem intermediateHomotopy_initial_square {n : ℕ} (S : Stage X n) :
    TopCat.ofHom S.polyhedral ≫ TopCat.ofHom (smallIntermediateOld S) =
      TopCat.ofHom (smallFamilyOld S) ≫ TopCat.ofHom (smallIntermediateFamily S) :=
  pushout.condition (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))

private theorem oldCollapse_terminal_square {n : ℕ} (S : Stage X n) :
    TopCat.ofHom S.polyhedral ≫ TopCat.ofHom (smallIntermediateOld S) =
      TopCat.ofHom (smallFamilyOld S) ≫
        TopCat.ofHom ((smallIntermediateFamily S).comp
          ((smallFamilyOld S).comp (smallFamilyRetraction S))) := by
  apply TopCat.ext
  intro y
  change smallIntermediateOld S (S.polyhedral y) =
    smallIntermediateFamily S (smallFamilyOld S (smallFamilyRetraction S (smallFamilyOld S y)))
  rw [smallFamilyRetraction_old]
  exact smallIntermediate_identification S y

private theorem oldCollapse_compatible {n : ℕ} (S : Stage X n)
    (t : unitInterval) (y : S.polyhedron.Realization) :
    ContinuousMap.Homotopy.refl (smallIntermediateOld S) (t, S.polyhedral y) =
      familyIntoIntermediateHomotopy S (t, smallFamilyOld S y) := by
  change smallIntermediateOld S (S.polyhedral y) =
    smallIntermediateFamily S (smallFamilyDeformation S (t, smallFamilyOld S y))
  rw [(smallFamilyDeformation S).eq_fst t (Set.mem_range_self y)]
  exact smallIntermediate_identification S y

private def rawIntermediateOldHomotopy {n : ℕ} (S : Stage X n) :=
  TopCat.Homotopy.pushoutDesc (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (ContinuousMap.Homotopy.refl (smallIntermediateOld S))
    (familyIntoIntermediateHomotopy S)
    (intermediateHomotopy_initial_square S)
    (oldCollapse_terminal_square S)
    (oldCollapse_compatible S)

private theorem rawIntermediateOldHomotopy_old {n : ℕ} (S : Stage X n)
    (t : unitInterval) (z : S.space) :
    rawIntermediateOldHomotopy S (t, smallIntermediateOld S z) = smallIntermediateOld S z :=
  TopCat.Homotopy.pushoutDesc_apply_inl (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (ContinuousMap.Homotopy.refl (smallIntermediateOld S))
    (familyIntoIntermediateHomotopy S) (intermediateHomotopy_initial_square S)
    (oldCollapse_terminal_square S) (oldCollapse_compatible S) t z

private theorem rawIntermediateOldHomotopy_family {n : ℕ} (S : Stage X n)
    (t : unitInterval) (b : (smallFamilyComplex S).Realization) :
    rawIntermediateOldHomotopy S (t, smallIntermediateFamily S b) =
      smallIntermediateFamily S (smallFamilyDeformation S (t, b)) :=
  TopCat.Homotopy.pushoutDesc_apply_inr (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (ContinuousMap.Homotopy.refl (smallIntermediateOld S))
    (familyIntoIntermediateHomotopy S) (intermediateHomotopy_initial_square S)
    (oldCollapse_terminal_square S) (oldCollapse_compatible S) t b

private def intermediateOldDeformation {n : ℕ} (S : Stage X n) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallIntermediate S))
      ((smallIntermediateOld S).comp (intermediateToOld S).hom)
      (Set.range (smallIntermediateOld S)) := by
  let K := rawIntermediateOldHomotopy S
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro a
    let hs := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨z, rfl⟩
      exact rawIntermediateOldHomotopy_old S 0 z
    · rcases ha with ⟨b, rfl⟩
      simpa only [ContinuousMap.id_apply] using!
        (rawIntermediateOldHomotopy_family S 0 b).trans
          (congrArg (smallIntermediateFamily S)
            ((smallFamilyDeformation S).toHomotopy.apply_zero b))
  · intro a
    let hs := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨z, rfl⟩
      simpa only [ContinuousMap.comp_apply] using!
        (rawIntermediateOldHomotopy_old S 1 z).trans
          (congrArg (smallIntermediateOld S) (intermediateToOld_old S z)).symm
    · rcases ha with ⟨b, rfl⟩
      simpa only [ContinuousMap.comp_apply] using! (calc
        rawIntermediateOldHomotopy S (1, smallIntermediateFamily S b) =
            smallIntermediateFamily S (smallFamilyDeformation S (1, b)) :=
          rawIntermediateOldHomotopy_family S 1 b
        _ = smallIntermediateFamily S (smallFamilyOld S (smallFamilyRetraction S b)) :=
          congrArg (smallIntermediateFamily S) ((smallFamilyDeformation S).toHomotopy.apply_one b)
        _ = smallIntermediateOld S (S.polyhedral (smallFamilyRetraction S b)) :=
          (smallIntermediate_identification S (smallFamilyRetraction S b)).symm
        _ = smallIntermediateOld S (intermediateToOld S (smallIntermediateFamily S b)) :=
          (congrArg (smallIntermediateOld S) (intermediateToOld_family S b)).symm)
  · intro t a ha
    rcases ha with ⟨z, rfl⟩
    exact rawIntermediateOldHomotopy_old S t z

private def actualIntermediateOldCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse (smallIntermediate S) S.space where
  «include» := TopCat.ofHom (smallIntermediateOld S)
  retract := intermediateToOld S
  retraction := by
    apply TopCat.ext
    intro z
    exact intermediateToOld_old S z
  deformation := intermediateOldDeformation S

private theorem intermediateToFamily_square {n : ℕ} (S : Stage X n) :
    TopCat.ofHom S.polyhedral ≫
        TopCat.ofHom ((smallFamilyOld S).comp S.retractPolyhedral) =
      TopCat.ofHom (smallFamilyOld S) ≫
        𝟙 (TopCat.of ((smallFamilyComplex S).Realization)) := by
  apply TopCat.ext
  intro y
  change smallFamilyOld S (S.retractPolyhedral (S.polyhedral y)) = smallFamilyOld S y
  exact congrArg (smallFamilyOld S) (S.polyhedral_retraction y)

private def intermediateToFamily {n : ℕ} (S : Stage X n) :
    smallIntermediate S ⟶ TopCat.of ((smallFamilyComplex S).Realization) :=
  pushout.desc (TopCat.ofHom ((smallFamilyOld S).comp S.retractPolyhedral))
    (𝟙 (TopCat.of ((smallFamilyComplex S).Realization))) (intermediateToFamily_square S)

private theorem intermediateToFamily_old {n : ℕ} (S : Stage X n) (z : S.space) :
    intermediateToFamily S (smallIntermediateOld S z) =
      smallFamilyOld S (S.retractPolyhedral z) :=
  ConcreteCategory.congr_hom
    (pushout.inl_desc (f := TopCat.ofHom S.polyhedral)
      (g := TopCat.ofHom (smallFamilyOld S))
      (TopCat.ofHom ((smallFamilyOld S).comp S.retractPolyhedral))
      (𝟙 (TopCat.of ((smallFamilyComplex S).Realization)))
      (intermediateToFamily_square S)) z

private theorem intermediateToFamily_family {n : ℕ} (S : Stage X n)
    (b : (smallFamilyComplex S).Realization) :
    intermediateToFamily S (smallIntermediateFamily S b) = b :=
  ConcreteCategory.congr_hom
    (pushout.inr_desc (f := TopCat.ofHom S.polyhedral)
      (g := TopCat.ofHom (smallFamilyOld S))
      (TopCat.ofHom ((smallFamilyOld S).comp S.retractPolyhedral))
      (𝟙 (TopCat.of ((smallFamilyComplex S).Realization)))
      (intermediateToFamily_square S)) b

private def previousPolyhedralIntoIntermediateHomotopy {n : ℕ} (S : Stage X n) :=
  (ContinuousMap.Homotopy.refl (smallIntermediateOld S)).comp
    S.polyhedralDeformation.toHomotopy

private theorem familyCollapse_terminal_square {n : ℕ} (S : Stage X n) :
    TopCat.ofHom S.polyhedral ≫
        TopCat.ofHom ((smallIntermediateOld S).comp
          (S.polyhedral.comp S.retractPolyhedral)) =
      TopCat.ofHom (smallFamilyOld S) ≫ TopCat.ofHom (smallIntermediateFamily S) := by
  apply TopCat.ext
  intro y
  change smallIntermediateOld S (S.polyhedral (S.retractPolyhedral (S.polyhedral y))) =
    smallIntermediateFamily S (smallFamilyOld S y)
  rw [S.polyhedral_retraction]
  exact smallIntermediate_identification S y

private theorem familyCollapse_compatible {n : ℕ} (S : Stage X n)
    (t : unitInterval) (y : S.polyhedron.Realization) :
    previousPolyhedralIntoIntermediateHomotopy S (t, S.polyhedral y) =
      ContinuousMap.Homotopy.refl (smallIntermediateFamily S) (t, smallFamilyOld S y) := by
  change smallIntermediateOld S (S.polyhedralDeformation (t, S.polyhedral y)) =
    smallIntermediateFamily S (smallFamilyOld S y)
  rw [S.polyhedralDeformation.eq_fst t (Set.mem_range_self y)]
  exact smallIntermediate_identification S y

private def rawIntermediateFamilyHomotopy {n : ℕ} (S : Stage X n) :=
  TopCat.Homotopy.pushoutDesc (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (previousPolyhedralIntoIntermediateHomotopy S)
    (ContinuousMap.Homotopy.refl (smallIntermediateFamily S))
    (intermediateHomotopy_initial_square S)
    (familyCollapse_terminal_square S)
    (familyCollapse_compatible S)

private theorem rawIntermediateFamilyHomotopy_old {n : ℕ} (S : Stage X n)
    (t : unitInterval) (z : S.space) :
    rawIntermediateFamilyHomotopy S (t, smallIntermediateOld S z) =
      smallIntermediateOld S (S.polyhedralDeformation (t, z)) :=
  TopCat.Homotopy.pushoutDesc_apply_inl (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (previousPolyhedralIntoIntermediateHomotopy S)
    (ContinuousMap.Homotopy.refl (smallIntermediateFamily S))
    (intermediateHomotopy_initial_square S) (familyCollapse_terminal_square S)
    (familyCollapse_compatible S) t z

private theorem rawIntermediateFamilyHomotopy_family {n : ℕ} (S : Stage X n)
    (t : unitInterval) (b : (smallFamilyComplex S).Realization) :
    rawIntermediateFamilyHomotopy S (t, smallIntermediateFamily S b) =
      smallIntermediateFamily S b :=
  TopCat.Homotopy.pushoutDesc_apply_inr (f := TopCat.ofHom S.polyhedral)
    (g := TopCat.ofHom (smallFamilyOld S))
    (previousPolyhedralIntoIntermediateHomotopy S)
    (ContinuousMap.Homotopy.refl (smallIntermediateFamily S))
    (intermediateHomotopy_initial_square S) (familyCollapse_terminal_square S)
    (familyCollapse_compatible S) t b

private def intermediateFamilyDeformation {n : ℕ} (S : Stage X n) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (smallIntermediate S))
      ((smallIntermediateFamily S).comp (intermediateToFamily S).hom)
      (Set.range (smallIntermediateFamily S)) := by
  let K := rawIntermediateFamilyHomotopy S
  refine
    { toFun := K
      continuous_toFun := K.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro a
    let hs := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨z, rfl⟩
      simpa only [ContinuousMap.id_apply] using!
        (rawIntermediateFamilyHomotopy_old S 0 z).trans
          (congrArg (smallIntermediateOld S) (S.polyhedralDeformation.toHomotopy.apply_zero z))
    · rcases ha with ⟨b, rfl⟩
      exact rawIntermediateFamilyHomotopy_family S 0 b
  · intro a
    let hs := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) a with ha | ha
    · rcases ha with ⟨z, rfl⟩
      simpa only [ContinuousMap.comp_apply] using! (calc
        rawIntermediateFamilyHomotopy S (1, smallIntermediateOld S z) =
            smallIntermediateOld S (S.polyhedralDeformation (1, z)) :=
          rawIntermediateFamilyHomotopy_old S 1 z
        _ = smallIntermediateOld S (S.polyhedral (S.retractPolyhedral z)) :=
          congrArg (smallIntermediateOld S) (S.polyhedralDeformation.toHomotopy.apply_one z)
        _ = smallIntermediateFamily S (smallFamilyOld S (S.retractPolyhedral z)) :=
          smallIntermediate_identification S (S.retractPolyhedral z)
        _ = smallIntermediateFamily S (intermediateToFamily S (smallIntermediateOld S z)) :=
          (congrArg (smallIntermediateFamily S) (intermediateToFamily_old S z)).symm)
    · rcases ha with ⟨b, rfl⟩
      simpa only [ContinuousMap.comp_apply] using!
        (rawIntermediateFamilyHomotopy_family S 1 b).trans
          (congrArg (smallIntermediateFamily S) (intermediateToFamily_family S b)).symm
  · intro t a ha
    rcases ha with ⟨b, rfl⟩
    exact rawIntermediateFamilyHomotopy_family S t b

private def actualIntermediateFamilyCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse (smallIntermediate S) (TopCat.of ((smallFamilyComplex S).Realization)) where
  «include» := TopCat.ofHom (smallIntermediateFamily S)
  retract := intermediateToFamily S
  retraction := by
    apply TopCat.ext
    intro b
    exact intermediateToFamily_family S b
  deformation := intermediateFamilyDeformation S

private def previousOriginalCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse S.space (Topology.CWComplex.skeletonTop X (n + 1)) where
  «include» := TopCat.ofHom S.original
  retract := TopCat.ofHom S.retractOriginal
  retraction := by
    apply TopCat.ext
    intro x
    exact S.original_retraction x
  deformation := S.originalDeformation

private def actualIntermediateOriginalCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse (smallIntermediate S) (Topology.CWComplex.skeletonTop X (n + 1)) :=
  composeFiniteCollapses (actualIntermediateOldCollapse S) (previousOriginalCollapse S)

end ActualCommonSuccessorConstruction

end

/- Same-module actual original-end instantiation of34/35.
The old-end collapse is computed from the previous Stage and small family.
Only genuine pushout presentation Isos occur after the actual reduction.
The complete original successor skeleton is the final target. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open ActualRefinedTubeCharacteristicConstruction47
open StationaryAttachmentRetractionConstruction47
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualSuccessorSpace {n : ℕ} (S : Stage X n) : TopCat.{u} :=
  refinedTubeSpace (n + 1) (smallSuccessorBoundary S)

private theorem actualIntermediateOriginalCollapse_include {n : ℕ} (S : Stage X n) :
    (actualIntermediateOriginalCollapse S).include =
      TopCat.ofHom (smallIntermediateOriginal S) := by
  apply TopCat.ext
  intro x
  rfl

omit [T2Space X] in
private theorem endpointSphereInclusion_original (d : ℕ) :
    TopCat.ofHom (endpointSphereInclusion
      (J := Topology.CWComplex.cell (Set.univ : Set X) d) d) =
      sphereSumToDiskSum X d := by
  apply TopCat.ext
  rintro ⟨i, s⟩
  rfl

private theorem actualOriginalRetainedEnd_square {n : ℕ} (S : Stage X n) :
    IsPushout
      (sphereSumToSkeleton X (n + 1) ≫ (actualIntermediateOriginalCollapse S).include)
      (sphereSumToDiskSum X (n + 1))
      (diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false)
      (diskEndDisks (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false) := by
  have h₀ := originalDiskEnd_boundary_factorization (n + 1) (smallSuccessorBoundary S)
    (smallIntermediateOriginal S) (smallSuccessorBoundary_zero S)
  rw [actualIntermediateOriginalCollapse_include, ← h₀,
    ← endpointSphereInclusion_original (X := X) (n + 1)]
  exact IsPushout.of_hasPushout
    (TopCat.ofHom (endpointBoundary (n + 1)
      (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false))
    (TopCat.ofHom (endpointSphereInclusion
      (J := CellIndex (X := X) n) (n + 1)))

private def actualOriginalRetainedEndIso {n : ℕ} (S : Stage X n) :
    unitDiskEndSpace (n + 1) (smallSuccessorBoundary S) false ≅
      retainedAttachment (sphereSumToSkeleton X (n + 1))
        (sphereSumToDiskSum X (n + 1)) (actualIntermediateOriginalCollapse S).include :=
  (actualOriginalRetainedEnd_square S).isoPushout

private def actualOriginalLiftedCollapse {n : ℕ} (S : Stage X n) :=
  liftedAttachingCollapse
    (sphereSumToSkeleton X (n + 1)) (sphereSumToDiskSum X (n + 1))
    (actualIntermediateOriginalCollapse S).include
    (actualIntermediateOriginalCollapse S).retract
    (actualIntermediateOriginalCollapse S).retraction
    (actualIntermediateOriginalCollapse S).deformation

private def actualOriginalSuccessorCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse (actualSuccessorSpace S) (skeletonTop X ((n + 1) + 1)) :=
  composeFiniteCollapses
    (elementaryTubeCollapse (n + 1) (smallSuccessorBoundary S) false)
    (composeFiniteCollapses (finiteCollapseOfIso (actualOriginalRetainedEndIso S))
      (composeFiniteCollapses (actualOriginalLiftedCollapse S)
        (finiteCollapseOfIso (isPushout_skeletonAttachment X (n + 1)).isoPushout.symm)))

private theorem actualOriginalSuccessorCollapse_old {n : ℕ} (S : Stage X n)
    (x : skeletonTop X (n + 1)) :
    (actualOriginalSuccessorCollapse S).include (skeletonTransition X (n + 1) x) =
      oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (smallIntermediateOriginal S x) := by
  let f := sphereSumToSkeleton X (n + 1)
  let g := sphereSumToDiskSum X (n + 1)
  let c := (actualIntermediateOriginalCollapse S).include
  let e := actualOriginalRetainedEndIso S
  let U := unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) false
  have h₀ : (isPushout_skeletonAttachment X (n + 1)).isoPushout.hom
      (skeletonTransition X (n + 1) x) = selectedOld f g x := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom
        (isPushout_skeletonAttachment X (n + 1)).inl_isoPushout_hom x
  have h₁ : e.inv (retainedOld f g c (c x)) =
      diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S))
        false (c x) := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualOriginalRetainedEnd_square S).inl_isoPushout_inv (c x)
  have hc : c x = smallIntermediateOriginal S x :=
    ConcreteCategory.congr_hom (actualIntermediateOriginalCollapse_include S) x
  change U (e.inv (attachmentInclude f g c
    ((isPushout_skeletonAttachment X (n + 1)).isoPushout.hom
      (skeletonTransition X (n + 1) x)))) = _
  calc
    _ = U (e.inv (attachmentInclude f g c (selectedOld f g x))) :=
      congrArg (fun z : selectedAttachment f g => U (e.inv (attachmentInclude f g c z))) h₀
    _ = U (e.inv (retainedOld f g c (c x))) :=
      congrArg (fun z : retainedAttachment f g c => U (e.inv z)) (attachmentInclude_old f g c x)
    _ = U (diskEndOld (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false (c x)) :=
      congrArg U h₁
    _ = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (c x) :=
      unitDiskEndInclude_old (n + 1) (smallSuccessorBoundary S) false (c x)
    _ = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (smallIntermediateOriginal S x) :=
      congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) hc

/-- The entire actual original closed disk, not only its boundary or center. -/
private theorem actualOriginalSuccessorCollapse_disk {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) (q : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (actualOriginalSuccessorCollapse S).include (characteristicDiskToSkeleton (n + 1) i q) =
      originalCylinderMap (n + 1) (smallSuccessorBoundary S) i (q, 0) := by
  let f := sphereSumToSkeleton X (n + 1)
  let g := sphereSumToDiskSum X (n + 1)
  let c := (actualIntermediateOriginalCollapse S).include
  let e := actualOriginalRetainedEndIso S
  let U := unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) false
  have h₀ : (isPushout_skeletonAttachment X (n + 1)).isoPushout.hom
      (characteristicDiskToSkeleton (n + 1) i q) = selectedDisks f g ⟨i, q⟩ := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom
        (isPushout_skeletonAttachment X (n + 1)).inr_isoPushout_hom ⟨i, q⟩
  have h₁ : e.inv (retainedDisks f g c ⟨i, q⟩) =
      diskEndDisks (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S))
        false ⟨i, q⟩ := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualOriginalRetainedEnd_square S).inr_isoPushout_inv ⟨i, q⟩
  change U (e.inv (attachmentInclude f g c
    ((isPushout_skeletonAttachment X (n + 1)).isoPushout.hom
      (characteristicDiskToSkeleton (n + 1) i q)))) = _
  calc
    _ = U (e.inv (attachmentInclude f g c (selectedDisks f g ⟨i, q⟩))) :=
      congrArg (fun z : selectedAttachment f g => U (e.inv (attachmentInclude f g c z))) h₀
    _ = U (e.inv (retainedDisks f g c ⟨i, q⟩)) :=
      congrArg (fun z : retainedAttachment f g c => U (e.inv z))
        (attachmentInclude_disk f g c ⟨i, q⟩)
    _ = U (diskEndDisks (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false ⟨i, q⟩) :=
      congrArg U h₁
    _ = originalCylinderMap (n + 1) (smallSuccessorBoundary S) i (q, 0) :=
      unitDiskEndInclude_disk (n + 1) (smallSuccessorBoundary S) false i q

private theorem actualOriginalSuccessorCollapse_retraction {n : ℕ} (S : Stage X n)
    (x : skeletonTop X ((n + 1) + 1)) :
    (actualOriginalSuccessorCollapse S).retract
      ((actualOriginalSuccessorCollapse S).include x) = x :=
  finiteCollapse_retraction (actualOriginalSuccessorCollapse S) x

private theorem actualOriginalSuccessorCollapse_fixed {n : ℕ} (S : Stage X n)
    (t : unitInterval) (x : skeletonTop X ((n + 1) + 1)) :
    (actualOriginalSuccessorCollapse S).deformation
      (t, (actualOriginalSuccessorCollapse S).include x) =
        (actualOriginalSuccessorCollapse S).include x :=
  (actualOriginalSuccessorCollapse S).deformation.eq_fst t (Set.mem_range_self x)

end ActualCommonSuccessorConstruction

end

/- Same-module actual polyhedral-end instantiation.
The intermediate stage retracts to the constructed small cylinder family.
The reduced disk attachment is identified with its ACTUAL ordinary cone
pushout using the original disk/copied-cone homeomorphisms. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47
open StationaryAttachmentRetractionConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualSubdivisions {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) : ℕ :=
  (cellApproximation S j).subdivisions

private def actualNextPolyhedron {n : ℕ} (S : Stage X n) :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Cone.associatedFamily
    (cellPolyhedron S) S.polyhedron (cellMap S)

private theorem actualSmallInclusionPoint {V : Type*}
    {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) (x : P.Realization) :
    ((MappingCylinder.inclusionMorphism h).realization x).point = x.point := by
  change ((MappingCylinder.inclusionMorphism h).realizationMap x).point = x.point
  rw [Morphism.realizationMap_point]
  exact Realization.map_vertexCoordinates x

private def actualCopiedRelabel {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    CopiedSphere S j ≃ₜ
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization :=
  MappingCylinder.relabelHomeomorph (barycentricSubdivision (cellPolyhedron S j))
    Function.Embedding.inl

private theorem actualDomainsToCylinder_copied {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) (x : CopiedSphere S j) :
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
      (cellPolyhedron S) S.polyhedron (cellMap S) ⟨j, actualCopiedRelabel S j x⟩ =
        smallFamilyCopied S j x := by
  rw [PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder_apply]
  apply Realization.ext
  rw [PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion_point]
  have hrel : (actualCopiedRelabel S j x).point =
      x.point.map (Function.Embedding.inl : Face (cellPolyhedron S j) ↪
        Face (cellPolyhedron S j) ⊕ S.vertices) := by
    simpa only [actualCopiedRelabel, ← Homeomorph.coe_toEquiv,
      MappingCylinder.relabelHomeomorph, Equiv.coe_ofBijective,
      Equiv.ofBijective_apply] using!
      MappingCylinder.relabelMorphism_point (barycentricSubdivision (cellPolyhedron S j))
        (Function.Embedding.inl : Face (cellPolyhedron S j) ↪
          Face (cellPolyhedron S j) ⊕ S.vertices) x
  calc
    _ = (actualCopiedRelabel S j x).point.map
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (cellPolyhedron S) j) :=
      congrArg (fun z : Convexity.StdSimplex ℝ (Face (cellPolyhedron S j) ⊕ S.vertices) =>
        z.map (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (cellPolyhedron S) j))
        (actualSmallInclusionPoint (small_domain_le (cellMap S j))
          (actualCopiedRelabel S j x))
    _ = (x.point.map (Function.Embedding.inl : Face (cellPolyhedron S j) ↪
        Face (cellPolyhedron S j) ⊕ S.vertices)).map
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (cellPolyhedron S) j) :=
      congrArg (fun z : Convexity.StdSimplex ℝ (Face (cellPolyhedron S j) ⊕ S.vertices) =>
        z.map (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (cellPolyhedron S) j)) hrel
    _ = (smallFamilyCopied S j x).point :=
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.copiedInclusion_point
        (cellPolyhedron S) S.polyhedron (cellMap S) j x).symm

private theorem actualCopiedSphereComparison {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    originalSphereToCopiedDomain (W := S.vertices) (n + 1) (actualSubdivisions S j) s =
      actualCopiedRelabel S j ((copiedSphereComparison S j).symm s) := rfl

private def actualSphereFamilyComparison {n : ℕ} (S : Stage X n) :
    EndpointSphereFamily (J := CellIndex (X := X) n) (n + 1) ≃ₜ
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum (cellPolyhedron S) S.vertices :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph fun j =>
    originalSphereToCopiedDomain (W := S.vertices) (n + 1) (actualSubdivisions S j)

private def actualPolyhedralSphereMap {n : ℕ} (S : Stage X n) :
    TopCat.of (EndpointSphereFamily (J := CellIndex (X := X) n) (n + 1)) ⟶
      TopCat.of (smallFamilyComplex S).Realization :=
  TopCat.ofHom (actualSphereFamilyComparison S :
    C(EndpointSphereFamily (J := CellIndex (X := X) n) (n + 1),
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum (cellPolyhedron S) S.vertices)) ≫
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
      (cellPolyhedron S) S.polyhedron (cellMap S)

private theorem actualPolyhedralBoundary_factor {n : ℕ} (S : Stage X n) :
    TopCat.ofHom (endpointBoundary (n + 1)
      (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true) =
        actualPolyhedralSphereMap S ≫ (actualIntermediateFamilyCollapse S).include := by
  apply TopCat.ext
  rintro ⟨j, s⟩
  change endpointBoundary (n + 1)
      (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true ⟨j, s⟩ =
    smallIntermediateFamily S
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
        (cellPolyhedron S) S.polyhedron (cellMap S)
          (actualSphereFamilyComparison S ⟨j, s⟩))
  have hSigma : actualSphereFamilyComparison S ⟨j, s⟩ =
      (⟨j, originalSphereToCopiedDomain (W := S.vertices)
        (n + 1) (actualSubdivisions S j) s⟩ :
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
          (cellPolyhedron S) S.vertices) := by
    dsimp only [actualSphereFamilyComparison]
    exact PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply
      (fun k => originalSphereToCopiedDomain (W := S.vertices)
        (n + 1) (actualSubdivisions S k)) j s
  rw [hSigma, normalizedEndpointBoundary_value]
  change smallSuccessorBoundary S ⟨j, (s, 1)⟩ = _
  rw [smallSuccessorBoundary_one, actualCopiedSphereComparison,
    actualDomainsToCylinder_copied]

private def actualOrdinaryConeHomeomorph {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n) :
    TopCat.cone (TopCat.of
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization) ≃ₜ
      (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)).Realization := by
  letI := cellFiniteFaces S j
  letI := MappingCylinder.finiteFaces_domainComplex (cellPolyhedron S j) S.vertices
  exact MappingCylinder.ordinaryConeHomeomorph
    (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)

private def actualConeDiskComparison {n : ℕ} (S : Stage X n) (j : CellIndex (X := X) n) :
    TopCat.cone (TopCat.of
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization) ≃ₜ
        (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst :=
  (actualOrdinaryConeHomeomorph S j).trans
    (originalDiskToCopiedConeComplex (W := S.vertices)
      (n + 1) (actualSubdivisions S j)).symm

private theorem actualConeDiskComparison_value {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (q : TopCat.cone (TopCat.of
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization)) :
    actualConeDiskComparison S j q =
      actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) j q := rfl

private def actualConeFamilyComparison {n : ℕ} (S : Stage X n) :
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum (cellPolyhedron S) S.vertices ≃ₜ
      EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1) :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph (actualConeDiskComparison S)

private theorem actualReducedPolyhedralEnd_square {n : ℕ} (S : Stage X n) :
    IsPushout (actualPolyhedralSphereMap S)
      (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S))
      (TopCat.ofHom ((actualConeFamilyComparison S).symm :
        C(EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1),
          PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum (cellPolyhedron S) S.vertices)) ≫
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)) := by
  let es : TopCat.of (EndpointSphereFamily (J := CellIndex (X := X) n) (n + 1)) ≅
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum (cellPolyhedron S) S.vertices :=
    TopCat.isoOfHomeo (actualSphereFamilyComparison S)
  let ed : TopCat.of (EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1)) ≅
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum (cellPolyhedron S) S.vertices :=
    TopCat.isoOfHomeo ((actualConeFamilyComparison S).symm)
  refine (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.ordinaryConeFamily_isPushout
    (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)).of_iso'
      es (Iso.refl _) ed (Iso.refl _) ?_ ?_ ?_ ?_
  · apply TopCat.ext
    intro x
    rfl
  · apply TopCat.ext
    rintro ⟨j, s⟩
    change PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCones
        (cellPolyhedron S) (actualSphereFamilyComparison S ⟨j, s⟩) =
      (actualConeFamilyComparison S).symm
        ⟨j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).map s⟩
    let x : (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization :=
      originalSphereToCopiedDomain (W := S.vertices) (n + 1) (actualSubdivisions S j) s
    have hSigma : actualSphereFamilyComparison S ⟨j, s⟩ =
        (⟨j, x⟩ :
          PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
            (cellPolyhedron S) S.vertices) := by
      dsimp only [actualSphereFamilyComparison]
      exact PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply
        (fun k => originalSphereToCopiedDomain (W := S.vertices)
          (n + 1) (actualSubdivisions S k)) j s
    rw [hSigma,
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCones_apply]
    apply (actualConeFamilyComparison S).injective
    let q : TopCat.cone (TopCat.of
        (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization) :=
      TopCat.coneBase (TopCat.of
        (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization) x
    have hbase : actualConeDiskComparison S j q =
        (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).map s := by
      refine (actualConeDiskComparison_value S j q).trans ?_
      simpa only [Homeomorph.symm_apply_apply] using!
        actualConeToTopDisk_base (W := S.vertices) (n + 1) (actualSubdivisions S) j
          (originalSphereToCopiedDomain (W := S.vertices)
            (n + 1) (actualSubdivisions S j) s)
    have hleft : actualConeFamilyComparison S
        (⟨j, q⟩ : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
          (cellPolyhedron S) S.vertices) =
        (⟨j, actualConeDiskComparison S j q⟩ :
          EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1)) := by
      simpa only [actualConeFamilyComparison] using!
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply
          (actualConeDiskComparison S) j q
    calc
      _ = (⟨j, actualConeDiskComparison S j q⟩ :
          EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1)) := hleft
      _ = (⟨j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).map s⟩ :
          EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1)) :=
        congrArg (fun z : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst =>
          (⟨j, z⟩ : EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1))) hbase
      _ = actualConeFamilyComparison S
          ((actualConeFamilyComparison S).symm
            ⟨j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).map s⟩) :=
        ((actualConeFamilyComparison S).apply_symm_apply
          ⟨j, (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).map s⟩).symm
  · apply TopCat.ext
    intro x
    rfl
  · apply TopCat.ext
    intro x
    rfl

private theorem actualPolyhedralRetainedEnd_square {n : ℕ} (S : Stage X n) :
    IsPushout (actualPolyhedralSphereMap S ≫ (actualIntermediateFamilyCollapse S).include)
      (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
      (diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true)
      (diskEndDisks (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true) := by
  rw [← actualPolyhedralBoundary_factor S]
  exact IsPushout.of_hasPushout _ _

private def actualPolyhedralRetainedEndIso {n : ℕ} (S : Stage X n) :
    unitDiskEndSpace (n + 1) (smallSuccessorBoundary S) true ≅
      retainedAttachment (actualPolyhedralSphereMap S)
        (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
        (actualIntermediateFamilyCollapse S).include :=
  (actualPolyhedralRetainedEnd_square S).isoPushout

private def actualPolyhedralLiftedCollapse {n : ℕ} (S : Stage X n) :=
  liftedAttachingCollapse (actualPolyhedralSphereMap S)
    (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
    (actualIntermediateFamilyCollapse S).include
    (actualIntermediateFamilyCollapse S).retract
    (actualIntermediateFamilyCollapse S).retraction
    (actualIntermediateFamilyCollapse S).deformation

private def actualPolyhedralSuccessorCollapse {n : ℕ} (S : Stage X n) :
    FiniteCollapse (actualSuccessorSpace S) (TopCat.of (actualNextPolyhedron S).Realization) :=
  composeFiniteCollapses
    (elementaryTubeCollapse (n + 1) (smallSuccessorBoundary S) true)
    (composeFiniteCollapses (finiteCollapseOfIso (actualPolyhedralRetainedEndIso S))
      (composeFiniteCollapses (actualPolyhedralLiftedCollapse S)
        (finiteCollapseOfIso (actualReducedPolyhedralEnd_square S).isoPushout.symm)))

private theorem actualPolyhedralSuccessorCollapse_cylinder {n : ℕ} (S : Stage X n)
    (b : (smallFamilyComplex S).Realization) :
    (actualPolyhedralSuccessorCollapse S).include
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) b) =
      oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (smallIntermediateFamily S b) := by
  let f := actualPolyhedralSphereMap S
  let g := TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1))
  let c := (actualIntermediateFamilyCollapse S).include
  let e := actualPolyhedralRetainedEndIso S
  let U := unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) true
  have h₀ : (actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) b) = selectedOld f g b := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualReducedPolyhedralEnd_square S).inl_isoPushout_hom b
  have h₁ : e.inv (retainedOld f g c (c b)) =
      diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S))
        true (c b) := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualPolyhedralRetainedEnd_square S).inl_isoPushout_inv (c b)
  have hc : c b = smallIntermediateFamily S b := rfl
  change U (e.inv (attachmentInclude f g c
    ((actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) b)))) = _
  calc
    _ = U (e.inv (attachmentInclude f g c (selectedOld f g b))) :=
      congrArg (fun z : selectedAttachment f g => U (e.inv (attachmentInclude f g c z))) h₀
    _ = U (e.inv (retainedOld f g c (c b))) :=
      congrArg (fun z : retainedAttachment f g c => U (e.inv z)) (attachmentInclude_old f g c b)
    _ = U (diskEndOld (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true (c b)) :=
      congrArg U h₁
    _ = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (c b) :=
      unitDiskEndInclude_old (n + 1) (smallSuccessorBoundary S) true (c b)
    _ = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) (smallIntermediateFamily S b) :=
      congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) hc

/-- Every point of each actual ordinary cone is retained, including its base
and apex; its disk coordinate is the actual original copied-cone comparison. -/
private theorem actualPolyhedralSuccessorCollapse_cone {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (q : TopCat.cone (TopCat.of
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization)) :
    (actualPolyhedralSuccessorCollapse S).include
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) ⟨j, q⟩) =
      originalCylinderMap (n + 1) (smallSuccessorBoundary S) j
        (actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) j q, 1) := by
  let f := actualPolyhedralSphereMap S
  let g := TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1))
  let c := (actualIntermediateFamilyCollapse S).include
  let e := actualPolyhedralRetainedEndIso S
  let U := unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) true
  let p : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
      (cellPolyhedron S) S.vertices := ⟨j, q⟩
  let y : EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1) :=
    actualConeFamilyComparison S p
  have hraw : (actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
          ((actualConeFamilyComparison S).symm y)) = selectedDisks f g y := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualReducedPolyhedralEnd_square S).inr_isoPushout_hom y
  have hcancel : (actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
          ((actualConeFamilyComparison S).symm y)) =
      (actualReducedPolyhedralEnd_square S).isoPushout.hom
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) p) :=
    congrArg (fun z : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
        (cellPolyhedron S) S.vertices =>
      (actualReducedPolyhedralEnd_square S).isoPushout.hom
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) z))
      ((actualConeFamilyComparison S).symm_apply_apply p)
  have h₀ : (actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) p) =
      selectedDisks f g y := hcancel.symm.trans hraw
  have h₁ : e.inv (retainedDisks f g c y) =
      diskEndDisks (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S))
        true y := by
    simpa only [ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualPolyhedralRetainedEnd_square S).inr_isoPushout_inv y
  have hy : y = (⟨j, actualConeDiskComparison S j q⟩ :
      EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1)) := by
    simpa only [y, p, actualConeFamilyComparison] using!
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply
        (actualConeDiskComparison S) j q
  change U (e.inv (attachmentInclude f g c
    ((actualReducedPolyhedralEnd_square S).isoPushout.hom
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) p)))) = _
  calc
    _ = U (e.inv (attachmentInclude f g c (selectedDisks f g y))) :=
      congrArg (fun z : selectedAttachment f g => U (e.inv (attachmentInclude f g c z))) h₀
    _ = U (e.inv (retainedDisks f g c y)) :=
      congrArg (fun z : retainedAttachment f g c => U (e.inv z)) (attachmentInclude_disk f g c y)
    _ = U (diskEndDisks (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true y) :=
      congrArg U h₁
    _ = U (diskEndDisks (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true
          ⟨j, actualConeDiskComparison S j q⟩) :=
      congrArg (fun z : EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1) =>
        U (diskEndDisks (n + 1)
          (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true z)) hy
    _ = originalCylinderMap (n + 1) (smallSuccessorBoundary S) j
        (actualConeDiskComparison S j q, 1) :=
      unitDiskEndInclude_disk (n + 1) (smallSuccessorBoundary S) true j
        (actualConeDiskComparison S j q)
    _ = originalCylinderMap (n + 1) (smallSuccessorBoundary S) j
        (actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) j q, 1) :=
      congrArg (fun z : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst =>
        originalCylinderMap (n + 1) (smallSuccessorBoundary S) j (z, 1))
        (actualConeDiskComparison_value S j q)

private theorem actualPolyhedralSuccessorCollapse_retraction {n : ℕ} (S : Stage X n)
    (p : (actualNextPolyhedron S).Realization) :
    (actualPolyhedralSuccessorCollapse S).retract
      ((actualPolyhedralSuccessorCollapse S).include p) = p :=
  finiteCollapse_retraction (actualPolyhedralSuccessorCollapse S) p

/-- Every point of an actual closed finite face of the copied cone complex
has the original top-disk coordinate. No vertex-only reduction is used. -/
private theorem actualPolyhedralSuccessorCollapse_top_face {n : ℕ} (S : Stage X n)
    (j : CellIndex (X := X) n)
    (s : Face (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)))
    (q : Convexity.StdSimplex ℝ s.val) :
    (actualPolyhedralSuccessorCollapse S).include
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
        ⟨j, (actualOrdinaryConeHomeomorph S j).symm
          (Realization.faceMap (MappingCylinder.coneComplex
            (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)) s q)⟩) =
      originalCylinderMap (n + 1) (smallSuccessorBoundary S) j
        ((originalDiskToCopiedConeComplex (W := S.vertices)
            (n + 1) (actualSubdivisions S j)).symm
          (Realization.faceMap (MappingCylinder.coneComplex
            (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)) s q), 1) := by
  rw [actualPolyhedralSuccessorCollapse_cone]
  change originalCylinderMap (n + 1) (smallSuccessorBoundary S) j
      ((originalDiskToCopiedConeComplex (W := S.vertices)
          (n + 1) (actualSubdivisions S j)).symm
        ((actualOrdinaryConeHomeomorph S j)
          ((actualOrdinaryConeHomeomorph S j).symm
            (Realization.faceMap (MappingCylinder.coneComplex
              (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices)) s q))), 1) = _
  rw [Homeomorph.apply_symm_apply]

private theorem actualPolyhedralSuccessorCollapse_fixed {n : ℕ} (S : Stage X n)
    (t : unitInterval) (p : (actualNextPolyhedron S).Realization) :
    (actualPolyhedralSuccessorCollapse S).deformation
        (t, (actualPolyhedralSuccessorCollapse S).include p) =
      (actualPolyhedralSuccessorCollapse S).include p :=
  (actualPolyhedralSuccessorCollapse S).deformation.eq_fst t (Set.mem_range_self p)

end ActualCommonSuccessorConstruction

end

/- Same-module complete agreement with the actual route32 forward maps.
The finite collapse construction uses exactly the original successor and
associated-family inclusions: equality follows on both actual pushout legs. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualOriginalForwardMap_agreement {n : ℕ} (S : Stage X n) :
    (actualOriginalSuccessorCollapse S).include.hom =
      originalSuccessorEndMap (n + 1) (smallSuccessorBoundary S)
        (smallIntermediateOriginal S) (smallSuccessorBoundary_zero S) := by
  apply ContinuousMap.ext
  intro x
  let hs := isPushout_skeletonAttachment X (n + 1)
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨y, rfl⟩
    exact (actualOriginalSuccessorCollapse_old S y).trans
      (originalSuccessorEndMap_old (n + 1) (smallSuccessorBoundary S)
        (smallIntermediateOriginal S) (smallSuccessorBoundary_zero S) y).symm
  · rcases hx with ⟨⟨i, q⟩, rfl⟩
    exact (actualOriginalSuccessorCollapse_disk S i q).trans
      (originalSuccessorEndMap_disk (n + 1) (smallSuccessorBoundary S)
        (smallIntermediateOriginal S) (smallSuccessorBoundary_zero S) i q).symm

private theorem actualTopBoundary_formula {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    smallSuccessorBoundary S ⟨i, (s, 1)⟩ =
      smallIntermediateFamily S
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (cellPolyhedron S) S.polyhedron (cellMap S)
          ⟨i, originalSphereToCopiedDomain (W := S.vertices)
            (n + 1) (actualSubdivisions S i) s⟩) := by
  rw [smallSuccessorBoundary_one, actualCopiedSphereComparison,
    actualDomainsToCylinder_copied]

private theorem actualPolyhedralForwardMap_agreement {n : ℕ} (S : Stage X n) :
    (actualPolyhedralSuccessorCollapse S).include.hom =
      polyhedralSuccessorEndMap (W := S.vertices) (n + 1) (actualSubdivisions S)
        S.polyhedron (cellMap S) (smallSuccessorBoundary S)
        (smallIntermediateFamily S) (actualTopBoundary_formula S) := by
  apply ContinuousMap.ext
  intro x
  let hs := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.ordinaryConeFamily_isPushout
    (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨b, rfl⟩
    exact (actualPolyhedralSuccessorCollapse_cylinder S b).trans
      (polyhedralSuccessorEndMap_cylinder (W := S.vertices)
        (n + 1) (actualSubdivisions S) S.polyhedron (cellMap S)
        (smallSuccessorBoundary S) (smallIntermediateFamily S)
        (actualTopBoundary_formula S) b).symm
  · rcases hx with ⟨⟨i, q⟩, rfl⟩
    exact (actualPolyhedralSuccessorCollapse_cone S i q).trans
      (polyhedralSuccessorEndMap_cone (W := S.vertices)
        (n + 1) (actualSubdivisions S) S.polyhedron (cellMap S)
        (smallSuccessorBoundary S) (smallIntermediateFamily S)
        (actualTopBoundary_formula S) i q).symm

end ActualCommonSuccessorConstruction

end

/- Same-module X-only recursion for the FINITE TOPOLOGICAL end data.
The initial state and each successor's approximation, small family, tube,
both actual end retractions and homotopies are constructed from X.

The following sections equip these same spaces with compatible Hausdorff
classical CW structures, end labels, subcomplexes and dimension bounds. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualTopologicalSuccessor {n : ℕ} (S : Stage X n) : Stage X (n + 1) where
  vertices := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Cone.ConeLabels
    (W := S.vertices) (cellPolyhedron S)
  polyhedron := actualNextPolyhedron S
  space := actualSuccessorSpace S
  original := (actualOriginalSuccessorCollapse S).include.hom
  polyhedral := (actualPolyhedralSuccessorCollapse S).include.hom
  retractOriginal := (actualOriginalSuccessorCollapse S).retract.hom
  retractPolyhedral := (actualPolyhedralSuccessorCollapse S).retract.hom
  original_retraction := actualOriginalSuccessorCollapse_retraction S
  polyhedral_retraction := actualPolyhedralSuccessorCollapse_retraction S
  originalDeformation := (actualOriginalSuccessorCollapse S).deformation
  polyhedralDeformation := (actualPolyhedralSuccessorCollapse S).deformation

private def actualFiniteStages : ∀ n : ℕ, Stage X n :=
  Nat.rec (initialStage X) (fun _ S => actualTopologicalSuccessor X S)

private def actualCommonStageTransition {n : ℕ} (S : Stage X n) :
    C(S.space, (actualTopologicalSuccessor X S).space) :=
  (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)).comp (smallIntermediateOld S)

private def actualPolyhedralStageTransition {n : ℕ} (S : Stage X n) :
    C(S.polyhedron.Realization, (actualTopologicalSuccessor X S).polyhedron.Realization) :=
  (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
    (cellPolyhedron S) S.polyhedron (cellMap S)).hom.comp (smallFamilyOld S)

private theorem actualCommonStageTransition_original {n : ℕ} (S : Stage X n)
    (x : Topology.CWComplex.skeletonTop X (n + 1)) :
    (actualTopologicalSuccessor X S).original (Topology.CWComplex.skeletonTransition X (n + 1) x) =
      actualCommonStageTransition X S (S.original x) :=
  actualOriginalSuccessorCollapse_old S x

private theorem actualCommonStageTransition_polyhedral {n : ℕ} (S : Stage X n)
    (y : S.polyhedron.Realization) :
    (actualTopologicalSuccessor X S).polyhedral (actualPolyhedralStageTransition X S y) =
      actualCommonStageTransition X S (S.polyhedral y) := by
  change (actualPolyhedralSuccessorCollapse S).include
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (smallFamilyOld S y)) =
    oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)
      (smallIntermediateOld S (S.polyhedral y))
  rw [actualPolyhedralSuccessorCollapse_cylinder]
  exact congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S))
    (smallIntermediate_identification S y).symm

private structure SharedEndPoint {n : ℕ} (S : Stage X n) where
  original : Topology.CWComplex.skeletonTop X (n + 1)
  polyhedral : S.polyhedron.Realization
  same : S.original original = S.polyhedral polyhedral

private def successorSharedEndPoint {n : ℕ} (S : Stage X n) (p : SharedEndPoint X S) :
    SharedEndPoint X (actualTopologicalSuccessor X S) where
  original := Topology.CWComplex.skeletonTransition X (n + 1) p.original
  polyhedral := actualPolyhedralStageTransition X S p.polyhedral
  same := by
    rw [actualCommonStageTransition_original, actualCommonStageTransition_polyhedral]
    exact congrArg (actualCommonStageTransition X S) p.same

private def initialSharedZeroPoint (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    SharedEndPoint X (initialStage X) where
  original := (Topology.CWComplex.commonZeroSkeleton X).homeomorph
    (Realization.vertex
      ((⊥ : AbstractSimplicialComplex
        (Topology.CWComplex.cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex)
      j ((⊥ : AbstractSimplicialComplex
        (Topology.CWComplex.cell (Set.univ : Set X) 0)).singleton_mem j))
  polyhedral := Realization.vertex
    ((⊥ : AbstractSimplicialComplex
      (Topology.CWComplex.cell (Set.univ : Set X) 0)).toPreAbstractSimplicialComplex)
    j ((⊥ : AbstractSimplicialComplex
      (Topology.CWComplex.cell (Set.univ : Set X) 0)).singleton_mem j)
  same := rfl

private def actualSharedZeroPoint (j : Topology.CWComplex.cell (Set.univ : Set X) 0) :
    ∀ n : ℕ, SharedEndPoint X (actualFiniteStages X n) :=
  Nat.rec (initialSharedZeroPoint X j)
    (fun n p => successorSharedEndPoint X (actualFiniteStages X n) p)

private theorem actualSharedZeroPoint_original_value
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) (n : ℕ) :
    (actualSharedZeroPoint X j n).original.val =
      Topology.CWComplex.map (C := (Set.univ : Set X)) 0 j (0 : Fin 0 → ℝ) := by
  induction n with
  | zero =>
    exact (Topology.CWComplex.commonZeroSkeleton X).homeomorph_vertex j
  | succ n ih =>
    exact ih

private theorem actualFiniteOriginalEnd_stationary (n : ℕ) (t : unitInterval)
    (x : Topology.CWComplex.skeletonTop X (n + 1)) :
    (actualFiniteStages X n).originalDeformation
      (t, (actualFiniteStages X n).original x) = (actualFiniteStages X n).original x :=
  (actualFiniteStages X n).originalDeformation.eq_fst t (Set.mem_range_self x)

private theorem actualFinitePolyhedralEnd_stationary (n : ℕ) (t : unitInterval)
    (p : (actualFiniteStages X n).polyhedron.Realization) :
    (actualFiniteStages X n).polyhedralDeformation
      (t, (actualFiniteStages X n).polyhedral p) = (actualFiniteStages X n).polyhedral p :=
  (actualFiniteStages X n).polyhedralDeformation.eq_fst t (Set.mem_range_self p)

private theorem actualSharedZeroPoint_original_fixed
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) (n : ℕ) (t : unitInterval) :
    (actualFiniteStages X n).originalDeformation
      (t, (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original) =
        (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original :=
  actualFiniteOriginalEnd_stationary X n t (actualSharedZeroPoint X j n).original

private theorem actualSharedZeroPoint_polyhedral_fixed
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) (n : ℕ) (t : unitInterval) :
    (actualFiniteStages X n).polyhedralDeformation
      (t, (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original) =
        (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original := by
  rw [(actualSharedZeroPoint X j n).same]
  exact actualFinitePolyhedralEnd_stationary X n t (actualSharedZeroPoint X j n).polyhedral

end ActualCommonSuccessorConstruction

end

/- Same-module actual intermediate separation field.
The two retractions are the constructed36 maps, not new premises.
They give an injective continuous map to previous Z × actual small B.
This is the inductive intermediate T2 field; tube T2 still must be derived. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualIntermediateJointRetraction {n : ℕ} (S : Stage X n) :
    C(smallIntermediate S, S.space × (smallFamilyComplex S).Realization) :=
  (intermediateToOld S).hom.prodMk (intermediateToFamily S).hom

private theorem actualIntermediateJointRetraction_cross {n : ℕ} (S : Stage X n)
    (z : S.space) (b : (smallFamilyComplex S).Realization)
    (h : actualIntermediateJointRetraction S (smallIntermediateOld S z) =
      actualIntermediateJointRetraction S (smallIntermediateFamily S b)) :
    smallIntermediateOld S z = smallIntermediateFamily S b := by
  have hz := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change intermediateToOld S (smallIntermediateOld S z) =
    intermediateToOld S (smallIntermediateFamily S b) at hz
  rw [intermediateToOld_old, intermediateToOld_family] at hz
  change intermediateToFamily S (smallIntermediateOld S z) =
    intermediateToFamily S (smallIntermediateFamily S b) at hb
  rw [intermediateToFamily_old, intermediateToFamily_family] at hb
  have hp : S.retractPolyhedral z = smallFamilyRetraction S b :=
    (congrArg S.retractPolyhedral hz).trans
      (S.polyhedral_retraction (smallFamilyRetraction S b))
  calc
    smallIntermediateOld S z =
        smallIntermediateOld S (S.polyhedral (smallFamilyRetraction S b)) :=
      congrArg (smallIntermediateOld S) hz
    _ = smallIntermediateFamily S (smallFamilyOld S (smallFamilyRetraction S b)) :=
      smallIntermediate_identification S (smallFamilyRetraction S b)
    _ = smallIntermediateFamily S (smallFamilyOld S (S.retractPolyhedral z)) :=
      congrArg (fun y => smallIntermediateFamily S (smallFamilyOld S y)) hp.symm
    _ = smallIntermediateFamily S b :=
      congrArg (smallIntermediateFamily S) hb

private theorem actualIntermediateJointRetraction_injective {n : ℕ} (S : Stage X n) :
    Function.Injective (actualIntermediateJointRetraction S) := by
  intro a b hab
  let hs := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
    (TopCat.ofHom (smallFamilyOld S))
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) a with ha | ha
  · rcases ha with ⟨z, rfl⟩
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) b with hb | hb
    · rcases hb with ⟨w, rfl⟩
      have h := congrArg Prod.fst hab
      change intermediateToOld S (smallIntermediateOld S z) =
        intermediateToOld S (smallIntermediateOld S w) at h
      rw [intermediateToOld_old, intermediateToOld_old] at h
      exact congrArg (smallIntermediateOld S) h
    · rcases hb with ⟨w, rfl⟩
      exact actualIntermediateJointRetraction_cross S z w hab
  · rcases ha with ⟨z, rfl⟩
    rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) b with hb | hb
    · rcases hb with ⟨w, rfl⟩
      exact (actualIntermediateJointRetraction_cross S w z hab.symm).symm
    · rcases hb with ⟨w, rfl⟩
      have h := congrArg Prod.snd hab
      change intermediateToFamily S (smallIntermediateFamily S z) =
        intermediateToFamily S (smallIntermediateFamily S w) at h
      rw [intermediateToFamily_family, intermediateToFamily_family] at h
      exact congrArg (smallIntermediateFamily S) h

private def actualIntermediateT2Space {n : ℕ} (S : Stage X n)
    [T2Space S.space] : T2Space (smallIntermediate S) :=
  T2Space.of_injective_continuous
    (f := actualIntermediateJointRetraction S)
    (actualIntermediateJointRetraction_injective S)
    (actualIntermediateJointRetraction S).continuous

end ActualCommonSuccessorConstruction

end

/- Closedness of the constructed stage inclusions.
The induction starts with the zero homeomorphism. Each successor uses
the derived closed maps and endpoint presentation isomorphisms. Neither
new-stage T2 nor a supplied CW/subcomplex witness is assumed for closedness. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open ActualRefinedTubeCharacteristicConstruction47
open StationaryAttachmentRetractionConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualOriginalSuccessor_include_closed {n : ℕ} (S : Stage X n)
    (hOriginal : IsClosedEmbedding S.original) :
    IsClosedEmbedding (actualOriginalSuccessorCollapse S).include := by
  have hbase : IsClosedEmbedding (actualIntermediateOriginalCollapse S).include := by
    rw [actualIntermediateOriginalCollapse_include]
    exact (smallIntermediateOld_closed S).comp hOriginal
  have hlift := attachmentInclude_closed
    (sphereSumToSkeleton X (n + 1)) (sphereSumToDiskSum X (n + 1))
    (actualIntermediateOriginalCollapse S).include hbase
  change IsClosedEmbedding
    (unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) false ∘
      ((actualOriginalRetainedEndIso S).inv ∘
        (attachmentInclude (sphereSumToSkeleton X (n + 1))
          (sphereSumToDiskSum X (n + 1))
          (actualIntermediateOriginalCollapse S).include ∘
            (isPushout_skeletonAttachment X (n + 1)).isoPushout.hom)))
  exact (unitDiskEndInclude_closed (n + 1) (smallSuccessorBoundary S) false).comp
    ((TopCat.homeoOfIso (actualOriginalRetainedEndIso S)).symm.isClosedEmbedding.comp
      (hlift.comp
        (TopCat.homeoOfIso (isPushout_skeletonAttachment X (n + 1)).isoPushout).isClosedEmbedding))

private theorem actualIntermediateFamily_include_closed {n : ℕ} (S : Stage X n)
    (hPolyhedral : IsClosedEmbedding S.polyhedral) :
    IsClosedEmbedding (actualIntermediateFamilyCollapse S).include :=
  TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral)
      (TopCat.ofHom (smallFamilyOld S))) hPolyhedral

private theorem actualPolyhedralSuccessor_include_closed {n : ℕ} (S : Stage X n)
    (hPolyhedral : IsClosedEmbedding S.polyhedral) :
    IsClosedEmbedding (actualPolyhedralSuccessorCollapse S).include := by
  have hbase := actualIntermediateFamily_include_closed S hPolyhedral
  have hlift := attachmentInclude_closed (actualPolyhedralSphereMap S)
    (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
    (actualIntermediateFamilyCollapse S).include hbase
  change IsClosedEmbedding
    (unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) true ∘
      ((actualPolyhedralRetainedEndIso S).inv ∘
        (attachmentInclude (actualPolyhedralSphereMap S)
          (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
          (actualIntermediateFamilyCollapse S).include ∘
            (actualReducedPolyhedralEnd_square S).isoPushout.hom)))
  exact (unitDiskEndInclude_closed (n + 1) (smallSuccessorBoundary S) true).comp
    ((TopCat.homeoOfIso (actualPolyhedralRetainedEndIso S)).symm.isClosedEmbedding.comp
      (hlift.comp
        (TopCat.homeoOfIso (actualReducedPolyhedralEnd_square S).isoPushout).isClosedEmbedding))

private theorem actualFiniteStages_end_closed
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] :
    ∀ n : ℕ, IsClosedEmbedding (actualFiniteStages X n).original ∧
      IsClosedEmbedding (actualFiniteStages X n).polyhedral := by
  intro n
  induction n with
  | zero =>
    constructor
    · change IsClosedEmbedding (ContinuousMap.id (skeletonTop X 1))
      exact IsClosedEmbedding.id
    · change IsClosedEmbedding (Topology.CWComplex.commonZeroSkeleton X).homeomorph
      exact (Topology.CWComplex.commonZeroSkeleton X).homeomorph.isClosedEmbedding
  | succ n ih =>
    constructor
    · exact actualOriginalSuccessor_include_closed (actualFiniteStages X n) ih.1
    · exact actualPolyhedralSuccessor_include_closed (actualFiniteStages X n) ih.2

private theorem actualCommonStageTransition_closed {n : ℕ} (S : Stage X n) :
    IsClosedEmbedding (actualCommonStageTransition X S) :=
  (oldIntoTubeSpace_closed (n + 1) (smallSuccessorBoundary S)).comp
    (smallIntermediateOld_closed S)

end ActualCommonSuccessorConstruction

end

/- Same-module actual open-set descent for the tube pushout.
Continuous classifiers into lifted Sierpinski Prop descend by the ACTUAL
pushout universal property. No quotient topology or open-set extension
witness for the final tube is supplied. Collar lifts instantiate these sets.

The existing ClosedEmbedding provider imports Mathlib.Topology.Maps.Basic,
which publicly imports Mathlib.Topology.Order and continuous_Prop. No new
Sierpinski import or generic open-set wrapper is required. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private def oldOpenClassifier (U : Set A) (hU : IsOpen U) :
    A ⟶ TopCat.of (ULift.{u} Prop) :=
  TopCat.ofHom
    ⟨fun a => ULift.up (a ∈ U), continuous_uliftUp.comp (continuous_Prop.mpr hU)⟩

private def cylinderOpenClassifier (d : ℕ)
    (U : Set (cylinderSum (I := I) d)) (hU : IsOpen U) :
    cylinderSum (I := I) d ⟶ TopCat.of (ULift.{u} Prop) :=
  TopCat.ofHom
    ⟨fun p => ULift.up (p ∈ U), continuous_uliftUp.comp (continuous_Prop.mpr hU)⟩

private theorem tubeOpenClassifier_square (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V) :
    TopCat.ofHom H ≫ oldOpenClassifier U hU =
      sideInclusion (I := I) d ≫ cylinderOpenClassifier d V hV := by
  apply TopCat.ext
  intro s
  apply ULift.ext
  exact propext (htrace s)

private def tubeOpenClassifier (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V) :
    refinedTubeSpace d H ⟶ TopCat.of (ULift.{u} Prop) :=
  pushout.desc (oldOpenClassifier U hU) (cylinderOpenClassifier d V hV)
    (tubeOpenClassifier_square d H U V hU hV htrace)

private def descendedTubeOpen (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V) :
    Set (refinedTubeSpace d H) :=
  {x | (tubeOpenClassifier d H U V hU hV htrace x).down}

private theorem descendedTubeOpen_isOpen (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V) :
    IsOpen (descendedTubeOpen d H U V hU hV htrace) :=
  continuous_Prop.mp
    (continuous_uliftDown.comp (tubeOpenClassifier d H U V hU hV htrace).hom.continuous)

private theorem descendedTubeOpen_old (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V)
    (a : A) :
    oldIntoTubeSpace d H a ∈ descendedTubeOpen d H U V hU hV htrace ↔ a ∈ U := by
  have h : tubeOpenClassifier d H U V hU hV htrace (oldIntoTubeSpace d H a) =
      oldOpenClassifier U hU a := by
    simpa only [tubeOpenClassifier, oldIntoTubeSpace, TopCat.comp_app] using!
      ConcreteCategory.congr_hom (pushout.inl_desc
        (oldOpenClassifier U hU) (cylinderOpenClassifier d V hV)
        (tubeOpenClassifier_square d H U V hU hV htrace)) a
  change (tubeOpenClassifier d H U V hU hV htrace (oldIntoTubeSpace d H a)).down ↔ a ∈ U
  exact iff_of_eq (congrArg ULift.down h)

private theorem descendedTubeOpen_cylinder (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set A) (V : Set (cylinderSum (I := I) d))
    (hU : IsOpen U) (hV : IsOpen V)
    (htrace : ∀ s : sideSum (I := I) d, H s ∈ U ↔ sideInclusion d s ∈ V)
    (p : cylinderSum (I := I) d) :
    pushout.inr (TopCat.ofHom H) (sideInclusion d) p ∈
      descendedTubeOpen d H U V hU hV htrace ↔ p ∈ V := by
  have h : tubeOpenClassifier d H U V hU hV htrace
      (pushout.inr (TopCat.ofHom H) (sideInclusion d) p) = cylinderOpenClassifier d V hV p := by
    simpa only [tubeOpenClassifier, TopCat.comp_app] using!
      ConcreteCategory.congr_hom (pushout.inr_desc
        (oldOpenClassifier U hU) (cylinderOpenClassifier d V hV)
        (tubeOpenClassifier_square d H U V hU hV htrace)) p
  change (tubeOpenClassifier d H U V hU hV htrace
      (pushout.inr (TopCat.ofHom H) (sideInclusion d) p)).down ↔ p ∈ V
  exact iff_of_eq (congrArg ULift.down h)

private theorem descendedTubeOpen_disjoint (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U₁ U₂ : Set A) (V₁ V₂ : Set (cylinderSum (I := I) d))
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (htrace₁ : ∀ s : sideSum (I := I) d, H s ∈ U₁ ↔ sideInclusion d s ∈ V₁)
    (htrace₂ : ∀ s : sideSum (I := I) d, H s ∈ U₂ ↔ sideInclusion d s ∈ V₂)
    (hU : Disjoint U₁ U₂) (hV : Disjoint V₁ V₂) :
    Disjoint (descendedTubeOpen d H U₁ V₁ hU₁ hV₁ htrace₁)
      (descendedTubeOpen d H U₂ V₂ hU₂ hV₂ htrace₂) := by
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  let hs := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  rcases Types.eq_or_eq_of_isPushout (hs.map (forget TopCat)) x with hx | hx
  · rcases hx with ⟨a, rfl⟩
    exact Set.disjoint_left.mp hU
      ((descendedTubeOpen_old d H U₁ V₁ hU₁ hV₁ htrace₁ a).mp hx₁)
      ((descendedTubeOpen_old d H U₂ V₂ hU₂ hV₂ htrace₂ a).mp hx₂)
  · rcases hx with ⟨p, rfl⟩
    exact Set.disjoint_left.mp hV
      ((descendedTubeOpen_cylinder d H U₁ V₁ hU₁ hV₁ htrace₁ p).mp hx₁)
      ((descendedTubeOpen_cylinder d H U₂ V₂ hU₂ hV₂ htrace₂ p).mp hx₂)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module actual sphere collar in each original disk×interval.
Separating opens of A are extended through the ACTUAL varying attaching H.
The collar, radial sphere point, continuity and boundary trace are derived.
No tube Hausdorff/CW, countability or supplied open extension is assumed. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private abbrev OriginalCylinderRow (d : ℕ) :=
  (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval

private def originalSphereCollar (d : ℕ) : Set (OriginalCylinderRow.{u} d) :=
  {p | (1 / 2 : ℝ) < ‖p.1.down.val‖}

private theorem originalSphereCollar_open (d : ℕ) :
    IsOpen (originalSphereCollar.{u} d) :=
  isOpen_lt continuous_const
    (continuous_norm.comp
      (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)))

private theorem originalSide_norm (d : ℕ)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) :
    ‖((Topology.CWComplex.classicalCellDiskPair.{u} d).map s).down.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp s.down.property

private theorem originalSide_mem_collar (d : ℕ)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : unitInterval) :
    ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t) ∈ originalSphereCollar d := by
  change (1 / 2 : ℝ) < ‖((Topology.CWComplex.classicalCellDiskPair.{u} d).map s).down.val‖
  rw [originalSide_norm]
  norm_num

private theorem collarVector_ne_zero (d : ℕ) (p : originalSphereCollar.{u} d) :
    p.val.1.down.val ≠ (0 : Fin d → ℝ) :=
  norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) p.property)

private def originalCollarSpherePoint (d : ℕ) :
    C(originalSphereCollar.{u} d,
      (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) where
  toFun p := ULift.up
    ⟨(‖p.val.1.down.val‖⁻¹ : ℝ) • p.val.1.down.val,
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (collarVector_ne_zero d p))⟩
  continuous_toFun := by
    have hc : Continuous (fun p : originalSphereCollar.{u} d => p.val.1.down.val) :=
      continuous_subtype_val.comp
        (continuous_uliftDown.comp (continuous_fst.comp continuous_subtype_val))
    have hn : ∀ p : originalSphereCollar.{u} d, ‖p.val.1.down.val‖ ≠ 0 :=
      fun p => (norm_pos_iff.mpr (collarVector_ne_zero d p)).ne'
    have hs : Continuous (fun p : originalSphereCollar.{u} d =>
        (⟨(‖p.val.1.down.val‖⁻¹ : ℝ) • p.val.1.down.val,
          mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (collarVector_ne_zero d p))⟩ :
            Metric.sphere (0 : Fin d → ℝ) 1)) :=
      (((continuous_norm.comp hc).inv₀ hn).smul hc).subtype_mk _
    exact continuous_uliftUp.comp hs

private def originalCollarNormalizer (d : ℕ) :
    C(originalSphereCollar.{u} d,
      (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) :=
  (originalCollarSpherePoint d).prodMk
    ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

private theorem originalCollarNormalizer_side (d : ℕ)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd) (t : unitInterval) :
    originalCollarNormalizer d
      ⟨((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t),
        originalSide_mem_collar d s t⟩ = (s, t) := by
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change (‖s.down.val‖⁻¹ : ℝ) • s.down.val = s.down.val
    rw [mem_sphere_zero_iff_norm.mp s.down.property, inv_one, one_smul]
  · rfl

private def originalAttachingRow (d : ℕ) (H : C(sideSum (I := I) d, A)) (i : I) :
    C((Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval, A) :=
  H.comp
    (⟨fun p : (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval =>
        (⟨i, p⟩ : sideSum (I := I) d), by
          change Continuous
            (@Sigma.mk I
              (fun _ : I => (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval) i)
          exact continuous_sigmaMk
            (σ := fun _ : I => (Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval)
            (i := i)⟩ :
      C((Topology.CWComplex.classicalCellDiskPair.{u} d).snd × unitInterval,
        sideSum (I := I) d))

private def collarOpenRow (d : ℕ) (H : C(sideSum (I := I) d, A))
    (U : Set A) (i : I) : Set (OriginalCylinderRow.{u} d) :=
  Subtype.val '' ((originalCollarNormalizer d) ⁻¹' ((originalAttachingRow d H i) ⁻¹' U))

private theorem collarOpenRow_isOpen (d : ℕ) (H : C(sideSum (I := I) d, A))
    (U : Set A) (hU : IsOpen U) (i : I) : IsOpen (collarOpenRow d H U i) :=
  (originalSphereCollar_open d).isOpenMap_subtype_val _
    ((hU.preimage (originalAttachingRow d H i).continuous).preimage
      (originalCollarNormalizer d).continuous)

private def collarOpenFamily (d : ℕ) (H : C(sideSum (I := I) d, A))
    (U : Set A) : Set (cylinderSum (I := I) d) :=
  {p | p.2 ∈ collarOpenRow d H U p.1}

private theorem collarOpenFamily_isOpen (d : ℕ) (H : C(sideSum (I := I) d, A))
    (U : Set A) (hU : IsOpen U) : IsOpen (collarOpenFamily d H U) := by
  rw [isOpen_sigma_iff]
  intro i
  exact collarOpenRow_isOpen d H U hU i

private theorem collarOpenFamily_boundary_trace (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (U : Set A) (p : sideSum (I := I) d) :
    H p ∈ U ↔ sideInclusion d p ∈ collarOpenFamily d H U := by
  rcases p with ⟨i, s, t⟩
  change H ⟨i, (s, t)⟩ ∈ U ↔
    ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t) ∈ collarOpenRow d H U i
  constructor
  · intro h
    refine ⟨⟨((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t),
      originalSide_mem_collar d s t⟩, ?_, rfl⟩
    change H ⟨i, originalCollarNormalizer d
      ⟨((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t),
        originalSide_mem_collar d s t⟩⟩ ∈ U
    rw [originalCollarNormalizer_side]
    exact h
  · rintro ⟨q, hq, heq⟩
    have hqeq : q =
        ⟨((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, t),
          originalSide_mem_collar d s t⟩ :=
      Subtype.ext heq
    change H ⟨i, originalCollarNormalizer d q⟩ ∈ U at hq
    rw [hqeq, originalCollarNormalizer_side] at hq
    exact hq

private theorem collarOpenFamily_disjoint (d : ℕ) (H : C(sideSum (I := I) d, A))
    (U V : Set A) (hUV : Disjoint U V) :
    Disjoint (collarOpenFamily d H U) (collarOpenFamily d H V) := by
  apply Set.disjoint_left.mpr
  intro p hpU hpV
  rcases hpU with ⟨q, hq, hqp⟩
  rcases hpV with ⟨r, hr, hrp⟩
  have hqr : q = r := Subtype.ext (hqp.trans hrp.symm)
  change H ⟨p.1, originalCollarNormalizer d q⟩ ∈ U at hq
  change H ⟨p.1, originalCollarNormalizer d r⟩ ∈ V at hr
  rw [← hqr] at hr
  exact Set.disjoint_left.mp hUV hq hr

private theorem actualTubeOldPoints_separated (d : ℕ)
    (H : C(sideSum (I := I) d, A)) [T2Space A] (a b : A) (hab : a ≠ b) :
    ∃ U V : Set (refinedTubeSpace d H), IsOpen U ∧ IsOpen V ∧
      oldIntoTubeSpace d H a ∈ U ∧ oldIntoTubeSpace d H b ∈ V ∧ Disjoint U V := by
  obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := T2Space.t2 hab
  let Uc := collarOpenFamily d H U
  let Vc := collarOpenFamily d H V
  have hUc : IsOpen Uc := collarOpenFamily_isOpen d H U hU
  have hVc : IsOpen Vc := collarOpenFamily_isOpen d H V hV
  have htraceU := collarOpenFamily_boundary_trace d H U
  have htraceV := collarOpenFamily_boundary_trace d H V
  refine ⟨descendedTubeOpen d H U Uc hU hUc htraceU,
    descendedTubeOpen d H V Vc hV hVc htraceV,
    descendedTubeOpen_isOpen d H U Uc hU hUc htraceU,
    descendedTubeOpen_isOpen d H V Vc hV hVc htraceV, ?_, ?_, ?_⟩
  · exact (descendedTubeOpen_old d H U Uc hU hUc htraceU a).mpr ha
  · exact (descendedTubeOpen_old d H V Vc hV hVc htraceV b).mpr hb
  · exact descendedTubeOpen_disjoint d H U V Uc Vc hU hV hUc hVc htraceU htraceV hUV
      (collarOpenFamily_disjoint d H U V hUV)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module off-side open-set geometry for the ACTUAL tube quotient.
The entire sigma family of disk interiors is open in the raw cylinder
family. Its separating opens descend with an EMPTY old-stage open.
No Hausdorff/CW structure on the tube and no finite family are assumed. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private theorem cylinderOffSide_open (d : ℕ) : IsOpen (cylinderOffSide.{u} d) := by
  have hc : IsClosed (Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map) :=
    (Topology.CWComplex.isClosedEmbedding_classicalCellDiskPair_map (n := d)).isClosed_range
  exact (hc.preimage continuous_fst).isOpen_compl

private def offSideCylinderInclusion (d : ℕ) :
    (Σ _ : I, cylinderOffSide.{u} d) → cylinderSum (I := I) d :=
  Sigma.map (id : I → I) (fun _ => Subtype.val)

private theorem offSideCylinderInclusion_openEmbedding (d : ℕ) :
    IsOpenEmbedding (offSideCylinderInclusion (I := I) d) :=
  (Topology.isOpenEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => (cylinderOffSide_open d).isOpenEmbedding_subtypeVal)

private theorem offSideCylinderInclusion_not_side (d : ℕ)
    (x : Σ _ : I, cylinderOffSide.{u} d) :
    offSideCylinderInclusion d x ∉ Set.range (sideInclusion (I := I) d) := by
  rintro ⟨⟨j, y⟩, h⟩
  have hij : j = x.fst := (Sigma.mk.inj_iff.mp h).1
  subst j
  have he : (⟨x.fst, sideProductMap.{u} d y⟩ : cylinderSum (I := I) d) =
      ⟨x.fst, x.snd.val⟩ := by
    simpa only [sideInclusion, offSideCylinderInclusion, sideProductMap,
      TopCat.hom_ofHom, ContinuousMap.coe_mk, Sigma.map, id_eq] using! h
  have hp : sideProductMap.{u} d y = x.snd.val :=
    (@sigma_mk_injective I
      (fun _ : I => (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)
      x.fst) he
  exact x.snd.property ⟨y.1, congrArg Prod.fst hp⟩

private theorem offSideCylinderInclusion_image_trace (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (U : Set (Σ _ : I, cylinderOffSide.{u} d)) (s : sideSum (I := I) d) :
    H s ∈ (∅ : Set A) ↔
      sideInclusion d s ∈ offSideCylinderInclusion d '' U := by
  constructor
  · intro h
    exact h.elim
  · rintro ⟨x, _, hx⟩
    exact (offSideCylinderInclusion_not_side d x) ⟨s, hx.symm⟩

private theorem offSideCylinderInclusion_disjoint_images (d : ℕ)
    (U V : Set (Σ _ : I, cylinderOffSide.{u} d)) (hUV : Disjoint U V) :
    Disjoint (offSideCylinderInclusion d '' U) (offSideCylinderInclusion d '' V) := by
  apply Set.disjoint_left.mpr
  intro p hpU hpV
  rcases hpU with ⟨x, hx, hxp⟩
  rcases hpV with ⟨y, hy, hyp⟩
  have hxy : x = y :=
    (offSideCylinderInclusion_openEmbedding d).injective (hxp.trans hyp.symm)
  subst y
  exact Set.disjoint_left.mp hUV hx hy

private theorem actualTubeOffSidePoints_separated (d : ℕ)
    (H : C(sideSum (I := I) d, A))
    (x y : Σ _ : I, cylinderOffSide.{u} d) (hxy : x ≠ y) :
    ∃ U V : Set (refinedTubeSpace d H), IsOpen U ∧ IsOpen V ∧
      wholeOffSideCylinderMap d H x ∈ U ∧
      wholeOffSideCylinderMap d H y ∈ V ∧ Disjoint U V := by
  let : T2Space ((Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) := by
    change T2Space (ULift.{u} (Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval)
    infer_instance
  let : T2Space (cylinderOffSide.{u} d) := by infer_instance
  let : T2Space (Σ _ : I, cylinderOffSide.{u} d) := by infer_instance
  obtain ⟨Ux, Vx, hUx, hVx, hx, hy, hUVx⟩ := T2Space.t2 hxy
  let Uc := offSideCylinderInclusion d '' Ux
  let Vc := offSideCylinderInclusion d '' Vx
  have hUc : IsOpen Uc := (offSideCylinderInclusion_openEmbedding d).isOpenMap Ux hUx
  have hVc : IsOpen Vc := (offSideCylinderInclusion_openEmbedding d).isOpenMap Vx hVx
  have htraceU := offSideCylinderInclusion_image_trace d H Ux
  have htraceV := offSideCylinderInclusion_image_trace d H Vx
  refine ⟨descendedTubeOpen d H ∅ Uc isOpen_empty hUc htraceU,
    descendedTubeOpen d H ∅ Vc isOpen_empty hVc htraceV,
    descendedTubeOpen_isOpen d H ∅ Uc isOpen_empty hUc htraceU,
    descendedTubeOpen_isOpen d H ∅ Vc isOpen_empty hVc htraceV, ?_, ?_, ?_⟩
  · change pushout.inr (TopCat.ofHom H) (sideInclusion d)
        (offSideCylinderInclusion d x) ∈
      descendedTubeOpen d H ∅ Uc isOpen_empty hUc htraceU
    exact (descendedTubeOpen_cylinder d H ∅ Uc isOpen_empty hUc htraceU
      (offSideCylinderInclusion d x)).mpr ⟨x, hx, rfl⟩
  · change pushout.inr (TopCat.ofHom H) (sideInclusion d)
        (offSideCylinderInclusion d y) ∈
      descendedTubeOpen d H ∅ Vc isOpen_empty hVc htraceV
    exact (descendedTubeOpen_cylinder d H ∅ Vc isOpen_empty hVc htraceV
      (offSideCylinderInclusion d y)).mpr ⟨y, hy, rfl⟩
  · exact descendedTubeOpen_disjoint d H ∅ ∅ Uc Vc isOpen_empty isOpen_empty
      hUc hVc htraceU htraceV (by simp)
      (offSideCylinderInclusion_disjoint_images d Ux Vx hUVx)

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module separation of an actual old-stage point from an off-side
tube point. A positive closed ball is chosen in THAT original metric
disk×interval, inside its open off-side set. The whole arbitrary sigma
family need not be compact, finite, metrizable or Hausdorff beforehand. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private theorem actualOffSide_closed_ball_neighborhood (d : ℕ)
    (x : Σ _ : I, cylinderOffSide.{u} d) :
    ∃ U F : Set (cylinderSum (I := I) d), IsOpen U ∧ IsClosed F ∧
      offSideCylinderInclusion d x ∈ U ∧ U ⊆ F ∧
        Disjoint F (Set.range (sideInclusion (I := I) d)) := by
  let : MetricSpace ((Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval) := by
    change MetricSpace (ULift.{u} (Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval)
    infer_instance
  have hn : cylinderOffSide.{u} d ∈ 𝓝 x.snd.val :=
    (cylinderOffSide_open d).mem_nhds x.snd.property
  obtain ⟨r, hr, hclosed⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall x.snd.val r ⊆ cylinderOffSide.{u} d :=
    Metric.nhds_basis_closedBall.mem_iff.mp hn
  let U : Set (cylinderSum (I := I) d) :=
    Sigma.mk x.fst '' Metric.ball x.snd.val r
  let F : Set (cylinderSum (I := I) d) :=
    Sigma.mk x.fst '' Metric.closedBall x.snd.val r
  have hU : IsOpen U := isOpenMap_sigmaMk _ Metric.isOpen_ball
  have hF : IsClosed F := isClosedMap_sigmaMk _ Metric.isClosed_closedBall
  refine ⟨U, F, hU, hF, ⟨x.snd.val, Metric.mem_ball_self hr, rfl⟩, ?_, ?_⟩
  · rintro z ⟨p, hp, hpz⟩
    exact ⟨p, Metric.ball_subset_closedBall hp, hpz⟩
  · apply Set.disjoint_left.mpr
    intro z hzF hzSide
    rcases hzF with ⟨p, hp, hpz⟩
    rcases hzSide with ⟨⟨j, s, t⟩, hsz⟩
    have he : (⟨j, sideProductMap.{u} d (s, t)⟩ : cylinderSum (I := I) d) =
        ⟨x.fst, p⟩ := hsz.trans hpz.symm
    have hij : j = x.fst := (Sigma.mk.inj_iff.mp he).1
    subst j
    have hside : sideProductMap.{u} d (s, t) = p :=
      (@sigma_mk_injective I
        (fun _ : I => (Topology.CWComplex.classicalCellDiskPair.{u} d).fst × unitInterval)
        x.fst) he
    exact (hclosed hp) ⟨s, congrArg Prod.fst hside⟩

private theorem actualTubeOldOffSidePoints_separated (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (a : A)
    (x : Σ _ : I, cylinderOffSide.{u} d) :
    ∃ U V : Set (refinedTubeSpace d H), IsOpen U ∧ IsOpen V ∧
      oldIntoTubeSpace d H a ∈ U ∧
      wholeOffSideCylinderMap d H x ∈ V ∧ Disjoint U V := by
  obtain ⟨B, F, hB, hF, hxB, hBF, hFside⟩ :=
    actualOffSide_closed_ball_neighborhood d x
  have htraceOld (s : sideSum (I := I) d) :
      H s ∈ (Set.univ : Set A) ↔ sideInclusion d s ∈ Fᶜ := by
    constructor
    · intro _ hsF
      exact Set.disjoint_left.mp hFside hsF (Set.mem_range_self s)
    · intro _
      exact Set.mem_univ _
  have htraceNew (s : sideSum (I := I) d) :
      H s ∈ (∅ : Set A) ↔ sideInclusion d s ∈ B := by
    constructor
    · intro h
      exact h.elim
    · intro hsB
      exact Set.disjoint_left.mp hFside (hBF hsB) (Set.mem_range_self s)
  have hFB : Disjoint Fᶜ B := by
    apply Set.disjoint_left.mpr
    intro p hpF hpB
    exact hpF (hBF hpB)
  refine ⟨descendedTubeOpen d H Set.univ Fᶜ isOpen_univ hF.isOpen_compl htraceOld,
    descendedTubeOpen d H ∅ B isOpen_empty hB htraceNew,
    descendedTubeOpen_isOpen d H Set.univ Fᶜ isOpen_univ hF.isOpen_compl htraceOld,
    descendedTubeOpen_isOpen d H ∅ B isOpen_empty hB htraceNew, ?_, ?_, ?_⟩
  · exact (descendedTubeOpen_old d H Set.univ Fᶜ isOpen_univ hF.isOpen_compl
      htraceOld a).mpr (Set.mem_univ a)
  · change pushout.inr (TopCat.ofHom H) (sideInclusion d)
        (offSideCylinderInclusion d x) ∈ descendedTubeOpen d H ∅ B isOpen_empty hB htraceNew
    exact (descendedTubeOpen_cylinder d H ∅ B isOpen_empty hB htraceNew
      (offSideCylinderInclusion d x)).mpr hxB
  · exact descendedTubeOpen_disjoint d H Set.univ ∅ Fᶜ B isOpen_univ isOpen_empty
      hF.isOpen_compl hB htraceOld htraceNew (by simp) hFB

end ActualRefinedTubeCharacteristicConstruction47

end

/- Same-module complete Hausdorff construction for the ACTUAL tube and
the actual X-only finite recursion. Type pushout coverage is refined to
old-stage or off-side points. All three separating-open constructions
are instantiated; the new tube's T2/CW is never an input.

Compatible classical CW fields and their end labels are still separate
outputs of the full af676 construction, not discharged by this fragment. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

variable {I : Type u} {A : TopCat.{u}}

private theorem actualTubePoint_old_or_offSide (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (z : refinedTubeSpace d H) :
    (∃ a : A, oldIntoTubeSpace d H a = z) ∨
      ∃ x : Σ _ : I, cylinderOffSide.{u} d, wholeOffSideCylinderMap d H x = z := by
  let sq := IsPushout.of_hasPushout (TopCat.ofHom H) (sideInclusion (I := I) d)
  rcases Types.eq_or_eq_of_isPushout' (sq.map (forget TopCat)) z with
    ha | ⟨⟨i, p⟩, hp, hside⟩
  · exact Or.inl ha
  · have hoff : p.1 ∉ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map := by
      rintro ⟨s, hs⟩
      apply hside
      refine ⟨⟨i, (s, p.2)⟩, ?_⟩
      change (⟨i, ((Topology.CWComplex.classicalCellDiskPair.{u} d).map s, p.2)⟩ :
        cylinderSum (I := I) d) = ⟨i, p⟩
      rw [hs]
    exact Or.inr ⟨⟨i, ⟨p, hoff⟩⟩, hp⟩

private def actualTubeT2Space (d : ℕ)
    (H : C(sideSum (I := I) d, A)) [T2Space A] :
    T2Space (refinedTubeSpace d H) where
  t2 := by
    intro z w hzw
    rcases actualTubePoint_old_or_offSide d H z with ⟨a, rfl⟩ | ⟨x, rfl⟩
    · rcases actualTubePoint_old_or_offSide d H w with ⟨b, rfl⟩ | ⟨y, rfl⟩
      · exact actualTubeOldPoints_separated d H a b
          (fun hab => hzw (congrArg (oldIntoTubeSpace d H) hab))
      · exact actualTubeOldOffSidePoints_separated d H a y
    · rcases actualTubePoint_old_or_offSide d H w with ⟨b, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨U, V, hU, hV, hb, hx, hUV⟩ :=
          actualTubeOldOffSidePoints_separated d H b x
        exact ⟨V, U, hV, hU, hx, hb, hUV.symm⟩
      · exact actualTubeOffSidePoints_separated d H x y
          (fun hxy => hzw (congrArg (wholeOffSideCylinderMap d H) hxy))

end ActualRefinedTubeCharacteristicConstruction47

namespace ActualCommonSuccessorConstruction

open ActualRefinedTubeCharacteristicConstruction47

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualSuccessorT2Space {n : ℕ} (S : Stage X n)
    [T2Space S.space] : T2Space (actualSuccessorSpace S) := by
  let : T2Space (smallIntermediate S) := actualIntermediateT2Space S
  exact actualTubeT2Space (n + 1) (smallSuccessorBoundary S)

private def actualFiniteStagesT2Space (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] :
    ∀ n : ℕ, T2Space (actualFiniteStages X n).space := by
  intro n
  induction n with
  | zero =>
      change T2Space (Topology.CWComplex.skeletonTop X 1)
      infer_instance
  | succ n ih =>
      let : T2Space (actualFiniteStages X n).space := ih
      change T2Space (actualSuccessorSpace (actualFiniteStages X n))
      exact actualSuccessorT2Space (actualFiniteStages X n)

private def actualFiniteIntermediateT2Space (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    T2Space (smallIntermediate (actualFiniteStages X n)) := by
  let : T2Space (actualFiniteStages X n).space := actualFiniteStagesT2Space X n
  exact actualIntermediateT2Space (actualFiniteStages X n)

end ActualCommonSuccessorConstruction

end

/- CW invariant for the original-space finite stages.
Dimension induction constructs this invariant rather than assuming it in
the original-space constructor. The spaces and end maps are the existing
recursion, whose separation and end-closedness properties have been derived.

The common n-stage may contain (n+1)-cells from disk cylinders. Its weak
polyhedral end has face cardinality at most n+1. These are different bounds. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private structure ActualFiniteClassicalData (n : ℕ) where
  cw : Topology.CWComplex (Set.univ : Set (actualFiniteStages X n).space)
  originalLabels :
    letI := cw
    ∀ m, m < n + 1 → Topology.CWComplex.cell (Set.univ : Set X) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m
  originalDisk :
    letI := cw
    ∀ (m : ℕ) (hm : m < n + 1)
      (j : Topology.CWComplex.cell (Set.univ : Set X) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      (actualFiniteStages X n).original
          (originalLowerDiskToSkeleton (n + 1) m hm j q) =
        Topology.CWComplex.map (C := (Set.univ : Set (actualFiniteStages X n).space))
          m (originalLabels m hm j) q.down.val
  polyhedralLabels :
    letI := cw
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (actualFiniteStages X n).polyhedron.Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m
  polyhedralDisk :
    letI := cw
    ∀ (m : ℕ)
      (j : Topology.CWComplex.cell
        (Set.univ : Set (actualFiniteStages X n).polyhedron.Realization) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      (actualFiniteStages X n).polyhedral
          (Topology.CWComplex.map m j q.down.val) =
        Topology.CWComplex.map (C := (Set.univ : Set (actualFiniteStages X n).space))
          m (polyhedralLabels m j) q.down.val
  commonDimension :
    letI := cw
    ∀ m (j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m),
      m ≤ n + 1
  polyhedronFaceBound :
    ∀ a : Face (actualFiniteStages X n).polyhedron, a.val.card ≤ n + 1

end ActualCommonSuccessorConstruction

end

/- Initial CW invariant from the original space.
The original strict-bound-one CW structure supplies the initial invariant.
The zero homeomorphism matches its cells with the weak zero end.
Both zero-dimensional bounds are derived; no label equivalence, dimension
or CW witness, or matching state is supplied to the outer constructor.
The canonical realization cell bridge supplies the initial labels. The
successor CW fold is constructed in the following sections. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open OriginalStrictSkeletonCWConstruction47 WeakClassicalCWDimensionConstruction47
open ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

private def zeroCellPointEquiv {Y : Type u} [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set Y)]
    (hdim : ∀ m (j : Topology.CWComplex.cell (Set.univ : Set Y) m), m = 0) :
    Topology.CWComplex.cell (Set.univ : Set Y) 0 ≃ Y := by
  refine Equiv.ofBijective
    (fun j => Topology.CWComplex.map (C := (Set.univ : Set Y)) 0 j ![]) ⟨?_, ?_⟩
  · exact Topology.CWComplex.injective_map_zero (Set.univ : Set Y)
  · intro y
    have hunion : (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set Y) m),
        Topology.CWComplex.map (C := (Set.univ : Set Y)) m j ''
          Metric.closedBall (0 : Fin m → ℝ) 1) = (Set.univ : Set Y) :=
      Topology.CWComplex.union' (C := (Set.univ : Set Y))
    have hy : y ∈ ⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set Y) m),
        Topology.CWComplex.map (C := (Set.univ : Set Y)) m j ''
          Metric.closedBall (0 : Fin m → ℝ) 1 :=
      hunion.symm ▸ Set.mem_univ y
    rcases Set.mem_iUnion.mp hy with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨j, hj⟩
    have hm0 := hdim m j
    subst m
    rcases hj with ⟨q, hq, hpoint⟩
    have hq0 : q = (![] : Fin 0 → ℝ) := Subsingleton.elim _ _
    refine ⟨j, ?_⟩
    simpa only [hq0] using hpoint

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualInitialPolyhedron_face_bound
    (a : Face (actualFiniteStages X 0).polyhedron) : a.val.card ≤ 1 := by
  obtain ⟨j, hj⟩ := (show ∃ j, a.val = {j} from a.property)
  rw [hj, Finset.card_singleton]

private theorem actualInitialPolyhedral_dimension_zero (m : ℕ)
    (j : Topology.CWComplex.cell
      (Set.univ : Set (actualFiniteStages X 0).polyhedron.Realization) m) : m = 0 := by
  have hm := WeakClassicalCWDimensionConstruction47.weakCWCell_dimension_bound
    (actualFiniteStages X 0).polyhedron 1
    (actualInitialPolyhedron_face_bound X) m j
  omega

private theorem actualInitialOriginal_dimension_zero (m : ℕ) :
    letI := originalStageCW (X := X) 1
    ∀ j : Topology.CWComplex.cell
      (Set.univ : Set (Topology.CWComplex.skeletonTop X 1)) m, m = 0 := by
  let := originalStageCW (X := X) 1
  intro j
  have hj : originalStageLabels (X := X) 1 m j ∈
      Set.range (originalStageLabels (X := X) 1 m) := Set.mem_range_self j
  rw [originalStageLabels_range] at hj
  have hm : m < 1 := by exact_mod_cast hj
  omega

private def actualInitialOriginalLabels :
    letI := originalStageCW (X := X) 1
    letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
      change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
      exact originalStageCW (X := X) 1
    ∀ m, m < 1 → Topology.CWComplex.cell (Set.univ : Set X) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X 0).space) m := by
  letI := originalStageCW (X := X) 1
  letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
    change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
    exact originalStageCW (X := X) 1
  intro m hm
  have hm0 : m = 0 := by omega
  subst m
  simpa only using! (originalSuccessorCellEquiv (X := X) 0).symm.toEmbedding

private theorem actualInitialOriginalDisk (m : ℕ) (hm : m < 1)
    (j : Topology.CWComplex.cell (Set.univ : Set X) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := originalStageCW (X := X) 1
    letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
      change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
      exact originalStageCW (X := X) 1
    (actualFiniteStages X 0).original (originalLowerDiskToSkeleton 1 m hm j q) =
      Topology.CWComplex.map (C := (Set.univ : Set (actualFiniteStages X 0).space)) m
        (actualInitialOriginalLabels X m hm j) q.down.val := by
  let := originalStageCW (X := X) 1
  let : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
    change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
    exact originalStageCW (X := X) 1
  have hm0 : m = 0 := by omega
  subst m
  change originalLowerDiskToSkeleton 1 0 hm j q =
    Topology.CWComplex.characteristicDiskMap
      (X := Topology.CWComplex.skeletonTop X 1) 0
      ((originalSuccessorCellEquiv (X := X) 0).symm j) q
  have hleft : originalLowerDiskToSkeleton (X := X) 1 0 hm j q =
      Topology.CWComplex.characteristicDiskToSkeleton (X := X) 0 j q := by
    apply Subtype.ext
    rfl
  have hright : Topology.CWComplex.characteristicDiskMap
      (X := Topology.CWComplex.skeletonTop X 1) 0
      ((originalSuccessorCellEquiv (X := X) 0).symm j) q =
        Topology.CWComplex.characteristicDiskToSkeleton (X := X) 0 j q := by
    simpa only using! originalSuccessorCellEquiv_disk (X := X) 0 j q
  exact Eq.trans hleft hright.symm

private def actualInitialPolyhedralLabels :
    letI := originalStageCW (X := X) 1
    letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
      change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
      exact originalStageCW (X := X) 1
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (actualFiniteStages X 0).polyhedron.Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X 0).space) m := by
  letI := originalStageCW (X := X) 1
  letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
    change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
    exact originalStageCW (X := X) 1
  intro m
  by_cases hm : m = 0
  · subst m
    let eP := zeroCellPointEquiv (Y := (actualFiniteStages X 0).polyhedron.Realization)
      (actualInitialPolyhedral_dimension_zero X)
    let eO := zeroCellPointEquiv (Y := Topology.CWComplex.skeletonTop X 1)
      (actualInitialOriginal_dimension_zero X)
    exact (eP.trans ((Topology.CWComplex.commonZeroSkeleton X).homeomorph.toEquiv.trans
      eO.symm)).toEmbedding
  · exact
      ⟨fun j => (hm (actualInitialPolyhedral_dimension_zero X m j)).elim,
        fun j _ _ => (hm (actualInitialPolyhedral_dimension_zero X m j)).elim⟩

private theorem actualInitialPolyhedralDisk (m : ℕ)
    (j : Topology.CWComplex.cell
      (Set.univ : Set (actualFiniteStages X 0).polyhedron.Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := originalStageCW (X := X) 1
    letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
      change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
      exact originalStageCW (X := X) 1
    (actualFiniteStages X 0).polyhedral (Topology.CWComplex.map m j q.down.val) =
      Topology.CWComplex.map (C := (Set.univ : Set (actualFiniteStages X 0).space)) m
        (actualInitialPolyhedralLabels X m j) q.down.val := by
  let := originalStageCW (X := X) 1
  let : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
    change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
    exact originalStageCW (X := X) 1
  have hm0 := actualInitialPolyhedral_dimension_zero X m j
  subst m
  have hq : q.down.val = (![] : Fin 0 → ℝ) := Subsingleton.elim _ _
  rw [hq]
  let eP := zeroCellPointEquiv (Y := (actualFiniteStages X 0).polyhedron.Realization)
    (actualInitialPolyhedral_dimension_zero X)
  let eO := zeroCellPointEquiv (Y := Topology.CWComplex.skeletonTop X 1)
    (actualInitialOriginal_dimension_zero X)
  change (Topology.CWComplex.commonZeroSkeleton X).homeomorph (eP j) =
    eO (eO.symm ((Topology.CWComplex.commonZeroSkeleton X).homeomorph (eP j)))
  exact (eO.apply_symm_apply _).symm

private def actualInitialClassicalData : ActualFiniteClassicalData X 0 := by
  letI := originalStageCW (X := X) 1
  letI : Topology.CWComplex (Set.univ : Set (actualFiniteStages X 0).space) := by
    change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
    exact originalStageCW (X := X) 1
  refine
    { cw := by
        change Topology.CWComplex (Set.univ : Set (Topology.CWComplex.skeletonTop X 1))
        exact originalStageCW (X := X) 1
      originalLabels := actualInitialOriginalLabels X
      originalDisk := actualInitialOriginalDisk X
      polyhedralLabels := actualInitialPolyhedralLabels X
      polyhedralDisk := actualInitialPolyhedralDisk X
      commonDimension := ?_
      polyhedronFaceBound := actualInitialPolyhedron_face_bound X }
  intro m j
  have hm := actualInitialOriginal_dimension_zero X m j
  omega

end ActualCommonSuccessorConstruction

end

/- CW structure on the constructed intermediate space.
The CW input is the previous constructed invariant of the fixed recursion,
not a premise of the final constructor. The small family obtains its
canonical CW labels from the public mono package. The new CW fields are
constructed, while closedness and T2 use the derived inclusion laws.
No CW, label, subcomplex or dimension witness on the intermediate space
is supplied. Successor labels are treated by the subsequent induction. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction Topology.CWComplex.MatchedAmalgam
open WeakClassicalCWDimensionConstruction47

universe u



namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualSmallFamilyOldClassicalLabels {n : ℕ} (S : Stage X n) :
    Σ' κ : ∀ m, Topology.CWComplex.cell (Set.univ : Set S.polyhedron.Realization) m ↪
        Topology.CWComplex.cell (Set.univ : Set (smallFamilyComplex S).Realization) m,
      ∀ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set S.polyhedron.Realization) m)
        (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
        smallFamilyOld S (Topology.CWComplex.map m j q.down.val) =
          Topology.CWComplex.map m (κ m j) q.down.val := by
  let h := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.oldTarget_le_family
    (cellPolyhedron S) S.polyhedron (cellMap S)
  let L := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabelInclusion S.polyhedron
    (Function.Embedding.inr : S.vertices ↪
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.Labels (cellPolyhedron S))
    (smallFamilyComplex S) h
  refine ⟨L.fst, ?_⟩
  intro m j q
  let z : S.polyhedron.Realization := Topology.CWComplex.map m j q.down.val
  apply Realization.ext
  have hOld : (smallFamilyOld S z).point =
      z.point.map (Function.Embedding.inr : S.vertices ↪
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.Labels (cellPolyhedron S)) :=
    (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
      (cellMap S) (cellFiniteFaces S)).old_point z
  have hRelabel :
      (Realization.inclusion h
        (MappingCylinder.relabelHomeomorph S.polyhedron Function.Embedding.inr z)).point =
      z.point.map (Function.Embedding.inr : S.vertices ↪
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.Labels (cellPolyhedron S)) := by
    change ((MappingCylinder.relabelMorphism S.polyhedron Function.Embedding.inr).realization z).point = _
    exact MappingCylinder.relabelMorphism_point S.polyhedron Function.Embedding.inr z
  have hCW := congrArg Realization.point (L.snd m j q)
  exact Eq.trans hOld (Eq.trans hRelabel.symm hCW)

private def actualFiniteIntermediateMatching (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    MatchingCharacteristicData
      (TopCat.ofHom (actualFiniteStages X n).polyhedral)
      (TopCat.ofHom (smallFamilyOld (actualFiniteStages X n))) := by
  letI := D.cw
  let S := actualFiniteStages X n
  let B := actualSmallFamilyOldClassicalLabels X S
  exact
    { leftLabels := D.polyhedralLabels
      rightLabels := B.fst
      leftLaw := fun m j q => D.polyhedralDisk m j (ULift.up q)
      rightLaw := fun m j q => B.snd m j (ULift.up q) }

private def actualFiniteIntermediateCW (n : ℕ) (D : ActualFiniteClassicalData X n) :
    Topology.CWComplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) := by
  letI := D.cw
  exact Topology.CWComplex.MatchedAmalgam.classicalCWComplex (actualFiniteIntermediateMatching X n D)
    (actualFiniteStages_end_closed X n).2
    (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.oldInclusion_isClosedEmbedding
      (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
      (cellMap (actualFiniteStages X n)))

private def actualFiniteIntermediateOldLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ m, Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  intro m
  exact Function.Embedding.inl

private theorem actualFiniteIntermediateOldDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      smallIntermediateOld (actualFiniteStages X n) (Topology.CWComplex.map m j q.down.val) =
        Topology.CWComplex.map m (actualFiniteIntermediateOldLabels X n D m j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  intro j q
  exact (left_characteristic
    (actualFiniteIntermediateMatching X n D) _ _ m j q.down.val).symm

private def actualFiniteIntermediateFamilyLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  intro m
  exact
    ⟨rightCellTransfer (actualFiniteIntermediateMatching X n D) m,
      rightCellTransfer_injective (actualFiniteIntermediateMatching X n D) m⟩

private theorem actualFiniteIntermediateFamilyDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ (j : Topology.CWComplex.cell
      (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      smallIntermediateFamily (actualFiniteStages X n) (Topology.CWComplex.map m j q.down.val) =
        Topology.CWComplex.map m (actualFiniteIntermediateFamilyLabels X n D m j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  intro j q
  let S := actualFiniteStages X n
  let M := actualFiniteIntermediateMatching X n D
  let q₀ : Metric.closedBall (0 : Fin m → ℝ) 1 := q.down
  let hf := (actualFiniteStages_end_closed X n).2
  let hg := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.oldInclusion_isClosedEmbedding
    (cellPolyhedron S) S.polyhedron (cellMap S)
  have hright : smallIntermediateFamily S
      (Topology.CWComplex.map
        (C := (Set.univ : Set (smallFamilyComplex S).Realization)) m j q₀.val) =
      Topology.CWComplex.MatchedAmalgam.cellMap M m (rightCellTransfer M m j) q₀.val := by
    simpa only [smallIntermediateFamily] using!
      rightCellTransfer_closed_characteristic M m j q₀
  have hwhole : Topology.CWComplex.map
      (C := (Set.univ : Set (smallIntermediate S))) m
        (actualFiniteIntermediateFamilyLabels X n D m j) q₀.val =
      Topology.CWComplex.MatchedAmalgam.cellMap M m (rightCellTransfer M m j) q₀.val := by
    change cellPartialEquiv M hf hg m (rightCellTransfer M m j) q₀.val =
      Topology.CWComplex.MatchedAmalgam.cellMap M m (rightCellTransfer M m j) q₀.val
    exact cellPartialEquiv_apply M hf hg m (rightCellTransfer M m j) q₀.val
  exact Eq.trans hright hwhole.symm

private def actualFiniteIntermediateOriginalLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ m, m < n + 1 → Topology.CWComplex.cell (Set.univ : Set X) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  intro m hm
  exact (D.originalLabels m hm).trans (actualFiniteIntermediateOldLabels X n D m)

private theorem actualFiniteIntermediateOriginalDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (hm : m < n + 1) (j : Topology.CWComplex.cell (Set.univ : Set X) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    smallIntermediateOriginal (actualFiniteStages X n)
        (ActualRefinedTubeCharacteristicConstruction47.originalLowerDiskToSkeleton
          (n + 1) m hm j q) =
      Topology.CWComplex.map m (actualFiniteIntermediateOriginalLabels X n D m hm j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  exact (congrArg (smallIntermediateOld (actualFiniteStages X n))
    (D.originalDisk m hm j q)).trans
      (actualFiniteIntermediateOldDisk X n D m (D.originalLabels m hm j) q)

private theorem actualSmallFamilyCW_dimension (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (j : Topology.CWComplex.cell
      (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m) : m ≤ n + 1 := by
  let S := actualFiniteStages X n
  have hfaces : ∀ a : Face (smallFamilyComplex S), a.val.card ≤ n + 2 := by
    intro a
    have h := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Bounds.cylinderFamily_face_card_le
      (cellPolyhedron S) S.polyhedron (cellMap S) (n + 1) (n + 1)
      (fun i => actualSphere_subdivision_face_card_le (n + 1) (cellApproximation S i).subdivisions)
      D.polyhedronFaceBound a
    exact h.trans (max_le (by omega) (by omega))
  have hm := WeakClassicalCWDimensionConstruction47.weakCWCell_dimension_bound
    (smallFamilyComplex S) (n + 2) hfaces m j
  omega

private theorem actualFiniteIntermediateCW_dimension (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ m (j : Topology.CWComplex.cell
      (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m), m ≤ n + 1 := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  intro m j
  change Cell (actualFiniteIntermediateMatching X n D) m at j
  cases j with
  | inl a => exact D.commonDimension m a
  | inr b => exact actualSmallFamilyCW_dimension X n D m b.val

/- A first actual X-only instantiation is produced, while the full later
successor tube/end-label CW recursion still must be assembled. -/
private def actualFirstIntermediateCW :
    Topology.CWComplex (Set.univ : Set (smallIntermediate (actualFiniteStages X 0))) :=
  actualFiniteIntermediateCW X 0 (actualInitialClassicalData X)

private theorem actualFirstIntermediateCW_dimension :
    letI := actualFirstIntermediateCW X
    ∀ m (j : Topology.CWComplex.cell
      (Set.univ : Set (smallIntermediate (actualFiniteStages X 0))) m), m ≤ 1 :=
  actualFiniteIntermediateCW_dimension X 0 (actualInitialClassicalData X)

end ActualCommonSuccessorConstruction

end

/- Closed CW subcomplexes of the constructed intermediate space.
Both leg maps are the pushout inclusions. Their cell maps use the
constructed labels, and closedness follows from the inclusion lemmas.
The shared carrier is the previous polyhedral end, not all of A.
No new-stage CW/subcomplex or end-identification witness is supplied. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open Topology.CWComplex.MatchedAmalgam

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteIntermediateOldSubcomplex (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    Topology.CWComplex.Subcomplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  let S := actualFiniteStages X n
  let M : MatchingCharacteristicData (𝟙 S.space) (TopCat.ofHom (smallIntermediateOld S)) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := actualFiniteIntermediateOldLabels X n D
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => actualFiniteIntermediateOldDisk X n D m j (ULift.up q) }
  exact matchingRightSubcomplex M (smallIntermediateOld_closed S)

private theorem actualFiniteIntermediateOldSubcomplex_carrier (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateOldSubcomplex X n D : Set (smallIntermediate (actualFiniteStages X n))) =
      Set.range (smallIntermediateOld (actualFiniteStages X n)) := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

private theorem actualFiniteIntermediateOldSubcomplex_labels (n : ℕ)
    (D : ActualFiniteClassicalData X n) (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateOldSubcomplex X n D).I m =
      Set.range (actualFiniteIntermediateOldLabels X n D m) := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

private def actualFiniteIntermediateFamilySubcomplex (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    Topology.CWComplex.Subcomplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  let S := actualFiniteStages X n
  let B := TopCat.of (smallFamilyComplex S).Realization
  let M : MatchingCharacteristicData (𝟙 B) (TopCat.ofHom (smallIntermediateFamily S)) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := actualFiniteIntermediateFamilyLabels X n D
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => actualFiniteIntermediateFamilyDisk X n D m j (ULift.up q) }
  have hB : IsClosedEmbedding (smallIntermediateFamily S) :=
    actualIntermediateFamily_include_closed S (actualFiniteStages_end_closed X n).2
  exact matchingRightSubcomplex M hB

private theorem actualFiniteIntermediateFamilySubcomplex_carrier (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateFamilySubcomplex X n D : Set (smallIntermediate (actualFiniteStages X n))) =
      Set.range (smallIntermediateFamily (actualFiniteStages X n)) := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

private theorem actualFiniteIntermediateFamilySubcomplex_labels (n : ℕ)
    (D : ActualFiniteClassicalData X n) (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateFamilySubcomplex X n D).I m =
      Set.range (actualFiniteIntermediateFamilyLabels X n D m) := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

private theorem actualFiniteIntermediateWholeLegs_intersection (n : ℕ) :
    Set.range (smallIntermediateOld (actualFiniteStages X n)) ∩
        Set.range (smallIntermediateFamily (actualFiniteStages X n)) =
      Set.range (smallIntermediatePolyhedron (actualFiniteStages X n)) := by
  let S := actualFiniteStages X n
  let sq := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral) (TopCat.ofHom (smallFamilyOld S))
  ext z
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hab : smallIntermediateOld S a = smallIntermediateFamily S b := ha.trans hb.symm
    obtain ⟨p, hp, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
        (sq.map (forget TopCat)).isColimit (actualFiniteStages_end_closed X n).2.injective a b).mp hab
    exact ⟨p, (congrArg (smallIntermediateOld S) hp).trans ha⟩
  · rintro ⟨p, rfl⟩
    exact ⟨⟨S.polyhedral p, rfl⟩,
      ⟨smallFamilyOld S p, (smallIntermediate_identification S p).symm⟩⟩

end ActualCommonSuccessorConstruction

end

/- The selected original end as an intermediate CW subcomplex.
Its carrier is the map from the original strict skeleton. The constructed
original labels below the strict bound and their open-cell union give the
carrier equation. The entire old common stage is not identified by an
isomorphism here. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteIntermediateOriginalSubcomplex (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    Topology.CWComplex.Subcomplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  let S := actualFiniteStages X n
  let κ := actualFiniteIntermediateOriginalLabels X n D
  refine
    { carrier := Set.range (smallIntermediateOriginal S)
      I := fun m => if hm : m < n + 1 then Set.range (κ m hm) else ∅
      closed' := ((smallIntermediateOld_closed S).comp
        (actualFiniteStages_end_closed X n).1).isClosed_range
      union' := ?_ }
  rw [Set.empty_union]
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨m, hmU⟩
    rcases Set.mem_iUnion.mp hmU with ⟨j, hjCell⟩
    by_cases hm : m < n + 1
    · have hj : j.val ∈ Set.range (κ m hm) := by
        simpa only [dite_eq_left hm] using! j.property
      rcases hj with ⟨a, ha⟩
      have hcell : z ∈ Topology.CWComplex.openCell
          (C := (Set.univ : Set (smallIntermediate S))) m (κ m hm a) := by
        rw [ha]
        exact hjCell
      rcases hcell with ⟨x, hx, hxz⟩
      let q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst :=
        ULift.up ⟨x, Metric.ball_subset_closedBall hx⟩
      exact ⟨originalLowerDiskToSkeleton (n + 1) m hm a q,
        (actualFiniteIntermediateOriginalDisk X n D m hm a q).trans hxz⟩
    · have hj : j.val ∈ (∅ : Set (Topology.CWComplex.cell
          (Set.univ : Set (smallIntermediate S)) m)) := by
        simpa only [dite_eq_right hm] using! j.property
      exact hj.elim
  · rintro ⟨x, rfl⟩
    let E := Topology.CWComplex.skeletonLT (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞)
    have hxE : x.val ∈ (E : Set X) := x.property
    have hE : (⋃ (m : ℕ) (j : E.I m),
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j.val) =
        (E : Set X) := by
      simpa only [Set.empty_union] using! E.union'
    have hx : x.val ∈ ⋃ (m : ℕ) (j : E.I m),
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j.val :=
      hE.symm ▸ hxE
    rcases Set.mem_iUnion.mp hx with ⟨m, hmU⟩
    rcases Set.mem_iUnion.mp hmU with ⟨j, hjCell⟩
    have hm : m < n + 1 := by
      have hmn : (m : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
        simpa only [E, Topology.CWComplex.skeletonLT_I] using! j.property
      exact_mod_cast hmn
    rcases hjCell with ⟨a, ha, hax⟩
    let q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst :=
      ULift.up ⟨a, Metric.ball_subset_closedBall ha⟩
    have hqx : originalLowerDiskToSkeleton (n + 1) m hm j.val q = x := by
      apply Subtype.ext
      change Topology.CWComplex.characteristicDiskMap (X := X) m j.val q = x.val
      rw [Topology.CWComplex.characteristicDiskMap_apply]
      exact hax
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
      ⟨⟨κ m hm j.val, ?_⟩, a, ha, ?_⟩⟩
    · change κ m hm j.val ∈ (if hs : m < n + 1 then Set.range (κ m hs) else ∅)
      rw [dite_eq_left hm]
      exact Set.mem_range_self j.val
    · exact (actualFiniteIntermediateOriginalDisk X n D m hm j.val q).symm.trans
        (congrArg (smallIntermediateOriginal S) hqx)

private theorem actualFiniteIntermediateOriginalSubcomplex_carrier (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateOriginalSubcomplex X n D :
        Set (smallIntermediate (actualFiniteStages X n))) =
      Set.range (smallIntermediateOriginal (actualFiniteStages X n)) := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

private theorem actualFiniteIntermediateOriginalSubcomplex_labels (n : ℕ)
    (D : ActualFiniteClassicalData X n) (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    (actualFiniteIntermediateOriginalSubcomplex X n D).I m =
      if hm : m < n + 1 then Set.range (actualFiniteIntermediateOriginalLabels X n D m hm)
      else ∅ := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  rfl

end ActualCommonSuccessorConstruction

end

/- Copied-domain CW labels and endpoint maps.
The domain inclusion is the small-domain subcomplex. Its block tag and
family inclusion use the constructed classical mono labels, transported
through the intermediate family inclusion. No attaching map, copied-domain
CW comparison or endpoint law is supplied. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction
open ActualRefinedTubeCharacteristicConstruction47
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualCopiedDomainToFamily {n : ℕ} (S : Stage X n) (i : CellIndex (X := X) n) :
    C((MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization,
      (smallFamilyComplex S).Realization) := by
  let ι : C((MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization,
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
        (cellPolyhedron S) S.vertices) := by
    change C((MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization,
      (Σ j, (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization))
    exact ContinuousMap.sigmaMk
      (X := fun j => (MappingCylinder.domainComplex (cellPolyhedron S j) S.vertices).Realization) i
  exact (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
    (cellPolyhedron S) S.polyhedron (cellMap S)).hom.comp ι

private def actualCopiedDomainFamilyClassicalLabels {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) :
    Σ' κ : ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallFamilyComplex S).Realization) m,
      ∀ (m : ℕ)
        (j : Topology.CWComplex.cell
          (Set.univ : Set (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization) m)
        (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
        actualCopiedDomainToFamily X S i (Topology.CWComplex.map m j q.down.val) =
          Topology.CWComplex.map m (κ m j) q.down.val := by
  let h := small_domain_le (cellMap S i)
  let a := PreAbstractSimplicialComplex.Realization.classicalSubcomplexOfInclusion h
  let b := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabelInclusion (smallCylinder (cellMap S i))
    (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag (W := S.vertices) (cellPolyhedron S) i)
    (smallFamilyComplex S)
    (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.block_le_family
      (cellPolyhedron S) S.polyhedron (cellMap S) i)
  refine ⟨fun m => (a.fst m).trans (b.fst m), ?_⟩
  intro m j q
  let q₀ : Metric.closedBall (0 : Fin m → ℝ) 1 := q.down
  let z : (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization :=
    Topology.CWComplex.map
      (C := (Set.univ : Set (MappingCylinder.domainComplex
        (cellPolyhedron S i) S.vertices).Realization)) m j q₀.val
  have hentry : actualCopiedDomainToFamily X S i z =
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion
        (cellPolyhedron S) S.polyhedron (cellMap S) i
        ((MappingCylinder.inclusionMorphism h).realization z) := by
    simpa only [actualCopiedDomainToFamily, ContinuousMap.comp_apply,
      ContinuousMap.sigmaMk_apply] using!
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder_apply
        (cellPolyhedron S) S.polyhedron (cellMap S) i z
  have hinclusion : (MappingCylinder.inclusionMorphism h).realization z =
      Realization.inclusion h z := by
    apply Realization.ext
    exact actualSmallInclusionPoint h z
  have ha : Realization.inclusion h z =
      Topology.CWComplex.map (C := (Set.univ : Set (smallCylinder (cellMap S i)).Realization))
        m (a.fst m j) q₀.val := by
    simpa only [z, q₀] using! a.snd.property.2.2 m j q
  have hb : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion
      (cellPolyhedron S) S.polyhedron (cellMap S) i
      (Topology.CWComplex.map
        (C := (Set.univ : Set (smallCylinder (cellMap S i)).Realization))
        m (a.fst m j) q₀.val) =
      Topology.CWComplex.map (C := (Set.univ : Set (smallFamilyComplex S).Realization))
        m (b.fst m (a.fst m j)) q₀.val := by
    let y : (smallCylinder (cellMap S i)).Realization :=
      Topology.CWComplex.map m (a.fst m j) q₀.val
    apply Realization.ext
    have hBlock :
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion
          (cellPolyhedron S) S.polyhedron (cellMap S) i y).point =
        y.point.map
          (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
            (W := S.vertices) (cellPolyhedron S) i) :=
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion_point
        (cellPolyhedron S) S.polyhedron (cellMap S) i y
    have hRelabel :
        (Realization.inclusion
          (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.block_le_family
            (cellPolyhedron S) S.polyhedron (cellMap S) i)
          (MappingCylinder.relabelHomeomorph (smallCylinder (cellMap S i))
            (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
              (W := S.vertices) (cellPolyhedron S) i) y)).point =
        y.point.map
          (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
            (W := S.vertices) (cellPolyhedron S) i) := by
      change ((MappingCylinder.relabelMorphism (smallCylinder (cellMap S i))
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (W := S.vertices) (cellPolyhedron S) i)).realization y).point = _
      exact MappingCylinder.relabelMorphism_point (smallCylinder (cellMap S i))
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.tag
          (W := S.vertices) (cellPolyhedron S) i) y
    have hCW := congrArg Realization.point (b.snd m (a.fst m j) q)
    exact Eq.trans hBlock (Eq.trans hRelabel.symm hCW)
  have hmiddle := congrArg
    (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.blockInclusion
      (cellPolyhedron S) S.polyhedron (cellMap S) i) (Eq.trans hinclusion ha)
  exact Eq.trans hentry (Eq.trans hmiddle hb)

private def actualFiniteCopiedDomainToIntermediate (n : ℕ)
    (i : CellIndex (X := X) n) :
    C((MappingCylinder.domainComplex
        (cellPolyhedron (actualFiniteStages X n) i) (actualFiniteStages X n).vertices).Realization,
      smallIntermediate (actualFiniteStages X n)) :=
  (smallIntermediateFamily (actualFiniteStages X n)).comp
    (actualCopiedDomainToFamily X (actualFiniteStages X n) i)

private def actualFiniteCopiedDomainIntermediateLabels (n : ℕ)
    (D : ActualFiniteClassicalData X n) (i : CellIndex (X := X) n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (MappingCylinder.domainComplex
          (cellPolyhedron (actualFiniteStages X n) i) (actualFiniteStages X n).vertices).Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  intro m
  exact ((actualCopiedDomainFamilyClassicalLabels X (actualFiniteStages X n) i).fst m).trans
    (actualFiniteIntermediateFamilyLabels X n D m)

private theorem actualFiniteCopiedDomainIntermediateDisk (n : ℕ)
    (D : ActualFiniteClassicalData X n) (i : CellIndex (X := X) n) (m : ℕ)
    (j : Topology.CWComplex.cell
      (Set.univ : Set (MappingCylinder.domainComplex
        (cellPolyhedron (actualFiniteStages X n) i) (actualFiniteStages X n).vertices).Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    actualFiniteCopiedDomainToIntermediate X n i (Topology.CWComplex.map m j q.down.val) =
      Topology.CWComplex.map m (actualFiniteCopiedDomainIntermediateLabels X n D i m j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let a := actualCopiedDomainFamilyClassicalLabels X (actualFiniteStages X n) i
  exact (congrArg (smallIntermediateFamily (actualFiniteStages X n)) (a.snd m j q)).trans
    (actualFiniteIntermediateFamilyDisk X n D m (a.fst m j) q)

private theorem actualFiniteTopBoundary_matches_copiedDomain (n : ℕ)
    (i : CellIndex (X := X) n)
    (s : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).snd) :
    smallSuccessorBoundary (actualFiniteStages X n) ⟨i, (s, 1)⟩ =
      actualFiniteCopiedDomainToIntermediate X n i
        (originalSphereToCopiedDomain (W := (actualFiniteStages X n).vertices) (n + 1)
          (actualSubdivisions (actualFiniteStages X n) i) s) := by
  let S := actualFiniteStages X n
  let z : (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization :=
    originalSphereToCopiedDomain (W := S.vertices) (n + 1) (actualSubdivisions S i) s
  have hboundary : smallSuccessorBoundary S ⟨i, (s, 1)⟩ =
      smallIntermediateFamily S
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (cellPolyhedron S) S.polyhedron (cellMap S) ⟨i, z⟩) := by
    simpa only [z] using! actualTopBoundary_formula S i s
  have hcopied : actualFiniteCopiedDomainToIntermediate X n i z =
      smallIntermediateFamily S
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
          (cellPolyhedron S) S.polyhedron (cellMap S) ⟨i, z⟩) := by
    rfl
  exact Eq.trans hboundary hcopied.symm

end ActualCommonSuccessorConstruction

end

/- Constructed successor CW structure.
Cell charts, disjointness, finite lower frontiers and weak topology are
derived from the component lemmas at the constructed intermediate labels
and the successor endpoint laws. No tube CW/frontier/matching witness is
supplied. The previous invariant is the original-space induction hypothesis;
the complete successor end-label construction follows below. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47 CommonSuccessorSmallCylinderConstruction

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteSuccessorCW (n : ℕ) (D : ActualFiniteClassicalData X n) :
    Topology.CWComplex (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) := by
  let S := actualFiniteStages X n
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI : T2Space (smallIntermediate S) := actualFiniteIntermediateT2Space X n
  let d := n + 1
  let r := actualSubdivisions S
  let H := smallSuccessorBoundary S
  refine
    { cell := refinedTubeCellLabels (W := S.vertices) d r
      map := refinedTubeCellPartialEquiv d r H
      source_eq := refinedTubeCellPartialEquiv_source d r H
      continuousOn := refinedTubeCellPartialEquiv_continuousOn d r H
      continuousOn_symm := refinedTubeCellPartialEquiv_continuousOn_symm d r H
      pairwiseDisjoint' := refinedTubeCell_pairwiseDisjoint d r H
      mapsTo' := ?_
      closed' := fun F _ hF => refinedTubeCell_closed_of_intersections d r H F hF
      union' := refinedTubeCell_union d r H }
  intro m j
  rcases j with a | (a | (a | a))
  · exact oldCell_mapsTo_finite_lower (W := S.vertices) d r H m a
  · rcases a with ⟨i, hm⟩
    subst m
    exact originalBottomCell_mapsTo_finite_lower (X := X) (W := S.vertices) d r H i
      (smallIntermediateOriginal S) (actualFiniteIntermediateOriginalLabels X n D)
      (actualFiniteIntermediateOriginalDisk X n D) (smallSuccessorBoundary_zero S i)
  · rcases a with ⟨i, j⟩
    exact newTopCell_mapsTo_finite_lower d r i H
      (actualFiniteCopiedDomainToIntermediate X n i)
      (actualFiniteCopiedDomainIntermediateLabels X n D i)
      (actualFiniteCopiedDomainIntermediateDisk X n D i)
      (actualFiniteTopBoundary_matches_copiedDomain X n i) m j
  · rcases a with ⟨i, hm⟩
    subst m
    exact wholeTube_mapsTo_finite_lower d r i H
      (actualFiniteCopiedDomainToIntermediate X n i)
      (actualFiniteCopiedDomainIntermediateLabels X n D i)
      (actualFiniteCopiedDomainIntermediateDisk X n D i)
      (actualFiniteTopBoundary_matches_copiedDomain X n i)
      (actualFiniteIntermediateCW_dimension X n D)

private theorem actualFiniteSuccessorCW_dimension (n : ℕ)
    (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∀ m (j : Topology.CWComplex.cell
      (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m), m ≤ n + 2 := by
  let S := actualFiniteStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  intro m j
  change refinedTubeCellLabels (W := S.vertices) (n + 1) (actualSubdivisions S) m at j
  rcases j with a | (a | (a | a))
  · have hm := actualFiniteIntermediateCW_dimension X n D m a
    omega
  · rcases a with ⟨i, hm⟩
    omega
  · rcases a with ⟨i, j⟩
    have hm := refinedTopConeCell_dimension_bound (n + 1) (actualSubdivisions S i) m j.val
    omega
  · rcases a with ⟨i, hm⟩
    omega

private theorem actualNextPolyhedron_face_bound (n : ℕ) (D : ActualFiniteClassicalData X n)
    (a : Face (actualNextPolyhedron (actualFiniteStages X n))) : a.val.card ≤ n + 2 := by
  let S := actualFiniteStages X n
  have h := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Bounds.associatedFamily_face_card_le
    (cellPolyhedron S) S.polyhedron (cellMap S) (n + 1) (n + 1)
    (fun i => actualSphere_subdivision_face_card_le (n + 1) (cellApproximation S i).subdivisions)
    D.polyhedronFaceBound a
  exact h.trans (max_le (by omega) (by omega))

private def actualFirstSuccessorCW :
    Topology.CWComplex (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X 0))) :=
  actualFiniteSuccessorCW X 0 (actualInitialClassicalData X)

end ActualCommonSuccessorConstruction

end

/- Original successor labels and complete disk equations.
The old degrees use the intermediate labels. The new degree uses the
bottom disk with the original cell identifier. The constructed end
inclusion is preserved; no end CW/comparison is assumed. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47 CommonSuccessorSmallCylinderConstruction

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteSuccessorOldLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m ↪
      Topology.CWComplex.cell
        (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  intro m
  exact Function.Embedding.inl

private theorem actualFiniteSuccessorOldDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∀ (j : Topology.CWComplex.cell
      (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))
          (Topology.CWComplex.map m j q.down.val) =
        Topology.CWComplex.map m (actualFiniteSuccessorOldLabels X n D m j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  intro j q
  exact (refinedTubeCellPartialEquiv_closed_characteristic
    (n + 1) (actualSubdivisions (actualFiniteStages X n))
    (smallSuccessorBoundary (actualFiniteStages X n)) m (Sum.inl j) q).symm

private def actualFiniteSuccessorOriginalCell (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (hm : m < n + 2) (j : Topology.CWComplex.cell (Set.univ : Set X) m) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    Topology.CWComplex.cell
      (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  exact if hOld : m < n + 1 then
    Sum.inl (actualFiniteIntermediateOriginalLabels X n D m hOld j)
  else by
    have hnew : m = n + 1 := by omega
    subst m
    exact Sum.inr (Sum.inl ⟨j, rfl⟩)

private def actualFiniteSuccessorOriginalLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∀ m, m < n + 2 → Topology.CWComplex.cell (Set.univ : Set X) m ↪
      Topology.CWComplex.cell
        (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  intro m hm
  refine ⟨actualFiniteSuccessorOriginalCell X n D m hm, ?_⟩
  intro a b hab
  by_cases hOld : m < n + 1
  · have htag :
        (Sum.inl (actualFiniteIntermediateOriginalLabels X n D m hOld a) :
          refinedTubeCellLabels (W := (actualFiniteStages X n).vertices)
            (A := smallIntermediate (actualFiniteStages X n)) (n + 1)
            (actualSubdivisions (actualFiniteStages X n)) m) =
          Sum.inl (actualFiniteIntermediateOriginalLabels X n D m hOld b) := by
      have hbranch (j : Topology.CWComplex.cell (Set.univ : Set X) m) :
          actualFiniteSuccessorOriginalCell X n D m hm j =
            Sum.inl (actualFiniteIntermediateOriginalLabels X n D m hOld j) := by
        change (if h : m < n + 1 then
            (Sum.inl (actualFiniteIntermediateOriginalLabels X n D m h j) :
              refinedTubeCellLabels (W := (actualFiniteStages X n).vertices)
                (A := smallIntermediate (actualFiniteStages X n)) (n + 1)
                (actualSubdivisions (actualFiniteStages X n)) m)
            else _) = _
        exact dite_eq_left hOld
      exact (hbranch a).symm.trans (hab.trans (hbranch b))
    exact (actualFiniteIntermediateOriginalLabels X n D m hOld).injective (Sum.inl.inj htag)
  · have hnew : m = n + 1 := by omega
    subst m
    have htag :
        (Sum.inr (Sum.inl ⟨a, rfl⟩) :
          refinedTubeCellLabels (W := (actualFiniteStages X n).vertices)
            (A := smallIntermediate (actualFiniteStages X n)) (n + 1)
            (actualSubdivisions (actualFiniteStages X n)) (n + 1)) =
          Sum.inr (Sum.inl ⟨b, rfl⟩) := by
      have hbranch (j : Topology.CWComplex.cell (Set.univ : Set X) (n + 1)) :
          actualFiniteSuccessorOriginalCell X n D (n + 1) hm j =
            (Sum.inr (Sum.inl ⟨j, rfl⟩) :
              refinedTubeCellLabels (W := (actualFiniteStages X n).vertices)
                (A := smallIntermediate (actualFiniteStages X n)) (n + 1)
                (actualSubdivisions (actualFiniteStages X n)) (n + 1)) := by
        change (if h : n + 1 < n + 1 then _ else
            (Sum.inr (Sum.inl ⟨j, rfl⟩) :
              refinedTubeCellLabels (W := (actualFiniteStages X n).vertices)
                (A := smallIntermediate (actualFiniteStages X n)) (n + 1)
                (actualSubdivisions (actualFiniteStages X n)) (n + 1))) = _
        simp only [dite_eq_right (lt_irrefl (n + 1))]
      exact (hbranch a).symm.trans (hab.trans (hbranch b))
    exact congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj htag))

private theorem actualFiniteSuccessorOriginalDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (hm : m < n + 2) (j : Topology.CWComplex.cell (Set.univ : Set X) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    (actualFiniteStages X (n + 1)).original (originalLowerDiskToSkeleton (n + 2) m hm j q) =
      Topology.CWComplex.map m (actualFiniteSuccessorOriginalLabels X n D m hm j) q.down.val := by
  let S := actualFiniteStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  by_cases hOld : m < n + 1
  · have hsk : originalLowerDiskToSkeleton (n + 2) m hm j q =
        skeletonTransition X (n + 1) (originalLowerDiskToSkeleton (n + 1) m hOld j q) := by
      apply Subtype.ext
      rfl
    rw [hsk]
    have hlabel : actualFiniteSuccessorOriginalLabels X n D m hm j =
        actualFiniteSuccessorOldLabels X n D m
          (actualFiniteIntermediateOriginalLabels X n D m hOld j) := by
      change (if h : m < n + 1 then
          (Sum.inl (actualFiniteIntermediateOriginalLabels X n D m h j) :
            refinedTubeCellLabels (W := S.vertices) (A := smallIntermediate S)
              (n + 1) (actualSubdivisions S) m) else _) = _
      exact dite_eq_left hOld
    have hpoint := (actualOriginalSuccessorCollapse_old S
      (originalLowerDiskToSkeleton (n + 1) m hOld j q)).trans
        ((congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S))
          (actualFiniteIntermediateOriginalDisk X n D m hOld j q)).trans
            (actualFiniteSuccessorOldDisk X n D m
              (actualFiniteIntermediateOriginalLabels X n D m hOld j) q))
    exact hpoint.trans (congrArg
      (fun a : Topology.CWComplex.cell (Set.univ : Set (actualSuccessorSpace S)) m =>
        Topology.CWComplex.map m a q.down.val) hlabel.symm)
  · have hnew : m = n + 1 := by omega
    subst m
    have hsk : originalLowerDiskToSkeleton (n + 2) (n + 1) hm j q =
        characteristicDiskToSkeleton (X := X) (n + 1) j q := by
      apply Subtype.ext
      rfl
    rw [hsk]
    let a : refinedTubeCellLabels (W := S.vertices) (A := smallIntermediate S)
        (n + 1) (actualSubdivisions S) (n + 1) := Sum.inr (Sum.inl ⟨j, rfl⟩)
    have hlabel : actualFiniteSuccessorOriginalLabels X n D (n + 1) hm j = a := by
      change (if h : n + 1 < n + 1 then _ else a) = a
      exact dite_eq_right (lt_irrefl (n + 1))
    have hcharacteristic : originalCylinderMap (n + 1) (smallSuccessorBoundary S) j (q, 0) =
        Topology.CWComplex.map (C := (Set.univ : Set (actualSuccessorSpace S))) (n + 1) a q.down.val := by
      change originalCylinderMap (n + 1) (smallSuccessorBoundary S) j (q, 0) =
        refinedTubeCellPartialEquiv (n + 1) (actualSubdivisions S)
          (smallSuccessorBoundary S) (n + 1) a q.down.val
      have hc : refinedTubeClosedCharacteristic (n + 1) (actualSubdivisions S)
          (smallSuccessorBoundary S) (n + 1) a q =
            originalCylinderMap (n + 1) (smallSuccessorBoundary S) j (q, 0) := by
        rfl
      exact hc.symm.trans
        (refinedTubeCellPartialEquiv_closed_characteristic
          (n + 1) (actualSubdivisions S) (smallSuccessorBoundary S) (n + 1) a q).symm
    exact (actualOriginalSuccessorCollapse_disk S j q).trans
      (hcharacteristic.trans (congrArg
        (fun a : Topology.CWComplex.cell (Set.univ : Set (actualSuccessorSpace S)) (n + 1) =>
          Topology.CWComplex.map (n + 1) a q.down.val) hlabel.symm))

end ActualCommonSuccessorConstruction

end

/- Cell characteristic formulas for the associated cover.
No characteristic-map or kappa-naturality equation is supplied. A cell
center detects membership in a covering CW subcomplex. End injectivity
and the complete disk equation detect equality of cell labels. -/

noncomputable section

open Topology

universe u

namespace ActualCommonSuccessorConstruction

private theorem cell_mem_some_cover_subcomplex {J : Type u} {Y : Type u}
    [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (E : J → Topology.CWComplex.Subcomplex (Set.univ : Set Y))
    (hcover : (⋃ i, (E i : Set Y)) = Set.univ) (m : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set Y) m) :
    ∃ i : J, j ∈ (E i).I m := by
  let y := Topology.CWComplex.map (C := (Set.univ : Set Y)) m j (0 : Fin m → ℝ)
  have hy : y ∈ ⋃ i, (E i : Set Y) := by
    rw [hcover]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_contra hnot
  exact ((E i).disjoint_openCell_subcomplex_of_notMem hnot).notMem_of_mem_left
    ⟨0, by simp, rfl⟩ hi

private theorem characteristic_labels_injective {Z Y : Type u}
    [TopologicalSpace Z] [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set Z)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(Z, Y)) (hf : Function.Injective f)
    (κ : ∀ m, Topology.CWComplex.cell (Set.univ : Set Z) m →
      Topology.CWComplex.cell (Set.univ : Set Y) m)
    (hκ : ∀ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set Z) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      f (Topology.CWComplex.map m j q.down.val) = Topology.CWComplex.map m (κ m j) q.down.val)
    (m : ℕ) : Function.Injective (κ m) := by
  intro a b hab
  let q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst := ULift.up ⟨0, by simp⟩
  have hp : Topology.CWComplex.map (C := (Set.univ : Set Z)) m a (0 : Fin m → ℝ) =
      Topology.CWComplex.map (C := (Set.univ : Set Z)) m b 0 := by
    apply hf
    exact (hκ m a q).trans ((congrArg (fun j => Topology.CWComplex.map
      (C := (Set.univ : Set Y)) m j q.down.val) hab).trans (hκ m b q).symm)
  by_contra hne
  have hs : (⟨m, a⟩ : Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n) ≠ ⟨m, b⟩ := by
    intro h
    exact hne (sigma_mk_injective h)
  have hpRel : RelCWComplex.map (C := (Set.univ : Set Z)) m b (0 : Fin m → ℝ) =
      RelCWComplex.map (C := (Set.univ : Set Z)) m a 0 := by
    simpa only [Topology.CWComplex.map_def] using! hp.symm
  exact (Topology.CWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set Z)) hs).notMem_of_mem_left
    ⟨0, by simp, rfl⟩ ⟨0, by simp, hpRel⟩

end ActualCommonSuccessorConstruction

end

/- CW component cover of the associated complex.
The cylinder and each weak cone are injectively relabeled as subcomplexes.
Their complete disk equations yield the classical component subcomplexes.
The cylinder/ordinary-cone carrier cover gives the CW cover; no cover,
inverse or characteristic-map formula is supplied. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction
open Topology.CWComplex.MatchedAmalgam
open PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Cone
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualCylinderToNextPolyhedron {n : ℕ} (S : Stage X n) :
    C((smallFamilyComplex S).Realization, (actualNextPolyhedron S).Realization) :=
  (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
    (cellPolyhedron S) S.polyhedron (cellMap S)).hom

private def actualWeakConeToNextPolyhedron {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) :
    C((MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization,
      (actualNextPolyhedron S).Realization) := by
  let e : (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization ≃ₜ
      (attachedBlock (W := S.vertices) (cellPolyhedron S) i).Realization := by
    change (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization ≃ₜ
      (MappingCylinder.relabelComplex
        (MappingCylinder.coneComplex (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices))
        (coneTag (W := S.vertices) (cellPolyhedron S) i)).Realization
    exact MappingCylinder.relabelHomeomorph
      (MappingCylinder.coneComplex (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices))
      (coneTag (W := S.vertices) (cellPolyhedron S) i)
  let c : C((MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization,
      (attachedBlock (W := S.vertices) (cellPolyhedron S) i).Realization) :=
    ⟨e, (by
      exact e.continuous)⟩
  exact (⟨Realization.inclusion
      ((le_iSup (attachedBlock (W := S.vertices) (cellPolyhedron S)) i).trans le_sup_right),
    (by
      exact Realization.continuous_inclusion
        ((le_iSup (attachedBlock (W := S.vertices) (cellPolyhedron S)) i).trans le_sup_right))⟩ :
      C((attachedBlock (W := S.vertices) (cellPolyhedron S) i).Realization,
        (actualNextPolyhedron S).Realization)).comp c


private def actualCylinderNextPolyhedronLabels {n : ℕ} (S : Stage X n) :
    Σ' κ : ∀ m, Topology.CWComplex.cell (Set.univ : Set (smallFamilyComplex S).Realization) m ↪
        Topology.CWComplex.cell (Set.univ : Set (actualNextPolyhedron S).Realization) m,
      ∀ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (smallFamilyComplex S).Realization) m)
        (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
        actualCylinderToNextPolyhedron X S (Topology.CWComplex.map m j q.down.val) =
          Topology.CWComplex.map m (κ m j) q.down.val := by
  let h : MappingCylinder.relabelComplex (smallFamilyComplex S) Function.Embedding.inl ≤
      actualNextPolyhedron S := by exact le_sup_left
  let L := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabelInclusion (smallFamilyComplex S) Function.Embedding.inl
    (actualNextPolyhedron S) h
  refine ⟨L.fst, ?_⟩
  intro m j q
  have hMap :
      actualCylinderToNextPolyhedron X S (Topology.CWComplex.map m j q.down.val) =
      Realization.inclusion h
        (MappingCylinder.relabelHomeomorph (smallFamilyComplex S) Function.Embedding.inl
          (Topology.CWComplex.map m j q.down.val)) :=
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated_apply
      (cellPolyhedron S) S.polyhedron (cellMap S)
      (Topology.CWComplex.map m j q.down.val)
  exact Eq.trans hMap (L.snd m j q)

private def actualConeNextPolyhedronLabels {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) :
    Σ' κ : ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (MappingCylinder.coneComplex
          (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualNextPolyhedron S).Realization) m,
      ∀ (m : ℕ) (j : Topology.CWComplex.cell
          (Set.univ : Set (MappingCylinder.coneComplex
            (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization) m)
        (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
        actualWeakConeToNextPolyhedron X S i (Topology.CWComplex.map m j q.down.val) =
          Topology.CWComplex.map m (κ m j) q.down.val := by
  let L := PreAbstractSimplicialComplex.Realization.classicalCellEmbeddingOfRelabelInclusion
    (MappingCylinder.coneComplex (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices))
    (coneTag (cellPolyhedron S) i) (actualNextPolyhedron S)
    ((le_iSup (attachedBlock (cellPolyhedron S)) i).trans le_sup_right)
  refine ⟨L.fst, ?_⟩
  intro m j q
  simpa only [actualWeakConeToNextPolyhedron, ContinuousMap.comp_apply] using! L.snd m j q

private theorem actualCylinderToNextPolyhedron_closed {n : ℕ} (S : Stage X n) :
    IsClosedEmbedding (actualCylinderToNextPolyhedron X S) :=
  PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated_isClosedEmbedding
    (cellPolyhedron S) S.polyhedron (cellMap S)

private theorem actualWeakConeToNextPolyhedron_closed {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) : IsClosedEmbedding (actualWeakConeToNextPolyhedron X S i) := by
  dsimp only [actualWeakConeToNextPolyhedron]
  exact (Realization.isClosedEmbedding_inclusion
    ((le_iSup (attachedBlock (cellPolyhedron S)) i).trans le_sup_right)).comp
      (MappingCylinder.relabelHomeomorph
        (MappingCylinder.coneComplex (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices))
        (coneTag (cellPolyhedron S) i)).isClosedEmbedding

private theorem actualOrdinaryConeToNextPolyhedron_value {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n)
    (x : TopCat.cone (TopCat.of
      (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization)) :
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) ⟨i, x⟩ =
      actualWeakConeToNextPolyhedron X S i (actualOrdinaryConeHomeomorph S i x) := by
  let := cellFiniteFaces S i
  let := MappingCylinder.finiteFaces_domainComplex (cellPolyhedron S i) S.vertices
  have h := PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ScalarCone.scalarAssociated_ordinaryCone
    (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) i x
  apply Realization.ext
  calc
    _ = (smallOrdinaryConeAttachment (cellMap S i) x).point.map
        (coneTag (cellPolyhedron S) i) :=
      (congrArg Realization.point h).trans
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ScalarCone.scalarAssociated_point
          (cellPolyhedron S) S.polyhedron (cellMap S) i
            (smallOrdinaryConeAttachment (cellMap S i) x))
    _ = (actualOrdinaryConeHomeomorph S i x).point.map (coneTag (cellPolyhedron S) i) := by
      have hp := smallOrdinaryConeAttachment_point (cellMap S i) x
      simpa only [actualOrdinaryConeHomeomorph] using!
        congrArg (fun p => p.map (coneTag (cellPolyhedron S) i)) hp
    _ = (actualWeakConeToNextPolyhedron X S i (actualOrdinaryConeHomeomorph S i x)).point := by
      have hp := MappingCylinder.relabelMorphism_point
        (MappingCylinder.coneComplex (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices))
        (coneTag (W := S.vertices) (cellPolyhedron S) i) (actualOrdinaryConeHomeomorph S i x)
      simpa only [actualWeakConeToNextPolyhedron, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, Realization.inclusion_point, ← Homeomorph.coe_toEquiv,
        MappingCylinder.relabelHomeomorph, Equiv.coe_ofBijective,
        Equiv.ofBijective_apply] using! hp.symm


private def actualCylinderNextPolyhedronSubcomplex {n : ℕ} (S : Stage X n) :
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualNextPolyhedron S).Realization) := by
  let B := TopCat.of (smallFamilyComplex S).Realization
  let a := actualCylinderNextPolyhedronLabels X S
  let M : MatchingCharacteristicData (𝟙 B) (TopCat.ofHom (actualCylinderToNextPolyhedron X S)) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := a.fst
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => a.snd m j (ULift.up q) }
  exact matchingRightSubcomplex M (actualCylinderToNextPolyhedron_closed X S)

private def actualConeNextPolyhedronSubcomplex {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) :
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualNextPolyhedron S).Realization) := by
  let C := TopCat.of (MappingCylinder.coneComplex
    (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization
  let a := actualConeNextPolyhedronLabels X S i
  let M : MatchingCharacteristicData (𝟙 C) (TopCat.ofHom (actualWeakConeToNextPolyhedron X S i)) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := a.fst
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => a.snd m j (ULift.up q) }
  exact matchingRightSubcomplex M (actualWeakConeToNextPolyhedron_closed X S i)

private def actualNextPolyhedronCover {n : ℕ} (S : Stage X n) :
    Option (CellIndex (X := X) n) →
      Topology.CWComplex.Subcomplex (Set.univ : Set (actualNextPolyhedron S).Realization)
  | none => actualCylinderNextPolyhedronSubcomplex X S
  | some i => actualConeNextPolyhedronSubcomplex X S i

private theorem actualNextPolyhedronCover_covers {n : ℕ} (S : Stage X n) :
    (⋃ i, (actualNextPolyhedronCover X S i : Set (actualNextPolyhedron S).Realization)) = Set.univ := by
  have hcover : (Set.range (actualCylinderToNextPolyhedron X S) ∪
      ⋃ i, Set.range (fun x : TopCat.cone (TopCat.of
          (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization) =>
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
            (⟨i, x⟩ : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
              (cellPolyhedron S) S.vertices))) =
      (Set.univ : Set (actualNextPolyhedron S).Realization) := by
    simpa only [actualCylinderToNextPolyhedron] using!
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Geometry.associatedFamily_cover
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    have hy : y ∈ Set.range (actualCylinderToNextPolyhedron X S) ∪
        ⋃ i, Set.range (fun x : TopCat.cone (TopCat.of
            (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices).Realization) =>
          PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
            (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)
              (⟨i, x⟩ : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
                (cellPolyhedron S) S.vertices)) :=
      Eq.mpr (congrArg (fun T : Set (actualNextPolyhedron S).Realization => y ∈ T) hcover)
        (Set.mem_univ y)
    rcases hy with hy | hy
    · exact Set.mem_iUnion.mpr ⟨none, hy⟩
    · rcases Set.mem_iUnion.mp hy with ⟨i, x, hx⟩
      exact Set.mem_iUnion.mpr ⟨some i,
        ⟨actualOrdinaryConeHomeomorph S i x,
          (actualOrdinaryConeToNextPolyhedron_value X S i x).symm.trans hx⟩⟩

end ActualCommonSuccessorConstruction

end

/- Polyhedral successor labels.
Each cell belongs to a constructed cylinder/cone CW subcomplex by carrier
coverage and open-cell disjointness. Its label and complete disk equality
come from the constructed intermediate labels and endpoint transfer.
End injectivity proves label injectivity. No supplied label packet, end
inverse or characteristic-map/kappa-naturality equation is used. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualConeCharacteristic_topDisk {n : ℕ} (S : Stage X n)
    (i : CellIndex (X := X) n) (m : ℕ)
    (a : Topology.CWComplex.cell
      (Set.univ : Set (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) i
        ((actualOrdinaryConeHomeomorph S i).symm (Topology.CWComplex.map m a q.down.val)) =
      refinedTopConeDiskCharacteristic (W := S.vertices) (n + 1)
        (actualSubdivisions S i) m a q := by
  let e := originalDiskToCopiedConeComplex (W := S.vertices) (n + 1) (actualSubdivisions S i)
  let z := Topology.CWComplex.map
    (C := (Set.univ : Set (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization)) m a q.down.val
  let x := (actualOrdinaryConeHomeomorph S i).symm z
  let φ := refinedTopConeDiskCharacteristic (W := S.vertices) (n + 1)
    (actualSubdivisions S i) m a q
  have hOrd : actualOrdinaryConeHomeomorph S i x = z :=
    (actualOrdinaryConeHomeomorph S i).apply_symm_apply z
  have h₀ : actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) i x =
      e.symm z := by
    calc
      _ = actualConeDiskComparison S i x := (actualConeDiskComparison_value S i x).symm
      _ = e.symm (actualOrdinaryConeHomeomorph S i x) := rfl
      _ = e.symm z := congrArg e.symm hOrd
  have hφ : e φ = z := by
    simpa only using! refinedTopConeDiskCharacteristic_whole
      (W := S.vertices) (n + 1) (actualSubdivisions S i) m a q
  have h₁ : e.symm z = φ :=
    (congrArg e.symm hφ).symm.trans (e.symm_apply_apply φ)
  exact h₀.trans h₁

private theorem actualCylinderCell_to_successorDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (a : Topology.CWComplex.cell
      (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    (actualFiniteStages X (n + 1)).polyhedral
        (actualCylinderToNextPolyhedron X (actualFiniteStages X n)
          (Topology.CWComplex.map m a q.down.val)) =
      Topology.CWComplex.map m
        (actualFiniteSuccessorOldLabels X n D m
          (actualFiniteIntermediateFamilyLabels X n D m a)) q.down.val := by
  let S := actualFiniteStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  exact (actualPolyhedralSuccessorCollapse_cylinder S (Topology.CWComplex.map m a q.down.val)).trans
    ((congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S))
      (actualFiniteIntermediateFamilyDisk X n D m a q)).trans
        (actualFiniteSuccessorOldDisk X n D m (actualFiniteIntermediateFamilyLabels X n D m a) q))

private theorem actualConeCell_to_successorDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (i : CellIndex (X := X) n) (m : ℕ)
    (a : Topology.CWComplex.cell
      (Set.univ : Set (MappingCylinder.coneComplex
        (MappingCylinder.domainComplex (cellPolyhedron (actualFiniteStages X n) i)
          (actualFiniteStages X n).vertices)).Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    (actualFiniteStages X (n + 1)).polyhedral
        (actualWeakConeToNextPolyhedron X (actualFiniteStages X n) i
          (Topology.CWComplex.map m a q.down.val)) =
      Topology.CWComplex.map
        (C := (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n)))) m
        (topCellTransfer (A := smallIntermediate (actualFiniteStages X n))
          (W := (actualFiniteStages X n).vertices) (n + 1)
          (actualSubdivisions (actualFiniteStages X n)) i
          (actualFiniteCopiedDomainIntermediateLabels X n D i) m a) q.down.val := by
  let S := actualFiniteStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  let z := Topology.CWComplex.map
    (C := (Set.univ : Set (MappingCylinder.coneComplex
      (MappingCylinder.domainComplex (cellPolyhedron S i) S.vertices)).Realization)) m a q.down.val
  let x := (actualOrdinaryConeHomeomorph S i).symm z
  have hcone : actualWeakConeToNextPolyhedron X S i z =
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) ⟨i, x⟩ :=
    ((actualOrdinaryConeToNextPolyhedron_value X S i x).trans
      (congrArg (actualWeakConeToNextPolyhedron X S i)
        ((actualOrdinaryConeHomeomorph S i).apply_symm_apply z))).symm
  have hEnd : (actualFiniteStages X (n + 1)).polyhedral
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S) ⟨i, x⟩) =
      originalCylinderMap (n + 1) (smallSuccessorBoundary S) i
        (actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) i x, 1) :=
    actualPolyhedralSuccessorCollapse_cone S i x
  have hchar : actualConeToTopDisk (W := S.vertices) (n + 1) (actualSubdivisions S) i x =
      refinedTopConeDiskCharacteristic (W := S.vertices) (n + 1)
        (actualSubdivisions S i) m a q :=
    actualConeCharacteristic_topDisk X S i m a q
  have hTransfer : originalCylinderMap (n + 1) (smallSuccessorBoundary S) i
      (refinedTopConeDiskCharacteristic (W := S.vertices) (n + 1)
        (actualSubdivisions S i) m a q, 1) =
      Topology.CWComplex.map (C := (Set.univ : Set (actualSuccessorSpace S))) m
        (topCellTransfer (A := smallIntermediate S) (W := S.vertices) (n + 1)
          (actualSubdivisions S) i (actualFiniteCopiedDomainIntermediateLabels X n D i) m a)
        q.down.val := by
    change originalCylinderMap (n + 1) (smallSuccessorBoundary S) i
        (refinedTopConeDiskCharacteristic (W := S.vertices) (n + 1)
          (actualSubdivisions S i) m a q, 1) =
      refinedTubeCellPartialEquiv (A := smallIntermediate S) (W := S.vertices)
        (n + 1) (actualSubdivisions S) (smallSuccessorBoundary S) m
        (topCellTransfer (A := smallIntermediate S) (W := S.vertices) (n + 1)
          (actualSubdivisions S) i (actualFiniteCopiedDomainIntermediateLabels X n D i) m a)
        q.down.val
    exact (topCellTransfer_closed_characteristic (A := smallIntermediate S) (W := S.vertices)
      (n + 1) (actualSubdivisions S) i (smallSuccessorBoundary S)
      (actualFiniteCopiedDomainToIntermediate X n i)
      (actualFiniteCopiedDomainIntermediateLabels X n D i)
      (actualFiniteCopiedDomainIntermediateDisk X n D i)
      (actualFiniteTopBoundary_matches_copiedDomain X n i) m a q).symm
  exact (congrArg (actualFiniteStages X (n + 1)).polyhedral hcone).trans
    (hEnd.trans ((congrArg (fun t : (Topology.CWComplex.classicalCellDiskPair.{u} (n + 1)).fst =>
      originalCylinderMap (n + 1) (smallSuccessorBoundary S) i (t, 1)) hchar).trans hTransfer))

private theorem actualPolyhedralCell_has_successorLabel (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (j : Topology.CWComplex.cell
      (Set.univ : Set (actualNextPolyhedron (actualFiniteStages X n)).Realization) m) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∃ a : Topology.CWComplex.cell
        (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m,
      ∀ q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst,
        (actualFiniteStages X (n + 1)).polyhedral (Topology.CWComplex.map m j q.down.val) =
          Topology.CWComplex.map m a q.down.val := by
  let S := actualFiniteStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  obtain ⟨o, ho⟩ := cell_mem_some_cover_subcomplex (actualNextPolyhedronCover X S)
    (actualNextPolyhedronCover_covers X S) m j
  cases o with
  | none =>
      change j ∈ Set.range ((actualCylinderNextPolyhedronLabels X S).fst m) at ho
      rcases ho with ⟨a, ha⟩
      refine ⟨actualFiniteSuccessorOldLabels X n D m
        (actualFiniteIntermediateFamilyLabels X n D m a), ?_⟩
      intro q
      rw [← ha]
      exact (congrArg (actualFiniteStages X (n + 1)).polyhedral
        ((actualCylinderNextPolyhedronLabels X S).snd m a q).symm).trans
          (actualCylinderCell_to_successorDisk X n D m a q)
  | some i =>
      change j ∈ Set.range ((actualConeNextPolyhedronLabels X S i).fst m) at ho
      rcases ho with ⟨a, ha⟩
      let a' : Topology.CWComplex.cell (Set.univ : Set (actualSuccessorSpace S)) m :=
        topCellTransfer (A := smallIntermediate S) (W := S.vertices) (n + 1)
          (actualSubdivisions S) i (actualFiniteCopiedDomainIntermediateLabels X n D i) m a
      refine ⟨a', ?_⟩
      intro q
      rw [← ha]
      exact (congrArg (actualFiniteStages X (n + 1)).polyhedral
        ((actualConeNextPolyhedronLabels X S i).snd m a q).symm).trans
          (actualConeCell_to_successorDisk X n D i m a q)

private def actualFiniteSuccessorPolyhedralCell (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (j : Topology.CWComplex.cell
      (Set.univ : Set (actualNextPolyhedron (actualFiniteStages X n)).Realization) m) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    Topology.CWComplex.cell
      (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  exact Classical.choose (actualPolyhedralCell_has_successorLabel X n D m j)

private theorem actualFiniteSuccessorPolyhedralDisk (n : ℕ) (D : ActualFiniteClassicalData X n)
    (m : ℕ) (j : Topology.CWComplex.cell
      (Set.univ : Set (actualNextPolyhedron (actualFiniteStages X n)).Realization) m)
    (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    (actualFiniteStages X (n + 1)).polyhedral (Topology.CWComplex.map m j q.down.val) =
      Topology.CWComplex.map m (actualFiniteSuccessorPolyhedralCell X n D m j) q.down.val := by
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  exact Classical.choose_spec (actualPolyhedralCell_has_successorLabel X n D m j) q

private def actualFiniteSuccessorPolyhedralLabels (n : ℕ) (D : ActualFiniteClassicalData X n) :
    letI := D.cw
    letI := actualFiniteIntermediateCW X n D
    letI := actualFiniteSuccessorCW X n D
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (actualNextPolyhedron (actualFiniteStages X n)).Realization) m ↪
      Topology.CWComplex.cell
        (Set.univ : Set (actualSuccessorSpace (actualFiniteStages X n))) m := by
  let S := actualFiniteStages X n
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI : Topology.CWComplex (Set.univ : Set (actualNextPolyhedron S).Realization) := by
    change Topology.CWComplex (Set.univ : Set
      (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Cone.associatedFamily
        (cellPolyhedron S) S.polyhedron (cellMap S)).Realization)
    infer_instance
  letI : Topology.CWComplex (Set.univ : Set (actualSuccessorSpace S)) :=
    actualFiniteSuccessorCW X n D
  intro m
  exact
    ⟨actualFiniteSuccessorPolyhedralCell X n D m,
      @characteristic_labels_injective
        (actualNextPolyhedron S).Realization (actualSuccessorSpace S)
        (inferInstance : TopologicalSpace (actualNextPolyhedron S).Realization)
        (inferInstance : TopologicalSpace (actualSuccessorSpace S))
        (inferInstance : Topology.CWComplex (Set.univ : Set (actualNextPolyhedron S).Realization))
        (inferInstance : Topology.CWComplex (Set.univ : Set (actualSuccessorSpace S)))
        ((actualFiniteStages X (n + 1)).polyhedral :
          C((actualNextPolyhedron S).Realization, actualSuccessorSpace S))
        (actualFiniteStages_end_closed X (n + 1)).2.injective
        (actualFiniteSuccessorPolyhedralCell X n D)
        (actualFiniteSuccessorPolyhedralDisk X n D) m⟩

end ActualCommonSuccessorConstruction

end

/- Classical CW induction for the original-space finite stages.
The initializer and both successor label families are constructed.
The remaining numerical fields follow from the derived bounds.
No CW, matching, inverse or attaching-homotopy packet is supplied. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualSuccessorClassicalData (n : ℕ) (D : ActualFiniteClassicalData X n) :
    ActualFiniteClassicalData X (n + 1) := by
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  exact
    { cw := actualFiniteSuccessorCW X n D
      originalLabels := actualFiniteSuccessorOriginalLabels X n D
      originalDisk := actualFiniteSuccessorOriginalDisk X n D
      polyhedralLabels := actualFiniteSuccessorPolyhedralLabels X n D
      polyhedralDisk := actualFiniteSuccessorPolyhedralDisk X n D
      commonDimension := actualFiniteSuccessorCW_dimension X n D
      polyhedronFaceBound := actualNextPolyhedron_face_bound X n D }

private def actualFiniteClassicalStages : ∀ n : ℕ, ActualFiniteClassicalData X n :=
  Nat.rec (actualInitialClassicalData X) (fun n D => actualSuccessorClassicalData X n D)

private def actualFiniteStageCW (n : ℕ) :
    Topology.CWComplex (Set.univ : Set (actualFiniteStages X n).space) :=
  (actualFiniteClassicalStages X n).cw

private def actualFiniteStageIntermediateCW (n : ℕ) :
    Topology.CWComplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) :=
  actualFiniteIntermediateCW X n (actualFiniteClassicalStages X n)

private theorem actualFiniteStageCW_dimension (n : ℕ) :
    letI := actualFiniteStageCW X n
    ∀ m (j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m), m ≤ n + 1 :=
  (actualFiniteClassicalStages X n).commonDimension

private theorem actualFiniteStagePolyhedron_face_bound (n : ℕ)
    (a : Face (actualFiniteStages X n).polyhedron) : a.val.card ≤ n + 1 :=
  (actualFiniteClassicalStages X n).polyhedronFaceBound a

end ActualCommonSuccessorConstruction

end

/- Closed CW end subcomplexes after the original-space induction.
Original labels are the original degrees below the strict bound;
polyhedral labels are the canonical constructed end labels.
Both carriers are the constructed end maps. No CW/end packet is supplied. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47 Topology.CWComplex.MatchedAmalgam

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteOriginalEndSubcomplex (n : ℕ) :
    letI := actualFiniteStageCW X n
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X n).space) := by
  let D := actualFiniteClassicalStages X n
  letI := D.cw
  let S := actualFiniteStages X n
  let κ := D.originalLabels
  refine
    { carrier := Set.range S.original
      I := fun m => if hm : m < n + 1 then Set.range (κ m hm) else ∅
      closed' := (actualFiniteStages_end_closed X n).1.isClosed_range
      union' := ?_ }
  rw [Set.empty_union]
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨m, hmU⟩
    rcases Set.mem_iUnion.mp hmU with ⟨j, hjCell⟩
    by_cases hm : m < n + 1
    · have hj := j.property
      change j.val ∈ (if hs : m < n + 1 then Set.range (κ m hs) else ∅) at hj
      rw [dite_eq_left hm] at hj
      rcases hj with ⟨a, ha⟩
      have hcell : z ∈ Topology.CWComplex.openCell (C := (Set.univ : Set S.space)) m (κ m hm a) := by
        rw [ha]
        exact hjCell
      rcases hcell with ⟨x, hx, hxz⟩
      let q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst :=
        ULift.up ⟨x, Metric.ball_subset_closedBall hx⟩
      exact ⟨originalLowerDiskToSkeleton (n + 1) m hm a q, (D.originalDisk m hm a q).trans hxz⟩
    · have hj := j.property
      change j.val ∈ (if hs : m < n + 1 then Set.range (κ m hs) else ∅) at hj
      rw [dite_eq_right hm] at hj
      exact hj.elim
  · rintro ⟨x, rfl⟩
    let E := Topology.CWComplex.skeletonLT (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞)
    have hx : x.val ∈ (E : Set X) := x.property
    have hE : (⋃ m, ⋃ j : E.I m,
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j.val) = (E : Set X) :=
      Topology.CWComplex.Subcomplex.union (E := E)
    have hxU : x.val ∈ (⋃ m, ⋃ j : E.I m,
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j.val) :=
      Eq.mpr (congrArg (fun T : Set X => x.val ∈ T) hE) hx
    rcases Set.mem_iUnion.mp hxU with ⟨m, hmU⟩
    rcases Set.mem_iUnion.mp hmU with ⟨j, hjCell⟩
    have hm : m < n + 1 := by
      have hmn : (m : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
        simpa only [E, Topology.CWComplex.skeletonLT_I, Set.mem_ofPred_eq] using! j.property
      exact_mod_cast hmn
    rcases hjCell with ⟨a, ha, hax⟩
    let q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst :=
      ULift.up ⟨a, Metric.ball_subset_closedBall ha⟩
    have hqx : originalLowerDiskToSkeleton (n + 1) m hm j.val q = x := by
      apply Subtype.ext
      change Topology.CWComplex.characteristicDiskMap (X := X) m j.val q = x.val
      rw [Topology.CWComplex.characteristicDiskMap_apply]
      simpa only [Topology.CWComplex.map_def] using! hax
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨⟨κ m hm j.val, ?_⟩, a, ha, ?_⟩⟩
    · change κ m hm j.val ∈ (if hs : m < n + 1 then Set.range (κ m hs) else ∅)
      rw [dite_eq_left hm]
      exact Set.mem_range_self j.val
    · simpa only [Topology.CWComplex.map_def] using!
        (D.originalDisk m hm j.val q).symm.trans (congrArg S.original hqx)

private def actualFinitePolyhedralEndSubcomplex (n : ℕ) :
    letI := actualFiniteStageCW X n
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X n).space) := by
  let D := actualFiniteClassicalStages X n
  letI := D.cw
  let S := actualFiniteStages X n
  let P := TopCat.of S.polyhedron.Realization
  let M : MatchingCharacteristicData (𝟙 P) (TopCat.ofHom S.polyhedral) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := D.polyhedralLabels
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => D.polyhedralDisk m j (ULift.up q) }
  exact matchingRightSubcomplex M (actualFiniteStages_end_closed X n).2

private theorem actualFiniteOriginalEndSubcomplex_carrier (n : ℕ) :
    letI := actualFiniteStageCW X n
    (actualFiniteOriginalEndSubcomplex X n : Set (actualFiniteStages X n).space) =
      Set.range (actualFiniteStages X n).original := by
  let := actualFiniteStageCW X n
  rfl

private theorem actualFiniteOriginalEndSubcomplex_labels (n m : ℕ) :
    letI := actualFiniteStageCW X n
    (actualFiniteOriginalEndSubcomplex X n).I m =
      if hm : m < n + 1 then Set.range ((actualFiniteClassicalStages X n).originalLabels m hm)
      else ∅ := by
  let := actualFiniteStageCW X n
  rfl

private theorem actualFinitePolyhedralEndSubcomplex_carrier (n : ℕ) :
    letI := actualFiniteStageCW X n
    (actualFinitePolyhedralEndSubcomplex X n : Set (actualFiniteStages X n).space) =
      Set.range (actualFiniteStages X n).polyhedral := by
  let := actualFiniteStageCW X n
  rfl

private theorem actualFinitePolyhedralEndSubcomplex_labels (n m : ℕ) :
    letI := actualFiniteStageCW X n
    (actualFinitePolyhedralEndSubcomplex X n).I m =
      Set.range ((actualFiniteClassicalStages X n).polyhedralLabels m) := by
  let := actualFiniteStageCW X n
  rfl

end ActualCommonSuccessorConstruction

end

/- Common-stage transitions as closed CW inclusions.
The transition is the old-to-intermediate-to-tube composite. Both
constructed cell tags intertwine complete closed disks. The CW induction
supplies the source and target structures, and the inclusion lemmas
supply closedness. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47 Topology.CWComplex.MatchedAmalgam

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualFiniteCWTransitionLabels (n : ℕ) :
    letI := actualFiniteStageCW X n
    letI := actualFiniteStageCW X (n + 1)
    ∀ m, Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X (n + 1)).space) m := by
  let D := actualFiniteClassicalStages X n
  letI := D.cw
  letI := actualFiniteIntermediateCW X n D
  letI := actualFiniteSuccessorCW X n D
  intro m
  exact (actualFiniteIntermediateOldLabels X n D m).trans (actualFiniteSuccessorOldLabels X n D m)

private theorem actualFiniteCWTransitionDisk (n m : ℕ) :
    letI := actualFiniteStageCW X n
    letI := actualFiniteStageCW X (n + 1)
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m)
      (q : (Topology.CWComplex.classicalCellDiskPair.{u} m).fst),
      actualCommonStageTransition X (actualFiniteStages X n) (Topology.CWComplex.map m j q.down.val) =
        Topology.CWComplex.map m (actualFiniteCWTransitionLabels X n m j) q.down.val := by
  let S := actualFiniteStages X n
  let D := actualFiniteClassicalStages X n
  let := D.cw
  let := actualFiniteIntermediateCW X n D
  let := actualFiniteSuccessorCW X n D
  intro j q
  exact (congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S))
    (actualFiniteIntermediateOldDisk X n D m j q)).trans
      (actualFiniteSuccessorOldDisk X n D m (actualFiniteIntermediateOldLabels X n D m j) q)

private def actualFiniteCWTransitionSubcomplex (n : ℕ) :
    letI := actualFiniteStageCW X (n + 1)
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X (n + 1)).space) := by
  letI := actualFiniteStageCW X n
  letI := actualFiniteStageCW X (n + 1)
  let S := actualFiniteStages X n
  letI : Topology.CWComplex (Set.univ : Set S.space) := actualFiniteStageCW X n
  letI : Topology.CWComplex (Set.univ : Set (actualTopologicalSuccessor X S).space) :=
    actualFiniteStageCW X (n + 1)
  let M : MatchingCharacteristicData (𝟙 S.space) (TopCat.ofHom (actualCommonStageTransition X S)) :=
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := actualFiniteCWTransitionLabels X n
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m j q => actualFiniteCWTransitionDisk X n m j (ULift.up q) }
  exact matchingRightSubcomplex M (actualCommonStageTransition_closed S)

private theorem actualFiniteCWTransitionSubcomplex_carrier (n : ℕ) :
    letI := actualFiniteStageCW X (n + 1)
    (actualFiniteCWTransitionSubcomplex X n : Set (actualFiniteStages X (n + 1)).space) =
      Set.range (actualCommonStageTransition X (actualFiniteStages X n)) := by
  let := actualFiniteStageCW X (n + 1)
  rfl

private theorem actualFiniteCWTransitionSubcomplex_labels (n m : ℕ) :
    letI := actualFiniteStageCW X (n + 1)
    (actualFiniteCWTransitionSubcomplex X n).I m = Set.range (actualFiniteCWTransitionLabels X n m) := by
  let := actualFiniteStageCW X (n + 1)
  rfl

end ActualCommonSuccessorConstruction

end

/- Intermediate and old-stage retraction coordinates.
Each retraction is the constructed composite. Presentation isomorphisms
identify the same retained-A attachment. The equations derive old/end
preimages; no intersection witness is supplied. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open ActualRefinedTubeCharacteristicConstruction47 StationaryAttachmentRetractionConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualOriginalSuccessorRetraction_intermediate {n : ℕ} (S : Stage X n)
    (a : smallIntermediate S) :
    (actualOriginalSuccessorCollapse S).retract
        (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a) =
      skeletonTransition X (n + 1) ((actualIntermediateOriginalCollapse S).retract a) := by
  change (isPushout_skeletonAttachment X (n + 1)).isoPushout.inv
      (attachmentRetraction (sphereSumToSkeleton X (n + 1)) (sphereSumToDiskSum X (n + 1))
        (actualIntermediateOriginalCollapse S).include (actualIntermediateOriginalCollapse S).retract
        (actualIntermediateOriginalCollapse S).retraction
        ((actualOriginalRetainedEndIso S).hom
          (unitDiskEndRetraction (n + 1) (smallSuccessorBoundary S) false
            (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a)))) = _
  rw [unitDiskEndRetraction_old]
  have hin : (actualOriginalRetainedEndIso S).hom
      (diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) false a) =
      retainedOld (sphereSumToSkeleton X (n + 1)) (sphereSumToDiskSum X (n + 1))
        (actualIntermediateOriginalCollapse S).include a := by
    simpa only [actualOriginalRetainedEndIso, ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualOriginalRetainedEnd_square S).inl_isoPushout_hom a
  rw [hin, attachmentRetraction_old]
  simpa only [ConcreteCategory.comp_apply] using!
    ConcreteCategory.congr_hom (isPushout_skeletonAttachment X (n + 1)).inl_isoPushout_inv
      ((actualIntermediateOriginalCollapse S).retract a)

private theorem actualPolyhedralSuccessorRetraction_intermediate {n : ℕ} (S : Stage X n)
    (a : smallIntermediate S) :
    (actualPolyhedralSuccessorCollapse S).retract
        (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a) =
      PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) ((actualIntermediateFamilyCollapse S).retract a) := by
  change (actualReducedPolyhedralEnd_square S).isoPushout.inv
      (attachmentRetraction (actualPolyhedralSphereMap S)
        (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
        (actualIntermediateFamilyCollapse S).include (actualIntermediateFamilyCollapse S).retract
        (actualIntermediateFamilyCollapse S).retraction
        ((actualPolyhedralRetainedEndIso S).hom
          (unitDiskEndRetraction (n + 1) (smallSuccessorBoundary S) true
            (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a)))) = _
  rw [unitDiskEndRetraction_old]
  have hin : (actualPolyhedralRetainedEndIso S).hom
      (diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary S)) true a) =
      retainedOld (actualPolyhedralSphereMap S)
        (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
        (actualIntermediateFamilyCollapse S).include a := by
    simpa only [actualPolyhedralRetainedEndIso, ConcreteCategory.comp_apply] using!
      ConcreteCategory.congr_hom (actualPolyhedralRetainedEnd_square S).inl_isoPushout_hom a
  rw [hin, attachmentRetraction_old]
  simpa only [ConcreteCategory.comp_apply] using!
    ConcreteCategory.congr_hom (actualReducedPolyhedralEnd_square S).inl_isoPushout_inv
      ((actualIntermediateFamilyCollapse S).retract a)

private theorem actualOriginalSuccessorRetraction_old {n : ℕ} (S : Stage X n) (z : S.space) :
    (actualTopologicalSuccessor X S).retractOriginal (actualCommonStageTransition X S z) =
      skeletonTransition X (n + 1) (S.retractOriginal z) := by
  have h := actualOriginalSuccessorRetraction_intermediate S (smallIntermediateOld S z)
  change (actualTopologicalSuccessor X S).retractOriginal (actualCommonStageTransition X S z) =
    skeletonTransition X (n + 1)
      (S.retractOriginal (intermediateToOld S (smallIntermediateOld S z))) at h
  rw [intermediateToOld_old] at h
  exact h

private theorem actualPolyhedralSuccessorRetraction_old {n : ℕ} (S : Stage X n) (z : S.space) :
    (actualTopologicalSuccessor X S).retractPolyhedral (actualCommonStageTransition X S z) =
      actualPolyhedralStageTransition X S (S.retractPolyhedral z) := by
  have h := actualPolyhedralSuccessorRetraction_intermediate S (smallIntermediateOld S z)
  change (actualTopologicalSuccessor X S).retractPolyhedral (actualCommonStageTransition X S z) =
    PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
      (cellPolyhedron S) S.polyhedron (cellMap S)
      (intermediateToFamily S (smallIntermediateOld S z)) at h
  rw [intermediateToFamily_old] at h
  exact h

end ActualCommonSuccessorConstruction

end

/- Higher end-preimage equations.
The retraction coordinates follow from the constructed composite.
Included/retracted identities and the old-end forward equations imply
the preimage formulas. No intersection or preimage is assumed. -/

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open ActualRefinedTubeCharacteristicConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualIntermediate_preimage_originalSuccessor {n : ℕ} (S : Stage X n) :
    (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) ⁻¹'
        Set.range (actualOriginalSuccessorCollapse S).include =
      Set.range (smallIntermediateOriginal S) := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    let r := (actualIntermediateOriginalCollapse S).retract
    have hxx : x = skeletonTransition X (n + 1) (r a) :=
      (finiteCollapse_retraction (actualOriginalSuccessorCollapse S) x).symm.trans
        ((congrArg (actualOriginalSuccessorCollapse S).retract hx).trans
          (actualOriginalSuccessorRetraction_intermediate S a))
    have hpoint : oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)
        (smallIntermediateOriginal S (r a)) = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a :=
      (actualOriginalSuccessorCollapse_old S (r a)).symm.trans
        ((congrArg (actualOriginalSuccessorCollapse S).include hxx.symm).trans hx)
    exact ⟨r a, (oldIntoTubeSpace_closed (n + 1) (smallSuccessorBoundary S)).injective hpoint⟩
  · rintro ⟨x, rfl⟩
    exact ⟨skeletonTransition X (n + 1) x, actualOriginalSuccessorCollapse_old S x⟩

private theorem actualIntermediate_preimage_polyhedralSuccessor {n : ℕ} (S : Stage X n) :
    (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) ⁻¹'
        Set.range (actualPolyhedralSuccessorCollapse S).include =
      Set.range (smallIntermediateFamily S) := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    let r := (actualIntermediateFamilyCollapse S).retract
    have hxx : x = PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
        (cellPolyhedron S) S.polyhedron (cellMap S) (r a) :=
      (finiteCollapse_retraction (actualPolyhedralSuccessorCollapse S) x).symm.trans
        ((congrArg (actualPolyhedralSuccessorCollapse S).retract hx).trans
          (actualPolyhedralSuccessorRetraction_intermediate S a))
    have hpoint : oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)
        (smallIntermediateFamily S (r a)) = oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a :=
      (actualPolyhedralSuccessorCollapse_cylinder S (r a)).symm.trans
        ((congrArg (actualPolyhedralSuccessorCollapse S).include hxx.symm).trans hx)
    exact ⟨r a, (oldIntoTubeSpace_closed (n + 1) (smallSuccessorBoundary S)).injective hpoint⟩
  · rintro ⟨b, rfl⟩
    exact ⟨PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
      (cellPolyhedron S) S.polyhedron (cellMap S) b, actualPolyhedralSuccessorCollapse_cylinder S b⟩

private theorem actualCommonStageTransition_preimage_original {n : ℕ} (S : Stage X n) :
    (actualCommonStageTransition X S) ⁻¹' Set.range (actualTopologicalSuccessor X S).original =
      Set.range S.original := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    have hxx : x = skeletonTransition X (n + 1) (S.retractOriginal z) :=
      ((actualTopologicalSuccessor X S).original_retraction x).symm.trans
        ((congrArg (actualTopologicalSuccessor X S).retractOriginal hx).trans
          (actualOriginalSuccessorRetraction_old S z))
    have hpoint : actualCommonStageTransition X S (S.original (S.retractOriginal z)) =
        actualCommonStageTransition X S z :=
      (actualCommonStageTransition_original X S (S.retractOriginal z)).symm.trans
        ((congrArg (actualTopologicalSuccessor X S).original hxx.symm).trans hx)
    exact ⟨S.retractOriginal z, (actualCommonStageTransition_closed S).injective hpoint⟩
  · rintro ⟨x, rfl⟩
    exact ⟨skeletonTransition X (n + 1) x, actualCommonStageTransition_original X S x⟩

private theorem actualCommonStageTransition_preimage_polyhedral {n : ℕ} (S : Stage X n) :
    (actualCommonStageTransition X S) ⁻¹' Set.range (actualTopologicalSuccessor X S).polyhedral =
      Set.range S.polyhedral := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    have hxx : x = actualPolyhedralStageTransition X S (S.retractPolyhedral z) :=
      ((actualTopologicalSuccessor X S).polyhedral_retraction x).symm.trans
        ((congrArg (actualTopologicalSuccessor X S).retractPolyhedral hx).trans
          (actualPolyhedralSuccessorRetraction_old S z))
    have hpoint : actualCommonStageTransition X S (S.polyhedral (S.retractPolyhedral z)) =
        actualCommonStageTransition X S z :=
      (actualCommonStageTransition_polyhedral X S (S.retractPolyhedral z)).symm.trans
        ((congrArg (actualTopologicalSuccessor X S).polyhedral hxx.symm).trans hx)
    exact ⟨S.retractPolyhedral z, (actualCommonStageTransition_closed S).injective hpoint⟩
  · rintro ⟨p, rfl⟩
    exact ⟨actualPolyhedralStageTransition X S p, actualCommonStageTransition_polyhedral X S p⟩

end ActualCommonSuccessorConstruction

end

/- Intersection of the retained-A bottom and top.
Disk-end pushout coverage gives old A or a complete endpoint disk.
Off-side sigma injectivity keeps distinct endpoint heights distinct.
The attaching homotopy is arbitrary; no CW or intersection data is supplied.
Empty and infinite families and dimension zero are included. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace ActualRefinedTubeCharacteristicConstruction47

open ActualCommonSuccessorConstruction

variable {I : Type u} {A : TopCat.{u}}

private theorem retainedDiskEnd_point_old_or_disk (d : ℕ)
    (H : C(sideSum (I := I) d, A)) (top : Bool) (x : unitDiskEndSpace d H top) :
    (∃ a : A, unitDiskEndInclude d H top x = oldIntoTubeSpace d H a) ∨
      ∃ (i : I) (q : (Topology.CWComplex.classicalCellDiskPair.{u} d).fst),
        unitDiskEndInclude d H top x = originalCylinderMap d H i (q, unitSelectedHeight top) := by
  let sq := IsPushout.of_hasPushout
    (TopCat.ofHom (endpointBoundary d (normalizedLiteralBoundary d H) top))
    (TopCat.ofHom (endpointSphereInclusion (J := I) d))
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with
    ⟨a, rfl⟩ | ⟨⟨i, q⟩, rfl⟩
  · exact Or.inl ⟨a, unitDiskEndInclude_old d H top a⟩
  · exact Or.inr ⟨i, q, unitDiskEndInclude_disk d H top i q⟩

private theorem retainedBottomTopRanges_intersection (d : ℕ)
    (H : C(sideSum (I := I) d, A)) :
    Set.range (unitDiskEndInclude d H false) ∩ Set.range (unitDiskEndInclude d H true) =
      Set.range (oldIntoTubeSpace d H) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rcases retainedDiskEnd_point_old_or_disk d H false x with ⟨a, ha⟩ | ⟨i, q, hq⟩
    · exact ⟨a, ha.symm.trans hx⟩
    · rcases retainedDiskEnd_point_old_or_disk d H true y with ⟨b, hb⟩ | ⟨j, r, hr⟩
      · exact ⟨b, hb.symm.trans hy⟩
      · have heq : originalCylinderMap d H i (q, 0) = originalCylinderMap d H j (r, 1) :=
          hq.symm.trans (hx.trans (hy.symm.trans hr))
        by_cases hqs : q ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map
        · rcases hqs with ⟨s, rfl⟩
          exact ⟨H ⟨i, (s, 0)⟩,
            (originalCylinderMap_whole_side d H i s 0).symm.trans (hq.symm.trans hx)⟩
        · by_cases hrs : r ∈ Set.range (Topology.CWComplex.classicalCellDiskPair.{u} d).map
          · rcases hrs with ⟨s, rfl⟩
            exact ⟨H ⟨j, (s, 1)⟩,
              (originalCylinderMap_whole_side d H j s 1).symm.trans (hr.symm.trans hy)⟩
          · let p : Σ _ : I, cylinderOffSide.{u} d := ⟨i, ⟨(q, 0), hqs⟩⟩
            let t : Σ _ : I, cylinderOffSide.{u} d := ⟨j, ⟨(r, 1), hrs⟩⟩
            have hpt : p = t := (wholeOffSideCylinderMap_isEmbedding d H).injective heq
            have ht : (0 : unitInterval) = 1 := congrArg (fun v => v.snd.val.2) hpt
            exact (zero_ne_one (congrArg Subtype.val ht)).elim
  · rintro ⟨a, rfl⟩
    exact ⟨⟨diskEndOld d (normalizedLiteralBoundary d H) false a,
      unitDiskEndInclude_old d H false a⟩,
      ⟨diskEndOld d (normalizedLiteralBoundary d H) true a,
        unitDiskEndInclude_old d H true a⟩⟩

end ActualRefinedTubeCharacteristicConstruction47

namespace ActualCommonSuccessorConstruction

open ActualRefinedTubeCharacteristicConstruction47
open Topology.CWComplex

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualOriginalSuccessorRange_subset_retainedBottom {n : ℕ} (S : Stage X n) :
    Set.range (actualOriginalSuccessorCollapse S).include ⊆
      Set.range (unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) false) := by
  rintro z ⟨x, rfl⟩
  refine ⟨(actualOriginalRetainedEndIso S).inv
    ((actualOriginalLiftedCollapse S).include
      ((isPushout_skeletonAttachment X (n + 1)).isoPushout.hom x)), ?_⟩
  rfl

private theorem actualPolyhedralSuccessorRange_subset_retainedTop {n : ℕ} (S : Stage X n) :
    Set.range (actualPolyhedralSuccessorCollapse S).include ⊆
      Set.range (unitDiskEndInclude (n + 1) (smallSuccessorBoundary S) true) := by
  rintro z ⟨x, rfl⟩
  refine ⟨(actualPolyhedralRetainedEndIso S).inv
    ((actualPolyhedralLiftedCollapse S).include ((actualReducedPolyhedralEnd_square S).isoPushout.hom x)), ?_⟩
  rfl

end ActualCommonSuccessorConstruction

end

/- Finite-stage end intersection.
The selected ranges lie in the retained-A bottom and top ends, whose
intersection is old A. The intermediate preimages and small-family
pushout reduce the claim to the previous original/polyhedral intersection.
No prior intersection witness is supplied. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private theorem actualSuccessorEndRanges_intersection {n : ℕ} (S : Stage X n) :
    Set.range (actualTopologicalSuccessor X S).original ∩
        Set.range (actualTopologicalSuccessor X S).polyhedral =
      (actualCommonStageTransition X S) '' (Set.range S.original ∩ Set.range S.polyhedral) := by
  ext z
  constructor
  · rintro ⟨hzO, hzP⟩
    have hzOld : z ∈ Set.range (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) := by
      rw [← retainedBottomTopRanges_intersection (n + 1) (smallSuccessorBoundary S)]
      exact ⟨actualOriginalSuccessorRange_subset_retainedBottom S hzO,
        actualPolyhedralSuccessorRange_subset_retainedTop S hzP⟩
    rcases hzOld with ⟨a, haz⟩
    have haO : a ∈ Set.range (smallIntermediateOriginal S) := by
      rw [← actualIntermediate_preimage_originalSuccessor S]
      change oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a ∈
        Set.range (actualOriginalSuccessorCollapse S).include
      rw [haz]
      exact hzO
    have haP : a ∈ Set.range (smallIntermediateFamily S) := by
      rw [← actualIntermediate_preimage_polyhedralSuccessor S]
      change oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S) a ∈
        Set.range (actualPolyhedralSuccessorCollapse S).include
      rw [haz]
      exact hzP
    rcases haO with ⟨x, hxa⟩
    rcases haP with ⟨b, hba⟩
    have hcross : smallIntermediateOld S (S.original x) = smallIntermediateFamily S b :=
      hxa.trans hba.symm
    have hpoly : Function.Injective S.polyhedral := by
      intro p q hpq
      exact (S.polyhedral_retraction p).symm.trans
        ((congrArg S.retractPolyhedral hpq).trans (S.polyhedral_retraction q))
    let sq := IsPushout.of_hasPushout (TopCat.ofHom S.polyhedral) (TopCat.ofHom (smallFamilyOld S))
    obtain ⟨p, hp, _⟩ :=
      (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
        (sq.map (forget TopCat)).isColimit hpoly (S.original x) b).mp hcross
    refine ⟨S.original x, ⟨⟨x, rfl⟩, ⟨p, hp⟩⟩, ?_⟩
    exact (congrArg (oldIntoTubeSpace (n + 1) (smallSuccessorBoundary S)) hxa).trans haz
  · rintro ⟨y, ⟨⟨x, hx⟩, ⟨p, hp⟩⟩, hyz⟩
    constructor
    · refine ⟨Topology.CWComplex.skeletonTransition X (n + 1) x, ?_⟩
      exact (actualCommonStageTransition_original X S x).trans
        ((congrArg (actualCommonStageTransition X S) hx).trans hyz)
    · refine ⟨actualPolyhedralStageTransition X S p, ?_⟩
      exact (actualCommonStageTransition_polyhedral X S p).trans
        ((congrArg (actualCommonStageTransition X S) hp).trans hyz)

private theorem actualFiniteStages_original_preimage
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    (actualCommonStageTransition X (actualFiniteStages X n)) ⁻¹'
        Set.range (actualFiniteStages X (n + 1)).original =
      Set.range (actualFiniteStages X n).original :=
  actualCommonStageTransition_preimage_original (actualFiniteStages X n)

private theorem actualFiniteStages_polyhedral_preimage
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    (actualCommonStageTransition X (actualFiniteStages X n)) ⁻¹'
        Set.range (actualFiniteStages X (n + 1)).polyhedral =
      Set.range (actualFiniteStages X n).polyhedral :=
  actualCommonStageTransition_preimage_polyhedral (actualFiniteStages X n)

private theorem actualFiniteStages_end_intersection
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Set.range (actualFiniteStages X (n + 1)).original ∩
        Set.range (actualFiniteStages X (n + 1)).polyhedral =
      (actualCommonStageTransition X (actualFiniteStages X n)) ''
        (Set.range (actualFiniteStages X n).original ∩ Set.range (actualFiniteStages X n).polyhedral) :=
  actualSuccessorEndRanges_intersection (actualFiniteStages X n)

end ActualCommonSuccessorConstruction

end

/- Accumulated image of the common zero stage.
Both initial end ranges are the complete original zero skeleton.
The successor intersection recurrence identifies every finite end
intersection with this initial-stage image. -/

noncomputable section

open CategoryTheory Topology

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def actualCommonZeroToStage :
    ∀ n : ℕ, C((actualFiniteStages X 0).space, (actualFiniteStages X n).space) :=
  Nat.rec (ContinuousMap.id _) (fun n j =>
    (actualCommonStageTransition X (actualFiniteStages X n)).comp j)

private theorem actualInitialEndRanges_intersection :
    Set.range (actualFiniteStages X 0).original ∩ Set.range (actualFiniteStages X 0).polyhedral =
      Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    exact ⟨⟨z, rfl⟩,
      ⟨(Topology.CWComplex.commonZeroSkeleton X).homeomorph.symm z,
        (Topology.CWComplex.commonZeroSkeleton X).homeomorph.apply_symm_apply z⟩⟩

private theorem actualFiniteEndIntersection_zeroImage (n : ℕ) :
    Set.range (actualFiniteStages X n).original ∩ Set.range (actualFiniteStages X n).polyhedral =
      Set.range (actualCommonZeroToStage X n) := by
  induction n with
  | zero =>
      rw [actualInitialEndRanges_intersection]
      ext z
      constructor
      · intro _
        exact ⟨z, rfl⟩
      · intro _
        exact Set.mem_univ z
  | succ n ih =>
      rw [actualFiniteStages_end_intersection X n, ih]
      ext z
      constructor
      · rintro ⟨y, ⟨x, hxy⟩, hyz⟩
        exact ⟨x, (congrArg (actualCommonStageTransition X (actualFiniteStages X n)) hxy).trans hyz⟩
      · rintro ⟨x, rfl⟩
        exact ⟨actualCommonZeroToStage X n x, ⟨x, rfl⟩, rfl⟩

private theorem actualCommonZeroToStage_closed (n : ℕ) :
    IsClosedEmbedding (actualCommonZeroToStage X n) := by
  induction n with
  | zero => exact IsClosedEmbedding.id
  | succ n ih =>
      exact (actualCommonStageTransition_closed (actualFiniteStages X n)).comp ih

end ActualCommonSuccessorConstruction

end

/- Finite common system for the original space.
The objects and end/retraction/homotopy maps come from the constructed
recursion. CW and closed subcomplex data follow from its induction,
T2 from the separation lemmas, and range formulas from the preimage
equations. Both elementary families fix the entire intermediate A.
Finite end families retain their selected-end and original-zero point
equations. No final CW, inverse or intersection witness is supplied. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47
open scoped unitInterval

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private structure ActualCommonSuccessorCWSystem where
  classical : ∀ n : ℕ, ActualFiniteClassicalData X n
  commonT2 : ∀ n : ℕ, T2Space (actualFiniteStages X n).space
  intermediateCW : ∀ n : ℕ,
    Topology.CWComplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n)))
  intermediateT2 : ∀ n : ℕ, T2Space (smallIntermediate (actualFiniteStages X n))
  intermediateOld (n : ℕ) :
    letI := intermediateCW n
    Topology.CWComplex.Subcomplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n)))
  intermediateOldLabels (n : ℕ) :
    letI := (classical n).cw
    letI := intermediateCW n
    ∀ m, Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m
  intermediateOld_carrier (n : ℕ) :
    letI := intermediateCW n
    (intermediateOld n : Set (smallIntermediate (actualFiniteStages X n))) =
      Set.range (smallIntermediateOld (actualFiniteStages X n))
  intermediateOld_labels (n m : ℕ) :
    letI := (classical n).cw
    letI := intermediateCW n
    (intermediateOld n).I m = Set.range (intermediateOldLabels n m)
  intermediateOld_characteristicDiskMap (n m : ℕ) :
    letI := (classical n).cw
    letI := intermediateCW n
    ∀ j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m,
      Topology.CWComplex.characteristicDiskMap (X := (actualFiniteStages X n).space) m j ≫
          TopCat.ofHom (smallIntermediateOld (actualFiniteStages X n)) =
        Topology.CWComplex.characteristicDiskMap (X := smallIntermediate (actualFiniteStages X n)) m
          (intermediateOldLabels n m j)
  intermediateFamily (n : ℕ) :
    letI := intermediateCW n
    Topology.CWComplex.Subcomplex (Set.univ : Set (smallIntermediate (actualFiniteStages X n)))
  intermediateFamilyLabels (n : ℕ) :
    letI := intermediateCW n
    ∀ m, Topology.CWComplex.cell
        (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m ↪
      Topology.CWComplex.cell (Set.univ : Set (smallIntermediate (actualFiniteStages X n))) m
  intermediateFamily_carrier (n : ℕ) :
    letI := intermediateCW n
    (intermediateFamily n : Set (smallIntermediate (actualFiniteStages X n))) =
      Set.range (smallIntermediateFamily (actualFiniteStages X n))
  intermediateFamily_labels (n m : ℕ) :
    letI := (classical n).cw
    letI := intermediateCW n
    (intermediateFamily n).I m = Set.range (intermediateFamilyLabels n m)
  intermediateFamily_characteristicDiskMap (n m : ℕ) :
    letI := (classical n).cw
    letI := intermediateCW n
    ∀ j : Topology.CWComplex.cell
      (Set.univ : Set (smallFamilyComplex (actualFiniteStages X n)).Realization) m,
      Topology.CWComplex.characteristicDiskMap
          (X := TopCat.of (smallFamilyComplex (actualFiniteStages X n)).Realization) m j ≫
          TopCat.ofHom (smallIntermediateFamily (actualFiniteStages X n)) =
        Topology.CWComplex.characteristicDiskMap (X := smallIntermediate (actualFiniteStages X n)) m
          (intermediateFamilyLabels n m j)
  originalEnd (n : ℕ) :
    letI := (classical n).cw
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X n).space)
  originalEnd_carrier (n : ℕ) :
    letI := (classical n).cw
    (originalEnd n : Set (actualFiniteStages X n).space) = Set.range (actualFiniteStages X n).original
  originalEnd_labels (n m : ℕ) :
    letI := (classical n).cw
    (originalEnd n).I m =
      if hm : m < n + 1 then Set.range ((classical n).originalLabels m hm) else ∅
  polyhedralEnd (n : ℕ) :
    letI := (classical n).cw
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X n).space)
  polyhedralEnd_carrier (n : ℕ) :
    letI := (classical n).cw
    (polyhedralEnd n : Set (actualFiniteStages X n).space) = Set.range (actualFiniteStages X n).polyhedral
  polyhedralEnd_labels (n m : ℕ) :
    letI := (classical n).cw
    (polyhedralEnd n).I m = Set.range ((classical n).polyhedralLabels m)
  oldStage (n : ℕ) :
    letI := (classical (n + 1)).cw
    Topology.CWComplex.Subcomplex (Set.univ : Set (actualFiniteStages X (n + 1)).space)
  oldStageLabels (n : ℕ) :
    letI := (classical n).cw
    letI := (classical (n + 1)).cw
    ∀ m, Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m ↪
      Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X (n + 1)).space) m
  oldStage_labels (n m : ℕ) :
    letI := (classical n).cw
    letI := (classical (n + 1)).cw
    (oldStage n).I m = Set.range (oldStageLabels n m)
  oldStage_characteristicDiskMap (n m : ℕ) :
    letI := (classical n).cw
    letI := (classical (n + 1)).cw
    ∀ j : Topology.CWComplex.cell (Set.univ : Set (actualFiniteStages X n).space) m,
      Topology.CWComplex.characteristicDiskMap (X := (actualFiniteStages X n).space) m j ≫
          TopCat.ofHom (actualCommonStageTransition X (actualFiniteStages X n)) =
        Topology.CWComplex.characteristicDiskMap (X := (actualFiniteStages X (n + 1)).space) m
          (oldStageLabels n m j)
  oldStage_carrier (n : ℕ) :
    letI := (classical (n + 1)).cw
    (oldStage n : Set (actualFiniteStages X (n + 1)).space) =
      Set.range (actualCommonStageTransition X (actualFiniteStages X n))
  original_preimage (n : ℕ) :
    (actualCommonStageTransition X (actualFiniteStages X n)) ⁻¹'
        Set.range (actualFiniteStages X (n + 1)).original = Set.range (actualFiniteStages X n).original
  polyhedral_preimage (n : ℕ) :
    (actualCommonStageTransition X (actualFiniteStages X n)) ⁻¹'
        Set.range (actualFiniteStages X (n + 1)).polyhedral = Set.range (actualFiniteStages X n).polyhedral
  end_intersection (n : ℕ) :
    Set.range (actualFiniteStages X (n + 1)).original ∩
        Set.range (actualFiniteStages X (n + 1)).polyhedral =
      (actualCommonStageTransition X (actualFiniteStages X n)) ''
        (Set.range (actualFiniteStages X n).original ∩ Set.range (actualFiniteStages X n).polyhedral)
  zero_intersection (n : ℕ) :
    Set.range (actualFiniteStages X n).original ∩ Set.range (actualFiniteStages X n).polyhedral =
      Set.range (actualCommonZeroToStage X n)
  elementaryOriginal (n : ℕ) :
    FiniteCollapse (actualSuccessorSpace (actualFiniteStages X n))
      (unitDiskEndSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) false)
  elementaryPolyhedral (n : ℕ) :
    FiniteCollapse (actualSuccessorSpace (actualFiniteStages X n))
      (unitDiskEndSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) true)
  elementaryOriginal_fixed_old (n : ℕ) (t : unitInterval)
    (a : smallIntermediate (actualFiniteStages X n)) :
    (elementaryOriginal n).deformation
        (t, oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) a) =
      oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) a
  elementaryPolyhedral_fixed_old (n : ℕ) (t : unitInterval)
    (a : smallIntermediate (actualFiniteStages X n)) :
    (elementaryPolyhedral n).deformation
        (t, oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) a) =
      oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) a
  original_fixed_end (n : ℕ) (t : unitInterval)
    (x : Topology.CWComplex.skeletonTop X (n + 1)) :
    (actualFiniteStages X n).originalDeformation (t, (actualFiniteStages X n).original x) =
      (actualFiniteStages X n).original x
  polyhedral_fixed_end (n : ℕ) (t : unitInterval)
    (p : (actualFiniteStages X n).polyhedron.Realization) :
    (actualFiniteStages X n).polyhedralDeformation (t, (actualFiniteStages X n).polyhedral p) =
      (actualFiniteStages X n).polyhedral p
  original_zero_fixed (j : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (n : ℕ) (t : unitInterval) :
    (actualFiniteStages X n).originalDeformation
        (t, (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original) =
      (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original
  polyhedral_zero_fixed (j : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (n : ℕ) (t : unitInterval) :
    (actualFiniteStages X n).polyhedralDeformation
        (t, (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original) =
      (actualFiniteStages X n).original (actualSharedZeroPoint X j n).original
  original_zero_value (j : Topology.CWComplex.cell (Set.univ : Set X) 0) (n : ℕ) :
    (actualSharedZeroPoint X j n).original.val = Topology.CWComplex.map 0 j (0 : Fin 0 → ℝ)

private def actualCommonSuccessorCWSystem : ActualCommonSuccessorCWSystem X where
  classical := actualFiniteClassicalStages X
  commonT2 := actualFiniteStagesT2Space X
  intermediateCW := actualFiniteStageIntermediateCW X
  intermediateT2 := actualFiniteIntermediateT2Space X
  intermediateOld := fun n => actualFiniteIntermediateOldSubcomplex X n (actualFiniteClassicalStages X n)
  intermediateOldLabels := fun n =>
    actualFiniteIntermediateOldLabels X n (actualFiniteClassicalStages X n)
  intermediateOld_carrier := fun n =>
    actualFiniteIntermediateOldSubcomplex_carrier X n (actualFiniteClassicalStages X n)
  intermediateOld_labels := fun n m =>
    actualFiniteIntermediateOldSubcomplex_labels X n (actualFiniteClassicalStages X n) m
  intermediateOld_characteristicDiskMap := by
    intro n m j
    ext q
    simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
      actualFiniteIntermediateOldDisk X n (actualFiniteClassicalStages X n) m j q
  intermediateFamily := fun n =>
    actualFiniteIntermediateFamilySubcomplex X n (actualFiniteClassicalStages X n)
  intermediateFamilyLabels := fun n =>
    actualFiniteIntermediateFamilyLabels X n (actualFiniteClassicalStages X n)
  intermediateFamily_carrier := fun n =>
    actualFiniteIntermediateFamilySubcomplex_carrier X n (actualFiniteClassicalStages X n)
  intermediateFamily_labels := fun n m =>
    actualFiniteIntermediateFamilySubcomplex_labels X n (actualFiniteClassicalStages X n) m
  intermediateFamily_characteristicDiskMap := by
    intro n m j
    ext q
    simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
      actualFiniteIntermediateFamilyDisk X n (actualFiniteClassicalStages X n) m j q
  originalEnd := actualFiniteOriginalEndSubcomplex X
  originalEnd_carrier := actualFiniteOriginalEndSubcomplex_carrier X
  originalEnd_labels := actualFiniteOriginalEndSubcomplex_labels X
  polyhedralEnd := actualFinitePolyhedralEndSubcomplex X
  polyhedralEnd_carrier := actualFinitePolyhedralEndSubcomplex_carrier X
  polyhedralEnd_labels := actualFinitePolyhedralEndSubcomplex_labels X
  oldStage := actualFiniteCWTransitionSubcomplex X
  oldStageLabels := actualFiniteCWTransitionLabels X
  oldStage_labels := actualFiniteCWTransitionSubcomplex_labels X
  oldStage_characteristicDiskMap := by
    intro n m j
    ext q
    simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
      actualFiniteCWTransitionDisk X n m j q
  oldStage_carrier := actualFiniteCWTransitionSubcomplex_carrier X
  original_preimage := actualFiniteStages_original_preimage X
  polyhedral_preimage := actualFiniteStages_polyhedral_preimage X
  end_intersection := actualFiniteStages_end_intersection X
  zero_intersection := actualFiniteEndIntersection_zeroImage X
  elementaryOriginal := fun n => elementaryTubeCollapse (n + 1)
    (smallSuccessorBoundary (actualFiniteStages X n)) false
  elementaryPolyhedral := fun n => elementaryTubeCollapse (n + 1)
    (smallSuccessorBoundary (actualFiniteStages X n)) true
  elementaryOriginal_fixed_old := fun n t a => unitDiskEndRelativeHomotopy_old_fixed
    (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) false t a
  elementaryPolyhedral_fixed_old := fun n t a => unitDiskEndRelativeHomotopy_old_fixed
    (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) true t a
  original_fixed_end := actualFiniteOriginalEnd_stationary X
  polyhedral_fixed_end := actualFinitePolyhedralEnd_stationary X
  original_zero_fixed := actualSharedZeroPoint_original_fixed X
  polyhedral_zero_fixed := actualSharedZeroPoint_polyhedral_fixed X
  original_zero_value := actualSharedZeroPoint_original_value X

end ActualCommonSuccessorConstruction

end

/- Public finite-stage data. All fields use original X and public types;
the private Stage alias does not occur in this interface. -/

public section

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- A constructed finite common stage, with both actual ends and their
whole characteristic maps. Its space, CW structure and inverses are output data. -/
structure CommonSuccessorStageData (n : ℕ) where
  /-- The label type of the stage's simplicial complex `polyhedron`. -/
  vertices : Type u
  /-- The simplicial complex whose realization is the polyhedral end of the stage. -/
  polyhedron : PreAbstractSimplicialComplex vertices
  /-- The stage space, containing both ends. -/
  space : TopCat.{u}
  /-- The CW structure on `space`. -/
  cw : CWComplex (Set.univ : Set space)
  hausdorff : T2Space space
  /-- The original end: the closed embedding (`original_closed`) into `space` of
  `skeletonTop X (n + 1)`, the cells of `X` of dimension below `n + 1`. -/
  original : C(skeletonTop X (n + 1), space)
  /-- The polyhedral end: the closed embedding (`polyhedral_closed`) of the realization of
  `polyhedron` into `space`. -/
  polyhedral : C(polyhedron.Realization, space)
  /-- A retraction of `space` onto the original end (`original_retraction`). -/
  retractOriginal : C(space, skeletonTop X (n + 1))
  /-- A retraction of `space` onto the polyhedral end (`polyhedral_retraction`). -/
  retractPolyhedral : C(space, polyhedron.Realization)
  original_retraction : ∀ x, retractOriginal (original x) = x
  polyhedral_retraction : ∀ p, retractPolyhedral (polyhedral p) = p
  /-- A homotopy from the identity of `space` to `original ∘ retractOriginal`, fixing the
  original end. -/
  originalDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id space)
    (original.comp retractOriginal) (Set.range original)
  /-- A homotopy from the identity of `space` to `polyhedral ∘ retractPolyhedral`, fixing the
  polyhedral end. -/
  polyhedralDeformation : ContinuousMap.HomotopyRel (ContinuousMap.id space)
    (polyhedral.comp retractPolyhedral) (Set.range polyhedral)
  original_closed : IsClosedEmbedding original
  polyhedral_closed : IsClosedEmbedding polyhedral
  /-- The characteristic map of each `m`-cell of `X` with `m < n + 1`, as a map from the closed
  `m`-disk into `skeletonTop X (n + 1)` (`originalDiskLift_value`). -/
  originalDiskLift : ∀ m, m < n + 1 →
    cell (Set.univ : Set X) m → ((classicalCellDiskPair.{u} m).fst ⟶ skeletonTop X (n + 1))
  originalDiskLift_value : ∀ (m : ℕ) (hm : m < n + 1) (j : cell (Set.univ : Set X) m)
    (q : (classicalCellDiskPair.{u} m).fst),
    (originalDiskLift m hm j q).val = map (C := (Set.univ : Set X)) m j q.down.val
  /-- Sends each `m`-cell of `X` with `m < n + 1` to the `m`-cell of `space` whose characteristic
  map is `originalDiskLift` followed by `original` (`original_characteristicDiskMap`). -/
  originalLabels :
    letI := cw
    ∀ m, m < n + 1 → cell (Set.univ : Set X) m ↪ cell (Set.univ : Set space) m
  original_characteristicDiskMap :
    letI := cw
    ∀ (m : ℕ) (hm : m < n + 1) (j : cell (Set.univ : Set X) m),
      originalDiskLift m hm j ≫ TopCat.ofHom original =
        characteristicDiskMap (X := space) m (originalLabels m hm j)
  /-- Sends each `m`-cell of the realization of `polyhedron` to the `m`-cell of `space` whose
  characteristic map is its own followed by `polyhedral` (`polyhedral_characteristicDiskMap`). -/
  polyhedralLabels :
    letI := cw
    ∀ m, cell (Set.univ : Set polyhedron.Realization) m ↪ cell (Set.univ : Set space) m
  polyhedral_characteristicDiskMap :
    letI := cw
    ∀ (m : ℕ) (j : cell (Set.univ : Set polyhedron.Realization) m),
      characteristicDiskMap (X := TopCat.of polyhedron.Realization) m j ≫ TopCat.ofHom polyhedral =
        characteristicDiskMap (X := space) m (polyhedralLabels m j)
  commonDimension :
    letI := cw
    ∀ m (j : cell (Set.univ : Set space) m), m ≤ n + 1
  polyhedronFaceBound : ∀ a : Face polyhedron, a.val.card ≤ n + 1

end Topology.CWComplex

end

/- Public common-successor system data. Every carrier, map, CW structure,
approximation and homotopy is constructed output data. No private stage
alias, inverse or CW packet is an input to commonSuccessorSystem. -/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped unitInterval

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- The constructed finite common CW system for the original CW space.
The intermediate pieces, both closed CW ends and old-stage characteristic
maps are included explicitly with all higher intersection dictionaries. -/
structure CommonSuccessorSystemData where
  /-- The finite common stages, one for each `n`. -/
  stages : ∀ n : ℕ, CommonSuccessorStageData X n
  /-- A homeomorphism from `skeletonTop X 1`, the `0`-cells of `X`, to the stage-`0` space; it is
  the stage-`0` original end (`initial_original`). -/
  initialOriginalHomeomorph : skeletonTop X 1 ≃ₜ (stages 0).space
  initial_original : (stages 0).original = (initialOriginalHomeomorph : C(_, _))
  /-- Identifies the stage-`0` labels with the `0`-cells of `X`; the stage-`0` faces are exactly
  the corresponding singletons (`initialFaces`). -/
  initialVertices : (stages 0).vertices ≃ cell (Set.univ : Set X) 0
  initialFaces : ∀ s : Finset (stages 0).vertices,
    s ∈ (stages 0).polyhedron ↔ ∃ j, s = {initialVertices.symm j}
  initialSingleton_mem : ∀ j, {initialVertices.symm j} ∈ (stages 0).polyhedron
  initial_whole_original_fixed : ∀ t z, (stages 0).originalDeformation (t, z) = z
  initial_whole_polyhedral_fixed : ∀ t z, (stages 0).polyhedralDeformation (t, z) = z
  /-- A CW structure on each `skeletonTop X (n + 1)`. -/
  originalSkeletonCW : ∀ n, CWComplex (Set.univ : Set (skeletonTop X (n + 1)))
  /-- A homeomorphism from the realization of `SphereTriangulation.complex (n + 1)` to the
  boundary sphere of the closed `(n + 1)`-disk, given by `SphereTriangulation.sphereHomeomorph`
  (`sphereComparison_value`). -/
  sphereComparison : ∀ n,
    (SphereTriangulation.complex (n + 1)).Realization ≃ₜ (classicalCellDiskPair.{u} (n + 1)).snd
  sphereComparison_value : ∀ n x,
    (sphereComparison n x).down.val = (SphereTriangulation.sphereHomeomorph (n + 1) x).val
  /-- For each `(n + 1)`-cell, the number of barycentric subdivisions of the sphere triangulation
  used to approximate its attaching map. -/
  subdivisions : ∀ n, cell (Set.univ : Set X) (n + 1) → ℕ
  /-- The attaching map of the `(n + 1)`-cell `i`, read on the sphere triangulation through
  `sphereComparison` and moved to the stage-`n` polyhedral end by `original` and
  `retractPolyhedral` (`polyBoundary_value`). -/
  polyBoundary : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    C((SphereTriangulation.complex (n + 1)).Realization, (stages n).polyhedron.Realization)
  polyBoundary_value : ∀ n i x,
    polyBoundary n i x = (stages n).retractPolyhedral
      ((stages n).original (characteristicSphereToSkeleton (n + 1) i (sphereComparison n x)))
  /-- A simplicial map from the `subdivisions n i`-fold subdivided sphere triangulation to the
  stage-`n` polyhedron, a simplicial approximation of `polyBoundary n i`
  (`approximationSupport`). -/
  approximatingMap : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    Morphism (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))
      (stages n).polyhedron
  /-- The straight-line homotopy (`approximationPoint`) from `polyBoundary n i`, precomposed with
  the subdivision homeomorphism, to the realization of `approximatingMap n i`. -/
  approximationHomotopy : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    ContinuousMap.Homotopy
      ((polyBoundary n i).comp
        (subdivisionRealizationMap (SphereTriangulation.complex (n + 1)) (subdivisions n i)))
      (approximatingMap n i).realization
  approximationSupport : ∀ n i x,
    ((approximatingMap n i).realization x).point.weights.support ⊆
      (polyBoundary n i (iteratedHomeomorph (SphereTriangulation.complex (n + 1))
        (subdivisions n i) x)).point.weights.support
  approximationPoint : ∀ n i t x,
    (approximationHomotopy n i (t, x)).point = Realization.segmentPoint t
      (polyBoundary n i (iteratedHomeomorph (SphereTriangulation.complex (n + 1))
        (subdivisions n i) x)).point ((approximatingMap n i).realization x).point
  approximationVerticesFixed : ∀ n i
    (a : Vertex (SphereTriangulation.complex (n + 1)))
    (c : Vertex (stages n).polyhedron),
    polyBoundary n i (Realization.vertex (SphereTriangulation.complex (n + 1)) a.val a.property) =
        Realization.vertex (stages n).polyhedron c.val c.property →
      (approximatingMap n i).vertexMap
          (persistentVertex (SphereTriangulation.complex (n + 1)) (subdivisions n i) a) = c ∧
        ∀ t : unitInterval,
          approximationHomotopy n i
              (t, Realization.vertex
                (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))
                (persistentVertex (SphereTriangulation.complex (n + 1)) (subdivisions n i) a).val
                (persistentVertex (SphereTriangulation.complex (n + 1)) (subdivisions n i) a).property) =
            polyBoundary n i
              (Realization.vertex (SphereTriangulation.complex (n + 1)) a.val a.property)
  /-- The label type of `family n`. -/
  familyVertices : ℕ → Type u
  /-- The stage-`n` family complex: it contains the stage-`n` polyhedron (`familyOld`) and a copy
  of each subdivided attaching sphere (`familyCopied`), and retracts onto the polyhedron. -/
  family : ∀ n, PreAbstractSimplicialComplex (familyVertices n)
  /-- The closed embedding (`familyOld_closed`) of the stage-`n` polyhedron into `family n`. -/
  familyOld : ∀ n, C((stages n).polyhedron.Realization, (family n).Realization)
  familyOld_closed : ∀ n, IsClosedEmbedding (familyOld n)
  /-- A retraction of `family n` onto the stage-`n` polyhedron (`familyRetraction_old`); on each
  copied sphere it is the approximating map (`familyRetraction_copied`). -/
  familyRetraction : ∀ n, C((family n).Realization, (stages n).polyhedron.Realization)
  familyRetraction_old : ∀ n p, familyRetraction n (familyOld n p) = p
  /-- A homotopy from the identity of `family n` to `familyOld n ∘ familyRetraction n`, fixing
  the image of `familyOld n`. -/
  familyDeformation : ∀ n,
    ContinuousMap.HomotopyRel (ContinuousMap.id (family n).Realization)
      ((familyOld n).comp (familyRetraction n)) (Set.range (familyOld n))
  /-- A homeomorphism from the realization of the barycentric subdivision of the subdivided sphere
  triangulation of the cell `i` to the boundary sphere of the closed `(n + 1)`-disk. -/
  copiedSphere : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    (barycentricSubdivision
      (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))).Realization ≃ₜ
        (classicalCellDiskPair.{u} (n + 1)).snd
  /-- The closed embedding (`familyCopied_closed`) of the copied sphere of the cell `i` into
  `family n`. -/
  familyCopied : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    C((barycentricSubdivision
      (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))).Realization,
      (family n).Realization)
  familyCopied_closed : ∀ n i, IsClosedEmbedding (familyCopied n i)
  familyCopied_old_disjoint : ∀ n i,
    Disjoint (Set.range (familyCopied n i)) (Set.range (familyOld n))
  familyCopied_distinct_disjoint : ∀ n i j, i ≠ j →
    Disjoint (Set.range (familyCopied n i)) (Set.range (familyCopied n j))
  familyRetraction_copied : ∀ n i x,
    familyRetraction n (familyCopied n i x) = (approximatingMap n i).realization
      (barycentricHomeomorph
        (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i)) x)
  /-- The stage-`n` intermediate space: `family n` glued to the stage-`n` space along the
  polyhedral end (`intermediate_isPushout`). -/
  intermediate : ℕ → TopCat.{u}
  /-- The CW structure on `intermediate n`. -/
  intermediateCW : ∀ n, CWComplex (Set.univ : Set (intermediate n))
  intermediateT2 : ∀ n, T2Space (intermediate n)
  /-- The closed embedding (`oldToIntermediate_closed`) of the stage-`n` space into
  `intermediate n`, a leg of `intermediate_isPushout`. -/
  oldToIntermediate : ∀ n, C((stages n).space, intermediate n)
  /-- The closed embedding (`familyToIntermediate_closed`) of `family n` into `intermediate n`, a
  leg of `intermediate_isPushout`. -/
  familyToIntermediate : ∀ n, C((family n).Realization, intermediate n)
  oldToIntermediate_closed : ∀ n, IsClosedEmbedding (oldToIntermediate n)
  familyToIntermediate_closed : ∀ n, IsClosedEmbedding (familyToIntermediate n)
  intermediate_range_intersection : ∀ n,
    Set.range (oldToIntermediate n) ∩ Set.range (familyToIntermediate n) =
      Set.range ((oldToIntermediate n).comp (stages n).polyhedral)
  intermediate_isPushout : ∀ n,
    IsPushout (TopCat.ofHom (stages n).polyhedral) (TopCat.ofHom (familyOld n))
      (TopCat.ofHom (oldToIntermediate n)) (TopCat.ofHom (familyToIntermediate n))
  /-- The subcomplex of `intermediate n` carried by the image of `oldToIntermediate n`
  (`intermediateOld_carrier`). -/
  intermediateOld (n : ℕ) :
    letI := intermediateCW n
    Subcomplex (Set.univ : Set (intermediate n))
  /-- Sends each `m`-cell of the stage-`n` space to the cell of `intermediate n` whose
  characteristic map is its own followed by `oldToIntermediate n`
  (`intermediateOld_characteristicDiskMap`). -/
  intermediateOldLabels (n : ℕ) :
    letI := (stages n).cw
    letI := intermediateCW n
    ∀ m, cell (Set.univ : Set (stages n).space) m ↪ cell (Set.univ : Set (intermediate n)) m
  intermediateOld_carrier (n : ℕ) :
    letI := intermediateCW n
    (intermediateOld n : Set (intermediate n)) = Set.range (oldToIntermediate n)
  intermediateOld_labels (n m : ℕ) :
    letI := (stages n).cw
    letI := intermediateCW n
    (intermediateOld n).I m = Set.range (intermediateOldLabels n m)
  intermediateOld_characteristicDiskMap (n m : ℕ) :
    letI := (stages n).cw
    letI := intermediateCW n
    ∀ j : cell (Set.univ : Set (stages n).space) m,
      characteristicDiskMap (X := (stages n).space) m j ≫ TopCat.ofHom (oldToIntermediate n) =
        characteristicDiskMap (X := intermediate n) m (intermediateOldLabels n m j)
  /-- The subcomplex of `intermediate n` carried by the image of `familyToIntermediate n`
  (`intermediateFamily_carrier`). -/
  intermediateFamily (n : ℕ) :
    letI := intermediateCW n
    Subcomplex (Set.univ : Set (intermediate n))
  /-- Sends each `m`-cell of the realization of `family n` to the cell of `intermediate n` whose
  characteristic map is its own followed by `familyToIntermediate n`
  (`intermediateFamily_characteristicDiskMap`). -/
  intermediateFamilyLabels (n : ℕ) :
    letI := intermediateCW n
    ∀ m, cell (Set.univ : Set (family n).Realization) m ↪ cell (Set.univ : Set (intermediate n)) m
  intermediateFamily_carrier (n : ℕ) :
    letI := intermediateCW n
    (intermediateFamily n : Set (intermediate n)) = Set.range (familyToIntermediate n)
  intermediateFamily_labels (n m : ℕ) :
    letI := intermediateCW n
    (intermediateFamily n).I m = Set.range (intermediateFamilyLabels n m)
  intermediateFamily_characteristicDiskMap (n m : ℕ) :
    letI := intermediateCW n
    ∀ j : cell (Set.univ : Set (family n).Realization) m,
      characteristicDiskMap (X := TopCat.of (family n).Realization) m j ≫
          TopCat.ofHom (familyToIntermediate n) =
        characteristicDiskMap (X := intermediate n) m (intermediateFamilyLabels n m j)
  /-- The tube attaching map into `intermediate n`: on the summand of the `(n + 1)`-cell `i` it is
  the original attaching map of `i` at time `0` (`attaching_zero`) and the copied sphere of `i`
  at time `1` (`attaching_one`). -/
  attaching : ∀ n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).snd × unitInterval),
      intermediate n)
  attaching_zero : ∀ n i s,
    attaching n ⟨i, (s, 0)⟩ = oldToIntermediate n
      ((stages n).original (characteristicSphereToSkeleton (n + 1) i s))
  attaching_one : ∀ n i s,
    attaching n ⟨i, (s, 1)⟩ = familyToIntermediate n
      (familyCopied n i ((copiedSphere n i).symm s))
  /-- The boundary inclusion of each sphere-times-interval summand into the matching
  disk-times-interval summand (`sideInclusion_value`). -/
  sideInclusion : ∀ n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).snd × unitInterval),
      (Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).fst × unitInterval))
  sideInclusion_value : ∀ n i s t,
    sideInclusion n ⟨i, (s, t)⟩ = ⟨i, ((classicalCellDiskPair.{u} (n + 1)).map s, t)⟩
  /-- The closed embedding (`intermediateToCommon_closed`) of `intermediate n` into the
  stage-`(n + 1)` space, a leg of `tube_isPushout`. -/
  intermediateToCommon : ∀ n, C(intermediate n, (stages (n + 1)).space)
  intermediateToCommon_closed : ∀ n, IsClosedEmbedding (intermediateToCommon n)
  /-- The tubes: the map from the disk-times-interval summands into the stage-`(n + 1)` space, a
  leg of `tube_isPushout`; at time `0` it is the original characteristic map
  (`original_disk_end`). -/
  cylinders : ∀ n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).fst × unitInterval),
      (stages (n + 1)).space)
  tube_isPushout : ∀ n,
    IsPushout (TopCat.ofHom (attaching n)) (TopCat.ofHom (sideInclusion n))
      (TopCat.ofHom (intermediateToCommon n)) (TopCat.ofHom (cylinders n))
  original_disk_end : ∀ n i q,
    (stages (n + 1)).original (characteristicDiskToSkeleton (n + 1) i q) =
      cylinders n ⟨i, (q, 0)⟩
  /-- The closed embedding (`familyToNext_closed`) of `family n` into the stage-`(n + 1)`
  polyhedron, compatible with `intermediateToCommon` (`polyhedral_cylinder_end`). -/
  familyToNext : ∀ n, C((family n).Realization, (stages (n + 1)).polyhedron.Realization)
  familyToNext_closed : ∀ n, IsClosedEmbedding (familyToNext n)
  polyhedral_cylinder_end : ∀ n b,
    (stages (n + 1)).polyhedral (familyToNext n b) =
      intermediateToCommon n (familyToIntermediate n b)
  /-- A homeomorphism from the topological cone on the copied domain of the cell `i` (the
  barycentric subdivision of its subdivided sphere triangulation) to the closed `(n + 1)`-disk. -/
  coneDiskComparison : ∀ n (i : cell (Set.univ : Set X) (n + 1)),
    TopCat.cone (TopCat.of (MappingCylinder.domainComplex
      (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))
      (stages n).vertices).Realization) ≃ₜ (classicalCellDiskPair.{u} (n + 1)).fst
  /-- The map from these cones into the stage-`(n + 1)` polyhedron; it meets the tubes at time
  `1` (`polyhedral_cone_end`). -/
  conesToNext : ∀ n,
    C((Σ i : cell (Set.univ : Set X) (n + 1),
      TopCat.cone (TopCat.of (MappingCylinder.domainComplex
        (subdivisionIter (SphereTriangulation.complex (n + 1)) (subdivisions n i))
        (stages n).vertices).Realization)), (stages (n + 1)).polyhedron.Realization)
  polyhedral_cone_end : ∀ n i q,
    (stages (n + 1)).polyhedral (conesToNext n ⟨i, q⟩) =
      cylinders n ⟨i, (coneDiskComparison n i q, 1)⟩
  /-- The copied spheres in `family n`: `familyCopied` after the inverse of `copiedSphere`
  (`familySphere_value`). -/
  familySphere : ∀ n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).snd),
      (family n).Realization)
  familySphere_value : ∀ n i s,
    familySphere n ⟨i, s⟩ = familyCopied n i ((copiedSphere n i).symm s)
  /-- The disks in the stage-`(n + 1)` polyhedron: `conesToNext` after the inverse of
  `coneDiskComparison` (`polyhedralDisks_value`). -/
  polyhedralDisks : ∀ n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).fst),
      (stages (n + 1)).polyhedron.Realization)
  polyhedralDisks_value : ∀ n i q,
    polyhedralDisks n ⟨i, q⟩ = conesToNext n ⟨i, (coneDiskComparison n i).symm q⟩
  polyhedral_isPushout : ∀ n,
    IsPushout (TopCat.ofHom (familySphere n)) (sphereSumToDiskSum X (n + 1))
      (TopCat.ofHom (familyToNext n)) (TopCat.ofHom (polyhedralDisks n))
  /-- The closed embedding (`transition_closed`) of the stage-`n` space into the stage-`(n + 1)`
  space, equal to `intermediateToCommon n ∘ oldToIntermediate n` (`transition_formula`). -/
  transition : ∀ n, C((stages n).space, (stages (n + 1)).space)
  transition_closed : ∀ n, IsClosedEmbedding (transition n)
  transition_formula : ∀ n, transition n = (intermediateToCommon n).comp (oldToIntermediate n)
  /-- The closed embedding (`polyhedralTransition_closed`) of the stage-`n` polyhedron into the
  stage-`(n + 1)` polyhedron, compatible with `transition` (`transition_polyhedral`). -/
  polyhedralTransition : ∀ n,
    C((stages n).polyhedron.Realization, (stages (n + 1)).polyhedron.Realization)
  polyhedralTransition_closed : ∀ n, IsClosedEmbedding (polyhedralTransition n)
  transition_original : ∀ n x,
    (stages (n + 1)).original (skeletonTransition X (n + 1) x) = transition n ((stages n).original x)
  transition_polyhedral : ∀ n p,
    (stages (n + 1)).polyhedral (polyhedralTransition n p) = transition n ((stages n).polyhedral p)
  /-- The subcomplex of the stage-`(n + 1)` space carried by the image of `transition n`
  (`oldStage_carrier`). -/
  oldStage (n : ℕ) :
    letI := (stages (n + 1)).cw
    Subcomplex (Set.univ : Set (stages (n + 1)).space)
  /-- Sends each `m`-cell of the stage-`n` space to the cell of the stage-`(n + 1)` space whose
  characteristic map is its own followed by `transition n` (`oldStage_characteristicDiskMap`). -/
  oldStageLabels (n : ℕ) :
    letI := (stages n).cw
    letI := (stages (n + 1)).cw
    ∀ m, cell (Set.univ : Set (stages n).space) m ↪ cell (Set.univ : Set (stages (n + 1)).space) m
  oldStage_carrier (n : ℕ) :
    letI := (stages (n + 1)).cw
    (oldStage n : Set (stages (n + 1)).space) = Set.range (transition n)
  oldStage_labels (n m : ℕ) :
    letI := (stages n).cw
    letI := (stages (n + 1)).cw
    (oldStage n).I m = Set.range (oldStageLabels n m)
  oldStage_characteristicDiskMap (n m : ℕ) :
    letI := (stages n).cw
    letI := (stages (n + 1)).cw
    ∀ j : cell (Set.univ : Set (stages n).space) m,
      characteristicDiskMap (X := (stages n).space) m j ≫ TopCat.ofHom (transition n) =
        characteristicDiskMap (X := (stages (n + 1)).space) m (oldStageLabels n m j)
  /-- The original end as a subcomplex of the stage-`n` space (`originalEnd_carrier`,
  `originalEnd_labels`). -/
  originalEnd (n : ℕ) :
    letI := (stages n).cw
    Subcomplex (Set.univ : Set (stages n).space)
  originalEnd_carrier (n : ℕ) :
    letI := (stages n).cw
    (originalEnd n : Set (stages n).space) = Set.range (stages n).original
  originalEnd_labels (n m : ℕ) :
    letI := (stages n).cw
    (originalEnd n).I m = if hm : m < n + 1 then Set.range ((stages n).originalLabels m hm) else ∅
  /-- The polyhedral end as a subcomplex of the stage-`n` space (`polyhedralEnd_carrier`,
  `polyhedralEnd_labels`). -/
  polyhedralEnd (n : ℕ) :
    letI := (stages n).cw
    Subcomplex (Set.univ : Set (stages n).space)
  polyhedralEnd_carrier (n : ℕ) :
    letI := (stages n).cw
    (polyhedralEnd n : Set (stages n).space) = Set.range (stages n).polyhedral
  polyhedralEnd_labels (n m : ℕ) :
    letI := (stages n).cw
    (polyhedralEnd n).I m = Set.range ((stages n).polyhedralLabels m)
  original_preimage : ∀ n,
    (transition n) ⁻¹' Set.range (stages (n + 1)).original = Set.range (stages n).original
  polyhedral_preimage : ∀ n,
    (transition n) ⁻¹' Set.range (stages (n + 1)).polyhedral = Set.range (stages n).polyhedral
  end_intersection : ∀ n,
    Set.range (stages (n + 1)).original ∩ Set.range (stages (n + 1)).polyhedral =
      (transition n) '' (Set.range (stages n).original ∩ Set.range (stages n).polyhedral)
  /-- The composite of the transitions from stage `0` to stage `n` (`initialToStage_zero`,
  `initialToStage_succ`). -/
  initialToStage : ∀ n, C((stages 0).space, (stages n).space)
  initialToStage_zero : initialToStage 0 = ContinuousMap.id (stages 0).space
  initialToStage_succ : ∀ n, initialToStage (n + 1) = (transition n).comp (initialToStage n)
  initialToStage_closed : ∀ n, IsClosedEmbedding (initialToStage n)
  zero_intersection : ∀ n,
    Set.range (stages n).original ∩ Set.range (stages n).polyhedral = Set.range (initialToStage n)
  /-- `intermediate n` with closed `(n + 1)`-disks attached along `elementaryBoundary top n`
  (`elementary_isPushout`): at the original end of the tubes if `top = false`, at the
  polyhedral end if `top = true`. -/
  elementarySpace : Bool → ℕ → TopCat.{u}
  /-- The attaching map at the `top` end of the tubes: `attaching` at time `1` if `top`, else at
  time `0` (`elementaryBoundary_value`). -/
  elementaryBoundary : ∀ (top : Bool) (n : ℕ),
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).snd),
      intermediate n)
  elementaryBoundary_value : ∀ top n i s,
    elementaryBoundary top n ⟨i, s⟩ = attaching n ⟨i, (s, if top then 1 else 0)⟩
  /-- The inclusion of `intermediate n` into `elementarySpace top n`, a leg of
  `elementary_isPushout`. -/
  elementaryOld : ∀ top n, C(intermediate n, elementarySpace top n)
  /-- The attached disks, a leg of `elementary_isPushout`. -/
  elementaryDisks : ∀ top n,
    C((Σ _ : cell (Set.univ : Set X) (n + 1), (classicalCellDiskPair.{u} (n + 1)).fst),
      elementarySpace top n)
  elementary_isPushout : ∀ top n,
    IsPushout (TopCat.ofHom (elementaryBoundary top n)) (sphereSumToDiskSum X (n + 1))
      (TopCat.ofHom (elementaryOld top n)) (TopCat.ofHom (elementaryDisks top n))
  /-- The closed embedding (`elementaryInclude_closed`) of `elementarySpace top n` into the
  stage-`(n + 1)` space, onto the image of `intermediateToCommon n` and the `top` end of the
  tubes (`elementary_image`). -/
  elementaryInclude : ∀ top n, C(elementarySpace top n, (stages (n + 1)).space)
  /-- A retraction of the stage-`(n + 1)` space onto `elementarySpace top n`
  (`elementary_retraction`). -/
  elementaryRetraction : ∀ top n, C((stages (n + 1)).space, elementarySpace top n)
  elementaryInclude_old : ∀ top n a,
    elementaryInclude top n (elementaryOld top n a) = intermediateToCommon n a
  elementaryInclude_disk : ∀ top n i q,
    elementaryInclude top n (elementaryDisks top n ⟨i, q⟩) =
      cylinders n ⟨i, (q, if top then 1 else 0)⟩
  elementaryInclude_closed : ∀ top n, IsClosedEmbedding (elementaryInclude top n)
  elementaryRetraction_old : ∀ top n a,
    elementaryRetraction top n (intermediateToCommon n a) = elementaryOld top n a
  elementaryRetraction_disk : ∀ top n i q,
    elementaryRetraction top n (cylinders n ⟨i, (q, if top then 1 else 0)⟩) =
      elementaryDisks top n ⟨i, q⟩
  elementary_image : ∀ top n,
    Set.range (elementaryInclude top n) = Set.range (intermediateToCommon n) ∪
      Set.range (fun z : (Σ _ : cell (Set.univ : Set X) (n + 1),
        (classicalCellDiskPair.{u} (n + 1)).fst) =>
        cylinders n ⟨z.1, (z.2, if top then 1 else 0)⟩)
  elementary_retraction : ∀ top n x,
    elementaryRetraction top n (elementaryInclude top n x) = x
  /-- A homotopy from the identity of the stage-`(n + 1)` space to
  `elementaryInclude top n ∘ elementaryRetraction top n`, fixing the image of
  `elementaryInclude top n`. -/
  elementaryHomotopy : ∀ top n,
    ContinuousMap.HomotopyRel (ContinuousMap.id (stages (n + 1)).space)
      ((elementaryInclude top n).comp (elementaryRetraction top n))
      (Set.range (elementaryInclude top n))
  elementary_fixed_intermediate : ∀ top n t a,
    elementaryHomotopy top n (t, intermediateToCommon n a) = intermediateToCommon n a
  elementary_fixed_disk : ∀ top n t i q,
    elementaryHomotopy top n (t, cylinders n ⟨i, (q, if top then 1 else 0)⟩) =
      cylinders n ⟨i, (q, if top then 1 else 0)⟩
  /-- The point of the `0`-cell `j` in `skeletonTop X (n + 1)` (`zero_value`,
  `zeroOriginal_succ`). -/
  zeroOriginal : ∀ j : cell (Set.univ : Set X) 0, ∀ n, skeletonTop X (n + 1)
  /-- The point of the stage-`n` polyhedron matching the `0`-cell `j`: the stage-`0` vertex of
  `j` (`initial_zero_vertex`) carried by `polyhedralTransition` (`zeroPolyhedral_succ`). -/
  zeroPolyhedral : ∀ j : cell (Set.univ : Set X) 0, ∀ n, (stages n).polyhedron.Realization
  zeroOriginal_succ : ∀ j n, zeroOriginal j (n + 1) = skeletonTransition X (n + 1) (zeroOriginal j n)
  zeroPolyhedral_succ : ∀ j n, zeroPolyhedral j (n + 1) = polyhedralTransition n (zeroPolyhedral j n)
  initial_zero_vertex : ∀ j, zeroPolyhedral j 0 = Realization.vertex (stages 0).polyhedron
    (initialVertices.symm j) (initialSingleton_mem j)
  zero_same : ∀ j n, (stages n).original (zeroOriginal j n) = (stages n).polyhedral (zeroPolyhedral j n)
  zero_value : ∀ j n, (zeroOriginal j n).val = map (C := (Set.univ : Set X)) 0 j (0 : Fin 0 → ℝ)
  original_zero_fixed : ∀ j n t,
    (stages n).originalDeformation (t, (stages n).original (zeroOriginal j n)) =
      (stages n).original (zeroOriginal j n)
  polyhedral_zero_fixed : ∀ j n t,
    (stages n).polyhedralDeformation (t, (stages n).original (zeroOriginal j n)) =
      (stages n).original (zeroOriginal j n)

end Topology.CWComplex

end

/- Adapter from the original-space construction to the public stage type.
The interface uses public types. Its internal Stage appears only in the
construction body; no premise is added. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def publicCommonSuccessorStage (n : ℕ) :
    Topology.CWComplex.CommonSuccessorStageData X n := by
  let S := actualFiniteStages X n
  let D := actualFiniteClassicalStages X n
  letI := D.cw
  refine
    { vertices := S.vertices
      polyhedron := S.polyhedron
      space := S.space
      cw := D.cw
      hausdorff := actualFiniteStagesT2Space X n
      original := S.original
      polyhedral := S.polyhedral
      retractOriginal := S.retractOriginal
      retractPolyhedral := S.retractPolyhedral
      original_retraction := S.original_retraction
      polyhedral_retraction := S.polyhedral_retraction
      originalDeformation := S.originalDeformation
      polyhedralDeformation := S.polyhedralDeformation
      original_closed := (actualFiniteStages_end_closed X n).1
      polyhedral_closed := (actualFiniteStages_end_closed X n).2
      originalDiskLift := fun m hm j =>
        ActualRefinedTubeCharacteristicConstruction47.originalLowerDiskToSkeleton
          (X := X) (n + 1) m hm j
      originalDiskLift_value := ?_
      originalLabels := D.originalLabels
      original_characteristicDiskMap := ?_
      polyhedralLabels := D.polyhedralLabels
      polyhedral_characteristicDiskMap := ?_
      commonDimension := D.commonDimension
      polyhedronFaceBound := D.polyhedronFaceBound }
  · intro m hm j q
    change Topology.CWComplex.characteristicDiskMap (X := X) m j q =
      Topology.CWComplex.map (C := (Set.univ : Set X)) m j q.down.val
    exact Topology.CWComplex.characteristicDiskMap_apply m j q
  · intro m hm j
    ext q
    simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
      D.originalDisk m hm j q
  · intro m j
    ext q
    simpa only [TopCat.comp_app, Topology.CWComplex.characteristicDiskMap_apply] using!
      D.polyhedralDisk m j q

end ActualCommonSuccessorConstruction

end

/- Complete adapter to the public common-system signature.
The data come from the original-space construction. The public interface
contains no internal Stage, approximation or finite-collapse type. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open ActualRefinedTubeCharacteristicConstruction47 OriginalStrictSkeletonCWConstruction47
open PreAbstractSimplicialComplex.MappingCylinder.SmallCylinder CommonSuccessorSmallCylinderConstruction

universe u

namespace ActualCommonSuccessorConstruction

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]

private def publicCommonSuccessorSystem : Topology.CWComplex.CommonSuccessorSystemData X := by
  let Q := actualCommonSuccessorCWSystem X
  refine
    { stages := publicCommonSuccessorStage X
      initialOriginalHomeomorph := Homeomorph.refl (Topology.CWComplex.skeletonTop X 1)
      initial_original := rfl
      initialVertices := Equiv.refl _
      initialFaces := fun _ => Iff.rfl
      initialSingleton_mem := fun j =>
        (⊥ : AbstractSimplicialComplex (Topology.CWComplex.cell (Set.univ : Set X) 0)).singleton_mem j
      initial_whole_original_fixed := fun t z =>
        (Topology.CWComplex.commonZeroSkeleton X).initialHomotopy.eq_fst t (Set.mem_univ z)
      initial_whole_polyhedral_fixed := fun t z =>
        (Topology.CWComplex.commonZeroSkeleton X).polyhedronHomotopy.eq_fst t (Set.mem_univ z)
      originalSkeletonCW := fun n => originalStageCW (X := X) (n + 1)
      sphereComparison := fun n => liftedSphereComparison.{u} (n + 1)
      sphereComparison_value := fun n x => liftedSphereComparison_coordinate.{u} (n + 1) x
      subdivisions := fun n i => (cellApproximation (actualFiniteStages X n) i).subdivisions
      polyBoundary := fun n i => polyhedralBoundary (actualFiniteStages X n) i
      polyBoundary_value := fun _ _ _ => rfl
      approximatingMap := fun n i => (cellApproximation (actualFiniteStages X n) i).map
      approximationHomotopy := fun n i => (cellApproximation (actualFiniteStages X n) i).carrier
      approximationSupport := fun n i => (cellApproximation (actualFiniteStages X n) i).support
      approximationPoint := fun n i => (cellApproximation (actualFiniteStages X n) i).coordinate
      approximationVerticesFixed := fun n i => (cellApproximation (actualFiniteStages X n) i).vertices_fixed
      familyVertices := fun n => PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.Labels
        (cellPolyhedron (actualFiniteStages X n))
      family := fun n => smallFamilyComplex (actualFiniteStages X n)
      familyOld := fun n => smallFamilyOld (actualFiniteStages X n)
      familyOld_closed := fun n => PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.oldInclusion_isClosedEmbedding
        (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
        (cellMap (actualFiniteStages X n))
      familyRetraction := fun n => smallFamilyRetraction (actualFiniteStages X n)
      familyRetraction_old := fun n p => smallFamilyRetraction_old (actualFiniteStages X n) p
      familyDeformation := fun n => smallFamilyDeformation (actualFiniteStages X n)
      copiedSphere := fun n i => copiedSphereComparison (actualFiniteStages X n) i
      familyCopied := fun n i => smallFamilyCopied (actualFiniteStages X n) i
      familyCopied_closed := fun n i => PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.copiedInclusion_isClosedEmbedding
        (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
        (cellMap (actualFiniteStages X n)) i
      familyCopied_old_disjoint := fun n i => PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.copied_old_disjoint
        (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
        (cellMap (actualFiniteStages X n)) i
      familyCopied_distinct_disjoint := fun n i j hij =>
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Tagged.copied_copied_disjoint
          (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
          (cellMap (actualFiniteStages X n)) hij
      familyRetraction_copied := fun n i x => smallFamilyRetraction_copied (actualFiniteStages X n) i x
      intermediate := fun n => smallIntermediate (actualFiniteStages X n)
      intermediateCW := Q.intermediateCW
      intermediateT2 := Q.intermediateT2
      oldToIntermediate := fun n => smallIntermediateOld (actualFiniteStages X n)
      familyToIntermediate := fun n => smallIntermediateFamily (actualFiniteStages X n)
      oldToIntermediate_closed := fun n => smallIntermediateOld_closed (actualFiniteStages X n)
      familyToIntermediate_closed := fun n => actualIntermediateFamily_include_closed
        (actualFiniteStages X n) (actualFiniteStages_end_closed X n).2
      intermediate_range_intersection := actualFiniteIntermediateWholeLegs_intersection X
      intermediate_isPushout := fun n => IsPushout.of_hasPushout
        (TopCat.ofHom (actualFiniteStages X n).polyhedral)
        (TopCat.ofHom (smallFamilyOld (actualFiniteStages X n)))
      intermediateOld := Q.intermediateOld
      intermediateOldLabels := Q.intermediateOldLabels
      intermediateOld_carrier := Q.intermediateOld_carrier
      intermediateOld_labels := Q.intermediateOld_labels
      intermediateOld_characteristicDiskMap := Q.intermediateOld_characteristicDiskMap
      intermediateFamily := Q.intermediateFamily
      intermediateFamilyLabels := Q.intermediateFamilyLabels
      intermediateFamily_carrier := Q.intermediateFamily_carrier
      intermediateFamily_labels := Q.intermediateFamily_labels
      intermediateFamily_characteristicDiskMap := Q.intermediateFamily_characteristicDiskMap
      attaching := fun n => smallSuccessorBoundary (actualFiniteStages X n)
      attaching_zero := fun n i s => smallSuccessorBoundary_zero (actualFiniteStages X n) i s
      attaching_one := fun n i s => smallSuccessorBoundary_one (actualFiniteStages X n) i s
      sideInclusion := fun n =>
        (ActualRefinedTubeCharacteristicConstruction47.sideInclusion
          (I := CellIndex (X := X) n) (n + 1)).hom
      sideInclusion_value := fun _ _ _ _ => rfl
      intermediateToCommon := fun n =>
        oldIntoTubeSpace (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))
      intermediateToCommon_closed := fun n => oldIntoTubeSpace_closed
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))
      cylinders := fun n => (pushout.inr
        (TopCat.ofHom (smallSuccessorBoundary (actualFiniteStages X n)))
        (ActualRefinedTubeCharacteristicConstruction47.sideInclusion
          (I := CellIndex (X := X) n) (n + 1))).hom
      tube_isPushout := fun n => IsPushout.of_hasPushout
        (TopCat.ofHom (smallSuccessorBoundary (actualFiniteStages X n)))
        (ActualRefinedTubeCharacteristicConstruction47.sideInclusion
          (I := CellIndex (X := X) n) (n + 1))
      original_disk_end := fun n i q => actualOriginalSuccessorCollapse_disk (actualFiniteStages X n) i q
      familyToNext := fun n =>
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
          (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
          (cellMap (actualFiniteStages X n))).hom
      familyToNext_closed := fun n =>
        PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated_isClosedEmbedding
          (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
          (cellMap (actualFiniteStages X n))
      polyhedral_cylinder_end := fun n b => actualPolyhedralSuccessorCollapse_cylinder
        (actualFiniteStages X n) b
      coneDiskComparison := fun n i => actualConeDiskComparison (actualFiniteStages X n) i
      conesToNext := fun n =>
        (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
          (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
          (cellMap (actualFiniteStages X n)) (cellFiniteFaces (actualFiniteStages X n))).hom
      polyhedral_cone_end := fun n i q => by
        simpa only [actualConeDiskComparison_value] using!
          actualPolyhedralSuccessorCollapse_cone (actualFiniteStages X n) i q
      familySphere := fun n => (actualPolyhedralSphereMap (actualFiniteStages X n)).hom
      familySphere_value := fun n i s => by
        let S := actualFiniteStages X n
        have hSigma : actualSphereFamilyComparison S ⟨i, s⟩ =
            (⟨i, originalSphereToCopiedDomain (W := S.vertices)
              (n + 1) (actualSubdivisions S i) s⟩ :
                PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
                  (cellPolyhedron S) S.vertices) := by
          dsimp only [actualSphereFamilyComparison]
          exact PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_apply
            (fun j => originalSphereToCopiedDomain (W := S.vertices)
              (n + 1) (actualSubdivisions S j)) i s
        have hMap : (actualPolyhedralSphereMap S).hom ⟨i, s⟩ =
            PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
              (cellPolyhedron S) S.polyhedron (cellMap S)
                ⟨i, originalSphereToCopiedDomain (W := S.vertices)
                  (n + 1) (actualSubdivisions S i) s⟩ := by
          dsimp only [actualPolyhedralSphereMap]
          simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply]
          exact congrArg (fun q :
              PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainSum
                (cellPolyhedron S) S.vertices =>
                  (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
                    (cellPolyhedron S) S.polyhedron (cellMap S)).hom q) hSigma
        have hCopied :
            PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.domainsToCylinder
              (cellPolyhedron S) S.polyhedron (cellMap S)
                ⟨i, originalSphereToCopiedDomain (W := S.vertices)
                  (n + 1) (actualSubdivisions S i) s⟩ =
                    smallFamilyCopied S i ((copiedSphereComparison S i).symm s) := by
          rw [actualCopiedSphereComparison]
          exact actualDomainsToCylinder_copied S i ((copiedSphereComparison S i).symm s)
        exact Eq.trans hMap hCopied
      polyhedralDisks := fun n =>
        (TopCat.ofHom ((actualConeFamilyComparison (actualFiniteStages X n)).symm :
            C(EndpointDiskFamily (J := CellIndex (X := X) n) (n + 1),
              PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
                (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).vertices)) ≫
          PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
            (cellPolyhedron (actualFiniteStages X n)) (actualFiniteStages X n).polyhedron
            (cellMap (actualFiniteStages X n)) (cellFiniteFaces (actualFiniteStages X n))).hom
      polyhedralDisks_value := fun n i q => by
        let S := actualFiniteStages X n
        have hSigma : (actualConeFamilyComparison S).symm ⟨i, q⟩ =
            (⟨i, (actualConeDiskComparison S i).symm q⟩ :
              PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
                (cellPolyhedron S) S.vertices) := by
          dsimp only [actualConeFamilyComparison]
          exact PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.Comparisons.sigmaHomeomorph_symm_apply
            (actualConeDiskComparison S) i q
        simp only [TopCat.hom_comp, TopCat.hom_ofHom]
        exact congrArg
          (fun z : PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.coneSum
              (cellPolyhedron S) S.vertices =>
            (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.conesToAssociated
              (cellPolyhedron S) S.polyhedron (cellMap S) (cellFiniteFaces S)).hom z) hSigma
      polyhedral_isPushout := fun n => by
        simpa only [endpointSphereInclusion_original] using!
          actualReducedPolyhedralEnd_square (actualFiniteStages X n)
      transition := fun n => actualCommonStageTransition X (actualFiniteStages X n)
      transition_closed := fun n => actualCommonStageTransition_closed (actualFiniteStages X n)
      transition_formula := fun _ => rfl
      polyhedralTransition := fun n => actualPolyhedralStageTransition X (actualFiniteStages X n)
      polyhedralTransition_closed := fun n => by
        let S := actualFiniteStages X n
        change IsClosedEmbedding
          ((PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
            (cellPolyhedron S) S.polyhedron (cellMap S)).hom.comp (smallFamilyOld S))
        exact
          (PreAbstractSimplicialComplex.MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated_isClosedEmbedding
            (cellPolyhedron S) S.polyhedron (cellMap S)).comp
              (MappingCylinder.smallFamilyAttachments (cellPolyhedron S) S.polyhedron
                (cellMap S) (cellFiniteFaces S)).old_closed
      transition_original := fun n => actualCommonStageTransition_original X (actualFiniteStages X n)
      transition_polyhedral := fun n => actualCommonStageTransition_polyhedral X (actualFiniteStages X n)
      oldStage := Q.oldStage
      oldStageLabels := Q.oldStageLabels
      oldStage_carrier := Q.oldStage_carrier
      oldStage_labels := Q.oldStage_labels
      oldStage_characteristicDiskMap := Q.oldStage_characteristicDiskMap
      originalEnd := Q.originalEnd
      originalEnd_carrier := Q.originalEnd_carrier
      originalEnd_labels := Q.originalEnd_labels
      polyhedralEnd := Q.polyhedralEnd
      polyhedralEnd_carrier := Q.polyhedralEnd_carrier
      polyhedralEnd_labels := Q.polyhedralEnd_labels
      original_preimage := Q.original_preimage
      polyhedral_preimage := Q.polyhedral_preimage
      end_intersection := Q.end_intersection
      initialToStage := actualCommonZeroToStage X
      initialToStage_zero := rfl
      initialToStage_succ := fun _ => rfl
      initialToStage_closed := actualCommonZeroToStage_closed X
      zero_intersection := Q.zero_intersection
      elementarySpace := fun top n => unitDiskEndSpace (n + 1)
        (smallSuccessorBoundary (actualFiniteStages X n)) top
      elementaryBoundary := fun top n => endpointBoundary (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))) top
      elementaryBoundary_value := fun top n i s =>
        normalizedEndpointBoundary_value (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top i s
      elementaryOld := fun top n => (diskEndOld (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))) top).hom
      elementaryDisks := fun top n => (diskEndDisks (n + 1)
        (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))) top).hom
      elementary_isPushout := fun top n => by
        simpa only [endpointSphereInclusion_original] using!
          (IsPushout.of_hasPushout
            (TopCat.ofHom (endpointBoundary (n + 1)
              (normalizedLiteralBoundary (n + 1) (smallSuccessorBoundary (actualFiniteStages X n))) top))
            (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1))))
      elementaryInclude := fun top n => (elementaryTubeCollapse (n + 1)
        (smallSuccessorBoundary (actualFiniteStages X n)) top).include.hom
      elementaryRetraction := fun top n => (elementaryTubeCollapse (n + 1)
        (smallSuccessorBoundary (actualFiniteStages X n)) top).retract.hom
      elementaryInclude_old := fun top n a => unitDiskEndInclude_old
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top a
      elementaryInclude_disk := fun top n i q => unitDiskEndInclude_disk
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top i q
      elementaryInclude_closed := fun top n => unitDiskEndInclude_closed
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top
      elementaryRetraction_old := fun top n a => unitDiskEndRetraction_old
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top a
      elementaryRetraction_disk := fun top n i q => by
        change unitDiskEndRetraction (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top
            (originalCylinderMap (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) i
              (q, unitSelectedHeight top)) = _
        rw [← unitDiskEndInclude_disk]
        exact unitDiskEndRetraction_include (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top _
      elementary_image := fun top n => by
        let H := smallSuccessorBoundary (actualFiniteStages X n)
        let sq := IsPushout.of_hasPushout
          (TopCat.ofHom (endpointBoundary (n + 1) (normalizedLiteralBoundary (n + 1) H) top))
          (TopCat.ofHom (endpointSphereInclusion (J := CellIndex (X := X) n) (n + 1)))
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with hx | hx
          · rcases hx with ⟨a, rfl⟩
            exact Or.inl ⟨a, (unitDiskEndInclude_old (n + 1) H top a).symm⟩
          · rcases hx with ⟨⟨i, q⟩, rfl⟩
            exact Or.inr ⟨⟨i, q⟩, (unitDiskEndInclude_disk (n + 1) H top i q).symm⟩
        · rintro (⟨a, ha⟩ | ⟨⟨i, q⟩, hq⟩)
          · exact ⟨diskEndOld (n + 1) (normalizedLiteralBoundary (n + 1) H) top a,
              (unitDiskEndInclude_old (n + 1) H top a).trans ha⟩
          · exact ⟨diskEndDisks (n + 1) (normalizedLiteralBoundary (n + 1) H) top ⟨i, q⟩,
              (unitDiskEndInclude_disk (n + 1) H top i q).trans hq⟩
      elementary_retraction := fun top n x => finiteCollapse_retraction
        (elementaryTubeCollapse (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top) x
      elementaryHomotopy := fun top n => (elementaryTubeCollapse (n + 1)
        (smallSuccessorBoundary (actualFiniteStages X n)) top).deformation
      elementary_fixed_intermediate := fun top n t a => unitDiskEndRelativeHomotopy_old_fixed
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top t a
      elementary_fixed_disk := fun top n t i q => unitDiskEndRelativeHomotopy_disk_fixed
        (n + 1) (smallSuccessorBoundary (actualFiniteStages X n)) top t i q
      zeroOriginal := fun j n => (actualSharedZeroPoint X j n).original
      zeroPolyhedral := fun j n => (actualSharedZeroPoint X j n).polyhedral
      zeroOriginal_succ := fun _ _ => rfl
      zeroPolyhedral_succ := fun _ _ => rfl
      initial_zero_vertex := fun _ => rfl
      zero_same := fun j n => (actualSharedZeroPoint X j n).same
      zero_value := actualSharedZeroPoint_original_value X
      original_zero_fixed := actualSharedZeroPoint_original_fixed X
      polyhedral_zero_fixed := actualSharedZeroPoint_polyhedral_fixed X }

end ActualCommonSuccessorConstruction

end

public section

noncomputable section

universe u

namespace Topology.CWComplex

/-- Construct the actual finite common CW/polyhedral system, including both
end retractions, whole characteristic maps and strong intersection laws. -/
def commonSuccessorSystem (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    CommonSuccessorSystemData X :=
  ActualCommonSuccessorConstruction.publicCommonSuccessorSystem X

end Topology.CWComplex

end

public section

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open ActualCommonSuccessorConstruction

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- The actual old-vertex inclusion, first into its family cylinder and then its associated cone. -/
def commonSuccessorSystemVertexTransition (n : ℕ) :
    ((commonSuccessorSystem X).stages n).vertices ↪
      ((commonSuccessorSystem X).stages (n + 1)).vertices := by
  let S := actualFiniteStages X n
  change S.vertices ↪ (actualTopologicalSuccessor X S).vertices
  exact Function.Embedding.inr.trans Function.Embedding.inl

/-- Every original stage face maps to its literal face in the constructed next polyhedron. -/
theorem commonSuccessorSystemVertexTransition_faces (n : ℕ)
    (s : Finset ((commonSuccessorSystem X).stages n).vertices)
    (hs : s ∈ ((commonSuccessorSystem X).stages n).polyhedron) :
    s.map (commonSuccessorSystemVertexTransition X n) ∈
      ((commonSuccessorSystem X).stages (n + 1)).polyhedron := by
  classical
  let S := actualFiniteStages X n
  let s₀ : Finset S.vertices := s
  have hs₀ : s₀ ∈ S.polyhedron := hs
  let e₀ : S.vertices ↪
      MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S) :=
    Function.Embedding.inr
  let e₁ : MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S) ↪
      MappingCylinder.SmallFamily.Cone.ConeLabels (W := S.vertices) (cellPolyhedron S) :=
    Function.Embedding.inl
  have hOld : s₀.map e₀ ∈ smallFamilyComplex S := by
    apply MappingCylinder.SmallFamily.Tagged.oldTarget_le_family
      (cellPolyhedron S) S.polyhedron (cellMap S)
    refine ⟨s₀, hs₀, ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_map]
    rfl
  have hPart : s₀.map (e₀.trans e₁) ∈
      MappingCylinder.SmallFamily.Cone.cylinderPart
        (cellPolyhedron S) S.polyhedron (cellMap S) := by
    change s₀.map (e₀.trans e₁) ∈ MappingCylinder.relabelComplex (smallFamilyComplex S) e₁
    refine ⟨s₀.map e₀, hOld, ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨w, ⟨v₀, hv₀, rfl⟩, rfl⟩
      exact ⟨v₀, hv₀, rfl⟩
    · rintro ⟨v₀, hv₀, rfl⟩
      exact ⟨e₀ v₀, ⟨v₀, hv₀, rfl⟩, rfl⟩
  have hNext : s₀.map (e₀.trans e₁) ∈
      MappingCylinder.SmallFamily.Cone.associatedFamily
        (cellPolyhedron S) S.polyhedron (cellMap S) :=
    (show MappingCylinder.SmallFamily.Cone.cylinderPart
        (cellPolyhedron S) S.polyhedron (cellMap S) ≤
        MappingCylinder.SmallFamily.Cone.associatedFamily
          (cellPolyhedron S) S.polyhedron (cellMap S) from le_sup_left) hPart
  simpa only [S, s₀, e₀, e₁, commonSuccessorSystemVertexTransition] using! hNext

/-- The whole finite barycentric point is transported by the same actual ambient vertex inclusion. -/
theorem commonSuccessorSystem_polyhedralTransition_point (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    ((commonSuccessorSystem X).polyhedralTransition n p).point =
      p.point.map (commonSuccessorSystemVertexTransition X n) := by
  let S := actualFiniteStages X n
  let p₀ : S.polyhedron.Realization := p
  let e : S.vertices ↪ MappingCylinder.SmallFamily.Cone.ConeLabels
      (W := S.vertices) (cellPolyhedron S) :=
    Function.Embedding.inr.trans Function.Embedding.inl
  have hOld : (MappingCylinder.SmallFamily.Tagged.oldInclusion
      (cellPolyhedron S) S.polyhedron (cellMap S) p₀).point =
      p₀.point.map (Function.Embedding.inr : S.vertices ↪
        MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S)) :=
    MappingCylinder.SmallFamily.Tagged.oldInclusion_point
      (cellPolyhedron S) S.polyhedron (cellMap S) p₀
  have hCone : (MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
      (cellPolyhedron S) S.polyhedron (cellMap S)
      (MappingCylinder.SmallFamily.Tagged.oldInclusion
        (cellPolyhedron S) S.polyhedron (cellMap S) p₀)).point =
      (MappingCylinder.SmallFamily.Tagged.oldInclusion
        (cellPolyhedron S) S.polyhedron (cellMap S) p₀).point.map
        (Function.Embedding.inl :
          MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S) ↪
          MappingCylinder.SmallFamily.Cone.ConeLabels (W := S.vertices) (cellPolyhedron S)) :=
    MappingCylinder.SmallFamily.Geometry.cylinderCone_point
      (cellPolyhedron S) S.polyhedron (cellMap S)
      (MappingCylinder.SmallFamily.Tagged.oldInclusion
        (cellPolyhedron S) S.polyhedron (cellMap S) p₀)
  have hMapped := congrArg (fun q : Convexity.StdSimplex ℝ
      (MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S)) =>
        q.map (Function.Embedding.inl :
          MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S) ↪
          MappingCylinder.SmallFamily.Cone.ConeLabels (W := S.vertices) (cellPolyhedron S))) hOld
  have hComp : (p₀.point.map (Function.Embedding.inr : S.vertices ↪
      MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S))).map
      (Function.Embedding.inl :
        MappingCylinder.SmallFamily.Tagged.Labels (W := S.vertices) (cellPolyhedron S) ↪
        MappingCylinder.SmallFamily.Cone.ConeLabels (W := S.vertices) (cellPolyhedron S)) =
      p₀.point.map e := by
    rw [Convexity.StdSimplex.map_map]
    rfl
  have hPoint : (actualPolyhedralStageTransition X S p₀).point = p₀.point.map e := by
    change (MappingCylinder.SmallFamily.ConePushout.cylinderToAssociated
      (cellPolyhedron S) S.polyhedron (cellMap S)
      (MappingCylinder.SmallFamily.Tagged.oldInclusion
        (cellPolyhedron S) S.polyhedron (cellMap S) p₀)).point = p₀.point.map e
    exact Eq.trans hCone (Eq.trans hMapped hComp)
  simpa only [S, p₀, e, commonSuccessorSystemVertexTransition] using! hPoint

end Topology.CWComplex

end


/- Exact old-stage traces for open pairs, reused by the ordinary dimension union. -/
noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open ActualCommonSuccessorConstruction ActualRefinedTubeCharacteristicConstruction47

universe u

namespace ActualCommonSuccessorConstruction

private theorem actualTransition_disjointOpenExtension
    {X : TopCat.{u}} [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    {n : ℕ} (S : Stage X n) (U V : Set S.space)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) :
    ∃ U' V' : Set (actualTopologicalSuccessor X S).space,
      IsOpen U' ∧ IsOpen V' ∧ Disjoint U' V' ∧
      actualCommonStageTransition X S ⁻¹' U' = U ∧
      actualCommonStageTransition X S ⁻¹' V' = V := by
  let d := n + 1
  let H := smallSuccessorBoundary S
  let A₁ : Set (smallIntermediate S) := intermediateToOld S ⁻¹' U
  let A₂ : Set (smallIntermediate S) := intermediateToOld S ⁻¹' V
  have hA₁ : IsOpen A₁ := hU.preimage (intermediateToOld S).hom.continuous
  have hA₂ : IsOpen A₂ := hV.preimage (intermediateToOld S).hom.continuous
  have hA : Disjoint A₁ A₂ := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact hUV.notMem_of_mem_left ha hb
  let B₁ := collarOpenFamily d H A₁
  let B₂ := collarOpenFamily d H A₂
  have hB₁ : IsOpen B₁ := collarOpenFamily_isOpen d H A₁ hA₁
  have hB₂ : IsOpen B₂ := collarOpenFamily_isOpen d H A₂ hA₂
  have ht₁ : ∀ p : sideSum (I := CellIndex (X := X) n) d,
      H p ∈ A₁ ↔ sideInclusion d p ∈ B₁ :=
    collarOpenFamily_boundary_trace d H A₁
  have ht₂ : ∀ p : sideSum (I := CellIndex (X := X) n) d,
      H p ∈ A₂ ↔ sideInclusion d p ∈ B₂ :=
    collarOpenFamily_boundary_trace d H A₂
  let E₁ := descendedTubeOpen d H A₁ B₁ hA₁ hB₁ ht₁
  let E₂ := descendedTubeOpen d H A₂ B₂ hA₂ hB₂ ht₂
  have hE₁ : IsOpen E₁ := descendedTubeOpen_isOpen d H A₁ B₁ hA₁ hB₁ ht₁
  have hE₂ : IsOpen E₂ := descendedTubeOpen_isOpen d H A₂ B₂ hA₂ hB₂ ht₂
  have hE : Disjoint E₁ E₂ :=
    descendedTubeOpen_disjoint d H A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ ht₁ ht₂ hA
      (collarOpenFamily_disjoint d H A₁ A₂ hA)
  have hp₁ : actualCommonStageTransition X S ⁻¹' E₁ = U := by
    ext x
    change oldIntoTubeSpace d H (smallIntermediateOld S x) ∈ E₁ ↔ x ∈ U
    calc
      _ ↔ smallIntermediateOld S x ∈ A₁ :=
        descendedTubeOpen_old d H A₁ B₁ hA₁ hB₁ ht₁ (smallIntermediateOld S x)
      _ ↔ x ∈ U := by
        change intermediateToOld S (smallIntermediateOld S x) ∈ U ↔ x ∈ U
        rw [intermediateToOld_old]
  have hp₂ : actualCommonStageTransition X S ⁻¹' E₂ = V := by
    ext x
    change oldIntoTubeSpace d H (smallIntermediateOld S x) ∈ E₂ ↔ x ∈ V
    calc
      _ ↔ smallIntermediateOld S x ∈ A₂ :=
        descendedTubeOpen_old d H A₂ B₂ hA₂ hB₂ ht₂ (smallIntermediateOld S x)
      _ ↔ x ∈ V := by
        change intermediateToOld S (smallIntermediateOld S x) ∈ V ↔ x ∈ V
        rw [intermediateToOld_old]
  exact ⟨E₁, E₂, hE₁, hE₂, hE, hp₁, hp₂⟩

end ActualCommonSuccessorConstruction

namespace Topology.CWComplex

/-- Every disjoint open pair in the constructed stage extends to the actual next stage
with both original transition preimages retained exactly. -/
public theorem commonSuccessorSystem_transition_disjointOpenExtension
    (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ)
    (U V : Set ((commonSuccessorSystem X).stages n).space)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V) :
    ∃ U' V' : Set ((commonSuccessorSystem X).stages (n + 1)).space,
      IsOpen U' ∧ IsOpen V' ∧ Disjoint U' V' ∧
      (commonSuccessorSystem X).transition n ⁻¹' U' = U ∧
      (commonSuccessorSystem X).transition n ⁻¹' V' = V := by
  exact ActualCommonSuccessorConstruction.actualTransition_disjointOpenExtension
    (actualFiniteStages X n) U V hU hV hUV

end Topology.CWComplex

end

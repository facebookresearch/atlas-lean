/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization
public import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder
public import MathlibExt.Topology.CWComplex.CharacteristicDiskMap
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Classical cells under relabeling and complex inclusion

Transport the selected canonical CW cells and complete closed characteristic
disks through an injective ambient relabeling and an actual complex inclusion.
The inclusion package also records the closed subcomplex carrier and cell labels.
-/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped Simplicial

universe u

namespace PreAbstractSimplicialComplex.Realization

namespace ClassicalCellEmbeddingConstruction

variable {V W : Type u} {P Q : PreAbstractSimplicialComplex V}

private theorem weakOpenCell_image (P : PreAbstractSimplicialComplex V) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj (faceNerve P))) n) :
    Topology.CWComplex.openCell (C := (Set.univ : Set P.Realization)) n j =
      Realization.affineHomeomorph P ''
        Topology.CWComplex.openCell (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j := by
  change ((Topology.CWComplex.map
      (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j).transEquiv
        (Realization.affineHomeomorph P).toEquiv) '' Metric.ball 0 1 = _
  simp only [PartialEquiv.coe_transEquiv, Homeomorph.coe_toEquiv,
    Topology.RelCWComplex.openCell, Topology.CWComplex.map_def, Set.image_image]
  rfl

private def weakClassicalSubcomplexOfInclusion (h : P ≤ Q) :
    Σ κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set Q.Realization) n,
      {A : Topology.CWComplex.Subcomplex (Set.univ : Set Q.Realization) //
        (A : Set Q.Realization) = Set.range (Realization.inclusion h) ∧
        (∀ n, A.I n = Set.range (κ n)) ∧
        ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
          (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
          Realization.inclusion h
              (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
            Topology.CWComplex.map (C := (Set.univ : Set Q.Realization)) n (κ n j) x.down.val} := by
  let d := SSet.realizationClassicalCWSubcomplexOfMono (faceNerveInclusion h)
  let κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
      Topology.CWComplex.cell (Set.univ : Set Q.Realization) n := d.fst
  let e := Realization.affineHomeomorph Q
  let A : Topology.CWComplex.Subcomplex (Set.univ : Set Q.Realization) :=
    { carrier := e '' (d.snd.val : Set (SSet.toTop.obj (faceNerve Q)))
      I := d.snd.val.I
      closed' := e.isClosedMap _ d.snd.val.closed
      union' := by
        have hUnion := d.snd.val.union'
        rw [Set.empty_union] at hUnion ⊢
        simpa only [Set.image_iUnion, weakOpenCell_image] using!
          congrArg (fun S => e '' S) hUnion }
  refine ⟨κ, ⟨A, ?_, ?_, ?_⟩⟩
  · change e '' (d.snd.val : Set (SSet.toTop.obj (faceNerve Q))) = _
    rw [d.snd.property.1]
    ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, hz⟩
      exact ⟨Realization.affineHomeomorph P x,
        (Realization.affineHomeomorph_inclusion h x).symm.trans hz⟩
    · rintro ⟨x, rfl⟩
      let y := (Realization.affineHomeomorph P).symm x
      exact ⟨SSet.toTop.map (faceNerveInclusion h) y, ⟨y, rfl⟩,
        (Realization.affineHomeomorph_inclusion h y).trans
          (congrArg (Realization.inclusion h)
              ((Realization.affineHomeomorph P).apply_symm_apply x))⟩
  · intro n
    exact d.snd.property.2.1 n
  · intro n j x
    change Realization.inclusion h
        (Realization.affineHomeomorph P
          (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j
              x.down.val)) =
      Realization.affineHomeomorph Q
        (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj (faceNerve Q)))) n
            (κ n j) x.down.val)
    calc
      _ = Realization.affineHomeomorph Q
          (SSet.toTop.map (faceNerveInclusion h)
            (Topology.CWComplex.map
              (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j x.down.val)) :=
        (Realization.affineHomeomorph_inclusion h _).symm
      _ = _ := congrArg (Realization.affineHomeomorph Q) (d.snd.property.2.2 n j x)

private def relabeledFace (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Face P → Face (MappingCylinder.relabelComplex P e) := by
  classical
  exact fun a => ⟨a.val.image e, ⟨a.val, a.property, rfl⟩⟩

private theorem relabeledFace_injective (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Function.Injective (relabeledFace P e) := by
  classical
  intro a b h
  apply Subtype.ext
  exact Finset.image_injective e.injective (congrArg Subtype.val h)

private theorem relabeledFace_surjective (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Function.Surjective (relabeledFace P e) := by
  classical
  intro b
  rcases b.property with ⟨a, ha, hab⟩
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

private def relabeledFaceOrderIso (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Face P ≃o Face (MappingCylinder.relabelComplex P e) := by
  classical
  exact
    { toEquiv := Equiv.ofBijective (relabeledFace P e)
        ⟨relabeledFace_injective P e, relabeledFace_surjective P e⟩
      map_rel_iff' := by
        intro a b
        change a.val.image e ⊆ b.val.image e ↔ a.val ⊆ b.val
        exact Finset.image_subset_image_iff e.injective }

private def relabeledNerveMap (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    faceNerve P ⟶ faceNerve (MappingCylinder.relabelComplex P e) :=
  CategoryTheory.nerveMap (relabeledFaceOrderIso P e).monotone.functor

private theorem relabeledNerveMap_mono (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Mono (relabeledNerveMap P e) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext (F := a) (G := b)
    (h := fun j => (relabeledFaceOrderIso P e).injective
      (congrArg (fun z : (faceNerve (MappingCylinder.relabelComplex P e)).obj n => z.obj j) hab))
    (w := by intro j hj; subsingleton)

private theorem affineHomeomorph_relabel (P : PreAbstractSimplicialComplex V) (e : V ↪ W)
    (z : SSet.toTop.obj (faceNerve P)) :
    MappingCylinder.relabelHomeomorph P e (Realization.affineHomeomorph P z) =
      Realization.affineHomeomorph (MappingCylinder.relabelComplex P e)
        (SSet.toTop.map (relabeledNerveMap P e) z) := by
  obtain ⟨n, σ, _, q, _, rfl⟩ := SSet.exists_nonDegenerate_interior_presentation (faceNerve P) z
  change MappingCylinder.relabelHomeomorph P e
      (Realization.affineToTop P (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q))) =
    Realization.affineToTop (MappingCylinder.relabelComplex P e)
      (SSet.toTop.map (relabeledNerveMap P e)
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm q)))
  rw [Realization.realizedCell_naturality, Realization.affineToTop_cell,
      Realization.affineToTop_cell]
  apply Realization.ext
  change ((MappingCylinder.relabelMorphism P e).realization (Realization.chainMap P σ q)).point = _
  rw [MappingCylinder.relabelMorphism_point]
  change (Realization.chainPoint σ q).map e =
    Realization.chainPoint ((relabeledNerveMap P e).app _ σ) q
  rw [Realization.chainPoint, Convexity.map_iConvexComb, Realization.chainPoint]
  apply Convexity.iConvexComb_congr
  intro j _
  exact Realization.map_subBarycenter_injective e e.injective (σ.obj j).val
    (P.isRelLowerSet_faces (σ.obj j).property).1

private def weakRelabelClassicalCellLaw (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Σ' κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set (MappingCylinder.relabelComplex P e).Realization) n,
      ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
        (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
        MappingCylinder.relabelHomeomorph P e
            (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
          Topology.CWComplex.map
            (C := (Set.univ : Set (MappingCylinder.relabelComplex P e).Realization)) n
                (κ n j) x.down.val := by
  letI := relabeledNerveMap_mono P e
  let d := SSet.realizationClassicalCWSubcomplexOfMono (relabeledNerveMap P e)
  refine ⟨d.fst, ?_⟩
  intro n j x
  change MappingCylinder.relabelHomeomorph P e
      (Realization.affineHomeomorph P
        (Topology.CWComplex.map (C := (Set.univ : Set (SSet.toTop.obj (faceNerve P)))) n j
            x.down.val)) =
    Realization.affineHomeomorph (MappingCylinder.relabelComplex P e)
      (Topology.CWComplex.map
        (C := (Set.univ : Set (SSet.toTop.obj (faceNerve (MappingCylinder.relabelComplex P e)))))
        n (d.fst n j) x.down.val)
  rw [affineHomeomorph_relabel]
  exact congrArg (Realization.affineHomeomorph (MappingCylinder.relabelComplex P e))
    (d.snd.property.2.2 n j x)

private def oldTargetClassicalCellLaw (P : PreAbstractSimplicialComplex V) (e : V ↪ W)
    (Q : PreAbstractSimplicialComplex W) (h : MappingCylinder.relabelComplex P e ≤ Q) :
    Σ' κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set Q.Realization) n,
      ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
        (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
        Realization.inclusion h (MappingCylinder.relabelHomeomorph P e
          (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val)) =
            Topology.CWComplex.map (C := (Set.univ : Set Q.Realization)) n (κ n j) x.down.val := by
  let r := weakRelabelClassicalCellLaw P e
  let i := weakClassicalSubcomplexOfInclusion h
  refine ⟨fun n => (r.fst n).trans (i.fst n), ?_⟩
  intro n j x
  exact (congrArg (Realization.inclusion h) (r.snd n j x)).trans
    (i.snd.property.2.2 n (r.fst n j) x)

private theorem relabeledRealizationMap_surjective
    (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Function.Surjective (SSet.toTop.map (relabeledNerveMap P e)) := by
  intro y
  let ψ := Realization.affineHomeomorph (MappingCylinder.relabelComplex P e)
  let φ := Realization.affineHomeomorph P
  let R := MappingCylinder.relabelHomeomorph P e
  let x := φ.symm (R.symm (ψ y))
  refine ⟨x, ψ.injective ?_⟩
  calc
    ψ (SSet.toTop.map (relabeledNerveMap P e) x) = R (φ x) :=
      (affineHomeomorph_relabel P e x).symm
    _ = ψ y := by
      dsimp only [x]
      rw [φ.apply_symm_apply, R.apply_symm_apply]

private theorem weakRelabelClassicalCellLaw_surjective
    (P : PreAbstractSimplicialComplex V) (e : V ↪ W) (n : ℕ) :
    Function.Surjective ((weakRelabelClassicalCellLaw P e).fst n) := by
  let := relabeledNerveMap_mono P e
  let d := SSet.realizationClassicalCWSubcomplexOfMono (relabeledNerveMap P e)
  change Function.Surjective (d.fst n)
  intro j
  have hA : (d.snd.val : Set (SSet.toTop.obj (faceNerve (MappingCylinder.relabelComplex P e)))) =
      Set.univ :=
    d.snd.property.1.trans (Set.range_eq_univ.mpr (relabeledRealizationMap_surjective P e))
  have hj : j ∈ d.snd.val.I n := by
    by_contra hj
    let x := Topology.CWComplex.map
      (C := (Set.univ : Set (SSet.toTop.obj
          (faceNerve (MappingCylinder.relabelComplex P e))))) n j 0
    have hxOpen : x ∈ Topology.CWComplex.openCell
        (C := (Set.univ : Set (SSet.toTop.obj
            (faceNerve (MappingCylinder.relabelComplex P e))))) n j :=
      ⟨0, by simp, rfl⟩
    have hxA : x ∈ (d.snd.val : Set
        (SSet.toTop.obj (faceNerve (MappingCylinder.relabelComplex P e)))) := by
      rw [hA]
      exact Set.mem_univ x
    exact (d.snd.val.disjoint_openCell_subcomplex_of_notMem hj).notMem_of_mem_left hxOpen hxA
  rw [d.snd.property.2.1 n] at hj
  exact hj

end ClassicalCellEmbeddingConstruction

/-- The canonical closed CW subcomplex and whole characteristic disks of an actual inclusion. -/
public def classicalSubcomplexOfInclusion {V : Type u}
    {P Q : PreAbstractSimplicialComplex V} (h : P ≤ Q) :
    Σ κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set Q.Realization) n,
      {A : Topology.CWComplex.Subcomplex (Set.univ : Set Q.Realization) //
        (A : Set Q.Realization) = Set.range (Realization.inclusion h) ∧
        (∀ n, A.I n = Set.range (κ n)) ∧
        ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
          (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
          Realization.inclusion h
              (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
            Topology.CWComplex.map (C := (Set.univ : Set Q.Realization)) n (κ n j) x.down.val} := by
  exact ClassicalCellEmbeddingConstruction.weakClassicalSubcomplexOfInclusion h

/-- The canonical cell embedding induced by an injective ambient relabeling. -/
public def classicalCellEmbeddingOfRelabel {V W : Type u}
    (P : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    Σ' κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set (MappingCylinder.relabelComplex P e).Realization) n,
      ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
        (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
        MappingCylinder.relabelHomeomorph P e
            (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val) =
          Topology.CWComplex.map
            (C := (Set.univ : Set (MappingCylinder.relabelComplex P e).Realization)) n
                (κ n j) x.down.val := by
  exact ClassicalCellEmbeddingConstruction.weakRelabelClassicalCellLaw P e

/-- Every canonical cell of the relabeled complex comes from an original cell. -/
public theorem classicalCellEmbeddingOfRelabel_surjective {V W : Type u}
    (P : PreAbstractSimplicialComplex V) (e : V ↪ W) (n : ℕ) :
    Function.Surjective ((classicalCellEmbeddingOfRelabel P e).fst n) := by
  exact ClassicalCellEmbeddingConstruction.weakRelabelClassicalCellLaw_surjective P e n

/-- Canonical classical cells for an injective relabeling followed by a complex inclusion.
The complete original closed characteristic disks are retained. -/
public def classicalCellEmbeddingOfRelabelInclusion {V W : Type u}
    (P : PreAbstractSimplicialComplex V) (e : V ↪ W)
    (Q : PreAbstractSimplicialComplex W) (h : MappingCylinder.relabelComplex P e ≤ Q) :
    Σ' κ : ∀ n, Topology.CWComplex.cell (Set.univ : Set P.Realization) n ↪
        Topology.CWComplex.cell (Set.univ : Set Q.Realization) n,
      ∀ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set P.Realization) n)
        (x : (Topology.CWComplex.classicalCellDiskPair.{u} n).fst),
        Realization.inclusion h (MappingCylinder.relabelHomeomorph P e
          (Topology.CWComplex.map (C := (Set.univ : Set P.Realization)) n j x.down.val)) =
            Topology.CWComplex.map (C := (Set.univ : Set Q.Realization)) n (κ n j) x.down.val := by
  exact ClassicalCellEmbeddingConstruction.oldTargetClassicalCellLaw P e Q h

end PreAbstractSimplicialComplex.Realization
end

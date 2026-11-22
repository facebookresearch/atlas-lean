/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Discrete
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyIdentities
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence

/-!
# Geometric realization is invariant under simplicial reversal

For a simplicial set `X`, geometric realization of the covariant reversal
`SimplicialObject.opFunctor.obj X` is naturally isomorphic to the realization
of `X`. The comparison goes through levelwise-discrete simplicial spaces:
`SSet.toTopLevelwiseDiscreteNatIso` identifies ordinary realization with
`TopCat.simplicialRealization` after `SSet.levelwiseDiscrete`, postcomposition
with `TopCat.discrete` commutes with precomposition with `SimplexCategory.rev`,
and `TopCat.SimplicialRealization.opIso` reverses simplicial spaces.

Consequences recorded here: naturality of the reversal comparison, transfer
of the weak-homotopy-equivalence property across reversal, and fixity of
realized vertices.

Nonclaims: no nerve, comma, Bousfield–Kan, homotopy-fiber, or Quillen-theorem
claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial

namespace SSet

universe u

/-- Postcomposition with `TopCat.discrete` commutes with precomposition with
`SimplexCategory.rev`: levelwise-discrete simplicial spaces are stable under
reversal. Both sides are the same composite of functors. -/
noncomputable def levelwiseDiscreteOpIso (X : SSet.{u}) :
    levelwiseDiscrete.obj (SimplicialObject.opFunctor.obj X) ≅
      SimplicialObject.opFunctor.obj (levelwiseDiscrete.obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The forward map of `levelwiseDiscreteOpIso` is the identity. -/
theorem levelwiseDiscreteOpIso_hom (X : SSet.{u}) :
    (levelwiseDiscreteOpIso X).hom = 𝟙 _ := by
  ext n
  rfl

/-- Levelwise-discrete commutes with reversal on maps. -/
theorem levelwiseDiscrete_map_opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    levelwiseDiscrete.map (SimplicialObject.opFunctor.map f) =
      SimplicialObject.opFunctor.map (levelwiseDiscrete.map f) := by
  refine NatTrans.ext ?_
  funext n
  simp only [levelwiseDiscrete_map_app, SimplicialObject.opFunctor_map_app]
  rfl

/-- Forward discrete comparison with unfolded codomain (proof alias). -/
private noncomputable abbrev toTopDiscreteFwd (X : SSet.{u}) :
    SSet.toTop.obj X ⟶
      TopCat.simplicialRealization.obj (levelwiseDiscrete.obj X) :=
  (toTopLevelwiseDiscreteNatIso.app X).hom

/-- Backward discrete comparison with unfolded domain (proof alias). -/
private noncomputable abbrev toTopDiscreteBwd (X : SSet.{u}) :
    TopCat.simplicialRealization.obj (levelwiseDiscrete.obj X) ⟶
      SSet.toTop.obj X :=
  (toTopLevelwiseDiscreteNatIso.app X).symm.hom

/-- Geometric realization is invariant under the covariant simplicial
reversal. -/
noncomputable def toTopReversalIso (X : SSet.{u}) :
    SSet.toTop.obj (SimplicialObject.opFunctor.obj X) ≅ SSet.toTop.obj X :=
  (toTopLevelwiseDiscreteNatIso.app (SimplicialObject.opFunctor.obj X)) ≪≫
    (TopCat.simplicialRealization.mapIso (levelwiseDiscreteOpIso X)) ≪≫
      (TopCat.SimplicialRealization.opIso (levelwiseDiscrete.obj X)) ≪≫
        (toTopLevelwiseDiscreteNatIso.app X).symm

/-- Naturality of realization reversal. -/
theorem toTopReversalIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
        (toTopReversalIso Y).hom =
      (toTopReversalIso X).hom ≫ SSet.toTop.map f := by
  have hmap := levelwiseDiscrete_map_opFunctor_map f
  have htop : SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) =
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
        TopCat.simplicialRealization.map
          (levelwiseDiscrete.map (SimplicialObject.opFunctor.map f)) :=
    toTopLevelwiseDiscreteNatIso.hom.naturality _
  have hop := TopCat.SimplicialRealization.opIso_naturality
    (levelwiseDiscrete.map f)
  have hinv : TopCat.simplicialRealization.map (levelwiseDiscrete.map f) ≫
      toTopDiscreteBwd Y =
      toTopDiscreteBwd X ≫ SSet.toTop.map f :=
    toTopLevelwiseDiscreteNatIso.symm.hom.naturality f
  have hbX : toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso X)).hom =
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) := by
    have h : (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso X)).hom = 𝟙 _ := by
      rw [Functor.mapIso_hom, levelwiseDiscreteOpIso_hom]
      exact CategoryTheory.Functor.map_id _ _
    rw [h]
    exact Category.comp_id _
  have hbY : toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso Y)).hom =
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) := by
    have h : (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso Y)).hom = 𝟙 _ := by
      rw [Functor.mapIso_hom, levelwiseDiscreteOpIso_hom]
      exact CategoryTheory.Functor.map_id _ _
    rw [h]
    exact Category.comp_id _
  have hbY' : ((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso Y)).hom) =
      (SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) := by
    have e1 : ((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
            toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
            (TopCat.simplicialRealization.mapIso
              (levelwiseDiscreteOpIso Y)).hom) =
            SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
            (toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) ≫
            (TopCat.simplicialRealization.mapIso
              (levelwiseDiscreteOpIso Y)).hom) :=
          Category.assoc _ _ _
    have e2 : SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
            (toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) ≫
            (TopCat.simplicialRealization.mapIso
              (levelwiseDiscreteOpIso Y)).hom) =
            SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
            toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y) :=
          congrArg
            (fun g => SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫ g)
            hbY
    exact Eq.trans e1 e2
  have hopStep' :
      ((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
        TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map
          (levelwiseDiscrete.map f))) ≫
        (TopCat.SimplicialRealization.opIso
          (levelwiseDiscrete.obj Y)).hom) =
      ((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
        (TopCat.SimplicialRealization.opIso
          (levelwiseDiscrete.obj X)).hom) ≫
        TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) :=
    calc ((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map
              (levelwiseDiscrete.map f))) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj Y)).hom)
        = toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map
              (levelwiseDiscrete.map f)) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj Y)).hom) :=
          Category.assoc _ _ _
      _ = toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            ((TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom ≫
            TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) :=
          congrArg
            (fun g => toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫ g)
            hop
      _ = ((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom) ≫
            TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) :=
          (Category.assoc _ _ _).symm
  have hinvStep' :
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
        (TopCat.SimplicialRealization.opIso
          (levelwiseDiscrete.obj X)).hom) ≫
        TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) ≫
        toTopDiscreteBwd Y) =
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
        (TopCat.SimplicialRealization.opIso
          (levelwiseDiscrete.obj X)).hom) ≫
        toTopDiscreteBwd X) ≫
      SSet.toTop.map f) :=
    calc (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom) ≫
            TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) ≫
            toTopDiscreteBwd Y)
        = (toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom) ≫
            (TopCat.simplicialRealization.map (levelwiseDiscrete.map f) ≫
            toTopDiscreteBwd Y) :=
          Category.assoc _ _ _
      _ = (toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom) ≫
            (toTopDiscreteBwd X ≫ SSet.toTop.map f) :=
          congrArg
            (fun g => (toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
              (TopCat.SimplicialRealization.opIso
                (levelwiseDiscrete.obj X)).hom) ≫ g)
            hinv
      _ = (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
            (TopCat.SimplicialRealization.opIso
              (levelwiseDiscrete.obj X)).hom) ≫
            toTopDiscreteBwd X) ≫
          SSet.toTop.map f) :=
          (Category.assoc _ _ _).symm
  unfold toTopReversalIso
  simp only [Iso.trans_hom]
  repeat rw [← Category.assoc]
  change ((((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso Y)).hom) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
    toTopDiscreteBwd Y) =
    ((((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso X)).hom) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
    toTopDiscreteBwd X) ≫
    SSet.toTop.map f)
  -- Each step is restated freshly: `rw [hmap]` would transplant a morphism
  -- whose type is only semireducibly defeq, poisoning later `rw` matches.
  have e1 : ((((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso Y)).hom) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) =
      (((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) :=
    congrArg (fun g => ((g ≫ (TopCat.SimplicialRealization.opIso
      (levelwiseDiscrete.obj Y)).hom) ≫ toTopDiscreteBwd Y)) hbY'
  have e2 : (((SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
      toTopDiscreteFwd (SimplicialObject.opFunctor.obj Y)) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) =
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      TopCat.simplicialRealization.map
        (levelwiseDiscrete.map (SimplicialObject.opFunctor.map f))) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) :=
    congrArg (fun g => ((g ≫ (TopCat.SimplicialRealization.opIso
      (levelwiseDiscrete.obj Y)).hom) ≫ toTopDiscreteBwd Y)) htop
  have e3 : (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      TopCat.simplicialRealization.map
        (levelwiseDiscrete.map (SimplicialObject.opFunctor.map f))) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) =
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map
        (levelwiseDiscrete.map f))) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) :=
    congrArg (fun g => (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      TopCat.simplicialRealization.map g) ≫ (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫ toTopDiscreteBwd Y)) hmap
  have e4 : (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      TopCat.simplicialRealization.map (SimplicialObject.opFunctor.map
        (levelwiseDiscrete.map f))) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj Y)).hom) ≫
      toTopDiscreteBwd Y) =
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
      TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) ≫
      toTopDiscreteBwd Y) :=
    congrArg (fun g => (g ≫ toTopDiscreteBwd Y)) hopStep'
  have e5 : (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
      TopCat.simplicialRealization.map (levelwiseDiscrete.map f)) ≫
      toTopDiscreteBwd Y) =
      (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
      toTopDiscreteBwd X) ≫
      SSet.toTop.map f) :=
    hinvStep'
  have e6 : (((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
      toTopDiscreteBwd X) ≫
      SSet.toTop.map f) =
      ((((toTopDiscreteFwd (SimplicialObject.opFunctor.obj X) ≫
      (TopCat.simplicialRealization.mapIso
        (levelwiseDiscreteOpIso X)).hom) ≫
      (TopCat.SimplicialRealization.opIso
        (levelwiseDiscrete.obj X)).hom) ≫
      toTopDiscreteBwd X) ≫
      SSet.toTop.map f) :=
    congrArg (fun g => ((((g ≫ (TopCat.SimplicialRealization.opIso
      (levelwiseDiscrete.obj X)).hom) ≫ toTopDiscreteBwd X) ≫
      SSet.toTop.map f))) hbX.symm
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

/-- Naturality of the inverse realization-reversal iso. -/
theorem toTopReversalIso_inv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map f ≫ (toTopReversalIso Y).inv =
      (toTopReversalIso X).inv ≫
        SSet.toTop.map (SimplicialObject.opFunctor.map f) := by
  have h := toTopReversalIso_naturality f
  have h2 : (toTopReversalIso X).hom ≫
        (SSet.toTop.map f ≫ (toTopReversalIso Y).inv) =
      (toTopReversalIso X).hom ≫ ((toTopReversalIso X).inv ≫
        SSet.toTop.map (SimplicialObject.opFunctor.map f)) := by
    calc (toTopReversalIso X).hom ≫ (SSet.toTop.map f ≫ (toTopReversalIso Y).inv)
        = ((toTopReversalIso X).hom ≫ SSet.toTop.map f) ≫
            (toTopReversalIso Y).inv := by
          rw [← Category.assoc]
      _ = (SSet.toTop.map (SimplicialObject.opFunctor.map f) ≫
            (toTopReversalIso Y).hom) ≫ (toTopReversalIso Y).inv := by
          rw [← h]
      _ = SSet.toTop.map (SimplicialObject.opFunctor.map f) := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (toTopReversalIso X).hom ≫ ((toTopReversalIso X).inv ≫
          SSet.toTop.map (SimplicialObject.opFunctor.map f)) := by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (cancel_epi (toTopReversalIso X).hom).mp h2

/-- A reversed map realizes to a weak homotopy equivalence whenever the
original map does. -/
theorem toTopReversal_mem_weakHomotopyEquivalences {X Y : SSet.{u}}
    (f : X ⟶ Y)
    (h : TopCat.weakHomotopyEquivalences (SSet.toTop.map f)) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (SimplicialObject.opFunctor.map f)) := by
  have hnat := toTopReversalIso_naturality f
  have heq : SSet.toTop.map (SimplicialObject.opFunctor.map f) =
      (toTopReversalIso X).hom ≫
        (SSet.toTop.map f ≫ (toTopReversalIso Y).inv) := by
    have hcomp := congrArg (· ≫ (toTopReversalIso Y).inv) hnat
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hcomp
    exact hcomp
  rw [heq]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.comp_mem _ _ h
      (TopCat.weakHomotopyEquivalences.of_isIso _))

/-- Realized weak-equivalence status is unchanged by simplicial reversal. -/
theorem toTopReversal_mem_weakHomotopyEquivalences_iff {X Y : SSet.{u}}
    (f : X ⟶ Y) :
    TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (SimplicialObject.opFunctor.map f)) ↔
      TopCat.weakHomotopyEquivalences (SSet.toTop.map f) := by
  refine ⟨fun h => ?_, fun h => toTopReversal_mem_weakHomotopyEquivalences f h⟩
  have hdouble := toTopReversal_mem_weakHomotopyEquivalences
    (SimplicialObject.opFunctor.map f) h
  have hnat := SimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have hmap := congrArg SSet.toTop.map hnat
  simp only [Functor.map_comp] at hmap
  have heq : SSet.toTop.map f =
      SSet.toTop.map
          (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X) ≫
        (SSet.toTop.map (SimplicialObject.opFunctor.map
          (SimplicialObject.opFunctor.map f)) ≫
          SSet.toTop.map
            (SimplicialObject.opFunctorCompOpFunctorIso.hom.app Y)) := by
    calc SSet.toTop.map f
        = 𝟙 _ ≫ SSet.toTop.map f := (Category.id_comp _).symm
      _ = SSet.toTop.map (𝟙 _) ≫ SSet.toTop.map f := by
          rw [CategoryTheory.Functor.map_id]
      _ = SSet.toTop.map
            (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X ≫
              SimplicialObject.opFunctorCompOpFunctorIso.hom.app X) ≫
            SSet.toTop.map f := by
          rw [Iso.inv_hom_id_app]
          rfl
      _ = (SSet.toTop.map
              (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X) ≫
            SSet.toTop.map
              (SimplicialObject.opFunctorCompOpFunctorIso.hom.app X)) ≫
            SSet.toTop.map f := by
          rw [Functor.map_comp]
      _ = SSet.toTop.map
              (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X) ≫
            (SSet.toTop.map
              (SimplicialObject.opFunctorCompOpFunctorIso.hom.app X) ≫
              SSet.toTop.map f) := by
          rw [Category.assoc]
      _ = SSet.toTop.map
              (SimplicialObject.opFunctorCompOpFunctorIso.inv.app X) ≫
            (SSet.toTop.map (SimplicialObject.opFunctor.map
              (SimplicialObject.opFunctor.map f)) ≫
              SSet.toTop.map
                (SimplicialObject.opFunctorCompOpFunctorIso.hom.app Y)) := by
          rw [← hmap]
  rw [heq]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.comp_mem _ _ hdouble
      (TopCat.weakHomotopyEquivalences.of_isIso _))

/-- The vertex of the reversed simplicial set corresponding to `x`
(explicit implicits, since they cannot be inferred from `x`). -/
abbrev opVertex {X : SSet.{u}} (x : X _⦋0⦌) :
    (SimplicialObject.opFunctor.obj X) _⦋0⦌ :=
  (SimplicialObject.opObjIso (X := SimplicialObject.opFunctor.obj X)
    (n := op ⦋0⦌)).hom x

/-- The reversal iso fixes realized vertices, up to the opposite
identification of vertices. By naturality for the constant map out of
`Δ[0]`, both sides reduce to the unique point of `|Δ[0]|`. -/
theorem toTopReversalIso_realizedVertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopReversalIso X).hom (realizedVertex (opVertex x)) =
      realizedVertex x := by
  have hconst : ∀ v : (Δ[0] : SSet.{u}) _⦋0⦌, (SSet.const x).app _ v = x :=
    fun v => by
      simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
        CategoryTheory.Functor.map_id, CategoryTheory.id_apply, TypeCat.hom_ofHom,
        TypeCat.Fun.mk_apply]
  have hnat :=
    toTopReversalIso_naturality (SSet.const (X := (Δ[0] : SSet.{u})) x)
  set v0 := SSet.stdSimplex.const 0 0 (op ⦋0⦌)
  have happ := congrArg (fun g => g (realizedVertex (opVertex v0))) hnat
  simp only [TopCat.comp_app] at happ
  have hL : SSet.toTop.map (SimplicialObject.opFunctor.map (SSet.const x))
      (realizedVertex (opVertex v0)) =
      realizedVertex (opVertex x) := by
    rw [← realizedVertex_naturality]
    congr 1
    rw [SimplicialObject.opFunctor_map_app]
    change (SSet.const x).app _ v0 = x
    exact hconst v0
  have hR : (toTopReversalIso (Δ[0] : SSet.{u})).hom
      (realizedVertex (opVertex v0)) =
      (default : SSet.toTop.obj (Δ[0] : SSet.{u})) :=
    Subsingleton.elim _ _
  rw [hL, hR] at happ
  conv_rhs => rw [realizedVertex_eq_const]
  exact happ

namespace OppositeRealization

/-- Reversal preserves and reflects the same realization-weak morphism property. -/
theorem realizationWeakEquivalences_op_map_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.realizationWeakEquivalences (SimplicialObject.opFunctor.map f) ↔
      SSet.realizationWeakEquivalences f := by
  change TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (SimplicialObject.opFunctor.map f)) ↔
    TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact SSet.toTopReversal_mem_weakHomotopyEquivalences_iff f

end OppositeRealization

end SSet

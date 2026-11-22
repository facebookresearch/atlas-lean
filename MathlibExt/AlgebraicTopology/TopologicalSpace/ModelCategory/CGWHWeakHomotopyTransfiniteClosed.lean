/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteUnconditional
public import Mathlib.Order.Shrink

/-!
# Native closed transfinite weak-equivalence closure

The actual native injective-colimit comparison sends a continuous CGWH
diagram with closed successor embeddings to its included topological
diagram. The CGWH codomains are T1, so those maps are closed-T1 embeddings.
Unconditional topological closure and creation of native weak equivalences
give endpoint closure. Order-isomorphic shrinking covers every shape in a
same or smaller carrier universe while retaining the independent compact
probe universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory Limits Topology

namespace CGWH

private theorem weakHomotopyEquivalences_of_transfiniteComposition_closed_sameUniverse
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : (weakHomotopyEquivalences ⊓
      TopCat.closedEmbeddings.inverseImage cgwhToTop).TransfiniteCompositionOfShape J f) :
    weakHomotopyEquivalences f := by
  let j := cgwhToCompactlyGenerated.{u, v}
  let k := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let T := cgwhToTop.{u, v}
  let _ : hf.F.IsWellOrderContinuous :=
    hf.toTransfiniteCompositionOfShape.isWellOrderContinuous
  have hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (j.map (hf.F.map (homOfLE (Order.le_succ a)))).hom := by
    intro a ha
    change Function.Injective
      (T.map (hf.F.map (homOfLE (Order.le_succ a)))).hom
    exact ((TopCat.closedEmbeddings_iff _).1 (hf.map_mem a ha).2).injective
  let cCG : CategoryTheory.TransfiniteCompositionOfShape J (j.map f) :=
    { F := hf.F ⋙ j
      isoBot := j.mapIso hf.isoBot
      isWellOrderContinuous := by
        constructor
        intro m hm
        let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
        let _ : OrderBot (Set.Iio m) :=
          { bot := ⟨⊥, hm.bot_lt⟩
            bot_le := fun _ => bot_le }
        let _ : IsFiltered (Set.Iio m) := by infer_instance
        let pInit : Set.Iio m ≤i J :=
          { toRelEmbedding := (Set.principalSegIio m).toRelEmbedding
            mem_range_of_rel' := by
              intro a b hb
              exact ⟨⟨b, hb.trans a.property⟩, rfl⟩ }
        let R := (Set.principalSegIio m).monotone.functor ⋙ hf.F
        let _ : R.IsWellOrderContinuous := by
          change (pInit.monotone.functor ⋙ hf.F).IsWellOrderContinuous
          infer_instance
        have hR : ∀ ⦃a b : Set.Iio m⦄ (g : a ⟶ b), Function.Injective
            (j.map (R.map g)).hom := by
          intro a b g
          change Function.Injective
            (j.map (hf.F.map
              ((Set.principalSegIio m).monotone.functor.map g))).hom
          have hg : (Set.principalSegIio m).monotone.functor.map g =
              homOfLE (leOfHom g) := Subsingleton.elim _ _
          rw [hg]
          exact injective_map_of_injective_succ hf.F hSucc _
        refine ⟨isColimitMapCoconeOfInjectiveSucc R
          (fun a ha => hR (homOfLE (Order.le_succ a)))
          ((Set.principalSegIio m).cocone hf.F)
          (hf.F.isColimitOfIsWellOrderContinuous m hm)⟩
      incl := Functor.whiskerRight hf.incl j ≫
        (Functor.constComp _ _ _).hom
      isColimit := isColimitMapCoconeOfInjectiveSucc hf.F hSucc
        (Cocone.mk _ hf.incl) hf.isColimit
      fac := by
        dsimp [j]
        simp [← Functor.map_comp] }
  let _ : PreservesWellOrderContinuousOfShape J k :=
    { preservesColimitsOfShape := fun _ _ ↦ by infer_instance }
  let cTop := cCG.map k
  let hmap :
      (TopCat.weakHomotopyEquivalences ⊓
        TopCat.closedT1Embeddings).TransfiniteCompositionOfShape J (T.map f) :=
    { __ := cTop
      map_mem := fun a ha => by
        constructor
        · change TopCat.weakHomotopyEquivalences
            (T.map (hf.F.map (homOfLE (Order.le_succ a))))
          exact (hf.map_mem a ha).1
        · change Topology.IsClosedT1Embedding
            (T.map (hf.F.map (homOfLE (Order.le_succ a)))).hom
          exact
            { toIsClosedEmbedding :=
                (TopCat.closedEmbeddings_iff _).1 (hf.map_mem a ha).2
              isClosed_singleton_of_notMem_range := by
                intro y _hy
                change IsClosed ({y} : Set (hf.F.obj (Order.succ a)))
                exact isClosed_singleton } }
  change TopCat.weakHomotopyEquivalences (T.map f)
  exact
    TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1_unconditional.{v, v} hmap

/-- An actual continuous native transfinite composition of weak homotopy
equivalences and closed embeddings is a weak homotopy equivalence when the
shape universe is no larger than the carrier universe. The compact probe
universe remains independent. -/
theorem weakHomotopyEquivalences.of_transfiniteComposition_closed
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [UnivLE.{w, v}]
    {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : (weakHomotopyEquivalences ⊓
      TopCat.closedEmbeddings.inverseImage cgwhToTop).TransfiniteCompositionOfShape J f) :
    weakHomotopyEquivalences f := by
  exact weakHomotopyEquivalences_of_transfiniteComposition_closed_sameUniverse
    (hf.ofOrderIso (orderIsoShrink.{v} J).symm)

end CGWH

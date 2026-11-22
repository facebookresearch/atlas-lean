/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundaryCountableTestChain

/-!
# The SAME actual original countable union solves every original boundary test

Finite presentability factors each whole original test through an actual
stage. The proved next-stage original lift and the full union cocone
supply its genuine original square lift. The SAME native horn right
factor therefore has every original boundary lift; its actual weak unit
proves weakness of the unchanged original union terminal map.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestUnionWeak
open OriginalBoundaryGoodTree OriginalBoundaryCountableTestEnlargement
variable {O : Type u} [Countable O] {C D : FixedObjects O} [CountableHoms C] (f : C ⟶ D)
variable (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))

/-- Every full original boundary generator lifts against the SAME actual final native right factor. -/
theorem boundary_lifting (i : (boundaryFamily O).toSet) :
    HasLiftingProperty i.val.hom
      (OriginalFibrantReplacement.right O (piece f (OriginalBoundaryCountableTestChain.finalSupport f hD))) := by
  let K := OriginalBoundaryCountableTestChain.replacedDiagram f hD
  let c := OriginalBoundaryCountableTestChain.replacedCocone f hD
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  let _ : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).mpr inferInstance
  let _ : IsFinitelyPresentable.{u} i.val.left :=
    (OriginalBoundaryFiniteTestDescent.boundary_ends_presentable i).1
  refine ⟨fun {top} {bottom} sq => ?_⟩
  obtain ⟨n, topn, htop⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0.{u} (OriginalBoundaryCountableTestChain.replacedIsColimit f hD) top
  obtain ⟨l, hl, _hr⟩ := step_has_lift f hD
    (OriginalBoundaryCountableTestChain.stages f hD n) ⟨i, topn⟩
  have hl' : i.val.hom ≫ l = topn ≫ K.map (homOfLE (Nat.le_succ n)) := by
    exact (hl.trans (congrArg (fun k => topn ≫ k)
      (OriginalBoundaryCountableTestChain.replacedDiagram_succ f hD n).symm))
  exact CommSq.HasLift.mk'
    { l := l ≫ c.ι.app (n + 1)
      fac_left := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ c.ι.app (n + 1)) hl').trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => topn ≫ k) (c.w (homOfLE (Nat.le_succ n)))).trans htop)))
      fac_right := CodiscreteTerminal.isTerminal.hom_ext _ _ }

/-- The full original boundary right-lifting class contains the SAME actual final native right factor. -/
theorem right_boundary_rlp :
    (boundaryFamily O).rlp
      (OriginalFibrantReplacement.right O (piece f (OriginalBoundaryCountableTestChain.finalSupport f hD))) := by
  intro A B i hi
  exact boundary_lifting f hD ⟨Arrow.mk i, hi⟩

/-- The SAME actual original countable union terminal map is genuinely weak on every complete original Hom. -/
theorem terminal_weak :
    FixedObjectModel.weakEquivalences O
      (CodiscreteTerminal.toTerminal (piece f (OriginalBoundaryCountableTestChain.finalSupport f hD))) :=
  (OriginalFibrantReplacement.right_boundary_rlp_iff O _).mp (right_boundary_rlp f hD)

/-- The actual final union retains countable full Homs, without a countable original target premise. -/
theorem countableHoms :
    CountableHoms (piece f (OriginalBoundaryCountableTestChain.finalSupport f hD)) :=
  piece_countableHoms f _

/-- The SAME actual final source inclusion is genuinely cofibrant in the full original fixed-label model. -/
theorem root_cofibration :
    FixedObjectModel.cofibrations O
      (OriginalBoundaryGoodTree.root f (OriginalBoundaryCountableTestChain.finalSupport f hD)) :=
  OriginalBoundaryGoodTree.root_cofibration f _

/-- The full unchanged original input map factors through this SAME actual weak countable union. -/
theorem root_toOriginal :
    OriginalBoundaryGoodTree.root f (OriginalBoundaryCountableTestChain.finalSupport f hD) ≫
      OriginalBoundaryGoodTree.toOriginal f (OriginalBoundaryCountableTestChain.finalSupport f hD) = f :=
  OriginalBoundaryGoodTree.root_toOriginal f _

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestUnionWeak

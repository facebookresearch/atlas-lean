/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundaryFiniteTestDescent
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHornIterationCountability

/-!
# One original countable support contains actual lifts of every original boundary test

Every original ordered-pair and dimension test is kept. Countability of
the SAME full replaced piece counts all whole top maps, including degree
zero and reverse-Hom tests. Actual finite lift descent supplies its real
supports and maps; their countable union gives the SAME original later
support, including the empty test family without a nonemptiness premise.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestEnlargement
open OriginalBoundaryGoodTree OriginalBoundarySupportDiagram OriginalBoundaryFiniteTestDescent
variable {O : Type u} {C D : FixedObjects O} (f : C ⟶ D)

/-- Every full original boundary test consists of its actual original generator and entire original top map. -/
abbrev Tests (B : Supports f) : Type (u + 1) :=
  Σ i : (boundaryFamily O).toSet, i.val.left ⟶ (replacedDiagram f).obj B

/-- The actual original support and full lift maps derived by finite descent for one original test. -/
structure LiftData (B : Supports f) (t : Tests f B) where
  /-- The actual countable original lower support containing the derived lift. -/
  support : Supports f
  /-- The SAME actual original source-support inclusion. -/
  toSupport : B ⟶ support
  /-- The whole actual original free-simplex lift. -/
  lift : t.1.val.right ⟶ (replacedDiagram f).obj support
  /-- Every original boundary map is retained by its full equality. -/
  boundary : t.1.val.hom ≫ lift = t.2 ≫ (replacedDiagram f).map toSupport
  /-- The full original terminal-map equation retains its actual native right factor. -/
  terminal : lift ≫ OriginalFibrantReplacement.right O ((diagram f).obj support) =
    CodiscreteTerminal.toTerminal t.1.val.right

/-- Actual finite original test descent constructs this data, without an assumed lift or support. -/
def liftData (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) (t : Tests f B) : LiftData f B t := by
  apply Classical.choice
  obtain ⟨E, g, l, hl, hr⟩ := OriginalBoundaryFiniteTestDescent.exists_lift f hD B t.1 t.2
  exact ⟨⟨E, g, l, hl, hr⟩⟩

variable [Countable O] [CountableHoms C]

/-- ALL actual original boundary tests over the SAME full replaced piece are countable. -/
instance tests_countable (B : Supports f) : Countable (Tests f B) := by
  let _ : CountableHoms (piece f B) := piece_countableHoms f B
  let _ : CountableHoms ((replacedDiagram f).obj B) :=
    originalFibrantReplacement_countableHoms (piece f B)
  let _ : ∀ i : (boundaryFamily O).toSet, Countable (i.val.left ⟶ (replacedDiagram f).obj B) :=
    fun i => boundaryFamily_top_maps_countable _ i
  infer_instance

/-- The entire original test family has its actual bound below ℵ₁ in its independent carrier universe. -/
theorem tests_bound (B : Supports f) : HasCardinalLT (Tests f B) rank.{u} := by
  obtain ⟨e, he⟩ := exists_injective_nat (Tests f B)
  exact (GoodOrderBounds.natLt rank Cardinal.aleph0_lt_aleph_one).of_injective e he

/-- The SAME actual chosen supports of the proved original finite lifts. -/
def supports (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) : Tests f B → Supports f := fun t => (liftData f hD B t).support

/-- The actual countable union of original derived lift supports, retaining the entire original source support. -/
def step (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) : Supports f := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.union rank B
    (BoundedLowerSupport.indexedUnion rank (supports f hD B) (tests_bound f B))

/-- The SAME original source support is retained even when its original test family is empty. -/
theorem le_step (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) : B ≤ step f hD B := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact BoundedLowerSupport.le_union_left rank B _

/-- Every actual original derived lift support is included with all of its original cells. -/
theorem support_le_step (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) (t : Tests f B) : (liftData f hD B t).support ≤ step f hD B := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact (BoundedLowerSupport.le_indexedUnion rank (supports f hD B) (tests_bound f B) t).trans
    (BoundedLowerSupport.le_union_right rank B _)

/-- ALL original boundary tests have their SAME full lifts on the actual countable next support. -/
theorem step_has_lift (hD : FixedObjectModel.weakEquivalences O (CodiscreteTerminal.toTerminal D))
    (B : Supports f) (t : Tests f B) :
    ∃ l : t.1.val.right ⟶ (replacedDiagram f).obj (step f hD B),
      t.1.val.hom ≫ l = t.2 ≫ (replacedDiagram f).map (homOfLE (le_step f hD B)) ∧
      l ≫ OriginalFibrantReplacement.right O ((diagram f).obj (step f hD B)) =
        CodiscreteTerminal.toTerminal t.1.val.right := by
  let H := liftData f hD B t
  let g : H.support ⟶ step f hD B := homOfLE (support_le_step f hD B t)
  refine ⟨H.lift ≫ (replacedDiagram f).map g, ?_, CodiscreteTerminal.isTerminal.hom_ext _ _⟩
  have hg : H.toSupport ≫ g = homOfLE (le_step f hD B) := Subsingleton.elim _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (replacedDiagram f).map g) H.boundary).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => t.2 ≫ k) ((replacedDiagram f).map_comp H.toSupport g).symm).trans
          (congrArg (fun k => t.2 ≫ (replacedDiagram f).map k) hg))))

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryCountableTestEnlargement

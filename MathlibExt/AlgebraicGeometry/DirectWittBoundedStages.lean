/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
public import MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Direct bounded W(R) subfunctors and their native space stages

The direct bounded subfunctor uses the two original p-power inclusions
inside W(R)[1/p]^n. Its maps are the original direct Witt scalar maps,
and increasing transitions leave the lattice unchanged. The tensor/direct
point dictionaries are computed from the proved coefficient equivalence
and the normalized lattice transport.

The direct space stages are precisely the existing native proper
ind-perfection stages, with their actual closed maps. Only their point
dictionary is transported to the original W(R) lattice functor. Their
ind-comparison composes the original colimit realization with this same
native coefficient dictionary.

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), Theorem 0.1,
and Section 1.2.1. No new representability theorem is assumed or requested.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DirectWittBoundedStages

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeWittLoopTests RelativeWittLatticeModels RelativeWittSpaceStages
open RelativeWittIndRealizations RelativeWittUnramifiedNormalization
open MathlibExt.LinearAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (n : ℕ)
  (M : UnramifiedModel p k n)

/-- The tensor/direct full point dictionary is the original lattice transport. -/
def functorIso : M.extension.functor ≅ M.functor :=
  NatIso.ofComponents (fun R ↦
    (show ULift.{1} (RelativeWittLatticeModels.Lattice p k (WittVector p k)
        (p : WittVector p k) R n) ≃ ULift.{1} (WittLattice p k R n) from
      { toFun := fun L ↦ ULift.up (M.comparison.lattice R L.down)
        invFun := fun L ↦ ULift.up ((M.comparison.lattice R).symm L.down)
        left_inv := fun L ↦ ULift.ext ((M.comparison.lattice R).symm_apply_apply L.down)
        right_inv := fun L ↦ ULift.ext ((M.comparison.lattice R).apply_symm_apply L.down) }).toIso)
    (by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro L
      apply ULift.ext
      change M.comparison.lattice S (M.extension.map f L.down) =
        M.comparison.lattice S (M.extension.map f
          ((M.comparison.lattice R).symm (M.comparison.lattice R L.down)))
      rw [Equiv.symm_apply_apply])

/-- The actual bounded direct-Witt subfunctor, with no geometric predicate oracle. -/
def boundedSubfunctor (N : ℕ) : Subfunctor M.functor where
  obj R := {L | LocalizedLattices.IsBoundedBy _ _ _ L.down N}
  map {R S} f L h := by
    let A := (M.comparison.lattice R).symm L.down
    have hA : LocalizedLattices.IsBoundedBy _ _ _ A N :=
      (M.comparison.bounds R A N).mpr (by
        change LocalizedLattices.IsBoundedBy _ _ _
          (M.comparison.lattice R ((M.comparison.lattice R).symm L.down)) N
        rw [Equiv.apply_symm_apply]
        exact h)
    exact (M.comparison.bounds S (M.extension.map f A) N).mp
      (M.extension.bounded f A N hA)

/-- The direct bounded functor inherits the original scalar map. -/
def boundedFunctor (N : ℕ) := (boundedSubfunctor p k n M N).toFunctor

/-- The original full lattice is unchanged by the bounded inclusion. -/
def boundedInclusion (N : ℕ) : boundedFunctor p k n M N ⟶ M.functor :=
  (boundedSubfunctor p k n M N).ι

/-- Increasing the bound leaves the actual direct lattice unchanged. -/
theorem boundedSubfunctor_le {N L : ℕ} (h : N ≤ L) :
    boundedSubfunctor p k n M N ≤ boundedSubfunctor p k n M L := by
  intro R A hA
  let B := (M.comparison.lattice R).symm A.down
  have hB : LocalizedLattices.IsBoundedBy _ _ _ B N :=
    (M.comparison.bounds R B N).mpr (by
      change LocalizedLattices.IsBoundedBy _ _ _
        (M.comparison.lattice R ((M.comparison.lattice R).symm A.down)) N
      rw [Equiv.apply_symm_apply]
      exact hA)
  have hL := (M.comparison.bounds R B L).mp (M.extension.increasing R B h hB)
  change LocalizedLattices.IsBoundedBy _ _ _ A.down L
  simpa only [B, Equiv.apply_symm_apply] using hL

/-- The actual increasing bounded transition is the native subfunctor inclusion. -/
def boundedTransition {N L : ℕ} (h : N ≤ L) :
    boundedFunctor p k n M N ⟶ boundedFunctor p k n M L :=
  Subfunctor.homOfLe (boundedSubfunctor_le p k n M h)

/-- Bounded point dictionaries retain both original p-power bounds. -/
def boundedEquiv (N : ℕ) (R : PerfectAlgebra p k) :
    ULift.{1} (RelativeWittLatticeModels.BoundedLattice p k (WittVector p k)
      (p : WittVector p k) R n N) ≃ (boundedFunctor p k n M N).obj R where
  toFun L := ⟨ULift.up (M.comparison.lattice R L.down.val),
    (M.comparison.bounds R L.down.val N).mp L.down.property⟩
  invFun L := ULift.up
    ⟨(M.comparison.lattice R).symm L.val.down,
      (M.comparison.bounds R ((M.comparison.lattice R).symm L.val.down) N).mpr (by
        rw [Equiv.apply_symm_apply]
        exact L.property)⟩
  left_inv L := by
    apply ULift.ext
    apply Subtype.ext
    exact (M.comparison.lattice R).symm_apply_apply L.down.val
  right_inv L := by
    apply Subtype.ext
    apply ULift.ext
    exact (M.comparison.lattice R).apply_symm_apply L.val.down

/-- The bounded dictionary is natural for the actual original Witt maps. -/
def boundedIso (N : ℕ) : M.extension.boundedFunctor N ≅ boundedFunctor p k n M N :=
  NatIso.ofComponents (fun R ↦ (boundedEquiv p k n M N R).toIso) (by
    intro R S f
    apply ConcreteCategory.hom_ext
    intro L
    apply Subtype.ext
    apply ULift.ext
    change M.comparison.lattice S (M.extension.map f L.down.val) =
      M.comparison.lattice S (M.extension.map f
        ((M.comparison.lattice R).symm (M.comparison.lattice R L.down.val)))
    rw [Equiv.symm_apply_apply])

/-- The full and bounded dictionaries preserve the same actual lattice inclusion. -/
theorem boundedIso_inclusion (N : ℕ) :
    (boundedIso p k n M N).hom ≫ boundedInclusion p k n M N =
      RelativeWittIndRealizations.boundedInclusion M.extension N ≫
        (functorIso p k n M).hom := by
  apply NatTrans.ext
  funext R
  apply ConcreteCategory.hom_ext
  intro L
  rfl

/-- The direct bounded dictionary preserves every original increasing transition. -/
theorem boundedIso_transition {N L : ℕ} (h : N ≤ L) :
    M.extension.transition h ≫ (boundedIso p k n M L).hom =
      (boundedIso p k n M N).hom ≫ boundedTransition p k n M h := by
  apply NatTrans.ext
  funext R
  apply ConcreteCategory.hom_ext
  intro A
  apply Subtype.ext
  rfl

variable (S : IndLatticeStages p k (WittVector p k) (p : WittVector p k) n M.extension)

/-- Direct points use the same original proper perfect-space stage. -/
def stagePoints (N : ℕ) : boundedFunctor p k n M N ≅
    spacePoints p k (S.stage N).perfection.space :=
  (boundedIso p k n M N).symm ≪≫ (S.stage N).points

/-- Native closed space transitions retain the exact direct-Witt point square. -/
theorem stagePoints_transition {N L : ℕ} (h : N ≤ L) :
    boundedTransition p k n M h ≫ (stagePoints p k n M S L).hom =
      (stagePoints p k n M S N).hom ≫ spacePointMap p k (S.transition h) := by
  apply (cancel_epi (boundedIso p k n M N).hom).mp
  simp only [stagePoints, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← boundedIso_transition, Category.assoc,
    Iso.hom_inv_id_assoc, S.normalized, ← Category.assoc, Iso.hom_inv_id_assoc]

/-- Native ind-realization to the original direct W(R) lattice sheaf. -/
def indComparison (I : IndRealization S) :
    colimit (spaceSheafDiagram S) ≅ (sheafification p k).obj M.functor :=
  I.comparison ≪≫ (sheafification p k).mapIso (functorIso p k n M)

/-- Every direct ind-insertion remains the actual bounded-lattice inclusion. -/
theorem indComparison_normalized (I : IndRealization S) (N : ℕ) :
    colimit.ι (spaceSheafDiagram S) N ≫ (indComparison p k n M S I).hom =
      (sheafification p k).map (stagePoints p k n M S N).inv ≫
        (sheafification p k).map (boundedInclusion p k n M N) := by
  change colimit.ι (spaceSheafDiagram S) N ≫ I.comparison.hom ≫
    (sheafification p k).map (functorIso p k n M).hom = _
  rw [← Category.assoc, I.normalized]
  change (sheafification p k).map (S.stage N).points.inv ≫
    (sheafification p k).map (RelativeWittIndRealizations.boundedInclusion M.extension N) ≫
      (sheafification p k).map (functorIso p k n M).hom = _
  rw [← _root_.CategoryTheory.Functor.map_comp,
    ← boundedIso_inclusion, _root_.CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← _root_.CategoryTheory.Functor.map_comp]
  rfl

end MathlibExt.AlgebraicGeometry.DirectWittBoundedStages

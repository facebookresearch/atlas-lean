/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSet
public import MathlibExt.AlgebraicTopology.SingularHomology.SingularSubdivision.QuasiIso
public import MathlibExt.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Two-set small-chain quasi-isomorphism

Coefficient-natural quasi-isomorphism for the `smallCoverBoth` cover and its
evaluation at a fixed coefficient group.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u z

/-- The two-set small-chain inclusion is a coefficient-natural
quasi-isomorphism in any abelian category with a projective finitely
presentable separator. -/
theorem smallChainInclusionNatTrans_twoSet_quasiIsoULift
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    {X : TopCat.{w}} (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    (HomologicalComplex.quasiIso C (ComplexShape.down ℕ)).functorCategory C
      (smallChainInclusionNatTrans C (smallCoverBoth A B)) := by
  intro R
  refine smallChain_inclusion_quasiIsoULift_of_open_refinement R G hG
    (fun b : Bool => interior (smallCoverBoth A B b))
    (smallCoverBoth A B) ?_ ?_ ?_
  · intro b
    exact isOpen_interior
  · intro x hx
    rcases hcover hx with hxA | hxB
    · exact Set.mem_iUnion.mpr
        ⟨true, by simpa [smallCoverBoth] using hxA⟩
    · exact Set.mem_iUnion.mpr
        ⟨false, by simpa [smallCoverBoth] using hxB⟩
  · apply subordinateCover_mono
    intro b
    exact ⟨b, interior_subset⟩

/-- The fixed-coefficient evaluation of the general two-set small-chain
quasi-isomorphism. -/
theorem smallChainInclusion_twoSet_quasiIsoULift
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    {X : TopCat.{w}} (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    QuasiIso (smallChainInclusion (C := C) R (smallCoverBoth A B)) :=
  smallChainInclusionNatTrans_twoSet_quasiIsoULift G hG A B hcover R

theorem smallChainInclusionNatTrans_twoSet_quasiIso
    {X : TopCat.{0}} (A B : Set X)
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    (HomologicalComplex.quasiIso AddCommGrpCat.{z}
      (ComplexShape.down ℕ)).functorCategory AddCommGrpCat.{z}
        (smallChainInclusionNatTrans AddCommGrpCat.{z} (smallCoverBoth A B)) :=
  smallChainInclusionNatTrans_twoSet_quasiIsoULift
    (AddCommGrpCat.of (ULift.{z} ℤ)) AddCommGrpCat.isSeparator_uliftInt
    A B hcover

theorem smallChainInclusion_twoSet_quasiIso
    {X : TopCat.{0}} (A B : Set X) (R : AddCommGrpCat.{z})
    (hcover : (Set.univ : Set X) ⊆ interior A ∪ interior B) :
    QuasiIso (smallChainInclusion R (smallCoverBoth A B)) :=
  smallChainInclusionNatTrans_twoSet_quasiIso A B hcover R

end AlgebraicTopology

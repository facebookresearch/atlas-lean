/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.Normalization
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihComposite
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.CutMonoClassification
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBlockClassification
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.BlockShuffleFaces

/-!
# Projected bisimplicial shuffle--Alexander--Whitney retraction

Sandwich the shuffle/Alexander--Whitney composite between the double Dold--Kan
normalization projectors.  At each source bidegree and target cut, every
non-distinguished term contains a noninjective simplex map and is killed by
one target projector.  The block shuffle at the original cut reduces to the
idempotent bidegree projector.  Summing proves the strict projected
retraction on the total complex.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialNormalization

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- One cut-and-shuffle term sandwiched between double-normalization projectors. -/
noncomputable def projectedShuffleAlexanderWhitneyTerm
    (p q : ℕ) (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (r : Fin (p + q + 1)) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B).X (p + q) :=
  bidegreePInfty B p q ≫
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand B s ≫
    AlgebraicTopology.BisimplicialAlexanderWhitney.summand B (p + q) r ≫
    (totalPInfty B).f (p + q)

private theorem projectedCutTail_congr
    (p t t' n : ℕ) (htt' : t = t')
    (h : p + t = n) (h' : p + t' = n) :
    AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
          B p t n h ≫ bidegreePInfty B p t ≫
        (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
          (ComplexShape.down ℕ) p t n h =
      AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
          B p t' n h' ≫ bidegreePInfty B p t' ≫
        (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
          (ComplexShape.down ℕ) p t' n h' := by
  subst t'
  rfl

/-- Expand a projected fixed-bidegree composite into cut-and-shuffle terms. -/
theorem projected_shuffleBidegree_comp_component (p q : ℕ) :
    bidegreePInfty B p q ≫
        AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree B p q ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.component B (p + q) ≫
        (totalPInfty B).f (p + q) =
      ∑ r : Fin (p + q + 1),
        ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
          projectedShuffleAlexanderWhitneyTerm B p q s r := by
  unfold AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree
    AlgebraicTopology.BisimplicialAlexanderWhitney.component
    projectedShuffleAlexanderWhitneyTerm
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]

/-- A term with a noninjective outer simplex word vanishes. -/
theorem projectedTerm_eq_zero_of_left_not_mono
    (p q : ℕ) (r : Fin (p + q + 1))
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (hleft : ¬ Mono
      (AlgebraicTopology.AlexanderWhitney.frontInclusion
        r.val (p + q - r.val) (p + q) (by omega) ≫ s.leftHom)) :
    projectedShuffleAlexanderWhitneyTerm B p q s r = 0 := by
  let t := p + q - r.val
  have hrt : r.val + t = p + q := by
    dsimp [t]
    omega
  let α := AlgebraicTopology.AlexanderWhitney.frontInclusion
    r.val t (p + q) hrt ≫ s.leftHom
  let β := AlgebraicTopology.AlexanderWhitney.backInclusion
    r.val t (p + q) hrt ≫ s.rightHom
  have hα : ¬ Mono α := by
    dsimp only [α, t]
    exact hleft
  have hmap :
      AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap B s ≫
          AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
            B r.val t (p + q) hrt =
        AlgebraicTopology.Bisimplicial.map B α β := by
    unfold AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap
    rw [AlgebraicTopology.BisimplicialEilenbergZilber.faceToBidegreeOfEq_eq_map]
    exact AlgebraicTopology.Bisimplicial.map_comp _ _ _ _ _
  have hkill :
      AlgebraicTopology.Bisimplicial.map B α β ≫
        bidegreePInfty B r.val t = 0 := by
    unfold bidegreePInfty
    rw [← Category.assoc,
      map_comp_outerPInfty_eq_zero_of_not_mono B _ _ _ _ α β hα,
      CategoryTheory.Limits.zero_comp]
  unfold projectedShuffleAlexanderWhitneyTerm
    AlgebraicTopology.BisimplicialAlexanderWhitney.summand
    AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand
  simp_rw [Category.assoc]
  rw [totalι_comp_totalPInfty]
  dsimp only [t,
    AlgebraicTopology.BisimplicialAlexanderWhitney.cutComplement] at hmap hkill ⊢
  have hkill' :
      AlgebraicTopology.Bisimplicial.map B α β ≫
          bidegreePInfty B r.val (p + q - r.val) ≫
          (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
            (ComplexShape.down ℕ) r.val (p + q - r.val) (p + q) (by
              change r.val + (p + q - r.val) = p + q
              omega) = 0 := by
    have hcomp := hkill =≫
      (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) r.val (p + q - r.val) (p + q) (by
          change r.val + (p + q - r.val) = p + q
          omega)
    simpa only [Category.assoc, CategoryTheory.Limits.zero_comp] using hcomp
  rw [Preadditive.zsmul_comp]
  rw [← Category.assoc _
    (AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
      B r.val t (p + q) hrt), hmap]
  rw [hkill', smul_zero, CategoryTheory.Limits.comp_zero]

/-- A term with a noninjective inner simplex word vanishes. -/
theorem projectedTerm_eq_zero_of_right_not_mono
    (p q : ℕ) (r : Fin (p + q + 1))
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (hright : ¬ Mono
      (AlgebraicTopology.AlexanderWhitney.backInclusion
        r.val (p + q - r.val) (p + q) (by omega) ≫ s.rightHom)) :
    projectedShuffleAlexanderWhitneyTerm B p q s r = 0 := by
  let t := p + q - r.val
  have hrt : r.val + t = p + q := by
    dsimp [t]
    omega
  let α := AlgebraicTopology.AlexanderWhitney.frontInclusion
    r.val t (p + q) hrt ≫ s.leftHom
  let β := AlgebraicTopology.AlexanderWhitney.backInclusion
    r.val t (p + q) hrt ≫ s.rightHom
  have hβ : ¬ Mono β := by
    dsimp only [β, t]
    exact hright
  have hmap :
      AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap B s ≫
          AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
            B r.val t (p + q) hrt =
        AlgebraicTopology.Bisimplicial.map B α β := by
    unfold AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap
    rw [AlgebraicTopology.BisimplicialEilenbergZilber.faceToBidegreeOfEq_eq_map]
    exact AlgebraicTopology.Bisimplicial.map_comp _ _ _ _ _
  have hcomm :
      ((outerPInfty B).f r.val).f t ≫ ((verticalPInfty B).f r.val).f t =
        ((verticalPInfty B).f r.val).f t ≫ ((outerPInfty B).f r.val).f t := by
    exact congrArg (fun k => (k.f r.val).f t)
      (outerPInfty_comp_verticalPInfty B)
  have hkill :
      AlgebraicTopology.Bisimplicial.map B α β ≫
        bidegreePInfty B r.val t = 0 := by
    unfold bidegreePInfty
    rw [hcomm]
    rw [← Category.assoc,
      map_comp_verticalPInfty_eq_zero_of_not_mono B _ _ _ _ α β hβ,
      CategoryTheory.Limits.zero_comp]
  unfold projectedShuffleAlexanderWhitneyTerm
    AlgebraicTopology.BisimplicialAlexanderWhitney.summand
    AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand
  simp_rw [Category.assoc]
  rw [totalι_comp_totalPInfty]
  dsimp only [t,
    AlgebraicTopology.BisimplicialAlexanderWhitney.cutComplement] at hmap hkill ⊢
  have hkill' :
      AlgebraicTopology.Bisimplicial.map B α β ≫
          bidegreePInfty B r.val (p + q - r.val) ≫
          (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
            (ComplexShape.down ℕ) r.val (p + q - r.val) (p + q) (by
              change r.val + (p + q - r.val) = p + q
              omega) = 0 := by
    have hcomp := hkill =≫
      (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
        (ComplexShape.down ℕ) r.val (p + q - r.val) (p + q) (by
          change r.val + (p + q - r.val) = p + q
          omega)
    simpa only [Category.assoc, CategoryTheory.Limits.zero_comp] using hcomp
  rw [Preadditive.zsmul_comp]
  rw [← Category.assoc _
    (AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
      B r.val t (p + q) hrt), hmap]
  rw [hkill', smul_zero, CategoryTheory.Limits.comp_zero]

/-- Every term at a nonoriginal cut vanishes. -/
theorem projectedTerm_eq_zero_of_cut_ne
    (p q : ℕ) (r : Fin (p + q + 1))
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (hrp : r.val ≠ p) :
    projectedShuffleAlexanderWhitneyTerm B p q s r = 0 := by
  classical
  by_cases hleft : Mono
      (AlgebraicTopology.AlexanderWhitney.frontInclusion
        r.val (p + q - r.val) (p + q) (by omega) ≫ s.leftHom)
  · let _ := hleft
    by_cases hright : Mono
        (AlgebraicTopology.AlexanderWhitney.backInclusion
          r.val (p + q - r.val) (p + q) (by omega) ≫ s.rightHom)
    · let _ := hright
      exact False.elim (hrp
        (AlgebraicTopology.EilenbergZilber.cut_eq_of_both_mono p q r s))
    · exact projectedTerm_eq_zero_of_right_not_mono B p q r s hright
  · exact projectedTerm_eq_zero_of_left_not_mono B p q r s hleft

/-- At the original cut, every nonblock shuffle term vanishes. -/
theorem projectedTerm_eq_zero_of_shuffle_ne
    (p q : ℕ) (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (hs : s ≠ AlgebraicTopology.EilenbergZilber.Shuffle.blockShuffle p q) :
    projectedShuffleAlexanderWhitneyTerm B p q s ⟨p, by omega⟩ = 0 := by
  apply projectedTerm_eq_zero_of_left_not_mono B
  intro hmono
  change Mono (AlgebraicTopology.AlexanderWhitney.frontInclusion
    p q (p + q) rfl ≫ s.leftHom) at hmono
  let _ := hmono
  exact hs (AlgebraicTopology.EilenbergZilber.Shuffle.eq_blockShuffle_of_left_mono
    p q s)

/-- The block shuffle at the original cut is the projected bidegree inclusion. -/
theorem projectedDistinguishedTerm (p q : ℕ) :
    projectedShuffleAlexanderWhitneyTerm B p q
        (AlgebraicTopology.EilenbergZilber.Shuffle.blockShuffle p q)
        ⟨p, by omega⟩ =
      bidegreePInfty B p q ≫
        (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
          (ComplexShape.down ℕ) p q (p + q) rfl := by
  have hmap :
      AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap B
          (AlgebraicTopology.EilenbergZilber.Shuffle.blockShuffle p q) ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
          B p q (p + q) rfl = 𝟙 _ := by
    unfold AlgebraicTopology.BisimplicialEilenbergZilber.shuffleMap
    rw [AlgebraicTopology.BisimplicialEilenbergZilber.faceToBidegreeOfEq_eq_map]
    rw [AlgebraicTopology.Bisimplicial.map_comp]
    rw [AlgebraicTopology.EilenbergZilber.Shuffle.frontInclusion_comp_blockShuffle_leftHom,
      AlgebraicTopology.EilenbergZilber.Shuffle.backInclusion_comp_blockShuffle_rightHom]
    exact AlgebraicTopology.Bisimplicial.map_id B p q
  unfold projectedShuffleAlexanderWhitneyTerm
    AlgebraicTopology.BisimplicialAlexanderWhitney.summand
    AlgebraicTopology.BisimplicialAlexanderWhitney.totalιOfEq
    AlgebraicTopology.BisimplicialEilenbergZilber.shuffleSummand
  simp_rw [Category.assoc]
  rw [totalι_comp_totalPInfty]
  rw [projectedCutTail_congr B p
    (AlgebraicTopology.BisimplicialAlexanderWhitney.cutComplement
      (p + q) (⟨p, by omega⟩ : Fin (p + q + 1))) q (p + q)
    (AlgebraicTopology.BisimplicialAlexanderWhitney.cutComplement_add p q)
    (AlgebraicTopology.BisimplicialAlexanderWhitney.cut_add (p + q)
      (⟨p, by omega⟩ : Fin (p + q + 1))) rfl]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.shuffleSignZ_blockShuffle]
  simp only [one_zsmul]
  rw [← Category.assoc _
    (AlgebraicTopology.BisimplicialAlexanderWhitney.faceToBidegreeOfEq
      B p q (p + q) rfl), hmap]
  simp only [Category.id_comp]
  rw [← Category.assoc, bidegreePInfty_idem]

/-- Sum the projected shuffle terms at a fixed cut. -/
theorem projectedCutSum (p q : ℕ) (r : Fin (p + q + 1)) :
    (∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        projectedShuffleAlexanderWhitneyTerm B p q s r) =
      if r = (⟨p, by omega⟩ : Fin (p + q + 1)) then
        bidegreePInfty B p q ≫
          (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
            (ComplexShape.down ℕ) p q (p + q) rfl
      else 0 := by
  classical
  by_cases hr : r = (⟨p, by omega⟩ : Fin (p + q + 1))
  · subst r
    rw [ite_eq_left rfl]
    rw [Fintype.sum_eq_single
      (AlgebraicTopology.EilenbergZilber.Shuffle.blockShuffle p q)]
    · exact projectedDistinguishedTerm B p q
    · intro s hs
      exact projectedTerm_eq_zero_of_shuffle_ne B p q s hs
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun s _ =>
      projectedTerm_eq_zero_of_cut_ne B p q r s (by
        intro hrval
        apply hr
        apply Fin.ext
        exact hrval)

/-- The projected composite restricts to the projected inclusion on each bidegree. -/
theorem projectedBidegreeIdentity (p q : ℕ) :
    bidegreePInfty B p q ≫
        AlgebraicTopology.BisimplicialEilenbergZilber.shuffleBidegree B p q ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.component B (p + q) ≫
        (totalPInfty B).f (p + q) =
      bidegreePInfty B p q ≫
        (AlgebraicTopology.bisimplicialAlternatingBicomplex A B).ιTotal
          (ComplexShape.down ℕ) p q (p + q) rfl := by
  rw [projected_shuffleBidegree_comp_component]
  simp_rw [projectedCutSum]
  rw [Finset.sum_ite_eq']
  simp

/-- The double-projector-sandwiched shuffle--Alexander--Whitney composite is the projector. -/
theorem projectedStrictRetraction :
    totalPInfty B ≫
        AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B ≫
        totalPInfty B =
      totalPInfty B := by
  ext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = n at h
  subst n
  simp only [HomologicalComplex.comp_f,
    AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap_f,
    AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap_f]
  rw [totalι_comp_totalPInfty_assoc]
  rw [totalι_comp_totalPInfty]
  rw [AlgebraicTopology.BisimplicialEilenbergZilber.totalι_comp_component_assoc]
  simp only [eqToHom_refl, Category.id_comp]
  exact projectedBidegreeIdentity B p q

end AlgebraicTopology.BisimplicialNormalization

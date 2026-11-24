/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalFundamentalGeneration

/-!
# Commutativity of the weak-diagonal fundamental group

Two pushouts of the maps from the zero object to a pair of Waldhausen
objects give the two cofiber relations in opposite orders.  The pushout
middle objects are canonically isomorphic, so their object edges agree in
the fundamental groupoid.  Thus the canonical object generators commute.
Since those generators generate the based fundamental group, subgroup
closure induction proves that all of its elements commute.

The multiplication on categorical endomorphisms is reversed:
`(a * b).asHom = b.asHom ≫ a.asHom`.  The cofiber relation below records that order explicitly.
This file installs no `CommGroup` instance and defines no K-zero map,
encode/decode map, realization comparison, additivity equivalence, spectrum,
or Q/S comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

set_option backward.isDefEq.respectTransparency false in
/-- A pushout of the two maps out of zero, whose `A`-leg is a cofibration,
supplies the complementary cofiber sequence `A → P → B`. -/
private noncomputable def zeroPushoutCofiberData
    {A B P : C} (iA : A ⟶ P) (iB : B ⟶ P)
    (h : IsPushout
      (HasZeroObject.zeroIsInitial.to A)
      (HasZeroObject.zeroIsInitial.to B) iA iB)
    (hiA : IsCofibration (C := C) iA) :
    { q : P ⟶ B // IsCofibrationSequence (C := C) iA q } := by
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  let w : (HasZeroObject.zeroIsInitial.to A) ≫ (0 : A ⟶ B) =
      (HasZeroObject.zeroIsInitial.to B) ≫ 𝟙 B :=
    (isZero_zero C).eq_of_src _ _
  let q : P ⟶ B := h.desc (0 : A ⟶ B) (𝟙 B) w
  have hiAq : iA ≫ q = 0 := by
    exact h.inl_desc (0 : A ⟶ B) (𝟙 B) w
  have hiBq : iB ≫ q = 𝟙 B := by
    exact h.inr_desc (0 : A ⟶ B) (𝟙 B) w
  let hzero : (0 : A ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ B) = iA ≫ q := by
    simpa using hiAq.symm
  have ht : IsColimit
      (PushoutCocone.mk (0 : (0 : C) ⟶ B) q hzero) := by
    refine PushoutCocone.IsColimit.mk
      (f := (0 : A ⟶ (0 : C))) (g := iA)
      (inl := (0 : (0 : C) ⟶ B)) (inr := q)
      hzero (fun s => iB ≫ s.inr) ?_ ?_ ?_
    · intro s
      exact (isZero_zero C).eq_of_src _ _
    · intro s
      apply h.hom_ext
      · rw [← Category.assoc, hiAq, zero_comp]
        simpa using s.condition
      · simp only [← Category.assoc, hiBq, Category.id_comp]
    · intro s m _hmZero hmP
      calc
        m = (iB ≫ q) ≫ m := by rw [hiBq, Category.id_comp]
        _ = iB ≫ (q ≫ m) := Category.assoc _ _ _
        _ = iB ≫ s.inr := by rw [hmP]
  have hq : IsPushout (0 : A ⟶ (0 : C)) iA
      (0 : (0 : C) ⟶ B) q :=
    IsPushout.of_isColimit ht
  exact ⟨q, hiA, 0, 0, hq⟩

/-- A cofiber sequence `X → Y → Z` gives the multiplicative relation
`[Z] * [X] = [Y]`.  The quotient precedes the source because multiplication
in `CategoryTheory.End` reverses categorical composition. -/
theorem stageWeakDiagonalObjectGenerator_quotient_mul_source
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    stageWeakDiagonalObjectGenerator C Z *
        stageWeakDiagonalObjectGenerator C X =
      stageWeakDiagonalObjectGenerator C Y := by
  apply CategoryTheory.End.ext
  rw [CategoryTheory.End.mul_asHom]
  simpa only [stageWeakDiagonalObjectGenerator] using
    (stageWeakDiagonalCofiberCompStruct C f g hSeq).homMk_comp

/-- Canonical object generators commute.  The proof uses two pushouts out of
zero because the Waldhausen axiom certifies only one cobase-changed leg as a
cofibration in each chosen pushout. -/
theorem stageWeakDiagonalObjectGenerator_comm (A B : C) :
    stageWeakDiagonalObjectGenerator C A *
        stageWeakDiagonalObjectGenerator C B =
      stageWeakDiagonalObjectGenerator C B *
        stageWeakDiagonalObjectGenerator C A := by
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  let zA : (0 : C) ⟶ A := HasZeroObject.zeroIsInitial.to A
  let zB : (0 : C) ⟶ B := HasZeroObject.zeroIsInitial.to B
  have hzA : IsCofibration (C := C) zA :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration A zA
  have hzB : IsCofibration (C := C) zB :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration B zB
  obtain ⟨PAB, iA, iB, hAB, hiA⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) zB hzB A zA
  obtain ⟨PBA, iB', iA', hBA, hiB'⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) zA hzA B zB
  let dAB := zeroPushoutCofiberData (C := C) iA iB hAB hiA
  let dBA := zeroPushoutCofiberData (C := C) iB' iA' hBA hiB'
  let qAB : PAB ⟶ B := dAB.1
  let qBA : PBA ⟶ A := dBA.1
  have hSeqAB : IsCofibrationSequence (C := C) iA qAB := dAB.2
  have hSeqBA : IsCofibrationSequence (C := C) iB' qBA := dBA.2
  have hABRel :
      stageWeakDiagonalObjectGenerator C B *
          stageWeakDiagonalObjectGenerator C A =
        stageWeakDiagonalObjectGenerator C PAB :=
    stageWeakDiagonalObjectGenerator_quotient_mul_source C iA qAB hSeqAB
  have hBARel :
      stageWeakDiagonalObjectGenerator C A *
          stageWeakDiagonalObjectGenerator C B =
        stageWeakDiagonalObjectGenerator C PBA :=
    stageWeakDiagonalObjectGenerator_quotient_mul_source C iB' qBA hSeqBA
  let e : PAB ≅ PBA := hAB.isoIsPushout A B hBA.flip
  have he : IsWeakEquivalence e.hom :=
    (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso e.hom
  have hMiddle :
      stageWeakDiagonalObjectGenerator C PAB =
        stageWeakDiagonalObjectGenerator C PBA := by
    apply CategoryTheory.End.ext
    simpa only [stageWeakDiagonalObjectGenerator] using
      (stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence C e.hom he)
  exact hBARel.trans (hMiddle.symm.trans hABRel.symm)

/-- Any two elements of the subgroup generated by object edges commute. -/
private theorem stageWeakDiagonalObjectGeneratorSubgroup_comm
    {x y : stageWeakDiagonalFundamentalGroup C}
    (hx : x ∈ stageWeakDiagonalObjectGeneratorSubgroup C)
    (hy : y ∈ stageWeakDiagonalObjectGeneratorSubgroup C) :
    Commute x y := by
  change x ∈ Subgroup.closure
      (Set.range (stageWeakDiagonalObjectGenerator C)) at hx
  change y ∈ Subgroup.closure
      (Set.range (stageWeakDiagonalObjectGenerator C)) at hy
  refine Subgroup.closure_induction₂
    (k := Set.range (stageWeakDiagonalObjectGenerator C))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact stageWeakDiagonalObjectGenerator_comm C A B
  · intro z _hz
    exact Commute.one_left z
  · intro z _hz
    exact Commute.one_right z
  · intro x y z _hx _hy _hz hxz hyz
    exact hxz.mul_left hyz
  · intro y z x _hy _hz _hx hxy hxz
    exact hxy.mul_right hxz
  · intro x y _hx _hy hxy
    exact hxy.inv_left
  · intro x y _hx _hy hxy
    exact hxy.inv_right

/-- Multiplication in the based combinatorial fundamental group is
commutative.  This is an explicit theorem, not a global `CommGroup`
instance. -/
theorem stageWeakDiagonalFundamentalGroup_mul_comm
    (f g : stageWeakDiagonalFundamentalGroup C) :
    f * g = g * f := by
  have hf : f ∈ stageWeakDiagonalObjectGeneratorSubgroup C := by
    rw [stageWeakDiagonalObjectGeneratorSubgroup_eq_top]
    exact Subgroup.mem_top f
  have hg : g ∈ stageWeakDiagonalObjectGeneratorSubgroup C := by
    rw [stageWeakDiagonalObjectGeneratorSubgroup_eq_top]
    exact Subgroup.mem_top g
  exact (stageWeakDiagonalObjectGeneratorSubgroup_comm C hf hg).eq

end CategoryTheory.Waldhausen.SConstruction

end

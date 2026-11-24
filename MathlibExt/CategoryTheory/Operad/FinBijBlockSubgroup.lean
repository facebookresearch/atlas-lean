/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal
public import Mathlib.CategoryTheory.Endomorphism
public import MathlibExt.GroupTheory.Permutation.Sum

/-!
# Ordered blocks of finite-bijection automorphisms

The right tensor functor extends an automorphism by the identity of the
final block. Conjugation by an actual block isomorphism expresses it as an
automorphism of the target finite set.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The chosen first-block action uses inverse precomposition, with no global instance. -/
@[instance_reducible]
def blockMulAction (R N M : SmallFinBijGroupoid) :
    MulAction (Aut R) (R ⊗ N ≅ M) where
  smul a e := (tensorRight N).mapIso a.asIso.symm ≪≫ e
  one_smul e := by
    change (tensorRight N).mapIso (Iso.refl R) ≪≫ e = e
    rw [Functor.mapIso_refl, Iso.refl_trans]
  mul_smul a c e := by
    change (tensorRight N).mapIso
      ((c.asIso.trans a.asIso).symm) ≪≫ e =
      (tensorRight N).mapIso a.asIso.symm ≪≫
        ((tensorRight N).mapIso c.asIso.symm ≪≫ e)
    rw [Iso.trans_symm, Functor.mapIso_trans, Iso.trans_assoc]

/-- The chosen action has the literal inverse-precomposition formula. -/
theorem blockMulAction_smul (R N M : SmallFinBijGroupoid)
    (a : Aut R) (e : R ⊗ N ≅ M) :
    letI := blockMulAction R N M
    a • e = (tensorRight N).mapIso a.asIso.symm ≪≫ e :=
  rfl

/-- Extend an automorphism of the complement block and conjugate it across
the supplied actual block comparison. -/
def blockAutHom (R N M : SmallFinBijGroupoid) (b : R ⊗ N ≅ M) :
    Aut R →* Aut M :=
  (Aut.autMulEquivOfIso b).toMonoidHom.comp
    (Functor.mapAut R (tensorRight N))

/-- The underlying first-block map retains the literal identity on N. -/
theorem blockAutHom_hom (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (a : Aut R) :
    (blockAutHom R N M b a).asIso.hom = b.inv ≫ (a.asIso.hom ▷ N) ≫ b.hom :=
  rfl

/-- The block homomorphism has the actual conjugated isomorphism as its value. -/
theorem blockAutHom_iso (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (a : Aut R) :
    b.symm ≪≫ (tensorRight N).mapIso a.asIso ≪≫ b =
      (blockAutHom R N M b a).asIso := by
  apply Iso.ext
  rfl

/-- Isomorphisms from the block sum to M form the actual automorphism
torsor after the fixed comparison b. -/
def blockIsoEquivAut (R N M : SmallFinBijGroupoid) (b : R ⊗ N ≅ M) :
    (R ⊗ N ≅ M) ≃ Aut M where
  toFun e := .of (b.symm ≪≫ e)
  invFun g := b ≪≫ g.asIso
  left_inv e := by
    simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  right_inv g := by
    apply Aut.ext
    change b.symm ≪≫ (b ≪≫ g.asIso) = g.asIso
    rw [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- Target postcomposition is the full left automorphism action. -/
theorem blockIsoEquivAut_postcompose (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (e : R ⊗ N ≅ M) (g : Aut M) :
    blockIsoEquivAut R N M b (e ≪≫ g.asIso) =
      g * blockIsoEquivAut R N M b e := by
  apply Aut.ext
  change b.symm ≪≫ (e ≪≫ g.asIso) = (b.symm ≪≫ e) ≪≫ g.asIso
  exact (Iso.trans_assoc _ _ _).symm

/-- Inverse first-block precomposition is right multiplication by the subgroup inverse. -/
theorem blockIsoEquivAut_precompose (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (e : R ⊗ N ≅ M) (a : Aut R) :
    blockIsoEquivAut R N M b
        ((tensorRight N).mapIso a.asIso.symm ≪≫ e) =
      blockIsoEquivAut R N M b e * (blockAutHom R N M b a)⁻¹ := by
  rw [← map_inv (blockAutHom R N M b)]
  apply Aut.ext
  change b.symm ≪≫ ((tensorRight N).mapIso a.asIso.symm ≪≫ e) =
    (blockAutHom R N M b a⁻¹).asIso ≪≫ (b.symm ≪≫ e)
  rw [← blockAutHom_iso R N M b a⁻¹]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rfl

/-- The chosen action agrees with the actual subgroup inverse under the torsor comparison. -/
theorem blockIsoEquivAut_smul (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (e : R ⊗ N ≅ M) (a : Aut R) :
    letI := blockMulAction R N M
    blockIsoEquivAut R N M b (a • e) =
      blockIsoEquivAut R N M b e * (blockAutHom R N M b a)⁻¹ :=
  blockIsoEquivAut_precompose R N M b e a

/-- The actual first-block action commutes with full target postcomposition. -/
theorem blockMulAction_postcompose (R N M : SmallFinBijGroupoid)
    (a : Aut R) (e : R ⊗ N ≅ M) (g : Aut M) :
    letI := blockMulAction R N M
    a • (e ≪≫ g.asIso) =
      (a • e) ≪≫ g.asIso := by
  let _ := blockMulAction R N M
  exact (Iso.trans_assoc _ _ _).symm

/-- The actual finite alphabet splits into the complement and final block. -/
def blockSplitEquiv (R N : SmallFinBijGroupoid) :
    ULift.{0, 0} (Fin (blockSumObj R N).of.len) ≃
      ULift.{0, 0} (Fin R.of.len) ⊕ ULift.{0, 0} (Fin N.of.len) :=
  Equiv.ulift.trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

/-- Actual finite-bijection automorphisms are permutations of the chosen finite alphabet. -/
def alphabetAutEquiv (R : SmallFinBijGroupoid) :
    Aut R ≃* Equiv.Perm (ULift.{0, 0} (Fin R.of.len)) where
  toFun a := FinBijGroupoid.equivOfHom (smallFinBijEquivalence.functor.map a.asIso.hom)
  invFun e := Aut.of (Core.isoMk
    { hom := e
      inv := e.symm
      hom_inv_id := by funext x; exact e.symm_apply_apply x
      inv_hom_id := by funext x; exact e.apply_symm_apply x })
  left_inv a := by
    apply Aut.ext
    apply Iso.ext
    apply Core.hom_ext
    funext x
    rfl
  right_inv e := by
    ext x
    rfl
  map_mul' a c := by
    ext x
    rfl

/-- The same actual automorphism group is the usual permutation group of Fin cardinality. -/
def finAutEquiv (R : SmallFinBijGroupoid) : Aut R ≃* Equiv.Perm (Fin R.of.len) :=
  (alphabetAutEquiv R).trans
    (Equiv.ulift : ULift.{0, 0} (Fin R.of.len) ≃ Fin R.of.len).permCongrHom

/-- The supplied block isomorphism gives the exact ordered split of the target alphabet. -/
def blockTargetSplit (R N M : SmallFinBijGroupoid) (b : R ⊗ N ≅ M) :
    ULift.{0, 0} (Fin M.of.len) ≃
      ULift.{0, 0} (Fin R.of.len) ⊕ ULift.{0, 0} (Fin N.of.len) :=
  (FinBijGroupoid.equivOfHom (smallFinBijEquivalence.functor.map b.hom)).symm.trans
    (blockSplitEquiv R N)

/-- Express a target automorphism on the actual ordered block alphabet. -/
def splitTargetAut (R N M : SmallFinBijGroupoid) (b : R ⊗ N ≅ M) :
    Aut M ≃* Equiv.Perm
      (ULift.{0, 0} (Fin R.of.len) ⊕ ULift.{0, 0} (Fin N.of.len)) :=
  (alphabetAutEquiv M).trans (blockTargetSplit R N M b).permCongrHom

/-- Extending an endomorphism by the identity final block is injective. -/
theorem tensorRight_endHom_injective (R N : SmallFinBijGroupoid) :
    Function.Injective (fun f : R ⟶ R => f ▷ N) := by
  intro f g hfg
  change blockSumHom f (𝟙 N) = blockSumHom g (𝟙 N) at hfg
  have hEquiv := congrArg
    (fun k => FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map k)) hfg
  rw [blockSumHom_equivOfHom, blockSumHom_equivOfHom] at hEquiv
  dsimp only at hEquiv
  let S := blockSplitEquiv R N
  let eF :
      ULift.{0, 0} (Fin R.of.len) ≃
        ULift.{0, 0} (Fin R.of.len) :=
    FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map f)
  let eG :
      ULift.{0, 0} (Fin R.of.len) ≃
        ULift.{0, 0} (Fin R.of.len) :=
    FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map g)
  let eN :
      ULift.{0, 0} (Fin N.of.len) ≃
        ULift.{0, 0} (Fin N.of.len) :=
    FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map (𝟙 N))
  have hEquivTyped :
      S.trans ((Equiv.sumCongr eF eN).trans S.symm) =
        S.trans ((Equiv.sumCongr eG eN).trans S.symm) := by
    exact hEquiv
  apply Core.hom_ext
  funext x
  change eF x = eG x
  have hEvalF :
      (S.trans ((Equiv.sumCongr eF eN).trans S.symm))
          (S.symm (Sum.inl x)) =
        S.symm (Sum.inl (eF x)) := by
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.sumCongr_apply, Sum.map_inl]
  have hEvalG :
      (S.trans ((Equiv.sumCongr eG eN).trans S.symm))
          (S.symm (Sum.inl x)) =
        S.symm (Sum.inl (eG x)) := by
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.sumCongr_apply, Sum.map_inl]
  have hPoint := congrArg
    (fun k => k (S.symm (Sum.inl x))) hEquivTyped
  rw [hEvalF, hEvalG] at hPoint
  have hInl : Sum.inl (eF x) = Sum.inl (eG x) :=
    S.symm.injective hPoint
  exact Sum.inl.inj hInl

/-- The complement automorphism group embeds in the actual target block. -/
theorem blockAutHom_injective (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) :
    Function.Injective (blockAutHom R N M b) := by
  intro a c hac
  have hmap : (Functor.mapAut R (tensorRight N)) a =
      (Functor.mapAut R (tensorRight N)) c :=
    (Aut.autMulEquivOfIso b).injective hac
  have hmapIso := congrArg Aut.asIso hmap
  change (tensorRight N).mapIso a.asIso = (tensorRight N).mapIso c.asIso at hmapIso
  have hHom := congrArg Iso.hom hmapIso
  change a.asIso.hom ▷ N = c.asIso.hom ▷ N at hHom
  apply Aut.ext
  apply Iso.ext
  apply tensorRight_endHom_injective R N
  exact hHom

/-- The chosen first-block action is free at every actual block isomorphism. -/
theorem blockMulAction_free (R N M : SmallFinBijGroupoid) (e : R ⊗ N ≅ M) :
    letI := blockMulAction R N M
    Function.Injective (fun a : Aut R => a • e) := by
  let _ := blockMulAction R N M
  intro a c hac
  have hCancel := congrArg (fun z : R ⊗ N ≅ M => z ≪≫ e.symm) hac
  change ((tensorRight N).mapIso a.asIso.symm ≪≫ e) ≪≫ e.symm =
    ((tensorRight N).mapIso c.asIso.symm ≪≫ e) ≪≫ e.symm at hCancel
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at hCancel
  have hInv : a.asIso.symm = c.asIso.symm := by
    have hHom := congrArg Iso.hom hCancel
    change a.asIso.symm.hom ▷ N = c.asIso.symm.hom ▷ N at hHom
    apply Iso.ext
    exact tensorRight_endHom_injective R N hHom
  apply Aut.ext
  exact Eq.trans (Iso.symm_symm_eq a.asIso).symm
    (Eq.trans (congrArg Iso.symm hInv) (Iso.symm_symm_eq c.asIso))

/-- The actual block map becomes first-summand extension on the ordered target alphabet. -/
theorem splitTargetAut_blockAut (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (a : Aut R) :
    splitTargetAut R N M b (blockAutHom R N M b a) =
      Equiv.Perm.sumInlHom (ULift.{0, 0} (Fin R.of.len))
        (ULift.{0, 0} (Fin N.of.len)) (alphabetAutEquiv R a) := by
  let alpha : R ≅ R := a.asIso
  let sigma : Equiv.Perm (ULift.{0, 0} (Fin R.of.len)) := alphabetAutEquiv R a
  let S := blockSplitEquiv R N
  let eB : ULift.{0, 0} (Fin (R ⊗ N).of.len) ≃ ULift.{0, 0} (Fin M.of.len) :=
    FinBijGroupoid.equivOfHom (smallFinBijEquivalence.functor.map b.hom)
  have hb (x : ULift.{0, 0} (Fin (R ⊗ N).of.len)) :
      b.inv.iso.hom (b.hom.iso.hom x) = x := by
    have h := congrArg (fun f : R ⊗ N ⟶ R ⊗ N => f.iso.hom x) b.hom_inv_id
    exact h
  have hBlock :
      FinBijGroupoid.equivOfHom
          (smallFinBijEquivalence.functor.map (alpha.hom ▷ N)) =
        S.trans ((Equiv.sumCongr sigma
          (Equiv.refl (ULift.{0, 0} (Fin N.of.len)))).trans S.symm) :=
    blockSumHom_equivOfHom alpha.hom (𝟙 N)
  ext x
  change S (eB.symm (eB ((alpha.hom ▷ N).iso.hom
    (b.inv.iso.hom (b.hom.iso.hom (S.symm x)))))) =
      (Equiv.sumCongr sigma (Equiv.refl _)) x
  rw [hb, Equiv.symm_apply_apply]
  have h := congrArg (fun k => S (k (S.symm x))) hBlock
  change S ((alpha.hom ▷ N).iso.hom (S.symm x)) =
    S (S.symm ((Equiv.sumCongr sigma (Equiv.refl _)) (S (S.symm x)))) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- The subgroup image is exactly the pointwise stabilizer of the actual final block. -/
theorem blockAutHom_range_iff (R N M : SmallFinBijGroupoid)
    (b : R ⊗ N ≅ M) (s : Aut M) :
    s ∈ (blockAutHom R N M b).range ↔
      ∀ x : ULift.{0, 0} (Fin N.of.len),
        alphabetAutEquiv M s ((blockTargetSplit R N M b).symm (Sum.inr x)) =
          (blockTargetSplit R N M b).symm (Sum.inr x) := by
  constructor
  · rintro ⟨a, rfl⟩ x
    apply (blockTargetSplit R N M b).injective
    rw [Equiv.apply_symm_apply]
    change splitTargetAut R N M b (blockAutHom R N M b a) (Sum.inr x) = Sum.inr x
    rw [splitTargetAut_blockAut]
    rfl
  · intro hfix
    have hsplit : ∀ x : ULift.{0, 0} (Fin N.of.len),
        splitTargetAut R N M b s (Sum.inr x) = Sum.inr x := by
      intro x
      change blockTargetSplit R N M b
        (alphabetAutEquiv M s ((blockTargetSplit R N M b).symm (Sum.inr x))) =
          Sum.inr x
      rw [hfix x, Equiv.apply_symm_apply]
    obtain ⟨a, ha⟩ :=
      (Equiv.Perm.mem_sumInlHom_range_iff (ULift.{0, 0} (Fin R.of.len))
        (ULift.{0, 0} (Fin N.of.len)) (splitTargetAut R N M b s)).mpr hsplit
    refine ⟨(alphabetAutEquiv R).symm a, ?_⟩
    apply (splitTargetAut R N M b).injective
    rw [splitTargetAut_blockAut, MulEquiv.apply_symm_apply]
    exact ha

end CategoryTheory.Operad.SmallFinBijGroupoid

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentation
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The kernel-augmented tail of a nonnegative resolution

Restricting a nonnegative chain complex through `embeddingDown'Add 1 1` gives
its positive tail. The first differential factors through the augmentation
kernel to augment this tail. For an augmentation that is a quasi-isomorphism
in degrees zero and one, the tail augmentation is a quasi-isomorphism in
degree zero. In positive degrees, exactness is inherited from the next degree
of the original complex.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Q : ChainComplex C ℕ} {M : C}

/-- The native degree shift used by the kernel-augmented tail. -/
abbrev kernelTailEmbedding :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ComplexShape.embeddingDown'Add (1 : ℕ) 1

/-- The kernel-tail embedding shifts every degree up by one. -/
lemma kernelTailEmbedding_f (i : ℕ) : kernelTailEmbedding.f i = i + 1 :=
  ComplexShape.embeddingDown'Add_f 1 1 i

/-- The kernel-tail embedding sends degree zero to degree one. -/
lemma kernelTailEmbedding_f_zero : kernelTailEmbedding.f 0 = 1 := by simp

/-- The kernel-tail embedding sends degree one to degree two. -/
lemma kernelTailEmbedding_f_one : kernelTailEmbedding.f 1 = 2 := by simp

local instance : kernelTailEmbedding.IsRelIff :=
  ComplexShape.instIsRelIffEmbeddingDown'Add 1 1

/-- Augment the actual restricted tail by the kernel of the original augmentation. -/
noncomputable def kernelTailAugmentation (π : Q ⟶ (single₀ C).obj M) :
    Q.restriction kernelTailEmbedding ⟶
      (single₀ C).obj (kernel (π.f 0)) := by
  have hπ : Q.d 1 0 ≫ π.f 0 = 0 := by
    simpa only [HomologicalComplex.single_obj_d, comp_zero] using (π.comm 1 0).symm
  let q : Q.X 1 ⟶ kernel (π.f 0) := kernel.lift (π.f 0) (Q.d 1 0) hπ
  have hq : Q.d 2 1 ≫ q = 0 := by
    apply (cancel_mono (kernel.ι (π.f 0))).1
    rw [Category.assoc, kernel.lift_ι, Q.d_comp_d, zero_comp]
  let e₀ : (Q.restriction kernelTailEmbedding).X 0 ≅ Q.X 1 :=
    Q.restrictionXIso kernelTailEmbedding (i := 0) (i' := 1)
      kernelTailEmbedding_f_zero
  let e₁ : (Q.restriction kernelTailEmbedding).X 1 ≅ Q.X 2 :=
    Q.restrictionXIso kernelTailEmbedding (i := 1) (i' := 2)
      kernelTailEmbedding_f_one
  have hd : (Q.restriction kernelTailEmbedding).d 1 0 =
      e₁.hom ≫ Q.d 2 1 ≫ e₀.inv :=
    Q.restriction_d_eq kernelTailEmbedding (i := 1) (j := 0)
      (i' := 2) (j' := 1) kernelTailEmbedding_f_one kernelTailEmbedding_f_zero
  have hf : (Q.restriction kernelTailEmbedding).d 1 0 ≫ (e₀.hom ≫ q) = 0 := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hq, comp_zero]
  exact (toSingle₀Equiv (Q.restriction kernelTailEmbedding)
    (kernel (π.f 0))).symm ⟨e₀.hom ≫ q, hf⟩

/-- The tail augmentation is the actual native kernel lift. -/
@[simp]
lemma kernelTailAugmentation_f_zero (π : Q ⟶ (single₀ C).obj M) :
    (kernelTailAugmentation π).f 0 =
      kernel.lift (π.f 0) (Q.d 1 0)
        (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]) := by
  unfold kernelTailAugmentation
  rw [toSingle₀Equiv_symm_apply_f_zero]
  apply eq_of_heq
  exact eqToHom_comp_heq
    (kernel.lift (π.f 0) (Q.d 1 0)
      (by rw [← π.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]))
    (congrArg Q.X kernelTailEmbedding_f_zero)

/-- The original augmentation's degrees zero and one give exactness at the tail augmentation. -/
lemma quasiIsoAt_zero_kernelTailAugmentation (π : Q ⟶ (single₀ C).obj M)
    [QuasiIsoAt π 0] [QuasiIsoAt π 1] : QuasiIsoAt (kernelTailAugmentation π) 0 := by
  have hπ : Q.d 1 0 ≫ π.f 0 = 0 := by
    simpa only [HomologicalComplex.single_obj_d, comp_zero] using (π.comm 1 0).symm
  let q : Q.X 1 ⟶ kernel (π.f 0) := kernel.lift (π.f 0) (Q.d 1 0) hπ
  let e₀ : (Q.restriction kernelTailEmbedding).X 0 ≅ Q.X 1 :=
    Q.restrictionXIso kernelTailEmbedding (i := 0) (i' := 1)
      kernelTailEmbedding_f_zero
  let e₁ : (Q.restriction kernelTailEmbedding).X 1 ≅ Q.X 2 :=
    Q.restrictionXIso kernelTailEmbedding (i := 1) (i' := 2)
      kernelTailEmbedding_f_one
  let e₃ : ((single₀ C).obj (kernel (π.f 0))).X 0 ≅ kernel (π.f 0) :=
    HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (kernel (π.f 0))
  have hd : (Q.restriction kernelTailEmbedding).d 1 0 =
      e₁.hom ≫ Q.d 2 1 ≫ e₀.inv :=
    Q.restriction_d_eq kernelTailEmbedding (i := 1) (j := 0)
      (i' := 2) (j' := 1) kernelTailEmbedding_f_one kernelTailEmbedding_f_zero
  let S : ShortComplex C := ShortComplex.mk
    ((Q.restriction kernelTailEmbedding).d 1 0)
    ((kernelTailAugmentation π).f 0) (by
      rw [← (kernelTailAugmentation π).comm 1 0,
        HomologicalComplex.single_obj_d, comp_zero])
  let N : ShortComplex C := ShortComplex.mk (Q.d 2 1) q (by
    apply (cancel_mono (kernel.ι (π.f 0))).1
    rw [Category.assoc, kernel.lift_ι, Q.d_comp_d, zero_comp])
  let e : S ≅ N := ShortComplex.isoMk (S₁ := S) (S₂ := N) e₁ e₀ e₃
    (by
      change e₁.hom ≫ Q.d 2 1 =
        (Q.restriction kernelTailEmbedding).d 1 0 ≫ e₀.hom
      rw [hd]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change e₀.hom ≫ q = (kernelTailAugmentation π).f 0 ≫ e₃.hom
      rw [kernelTailAugmentation_f_zero]
      have hleft : e₀.hom ≫ q ≍ q :=
        eqToHom_comp_heq q (congrArg Q.X kernelTailEmbedding_f_zero)
      have hright : q ≫ e₃.hom ≍ q :=
        comp_eqToHom_heq q (ChainComplex.single₀_obj_zero (kernel (π.f 0))).symm
      exact eq_of_heq (hleft.trans hright.symm))
  apply (quasiIsoAt_zero_iff_exact_and_epi_augmentation _).mpr
  change S.Exact ∧ Epi S.g
  exact (ShortComplex.exact_and_epi_g_iff_of_iso e).mpr
    ⟨exact_kernelLift_augmentation π, epi_kernelLift_augmentation π⟩

private lemma exactAt_restriction_positive (Q : ChainComplex C ℕ) (n : ℕ)
    (hQ : Q.ExactAt (n + 2)) :
    (Q.restriction kernelTailEmbedding).ExactAt (n + 1) := by
  have hQsc : (Q.sc' (n + 3) (n + 2) (n + 1)).Exact :=
    (HomologicalComplex.exactAt_iff' Q (n + 3) (n + 2) (n + 1)
      (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
      (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))).mp hQ
  apply (HomologicalComplex.exactAt_iff'
    (Q.restriction kernelTailEmbedding)
    (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (ComplexShape.down_mk _ _ rfl))
    (ComplexShape.next_eq' _ (ComplexShape.down_mk _ _ rfl))).mpr
  let e₁ : (Q.restriction kernelTailEmbedding).X (n + 2) ≅ Q.X (n + 3) :=
    Q.restrictionXIso kernelTailEmbedding (kernelTailEmbedding_f (n + 2))
  let e₂ : (Q.restriction kernelTailEmbedding).X (n + 1) ≅ Q.X (n + 2) :=
    Q.restrictionXIso kernelTailEmbedding (kernelTailEmbedding_f (n + 1))
  let e₃ : (Q.restriction kernelTailEmbedding).X n ≅ Q.X (n + 1) :=
    Q.restrictionXIso kernelTailEmbedding (kernelTailEmbedding_f n)
  let e : (Q.restriction kernelTailEmbedding).sc' (n + 2) (n + 1) n ≅
      Q.sc' (n + 3) (n + 2) (n + 1) :=
    ShortComplex.isoMk e₁ e₂ e₃
      (by
        change e₁.hom ≫ Q.d (n + 3) (n + 2) =
          (Q.restriction kernelTailEmbedding).d (n + 2) (n + 1) ≫ e₂.hom
        rw [Q.restriction_d_eq kernelTailEmbedding
          (kernelTailEmbedding_f (n + 2)) (kernelTailEmbedding_f (n + 1))]
        dsimp only [e₁, e₂]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by
        change e₂.hom ≫ Q.d (n + 2) (n + 1) =
          (Q.restriction kernelTailEmbedding).d (n + 1) n ≫ e₃.hom
        rw [Q.restriction_d_eq kernelTailEmbedding
          (kernelTailEmbedding_f (n + 1)) (kernelTailEmbedding_f n)]
        dsimp only [e₂, e₃]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact (ShortComplex.exact_iff_of_iso e).mpr hQsc

/-- An augmented quasi-isomorphism supplies an augmented quasi-isomorphism on its kernel tail. -/
lemma quasiIso_kernelTailAugmentation (π : Q ⟶ (single₀ C).obj M) [QuasiIso π] :
    QuasiIso (kernelTailAugmentation π) := by
  refine ⟨fun i => ?_⟩
  cases i with
  | zero =>
      have : QuasiIsoAt π 0 := (inferInstance : QuasiIso π).quasiIsoAt 0
      have : QuasiIsoAt π 1 := (inferInstance : QuasiIso π).quasiIsoAt 1
      exact quasiIsoAt_zero_kernelTailAugmentation π
  | succ n =>
      apply (quasiIsoAt_iff_exactAt' (kernelTailAugmentation π) (n + 1)
        (exactAt_succ_single_obj (kernel (π.f 0)) n)).mpr
      apply exactAt_restriction_positive
      have : QuasiIsoAt π (n + 2) := (inferInstance : QuasiIso π).quasiIsoAt (n + 2)
      exact (exactAt_iff_of_quasiIsoAt π (n + 2)).mpr
        (exactAt_succ_single_obj M (n + 1))

end ChainComplex

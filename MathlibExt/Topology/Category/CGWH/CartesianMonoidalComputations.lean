/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# Computations for the original cartesian tensor and its canonical symmetry

These are the same public computations and generated-continuity proof.
The foundational cartesian monoidal structure remains in CartesianMonoidal.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
public section

namespace CGWH

/-- The braiding is the canonical swap determined by the chosen cartesian products. -/
@[expose] public noncomputable local instance cartesianBraidedCategory : BraidedCategory CGWH.{u, v} :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- The inverse of the original product carrier comparison is continuous
on the existing compact Hausdorff probes. This is the same product proof
formerly private in CartesianClosed, now reused without a second copy. -/
public theorem tensorEquivProd_symm_continuousGeneratedBy
    (A Y : CGWH.{u, v}) :
    ContinuousGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (tensorEquivProd A Y).symm := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let H := WithGeneratedByTopology P (A × Y)
  let _ : UCompactlyGeneratedSpace.{u} H :=
    (isGeneratedBy_compactHausProbes_iff (Y := H)).1 inferInstance
  have hWeak : UWeakHausdorffSpace.{u} H := by
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K f g
    let fstH : C(H, A) :=
      ⟨fun p ↦ (WithGeneratedByTopology.equiv p : A × Y).1,
        continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩
    let sndH : C(H, Y) :=
      ⟨fun p ↦ (WithGeneratedByTopology.equiv p : A × Y).2,
        continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩
    have hSet : {k | f k = g k} =
        {k | fstH (f k) = fstH (g k)} ∩
          {k | sndH (f k) = sndH (g k)} := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro h
        rw [h]
        exact ⟨rfl, rfl⟩
      · rintro ⟨h₁, h₂⟩
        apply WithGeneratedByTopology.equiv.injective
        exact Prod.ext h₁ h₂
    rw [hSet]
    apply IsClosed.inter
    · exact (uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance)
        K (fstH.comp f) (fstH.comp g)
    · exact (uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance)
        K (sndH.comp f) (sndH.comp g)
  let _ : UWeakHausdorffSpace.{u} H := hWeak
  let Q : CGWH.{u, v} := CGWH.of H
  let fstQ : Q ⟶ A := ConcreteCategory.ofHom
    ⟨fun p ↦ (WithGeneratedByTopology.equiv p : A × Y).1,
      continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩
  let sndQ : Q ⟶ Y := ConcreteCategory.ofHom
    ⟨fun p ↦ (WithGeneratedByTopology.equiv p : A × Y).2,
      continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩
  let lift : Q ⟶ A ⊗ Y := CartesianMonoidalCategory.lift fstQ sndQ
  let toQ : ContinuousMapGeneratedBy P (A × Y) H :=
    WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy P (A × Y)
  let liftP : ContinuousMapGeneratedBy P H (A ⊗ Y : CGWH.{u, v}) :=
    ⟨lift, (ConcreteCategory.hom lift).continuous.continuousGeneratedBy⟩
  let q : ContinuousMapGeneratedBy P (A × Y) (A ⊗ Y : CGWH.{u, v}) :=
    liftP.comp toQ
  have hq : ((tensorEquivProd A Y).symm : (A × Y) →
      (A ⊗ Y : CGWH.{u, v})) = (q : (A × Y) →
        (A ⊗ Y : CGWH.{u, v})) := by
    funext p
    apply (tensorEquivProd A Y).injective
    apply Prod.ext
    · rw [Equiv.apply_symm_apply, tensorEquivProd_apply_fst]
      have hk := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_fst fstQ sndQ) (toQ p)
      change (CartesianMonoidalCategory.fst A Y) (q p) = p.1 at hk
      exact hk.symm
    · rw [Equiv.apply_symm_apply, tensorEquivProd_apply_snd]
      have hk := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_snd fstQ sndQ) (toQ p)
      change (CartesianMonoidalCategory.snd A Y) (q p) = p.2 at hk
      exact hk.symm
  rw [hq]
  exact q.prop

/-- Left whiskering preserves the original paired tensor point. -/
public theorem tensorMk_whiskerLeft {A B B' : CGWH.{u, v}}
    (f : B ⟶ B') (a : A) (b : B) :
    (A ◁ f) (tensorMk a b) = tensorMk a (f b) := by
  apply (tensorEquivProd A B').injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_fst A f) (tensorMk a b)
    simpa only [ConcreteCategory.comp_apply, tensorMk_fst] using h
  · rw [tensorEquivProd_apply_snd]
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerLeft_snd A f) (tensorMk a b)
    simpa only [ConcreteCategory.comp_apply, tensorMk_snd] using h

/-- The actual native symmetry swaps the two original paired tensor points. -/
public theorem tensorMk_braiding {A B : CGWH.{u, v}} (a : A) (b : B) :
    letI : BraidedCategory CGWH.{u, v} := CGWH.cartesianBraidedCategory.{u, v}
    (β_ A B).hom (tensorMk a b) = tensorMk b a := by
  letI : BraidedCategory CGWH.{u, v} := CGWH.cartesianBraidedCategory.{u, v}
  apply (tensorEquivProd B A).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    simpa only [ConcreteCategory.comp_apply, tensorMk_snd] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.braiding_hom_fst A B) (tensorMk a b)
  · rw [tensorEquivProd_apply_snd]
    simpa only [ConcreteCategory.comp_apply, tensorMk_fst] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.braiding_hom_snd A B) (tensorMk a b)

/-- The inverse original left unit map has its actual paired native value. -/
public theorem leftUnitor_inv_tensorMk (A : CGWH.{u, v}) (a : A) :
    (λ_ A).inv a = tensorMk (CartesianMonoidalCategory.toUnit A a) a := by
  apply (tensorEquivProd (𝟙_ CGWH.{u, v}) A).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.leftUnitor_inv_fst A) a
  · rw [tensorEquivProd_apply_snd]
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.leftUnitor_inv_snd A) a


end CGWH

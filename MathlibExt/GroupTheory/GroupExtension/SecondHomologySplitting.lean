/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.GroupTheory.GroupExtension.UniversalRecognition
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Central extensions of perfect groups with vanishing second integral homology

The native degree-one bar differential is surjective for a perfect group.
Vanishing native second integral homology makes every bar two-cycle a
boundary. A central factor set therefore factors through the degree-one
differential, and its resulting one-cochain corrects the original section
to a splitting of the original extension.

Kernel, total and quotient groups keep independent universes. The homology
hypothesis uses the native lifted integer representation of the actual group.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open scoped TensorProduct

universe u v w u' v'

namespace GroupExtension

private def barTwoCochain {G : Type u} {A : Type v} [AddCommGroup A]
    (c : G → G → A) : (G × G →₀ ULift.{u} ℤ) →+ A :=
  Finsupp.liftAddHom (fun p => (zmultiplesHom A (c p.1 p.2)).comp
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toAddEquiv.toAddMonoidHom)

private theorem barTwoCochain_single {G : Type u} {A : Type v}
    [AddCommGroup A] (c : G → G → A) (g h : G) (n : ULift.{u} ℤ) :
    barTwoCochain c (Finsupp.single (g, h) n) = n.down • c g h := by
  rw [barTwoCochain, Finsupp.liftAddHom_apply_single]
  rfl

private theorem barOneDifferential_surjective (G : Type u) [Group G] [Group.IsPerfect G] :
    Function.Surjective
      (groupHomology.d₂₁ (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))) := by
  let Z := Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)
  let _ : Group.IsPerfect (Group.Abelianization G) := by
    change Group.IsPerfect (G ⧸ commutator G)
    infer_instance
  let _ : Subsingleton (Group.Abelianization G) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  let _ : Subsingleton (Additive (Group.Abelianization G) ⊗[ℤ] Z) := inferInstance
  let _ : Subsingleton (groupHomology Z 1) :=
    (groupHomology.H1AddEquivOfIsTrivial Z).injective.subsingleton
  intro z
  have hz : z ∈ groupHomology.cycles₁ Z := by
    rw [groupHomology.cycles₁_eq_top_of_isTrivial]
    trivial
  have hbound := (groupHomology.H1π_eq_zero_iff (⟨z, hz⟩ : groupHomology.cycles₁ Z)).mp
    (Subsingleton.elim _ _)
  exact hbound

private theorem barTwoCochain_exists_primitive {G : Type u} {A : Type v}
    [Group G] [Group.IsPerfect G] [AddCommGroup A]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) 2))
    (c : G → G → A)
    (hc : ∀ g h k, c g h + c (g * h) k = c g (h * k) + c h k) :
    ∃ b : G → A, ∀ g h, c g h = b h - b (g * h) + b g := by
  let Z := Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)
  let C := barTwoCochain c
  let d := (groupHomology.d₂₁ Z).hom.toAddMonoidHom
  have hboundary : ∀ z : G × G × G →₀ ULift.{u} ℤ, C (groupHomology.d₃₂ Z z) = 0 := by
    intro z
    induction z using Finsupp.induction with
    | zero => simp
    | single_add p n z hp hn ih =>
      simp only [map_add, ih, add_zero]
      apply (congrArg C (groupHomology.d₃₂_single (A := Z) p n)).trans
      change barTwoCochain c
        (Finsupp.single (p.2.1, p.2.2) (Z.ρ p.1⁻¹ n) -
          Finsupp.single (p.1 * p.2.1, p.2.2) n +
          Finsupp.single (p.1, p.2.1 * p.2.2) n -
          Finsupp.single (p.1, p.2.1) n) = 0
      simp only [isTrivial_apply, map_sub, map_add, barTwoCochain_single]
      rw [barTwoCochain_single c p.2.1 p.2.2 n]
      have hzero : c p.2.1 p.2.2 - c (p.1 * p.2.1) p.2.2 +
          c p.1 (p.2.1 * p.2.2) - c p.1 p.2.1 = 0 := by
        calc
          _ = (c p.1 (p.2.1 * p.2.2) + c p.2.1 p.2.2) -
              (c p.1 p.2.1 + c (p.1 * p.2.1) p.2.2) := by abel
          _ = 0 := sub_eq_zero.mpr (hc p.1 p.2.1 p.2.2).symm
      rw [← smul_sub, ← smul_add, ← smul_sub, hzero, smul_zero]
  have hker : d.ker ≤ C.ker := by
    intro z hz
    apply AddMonoidHom.mem_ker.mpr
    have hz₂ : z ∈ groupHomology.cycles₂ Z := hz
    let _ : Subsingleton (groupHomology Z 2) := ModuleCat.subsingleton_of_isZero h₂
    have hbound := (groupHomology.H2π_eq_zero_iff (⟨z, hz₂⟩ : groupHomology.cycles₂ Z)).mp
      (Subsingleton.elim _ _)
    obtain ⟨t, ht⟩ := hbound
    exact (congrArg C ht).symm.trans (hboundary t)
  have hsurj : Function.Surjective d := barOneDifferential_surjective G
  let B := d.liftOfSurjective hsurj ⟨C, hker⟩
  have hcomp : B.comp d = C :=
    congrArg Subtype.val ((d.liftOfSurjective hsurj).symm_apply_apply ⟨C, hker⟩)
  refine ⟨fun g => B (Finsupp.single g 1), ?_⟩
  intro g h
  have hb := DFunLike.congr_fun hcomp (Finsupp.single (g, h) 1)
  have hleft : C (Finsupp.single (g, h) 1) = c g h :=
    (barTwoCochain_single c g h 1).trans (one_zsmul _)
  have hright : B (d (Finsupp.single (g, h) 1)) =
      B (Finsupp.single h 1) - B (Finsupp.single (g * h) 1) + B (Finsupp.single g 1) := by
    apply (congrArg B (groupHomology.d₂₁_single (A := Z) (g, h) 1)).trans
    simp only [isTrivial_apply, map_sub, map_add]
  exact hleft.symm.trans (hb.symm.trans hright)

private abbrev kernelCommGroup {N : Type v} {E : Type w} {G : Type u}
    [Group N] [Group E] [Group G] (S : GroupExtension N E G) (hS : S.IsCentral) :
    CommGroup N :=
  { (inferInstance : Group N) with
    mul_comm a b := S.inl_injective (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp (hS (S.rightHom_inl b)) (S.inl a)) }

/-- Every original central extension of a perfect group with vanishing native second
integral homology splits, with independent kernel, total and quotient universes. -/
theorem IsCentral.nonempty_splitting_of_isZero_secondHomology
    {N : Type v} {E : Type w} {G : Type u} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G) (hS : S.IsCentral) [Group.IsPerfect G]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) 2)) :
    Nonempty S.Splitting := by
  let _ : CommGroup N := kernelCommGroup S hS
  let σ := S.surjInvRightHom
  let c : G → G → N := fun g h =>
    (σ.mul_mul_mul_inv_mem_range_inl g h).choose
  have hc : ∀ g h, σ g * σ h = S.inl (c g h) * σ (g * h) := by
    intro g h
    simpa only [inv_mul_cancel_right] using
      (congrArg (fun z => z * σ (g * h))
        (σ.mul_mul_mul_inv_mem_range_inl g h).choose_spec).symm
  have hcentral : ∀ n : N, ∀ z : E, Commute (S.inl n) z := by
    intro n z
    exact (Subgroup.mem_center_iff.mp (hS (S.rightHom_inl n)) z).symm
  have hcocycle : ∀ g h k, c g h * c (g * h) k = c g (h * k) * c h k := by
    intro g h k
    apply S.inl_injective
    apply mul_right_cancel
    calc
      S.inl (c g h * c (g * h) k) * σ (g * (h * k)) =
          S.inl (c g h) * (S.inl (c (g * h) k) * σ ((g * h) * k)) := by
        rw [map_mul, mul_assoc, mul_assoc g h k]
      _ = S.inl (c g h) * (σ (g * h) * σ k) := by rw [← hc (g * h) k]
      _ = (σ g * σ h) * σ k := by rw [← mul_assoc, ← hc g h]
      _ = σ g * (σ h * σ k) := mul_assoc _ _ _
      _ = σ g * (S.inl (c h k) * σ (h * k)) := by rw [hc h k]
      _ = S.inl (c h k) * (σ g * σ (h * k)) := by
        rw [← mul_assoc, (hcentral (c h k) (σ g)).eq.symm, mul_assoc]
      _ = S.inl (c h k) * (S.inl (c g (h * k)) * σ (g * (h * k))) := by
        rw [hc g (h * k)]
      _ = S.inl (c h k * c g (h * k)) * σ (g * (h * k)) := by
        rw [S.inl.map_mul (c h k) (c g (h * k)), mul_assoc]
      _ = S.inl (c g (h * k) * c h k) * σ (g * (h * k)) := by
        rw [mul_comm (c h k) (c g (h * k))]
  obtain ⟨b, hb⟩ := barTwoCochain_exists_primitive h₂
    (fun g h => Additive.ofMul (c g h))
    (fun g h k => congrArg Additive.ofMul (hcocycle g h k))
  have hcorrection : ∀ g h,
      (Additive.toMul (b g))⁻¹ * (Additive.toMul (b h))⁻¹ * c g h =
        (Additive.toMul (b (g * h)))⁻¹ := by
    intro g h
    have ht := congrArg Additive.toMul (hb g h)
    simp only [toMul_ofMul, toMul_add, toMul_sub,
      div_eq_mul_inv] at ht
    rw [ht]
    calc
      _ = (Additive.toMul (b g))⁻¹ *
          (((Additive.toMul (b h))⁻¹ * Additive.toMul (b h)) *
            ((Additive.toMul (b (g * h)))⁻¹ * Additive.toMul (b g))) := by
        simp only [mul_assoc]
      _ = (Additive.toMul (b g))⁻¹ *
          ((Additive.toMul (b (g * h)))⁻¹ * Additive.toMul (b g)) := by
        rw [inv_mul_cancel, one_mul]
      _ = (Additive.toMul (b g))⁻¹ *
          (Additive.toMul (b g) * (Additive.toMul (b (g * h)))⁻¹) := by
        rw [mul_comm (Additive.toMul (b (g * h)))⁻¹ (Additive.toMul (b g))]
      _ = (Additive.toMul (b (g * h)))⁻¹ := by
        rw [inv_mul_cancel_left]
  let ρ : G → E := fun g => S.inl ((Additive.toMul (b g))⁻¹) * σ g
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := by
    intro g h
    change S.inl ((Additive.toMul (b (g * h)))⁻¹) * σ (g * h) =
      (S.inl ((Additive.toMul (b g))⁻¹) * σ g) *
        (S.inl ((Additive.toMul (b h))⁻¹) * σ h)
    symm
    calc
      _ = (S.inl ((Additive.toMul (b g))⁻¹) *
          S.inl ((Additive.toMul (b h))⁻¹)) * (σ g * σ h) := by
        calc
          _ = S.inl ((Additive.toMul (b g))⁻¹) *
              ((σ g * S.inl ((Additive.toMul (b h))⁻¹)) * σ h) := by
            simp only [mul_assoc]
          _ = S.inl ((Additive.toMul (b g))⁻¹) *
              ((S.inl ((Additive.toMul (b h))⁻¹) * σ g) * σ h) := by
            rw [(hcentral ((Additive.toMul (b h))⁻¹) (σ g)).eq.symm]
          _ = _ := by simp only [mul_assoc]
      _ = S.inl ((Additive.toMul (b g))⁻¹ * (Additive.toMul (b h))⁻¹ * c g h) *
          σ (g * h) := by
        rw [hc g h, S.inl.map_mul
          ((Additive.toMul (b g))⁻¹ * (Additive.toMul (b h))⁻¹) (c g h),
          S.inl.map_mul (Additive.toMul (b g))⁻¹ (Additive.toMul (b h))⁻¹]
        simp only [mul_assoc]
      _ = S.inl ((Additive.toMul (b (g * h)))⁻¹) * σ (g * h) := by rw [hcorrection]
  refine ⟨Splitting.mk (MonoidHom.mk' ρ hmul) ?_⟩
  intro g
  change S.rightHom (S.inl ((Additive.toMul (b g))⁻¹) * σ g) = g
  rw [map_mul, S.rightHom_inl, σ.rightHom_section, one_mul]

/-- A central extension with perfect total group and vanishing native second integral
homology is universal in any specified target kernel and total universes. -/
theorem IsCentral.isUniversalFor_of_isZero_secondHomology
    {N : Type v} {E : Type w} {G : Type u} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G} (hS : S.IsCentral) [Group.IsPerfect E]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{w} ℤ) E (ULift.{w} ℤ)) 2)) :
    IsUniversalFor.{v, w, u, u', v'} S := by
  refine ⟨hS, ?_⟩
  intro K D _ _ T hT
  obtain ⟨f, hf⟩ := (T.nonempty_splitting_pullback_iff_exists_lift S.rightHom).mp
    (IsCentral.nonempty_splitting_of_isZero_secondHomology
      (pullbackExtension T S.rightHom) (pullback_isCentral T S.rightHom hT) h₂)
  refine ⟨f, hf, fun g hg => ?_⟩
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hT (hg.trans hf.symm)

/-- The original fixed-universe universality predicate follows from the same native
perfectness and second-homology hypotheses. -/
theorem IsCentral.isUniversal_of_isZero_secondHomology
    {N : Type v} {E : Type w} {G : Type u} [Group N] [Group E] [Group G]
    {S : GroupExtension N E G} (hS : S.IsCentral) [Group.IsPerfect E]
    (h₂ : IsZero (groupHomology (Rep.trivial (ULift.{w} ℤ) E (ULift.{w} ℤ)) 2)) :
    S.IsUniversal :=
  hS.isUniversalFor_of_isZero_secondHomology h₂

end GroupExtension

end

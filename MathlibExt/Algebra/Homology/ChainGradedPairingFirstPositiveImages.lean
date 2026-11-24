/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositive
public import MathlibExt.Algebra.Homology.ChainGradedPairingPositiveImages
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact one-positive-factor images and their native quotient coordinates

The first bidegree is positive and the second is unrestricted in Nat. Native
total generators and the earned positive inclusion give the range equality;
no flatness or tensor-monomorphism assumption is used. Evaluation of the native
cokernel and the native module range quotient give the component isomorphism.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe u v

namespace HomologicalComplex.ChainGradedPairing

variable {R : Type u} [Ring R]
  [MonoidalCategory (ModuleCat.{v} R)] [MonoidalPreadditive (ModuleCat.{v} R)]
  {K₁ K₂ K₃ : ChainComplex (ModuleCat.{v} R) ℕ}
  (P : ChainGradedPairing K₁ K₂ K₃) (h₁ : K₁.d 1 0 = 0)

local notation "e₊" => ComplexShape.positiveNatEmbedding

/-- The exact degree pairs in the full positive-ideal action. -/
abbrev FirstPositiveDegree (n : ℕ) := {z : ℕ × ℕ // 0 < z.1 ∧ z.1 + z.2 = n}

/-- Sum of all original p>0, q≥0 component images in the original target. -/
def firstPositiveImages (n : ℕ) : Submodule R (K₃.X n) :=
  ⨆ z : FirstPositiveDegree n, LinearMap.range (pairAt P z.1.1 z.1.2 n z.2.2).hom

theorem pairAt_mem_firstPositiveImages (p q n : ℕ) (h : p + q = n) (hp : 0 < p)
    (x : ↥(K₁.X p ⊗ K₂.X q)) : (pairAt P p q n h).hom x ∈ firstPositiveImages P n :=
  Submodule.mem_iSup_of_mem ⟨(p, q), hp, h⟩ ⟨x, rfl⟩

private theorem firstPositiveComponent_mem (p q n : ℕ) (h : p + q = n)
    (x : ↥((K₁.stupidTrunc e₊).X p ⊗ K₂.X q)) :
    (pairAt (firstPositivePairing P h₁) p q n h).hom x ∈ firstPositiveImages P n := by
  by_cases hp : p = 0
  · subst p
    rw [pairAt, firstPositivePairing_pairAt, positiveStupidTruncInclusion_f_zero]
    simp
  · rw [pairAt, firstPositivePairing_pairAt]
    exact pairAt_mem_firstPositiveImages P p q n h (Nat.pos_of_ne_zero hp) _

private def firstPositiveComponentFactor (n : ℕ) :
    (tensorObj (K₁.stupidTrunc e₊) K₂).X n ⟶ ModuleCat.of R (firstPositiveImages P n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => ModuleCat.ofHom
    ((pairAt (firstPositivePairing P h₁) p q n h).hom.codRestrict
      (firstPositiveImages P n) (firstPositiveComponent_mem P h₁ p q n h)))

private theorem firstPositiveComponentFactor_comp (n : ℕ) :
    firstPositiveComponentFactor P h₁ n ≫ ModuleCat.ofHom (firstPositiveImages P n).subtype =
      (firstPositivePairing P h₁).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hc := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := K₁.stupidTrunc e₊) (K₂ := K₂)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{v} R))
    (c := ComplexShape.down ℕ) (j := n)
    (fun p q h => ModuleCat.ofHom
      ((pairAt (firstPositivePairing P h₁) p q n h).hom.codRestrict
        (firstPositiveImages P n) (firstPositiveComponent_mem P h₁ p q n h))) p q h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ ModuleCat.ofHom (firstPositiveImages P n).subtype) hc)

/-- The native strict first-factor pairing has precisely the full p>0,q≥0 range sum. -/
theorem range_firstPositivePairing (n : ℕ) :
    LinearMap.range ((firstPositivePairing P h₁).f n).hom = firstPositiveImages P n := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have h := ConcreteCategory.congr_hom (firstPositiveComponentFactor_comp P h₁ n) x
    exact h ▸ ((firstPositiveComponentFactor P h₁ n).hom x).property
  · apply iSup_le
    rintro ⟨⟨p, q⟩, hp, h⟩ y ⟨x, rfl⟩
    let g := (K₁.positiveStupidTruncInclusion h₁).f p ⊗ₘ (𝟙 K₂ : K₂ ⟶ K₂).f q
    let : IsIso g := by
      dsimp only [g]
      rw [positiveStupidTruncInclusion_f K₁ h₁ (i := p - 1) (i' := p) (by omega)]
      infer_instance
    let e := asIso g
    have hg : e.inv ≫ pairAt (firstPositivePairing P h₁) p q n h = pairAt P p q n h := by
      rw [pairAt, firstPositivePairing_pairAt]
      exact e.inv_hom_id_assoc _
    refine ⟨(ιTensorObj (K₁.stupidTrunc e₊) K₂ p q n h).hom (e.inv.hom x), ?_⟩
    exact ConcreteCategory.congr_hom hg x

theorem firstPositiveImages_zero : firstPositiveImages P 0 = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨⟨p, q⟩, hp, h⟩
    omega
  · exact bot_le

/-- Every original first-positive component is killed by the actual native projection. -/
theorem pairAt_comp_firstPositiveProjection (p q n : ℕ) (h : p + q = n) (hp : 0 < p)
    (x : ↥(K₁.X p ⊗ K₂.X q)) :
    ((firstPositiveProjection P h₁).f n).hom ((pairAt P p q n h).hom x) = 0 := by
  have hm := pairAt_mem_firstPositiveImages P p q n h hp x
  rw [← range_firstPositivePairing P h₁ n] at hm
  obtain ⟨z, hz⟩ := hm
  have hc : (firstPositivePairing P h₁).f n ≫ (firstPositiveProjection P h₁).f n = 0 := by
    simpa only [comp_f, zero_f] using
      congrArg (fun f => f.f n) (firstPositivePairing_comp_projection P h₁)
  exact (congrArg ((firstPositiveProjection P h₁).f n).hom hz).symm.trans
    (ConcreteCategory.congr_hom hc z)

/-- The actual module quotient degree, without introducing another chain engine. -/
def firstPositiveDegreeQuotient (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R ((K₃.X n) ⧸ firstPositiveImages P n)

/-- Native evaluation/cokernel preservation identifies this component quotient. -/
def firstPositiveCokernelDegreeIso (n : ℕ) :
    (firstPositiveCokernel P h₁).X n ≅ firstPositiveDegreeQuotient P n :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
      (firstPositivePairing P h₁) ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((firstPositivePairing P h₁).f n) ≪≫
    (Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)).toModuleIso

/-- The component comparison is characterized by the original quotient projection. -/
theorem firstPositiveProjection_degreeIso (n : ℕ) :
    (firstPositiveProjection P h₁).f n ≫ (firstPositiveCokernelDegreeIso P h₁ n).hom =
      ModuleCat.ofHom (firstPositiveImages P n).mkQ := by
  let F := HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n
  let f := firstPositivePairing P h₁
  let e := Submodule.quotEquivOfEq _ _ (range_firstPositivePairing P h₁ n)
  have h1 := PreservesCokernel.π_iso_hom F f
  have h2 := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (f.f n)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h12 := congrArg (fun g => g ≫
    (ModuleCat.cokernelIsoRangeQuotient (f.f n)).hom ≫ e.toModuleIso.hom) h1
  have h23 := congrArg (fun g => g ≫ e.toModuleIso.hom) h2
  have hc : (firstPositiveProjection P h₁).f n ≫ (firstPositiveCokernelDegreeIso P h₁ n).hom =
      ModuleCat.ofHom (LinearMap.range (f.f n).hom).mkQ ≫ e.toModuleIso.hom := by
    have hleft : (firstPositiveProjection P h₁).f n ≫ (firstPositiveCokernelDegreeIso P h₁ n).hom =
        (F.map (cokernel.π f) ≫ (PreservesCokernel.iso F f).hom) ≫
          (ModuleCat.cokernelIsoRangeQuotient (f.f n)).hom ≫ e.toModuleIso.hom := by
      simp only [firstPositiveCokernelDegreeIso, Category.assoc]
      rfl
    exact hleft.trans (h12.trans h23)
  exact (ConcreteCategory.congr_hom hc x).trans
    (Submodule.quotEquivOfEq_mk _ _ (range_firstPositivePairing P h₁ n) x)

end HomologicalComplex.ChainGradedPairing

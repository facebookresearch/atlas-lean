/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe

/-!
# Horseshoe endpoint coordinates from degreewise splittings

For projective horseshoe data in an abelian category, a chosen
splitting of each resolution row gives biproduct coordinates for the
middle terms. The chain-map equations identify the differential
diagonals with the endpoint differentials and make the left-source
to right-target component zero.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution.HorseshoeData
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} {hS : S.ShortExact}
variable {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact,
`P₁,P₃` endpoint projective resolutions, and `H` horseshoe data.
A splitting of every row `P₁,n → P₂,n → P₃,n` gives an endpoint
coordinate specification: `P₂,n ≅ P₁,n ⊞ P₃,n`, left inclusion,
right projection, endpoint differential diagonals, and zero
`P₁,n+1 → P₃,n` differential component. -/
def specOfSplittings (H : HorseshoeData hS P₁ P₃)
    (s : ∀ n : ℕ, (ShortComplex.mk (H.i.f n) (H.p.f n)
      (HomologicalComplex.congr_hom H.zero n)).Splitting) : H.Spec where
  middleXIso n := (s n).isoBinaryBiproduct
  i_f n := by
    have hf : (s n).isoBinaryBiproduct.hom ≫
        (biprod.fst : P₁.complex.X n ⊞ P₃.complex.X n ⟶ P₁.complex.X n) = (s n).r := by
      change biprod.lift (s n).r (H.p.f n) ≫ biprod.fst = (s n).r
      exact biprod.lift_fst _ _
    have hg : (s n).isoBinaryBiproduct.hom ≫
        (biprod.snd : P₁.complex.X n ⊞ P₃.complex.X n ⟶ P₃.complex.X n) = H.p.f n := by
      change biprod.lift (s n).r (H.p.f n) ≫ biprod.snd = H.p.f n
      exact biprod.lift_snd _ _
    apply biprod.hom_ext
    · rw [Category.assoc, hf, biprod.inl_fst]
      exact (s n).f_r
    · rw [Category.assoc, hg, biprod.inl_snd]
      exact HomologicalComplex.congr_hom H.zero n
  p_f n := by
    have hi : (biprod.inl : P₁.complex.X n ⟶ P₁.complex.X n ⊞ P₃.complex.X n) ≫
        (s n).isoBinaryBiproduct.inv = H.i.f n := by
      change biprod.inl ≫ biprod.desc (H.i.f n) (s n).s = H.i.f n
      exact biprod.inl_desc _ _
    have hs : (biprod.inr : P₃.complex.X n ⟶ P₁.complex.X n ⊞ P₃.complex.X n) ≫
        (s n).isoBinaryBiproduct.inv = (s n).s := by
      change biprod.inr ≫ biprod.desc (H.i.f n) (s n).s = (s n).s
      exact biprod.inr_desc _ _
    apply biprod.hom_ext'
    · rw [← Category.assoc, hi, biprod.inl_snd]
      exact HomologicalComplex.congr_hom H.zero n
    · rw [← Category.assoc, hs, biprod.inr_snd]
      exact (s n).s_g
  middle_d n := by
    let a : P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1) ⟶
        P₁.complex.X n ⊞ P₃.complex.X n := (s (n + 1)).isoBinaryBiproduct.inv ≫
            H.middle.complex.d (n + 1) n ≫
      (s n).isoBinaryBiproduct.hom
    have hf : (s n).isoBinaryBiproduct.hom ≫
        (biprod.fst : P₁.complex.X n ⊞ P₃.complex.X n ⟶ P₁.complex.X n) = (s n).r := by
      change biprod.lift (s n).r (H.p.f n) ≫ biprod.fst = (s n).r
      exact biprod.lift_fst _ _
    have hg : (s n).isoBinaryBiproduct.hom ≫
        (biprod.snd : P₁.complex.X n ⊞ P₃.complex.X n ⟶ P₃.complex.X n) = H.p.f n := by
      change biprod.lift (s n).r (H.p.f n) ≫ biprod.snd = H.p.f n
      exact biprod.lift_snd _ _
    have hi : (biprod.inl : P₁.complex.X (n + 1) ⟶ P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ≫
        (s (n + 1)).isoBinaryBiproduct.inv = H.i.f (n + 1) := by
      change biprod.inl ≫ biprod.desc (H.i.f (n + 1)) (s (n + 1)).s = H.i.f (n + 1)
      exact biprod.inl_desc _ _
    have hs : (biprod.inr : P₃.complex.X (n + 1) ⟶ P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ≫
        (s (n + 1)).isoBinaryBiproduct.inv = (s (n + 1)).s := by
      change biprod.inr ≫ biprod.desc (H.i.f (n + 1)) (s (n + 1)).s = (s (n + 1)).s
      exact biprod.inr_desc _ _
    have hr : H.i.f n ≫ (s n).r = 𝟙 (P₁.complex.X n) := (s n).f_r
    have hsp : (s (n + 1)).s ≫ H.p.f (n + 1) = 𝟙 (P₃.complex.X (n + 1)) := (s (n + 1)).s_g
    have hz : H.i.f n ≫ H.p.f n = 0 := HomologicalComplex.congr_hom H.zero n
    have h₁₁ : biprod.inl ≫ a ≫ biprod.fst = P₁.complex.d (n + 1) n := by
      calc
        biprod.inl ≫ a ≫ biprod.fst =
            ((biprod.inl ≫ (s (n + 1)).isoBinaryBiproduct.inv) ≫
              H.middle.complex.d (n + 1) n) ≫ (s n).r := by
          dsimp only [a]
          simpa only [Category.assoc] using
            congrArg (fun q =>
              (biprod.inl : P₁.complex.X (n + 1) ⟶ P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ≫
              (s (n + 1)).isoBinaryBiproduct.inv ≫
              H.middle.complex.d (n + 1) n ≫ q) hf
        _ = (H.i.f (n + 1) ≫ H.middle.complex.d (n + 1) n) ≫ (s n).r :=
          congrArg (fun q => (q ≫ H.middle.complex.d (n + 1) n) ≫ (s n).r) hi
        _ = (P₁.complex.d (n + 1) n ≫ H.i.f n) ≫ (s n).r :=
          congrArg (fun q => q ≫ (s n).r) (H.i.comm (n + 1) n)
        _ = P₁.complex.d (n + 1) n ≫ (H.i.f n ≫ (s n).r) := Category.assoc _ _ _
        _ = P₁.complex.d (n + 1) n :=
          (congrArg (fun q => P₁.complex.d (n + 1) n ≫ q) hr).trans (Category.comp_id _)
    have h₁₂ : biprod.inl ≫ a ≫ biprod.snd = 0 := by
      calc
        biprod.inl ≫ a ≫ biprod.snd =
            ((biprod.inl ≫ (s (n + 1)).isoBinaryBiproduct.inv) ≫
              H.middle.complex.d (n + 1) n) ≫ H.p.f n := by
          dsimp only [a]
          simpa only [Category.assoc] using
            congrArg (fun q =>
              (biprod.inl : P₁.complex.X (n + 1) ⟶ P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ≫
              (s (n + 1)).isoBinaryBiproduct.inv ≫
              H.middle.complex.d (n + 1) n ≫ q) hg
        _ = (H.i.f (n + 1) ≫ H.middle.complex.d (n + 1) n) ≫ H.p.f n :=
          congrArg (fun q => (q ≫ H.middle.complex.d (n + 1) n) ≫ H.p.f n) hi
        _ = (P₁.complex.d (n + 1) n ≫ H.i.f n) ≫ H.p.f n :=
          congrArg (fun q => q ≫ H.p.f n) (H.i.comm (n + 1) n)
        _ = P₁.complex.d (n + 1) n ≫ (H.i.f n ≫ H.p.f n) := Category.assoc _ _ _
        _ = 0 := (congrArg (fun q => P₁.complex.d (n + 1) n ≫ q) hz).trans (comp_zero)
    have h₂₂ : biprod.inr ≫ a ≫ biprod.snd = P₃.complex.d (n + 1) n := by
      calc
        biprod.inr ≫ a ≫ biprod.snd =
            ((biprod.inr ≫ (s (n + 1)).isoBinaryBiproduct.inv) ≫
              H.middle.complex.d (n + 1) n) ≫ H.p.f n := by
          dsimp only [a]
          simpa only [Category.assoc] using
            congrArg (fun q =>
              (biprod.inr : P₃.complex.X (n + 1) ⟶ P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ≫
              (s (n + 1)).isoBinaryBiproduct.inv ≫
              H.middle.complex.d (n + 1) n ≫ q) hg
        _ = ((s (n + 1)).s ≫ H.middle.complex.d (n + 1) n) ≫ H.p.f n :=
          congrArg (fun q => (q ≫ H.middle.complex.d (n + 1) n) ≫ H.p.f n) hs
        _ = (s (n + 1)).s ≫ (H.middle.complex.d (n + 1) n ≫ H.p.f n) := Category.assoc _ _ _
        _ = (s (n + 1)).s ≫ (H.p.f (n + 1) ≫ P₃.complex.d (n + 1) n) :=
          congrArg (fun q => (s (n + 1)).s ≫ q) (H.p.comm (n + 1) n).symm
        _ = ((s (n + 1)).s ≫ H.p.f (n + 1)) ≫ P₃.complex.d (n + 1) n :=
          (Category.assoc _ _ _).symm
        _ = P₃.complex.d (n + 1) n :=
          (congrArg (fun q => q ≫ P₃.complex.d (n + 1) n) hsp).trans (Category.id_comp _)
    exact (Biprod.ofComponents_eq a).symm.trans (by
      rw [h₁₁, h₁₂, h₂₂])

end CategoryTheory.ProjectiveResolution.HorseshoeData

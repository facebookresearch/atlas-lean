/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathlibExt.Algebra.Homology.ProjectiveResolutionAugment
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Projective horseshoe with prescribed endpoint resolutions

In an abelian category, a short exact sequence `X₁ → X₂ → X₃`
and projective resolutions `P₁,P₃` give a projective resolution `P₂`
of `X₂` with a degreewise split row `P₁ → P₂ → P₃` preserving both
augmentations. In degree `n`, `P₂,n ≅ P₁,n ⊞ P₃,n`.
The middle differential has the two endpoint differentials on the
diagonal, zero component from `P₁,n+1` to `P₃,n`, and a cross
component from `P₃,n+1` to `P₁,n`. Only the supplied endpoint
resolutions are needed for this construction.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} (hS : S.ShortExact)
variable (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)

private noncomputable def horseshoeLiftZero : P₃.complex.X 0 ⟶ S.X₂ := by
  let _ : Epi S.g := hS.epi_g
  exact Projective.factorThru
    (P := P₃.complex.X 0) (X := S.X₃) (E := S.X₂)
    (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) S.g

@[reassoc (attr := simp)]
private theorem horseshoeLiftZero_comp :
    horseshoeLiftZero hS P₃ ≫ S.g = P₃.π.f 0 := by
  let _ : Epi S.g := hS.epi_g
  exact Projective.factorThru_comp
    (P := P₃.complex.X 0) (X := S.X₃) (E := S.X₂)
    (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) S.g

private noncomputable def horseshoeLiftOne : P₃.complex.X 1 ⟶ S.X₁ :=
  hS.exact.liftFromProjective
    (P₃.complex.d 1 0 ≫ horseshoeLiftZero hS P₃) (by
      rw [Category.assoc, horseshoeLiftZero_comp]
      exact P₃.complex_d_comp_π_f_zero)

@[reassoc (attr := simp)]
private theorem horseshoeLiftOne_comp :
    horseshoeLiftOne hS P₃ ≫ S.f =
      P₃.complex.d 1 0 ≫ horseshoeLiftZero hS P₃ :=
  hS.exact.liftFromProjective_comp _ _

private noncomputable def horseshoeCrossZero :
    P₃.complex.X 1 ⟶ P₁.complex.X 0 := by
  let e : P₁.complex.X 0 ⟶ S.X₁ := P₁.π.f 0
  let _ : Epi e := by
    dsimp only [e]
    exact epi_of_isColimit_cofork P₁.isColimitCokernelCofork
  exact Projective.factorThru
    (P := P₃.complex.X 1) (X := S.X₁) (E := P₁.complex.X 0)
    (-horseshoeLiftOne hS P₃) e

@[reassoc (attr := simp)]
private theorem horseshoeCrossZero_comp :
    horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS ≫ P₁.π.f 0 =
      -horseshoeLiftOne hS P₃ :=
  by
    let e : P₁.complex.X 0 ⟶ S.X₁ := P₁.π.f 0
    let _ : Epi e := by
      dsimp only [e]
      exact epi_of_isColimit_cofork P₁.isColimitCokernelCofork
    change Projective.factorThru
        (P := P₃.complex.X 1) (X := S.X₁) (E := P₁.complex.X 0)
        (-horseshoeLiftOne hS P₃) e ≫ e = -horseshoeLiftOne hS P₃
    exact Projective.factorThru_comp
      (P := P₃.complex.X 1) (X := S.X₁) (E := P₁.complex.X 0)
      (-horseshoeLiftOne hS P₃) e

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeCrossOne_cycle :
    ((-P₃.complex.d 2 1) ≫
      horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS) ≫
        P₁.π.f 0 = 0 := by
  change (((-P₃.complex.d 2 1) ≫
      horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS) ≫
        (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) =
      (0 : P₃.complex.X 2 ⟶ S.X₁)
  have hAssoc :
      ((-P₃.complex.d 2 1) ≫
        horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS) ≫
          (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) =
        (-P₃.complex.d 2 1) ≫
          (horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS ≫
            (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) :=
    Category.assoc _ _ _
  have hCross :
      horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS ≫
          (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) =
        -horseshoeLiftOne hS P₃ :=
    horseshoeCrossZero_comp (P₁ := P₁) (P₃ := P₃) hS
  have hCrossPre :
      (-P₃.complex.d 2 1) ≫
          (horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS ≫
            (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) =
        (-P₃.complex.d 2 1) ≫ (-horseshoeLiftOne hS P₃) :=
    congrArg (fun k : P₃.complex.X 1 ⟶ S.X₁ =>
      (-P₃.complex.d 2 1) ≫ k) hCross
  have hDLift :
      P₃.complex.d 2 1 ≫ horseshoeLiftOne hS P₃ = 0 := by
    let _ : Mono S.f := hS.mono_f
    rw [← cancel_mono S.f, Category.assoc, horseshoeLiftOne_comp]
    simp
  calc
    (((-P₃.complex.d 2 1) ≫
        horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS) ≫
          (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) =
      (-P₃.complex.d 2 1) ≫
        (horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS ≫
          (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) := hAssoc
    _ = (-P₃.complex.d 2 1) ≫ (-horseshoeLiftOne hS P₃) := hCrossPre
    _ = P₃.complex.d 2 1 ≫ horseshoeLiftOne hS P₃ := by simp
    _ = 0 := hDLift

private noncomputable def horseshoeCrossOne :
    P₃.complex.X 2 ⟶ P₁.complex.X 1 :=
  P₁.exact₀.liftFromProjective
    ((-P₃.complex.d 2 1) ≫
      horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS)
    (horseshoeCrossOne_cycle (P₁ := P₁) (P₃ := P₃) hS)

@[reassoc (attr := simp)]
private theorem horseshoeCrossOne_comp :
    horseshoeCrossOne (P₁ := P₁) (P₃ := P₃) hS ≫
      P₁.complex.d 1 0 =
      (-P₃.complex.d 2 1) ≫
        horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS :=
  P₁.exact₀.liftFromProjective_comp _ _

private noncomputable def horseshoeCrossAux : ∀ n : ℕ,
    Σ' (f : P₃.complex.X (n + 1) ⟶ P₁.complex.X n)
      (f' : P₃.complex.X (n + 2) ⟶ P₁.complex.X (n + 1)),
      f' ≫ P₁.complex.d (n + 1) n +
        P₃.complex.d (n + 2) (n + 1) ≫ f = 0
  | 0 => ⟨horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS,
      horseshoeCrossOne (P₁ := P₁) (P₃ := P₃) hS, by
        rw [horseshoeCrossOne_comp, Preadditive.neg_comp]
        exact neg_add_cancel
          (P₃.complex.d 2 1 ≫
            horseshoeCrossZero (P₁ := P₁) (P₃ := P₃) hS)⟩
  | n + 1 =>
      let I := horseshoeCrossAux n
      let g := (-P₃.complex.d (n + 3) (n + 2)) ≫ I.2.1
      have hg : g ≫ P₁.complex.d (n + 1) n = 0 := by
        dsimp only [g]
        have hI : I.2.1 ≫ P₁.complex.d (n + 1) n =
            -(P₃.complex.d (n + 2) (n + 1) ≫ I.1) :=
          add_eq_zero_iff_eq_neg.mp I.2.2
        calc
          ((-P₃.complex.d (n + 3) (n + 2)) ≫ I.2.1) ≫
              P₁.complex.d (n + 1) n =
            (-P₃.complex.d (n + 3) (n + 2)) ≫
              (I.2.1 ≫ P₁.complex.d (n + 1) n) := Category.assoc _ _ _
          _ = 0 := by rw [hI]; simp
      let f'' := (P₁.exact_succ n).liftFromProjective g hg
      ⟨I.2.1, f'', by
        dsimp only [f'', g]
        rw [(P₁.exact_succ n).liftFromProjective_comp]
        simpa only [Preadditive.neg_comp] using
          (neg_add_cancel
            (P₃.complex.d (n + 3) (n + 2) ≫ I.2.1))⟩

private noncomputable def horseshoeCross (n : ℕ) :
    P₃.complex.X (n + 1) ⟶ P₁.complex.X n :=
  (horseshoeCrossAux (P₁ := P₁) (P₃ := P₃) hS n).1

private theorem horseshoeCross_succ (n : ℕ) :
    horseshoeCross (P₁ := P₁) (P₃ := P₃) hS (n + 1) =
      (horseshoeCrossAux (P₁ := P₁) (P₃ := P₃) hS n).2.1 := by
  rfl

@[reassoc (attr := simp)]
private theorem horseshoeCross_comp (n : ℕ) :
    horseshoeCross (P₁ := P₁) (P₃ := P₃) hS (n + 1) ≫
        P₁.complex.d (n + 1) n +
      P₃.complex.d (n + 2) (n + 1) ≫
        horseshoeCross (P₁ := P₁) (P₃ := P₃) hS n = 0 := by
  rw [horseshoeCross_succ]
  exact (horseshoeCrossAux (P₁ := P₁) (P₃ := P₃) hS n).2.2

private noncomputable def horseshoeMiddleDifferential (n : ℕ) :
    (P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1)) ⟶
      (P₁.complex.X n ⊞ P₃.complex.X n) :=
  Biprod.ofComponents (P₁.complex.d (n + 1) n) 0
    (horseshoeCross (P₁ := P₁) (P₃ := P₃) hS n)
    (P₃.complex.d (n + 1) n)

private theorem horseshoeMiddleDifferential_sq (n : ℕ) :
    horseshoeMiddleDifferential (P₁ := P₁) (P₃ := P₃) hS (n + 1) ≫
      horseshoeMiddleDifferential (P₁ := P₁) (P₃ := P₃) hS n = 0 := by
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · simp [horseshoeMiddleDifferential]
    · simp [horseshoeMiddleDifferential]
  · apply biprod.hom_ext'
    · simp [horseshoeMiddleDifferential]
    · simp [horseshoeMiddleDifferential]

private noncomputable def horseshoeMiddleComplex : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => P₁.complex.X n ⊞ P₃.complex.X n)
    (horseshoeMiddleDifferential (P₁ := P₁) (P₃ := P₃) hS)
    (horseshoeMiddleDifferential_sq (P₁ := P₁) (P₃ := P₃) hS)

@[simp]
private theorem horseshoeMiddleComplex_d (n : ℕ) :
    (horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS).d (n + 1) n =
      horseshoeMiddleDifferential (P₁ := P₁) (P₃ := P₃) hS n := by
  unfold horseshoeMiddleComplex
  exact ChainComplex.of_d
    (fun m => P₁.complex.X m ⊞ P₃.complex.X m)
    (horseshoeMiddleDifferential (P₁ := P₁) (P₃ := P₃) hS) n

private noncomputable def horseshoeInclusion :
    P₁.complex ⟶
      horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS :=
  ChainComplex.ofHom (fun _ => biprod.inl) (fun n => by
    simp [horseshoeMiddleComplex, horseshoeMiddleDifferential])

private noncomputable def horseshoeProjection :
    horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS ⟶ P₃.complex :=
  ChainComplex.ofHom (fun _ => biprod.snd) (fun n => by
    simp [horseshoeMiddleComplex, horseshoeMiddleDifferential])

private theorem horseshoeInclusion_comp_projection :
    horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS ≫
      horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS = 0 := by
  ext n
  exact biprod.inl_snd

private theorem horseshoeComplexShortExact :
    (ShortComplex.mk
      (horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS)
      (horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS)
      (horseshoeInclusion_comp_projection
        (P₁ := P₁) (P₃ := P₃) hS)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro n
  exact (ShortComplex.Splitting.ofHasBinaryBiproduct
    (P₁.complex.X n) (P₃.complex.X n)).shortExact

private noncomputable def horseshoeMiddleAugmentationZero :
    (P₁.complex.X 0 ⊞ P₃.complex.X 0) ⟶ S.X₂ :=
  biprod.desc
    ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f)
    (horseshoeLiftZero hS P₃)

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeMiddleAugmentationZero_condition :
    (horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS).d 1 0 ≫
      horseshoeMiddleAugmentationZero hS P₁ P₃ = 0 := by
  have h :
      Biprod.ofComponents (P₁.complex.d 1 0) 0
          (horseshoeCross (P₁ := P₁) (P₃ := P₃) hS 0)
          (P₃.complex.d 1 0) ≫
        biprod.desc
          ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f)
          (horseshoeLiftZero hS P₃) =
        (0 : (P₁.complex.X 1 ⊞ P₃.complex.X 1) ⟶ S.X₂) := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, Biprod.inl_ofComponents]
      simp [Category.assoc]
    · rw [← Category.assoc, Biprod.inr_ofComponents]
      simp [horseshoeCross, horseshoeCrossAux, Category.assoc]
  rw [horseshoeMiddleComplex_d]
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeMiddleAugmentationZero_comp_g :
    horseshoeMiddleAugmentationZero hS P₁ P₃ ≫ S.g =
      biprod.snd ≫ (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) := by
  change biprod.desc
      ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f)
      (horseshoeLiftZero hS P₃) ≫ S.g =
    biprod.snd ≫ (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃)
  apply biprod.hom_ext'
  · simp [Category.assoc, S.zero]
  · simp

private noncomputable def horseshoeMiddleπ :
    horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS ⟶
      (ChainComplex.single₀ C).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨horseshoeMiddleAugmentationZero hS P₁ P₃,
      horseshoeMiddleAugmentationZero_condition hS P₁ P₃⟩

@[simp]
private theorem horseshoeMiddleπ_f_zero :
    (horseshoeMiddleπ hS P₁ P₃).f 0 =
      horseshoeMiddleAugmentationZero hS P₁ P₃ := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

@[reassoc]
private theorem horseshoeInclusion_comp_middleπ :
    horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS ≫
        horseshoeMiddleπ hS P₁ P₃ =
      P₁.π ≫ (ChainComplex.single₀ C).map S.f := by
  ext
  simp only [HomologicalComplex.comp_f, horseshoeMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact biprod.inl_desc
    ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f)
    (horseshoeLiftZero hS P₃)

@[reassoc]
private theorem horseshoeProjection_comp_π :
    horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS ≫ P₃.π =
      horseshoeMiddleπ hS P₁ P₃ ≫
        (ChainComplex.single₀ C).map S.g := by
  ext
  simp only [HomologicalComplex.comp_f, horseshoeMiddleπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  change biprod.snd ≫ (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) =
    horseshoeMiddleAugmentationZero hS P₁ P₃ ≫ S.g
  exact (horseshoeMiddleAugmentationZero_comp_g hS P₁ P₃).symm

private noncomputable def horseshoeMiddleAugmented : ChainComplex C ℕ :=
  (horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS).augment
    (horseshoeMiddleAugmentationZero hS P₁ P₃)
    (horseshoeMiddleAugmentationZero_condition hS P₁ P₃)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def horseshoeAugmentedInclusion :
    P₁.augmented ⟶
      horseshoeMiddleAugmented hS P₁ P₃ :=
  ChainComplex.ofHom
    (fun
      | 0 => S.f
      | n + 1 => (horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS).f n)
    (fun n => by
      cases n with
      | zero =>
          change biprod.inl ≫ horseshoeMiddleAugmentationZero hS P₁ P₃ =
            (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f
          exact biprod.inl_desc
            ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f)
            (horseshoeLiftZero hS P₃)
      | succ n =>
          simpa only [Nat.add_one, augmented,
            horseshoeMiddleAugmented, ChainComplex.augment_d_succ_succ] using
            (horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS).comm
              (n + 1) n)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def horseshoeAugmentedProjection :
    horseshoeMiddleAugmented hS P₁ P₃ ⟶
      P₃.augmented :=
  ChainComplex.ofHom
    (fun
      | 0 => S.g
      | n + 1 => (horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS).f n)
    (fun n => by
      cases n with
      | zero =>
          change biprod.snd ≫
              (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) =
            horseshoeMiddleAugmentationZero hS P₁ P₃ ≫ S.g
          exact (horseshoeMiddleAugmentationZero_comp_g hS P₁ P₃).symm
      | succ n =>
          simpa only [Nat.add_one, augmented,
            horseshoeMiddleAugmented, ChainComplex.augment_d_succ_succ] using
            (horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS).comm
              (n + 1) n)

private theorem horseshoeAugmentedInclusion_comp_projection :
    horseshoeAugmentedInclusion hS P₁ P₃ ≫
      horseshoeAugmentedProjection hS P₁ P₃ = 0 := by
  ext (_ | n)
  · exact S.zero
  · exact biprod.inl_snd

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeAugmentedShortExact :
    (ShortComplex.mk
      (horseshoeAugmentedInclusion hS P₁ P₃)
      (horseshoeAugmentedProjection hS P₁ P₃)
      (horseshoeAugmentedInclusion_comp_projection hS P₁ P₃)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro n
  cases n with
  | zero =>
      change S.ShortExact
      exact hS
  | succ n =>
      change (ShortComplex.mk
        (biprod.inl : P₁.complex.X n ⟶
          P₁.complex.X n ⊞ P₃.complex.X n)
        (biprod.snd : P₁.complex.X n ⊞ P₃.complex.X n ⟶
          P₃.complex.X n) biprod.inl_snd).ShortExact
      exact (ShortComplex.Splitting.ofHasBinaryBiproduct
        (P₁.complex.X n) (P₃.complex.X n)).shortExact

private theorem horseshoeMiddleAugmented_acyclic :
    (horseshoeMiddleAugmented hS P₁ P₃).Acyclic :=
  (horseshoeAugmentedShortExact hS P₁ P₃).acyclic_X₂
    P₁.augmented_acyclic P₃.augmented_acyclic

private theorem horseshoeMiddleπ_quasiIso :
    QuasiIso (horseshoeMiddleπ hS P₁ P₃) :=
  ChainComplex.quasiIso_toSingle₀_of_augment_acyclic
    (horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS) S.X₂
    (horseshoeMiddleAugmentationZero hS P₁ P₃)
    (horseshoeMiddleAugmentationZero_condition hS P₁ P₃)
    (horseshoeMiddleAugmented_acyclic hS P₁ P₃)

private noncomputable def horseshoeMiddleResolution :
    ProjectiveResolution S.X₂ where
  complex := horseshoeMiddleComplex (P₁ := P₁) (P₃ := P₃) hS
  projective n := by
    change Projective (P₁.complex.X n ⊞ P₃.complex.X n)
    infer_instance
  π := horseshoeMiddleπ hS P₁ P₃
  quasiIso := horseshoeMiddleπ_quasiIso hS P₁ P₃

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. Horseshoe data consists of a middle projective
resolution `P₂`
of `X₂` and chain maps `P₁ → P₂ → P₃` with zero composite, a short
exact row of resolution complexes, and compatibility with the two
augmentations and the maps of `S`. -/
structure HorseshoeData (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) where
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The middle object of the horseshoe data is a
projective
nonnegative chain resolution `P₂` of `X₂`. -/
  middle : ProjectiveResolution S.X₂
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the left map is a chain inclusion `i : P₁ → P₂` lifting
`S.f : X₁ → X₂`. -/
  i : P₁.complex ⟶ middle.complex
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the right map is a chain projection `p : P₂ → P₃` lifting
`S.g : X₂ → X₃`. -/
  p : middle.complex ⟶ P₃.complex
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the chosen chain maps satisfy `i ≫ p=0`, forming a short
complex of projective resolutions. -/
  zero : i ≫ p = 0
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the row of chain complexes `P₁ → P₂ → P₃` is short exact.
Its degree rows are split because the right terms are projective. -/
  shortExact : (ShortComplex.mk i p zero).ShortExact
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the left map satisfies `i ≫ π₂ = π₁ ≫ S.f[0]`, so it
preserves the augmentation over `X₁ → X₂`. -/
  i_augmentation :
    i ≫ middle.π = P₁.π ≫ (ChainComplex.single₀ C).map S.f
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the right map satisfies `p ≫ π₃ = π₂ ≫ S.g[0]`, so it
preserves the augmentation over `X₂ → X₃`. -/
  p_augmentation :
    p ≫ P₃.π = middle.π ≫ (ChainComplex.single₀ C).map S.g

namespace HorseshoeData

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, an endpoint coordinate specification identifies each
`P₂,n` with `P₁,n ⊞ P₃,n`, identifies `i,p` with the left inclusion
and right projection, and gives the endpoint block differential. -/
structure Spec (H : HorseshoeData hS P₁ P₃) where
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the middle degree-`n` term has a chosen isomorphism
`P₂,n ≅ P₁,n ⊞ P₃,n` in the endpoint coordinate specification. -/
  middleXIso (n : ℕ) : H.middle.complex.X n ≅
    P₁.complex.X n ⊞ P₃.complex.X n
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the endpoint coordinate specification makes the degree-`n`
map `i_n : P₁,n → P₂,n` the left biproduct inclusion. -/
  i_f (n : ℕ) : H.i.f n ≫ (middleXIso n).hom = biprod.inl
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the endpoint coordinate specification makes the degree-`n`
map `p_n : P₂,n → P₃,n` the right biproduct projection. -/
  p_f (n : ℕ) : (middleXIso n).inv ≫ H.p.f n = biprod.snd
  /-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. For horseshoe data `H` with middle resolution
`P₂`, the endpoint coordinate specification gives differential
diagonals `d_P₁,d_P₃`, zero component `P₁,n+1 → P₃,n`, and the
cross component `P₃,n+1 → P₁,n` extracted from the middle differential. -/
  middle_d (n : ℕ) :
    (middleXIso (n + 1)).inv ≫ H.middle.complex.d (n + 1) n ≫
        (middleXIso n).hom =
      Biprod.ofComponents (P₁.complex.d (n + 1) n) 0
        (biprod.inr ≫
          ((middleXIso (n + 1)).inv ≫ H.middle.complex.d (n + 1) n ≫
            (middleXIso n).hom) ≫ biprod.fst)
        (P₃.complex.d (n + 1) n)

end HorseshoeData

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. There exists horseshoe data together with endpoint
biproduct
coordinates identifying its inclusion, projection and differential
with the stated block form in every degree. -/
theorem horseshoe_spec_nonempty :
    Nonempty (Σ H : HorseshoeData hS P₁ P₃, H.Spec) := by
  let H : HorseshoeData hS P₁ P₃ :=
    { middle := horseshoeMiddleResolution hS P₁ P₃
      i := horseshoeInclusion (P₁ := P₁) (P₃ := P₃) hS
      p := horseshoeProjection (P₁ := P₁) (P₃ := P₃) hS
      zero := horseshoeInclusion_comp_projection hS P₁ P₃
      shortExact := horseshoeComplexShortExact hS P₁ P₃
      i_augmentation := horseshoeInclusion_comp_middleπ hS P₁ P₃
      p_augmentation := horseshoeProjection_comp_π hS P₁ P₃ }
  refine ⟨⟨H, ?_⟩⟩
  refine
    { middleXIso := fun _ => Iso.refl _
      i_f := ?_
      p_f := ?_
      middle_d := ?_ }
  · intro n
    simp only [Iso.refl_hom]
    exact Category.comp_id _
  · intro n
    simp only [Iso.refl_inv]
    exact Category.id_comp _
  · intro n
    simp [H, horseshoeMiddleResolution, horseshoeMiddleComplex,
      horseshoeMiddleDifferential]

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The projective horseshoe construction chooses
compatible
middle-resolution data for `S` from the two supplied endpoint
resolutions. -/
noncomputable def horseshoe : HorseshoeData hS P₁ P₃ :=
  (horseshoe_spec_nonempty hS P₁ P₃).some.1

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The constructed horseshoe admits endpoint biproduct
coordinates with left inclusion, right projection, endpoint
differentials on the diagonal, and zero left-to-right differential
component. -/
noncomputable def horseshoe_spec : (horseshoe hS P₁ P₃).Spec :=
  (horseshoe_spec_nonempty hS P₁ P₃).some.2

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The degree-`n` term of the constructed middle
resolution
is canonically isomorphic to `P₁,n ⊞ P₃,n`. -/
noncomputable def horseshoe_middle_X_iso (n : ℕ) :
    (horseshoe hS P₁ P₃).middle.complex.X n ≅
      P₁.complex.X n ⊞ P₃.complex.X n :=
  (horseshoe_spec hS P₁ P₃).middleXIso n

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. Under the endpoint coordinates, the degree-`n`
left chain
map of the constructed horseshoe is the left biproduct inclusion. -/
@[simp]
theorem horseshoe_i_f (n : ℕ) :
    (horseshoe hS P₁ P₃).i.f n ≫
      (horseshoe_middle_X_iso hS P₁ P₃ n).hom = biprod.inl :=
  (horseshoe_spec hS P₁ P₃).i_f n

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. Under the endpoint coordinates, the degree-`n`
right chain
map of the constructed horseshoe is the right biproduct projection. -/
@[simp]
theorem horseshoe_p_f (n : ℕ) :
    (horseshoe_middle_X_iso hS P₁ P₃ n).inv ≫
      (horseshoe hS P₁ P₃).p.f n = biprod.snd :=
  (horseshoe_spec hS P₁ P₃).p_f n

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. In the constructed endpoint coordinates, the middle
differential has diagonals `d_P₁,d_P₃`, zero component from
`P₁,n+1` to `P₃,n`, and its extracted cross component from
`P₃,n+1` to `P₁,n`. -/
theorem horseshoe_middle_d (n : ℕ) :
    (horseshoe_middle_X_iso hS P₁ P₃ (n + 1)).inv ≫
        (horseshoe hS P₁ P₃).middle.complex.d (n + 1) n ≫
        (horseshoe_middle_X_iso hS P₁ P₃ n).hom =
      Biprod.ofComponents (P₁.complex.d (n + 1) n) 0
        (biprod.inr ≫
          ((horseshoe_middle_X_iso hS P₁ P₃ (n + 1)).inv ≫
            (horseshoe hS P₁ P₃).middle.complex.d (n + 1) n ≫
            (horseshoe_middle_X_iso hS P₁ P₃ n).hom) ≫ biprod.fst)
        (P₃.complex.d (n + 1) n) :=
  (horseshoe_spec hS P₁ P₃).middle_d n

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The constructed left chain map followed by the
middle
augmentation equals the left augmentation followed by `S.f[0]`. -/
theorem horseshoe_i_augmentation :
    (horseshoe hS P₁ P₃).i ≫ (horseshoe hS P₁ P₃).middle.π =
      P₁.π ≫ (ChainComplex.single₀ C).map S.f :=
  (horseshoe hS P₁ P₃).i_augmentation

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The constructed right chain map followed by the
right
augmentation equals the middle augmentation followed by `S.g[0]`. -/
theorem horseshoe_p_augmentation :
    (horseshoe hS P₁ P₃).p ≫ P₃.π =
      (horseshoe hS P₁ P₃).middle.π ≫
        (ChainComplex.single₀ C).map S.g :=
  (horseshoe hS P₁ P₃).p_augmentation

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The inclusion and projection of the constructed
resolution
complexes form a short exact sequence `P₁ → P₂ → P₃`. -/
theorem horseshoe_shortExact :
    (ShortComplex.mk
      (horseshoe hS P₁ P₃).i
      (horseshoe hS P₁ P₃).p
      (horseshoe hS P₁ P₃).zero).ShortExact :=
  (horseshoe hS P₁ P₃).shortExact

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. Every degree-`n` object of the constructed middle
resolution
is projective, as it is isomorphic to the biproduct of the two
projective endpoint terms. -/
theorem horseshoe_middle_projective (n : ℕ) :
    Projective ((horseshoe hS P₁ P₃).middle.complex.X n) :=
  inferInstance

/-- Let `C` be abelian, `S : X₁ → X₂ → X₃` short exact, and
`P₁,P₃` projective resolutions of its endpoints. The augmentation of the constructed middle complex
to
`X₂[0]` is a quasi-isomorphism. -/
theorem horseshoe_middle_quasiIso :
    QuasiIso (horseshoe hS P₁ P₃).middle.π :=
  inferInstance

end CategoryTheory.ProjectiveResolution

end

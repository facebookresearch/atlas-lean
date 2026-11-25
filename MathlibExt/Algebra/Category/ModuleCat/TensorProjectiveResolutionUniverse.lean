/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionZeroNormalization

/-!
# Literal tensor augmentations of actual projective resolutions

The tensor product is Mathlib's direct-sum total of the original two
nonnegative resolution complexes. Its augmentation is the tensor of their
actual augmentations. The total differential has sign one in the first
direction and sign `(-1)^p` in the second direction.

The existing bifunctor augmentation comparison and native derived-zero
normalization identify its homology with the original native Tor and identify
degree zero with the literal tensor of the resolved modules. No length or
boundedness hypothesis is imposed on the resolutions or their coefficients.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor ZeroObject

universe u v

namespace ModuleCat.UniverseTensor

variable (R : Type u) [CommRing R]

local notation "c" => ComplexShape.down ℕ

private theorem ι_tensorSinglesIso_hom (M N : ModuleCat.{max u v} R) :
    HomologicalComplex.ιTensorObj ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
        ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N) 0 0 0 rfl ≫
      (Functor.LeftDerivedBalance.singleRightTotalIso (curriedTensor (ModuleCat.{max u v} R))
        ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M) N ≪≫
          (HomologicalComplex.singleMapHomologicalComplex (tensorRight N) c 0).app M).hom.f 0 =
      𝟙 (M ⊗ N) := by
  have hleft :
      ((HomologicalComplex.singleMapHomologicalComplex
        ((curriedTensor (ModuleCat.{max u v} R)).obj M) c 0).app N).hom.f 0 =
      𝟙 (M ⊗ N) := rfl
  have hright :
      ((HomologicalComplex.singleMapHomologicalComplex (tensorRight N) c 0).app M).hom.f 0 =
      𝟙 (M ⊗ N) := rfl
  dsimp only [Iso.trans_hom, HomologicalComplex.comp_f]
  rw [← Category.assoc, Functor.LeftDerivedBalance.ι_singleRightTotalIso_hom]
  change (((HomologicalComplex.singleMapHomologicalComplex
    ((curriedTensor (ModuleCat.{max u v} R)).obj M) c 0).app N).hom.f 0 ≫ 𝟙 (M ⊗ N)) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (tensorRight N) c 0).app M).hom.f 0 = _
  rw [hleft, hright]
  rfl

variable {M N : (ModuleCat.{max u v} R)}

variable {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}

/-- The literal tensor of two actual chain augmentations, with the canonical
comparison of the tensor of their degree-zero singles. -/
def tensorAugmentation
    (π : K ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : L ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N) :
    HomologicalComplex.tensorObj K L ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (M ⊗ N) :=
  HomologicalComplex.tensorHom π ρ ≫
    (Functor.LeftDerivedBalance.singleRightTotalIso (curriedTensor (ModuleCat.{max u v} R))
      ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M) N ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight N) c 0).app M).hom

/-- The degree-zero tensor representative uses both actual chain augmentations. -/
@[reassoc]
theorem ι_tensorAugmentation_zero
    (π : K ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M)
    (ρ : L ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj N) :
    HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫ (tensorAugmentation R π ρ).f 0 =
      π.f 0 ⊗ₘ ρ.f 0 := by
  dsimp only [tensorAugmentation, HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap, Category.assoc,
    Category.assoc, ι_tensorSinglesIso_hom]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- The actual tensor of the two original resolution augmentations, with the
canonical identification of the tensor of degree-zero singles. -/
def tensorResolutionAugmentation (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    HomologicalComplex.tensorObj P.complex Q.complex ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (M ⊗ N) :=
  tensorAugmentation R P.π Q.π

/-- The original degree-zero tensor representative maps by both original
augmentation maps, in their original order. -/
@[reassoc]
theorem ι_tensorResolutionAugmentation_zero
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    HomologicalComplex.ιTensorObj P.complex Q.complex 0 0 0 rfl ≫
      (tensorResolutionAugmentation R P Q).f 0 = P.π.f 0 ⊗ₘ Q.π.f 0 :=
  ι_tensorAugmentation_zero R P.π Q.π

private theorem projectiveTensorRightPreservesHomology (Y : (ModuleCat.{max u v} R)) [Projective Y] :
    (tensorRight Y).PreservesHomology := by
  have : Module.Flat R Y := inferInstance
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact Y hS

/-- Total homology of the actual tensor of two projective resolutions is
the original native Tor of the original resolved modules. -/
def tensorResolutionHomologyIso (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (n : ℕ) :
    (HomologicalComplex.tensorObj P.complex Q.complex).homology n ≅
      (((Tor (ModuleCat.{max u v} R) n).obj M).obj N) := by
  let F := curriedTensor (ModuleCat.{max u v} R)
  have : QuasiIso (Functor.LeftDerivedBalance.leftAugmentation F P Q.complex) :=
    Functor.LeftDerivedBalance.leftAugmentation_quasiIso F
      (fun Y hY => by
        let : Projective Y := hY
        exact projectiveTensorRightPreservesHomology R Y) P Q
  exact isoOfQuasiIsoAt (Functor.LeftDerivedBalance.leftAugmentation F P Q.complex) n ≪≫
    (Q.isoLeftDerivedObj (tensorLeft M) n).symm

/-- The canonical degree-zero comparison for the original tensor total has
the literal tensor product of the original coefficients as its target. -/
def tensorResolutionHomologyZeroIso (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (HomologicalComplex.tensorObj P.complex Q.complex).homology 0 ≅ M ⊗ N :=
  tensorResolutionHomologyIso R P Q 0 ≪≫ nativeTorZeroIso R M N


/-- The canonical native degree-zero comparison carries the original total
quotient class to the tensor of the two original augmentation maps. -/
@[reassoc]
theorem ι_tensorResolutionHomologyZeroIso_hom
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    HomologicalComplex.ιTensorObj P.complex Q.complex 0 0 0 rfl ≫
      ChainComplex.homologyZeroClass (HomologicalComplex.tensorObj P.complex Q.complex) ≫
        (tensorResolutionHomologyZeroIso R P Q).hom = P.π.f 0 ⊗ₘ Q.π.f 0 := by
  let T := HomologicalComplex.tensorObj P.complex Q.complex
  let F := tensorLeft M
  let L := (F.mapHomologicalComplex c).obj Q.complex
  let G := curriedTensor (ModuleCat.{max u v} R)
  let l : T ⟶ L := Functor.LeftDerivedBalance.leftAugmentation G P Q.complex
  let a : P.complex.X 0 ⟶ M := P.π.f 0
  let b : Q.complex.X 0 ⟶ N := Q.π.f 0
  have : PreservesFiniteColimits F := nativeTensorLeft_preservesFiniteColimits R M
  have : QuasiIso l := Functor.LeftDerivedBalance.leftAugmentation_quasiIso G
    (fun Y hY => by
      let : Projective Y := hY
      exact projectiveTensorRightPreservesHomology R Y) P Q
  let e := ChainComplex.homologyZeroIsoOfPreservedAugmentation F Q.π
  let E : (F.leftDerived 0).obj N ≅ L.homology 0 := Q.isoLeftDerivedObj F 0
  let Z : (F.leftDerived 0).obj N ≅ F.obj N := nativeTorZeroIso R M N
  let H : T.homology 0 ⟶ L.homology 0 := HomologicalComplex.homologyMap l 0
  have hnorm : E.inv ≫ Z.hom = e.hom := by
    have he : e.hom = L.homologyι 0 ≫ Q.fromLeftDerivedZero' F :=
      Q.normalizationHomologyZero_hom F
    have hz : Z.hom = E.hom ≫ L.homologyι 0 ≫ Q.fromLeftDerivedZero' F :=
      Q.fromLeftDerivedZero_eq F
    apply (cancel_epi E.hom).1
    exact (E.hom_inv_id_assoc Z.hom).trans
      (hz.trans (congrArg (fun f => E.hom ≫ f) he.symm))
  have hclass : ChainComplex.homologyZeroClass L ≫ e.hom = F.map b :=
    ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom F Q.π
  have hnatural : ChainComplex.homologyZeroClass T ≫ HomologicalComplex.homologyMap l 0 ≫
      e.hom = l.f 0 ≫ F.map b := by
    calc
      _ = (ChainComplex.homologyZeroClass T ≫ HomologicalComplex.homologyMap l 0) ≫ e.hom :=
        (Category.assoc _ _ _).symm
      _ = (l.f 0 ≫ ChainComplex.homologyZeroClass L) ≫ e.hom :=
        congrArg (fun f => f ≫ e.hom) (ChainComplex.homologyZeroClass_naturality l)
      _ = _ := by rw [Category.assoc, hclass]
  change HomologicalComplex.ιTensorObj P.complex Q.complex 0 0 0 rfl ≫
    ChainComplex.homologyZeroClass T ≫ H ≫ E.inv ≫ Z.hom = _
  have hnatural' : ChainComplex.homologyZeroClass T ≫ H ≫ e.hom = l.f 0 ≫ F.map b := hnatural
  rw [hnorm, hnatural']
  rw [← Category.assoc, Functor.LeftDerivedBalance.ι_leftAugmentation]
  change (a ▷ Q.complex.X 0) ≫ (M ◁ b) = a ⊗ₘ b
  exact (tensorHom_def a b).symm

/-- The canonical H0 quotient followed by the native tensor comparison is
exactly the degree-zero component of the literal tensor augmentation. -/
theorem tensorResolutionAugmentation_f_zero
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (tensorResolutionAugmentation R P Q).f 0 =
      ChainComplex.homologyZeroClass (HomologicalComplex.tensorObj P.complex Q.complex) ≫
        (tensorResolutionHomologyZeroIso R P Q).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hp : p = 0 := by change p + q = 0 at hpq; omega
  have hq : q = 0 := by change p + q = 0 at hpq; omega
  subst p
  subst q
  exact (ι_tensorResolutionAugmentation_zero R P Q).trans
    (ι_tensorResolutionHomologyZeroIso_hom R P Q).symm


private theorem homologyZeroClass_single_hom (X : ModuleCat.{max u v} R) :
    ChainComplex.homologyZeroClass ((ChainComplex.single₀ (ModuleCat.{max u v} R)).obj X) ≫
      (HomologicalComplex.singleObjHomologySelfIso c 0 X).hom = 𝟙 X := by
  let L := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj X
  let E : L.homology 0 ≅ X := HomologicalComplex.singleObjHomologySelfIso c 0 X
  let O : X ≅ L.opcycles 0 := HomologicalComplex.singleObjOpcyclesSelfIso c 0 X
  let I : L.homology 0 ≅ L.opcycles 0 := L.isoHomologyι₀
  have hE : I.hom ≫ O.inv = E.hom :=
    HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv c 0 X
  have hp : L.pOpcycles 0 ≫ O.inv = 𝟙 X :=
    HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv c 0 X
  change L.pOpcycles 0 ≫ I.inv ≫ E.hom = 𝟙 X
  rw [← hE, Iso.inv_hom_id_assoc]
  exact hp

/-- The actual homology map of the tensor augmentation is the canonical
native H0 tensor comparison, with the target's standard single homology iso. -/
@[reassoc]
theorem tensorResolutionAugmentation_homology_zero
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    HomologicalComplex.homologyMap (tensorResolutionAugmentation R P Q) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso c 0 (M ⊗ N)).hom =
        (tensorResolutionHomologyZeroIso R P Q).hom := by
  let T := HomologicalComplex.tensorObj P.complex Q.complex
  let S := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (M ⊗ N)
  let π : T ⟶ S := tensorResolutionAugmentation R P Q
  let H : T.homology 0 ⟶ S.homology 0 := HomologicalComplex.homologyMap π 0
  let κ : T.X 0 ⟶ T.homology 0 := ChainComplex.homologyZeroClass T
  let κS : M ⊗ N ⟶ S.homology 0 := ChainComplex.homologyZeroClass S
  let δ : T.X 0 ⟶ M ⊗ N := π.f 0
  let E : S.homology 0 ≅ M ⊗ N := HomologicalComplex.singleObjHomologySelfIso c 0 (M ⊗ N)
  let e : T.homology 0 ≅ M ⊗ N := tensorResolutionHomologyZeroIso R P Q
  have : Epi κ := by dsimp [κ, ChainComplex.homologyZeroClass]; infer_instance
  have hκ : κ ≫ H = δ ≫ κS := ChainComplex.homologyZeroClass_naturality π
  have hS : κS ≫ E.hom = 𝟙 (M ⊗ N) := homologyZeroClass_single_hom R (M ⊗ N)
  have hδ : δ = κ ≫ e.hom := tensorResolutionAugmentation_f_zero R P Q
  change H ≫ E.hom = e.hom
  apply (cancel_epi κ).1
  calc
    _ = (κ ≫ H) ≫ E.hom := (Category.assoc _ _ _).symm
    _ = (δ ≫ κS) ≫ E.hom := congrArg (fun f => f ≫ E.hom) hκ
    _ = δ ≫ (κS ≫ E.hom) := Category.assoc _ _ _
    _ = δ ≫ 𝟙 (M ⊗ N) := congrArg (fun f => δ ≫ f) hS
    _ = δ := Category.comp_id _
    _ = _ := hδ

/-- The literal tensor augmentation is a quasi-isomorphism precisely when
all positive original native Tor modules vanish. -/
theorem tensorResolutionAugmentation_quasiIso_iff
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (tensorResolutionAugmentation R P Q) ↔
      ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N) := by
  let T := HomologicalComplex.tensorObj P.complex Q.complex
  let S := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (M ⊗ N)
  let π : T ⟶ S := tensorResolutionAugmentation R P Q
  constructor
  · intro hπ n
    have : QuasiIso π := hπ
    have hz : IsZero (S.homology (n + 1)) :=
      (ChainComplex.exactAt_succ_single_obj (M ⊗ N) n).isZero_homology
    have hT : IsZero (T.homology (n + 1)) := hz.of_iso (isoOfQuasiIsoAt π (n + 1))
    exact hT.of_iso (tensorResolutionHomologyIso R P Q (n + 1)).symm
  · intro hTor
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    cases n with
    | zero =>
      let E : S.homology 0 ≅ M ⊗ N :=
        HomologicalComplex.singleObjHomologySelfIso c 0 (M ⊗ N)
      let H : T.homology 0 ⟶ S.homology 0 := HomologicalComplex.homologyMap π 0
      have hH : H ≫ E.hom = (tensorResolutionHomologyZeroIso R P Q).hom :=
        tensorResolutionAugmentation_homology_zero R P Q
      have hE : H = (tensorResolutionHomologyZeroIso R P Q).hom ≫ E.inv := by
        apply (cancel_mono E.hom).1
        rw [hH]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change IsIso H
      rw [hE]
      infer_instance
    | succ n =>
      have hT : IsZero (T.homology (n + 1)) :=
        (hTor n).of_iso (tensorResolutionHomologyIso R P Q (n + 1))
      exact hT.isIso
        ((ChainComplex.exactAt_succ_single_obj (M ⊗ N) n).isZero_homology)
        (HomologicalComplex.homologyMap π (n + 1))

/-- Every original tensor-total term is projective, without finite generation
or boundedness assumptions on either actual resolution. -/
theorem tensorResolutionTotal_projective
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    Projective ((HomologicalComplex.tensorObj P.complex Q.complex).X n) := by
  let B := (((curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex c c).obj
    P.complex).obj Q.complex
  let π := ComplexShape.π c c c
  let A := B.toGradedObject.mapObjFun π n
  have hterm (p q : ℕ) : Projective ((B.X p).X q) := by
    let X : ModuleCat.{max u v} R := P.complex.X p
    let Y : ModuleCat.{max u v} R := Q.complex.X q
    have : Projective X := P.projective p
    have : Projective Y := Q.projective q
    have : Module.Projective R X := inferInstance
    have : Module.Projective R Y := inferInstance
    have : Module.Projective R (TensorProduct R X Y) := inferInstance
    change Projective (ModuleCat.of R (TensorProduct R X Y))
    infer_instance
  have : ∀ i, Projective (A i) := fun i => hterm i.val.1 i.val.2
  let I := π ⁻¹' {n}
  let ε : ULift.{max u v} I ≃ I := Equiv.ulift
  let A' : ULift.{max u v} I → ModuleCat.{max u v} R := A ∘ ε
  have : ∀ i, Projective (A' i) := fun i => hterm (ε i).val.1 (ε i).val.2
  have hA : Projective (∐ A') := Projective.instSigmaObj A'
  change Projective (∐ A)
  exact Projective.of_iso (Sigma.reindex ε A) hA

/-- Under actual positive Tor vanishing, the original tensor total with the
literal tensor augmentation is a genuine projective resolution. -/
def tensorProjectiveResolution (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hTor : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N)) :
    ProjectiveResolution (M ⊗ N) where
  complex := HomologicalComplex.tensorObj P.complex Q.complex
  π := tensorResolutionAugmentation R P Q
  projective := tensorResolutionTotal_projective R P Q
  quasiIso := (tensorResolutionAugmentation_quasiIso_iff R P Q).mpr hTor

/-- The constructed resolution retains the literal original tensor total. -/
@[simp]
theorem tensorProjectiveResolution_complex
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hTor : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N)) :
    (tensorProjectiveResolution R P Q hTor).complex =
      HomologicalComplex.tensorObj P.complex Q.complex := rfl

/-- The constructed resolution retains the tensor of both actual augmentations. -/
@[simp]
theorem tensorProjectiveResolution_π
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hTor : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N)) :
    (tensorProjectiveResolution R P Q hTor).π = tensorResolutionAugmentation R P Q := rfl


/-- The canonical H0 projection followed by the native tensor comparison is
exactly the literal augmentation as a chain map. -/
theorem tensorResolutionAugmentation_eq_projection
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    tensorResolutionAugmentation R P Q =
      (ChainComplex.toSingle₀Equiv
        (HomologicalComplex.tensorObj P.complex Q.complex)
        ((HomologicalComplex.tensorObj P.complex Q.complex).homology 0)).symm
          ⟨ChainComplex.homologyZeroClass (HomologicalComplex.tensorObj P.complex Q.complex),
            ChainComplex.d_comp_homologyZeroClass _⟩ ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
          (tensorResolutionHomologyZeroIso R P Q).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    let T := HomologicalComplex.tensorObj P.complex Q.complex
    let κ : T.X 0 ⟶ T.homology 0 := ChainComplex.homologyZeroClass T
    let π : T ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (T.homology 0) :=
      (ChainComplex.toSingle₀Equiv T (T.homology 0)).symm
        ⟨κ, ChainComplex.d_comp_homologyZeroClass T⟩
    let e : T.homology 0 ≅ M ⊗ N := tensorResolutionHomologyZeroIso R P Q
    let a := (ChainComplex.single₀ (ModuleCat.{max u v} R)).map e.hom
    have hπ : π.f 0 = κ := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
    have ha : a.f 0 = e.hom := ChainComplex.single₀_map_f_zero e.hom
    have hcomp : (π ≫ a).f 0 = κ ≫ e.hom :=
      (HomologicalComplex.comp_f π a 0).trans (congrArg₂ (fun f g => f ≫ g) hπ ha)
    exact (tensorResolutionAugmentation_f_zero R P Q).trans hcomp.symm
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X c 0 (M ⊗ N) (n + 1) (by omega)).eq_of_tgt _ _

variable {M' N' : ModuleCat.{max u v} R}

/-- Simultaneous actual resolution maps commute with the literal tensor
augmentation and the tensor of their actual coefficient maps. -/
@[reassoc]
theorem tensorResolutionAugmentation_naturality
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
    (a : M ⟶ M') (b : N ⟶ N') (f : ProjectiveResolution.Hom P P' a)
    (g : ProjectiveResolution.Hom Q Q' b) :
    HomologicalComplex.tensorHom f.hom g.hom ≫ tensorResolutionAugmentation R P' Q' =
      tensorResolutionAugmentation R P Q ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map (a ⊗ₘ b) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    let T := HomologicalComplex.tensorObj P.complex Q.complex
    let T' := HomologicalComplex.tensorObj P'.complex Q'.complex
    let α : T.X 0 ⟶ T'.X 0 := (HomologicalComplex.tensorHom f.hom g.hom).f 0
    let ι : P.complex.X 0 ⊗ Q.complex.X 0 ⟶ T.X 0 :=
      HomologicalComplex.ιTensorObj P.complex Q.complex 0 0 0 rfl
    let ι' : P'.complex.X 0 ⊗ Q'.complex.X 0 ⟶ T'.X 0 :=
      HomologicalComplex.ιTensorObj P'.complex Q'.complex 0 0 0 rfl
    let δ : T.X 0 ⟶ M ⊗ N := (tensorResolutionAugmentation R P Q).f 0
    let δ' : T'.X 0 ⟶ M' ⊗ N' := (tensorResolutionAugmentation R P' Q').f 0
    let f₀ : P.complex.X 0 ⟶ P'.complex.X 0 := f.hom.f 0
    let g₀ : Q.complex.X 0 ⟶ Q'.complex.X 0 := g.hom.f 0
    let p₀ : P.complex.X 0 ⟶ M := P.π.f 0
    let q₀ : Q.complex.X 0 ⟶ N := Q.π.f 0
    let p₀' : P'.complex.X 0 ⟶ M' := P'.π.f 0
    let q₀' : Q'.complex.X 0 ⟶ N' := Q'.π.f 0
    let θ : P.complex.X 0 ⊗ Q.complex.X 0 ⟶ P'.complex.X 0 ⊗ Q'.complex.X 0 := f₀ ⊗ₘ g₀
    have hp : ι ≫ δ = p₀ ⊗ₘ q₀ := ι_tensorResolutionAugmentation_zero R P Q
    have hp' : ι' ≫ δ' = p₀' ⊗ₘ q₀' := ι_tensorResolutionAugmentation_zero R P' Q'
    have hf : f₀ ≫ p₀' = p₀ ≫ a := f.hom_f_zero_comp_π_f_zero
    have hg : g₀ ≫ q₀' = q₀ ≫ b := g.hom_f_zero_comp_π_f_zero
    have hθ : θ ≫ (p₀' ⊗ₘ q₀') = (p₀ ⊗ₘ q₀) ≫ (a ⊗ₘ b) := by
      dsimp only [θ]
      rw [tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom]
    have hmap : ι ≫ α = θ ≫ ι' := by
      have h := HomologicalComplex.ι_mapBifunctorMap
        (f₁ := f.hom) (f₂ := g.hom) (F := curriedTensor (ModuleCat.{max u v} R))
        («c» := c) 0 0 0 rfl
      change ι ≫ α = _ at h
      exact h.trans (congrArg (fun k => k ≫ ι') (tensorHom_def f₀ g₀).symm)
    change α ≫ δ' = δ ≫ (a ⊗ₘ b)
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hp0 : p = 0 := by change p + q = 0 at hpq; omega
    have hq0 : q = 0 := by change p + q = 0 at hpq; omega
    subst p
    subst q
    change ι ≫ (α ≫ δ') = ι ≫ (δ ≫ (a ⊗ₘ b))
    calc
      _ = (ι ≫ α) ≫ δ' := (Category.assoc _ _ _).symm
      _ = (θ ≫ ι') ≫ δ' := congrArg (fun k => k ≫ δ') hmap
      _ = θ ≫ (ι' ≫ δ') := Category.assoc _ _ _
      _ = θ ≫ (p₀' ⊗ₘ q₀') := congrArg (fun k => θ ≫ k) hp'
      _ = (p₀ ⊗ₘ q₀) ≫ (a ⊗ₘ b) := hθ
      _ = (ι ≫ δ) ≫ (a ⊗ₘ b) := congrArg (fun k => k ≫ (a ⊗ₘ b)) hp.symm
      _ = _ := Category.assoc _ _ _
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X c 0 (M' ⊗ N') (n + 1) (by omega)).eq_of_tgt _ _

/-- The canonical degree-zero tensor comparison is natural under the same
actual simultaneous resolution and coefficient maps. -/
@[reassoc]
theorem tensorResolutionHomologyZeroIso_naturality
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
    (a : M ⟶ M') (b : N ⟶ N') (f : ProjectiveResolution.Hom P P' a)
    (g : ProjectiveResolution.Hom Q Q' b) :
    HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f.hom g.hom) 0 ≫
      (tensorResolutionHomologyZeroIso R P' Q').hom =
        (tensorResolutionHomologyZeroIso R P Q).hom ≫ (a ⊗ₘ b) := by
  let T := HomologicalComplex.tensorObj P.complex Q.complex
  let T' := HomologicalComplex.tensorObj P'.complex Q'.complex
  let α : T ⟶ T' := HomologicalComplex.tensorHom f.hom g.hom
  let H : T.homology 0 ⟶ T'.homology 0 := HomologicalComplex.homologyMap α 0
  let κ : T.X 0 ⟶ T.homology 0 := ChainComplex.homologyZeroClass T
  let κ' : T'.X 0 ⟶ T'.homology 0 := ChainComplex.homologyZeroClass T'
  let e : T.homology 0 ≅ M ⊗ N := tensorResolutionHomologyZeroIso R P Q
  let e' : T'.homology 0 ≅ M' ⊗ N' := tensorResolutionHomologyZeroIso R P' Q'
  let δ : T.X 0 ⟶ M ⊗ N := (tensorResolutionAugmentation R P Q).f 0
  let δ' : T'.X 0 ⟶ M' ⊗ N' := (tensorResolutionAugmentation R P' Q').f 0
  let α₀ : T.X 0 ⟶ T'.X 0 := α.f 0
  have : Epi κ := by dsimp [κ, ChainComplex.homologyZeroClass]; infer_instance
  have hκ : κ ≫ H = α₀ ≫ κ' := ChainComplex.homologyZeroClass_naturality α
  have hδ : δ = κ ≫ e.hom := tensorResolutionAugmentation_f_zero R P Q
  have hδ' : δ' = κ' ≫ e'.hom := tensorResolutionAugmentation_f_zero R P' Q'
  have hα : α₀ ≫ δ' = δ ≫ (a ⊗ₘ b) := by
    have h := congrArg (fun k => k.f 0)
      (tensorResolutionAugmentation_naturality R P Q P' Q' a b f g)
    exact h
  change H ≫ e'.hom = e.hom ≫ (a ⊗ₘ b)
  apply (cancel_epi κ).1
  calc
    _ = (κ ≫ H) ≫ e'.hom := (Category.assoc _ _ _).symm
    _ = (α₀ ≫ κ') ≫ e'.hom := congrArg (fun k => k ≫ e'.hom) hκ
    _ = α₀ ≫ δ' := by rw [Category.assoc, ← hδ']
    _ = δ ≫ (a ⊗ₘ b) := hα
    _ = _ := by rw [hδ, Category.assoc]

/-- The actual simultaneous tensor map is a map of the constructed genuine
projective resolutions, with the original tensor coefficient map. -/
def tensorProjectiveResolutionHom
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
    (hTor : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N))
    (hTor' : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M').obj N'))
    (a : M ⟶ M') (b : N ⟶ N') (f : ProjectiveResolution.Hom P P' a)
    (g : ProjectiveResolution.Hom Q Q' b) :
    ProjectiveResolution.Hom (tensorProjectiveResolution R P Q hTor)
      (tensorProjectiveResolution R P' Q' hTor') (a ⊗ₘ b) where
  hom := HomologicalComplex.tensorHom f.hom g.hom
  hom_f_zero_comp_π_f_zero := by
    have h := congrArg (fun k => k.f 0)
      (tensorResolutionAugmentation_naturality R P Q P' Q' a b f g)
    exact h

end ModuleCat.UniverseTensor

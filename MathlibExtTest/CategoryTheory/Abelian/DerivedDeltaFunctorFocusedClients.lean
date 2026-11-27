/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.DimensionShift
import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism
import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroClass
import MathlibExt.CategoryTheory.Abelian.RightDerived.Additive
import MathlibExt.CategoryTheory.Abelian.RightDerived.NatIso
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Focused clients for derived functors and δ-functors

Chain homology and cochain homology are genuine homological and cohomological
δ-functors: every field of the structures is discharged from the homology
long exact sequence. On the non-split sequence `X → (X = X) → X[1]` of chain
complexes the connecting map is a dimension-shift isomorphism and is nonzero.

Left and right derived functors of the identity of `ℤ`-modules are additive,
derive natural isomorphisms and sums of transformations, and in degree zero
detect the nonzero map `𝟙 + 𝟙` on `ℤ`.
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Abelian

section HomologyDeltaFunctors

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Chain homology, with the snake-lemma boundary, is a homological δ-functor. -/
noncomputable def chainHomologyDeltaFunctor :
    HomologicalDeltaFunctor (ChainComplex C ℕ) C where
  T n := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n
  additive _ := inferInstance
  connecting n :=
    { app S := ShortComplex.ShortExact.δ S.property (n + 1) n rfl
      naturality S S' φ := (HomologicalComplex.HomologySequence.δ_naturality φ.hom
        S.property S'.property (n + 1) n rfl).symm }
  exactLeft n S := ⟨_, ShortComplex.ShortExact.homology_exact₁ S.property (n + 1) n rfl⟩
  exactMiddle n S := ⟨_, ShortComplex.ShortExact.homology_exact₂ S.property n⟩
  exactRight n S := ⟨_, ShortComplex.ShortExact.homology_exact₃ S.property (n + 1) n rfl⟩
  epiZero S := by
    have : Epi S.obj.g := (S.property : S.obj.ShortExact).epi_g
    exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.obj.g 0 (by simp)

/-- Cochain homology, with the snake-lemma boundary, is a cohomological δ-functor. -/
noncomputable def cochainHomologyDeltaFunctor :
    CohomologicalDeltaFunctor (CochainComplex C ℕ) C where
  T n := HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n
  additive _ := inferInstance
  connecting n :=
    { app S := ShortComplex.ShortExact.δ S.property n (n + 1) rfl
      naturality S S' φ := (HomologicalComplex.HomologySequence.δ_naturality φ.hom
        S.property S'.property n (n + 1) rfl).symm }
  exactLeft n S := ⟨_, ShortComplex.ShortExact.homology_exact₁ S.property n (n + 1) rfl⟩
  exactMiddle n S := ⟨_, ShortComplex.ShortExact.homology_exact₂ S.property n⟩
  exactRight n S := ⟨_, ShortComplex.ShortExact.homology_exact₃ S.property n (n + 1) rfl⟩
  monoZero S := by
    have : Mono S.obj.f := (S.property : S.obj.ShortExact).mono_f
    exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.obj.f 0 (by simp)

/-- An acyclic middle complex makes the chain-homology boundary an isomorphism. -/
example (n : ℕ) (S : ShortComplex.ShortExactSequences (ChainComplex C ℕ))
    (hn : S.obj.X₂.ExactAt n) (hs : S.obj.X₂.ExactAt (n + 1)) :
    IsIso (ShortComplex.ShortExact.δ S.property (n + 1) n rfl) :=
  (chainHomologyDeltaFunctor C).isIso_connecting_of_isZero_middle n S
    (hn.isZero_homology) (hs.isZero_homology)

/-- An acyclic middle complex makes the cochain-homology boundary an isomorphism,
and the dimension-shift isomorphism has that boundary as its forward map. -/
example (n : ℕ) (S : ShortComplex.ShortExactSequences (CochainComplex C ℕ))
    (hn : S.obj.X₂.ExactAt n) (hs : S.obj.X₂.ExactAt (n + 1)) :
    ((cochainHomologyDeltaFunctor C).connectingIsoOfIsZeroMiddle n S
      hn.isZero_homology hs.isZero_homology).hom =
      ShortComplex.ShortExact.δ S.property n (n + 1) rfl :=
  (cochainHomologyDeltaFunctor C).connectingIsoOfIsZeroMiddle_hom n S _ _

/-- A vanishing higher middle value makes the boundary a kernel of the next map. -/
example (n : ℕ) (S : ShortComplex.ShortExactSequences (ChainComplex C ℕ))
    (hs : S.obj.X₂.ExactAt (n + 1)) :
    Mono (ShortComplex.ShortExact.δ S.property (n + 1) n rfl) :=
  (chainHomologyDeltaFunctor C).mono_connecting_of_isZero_middle_succ n S hs.isZero_homology

end HomologyDeltaFunctors

section DiskSequence

variable {C : Type u} [Category.{v} C] [Abelian C] (X : C)

/-- `X` placed in degree zero. -/
noncomputable def pt₀ : ℕ → C
  | 0 => X
  | _ + 1 => 0

/-- `X` placed in degrees one and zero. -/
noncomputable def disk : ℕ → C
  | 0 => X
  | 1 => X
  | _ + 2 => 0

/-- `X` placed in degree one. -/
noncomputable def pt₁ : ℕ → C
  | 0 => 0
  | 1 => X
  | _ + 2 => 0

/-- The differential of the disk: the identity of `X` from degree one to degree zero. -/
noncomputable def diskD : (n : ℕ) → disk X (n + 1) ⟶ disk X n
  | 0 => 𝟙 X
  | _ + 1 => 0

/-- The degreewise inclusion of `X` in degree zero. -/
noncomputable def diskιf : (n : ℕ) → pt₀ X n ⟶ disk X n
  | 0 => 𝟙 X
  | _ + 1 => 0

/-- The degreewise projection onto `X` in degree one. -/
noncomputable def diskπf : (n : ℕ) → disk X n ⟶ pt₁ X n
  | 0 => 0
  | 1 => 𝟙 X
  | _ + 2 => 0

/-- The complex `X` concentrated in degree zero. -/
noncomputable def pt₀Complex : ChainComplex C ℕ :=
  ChainComplex.of (pt₀ X) (fun _ => 0) (fun _ => zero_comp)

/-- The acyclic complex `X = X` in degrees one and zero. -/
noncomputable def diskComplex : ChainComplex C ℕ :=
  ChainComplex.of (disk X) (diskD X) (fun _ => zero_comp)

/-- The complex `X` concentrated in degree one. -/
noncomputable def pt₁Complex : ChainComplex C ℕ :=
  ChainComplex.of (pt₁ X) (fun _ => 0) (fun _ => zero_comp)

/-- The inclusion of the degree-zero copy of `X`. -/
noncomputable def diskι : pt₀Complex X ⟶ diskComplex X :=
  ChainComplex.ofHom (diskιf X) (fun _ => (isZero_zero C).eq_of_src _ _)

/-- The projection onto the degree-one copy of `X`. -/
noncomputable def diskπ : diskComplex X ⟶ pt₁Complex X :=
  ChainComplex.ofHom (diskπf X) (fun n => match n with
    | 0 => (isZero_zero C).eq_of_tgt _ _
    | _ + 1 => (isZero_zero C).eq_of_src _ _)

/-- The short complex `X[0] → (X = X) → X[1]`. -/
noncomputable def diskSequence : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (diskι X) (diskπ X) (by
    ext n
    match n with
    | 0 => exact (isZero_zero C).eq_of_tgt _ _
    | _ + 1 => exact (isZero_zero C).eq_of_src _ _)

lemma diskSequence_shortExact : (diskSequence X).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  match n with
  | 0 =>
    refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (𝟙 X)))
      ((isZero_zero C).epi _)
    exact (ShortComplex.exact_iff_epi _ ((isZero_zero C).eq_of_tgt _ _)).2
      (inferInstanceAs (Epi (𝟙 X)))
  | 1 =>
    refine ShortComplex.ShortExact.mk' ?_ ((isZero_zero C).mono _)
      (inferInstanceAs (Epi (𝟙 X)))
    exact (ShortComplex.exact_iff_mono _ ((isZero_zero C).eq_of_src _ _)).2
      (inferInstanceAs (Mono (𝟙 X)))
  | _ + 2 =>
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C))
      ((isZero_zero C).mono _) ((isZero_zero C).epi _)

/-- The disk sequence as an object of the category of short exact sequences. -/
noncomputable def diskSES : ShortComplex.ShortExactSequences (ChainComplex C ℕ) :=
  ⟨diskSequence X, diskSequence_shortExact X⟩

lemma diskComplex_d_one_zero : (diskComplex X).d 1 0 = diskD X 0 :=
  ChainComplex.of_d (disk X) (diskD X) 0

lemma diskComplex_exactAt_zero : (diskComplex X).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
  refine (ShortComplex.exact_iff_epi _ ((diskComplex X).shape 0 0 (by simp))).2 ?_
  change Epi ((diskComplex X).d 1 0)
  rw [diskComplex_d_one_zero]
  exact inferInstanceAs (Epi (𝟙 X))

lemma diskComplex_exactAt_one : (diskComplex X).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  refine (ShortComplex.exact_iff_mono _ (ChainComplex.of_d (disk X) (diskD X) 1)).2 ?_
  change Mono ((diskComplex X).d 1 0)
  rw [diskComplex_d_one_zero]
  exact inferInstanceAs (Mono (𝟙 X))

/-- Degree-zero homology of `X[0]` is `X`. -/
noncomputable def pt₀HomologyIso : (pt₀Complex X).homology 0 ≅ X :=
  ((pt₀Complex X).isoHomologyπ 1 0 (by simp) (ChainComplex.of_d (pt₀ X) (fun _ => 0) 0)).symm ≪≫
    (pt₀Complex X).iCyclesIso 0 0 (by simp) ((pt₀Complex X).shape 0 0 (by simp))

/-- The boundary `H₁(X[1]) → H₀(X[0])` is a dimension-shift isomorphism. -/
lemma isIso_disk_connecting :
    IsIso (((chainHomologyDeltaFunctor C).connecting 0).app (diskSES X)) :=
  (chainHomologyDeltaFunctor C).isIso_connecting_of_isZero_middle 0 (diskSES X)
    (diskComplex_exactAt_zero X).isZero_homology (diskComplex_exactAt_one X).isZero_homology

/-- The connecting map of the disk sequence is nonzero whenever `X` is nonzero. -/
lemma disk_connecting_ne_zero (hX : ¬ IsZero X) :
    ((chainHomologyDeltaFunctor C).connecting 0).app (diskSES X) ≠ 0 := by
  intro h
  have := isIso_disk_connecting X
  apply hX
  refine IsZero.of_iso ?_ (pt₀HomologyIso X).symm
  rw [IsZero.iff_id_eq_zero]
  let δ := ((chainHomologyDeltaFunctor C).connecting 0).app (diskSES X)
  calc 𝟙 _ = inv δ ≫ δ := (IsIso.inv_hom_id δ).symm
    _ = inv δ ≫ 0 := congrArg (inv δ ≫ ·) h
    _ = 0 := comp_zero

/-- The disk sequence does not split when `X` is nonzero: a retraction of the
inclusion would factor the identity of `H₀(X[0]) ≅ X` through `H₀(X = X) = 0`. -/
lemma diskSequence_not_split (hX : ¬ IsZero X) : IsEmpty (diskSequence X).Splitting := by
  refine ⟨fun s => hX ?_⟩
  refine IsZero.of_iso ?_ (pt₀HomologyIso X).symm
  change IsZero ((diskSequence X).X₁.homology 0)
  rw [IsZero.iff_id_eq_zero]
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ 0) s.f_r
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h
  rw [← h, show HomologicalComplex.homologyMap (diskSequence X).f 0 = 0 from
    (diskComplex_exactAt_zero X).isZero_homology.eq_of_tgt _ _, zero_comp]

end DiskSequence

section Derived

/-- The integers as a `ℤ`-module. -/
abbrev Zmod : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

lemma id_add_id_ne_zero_of_iso {Y : ModuleCat.{0} ℤ} (e : Y ≅ Zmod) : 𝟙 Y + 𝟙 Y ≠ 0 := by
  intro h
  have h' : e.inv ≫ (𝟙 Y + 𝟙 Y) ≫ e.hom = 𝟙 Zmod + 𝟙 Zmod := by
    simp [Preadditive.add_comp, Preadditive.comp_add]
  rw [h, zero_comp, comp_zero] at h'
  have h1 := congrArg (fun φ : Zmod ⟶ Zmod => φ.hom (1 : ℤ)) h'
  simp at h1

/-- Degree-zero left derived identity on `ℤ` is isomorphic to `ℤ`. -/
noncomputable def leftZero : ((𝟭 (ModuleCat.{0} ℤ)).leftDerived 0).obj Zmod ≅ Zmod :=
  (Functor.leftDerivedZeroIsoSelf (𝟭 _)).app Zmod

/-- Degree-zero right derived identity on `ℤ` is isomorphic to `ℤ`. -/
noncomputable def rightZero : ((𝟭 (ModuleCat.{0} ℤ)).rightDerived 0).obj Zmod ≅ Zmod :=
  (Functor.rightDerivedZeroIsoSelf (𝟭 _)).app Zmod

/-- Additivity of `L₀ 𝟭` on `ℤ`: the derived map of `𝟙 + 𝟙` is `𝟙 + 𝟙`, which is nonzero. -/
example : ((𝟭 (ModuleCat.{0} ℤ)).leftDerived 0).map (𝟙 Zmod + 𝟙 Zmod) ≠ 0 := by
  rw [Functor.map_add, CategoryTheory.Functor.map_id]
  exact id_add_id_ne_zero_of_iso leftZero

/-- Additivity of `R₀ 𝟭` on `ℤ`: the derived map of `𝟙 + 𝟙` is `𝟙 + 𝟙`, which is nonzero. -/
example : ((𝟭 (ModuleCat.{0} ℤ)).rightDerived 0).map (𝟙 Zmod + 𝟙 Zmod) ≠ 0 := by
  rw [Functor.map_add, CategoryTheory.Functor.map_id]
  exact id_add_id_ne_zero_of_iso rightZero

/-- Additivity also holds in positive degree and for negation. -/
example (n : ℕ) {X Y : ModuleCat.{0} ℤ} (f g : X ⟶ Y) :
    ((𝟭 (ModuleCat.{0} ℤ)).leftDerived (n + 1)).map (f - g) =
      ((𝟭 _).leftDerived (n + 1)).map f - ((𝟭 _).leftDerived (n + 1)).map g :=
  Functor.map_sub _

/-- The derived transformation of `𝟙 + 𝟙` is nonzero at `ℤ` in degree zero. -/
example : (NatTrans.leftDerived (𝟙 (𝟭 (ModuleCat.{0} ℤ)) + 𝟙 (𝟭 _)) 0).app Zmod ≠ 0 := by
  rw [NatTrans.leftDerived_add, NatTrans.leftDerived_id, NatTrans.app_add, NatTrans.id_app]
  exact id_add_id_ne_zero_of_iso leftZero

/-- Derivation is additive on the category of additive functors. -/
example (n : ℕ) {F G : ModuleCat.{0} ℤ ⥤+ ModuleCat.{0} ℤ} (α β : F ⟶ G) :
    (leftDerivedDegreeFunctor (ModuleCat.{0} ℤ) (ModuleCat.{0} ℤ) n).map (α - β) =
      NatTrans.leftDerived α.hom n - NatTrans.leftDerived β.hom n := by
  rw [Functor.map_sub]
  rfl

/-- Projective resolutions send a difference to the difference of the lifts. -/
example {X Y : ModuleCat.{0} ℤ} (f g : X ⟶ Y) :
    (projectiveResolutions (ModuleCat.{0} ℤ)).map (f - g) =
      (projectiveResolutions _).map f - (projectiveResolutions _).map g :=
  Functor.map_sub _

/-- Injective resolutions send a difference to the difference of the descents. -/
example {X Y : ModuleCat.{0} ℤ} (f g : X ⟶ Y) :
    (injectiveResolutions (ModuleCat.{0} ℤ)).map (f - g) =
      (injectiveResolutions _).map f - (injectiveResolutions _).map g :=
  Functor.map_sub _

/-- Negation as a natural automorphism of the identity functor. -/
noncomputable def negIso : 𝟭 (ModuleCat.{0} ℤ) ≅ 𝟭 (ModuleCat.{0} ℤ) where
  hom := -𝟙 _
  inv := -𝟙 _

/-- Deriving an isomorphism and its inverse composes to the identity. -/
example (n : ℕ) :
    NatIso.leftDerived negIso n ≪≫ NatIso.leftDerived negIso.symm n =
      Iso.refl ((𝟭 (ModuleCat.{0} ℤ)).leftDerived n) := by
  rw [← NatIso.leftDerived_trans, Iso.self_symm_id, NatIso.leftDerived_refl]

/-- The same for right derivation. -/
example (n : ℕ) :
    NatIso.rightDerived negIso n ≪≫ NatIso.rightDerived negIso.symm n =
      Iso.refl ((𝟭 (ModuleCat.{0} ℤ)).rightDerived n) := by
  rw [← NatIso.rightDerived_trans, Iso.self_symm_id, NatIso.rightDerived_refl]

/-- The derived negation isomorphism is not the identity at `ℤ` in degree zero. -/
example : (NatIso.leftDerived negIso 0).hom.app Zmod ≠ 𝟙 _ := by
  intro h
  have h0 : NatTrans.leftDerived (𝟙 (𝟭 (ModuleCat.{0} ℤ)) + negIso.hom) 0 = 0 := by
    rw [show 𝟙 (𝟭 (ModuleCat.{0} ℤ)) + negIso.hom = 0 from add_neg_cancel _,
      NatTrans.leftDerived_zero]
  rw [NatTrans.leftDerived_add, NatTrans.leftDerived_id] at h0
  have h1 := congrArg (fun α => α.app Zmod) h0
  simp only [NatTrans.app_add, NatTrans.id_app, NatTrans.app_zero] at h1
  rw [← NatIso.leftDerived_hom, h] at h1
  exact id_add_id_ne_zero_of_iso leftZero h1

/-- Naturality of derived isomorphisms against a derived square. -/
example (n : ℕ) :
    NatTrans.leftDerived negIso.hom n ≫ (NatIso.leftDerived negIso n).hom =
      (NatIso.leftDerived negIso n).hom ≫ NatTrans.leftDerived negIso.hom n :=
  NatIso.leftDerived_hom_naturality negIso negIso negIso.hom negIso.hom rfl n

/-- The same naturality for right derivation. -/
example (n : ℕ) :
    NatTrans.rightDerived negIso.hom n ≫ (NatIso.rightDerived negIso n).hom =
      (NatIso.rightDerived negIso n).hom ≫ NatTrans.rightDerived negIso.hom n :=
  NatIso.rightDerived_hom_naturality negIso negIso negIso.hom negIso.hom rfl n

/-- For the trivial resolution of the projective module `ℤ`, the zero-class
composite is the identity of `ℤ`. -/
example :
    let P := ProjectiveResolution.self Zmod
    let K := ((𝟭 (ModuleCat.{0} ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv ≫
      (P.isoLeftDerivedObj (𝟭 _) 0).inv ≫ (𝟭 (ModuleCat.{0} ℤ)).fromLeftDerivedZero.app Zmod =
        𝟙 Zmod := by
  intro P K
  rw [ProjectiveResolution.zeroClass_fromLeftDerivedZero]
  rfl

/-- The zero-class formula along the identity chain isomorphism. -/
example :
    let P := ProjectiveResolution.self Zmod
    let K := ((𝟭 (ModuleCat.{0} ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv ≫
      HomologicalComplex.homologyMap (Iso.refl K).hom 0 ≫ (P.isoLeftDerivedObj (𝟭 _) 0).inv ≫
        (𝟭 (ModuleCat.{0} ℤ)).fromLeftDerivedZero.app Zmod = 𝟙 Zmod := by
  intro P K
  rw [ProjectiveResolution.zeroClass_fromLeftDerivedZero_of_iso P (𝟭 _) K (Iso.refl K)]
  rfl

end Derived

end MathlibExtTest.CategoryTheory.Abelian

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Iso
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.Projective.HorseshoeComparison
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Long exact sequences for left-derived functors

An additive functor sends a degreewise split projective horseshoe to a short exact sequence of
chain complexes. The homology connecting morphism, transported by resolution comparisons, gives
the left-derived boundary. One isomorphism transports the entire exact five-arrow window.

Only projective resolutions and additivity are needed. In particular the degree-zero map on the
quotient is epi without right exactness of the original functor. Identifying its degree-zero
derived functor with the original functor is a separate result requiring finite-colimit
preservation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace ProjectiveResolution.HorseshoeData

variable {S : ShortComplex C} {hS : S.ShortExact}
variable {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
variable (H : ProjectiveResolution.HorseshoeData hS P₁ P₃)

/-- The existing horseshoe sequence after applying an additive functor. -/
abbrev mapped (F : C ⥤ D) [F.Additive] : ShortComplex (ChainComplex D ℕ) :=
  (ShortComplex.mk H.i H.p H.zero).map (F.mapHomologicalComplex _)

/-- Additivity preserves the split horseshoe sequence in every degree. -/
theorem mapped_shortExact (sH : H.Spec) (F : C ⥤ D) [F.Additive] :
    (H.mapped F).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let s := (ShortComplex.Splitting.ofHasBinaryBiproduct
    (P₁.complex.X n) (P₃.complex.X n)).map F
  have hi : H.i.f n = biprod.inl ≫ (sH.middleXIso n).inv := by
    rw [← sH.i_f n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e :
      (ShortComplex.mk (biprod.inl : P₁.complex.X n ⟶
        P₁.complex.X n ⊞ P₃.complex.X n) biprod.snd biprod.inl_snd).map F ≅
      (H.mapped F).map (HomologicalComplex.eval D (ComplexShape.down ℕ) n) :=
    ShortComplex.isoMk (Iso.refl _) (F.mapIso (sH.middleXIso n).symm) (Iso.refl _)
      (by
        change (Iso.refl _).hom ≫ F.map (H.i.f n) =
          F.map biprod.inl ≫ (F.mapIso (sH.middleXIso n).symm).hom
        rw [Iso.refl_hom, Category.id_comp, hi, F.map_comp]
        rfl)
      (by
        change (F.mapIso (sH.middleXIso n).symm).hom ≫ F.map (H.p.f n) =
          F.map biprod.snd ≫ (Iso.refl _).hom
        rw [Iso.refl_hom, Category.comp_id]
        change F.map (sH.middleXIso n).inv ≫ F.map (H.p.f n) = F.map biprod.snd
        rw [← F.map_comp]
        exact F.congr_map (sH.p_f n))
  exact (s.ofIso e).shortExact

/-- The inclusion's degree-zero component has the augmentation square. -/
theorem i_f_zero_comp_π : H.i.f 0 ≫ H.middle.π.f 0 = P₁.π.f 0 ≫ S.f := by
  exact (HomologicalComplex.comp_f H.i H.middle.π 0).symm.trans
    ((HomologicalComplex.congr_hom H.i_augmentation 0).trans
      ((HomologicalComplex.comp_f P₁.π ((ChainComplex.single₀ C).map S.f) 0).trans
        (congrArg (P₁.π.f 0 ≫ ·) (ChainComplex.single₀_map_f_zero S.f))))

/-- The projection's degree-zero component has the augmentation square. -/
theorem p_f_zero_comp_π : H.p.f 0 ≫ P₃.π.f 0 = H.middle.π.f 0 ≫ S.g := by
  exact (HomologicalComplex.comp_f H.p P₃.π 0).symm.trans
    ((HomologicalComplex.congr_hom H.p_augmentation 0).trans
      ((HomologicalComplex.comp_f H.middle.π ((ChainComplex.single₀ C).map S.g) 0).trans
        (congrArg (H.middle.π.f 0 ≫ ·) (ChainComplex.single₀_map_f_zero S.g))))

variable [HasProjectiveResolutions C]

/-- The horseshoe boundary transported to the left-derived objects. -/
def delta (sH : H.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (F.leftDerived i).obj S.X₃ ⟶ (F.leftDerived j).obj S.X₁ :=
  (P₃.isoLeftDerivedObj F i).hom ≫ (H.mapped_shortExact sH F).δ i j hij ≫
    (P₁.isoLeftDerivedObj F j).inv

/-- The transported connecting map agrees with the homology boundary. -/
theorem delta_eq (sH : H.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hMF : (H.mapped F).ShortExact) :
    H.delta sH F i j hij =
      (P₃.isoLeftDerivedObj F i).hom ≫ hMF.δ i j hij ≫
        (P₁.isoLeftDerivedObj F j).inv := rfl

/-- Five consecutive arrows of the left-derived homology sequence. -/
def longSequence (sH : H.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) : ComposableArrows D 5 :=
  ComposableArrows.mk₅ ((F.leftDerived i).map S.f) ((F.leftDerived i).map S.g)
    (H.delta sH F i j hij) ((F.leftDerived j).map S.f) ((F.leftDerived j).map S.g)

/-- All six resolution comparisons identify the derived window with the LES. -/
def longSequenceIso (sH : H.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    H.longSequence sH F i j hij ≅
      HomologicalComplex.HomologySequence.composableArrows₅
        (H.mapped_shortExact sH F) i j hij := by
  refine ComposableArrows.isoMk₅ (P₁.isoLeftDerivedObj F i)
    (H.middle.isoLeftDerivedObj F i) (P₃.isoLeftDerivedObj F i)
    (P₁.isoLeftDerivedObj F j) (H.middle.isoLeftDerivedObj F j)
    (P₃.isoLeftDerivedObj F j) ?_ ?_ ?_ ?_ ?_
  · change (F.leftDerived i).map S.f ≫ (H.middle.isoLeftDerivedObj F i).hom =
      (P₁.isoLeftDerivedObj F i).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map H.i) i
    exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ H.middle H.i
      H.i_f_zero_comp_π F i
  · change (F.leftDerived i).map S.g ≫ (P₃.isoLeftDerivedObj F i).hom =
      (H.middle.isoLeftDerivedObj F i).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map H.p) i
    exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g H.middle P₃ H.p
      H.p_f_zero_comp_π F i
  · change H.delta sH F i j hij ≫ (P₁.isoLeftDerivedObj F j).hom =
      (P₃.isoLeftDerivedObj F i).hom ≫ (H.mapped_shortExact sH F).δ i j hij
    exact (Iso.eq_comp_inv (P₁.isoLeftDerivedObj F j)).mp
      (Category.assoc (P₃.isoLeftDerivedObj F i).hom
        ((H.mapped_shortExact sH F).δ i j hij) (P₁.isoLeftDerivedObj F j).inv).symm
  · change (F.leftDerived j).map S.f ≫ (H.middle.isoLeftDerivedObj F j).hom =
      (P₁.isoLeftDerivedObj F j).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map H.i) j
    exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.f P₁ H.middle H.i
      H.i_f_zero_comp_π F j
  · change (F.leftDerived j).map S.g ≫ (P₃.isoLeftDerivedObj F j).hom =
      (H.middle.isoLeftDerivedObj F j).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map H.p) j
    exact ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g H.middle P₃ H.p
      H.p_f_zero_comp_π F j

/-- Exactness of the entire derived window follows from one exact-sequence transport. -/
theorem longSequence_exact (sH : H.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (H.longSequence sH F i j hij).Exact :=
  ComposableArrows.exact_of_iso (H.longSequenceIso sH F i j hij).symm
    (HomologicalComplex.HomologySequence.composableArrows₅_exact
      (H.mapped_shortExact sH F) i j hij)

/-- The derived degree-zero quotient map is epi, without exactness of `F`. -/
theorem epi_leftDerived_map_g_zero (sH : H.Spec) (F : C ⥤ D) [F.Additive] :
    Epi ((F.leftDerived 0).map S.g) := by
  have hMF := H.mapped_shortExact sH F
  have : Epi (H.mapped F).g := hMF.epi_g
  have : Epi (HomologicalComplex.homologyMap (H.mapped F).g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by
      intro j hj
      simp only [ComplexShape.down_Rel] at hj
      exact Nat.succ_ne_zero j hj)
  let e : Arrow.mk ((F.leftDerived 0).map S.g) ≅
      Arrow.mk (HomologicalComplex.homologyMap (H.mapped F).g 0) :=
    Arrow.isoMk (H.middle.isoLeftDerivedObj F 0) (P₃.isoLeftDerivedObj F 0)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality S.g H.middle P₃ H.p
        H.p_f_zero_comp_π F 0).symm
  exact ((MorphismProperty.epimorphisms D).arrow_mk_iso_iff e).mpr
    (MorphismProperty.epimorphisms.infer_property _)

namespace Hom

variable {H}
variable {S' : ShortComplex C} {hS' : S'.ShortExact}
variable {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
variable {H' : ProjectiveResolution.HorseshoeData hS' P₁' P₃'}
variable {φ : S ⟶ S'} {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
variable {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}

/-- A supplied existing horseshoe comparison induces the mapped SES morphism. -/
def mapped (α : ProjectiveResolution.HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (F : C ⥤ D) [F.Additive] : H.mapped F ⟶ H'.mapped F :=
  ShortComplex.Hom.mk ((F.mapHomologicalComplex _).map u.hom)
    ((F.mapHomologicalComplex _).map α.hom) ((F.mapHomologicalComplex _).map w.hom)
    (by
      change (F.mapHomologicalComplex _).map u.hom ≫
          (F.mapHomologicalComplex _).map H'.i =
        (F.mapHomologicalComplex _).map H.i ≫ (F.mapHomologicalComplex _).map α.hom
      rw [← Functor.map_comp, ← Functor.map_comp, α.comm_i])
    (by
      change (F.mapHomologicalComplex _).map α.hom ≫
          (F.mapHomologicalComplex _).map H'.p =
        (F.mapHomologicalComplex _).map H.p ≫ (F.mapHomologicalComplex _).map w.hom
      rw [← Functor.map_comp, ← Functor.map_comp, α.comm_p])

/-- Naturality uses the given endpoint maps and the horseshoe boundary square. -/
theorem delta_naturality (α : ProjectiveResolution.HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (sH : H.Spec) (sH' : H'.Spec) (F : C ⥤ D) [F.Additive]
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    H.delta sH F i j hij ≫ (F.leftDerived j).map φ.τ₁ =
      (F.leftDerived i).map φ.τ₃ ≫ H'.delta sH' F i j hij := by
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (α.mapped F)
    (H.mapped_shortExact sH F) (H'.mapped_shortExact sH' F) i j hij
  change (H.mapped_shortExact sH F).δ i j hij ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map u.hom) j =
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map w.hom) i ≫
      (H'.mapped_shortExact sH' F).δ i j hij at hδ
  let a := (P₃.isoLeftDerivedObj F i).hom
  let a' := (P₃'.isoLeftDerivedObj F i).hom
  let t := (P₁.isoLeftDerivedObj F j).inv
  let t' := (P₁'.isoLeftDerivedObj F j).inv
  let d := (H.mapped_shortExact sH F).δ i j hij
  let d' := (H'.mapped_shortExact sH' F).δ i j hij
  let f := (F.leftDerived i).map φ.τ₃
  let g := (F.leftDerived j).map φ.τ₁
  let hm₁ := HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map u.hom) j
  let hm₃ := HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map w.hom) i
  have hu : u.hom.f 0 ≫ P₁'.π.f 0 = P₁.π.f 0 ≫ φ.τ₁ :=
    u.hom_f_zero_comp_π_f_zero.trans
      (congrArg (P₁.π.f 0 ≫ ·) (ChainComplex.single₀_map_f_zero φ.τ₁))
  have hw : w.hom.f 0 ≫ P₃'.π.f 0 = P₃.π.f 0 ≫ φ.τ₃ :=
    w.hom_f_zero_comp_π_f_zero.trans
      (congrArg (P₃.π.f 0 ≫ ·) (ChainComplex.single₀_map_f_zero φ.τ₃))
  have hs : f ≫ a' = a ≫ hm₃ :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality φ.τ₃ P₃ P₃' w.hom hw F i
  have ht : t ≫ g = hm₁ ≫ t' :=
    ProjectiveResolution.isoLeftDerivedObj_inv_naturality φ.τ₁ P₁ P₁' u.hom hu F j
  have hn : d ≫ hm₁ = hm₃ ≫ d' := hδ
  change (a ≫ d ≫ t) ≫ g = f ≫ (a' ≫ d' ≫ t')
  exact Iso.conjugate_naturality
    (P₃'.isoLeftDerivedObj F i) (P₃.isoLeftDerivedObj F i)
    (P₁'.isoLeftDerivedObj F j) (P₁.isoLeftDerivedObj F j)
    d' d f g hm₃ hm₁ hs ht.symm hn

end Hom
end ProjectiveResolution.HorseshoeData

variable [HasProjectiveResolutions C]

namespace LeftDerivedDelta

/-- The existing horseshoe construction with the chosen endpoint resolutions. -/
abbrev LDhorseshoe (S : ShortComplex C) (hS : S.ShortExact) :=
  ProjectiveResolution.horseshoe hS (projectiveResolution S.X₁)
    (projectiveResolution S.X₃)

/-- The canonical horseshoe sequence after applying `F`. -/
abbrev LDhorseshoeF (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) := (LDhorseshoe S hS).mapped F

/-- The canonical mapped horseshoe is short exact for every additive functor. -/
theorem LDhorseshoeF_shortExact (F : C ⥤ D) [F.Additive]
    (S : ShortComplex C) (hS : S.ShortExact) : (LDhorseshoeF F S hS).ShortExact :=
  (LDhorseshoe S hS).mapped_shortExact (ProjectiveResolution.horseshoe_spec hS _ _) F

/-- The canonical connecting map of the left-derived degree family. -/
def LDdelta (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) :
    (F.leftDerived (n + 1)).obj S.X₃ ⟶ (F.leftDerived n).obj S.X₁ :=
  (LDhorseshoe S hS).delta (ProjectiveResolution.horseshoe_spec hS _ _) F
    (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- The canonical boundary is the horseshoe homology boundary with endpoint transports. -/
theorem LDdelta_eq (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (hMF : (LDhorseshoeF F S hS).ShortExact) :
    LDdelta F n S hS =
      ((projectiveResolution S.X₃).isoLeftDerivedObj F (n + 1)).hom ≫
        hMF.δ (n + 1) n (ComplexShape.down_mk _ _ rfl) ≫
          ((projectiveResolution S.X₁).isoLeftDerivedObj F n).inv := rfl

/-- The canonical exact five-arrow window, containing the connecting morphism. -/
def LDlongSequence (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) : ComposableArrows D 5 :=
  (LDhorseshoe S hS).longSequence (ProjectiveResolution.horseshoe_spec hS _ _) F
    (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- Every canonical five-arrow window is exact. -/
theorem LDlongSequence_exact (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) : (LDlongSequence F n S hS).Exact :=
  (LDhorseshoe S hS).longSequence_exact (ProjectiveResolution.horseshoe_spec hS _ _) F
    (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- Exactness at the left term is a position in the transported window. -/
theorem LDexact_A (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ w : LDdelta F n S hS ≫ (F.leftDerived n).map S.f = 0,
      (ShortComplex.mk _ _ w).Exact := by
  have h := LDlongSequence_exact F n S hS
  exact ⟨h.toIsComplex.zero 2, h.exact 2⟩

/-- Exactness at the middle term is a position in the same transported window. -/
theorem LDexact_B (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ w : (F.leftDerived n).map S.f ≫ (F.leftDerived n).map S.g = 0,
      (ShortComplex.mk _ _ w).Exact := by
  have h := LDlongSequence_exact F n S hS
  exact ⟨h.toIsComplex.zero 3, h.exact 3⟩

/-- Exactness at the quotient term is a position in the same transported window. -/
theorem LDexact_C (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ w : (F.leftDerived (n + 1)).map S.g ≫ LDdelta F n S hS = 0,
      (ShortComplex.mk _ _ w).Exact := by
  have h := LDlongSequence_exact F n S hS
  exact ⟨h.toIsComplex.zero 1, h.exact 1⟩

/-- The degree-zero quotient map is epi without a right-exactness hypothesis on `F`. -/
theorem LDepi_zero (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) : Epi ((F.leftDerived 0).map S.g) :=
  (LDhorseshoe S hS).epi_leftDerived_map_g_zero
    (ProjectiveResolution.horseshoe_spec hS _ _) F

/-- The canonical boundary is natural under every map of short exact sequences. -/
theorem LDdelta_natural (F : C ⥤ D) [F.Additive] (n : ℕ)
    (S S' : ShortComplex C) (φ : S' ⟶ S) (hS : S.ShortExact) (hS' : S'.ShortExact) :
    (F.leftDerived (n + 1)).map φ.τ₃ ≫ LDdelta F n S hS =
      LDdelta F n S' hS' ≫ (F.leftDerived n).map φ.τ₁ := by
  let u := ProjectiveResolution.liftHom φ.τ₁ (projectiveResolution S'.X₁)
    (projectiveResolution S.X₁)
  let w := ProjectiveResolution.liftHom φ.τ₃ (projectiveResolution S'.X₃)
    (projectiveResolution S.X₃)
  obtain ⟨α⟩ := ProjectiveResolution.HorseshoeData.nonempty_hom
    (H := LDhorseshoe S' hS') (H' := LDhorseshoe S hS)
    (sH := ProjectiveResolution.horseshoe_spec hS' _ _)
    (sH' := ProjectiveResolution.horseshoe_spec hS _ _) (φ := φ) (u := u) (w := w)
  exact (α.delta_naturality (ProjectiveResolution.horseshoe_spec hS' _ _)
    (ProjectiveResolution.horseshoe_spec hS _ _) F
    (n + 1) n (ComplexShape.down_mk _ _ rfl)).symm

end LeftDerivedDelta
end CategoryTheory

end

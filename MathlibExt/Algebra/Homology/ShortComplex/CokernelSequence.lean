/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor

/-!
# Functorial cokernel sequences

The cokernel construction sends an arrow f : X₁ ⟶ X₂ to the short
complex X₁ ⟶ X₂ ⟶ coker f. It requires zero morphisms and cokernels.
For monomorphisms in an abelian category the sequence is short exact.
For homological complexes, the connecting morphisms are natural;
quasi-isomorphisms of monomorphic arrows induce quasi-isomorphisms
of cokernels, and a monomorphism is a quasi-isomorphism exactly when
its cokernel is acyclic.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCokernels C]

/-- The canonical functor `Arrow C ⥤ ShortComplex C` sending `f` to
`X₁ ⟶ X₂ ⟶ coker f`. Core uses only zero morphisms and cokernels; abelian
structure is not needed. -/
@[simps!]
noncomputable def cokernelSequenceFunctor : Arrow C ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence (Arrow C) C).functor.obj
    { f := Arrow.leftToRight (C := C)
      g := Limits.coker.π C
      zero := Limits.coker.condition C }

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The object map of `cokernelSequenceFunctor` is the pointwise
`ShortComplex.cokernelSequence`. -/
@[simp]
lemma cokernelSequenceFunctor_obj (f : Arrow C) :
    cokernelSequenceFunctor (C := C).obj f = ShortComplex.cokernelSequence f.hom :=
  rfl

/-- In an abelian category, for a monomorphism `f.hom`, the functorial cokernel
sequence `X₁ ⟶ X₂ ⟶ coker f` is short exact. -/
lemma cokernelSequence_shortExact (f : Arrow C) [Mono f.hom] :
    (cokernelSequenceFunctor (C := C).obj f).ShortExact := by
  have h_eq : cokernelSequenceFunctor (C := C).obj f =
      ShortComplex.cokernelSequence f.hom := rfl
  rw [h_eq]
  have h_mono : Mono (ShortComplex.cokernelSequence f.hom).f := by
    change Mono f.hom
    infer_instance
  have h_epi : Epi (ShortComplex.cokernelSequence f.hom).g := by
    infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f.hom) h_mono h_epi

end Abelian

end ShortComplex

end CategoryTheory

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}

/-- Horizontal criterion for a short exact sequence of homological complexes:
`S.f` is a quasi-isomorphism iff `S.X₃` is acyclic. Uses `homology_exact₂`
directly for epimorphy and `homology_exact₁` directly for monomorphy, with a
split on existence of a predecessor. -/
theorem quasiIso_f_iff (hS : S.ShortExact) :
    _root_.QuasiIso S.f ↔ S.X₃.Acyclic := by
  constructor
  · intro h
    exact hS.acyclic_X₃ h
  · intro hAcyc
    rw [_root_.quasiIso_iff]
    intro i
    rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
    have hEpi : Epi (HomologicalComplex.homologyMap S.f i) := by
      have hZero : IsZero (S.X₃.homology i) := (hAcyc i).isZero_homology
      have hgZero : HomologicalComplex.homologyMap S.g i = 0 :=
        IsZero.eq_zero_of_tgt hZero _
      exact (hS.homology_exact₂ i).epi_f hgZero
    have hMono : Mono (HomologicalComplex.homologyMap S.f i) := by
      by_cases hi : ∃ j, c.Rel j i
      · obtain ⟨j, hij⟩ := hi
        have hZeroJ : IsZero (S.X₃.homology j) := (hAcyc j).isZero_homology
        have hDeltaZero : hS.δ j i hij = 0 := IsZero.eq_zero_of_src hZeroJ _
        exact (hS.homology_exact₁ j i hij).mono_g hDeltaZero
      · have : Mono S.f := hS.mono_f
        have : Mono (S.f.f i) := inferInstance
        have hj : ∀ k, ¬ c.Rel k i := by
          intro k hk
          exact hi ⟨k, hk⟩
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f i hj
    have : IsIso (HomologicalComplex.homologyMap S.f i) := by
      have : Mono (HomologicalComplex.homologyMap S.f i) := hMono
      have : Epi (HomologicalComplex.homologyMap S.f i) := hEpi
      exact isIso_of_mono_of_epi _
    infer_instance

end CategoryTheory.ShortComplex.ShortExact

open CategoryTheory

namespace HomologicalComplex

namespace HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

/-- The functorial cokernel sequence of a bundled monomorphism is short exact. -/
theorem cokernelSequenceFunctor_mono_shortExact
    (A : (MorphismProperty.monomorphisms (HomologicalComplex C c)).Arrow ⊤ ⊤) :
    (CategoryTheory.ShortComplex.cokernelSequenceFunctor
      (C := HomologicalComplex C c)).obj
      ((MorphismProperty.Arrow.forget _ _ _).obj A) |>.ShortExact := by
  have : Mono ((MorphismProperty.Arrow.forget _ _ _).obj A).hom := by
    change Mono A.hom
    exact A.prop
  exact CategoryTheory.ShortComplex.cokernelSequence_shortExact _

/-- The pointwise connecting homomorphism for the cokernel short exact sequence
of a monomorphism of homological complexes. This is the opaque semantic boundary:
defined via `ShortExact.δ` of the functorial cokernel sequence. -/
noncomputable def cokernelSequenceδ
    (A : (MorphismProperty.monomorphisms (HomologicalComplex C c)).Arrow ⊤ ⊤)
    (i j : ι) (hij : c.Rel i j) :
    ((CategoryTheory.ShortComplex.cokernelSequenceFunctor
      (C := HomologicalComplex C c)).obj
      ((MorphismProperty.Arrow.forget _ _ _).obj A)).X₃.homology i ⟶
    ((CategoryTheory.ShortComplex.cokernelSequenceFunctor
      (C := HomologicalComplex C c)).obj
      ((MorphismProperty.Arrow.forget _ _ _).obj A)).X₁.homology j :=
  (cokernelSequenceFunctor_mono_shortExact A).δ i j hij

/-- Vertical theorem: for a morphism `φ` of monomorphic arrows of homological
complexes, if left and right legs are quasi-isomorphisms, then the induced map
on cokernels (via `Limits.coker`) is a quasi-isomorphism. Distinct from the
horizontal `quasiIso_f_iff` criterion. -/
lemma quasiIso_coker_map
    {A B : (MorphismProperty.monomorphisms (HomologicalComplex C c)).Arrow ⊤ ⊤}
    (φ : A ⟶ B)
    (h_left : QuasiIso φ.left)
    (h_right : QuasiIso φ.right) :
    QuasiIso
      ((MorphismProperty.Arrow.forget _ _ _ ⋙ Limits.coker (HomologicalComplex C c)).map φ) := by
  let F := CategoryTheory.ShortComplex.cokernelSequenceFunctor (C := HomologicalComplex C c)
  let forgetH := MorphismProperty.Arrow.forget
    (MorphismProperty.monomorphisms (HomologicalComplex C c)) ⊤ ⊤
  have hS_A : (F.obj (forgetH.obj A)).ShortExact :=
    cokernelSequenceFunctor_mono_shortExact A
  have hS_B : (F.obj (forgetH.obj B)).ShortExact :=
    cokernelSequenceFunctor_mono_shortExact B
  let ψ : F.obj (forgetH.obj A) ⟶ F.obj (forgetH.obj B) :=
    F.map (forgetH.map φ)
  have hτ₁ : ψ.τ₁ = φ.left := rfl
  have hτ₂ : ψ.τ₂ = φ.right := rfl
  have hτ₃ : ψ.τ₃ = (forgetH ⋙ Limits.coker _).map φ := rfl
  have h_left' : QuasiIso ψ.τ₁ := by
    rw [hτ₁]
    exact h_left
  have h_right' : QuasiIso ψ.τ₂ := by
    rw [hτ₂]
    exact h_right
  have h_τ₃ : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hS_A hS_B h_left' h_right'
  rw [← hτ₃]
  exact h_τ₃

/-- The connecting natural transformation for the cokernel sequence, with
component definitionally equal to `cokernelSequenceδ`. Naturality follows from
`δ_naturality` for short exact sequences. -/
noncomputable def cokernelSequenceδNatTrans
    (i j : ι) (hij : c.Rel i j) :
    (MorphismProperty.Arrow.forget
        (MorphismProperty.monomorphisms (HomologicalComplex C c)) ⊤ ⊤ ⋙
        Limits.coker (HomologicalComplex C c) ⋙
        HomologicalComplex.homologyFunctor C c i) ⟶
      (MorphismProperty.Arrow.forget
          (MorphismProperty.monomorphisms (HomologicalComplex C c)) ⊤ ⊤ ⋙
          Arrow.leftFunc ⋙
          HomologicalComplex.homologyFunctor C c j) :=
  δNatTransOfFamily
    (MorphismProperty.Arrow.forget
        (MorphismProperty.monomorphisms (HomologicalComplex C c)) ⊤ ⊤ ⋙
      CategoryTheory.ShortComplex.cokernelSequenceFunctor)
    cokernelSequenceFunctor_mono_shortExact i j hij

@[simp]
lemma cokernelSequenceδNatTrans_app
    (i j : ι) (hij : c.Rel i j)
    (A : (MorphismProperty.monomorphisms
      (HomologicalComplex C c)).Arrow ⊤ ⊤) :
    (cokernelSequenceδNatTrans i j hij).app A =
      cokernelSequenceδ A i j hij :=
  rfl

end HomologySequence

section CokernelCriterion

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
variable {K L : HomologicalComplex C c} (f : K ⟶ L) [Mono f]

/-- Horizontal criterion for a monomorphism of homological complexes: `f` is a
quasi-isomorphism iff its cokernel is acyclic. Derived from
`ShortExact.quasiIso_f_iff` applied to `ShortComplex.cokernelSequence`. -/
theorem quasiIso_iff_acyclic_cokernel :
    QuasiIso f ↔ (Limits.cokernel f).Acyclic := by
  let fArrow : Arrow (HomologicalComplex C c) := Arrow.mk f
  have : Mono fArrow.hom := by
    change Mono f
    infer_instance
  have hShortExact : (ShortComplex.cokernelSequence f).ShortExact := by
    have h1 : (CategoryTheory.ShortComplex.cokernelSequenceFunctor
        (C := HomologicalComplex C c)).obj fArrow =
        ShortComplex.cokernelSequence fArrow.hom :=
      CategoryTheory.ShortComplex.cokernelSequenceFunctor_obj fArrow
    have h2 : (CategoryTheory.ShortComplex.cokernelSequenceFunctor
        (C := HomologicalComplex C c)).obj fArrow |>.ShortExact :=
      CategoryTheory.ShortComplex.cokernelSequence_shortExact fArrow
    rw [h1] at h2
    exact h2
  have hIff := hShortExact.quasiIso_f_iff
  have hF : (ShortComplex.cokernelSequence f).f = f := rfl
  have hX₃ : (ShortComplex.cokernelSequence f).X₃ = Limits.cokernel f := rfl
  rw [hF] at hIff
  rw [hX₃] at hIff
  exact hIff

end CokernelCriterion


/- Generic coefficient-cokernel evaluation and transition maps, independent of topology. -/
noncomputable section CoefficientCokernelTransitions

universe uJ vJ uC vC

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {A B : J ⥤ ChainComplex C ℕ} (α : A ⟶ B) [Mono α]

/-- Evaluation identifies the chosen relative object with the pointwise cokernel. -/
@[no_expose]
def coefficientCokernelEvaluationIso (j : J) :
    (cokernel α).obj j ≅ cokernel (α.app j) :=
  PreservesCokernel.iso ((evaluation J (ChainComplex C ℕ)).obj j) α

omit [Mono α] in
private theorem coefficientCokernelEvaluationIso_projection_computation (j : J) :
    (cokernel.π α).app j ≫ (coefficientCokernelEvaluationIso α j).hom =
      cokernel.π (α.app j) := by
  let ev : (J ⥤ ChainComplex C ℕ) ⥤ ChainComplex C ℕ :=
    (evaluation J (ChainComplex C ℕ)).obj j
  have hProjection : ev.map (cokernel.π α) ≫ (PreservesCokernel.iso ev α).hom =
      cokernel.π (ev.map α) := PreservesCokernel.π_iso_hom ev α
  change ev.map (cokernel.π α) ≫ (PreservesCokernel.iso ev α).hom =
    cokernel.π (ev.map α)
  exact hProjection

omit [Mono α] in
/-- The entire original quotient projection is retained under evaluation. -/
theorem coefficientCokernelEvaluationIso_projection (j : J) :
    (cokernel.π α).app j ≫ (coefficientCokernelEvaluationIso α j).hom =
      cokernel.π (α.app j) :=
  coefficientCokernelEvaluationIso_projection_computation α j

/-- Original quasi-isomorphisms on both sides give the relative cokernel transition. -/
theorem cokernelDiagramTransition_quasiIso {j k : J} (a : j ⟶ k)
    (hA : QuasiIso (A.map a)) (hB : QuasiIso (B.map a)) :
    QuasiIso ((cokernel α).map a) := by
  let D := cokernel α
  let eJ := coefficientCokernelEvaluationIso α j
  let eK := coefficientCokernelEvaluationIso α k
  let f := cokernel.map (α.app j) (α.app k) (A.map a) (B.map a) (α.naturality a).symm
  let aj : (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ :=
    MorphismProperty.Arrow.mk (α.app j) (by infer_instance)
  let ak : (MorphismProperty.monomorphisms (ChainComplex C ℕ)).Arrow ⊤ ⊤ :=
    MorphismProperty.Arrow.mk (α.app k) (by infer_instance)
  let s : aj ⟶ ak :=
    MorphismProperty.Arrow.homMk (A.map a) (B.map a) (α.naturality a)
  have hRaw : QuasiIso f := by
    have h := HomologySequence.quasiIso_coker_map s hA hB
    change QuasiIso f at h
    exact h
  have hSquare : D.map a ≫ eK.hom = eJ.hom ≫ f := by
    apply (cancel_epi ((cokernel.π α).app j)).mp
    have hNat : (cokernel.π α).app j ≫ D.map a = B.map a ≫ (cokernel.π α).app k :=
      (cokernel.π α).naturality a |>.symm
    have hRawProjection : cokernel.π (α.app j) ≫ f = B.map a ≫ cokernel.π (α.app k) :=
      cokernel.π_desc _ _ _
    calc
      _ = ((cokernel.π α).app j ≫ D.map a) ≫ eK.hom := (Category.assoc _ _ _).symm
      _ = (B.map a ≫ (cokernel.π α).app k) ≫ eK.hom := congrArg (fun k => k ≫ eK.hom) hNat
      _ = B.map a ≫ cokernel.π (α.app k) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => B.map a ≫ k) (coefficientCokernelEvaluationIso_projection α k))
      _ = cokernel.π (α.app j) ≫ f := hRawProjection.symm
      _ = ((cokernel.π α).app j ≫ eJ.hom) ≫ f :=
        congrArg (fun k => k ≫ f) (coefficientCokernelEvaluationIso_projection α j).symm
      _ = _ := Category.assoc _ _ _
  have hMap : D.map a = eJ.hom ≫ f ≫ eK.inv := by
    apply (cancel_mono eK.hom).mp
    have h₁ : (eJ.hom ≫ f ≫ eK.inv) ≫ eK.hom =
        eJ.hom ≫ ((f ≫ eK.inv) ≫ eK.hom) :=
      Category.assoc eJ.hom (f ≫ eK.inv) eK.hom
    have h₂ : eJ.hom ≫ ((f ≫ eK.inv) ≫ eK.hom) =
        eJ.hom ≫ (f ≫ (eK.inv ≫ eK.hom)) :=
      congrArg (fun m : cokernel (α.app j) ⟶ cokernel (α.app k) => eJ.hom ≫ m)
        (Category.assoc f eK.inv eK.hom)
    have h₃ : eJ.hom ≫ (f ≫ (eK.inv ≫ eK.hom)) =
        eJ.hom ≫ (f ≫ 𝟙 (cokernel (α.app k))) :=
      congrArg (fun m : cokernel (α.app k) ⟶ cokernel (α.app k) => eJ.hom ≫ (f ≫ m))
        eK.inv_hom_id
    have h₄ : eJ.hom ≫ (f ≫ 𝟙 (cokernel (α.app k))) = eJ.hom ≫ f :=
      congrArg (fun m : cokernel (α.app j) ⟶ cokernel (α.app k) => eJ.hom ≫ m)
        (Category.comp_id f)
    exact hSquare.trans (h₁.trans (h₂.trans (h₃.trans h₄))).symm
  let : QuasiIso f := hRaw
  rw [hMap]
  infer_instance

end CoefficientCokernelTransitions

end HomologicalComplex

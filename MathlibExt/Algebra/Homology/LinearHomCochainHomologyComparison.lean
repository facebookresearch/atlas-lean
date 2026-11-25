/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
import MathlibExt.Algebra.Homology.LinearHomCochainComplexQuasiIso

/-!
# Hom-cochain cohomology and homology duals

This file defines the canonical comparison from the cohomology of a linear
Hom-cochain complex to the linear dual of homology.  The construction is valid
in an arbitrary abelian `R`-linear category: a cochain cycle restricts to
cycles of the chain complex and then descends to homology.

When the chain groups and homology objects are projective, the comparison is
an isomorphism.  That proof internally chooses sections of homology
projections.  Those choices are noncanonical proof data only: no splitting is
exposed by, or assumed in, the public comparison or its resulting isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace HomologicalComplex

variable (R : Type w) [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- The morphism on chain homology represented by a linear Hom-cochain cycle. -/
public noncomputable def linearHomCochainCycleDesc
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    K.homology n ⟶ M := by
  let D := (linearHomCochainComplexFunctor R C M).obj (op K)
  let f' : K.X n ⟶ M :=
    (D.iCycles n).hom f
  let hmid : (K.sc n).X₂ ⟶ M := by
    with_unfolding_all exact f'
  let hfac : (K.sc n).cycles ⟶ M := (K.sc n).iCycles ≫ hmid
  have hfac_eq : (K.sc n).toCycles ≫ hfac =
      (K.sc n).f ≫ hmid := by
    simpa only [hfac] using
      (ShortComplex.toCycles_i_assoc (S := K.sc n) hmid)
  have hsource : (K.sc n).f ≫ hmid = 0 := by
    have hf := ConcreteCategory.congr_hom ((D.sc n).iCycles_g) f
    have hdual :
        (D.sc n).g.hom ((D.sc n).iCycles.hom f) =
          (K.sc n).f ≫ hmid := by
      with_unfolding_all rfl
    exact hdual.symm.trans hf
  exact (K.sc n).descHomology hfac (hfac_eq.trans hsource)

/-- The morphism represented by a cochain cycle restricts to the original
cochain on chain cycles. -/
@[reassoc]
public theorem linearHomCochainCycleDesc_fac
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    K.homologyπ n ≫ linearHomCochainCycleDesc R K M n f =
      K.iCycles n ≫
        (((linearHomCochainComplexFunctor R C M).obj
          (op K)).iCycles n).hom f := by
  unfold linearHomCochainCycleDesc
  with_unfolding_all
    apply ShortComplex.π_descHomology

/-- Restriction of cochain cycles followed by descent to chain homology. -/
public noncomputable def linearHomCochainCyclesComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  ModuleCat.ofHom
    { toFun := linearHomCochainCycleDesc R K M n
      map_add' := by
        intro f g
        apply (cancel_epi (K.homologyπ n)).1
        rw [linearHomCochainCycleDesc_fac,
          Preadditive.comp_add,
          linearHomCochainCycleDesc_fac,
          linearHomCochainCycleDesc_fac]
        exact (congrArg (fun z => K.iCycles n ≫ z)
          (map_add ((((linearHomCochainComplexFunctor R C M).obj
            (op K)).iCycles n).hom) f g)).trans
          (by apply Preadditive.comp_add)
      map_smul' := by
        intro r f
        apply (cancel_epi (K.homologyπ n)).1
        rw [linearHomCochainCycleDesc_fac,
          Linear.comp_smul,
          linearHomCochainCycleDesc_fac]
        exact (congrArg (fun z => K.iCycles n ≫ z)
          (map_smul ((((linearHomCochainComplexFunctor R C M).obj
            (op K)).iCycles n).hom) r f)).trans
          (by apply Linear.comp_smul) }

/-- The homology morphism represented by a cochain cycle is its image under
the cycles comparison. -/
@[simp]
public theorem linearHomCochainCyclesComparison_hom_apply
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    (f : (((linearHomCochainComplexFunctor R C M).obj
      (op K)).sc n).leftHomologyData.K) :
    linearHomCochainCycleDesc R K M n f =
      (linearHomCochainCyclesComparison R K M n).hom f :=
  rfl

/-- Cochain boundaries induce the zero morphism on chain homology. -/
public theorem linearHomCochain_toCycles_comp_cyclesComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    (((linearHomCochainComplexFunctor R C M).obj (op K)).sc n).toCycles ≫
        linearHomCochainCyclesComparison R K M n =
      0 := by
  let D := (linearHomCochainComplexFunctor R C M).obj (op K)
  apply ModuleCat.hom_ext
  ext f
  let bcycle : (D.sc n).leftHomologyData.K := by
    with_unfolding_all exact (D.sc n).toCycles.hom f
  change linearHomCochainCycleDesc R K M n bcycle = 0
  apply (cancel_epi (K.homologyπ n)).1
  rw [Limits.comp_zero, linearHomCochainCycleDesc_fac]
  have hf :
      (D.iCycles n).hom
          bcycle =
        (D.sc n).f.hom f := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom ((D.sc n).toCycles_i) f
  let ftail : K.X ((ComplexShape.down ℕ).next n) ⟶ M := by
    with_unfolding_all exact f
  have hD : (D.sc n).f.hom f =
      K.d n ((ComplexShape.down ℕ).next n) ≫ ftail := by
    with_unfolding_all rfl
  rw [hf, hD]
  simpa only [Limits.zero_comp] using
    K.iCycles_d_assoc n ((ComplexShape.down ℕ).next n) ftail

/-- The canonical comparison from linear Hom-cochain cohomology to the linear
dual of homology. -/
public noncomputable def linearHomCochainHomologyComparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homology n ⟶
      ModuleCat.of R (K.homology n ⟶ M) :=
  (((linearHomCochainComplexFunctor R C M).obj (op K)).sc n).descHomology
    (linearHomCochainCyclesComparison R K M n)
    (linearHomCochain_toCycles_comp_cyclesComparison R K M n)

@[reassoc (attr := simp)]
public theorem linearHomCochainHomologyπ_comp_comparison
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homologyπ n ≫
        linearHomCochainHomologyComparison R K M n =
      linearHomCochainCyclesComparison R K M n := by
  apply ShortComplex.π_descHomology

/-- The Hom-cochain-to-homology comparison is covariantly natural in the
coefficient object. -/
@[reassoc]
public theorem linearHomCochainHomologyComparison_naturality_coefficient
    (K : ChainComplex C ℕ) {M N : C} (a : M ⟶ N) (n : ℕ) :
    homologyMap
          (((linearHomCochainComplexBifunctor R C).map a).app (op K)) n ≫
        linearHomCochainHomologyComparison R K N n =
      linearHomCochainHomologyComparison R K M n ≫
        ((linearYoneda R C).map a).app (op (K.homology n)) := by
  let Dₘ := (linearHomCochainComplexFunctor R C M).obj (op K)
  let Dₙ := (linearHomCochainComplexFunctor R C N).obj (op K)
  let F : Dₘ ⟶ Dₙ := by
    with_unfolding_all
      exact ((linearHomCochainComplexBifunctor R C).map a).app (op K)
  let cF : (Dₘ.sc n).leftHomologyData.K ⟶
      (Dₙ.sc n).leftHomologyData.K := by
    with_unfolding_all exact cyclesMap F n
  let aH : ModuleCat.of R (K.homology n ⟶ M) ⟶
      ModuleCat.of R (K.homology n ⟶ N) := by
    with_unfolding_all
      exact ((linearYoneda R C).map a).app (op (K.homology n))
  with_unfolding_all
    change homologyMap F n ≫
        linearHomCochainHomologyComparison R K N n =
      linearHomCochainHomologyComparison R K M n ≫ aH
  apply (cancel_epi (Dₘ.homologyπ n)).1
  rw [homologyπ_naturality_assoc,
    linearHomCochainHomologyπ_comp_comparison]
  with_unfolding_all
    change cF ≫ linearHomCochainCyclesComparison R K N n =
      Dₘ.homologyπ n ≫
        linearHomCochainHomologyComparison R K M n ≫
          aH
  rw [linearHomCochainHomologyπ_comp_comparison_assoc]
  apply ModuleCat.hom_ext
  ext f
  apply (cancel_epi (K.homologyπ n)).1
  with_unfolding_all
    change K.homologyπ n ≫
        linearHomCochainCycleDesc R K N n (cF.hom f) =
      K.homologyπ n ≫ (linearHomCochainCycleDesc R K M n f ≫ a)
  rw [linearHomCochainCycleDesc_fac]
  rw [← Category.assoc, linearHomCochainCycleDesc_fac]
  have hf :
      (Dₙ.iCycles n).hom (cF.hom f) =
        (Dₘ.iCycles n).hom f ≫ a := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom (cyclesMap_i F n) f
  rw [hf]
  exact (Category.assoc _ _ _).symm

/-- The Hom-cochain-to-homology comparison is contravariantly natural in the
chain complex. -/
@[reassoc]
public theorem linearHomCochainHomologyComparison_naturality_chain
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (M : C) (n : ℕ) :
    homologyMap ((linearHomCochainComplexFunctor R C M).map f.op) n ≫
        linearHomCochainHomologyComparison R K M n =
      linearHomCochainHomologyComparison R L M n ≫
        ModuleCat.ofHom (Linear.leftComp R M (homologyMap f n)) := by
  let Dₖ := (linearHomCochainComplexFunctor R C M).obj (op K)
  let Dₗ := (linearHomCochainComplexFunctor R C M).obj (op L)
  let F := (linearHomCochainComplexFunctor R C M).map f.op
  let cF : (Dₗ.sc n).leftHomologyData.K ⟶
      (Dₖ.sc n).leftHomologyData.K := by
    with_unfolding_all exact cyclesMap F n
  apply (cancel_epi (Dₗ.homologyπ n)).1
  rw [homologyπ_naturality_assoc,
    linearHomCochainHomologyπ_comp_comparison]
  with_unfolding_all
    change cF ≫ linearHomCochainCyclesComparison R K M n =
      Dₗ.homologyπ n ≫
        linearHomCochainHomologyComparison R L M n ≫
          ModuleCat.ofHom (Linear.leftComp R M (homologyMap f n))
  rw [linearHomCochainHomologyπ_comp_comparison_assoc]
  apply ModuleCat.hom_ext
  ext φ
  apply (cancel_epi (K.homologyπ n)).1
  change K.homologyπ n ≫
      linearHomCochainCycleDesc R K M n (cF.hom φ) =
    K.homologyπ n ≫
      (homologyMap f n ≫ linearHomCochainCycleDesc R L M n φ)
  rw [linearHomCochainCycleDesc_fac]
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    linearHomCochainCycleDesc_fac]
  have hφ :
      (Dₖ.iCycles n).hom (cF.hom φ) =
        f.f n ≫ (Dₗ.iCycles n).hom φ := by
    with_unfolding_all
      exact ConcreteCategory.congr_hom (cyclesMap_i F n) φ
  rw [hφ]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ ((Dₗ.iCycles n).hom φ))
      (cyclesMap_i f n).symm)).trans
    (Category.assoc _ _ _)

/-! ## The projective-homology isomorphism -/

private noncomputable def homologyComplex (K : ChainComplex C ℕ) :
    ChainComplex C ℕ where
  X i := K.homology i
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private noncomputable def homologyComplexXIso
    (K : ChainComplex C ℕ) (i : ℕ) :
    (homologyComplex K).X i ≅ K.homology i :=
  Iso.refl _

@[simp]
private lemma homologyComplex_d (K : ChainComplex C ℕ) (i j : ℕ) :
    (homologyComplex K).d i j = 0 :=
  rfl

private noncomputable def homologyCycleSection
    (K : ChainComplex C ℕ) (i : ℕ) [Projective (K.homology i)] :
    K.homology i ⟶ K.cycles i :=
  Projective.factorThru (f := 𝟙 (K.homology i)) (K.homologyπ i)

@[reassoc (attr := simp)]
private theorem homologyCycleSection_comp_homologyπ
    (K : ChainComplex C ℕ) (i : ℕ) [Projective (K.homology i)] :
    homologyCycleSection K i ≫ K.homologyπ i = 𝟙 _ := by
  apply Projective.factorThru_comp

/-- A noncanonical projective section gives a quasi-isomorphism from the
zero-differential homology complex.  This is internal proof machinery; the
chosen section is not exposed by the public comparison or isomorphism. -/
private noncomputable def homologyComplexTo
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] :
    homologyComplex K ⟶ K where
  f i := by
    let _ : Projective (K.homology i) := hK i
    exact (homologyComplexXIso K i).hom ≫
      homologyCycleSection K i ≫ K.iCycles i
  comm' i j _ := by
    rw [homologyComplex_d, zero_comp, Category.assoc, Category.assoc,
      iCycles_d, comp_zero, comp_zero]

@[simp]
private theorem homologyComplexTo_f
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] (i : ℕ) :
    (homologyComplexTo K).f i =
      (homologyComplexXIso K i).hom ≫
        homologyCycleSection K i ≫ K.iCycles i := by
  let _ : Projective (K.homology i) := hK i
  rfl

set_option linter.style.haveILetI false in
private theorem homologyComplexTo_quasiIso
    (K : ChainComplex C ℕ) [hK : ∀ i, Projective (K.homology i)] :
    QuasiIso (homologyComplexTo K) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let _ : Projective (K.homology i) := hK i
  let hICycles : IsIso ((homologyComplex K).iCycles i) :=
    ShortComplex.isIso_iCycles ((homologyComplex K).sc i) (by
      simp only [shortComplexFunctor_obj_g, homologyComplex_d]
      exact rfl)
  letI : IsIso ((homologyComplex K).iCycles i) := hICycles
  let hHomologyπ : IsIso ((homologyComplex K).homologyπ i) :=
    ShortComplex.isIso_homologyπ ((homologyComplex K).sc i) (by
      simp only [shortComplexFunctor_obj_f, homologyComplex_d]
      exact rfl)
  letI : IsIso ((homologyComplex K).homologyπ i) := hHomologyπ
  have hcycles :
      cyclesMap (homologyComplexTo K) i =
        (homologyComplex K).iCycles i ≫
          (homologyComplexXIso K i).hom ≫
            homologyCycleSection K i := by
    apply (cancel_mono (K.iCycles i)).1
    rw [cyclesMap_i, homologyComplexTo_f]
    simp only [Category.assoc]
  have h :
      (homologyComplex K).homologyπ i ≫
          homologyMap (homologyComplexTo K) i =
        (homologyComplex K).iCycles i ≫
          (homologyComplexXIso K i).hom := by
    simp only [homologyπ_naturality, hcycles, Category.assoc,
      homologyCycleSection_comp_homologyπ, Category.comp_id]
  let htarget : IsIso ((homologyComplex K).iCycles i ≫
      (homologyComplexXIso K i).hom) := by infer_instance
  let hcomp : IsIso ((homologyComplex K).homologyπ i ≫
      homologyMap (homologyComplexTo K) i) := h ▸ htarget
  letI : IsIso ((homologyComplex K).homologyπ i ≫
      homologyMap (homologyComplexTo K) i) := hcomp
  exact IsIso.of_isIso_comp_left ((homologyComplex K).homologyπ i)
    (homologyMap (homologyComplexTo K) i)

private theorem homologyπ_comp_homologyIsoOfZeros_hom
    {A : Type u'} [Category.{v'} A] [Abelian A]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex A c) (i : ι)
    (hf : (K.sc i).f = 0) (hg : (K.sc i).g = 0) :
    K.homologyπ i ≫
        ((ShortComplex.HomologyData.ofZeros (K.sc i) hf hg).left.homologyIso).hom =
      K.iCycles i := by
  let h := (ShortComplex.HomologyData.ofZeros (K.sc i) hf hg).left
  change (K.sc i).homologyπ ≫ h.homologyIso.hom = (K.sc i).iCycles
  rw [h.homologyπ_comp_homologyIso_hom, ← h.cyclesIso_hom_comp_i]
  rfl

private noncomputable def homologyComplexHomologyIsoX
    (K : ChainComplex C ℕ) (n : ℕ) :
    (homologyComplex K).homology n ≅ (homologyComplex K).X n :=
  (ShortComplex.HomologyData.ofZeros ((homologyComplex K).sc n)
    (by
      simp only [shortComplexFunctor_obj_f, homologyComplex_d]
      exact rfl)
    (by
      simp only [shortComplexFunctor_obj_g, homologyComplex_d]
      exact rfl)).left.homologyIso

private lemma linearHomHomologyComplex_d
    (K : ChainComplex C ℕ) (M : C) (i j : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
      (op (homologyComplex K))).d i j = 0 := by
  change ((linearYoneda R C).obj M).map
      ((homologyComplex K).d j i).op = 0
  rw [homologyComplex_d]
  simp only [op_zero, Functor.map_zero]

private noncomputable def linearHomHomologyComplexHomologyIsoX
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).homology n ≅
      ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).X n :=
  (ShortComplex.HomologyData.ofZeros
    (((linearHomCochainComplexFunctor R C M).obj
      (op (homologyComplex K))).sc n)
    (by
      simp only [shortComplexFunctor_obj_f, linearHomHomologyComplex_d]
      exact rfl)
    (by
      simp only [shortComplexFunctor_obj_g, linearHomHomologyComplex_d]
      exact rfl)).left.homologyIso

private noncomputable def homologyComplexComparisonIso
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    ((linearHomCochainComplexFunctor R C M).obj
        (op (homologyComplex K))).homology n ≅
      ModuleCat.of R ((homologyComplex K).homology n ⟶ M) :=
  linearHomHomologyComplexHomologyIsoX R K M n ≪≫
    ((linearYoneda R C).obj M).mapIso (homologyComplexHomologyIsoX K n).op

private theorem linearHomCochainHomologyComparison_homologyComplex
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    linearHomCochainHomologyComparison R (homologyComplex K) M n =
      (homologyComplexComparisonIso R K M n).hom := by
  let H := homologyComplex K
  let D := (linearHomCochainComplexFunctor R C M).obj (op H)
  let eH := homologyComplexHomologyIsoX K n
  let eD := linearHomHomologyComplexHomologyIsoX R K M n
  let iD : (D.sc n).leftHomologyData.K ⟶ D.X n := by
    with_unfolding_all exact D.iCycles n
  let p : D.X n ⟶ ModuleCat.of R (H.homology n ⟶ M) := by
    with_unfolding_all exact (((linearYoneda R C).obj M).mapIso eH.op).hom
  apply (cancel_epi (D.homologyπ n)).1
  rw [linearHomCochainHomologyπ_comp_comparison]
  have hDπ : D.homologyπ n ≫ eD.hom = iD := by
    with_unfolding_all
      apply homologyπ_comp_homologyIsoOfZeros_hom
  with_unfolding_all
    change linearHomCochainCyclesComparison R H M n =
      D.homologyπ n ≫ eD.hom ≫ p
  have hDπp : D.homologyπ n ≫ eD.hom ≫ p = iD ≫ p := by
    rw [← Category.assoc, hDπ]
    rfl
  rw [hDπp]
  apply ModuleCat.hom_ext
  ext f
  apply (cancel_epi (H.homologyπ n)).1
  change H.homologyπ n ≫ linearHomCochainCycleDesc R H M n f =
    H.homologyπ n ≫ p.hom (iD.hom f)
  rw [linearHomCochainCycleDesc_fac]
  let φ : H.X n ⟶ M :=
    (D.iCycles n).hom f
  have hp : p.hom (iD.hom f) = eH.hom ≫ φ := by
    with_unfolding_all rfl
  have hHπ : H.homologyπ n ≫ eH.hom = H.iCycles n := by
    dsimp only [H, eH, homologyComplexHomologyIsoX]
    apply homologyπ_comp_homologyIsoOfZeros_hom
  change H.iCycles n ≫ φ = H.homologyπ n ≫ p.hom (iD.hom f)
  rw [hp, ← Category.assoc, hHπ]

private theorem linearHomCochainHomologyComparison_homologyComplex_isIso
    (K : ChainComplex C ℕ) (M : C) (n : ℕ) :
    IsIso (linearHomCochainHomologyComparison R
      (homologyComplex K) M n) := by
  rw [linearHomCochainHomologyComparison_homologyComplex]
  infer_instance

set_option linter.style.haveILetI false in
/-- If a chain complex and all its homology objects are projective, the
canonical comparison from linear Hom-cochain cohomology to the linear dual of
homology is an isomorphism.

The proof internally chooses projective sections in order to compare with the
zero-differential homology complex.  No chosen section or splitting is part of
the theorem statement or the resulting public isomorphism. -/
public theorem linearHomCochainHomologyComparison_isIso_of_projective_terms_and_homology
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [hK : ∀ i, Projective (K.X i)]
    [hH : ∀ i, Projective (K.homology i)] :
    IsIso (linearHomCochainHomologyComparison R K M n) := by
  let H := homologyComplex K
  let f := homologyComplexTo K
  let g := (linearHomCochainComplexFunctor R C M).map f.op
  let cH := linearHomCochainHomologyComparison R H M n
  let cK := linearHomCochainHomologyComparison R K M n
  letI : ∀ i, Projective (H.X i) := fun i ↦ hH i
  letI : QuasiIso f := homologyComplexTo_quasiIso K
  letI : QuasiIso g :=
    linearHomCochainComplexFunctor_map_quasiIso_of_projective R f M
  letI : IsIso (homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).mp
      (inferInstance : QuasiIsoAt f n)
  letI : IsIso (homologyMap g n) :=
    (quasiIsoAt_iff_isIso_homologyMap g n).mp
      (inferInstance : QuasiIsoAt g n)
  let ef : H.homology n ≅ K.homology n := asIso (homologyMap f n)
  let pIso : ModuleCat.of R (K.homology n ⟶ M) ≅
      ModuleCat.of R (H.homology n ⟶ M) :=
    ((linearYoneda R C).obj M).mapIso ef.op
  let hcH : IsIso cH :=
    linearHomCochainHomologyComparison_homologyComplex_isIso R K M n
  letI : IsIso cH := hcH
  have hnat := linearHomCochainHomologyComparison_naturality_chain R f M n
  have hnat' : homologyMap g n ≫ cH = cK ≫ pIso.hom := by
    exact hnat
  let hleft : IsIso (homologyMap g n ≫ cH) := by infer_instance
  let hright : IsIso (cK ≫ pIso.hom) := hnat' ▸ hleft
  letI : IsIso (cK ≫ pIso.hom) := hright
  exact IsIso.of_isIso_comp_right cK pIso.hom

/-- The universal-coefficient isomorphism for a complex whose terms and homology
objects are projective, whose forward map is the canonical Hom-cochain
comparison.  It exposes no chosen splitting. -/
public noncomputable def linearHomCochainHomologyIsoOfProjectiveTermsAndHomology
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    ((linearHomCochainComplexFunctor R C M).obj (op K)).homology n ≅
      ModuleCat.of R (K.homology n ⟶ M) := by
  letI := linearHomCochainHomologyComparison_isIso_of_projective_terms_and_homology
    R K M n
  exact asIso (linearHomCochainHomologyComparison R K M n)

@[simp]
public theorem linearHomCochainHomologyIsoOfProjectiveTermsAndHomology_hom
    (K : ChainComplex C ℕ) (M : C) (n : ℕ)
    [∀ i, Projective (K.X i)]
    [∀ i, Projective (K.homology i)] :
    (linearHomCochainHomologyIsoOfProjectiveTermsAndHomology R K M n).hom =
      linearHomCochainHomologyComparison R K M n :=
  rfl

end HomologicalComplex

end

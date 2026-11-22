/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreUniversalProperty
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.IhomPiZeroHomotopyCategory

/-!
# Components of the actual core universal mapping comparison

The native scalar component/Hom bijection is transported by the actual
localized source counit and target unit. The transferred and independently
fixed scalar presentations therefore retain the same Kan–Quillen Ho maps.
The zero-projection comparison commutes with these functions and the original
local model's derived-component interpretation. Formal inverses occur only
in the localization or in the proved component bijections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialPresheaf.CoreMappingComponents

local notation "V" => toHomotopyCategory SSet

private theorem ho_pre_id {A B : SSet.{u}} (f : (V).obj A ⟶ (V).obj B) :
    (V).map (𝟙 A) ≫ f = f :=
  (congrArg (fun h => h ≫ f) ((V).map_id A)).trans (Category.id_comp f)

private theorem ho_post_id {A B : SSet.{u}} (f : (V).obj A ⟶ (V).obj B) :
    f ≫ (V).map (𝟙 B) = f :=
  (congrArg (fun h => f ≫ h) ((V).map_id B)).trans (Category.comp_id f)

/-- Actual weak replacement legs transport the native scalar component bijection. -/
def replacementHomEquiv {QK K L RL : SSet.{u}} (q : QK ⟶ K) (r : L ⟶ RL)
    [WeakEquivalence q] [WeakEquivalence r] [SSet.KanComplex RL] :
    SSet.π₀ ((ihom QK).obj RL) ≃ ((V).obj K ⟶ (V).obj L) :=
  (SSet.modelCategoryQuillen.ihomPiZeroHomEquiv QK RL).trans
    (Iso.homCongr (QuillenOrdinaryHoReplacement.replacementHoIso q)
      (QuillenOrdinaryHoReplacement.replacementHoIso r).symm)

/-- A represented component keeps both actual localized replacement legs. -/
theorem replacementHomEquiv_mk {QK K L RL : SSet.{u}} (q : QK ⟶ K) (r : L ⟶ RL)
    [WeakEquivalence q] [WeakEquivalence r] [SSet.KanComplex RL] (f : QK ⟶ RL) :
    replacementHomEquiv q r (SSet.π₀.mk (SSet.ihomVertexEquiv QK RL f)) =
      (QuillenOrdinaryHoReplacement.replacementHoIso q).inv ≫ (V).map f ≫
        (QuillenOrdinaryHoReplacement.replacementHoIso r).inv :=
  congrArg (fun h : (V).obj QK ⟶ (V).obj RL =>
    (QuillenOrdinaryHoReplacement.replacementHoIso q).inv ≫ h ≫
      (QuillenOrdinaryHoReplacement.replacementHoIso r).inv)
    (SSet.modelCategoryQuillen.ihomPiZeroHomEquiv_mk QK RL f)

/-- The transferred representative of an original scalar map has that exact Ho image. -/
theorem replacementHomEquiv_lift {QK K L RL : SSet.{u}} (q : QK ⟶ K) (r : L ⟶ RL)
    [WeakEquivalence q] [WeakEquivalence r] [SSet.KanComplex RL] (a : K ⟶ L) :
    replacementHomEquiv q r (SSet.π₀.mk (SSet.ihomVertexEquiv QK RL (q ≫ a ≫ r))) =
      (V).map a := by
  let qi := QuillenOrdinaryHoReplacement.replacementHoIso q
  let ri := QuillenOrdinaryHoReplacement.replacementHoIso r
  have hm : (V).map (q ≫ a ≫ r) = qi.hom ≫ (V).map a ≫ ri.hom :=
    ((V).map_comp q (a ≫ r)).trans
      (congrArg (fun h => (V).map q ≫ h) ((V).map_comp a r))
  have hc : qi.inv ≫ (V).map (q ≫ a ≫ r) ≫ ri.inv = (V).map a := by
    rw [hm]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact (replacementHomEquiv_mk q r (q ≫ a ≫ r)).trans hc

/-- Both-variable naturality retains the actual squares between weak replacement legs. -/
theorem replacementHomEquiv_natural
    {QK K L RL QK' K' L' RL' : SSet.{u}}
    (q : QK ⟶ K) (r : L ⟶ RL) (q' : QK' ⟶ K') (r' : L' ⟶ RL')
    [WeakEquivalence q] [WeakEquivalence r] [WeakEquivalence q'] [WeakEquivalence r']
    [SSet.KanComplex RL] [SSet.KanComplex RL']
    (p : QK' ⟶ QK) (a : K' ⟶ K) (b : L ⟶ L') (t : RL ⟶ RL')
    (hq : p ≫ q = q' ≫ a) (hr : r ≫ t = b ≫ r') (c : SSet.π₀ ((ihom QK).obj RL)) :
    replacementHomEquiv q' r'
        (SSet.mapπ₀ ((ihom QK').map t) (SSet.mapπ₀ ((pre p).app RL) c)) =
      (V).map a ≫ replacementHomEquiv q r c ≫ (V).map b := by
  let qi := QuillenOrdinaryHoReplacement.replacementHoIso q
  let qi' := QuillenOrdinaryHoReplacement.replacementHoIso q'
  let ri := QuillenOrdinaryHoReplacement.replacementHoIso r
  let ri' := QuillenOrdinaryHoReplacement.replacementHoIso r'
  have hs : (V).map p ≫ qi.hom = qi'.hom ≫ (V).map a :=
    ((V).map_comp p q).symm.trans (((V).congr_map hq).trans ((V).map_comp q' a))
  have ht : ri.hom ≫ (V).map t = (V).map b ≫ ri'.hom :=
    ((V).map_comp r t).symm.trans (((V).congr_map hr).trans ((V).map_comp b r'))
  have hsi : qi'.inv ≫ (V).map p = (V).map a ≫ qi.inv := by
    apply (cancel_mono qi.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun h => qi'.inv ≫ h) hs
  have hti : (V).map t ≫ ri'.inv = ri.inv ≫ (V).map b := by
    apply (cancel_epi ri.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun h => h ≫ ri'.inv) ht
  obtain ⟨x, rfl⟩ := c.mk_surjective
  obtain ⟨f, rfl⟩ := (SSet.ihomVertexEquiv QK RL).surjective x
  rw [SSet.mapπ₀_mk, SSet.ihomVertexEquiv_pre_app, SSet.mapπ₀_mk,
    SSet.ihomVertexEquiv_ihom_map, replacementHomEquiv_mk, replacementHomEquiv_mk]
  change qi'.inv ≫ (V).map (p ≫ f ≫ t) ≫ ri'.inv =
    (V).map a ≫ (qi.inv ≫ (V).map f ≫ ri.inv) ≫ (V).map b
  have hm : (V).map (p ≫ f ≫ t) = (V).map p ≫ (V).map f ≫ (V).map t :=
    ((V).map_comp p (f ≫ t)).trans
      (congrArg (fun h => (V).map p ≫ h) ((V).map_comp f t))
  calc
    qi'.inv ≫ (V).map (p ≫ f ≫ t) ≫ ri'.inv =
        (qi'.inv ≫ (V).map p) ≫ ((V).map f ≫ ((V).map t ≫ ri'.inv)) := by
      rw [hm]
      simp only [Category.assoc]
    _ = ((V).map a ≫ qi.inv) ≫ ((V).map f ≫ (ri.inv ≫ (V).map b)) := by
      rw [hsi, hti]
    _ = (V).map a ≫ (qi.inv ≫ (V).map f ≫ ri.inv) ≫ (V).map b := by
      simp only [Category.assoc]

variable {D : Type w} [Category.{v} D]

/-- Any independently fixed scalar Q/R convention gives its actual Ho Hom function. -/
def fixedHomEquiv (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z)))) ≃
      ((V).obj K ⟶ (V).obj (C.obj (op z))) := by
  let _ : WeakEquivalence (e.q.app K) := (weakEquivalence_iff _).mpr (e.q_trivialFibration K).2
  let _ : WeakEquivalence (e.r.app (C.obj (op z))) :=
    (weakEquivalence_iff _).mpr (e.r_trivialCofibration (C.obj (op z))).2
  let _ : SSet.KanComplex (e.R.obj (C.obj (op z))) := by
    change IsFibrant (e.R.obj (C.obj (op z)))
    exact e.R_isFibrant _
  exact replacementHomEquiv (e.q.app K) (e.r.app (C.obj (op z)))

/-- Fixed scalar source naturality keeps the independently chosen Q functor. -/
theorem fixedHomEquiv_source (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D)
    (c : SSet.π₀ ((ihom (e.Q.obj L)).obj (e.R.obj (C.obj (op z))))) :
    fixedHomEquiv z e K C (SSet.mapπ₀ ((pre (e.Q.map k)).app (e.R.obj (C.obj (op z)))) c) =
      (V).map k ≫ fixedHomEquiv z e L C c := by
  let qK : e.Q.obj K ⟶ K := e.q.app K
  let qL : e.Q.obj L ⟶ L := e.q.app L
  let _ : WeakEquivalence qK := (weakEquivalence_iff _).mpr (e.q_trivialFibration K).2
  let _ : WeakEquivalence qL := (weakEquivalence_iff _).mpr (e.q_trivialFibration L).2
  let r : C.obj (op z) ⟶ e.R.obj (C.obj (op z)) := e.r.app (C.obj (op z))
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr (e.r_trivialCofibration _).2
  let _ : SSet.KanComplex (e.R.obj (C.obj (op z))) := by
    change IsFibrant (e.R.obj (C.obj (op z)))
    exact e.R_isFibrant _
  change replacementHomEquiv qK r
      (SSet.mapπ₀ ((pre (e.Q.map k)).app (e.R.obj (C.obj (op z)))) c) =
    (V).map k ≫ replacementHomEquiv qL r c
  have h := replacementHomEquiv_natural qL r qK r
    (e.Q.map k) k (𝟙 (C.obj (op z))) (𝟙 (e.R.obj (C.obj (op z)))) (e.q.naturality k)
    (by simp only [Category.id_comp, Category.comp_id]) c
  let y := SSet.mapπ₀ ((pre (e.Q.map k)).app (e.R.obj (C.obj (op z)))) c
  have hi : SSet.mapπ₀ ((ihom (e.Q.obj K)).map (𝟙 (e.R.obj (C.obj (op z))))) y = y :=
    (congrArg (fun f => SSet.mapπ₀ f y) ((ihom (e.Q.obj K)).map_id _)).trans
      (SSet.mapπ₀_id_apply y)
  exact (congrArg (replacementHomEquiv qK r) hi).symm.trans
    (h.trans ((Category.assoc _ _ _).symm.trans (ho_post_id _)))

/-- Fixed scalar target naturality keeps the original zero component and the fixed R action. -/
theorem fixedHomEquiv_target (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C')
    (c : SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z))))) :
    fixedHomEquiv z e K C'
        (SSet.mapπ₀ ((ihom (e.Q.obj K)).map (e.R.map (f.app (op z)))) c) =
      fixedHomEquiv z e K C c ≫ (V).map (f.app (op z)) := by
  let q : e.Q.obj K ⟶ K := e.q.app K
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (e.q_trivialFibration K).2
  let r : C.obj (op z) ⟶ e.R.obj (C.obj (op z)) := e.r.app (C.obj (op z))
  let r' : C'.obj (op z) ⟶ e.R.obj (C'.obj (op z)) := e.r.app (C'.obj (op z))
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr (e.r_trivialCofibration _).2
  let _ : WeakEquivalence r' := (weakEquivalence_iff _).mpr (e.r_trivialCofibration _).2
  let _ : SSet.KanComplex (e.R.obj (C.obj (op z))) := by
    change IsFibrant (e.R.obj (C.obj (op z)))
    exact e.R_isFibrant _
  let _ : SSet.KanComplex (e.R.obj (C'.obj (op z))) := by
    change IsFibrant (e.R.obj (C'.obj (op z)))
    exact e.R_isFibrant _
  change replacementHomEquiv q r'
      (SSet.mapπ₀ ((ihom (e.Q.obj K)).map (e.R.map (f.app (op z)))) c) =
    replacementHomEquiv q r c ≫ (V).map (f.app (op z))
  have h := replacementHomEquiv_natural q r q r' (𝟙 (e.Q.obj K)) (𝟙 K)
    (f.app (op z)) (e.R.map (f.app (op z)))
    (by simp only [Category.id_comp, Category.comp_id]) (e.r.naturality _).symm c
  have hp : (pre (𝟙 (e.Q.obj K))).app (e.R.obj (C.obj (op z))) =
      𝟙 ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z)))) :=
    NatTrans.congr_app (pre_id (e.Q.obj K)) _
  have hi : SSet.mapπ₀ ((pre (𝟙 (e.Q.obj K))).app (e.R.obj (C.obj (op z)))) c = c :=
    (congrArg (fun f => SSet.mapπ₀ f c) hp).trans (SSet.mapπ₀_id_apply c)
  exact (congrArg (fun d => replacementHomEquiv q r'
    (SSet.mapπ₀ ((ihom (e.Q.obj K)).map (e.R.map (f.app (op z)))) d)) hi).symm.trans
      (h.trans (ho_pre_id _))

variable [Small.{u} D] [LocallySmall.{u} D] {I : Type i} [Small.{u} I]

/-- The proved evaluated Q/R legs interpret transferred scalar components in the same Ho. -/
def transferredHomEquiv (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) :
    SSet.π₀ (TransferredCoreReplacements.mappingModel S z K C) ≃
      ((V).obj K ⟶ (V).obj (C.obj (op z))) := by
  let q : (TransferredCoreReplacements.qReplacement S z).obj K ⟶ K :=
    (TransferredCoreReplacements.qCounit S z).app K
  let r : C.obj (op z) ⟶ (TransferredCoreReplacements.rReplacement S z).obj C :=
    (TransferredCoreReplacements.rUnit S z).app C
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.qCounit_trivialFibration S hz K).2
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.rUnit_trivialCofibration S z C hC).2
  let _ : SSet.KanComplex ((TransferredCoreReplacements.rReplacement S z).obj C) :=
    TransferredCoreReplacements.rReplacement_isKan S hz C
  exact replacementHomEquiv q r

/-- The transferred representative of a scalar map has the image of precisely that map. -/
theorem transferredHomEquiv_lift (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) (a : K ⟶ C.obj (op z)) :
    transferredHomEquiv S hz K C hC
        (SSet.π₀.mk (SSet.ihomVertexEquiv ((TransferredCoreReplacements.qReplacement S z).obj K)
          ((TransferredCoreReplacements.rReplacement S z).obj C)
          ((TransferredCoreReplacements.qCounit S z).app K ≫ a ≫
            (TransferredCoreReplacements.rUnit S z).app C))) = (V).map a := by
  let q := (TransferredCoreReplacements.qCounit S z).app K
  let r := (TransferredCoreReplacements.rUnit S z).app C
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.qCounit_trivialFibration S hz K).2
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.rUnit_trivialCofibration S z C hC).2
  let _ : SSet.KanComplex ((TransferredCoreReplacements.rReplacement S z).obj C) :=
    TransferredCoreReplacements.rReplacement_isKan S hz C
  exact replacementHomEquiv_lift q r a

/-- The entire zero-projection component function commutes with the constructed core Ho adjunct. -/
theorem comparison_piZero_commutes (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))).obj C)) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    transferredHomEquiv S hz K C hC
        (SSet.mapπ₀ (BaselineConstantCoreComparison.comparison S z K C) c) =
      CoreDerivedAdjunction.homEquiv S hz K C hC
        (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
          ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C c) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let G := (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let _ : IsCofibrant G := d.all_cofibrant G
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let M := innerHom ((localQ S).obj G) ((localR S).obj C)
  let c' : SSet.π₀ M := c
  let E : SSet.π₀ M ≃ (H.obj G ⟶ H.obj C) :=
    OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S G C
  let A : (H.obj G ⟶ H.obj C) ≃ ((V).obj K ⟶ (V).obj (C.obj (op z))) :=
    CoreDerivedAdjunction.homEquiv S hz K C hC
  let p : M ⟶ TransferredCoreReplacements.mappingModel S z K C :=
    BaselineConstantCoreComparison.comparison S z K C
  change transferredHomEquiv S hz K C hC (SSet.mapπ₀ p c') = A (E c')
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization H G C (E c')
  have he : E (SSet.π₀.mk (CoreUniversalProperty.derivedPoint S K C f)) = H.map f :=
    CoreUniversalProperty.derivedPoint_ho S K C f
  have hc : c' = SSet.π₀.mk (CoreUniversalProperty.derivedPoint S K C f) :=
    E.injective (hf.symm.trans he.symm)
  let a := ((BaselineConstantCoreComparison.unit (D := D)).app K).app (op z) ≫ f.app (op z)
  have hp : SSet.mapπ₀ p c' = SSet.π₀.mk
      (SSet.ihomVertexEquiv ((TransferredCoreReplacements.qReplacement S z).obj K)
        ((TransferredCoreReplacements.rReplacement S z).obj C)
        ((TransferredCoreReplacements.qCounit S z).app K ≫ a ≫
          (TransferredCoreReplacements.rUnit S z).app C)) :=
    (congrArg (SSet.mapπ₀ p) hc).trans
      ((SSet.mapπ₀_mk p _).trans
        (congrArg SSet.π₀.mk (CoreUniversalProperty.comparison_derivedPoint S z K C f)))
  have ha : A (E c') = (V).map a :=
    (congrArg A hf.symm).trans (CoreDerivedAdjunction.homEquiv_map S hz K C hC f)
  exact (congrArg (transferredHomEquiv S hz K C hC) hp).trans
    ((transferredHomEquiv_lift S hz K C hC a).trans ha.symm)

/-- The common scalar source has its actual composite counit to K. -/
def commonCounit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) :
    (ScalarCoreReplacementSpans.commonSource S z e).obj K ⟶ K :=
  (ScalarCoreReplacementSpans.sourceLeft S z e).app K ≫
    (TransferredCoreReplacements.qCounit S z).app K

/-- The common scalar target has the actual fixed-unit/right-inclusion map from the zero core. -/
def commonUnit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D) :
    C.obj (op z) ⟶ (ScalarCoreReplacementSpans.commonTarget S z e).obj C :=
  e.r.app (C.obj (op z)) ≫ (ScalarCoreReplacementSpans.targetRight S z e).app C

private theorem commonCounit_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) :
    WeakEquivalence (commonCounit S z e K) :=
  (weakEquivalence_iff _).mpr
    (SSet.realizationWeakEquivalences.comp_mem _ _
      (ScalarCoreReplacementSpans.sourceLeft_trivialFibration S z e K).2
      (TransferredCoreReplacements.qCounit_trivialFibration S hz K).2)

private theorem commonUnit_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) : WeakEquivalence (commonUnit S z e C) :=
  (weakEquivalence_iff _).mpr
    (SSet.realizationWeakEquivalences.comp_mem _ _ (e.r_trivialCofibration _).2
      (ScalarCoreReplacementSpans.targetRight_trivialCofibration S z e C hC).2)

/-- The common scalar presentation has the same actual Kan–Quillen Hom interpretation. -/
def commonHomEquiv (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D} (hz : IsTerminal z)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    SSet.π₀ (((ScalarCoreReplacementSpans.commonMapping S z e).obj (op K)).obj C) ≃
      ((V).obj K ⟶ (V).obj (C.obj (op z))) := by
  let _ := commonCounit_weak S hz e K
  let _ := commonUnit_weak S z e C hC
  let _ : SSet.KanComplex ((ScalarCoreReplacementSpans.commonTarget S z e).obj C) := by
    change IsFibrant ((ScalarCoreReplacementSpans.commonTarget S z e).obj C)
    exact ScalarCoreReplacementSpans.commonTarget_isFibrant S z e C
  exact replacementHomEquiv (commonCounit S z e K) (commonUnit S z e C)

/-- The actual transferred-to-common leg preserves the entire represented Ho function. -/
theorem transferredToCommon_ho (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ (TransferredCoreReplacements.mappingModel S z K C)) :
    commonHomEquiv S hz e K C hC
        (SSet.mapπ₀ (((ScalarCoreReplacementSpans.transferredToCommon S z e).app (op K)).app C) c) =
      transferredHomEquiv S hz K C hC c := by
  let q : (TransferredCoreReplacements.qReplacement S z).obj K ⟶ K :=
    (TransferredCoreReplacements.qCounit S z).app K
  let r : C.obj (op z) ⟶ (TransferredCoreReplacements.rReplacement S z).obj C :=
    (TransferredCoreReplacements.rUnit S z).app C
  let c' : SSet.π₀ ((ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).obj
      ((TransferredCoreReplacements.rReplacement S z).obj C)) := c
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.qCounit_trivialFibration S hz K).2
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr
    (TransferredCoreReplacements.rUnit_trivialCofibration S z C hC).2
  let _ := commonCounit_weak S hz e K
  let _ := commonUnit_weak S z e C hC
  let _ : SSet.KanComplex ((TransferredCoreReplacements.rReplacement S z).obj C) :=
    TransferredCoreReplacements.rReplacement_isKan S hz C
  let _ : SSet.KanComplex ((ScalarCoreReplacementSpans.commonTarget S z e).obj C) := by
    change IsFibrant ((ScalarCoreReplacementSpans.commonTarget S z e).obj C)
    exact ScalarCoreReplacementSpans.commonTarget_isFibrant S z e C
  have h := replacementHomEquiv_natural q r (commonCounit S z e K) (commonUnit S z e C)
    ((ScalarCoreReplacementSpans.sourceLeft S z e).app K) (𝟙 K) (𝟙 (C.obj (op z)))
    ((ScalarCoreReplacementSpans.targetLeft S z e).app C)
    (by exact (Category.comp_id _).symm)
    ((ScalarCoreReplacementSpans.commonTarget_square S z e C).trans (Category.id_comp _).symm) c'
  change replacementHomEquiv (commonCounit S z e K) (commonUnit S z e C)
      (SSet.mapπ₀ ((pre ((ScalarCoreReplacementSpans.sourceLeft S z e).app K)).app
        ((TransferredCoreReplacements.rReplacement S z).obj C) ≫
          (ihom ((ScalarCoreReplacementSpans.commonSource S z e).obj K)).map
            ((ScalarCoreReplacementSpans.targetLeft S z e).app C)) c') = replacementHomEquiv q r c'
  rw [SSet.mapπ₀_comp_apply]
  exact h.trans ((ho_pre_id _).trans (ho_post_id _))

/-- The actual fixed-to-common leg preserves the same entire scalar Ho function. -/
theorem fixedToCommon_ho (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z))))) :
    commonHomEquiv S hz e K C hC
        (SSet.mapπ₀ (((ScalarCoreReplacementSpans.fixedToCommon S z e).app (op K)).app C) c) =
      fixedHomEquiv z e K C c := by
  let q : e.Q.obj K ⟶ K := e.q.app K
  let r : C.obj (op z) ⟶ e.R.obj (C.obj (op z)) := e.r.app (C.obj (op z))
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (e.q_trivialFibration K).2
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr (e.r_trivialCofibration _).2
  let _ := commonCounit_weak S hz e K
  let _ := commonUnit_weak S z e C hC
  let _ : SSet.KanComplex (e.R.obj (C.obj (op z))) := by
    change IsFibrant (e.R.obj (C.obj (op z)))
    exact e.R_isFibrant _
  let _ : SSet.KanComplex ((ScalarCoreReplacementSpans.commonTarget S z e).obj C) := by
    change IsFibrant ((ScalarCoreReplacementSpans.commonTarget S z e).obj C)
    exact ScalarCoreReplacementSpans.commonTarget_isFibrant S z e C
  have h := replacementHomEquiv_natural q r (commonCounit S z e K) (commonUnit S z e C)
    ((ScalarCoreReplacementSpans.sourceRight S z e).app K) (𝟙 K) (𝟙 (C.obj (op z)))
    ((ScalarCoreReplacementSpans.targetRight S z e).app C)
    ((ScalarCoreReplacementSpans.commonSource_square S z e K).symm.trans (Category.comp_id _).symm)
    (by exact (Category.id_comp _).symm) c
  change replacementHomEquiv (commonCounit S z e K) (commonUnit S z e C)
      (SSet.mapπ₀ ((pre ((ScalarCoreReplacementSpans.sourceRight S z e).app K)).app
        (e.R.obj (C.obj (op z))) ≫
          (ihom ((ScalarCoreReplacementSpans.commonSource S z e).obj K)).map
            ((ScalarCoreReplacementSpans.targetRight S z e).app C)) c) = replacementHomEquiv q r c
  rw [SSet.mapπ₀_comp_apply]
  exact h.trans ((ho_pre_id _).trans (ho_post_id _))

/-- The original core Hom bijection takes values in any independently fixed scalar presentation. -/
def universalHomEquiv (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D} (hz : IsTerminal z)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))).obj C) ≃
    SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z)))) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  exact (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
    ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C).trans
      ((CoreDerivedAdjunction.homEquiv S hz K C hC).trans (fixedHomEquiv z e K C).symm)

/-- The component comparison agrees with the constructed original core Ho adjunct. -/
theorem universalHomEquiv_ho (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))).obj C)) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    fixedHomEquiv z e K C (universalHomEquiv S hz e K C hC c) =
      CoreDerivedAdjunction.homEquiv S hz K C hC
        (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
          ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C c) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  exact (fixedHomEquiv z e K C).apply_symm_apply _

/-- The proved component bijection is bound to the actual common-source/common-target cospan. -/
theorem universalHomEquiv_triangle (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))).obj C)) :
    SSet.mapπ₀ (((CoreUniversalMapping.toCommon S z e).app (op K)).app C) c =
      SSet.mapπ₀ (((ScalarCoreReplacementSpans.fixedToCommon S z e).app (op K)).app C)
        (universalHomEquiv S hz e K C hC c) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let p := BaselineConstantCoreComparison.comparison S z K C
  let l := ((ScalarCoreReplacementSpans.transferredToCommon S z e).app (op K)).app C
  let r := ((ScalarCoreReplacementSpans.fixedToCommon S z e).app (op K)).app C
  let a := CoreDerivedAdjunction.homEquiv S hz K C hC
    (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
      ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C c)
  have hl : commonHomEquiv S hz e K C hC (SSet.mapπ₀ (p ≫ l) c) = a :=
    (congrArg (commonHomEquiv S hz e K C hC) (SSet.mapπ₀_comp_apply p l c)).trans
      ((transferredToCommon_ho S hz e K C hC (SSet.mapπ₀ p c)).trans
        (comparison_piZero_commutes S hz K C hC c))
  have hr : commonHomEquiv S hz e K C hC
      (SSet.mapπ₀ r (universalHomEquiv S hz e K C hC c)) = a :=
    (fixedToCommon_ho S hz e K C hC _).trans (universalHomEquiv_ho S hz e K C hC c)
  exact (commonHomEquiv S hz e K C hC).injective (hl.trans hr.symm)

/-- The universal component bijection is natural in the original scalar source variable. -/
theorem universalHomEquiv_source (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C)
    (c : SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj L))).obj C)) :
    universalHomEquiv S hz e K C hC
        (SSet.mapπ₀ (localDerivedPrecomp S
          ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) C) c) =
      SSet.mapπ₀ ((pre (e.Q.map k)).app (e.R.obj (C.obj (op z))))
        (universalHomEquiv S hz e L C hC c) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let G := BaselineConstantCoreComparison.constantReplacement (D := D)
  let E := OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S (G.obj L) C
  let A := CoreDerivedAdjunction.homEquiv S hz K C hC
  have h₁ := universalHomEquiv_ho S hz e K C hC
    (SSet.mapπ₀ (localDerivedPrecomp S (G.map k) C) c)
  have h₂ := congrArg A
    (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv_source S (G.map k) C c)
  have h₃ := CoreDerivedAdjunction.homEquiv_source S hz k C hC (E c)
  have h₄ := congrArg (fun h => (V).map k ≫ h)
    (universalHomEquiv_ho S hz e L C hC c).symm
  have h₅ := (fixedHomEquiv_source z e k C (universalHomEquiv S hz e L C hC c)).symm
  apply (fixedHomEquiv z e K C).injective
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- The universal component bijection is natural in every actual local-fibrant target map. -/
theorem universalHomEquiv_target (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    {C C' : SimplicialPresheaf.{u} D} (hC : isOriginalLocalFibrant S C)
    (hC' : isOriginalLocalFibrant S C') (f : C ⟶ C')
    (c : SSet.π₀ (((localDerivedEnd S).obj
      (op ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))).obj C)) :
    universalHomEquiv S hz e K C' hC'
        (SSet.mapπ₀ (localDerivedPostcomp S
          ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) f) c) =
      SSet.mapπ₀ ((ihom (e.Q.obj K)).map (e.R.map (f.app (op z))))
        (universalHomEquiv S hz e K C hC c) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let G := (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K
  let E := OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S G C
  let A := CoreDerivedAdjunction.homEquiv S hz K C' hC'
  have h₁ := universalHomEquiv_ho S hz e K C' hC'
    (SSet.mapπ₀ (localDerivedPostcomp S G f) c)
  have h₂ := congrArg A
    (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv_target S G f c)
  have h₃ := CoreDerivedAdjunction.homEquiv_target S hz K hC hC' (E c) f
  have h₄ := congrArg (fun h => h ≫ (V).map (f.app (op z)))
    (universalHomEquiv_ho S hz e K C hC c).symm
  have h₅ := (fixedHomEquiv_target z e K f (universalHomEquiv S hz e K C hC c)).symm
  apply (fixedHomEquiv z e K C').injective
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end SimplicialPresheaf.CoreMappingComponents

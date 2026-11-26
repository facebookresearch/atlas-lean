/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels

/-!
# Crystalline Frobenius products

The source comparison and the Cartier Frobenius and Verschiebung maps satisfy
both multiplication-by-p identities on the full crystalline modules.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
Berthelot, Breen and Messing, *Théorie de Dieudonné cristalline II*;
Scholze and Weinstein, *Moduli of p-divisible groups*.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps
open PDivisibleGroupMaps PDivisiblePointFunctors
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open FullPDCrystallineTests FullPDCrystallineSourceMaps
open PDCrystallineFrobeniusMaps CrystallineFrobeniusSourceComparison
open NormalizedDieudonneFrobenius DieudonneFrobeniusProjectionModels
open MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat
open scoped CategoryTheory.MonObj

private instance multiply_group (S : Scheme.{0}) (X : Over S) [GrpObj X]
    [IsCommMonObj X] (k : ℕ) : IsMonHom (multiply S X k) := by
  change IsMonHom ((𝟙 X) ^ k)
  have h : ((𝟙 (Mon.mk X)) ^ k).hom = (𝟙 X) ^ k := by
    simp
  rw [← h]
  infer_instance

private theorem multiply_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) :
    multiply (Spec (.of R)) (G.levels.obj 0) p = 𝟙 _ := by
  let e := Classical.choice G.zero
  apply (cancel_mono e.hom).mp
  exact CartesianMonoidalCategory.toUnit_unique _ _

private theorem dual_multiply (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G) (n : ℕ) :
    (D.finiteIso n).hom ≫ (cartierDualFunctor R).map
        (finiteGroupHom (multiply (Spec (.of R)) (G.levels.obj n) p)).op =
      finiteGroupHom (multiply (Spec (.of R)) (D.group.levels.obj n) p) ≫
        (D.finiteIso n).hom := by
  cases n with
  | zero =>
    have hz (H : PDivisibleGroup (Spec (.of R)) p) :
        finiteGroupHom (multiply (Spec (.of R)) (H.levels.obj 0) p) =
          𝟙 (finiteLevel p R H 0) := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Grp.hom_ext
      change multiply (Spec (.of R)) (H.levels.obj 0) p = 𝟙 _
      exact multiply_zero p R H
    rw [hz G, hz D.group]
    simp
  | succ n =>
    rw [Nat.add_comm n 1]
    have hG : finiteGroupHom (multiply (Spec (.of R)) (G.levels.obj (1 + n)) p) =
        finiteDivision (G := G) 1 n ≫ finiteInclusion (G := G) n (1 + n)
          (Nat.le_add_left n 1) := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Grp.hom_ext
      change multiply (Spec (.of R)) (G.levels.obj (1 + n)) p =
        G.divide 1 n ≫ G.levels.map (homOfLE (Nat.le_add_left n 1))
      simpa only [pow_one] using (G.factor 1 n).symm
    have hD : finiteGroupHom (multiply (Spec (.of R)) (D.group.levels.obj (1 + n)) p) =
        finiteDivision (G := D.group) 1 n ≫ finiteInclusion (G := D.group) n (1 + n)
          (Nat.le_add_left n 1) := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Grp.hom_ext
      change multiply (Spec (.of R)) (D.group.levels.obj (1 + n)) p =
        D.group.divide 1 n ≫ D.group.levels.map (homOfLE (Nat.le_add_left n 1))
      simpa only [pow_one] using (D.group.factor 1 n).symm
    have hi := D.inclusions n (1 + n) (Nat.le_add_left n 1)
    have hd := D.divisions 1 n
    have hb : finiteDivisionBetween (G := G) n (1 + n) (Nat.le_add_left n 1) =
        finiteDivision (G := G) 1 n := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Grp.hom_ext
      change divisionBetween (G := G) n (1 + n) (Nat.le_add_left n 1) = G.divide 1 n
      have aux (k : ℕ) (hk : k = 1) (he : 1 + n = k + n) :
          G.levels.map (homOfLE he.le) ≫ G.divide k n = G.divide 1 n := by
        subst k
        have hh : homOfLE he.le = 𝟙 (1 + n) := Subsingleton.elim _ _
        rw [hh, G.levels.map_id, Category.id_comp]
      exact aux _ (Nat.add_sub_cancel 1 n) (Nat.sub_add_cancel (Nat.le_add_left n 1)).symm
    dsimp only [dualTransition] at hi
    rw [hb] at hi
    dsimp only [dualDivision] at hd
    rw [hG, hD, op_comp, Functor.map_comp]
    rw [← Category.assoc, ← hd, Category.assoc, ← hi, ← Category.assoc]

private theorem dual_product (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivisibleGroup (Spec (.of R)) p) (DG : CartierDualTower p R G)
    (DH : CartierDualTower p R H) (f : PDivisibleGroupMaps.Hom p G H)
    (g : PDivisibleGroupMaps.Hom p H G) (df : DualHom p R f DG DH)
    (dg : DualHom p R g DH DG)
    (h : ∀ n, f.levels.app n ≫ g.levels.app n =
      multiply (Spec (.of R)) (G.levels.obj n) p) (n : ℕ) :
    dg.hom.levels.app n ≫ df.hom.levels.app n =
      multiply (Spec (.of R)) (DG.group.levels.obj n) p := by
  have hb : finiteMap p R f n ≫ finiteMap p R g n =
      finiteGroupHom (multiply (Spec (.of R)) (G.levels.obj n) p) := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Grp.hom_ext
    change f.levels.app n ≫ g.levels.app n = _
    exact h n
  have hc : finiteMap p R dg.hom n ≫ finiteMap p R df.hom n =
      finiteGroupHom (multiply (Spec (.of R)) (DG.group.levels.obj n) p) := by
    apply (cancel_mono (DG.finiteIso n).hom).mp
    rw [Category.assoc, df.finite n, ← Category.assoc, dg.finite n]
    dsimp only [finiteDualMap]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, hb,
      dual_multiply p R G DG n]
  exact congrArg (fun u => (finiteForget R).map u) hc

private def pointsPower {S : Scheme.{0}} (p : ℕ) [Fact p.Prime]
    (G : PDivisibleGroup S p) (k : ℕ) : pointwisePoints (p := p) (S := S) G ⟶
      pointwisePoints (p := p) (S := S) G where
  app T := CommGrpCat.ofHom (powMonoidHom k)
  naturality {T U} f := by
    ext x
    change ((pointwisePoints (p := p) (S := S) G).map f x) ^ k =
      (pointwisePoints (p := p) (S := S) G).map f (x ^ k)
    exact (((pointwisePoints (p := p) (S := S) G).map f).hom.map_pow x k).symm

private theorem point_product {S : Scheme.{0}} (p : ℕ) [Fact p.Prime]
    (G H : PDivisibleGroup S p) (f : Hom p G H) (g : Hom p H G) (k : ℕ)
    (h : ∀ n, f.levels.app n ≫ g.levels.app n = multiply S (G.levels.obj n) k) :
    pointMap f ≫ pointMap g = pointsPower p G k := by
  apply colimit.hom_ext
  intro n
  change levelInclusion (p := p) (S := S) G n ≫ (pointMap f ≫ pointMap g) =
    levelInclusion (p := p) (S := S) G n ≫ _
  rw [← Category.assoc, pointMap_finite, Category.assoc, pointMap_finite, ← Category.assoc]
  apply NatTrans.ext
  funext T
  ext x
  change (levelInclusion (p := p) (S := S) G n).app T ((x ≫ f.levels.app n) ≫ g.levels.app n) =
    ((levelInclusion (p := p) (S := S) G n).app T x) ^ k
  rw [Category.assoc, h n, multiply, MonObj.comp_pow, Category.comp_id]
  exact ((levelInclusion (p := p) (S := S) G n).app T).hom.map_pow x k

open FullPDCrystallineSheaves in
private theorem group_product (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)
    (G H : PDivisibleGroup S.left p) (f : Hom p G H) (g : Hom p H G) (k : ℕ)
    (h : ∀ n, f.levels.app n ≫ g.levels.app n = multiply S.left (G.levels.obj n) k) :
    groupSheafMap p A S f ≫ groupSheafMap p A S g = k • 𝟙 _ := by
  have hp : groupPresheafMap p A S f ≫ groupPresheafMap p A S g = k • 𝟙 _ := by
    change CategoryTheory.Functor.whiskerLeft (reductions p A S).op
      (CategoryTheory.Functor.whiskerRight (pointMap f)
        (CommGrpCat.toAddCommGrp ⋙ liftAbelianGroups)) ≫
      CategoryTheory.Functor.whiskerLeft (reductions p A S).op
      (CategoryTheory.Functor.whiskerRight (pointMap g)
        (CommGrpCat.toAddCommGrp ⋙ liftAbelianGroups)) = _
    rw [← CategoryTheory.Functor.whiskerLeft_comp, ← CategoryTheory.Functor.whiskerRight_comp,
      point_product p G H f g k h]
    apply NatTrans.ext
    funext T
    ext x
    rfl
  rw [groupSheafMap, groupSheafMap, ← CategoryTheory.Functor.map_comp, hp,
    CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

private theorem ext_source_product {C : Type 1} [Category.{0} C]
    (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{1})
    (F G : Sheaf J AddCommGrpCat.{1}) (f : F ⟶ G) (g : G ⟶ F) (k n : ℕ)
    (h : f ≫ g = k • 𝟙 F) :
    MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap J O g n ≫
      MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap J O f n =
      k • 𝟙 _ := by
  apply PresheafOfModules.hom_ext
  intro P
  let : (J.overPullback AddCommGrpCat.{1} P.unop).Additive := {
    map_add := by
      intro X Y a b
      apply Sheaf.hom_ext
      ext U x
      rfl }
  change (PresheafOfModules.evaluation _ P).map
      (MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap J O g n ≫
        MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap J O f n) =
    (PresheafOfModules.evaluation _ P).map (k • 𝟙 _)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  dsimp only [PresheafOfModules.evaluation_map,
    MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap,
    MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.localExtMap]
  change (Ext.mk₀ ((J.overPullback AddCommGrpCat.{1} P.unop).map f)).comp
    ((Ext.mk₀ ((J.overPullback AddCommGrpCat.{1} P.unop).map g)).comp e (Nat.zero_add n))
      (Nat.zero_add n) = k • e
  rw [Ext.mk₀_comp_mk₀_assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  clear h
  induction k with
  | zero => simp
  | succ k ih => simp [succ_nsmul, Ext.mk₀_add, Ext.add_comp, ih]

private instance moduleSheafification_additive {C : Type 1} [Category.{0} C]
    (J : GrothendieckTopology C) (O : Sheaf J RingCat.{1}) :
    (PresheafOfModules.sheafification.{1} (𝟙 O.obj)).Additive := by
  let : (PresheafOfModules.sheafification.{1} (𝟙 O.obj) ⋙
      SheafOfModules.toSheaf O).Additive :=
    CategoryTheory.Functor.additive_of_iso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 O.obj)).symm
  exact CategoryTheory.Functor.additive_of_comp_faithful _ (SheafOfModules.toSheaf O)

open FullPDCrystallineSheaves in
private theorem native_source_product (p : ℕ) [Fact p.Prime] (A : PDBase)
    (S : Over A.reduction) (F G : CoefficientSheaves p A S) (f : F ⟶ G) (g : G ⟶ F)
    (k n : ℕ) (h : f ≫ g = k • 𝟙 _) :
    nativeSourceMap p A S g n ≫ nativeSourceMap p A S f n = k • 𝟙 _ := by
  let T := PresheafOfModules.sheafification
    (𝟙 (FullPDCrystallineExtModules.coefficientRing p A S).obj) ⋙
    SheafOfModules.forget (FullPDCrystallineExtModules.coefficientRing p A S) ⋙
      PresheafOfModules.restrictScalars (FullPDCrystallineExtModules.coefficientUnit p A S)
  change T.map (MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap
      (topology p A S) (structureRingSheaf p A S) g n) ≫
    T.map (MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap
      (topology p A S) (structureRingSheaf p A S) f n) = k • 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, ext_source_product _ _ F G f g k n h,
    CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

private theorem full_product (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (G H : PDivisibleGroup (Spec (.of R)) p) (DG : CartierDualTower p R G)
    (DH : CartierDualTower p R H) (f : PDivisibleGroupMaps.Hom p G H)
    (g : PDivisibleGroupMaps.Hom p H G) (df : DualHom p R f DG DH)
    (dg : DualHom p R g DH DG)
    (h : ∀ n, f.levels.app n ≫ g.levels.app n =
      multiply (Spec (.of R)) (G.levels.obj n) p) :
    Maps.fullMap p R A E DG DH f df ≫ Maps.fullMap p R A E DH DG g dg =
      p • 𝟙 (fullNativeModule p R A E G DG) := by
  exact native_source_product p (hullPDBase p R A) (baseScheme p R A E)
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) DG.group)
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) DH.group)
    (groupSheafMap p (hullPDBase p R A) (baseScheme p R A E) dg.hom)
    (groupSheafMap p (hullPDBase p R A) (baseScheme p R A E) df.hom) p 1
    (group_product p (hullPDBase p R A) (baseScheme p R A E) DG.group DH.group
      dg.hom df.hom p (dual_product p R G H DG DH f g df dg h))

/-- The crystalline Frobenius and Verschiebung of a $p$-divisible group over a semiperfect ring
compose to $p$: let $p$ be a prime, $R$ a semiperfect ring of characteristic $p$, $A$ the universal
PD hull of $W(R^\flat) \to R$ with its identification of residue ring with $R$, $F_0$ a PD
endomorphism of $A$ lifting the Witt vector Frobenius, and φ its completion on $A_{\mathrm{cris}}$,
with divided powers on the finite stages of $A_{\mathrm{cris}}$ compatible with φ (`PDStages`,
`Compatibility`); let $G$ be a $p$-divisible group over $R$ with a Cartier dual tower and Frobenius
and Verschiebung maps on it (`CartierFrobeniusVerschiebung`), and $N$ a comparison of the
Frobenius-reindexed crystalline Dieudonné module of $G$ with that of its Frobenius twist
(`SourceComparison`). Let $F$, from the Frobenius-reindexed module to the module of $G$, be $N$
followed by the map induced by the Verschiebung of $G$, and $V$, in the other direction, the map
induced by the Frobenius of $G$ followed by $N^{-1}$. Then $F \circ V = p$ and $V \circ F = p$
(`FullCrystalProducts`). -/
public theorem fullCrystallineFrobeniusProducts
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (hR : IsSemiperfect p R) (A : UniversalEnvelope p R) (E : ResidueIdentification A)
    (P : PDStages p R A E) (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
    (C : Compatibility p R A E P F₀ φ) (G : PDivisibleGroup (Spec (.of R)) p)
    (D : CartierDualTower p R G) (Q : CartierFrobeniusVerschiebung p R G D)
    (N : SourceComparison p R A E P F₀ φ C G D Q) :
    FullCrystalProducts p R A E P F₀ φ C G D Q N
    := by
  have _ := hR
  have hvf := full_product p R A E G Q.source.twist.group D Q.dualTwist
    (frobeniusHom p R G Q.source) (verschiebungHom p R G Q.source)
    Q.dualFrobenius Q.dualVerschiebung Q.source.first_product
  have hfv := full_product p R A E Q.source.twist.group G Q.dualTwist D
    (verschiebungHom p R G Q.source) (frobeniusHom p R G Q.source)
    Q.dualVerschiebung Q.dualFrobenius Q.source.second_product
  constructor
  · simpa only [crystallineVerschiebung, crystallineFrobenius, Category.assoc,
      Iso.inv_hom_id_assoc] using hvf
  · calc
      _ = N.moduleIso.hom ≫
          (Maps.fullMap p R A E Q.dualTwist D (verschiebungHom p R G Q.source)
            Q.dualVerschiebung ≫
          Maps.fullMap p R A E D Q.dualTwist (frobeniusHom p R G Q.source)
            Q.dualFrobenius) ≫ N.moduleIso.inv := by
        simp only [crystallineFrobenius, crystallineVerschiebung, Category.assoc]
      _ = _ := by
        rw [hfv, Preadditive.nsmul_comp, Category.id_comp,
          Preadditive.comp_nsmul, Iso.hom_inv_id]

end WantedExt.AlgebraicGeometry.CrystallineFrobeniusNormalization

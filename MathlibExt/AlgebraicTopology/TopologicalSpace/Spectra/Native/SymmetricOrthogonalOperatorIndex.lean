/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalSphereCoefficientComparison
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalTensor
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceGeneratorRecovery
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerCoefficient

/-!
# Actual maps between native spectrum operator indices

The symmetric-to-orthogonal integrand map uses the full original finite-bijection
Hom map and the original ordered sphere comparison. Its target is the actual
orthogonal weighted coend, with every continuous isometry parameter retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory
open BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.SpectrumIndexMaps

attribute [local instance] OrthogonalIndex.enrichedCategory
  OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual integrand map into the complete original orthogonal operator Hom. -/
def symmetricOrthogonalGenerator (n k a : I) :
    PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ k) ⊗
      PointedCGWH.sphereSequence.{u, v}.functor.obj a ⟶
        OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
  (symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
    (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom) ≫
      OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len a.of.len

/-- The original full fixed-right tensor action commutes with the native index inclusion. -/
theorem symmetricOrthogonalFixedRight (a b n : I) :
    (ρ_ (PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⟶ b))).inv ≫
      (𝟙 _ ⊗ₘ eId PointedCGWH.{u, v}
        (PointedCGWH.copowerIndexObj.{u, v, 0} I n)) ≫
      PointedCGWH.copowerTensorHom.{u, v, 0} I a b n n ≫
      symmetricOrthogonalHomMap.{u, v} (a ⊗ n) (b ⊗ n) =
    symmetricOrthogonalHomMap.{u, v} a b ≫
      (ρ_ (OrthogonalIndex.hom.{u, v} a.of.len b.of.len)).inv ≫
      (𝟙 _ ⊗ₘ eId PointedCGWH.{u, v} (n.of.len : OrthogonalIndex)) ≫
      OrthogonalIndex.tensorMap.{u, v} a.of.len b.of.len n.of.len n.of.len := by
  let H := (PointedCGWH.copowerIndexObj.{u, v, 0} I a ⟶[PointedCGWH.{u, v}]
    PointedCGWH.copowerIndexObj.{u, v, 0} I b)
  let K := OrthogonalIndex.hom.{u, v} a.of.len b.of.len
  let f : H ⟶ K := symmetricOrthogonalHomMap.{u, v} a b
  let e : 𝟙_ PointedCGWH.{u, v} ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (n ⟶ n) :=
    eId PointedCGWH.{u, v} (PointedCGWH.copowerIndexObj.{u, v, 0} I n)
  let e' : 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} n.of.len n.of.len :=
    eId PointedCGWH.{u, v} (n.of.len : OrthogonalIndex)
  let T := OrthogonalIndex.tensorMap.{u, v} a.of.len b.of.len n.of.len n.of.len
  let j : PointedCGWH.basedDiscreteObj.{u, v, 0} (n ⟶ n) ⟶
      OrthogonalIndex.hom.{u, v} n.of.len n.of.len := symmetricOrthogonalHomMap.{u, v} n n
  have hTensor : (𝟙 H ⊗ₘ e) ≫ (f ⊗ₘ j) = f ⊗ₘ e' := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => f ⊗ₘ z) (symmetricOrthogonalHomMap_id.{u, v} n)
  have hUnit : (ρ_ H).inv ≫ (f ⊗ₘ e') =
      f ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ e') := by
    rw [rightUnitor_inv_naturality_assoc]
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have ht := symmetricOrthogonalHomMap_tensor.{u, v} a b n n
  have he := congrArg (fun q => (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫ q) ht
  apply he.trans
  change (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫
      (f ⊗ₘ j) ≫ T =
    f ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ e') ≫ T
  simpa only [Category.assoc] using congrArg (fun z => z ≫ T)
    ((congrArg (fun z => (ρ_ H).inv ≫ z) hTensor).trans hUnit)

/-- The entire contravariant operator weight action respects the original inclusion. -/
theorem symmetricOrthogonalWeight (n k a b : I) :
    MonoidalClosed.uncurry
      ((Enriched.SphereOperator.weight
        (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k)).map
        (op ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj b))
        (op ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a))) ≫
      symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k =
    (symmetricOrthogonalHomMap.{u, v} (b ⊗ n) k ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} a b) ≫
      MonoidalClosed.uncurry
        ((OrthogonalOperatorIndex.weight.{u, v} n.of.len k.of.len).map
          (op (b.of.len : OrthogonalIndex)) (op (a.of.len : OrthogonalIndex))) := by
  let V := PointedCGWH.{u, v}
  let SymI := PointedCGWH.CopowerUnderlying.{u, v, 0} I
  let A : SymI := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj a
  let B : SymI := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj b
  let N : SymI := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj n
  let K : SymI := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj k
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let do' := OrthogonalIndex.enrichedMonoidalData.{u, v}
  let Ts := Enriched.SphereOperator.fixedRightTensor ds N
  let To := Enriched.SphereOperator.fixedRightTensor do' (n.of.len : OrthogonalIndex)
  let P : V := (B ⊗ N) ⟶[V] K
  let H : V := A ⟶[V] B
  let Q : V := (A ⊗ N) ⟶[V] (B ⊗ N)
  let P' : V := OrthogonalIndex.hom.{u, v} (b.of.len + n.of.len) k.of.len
  let H' : V := OrthogonalIndex.hom.{u, v} a.of.len b.of.len
  let Q' : V := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) (b.of.len + n.of.len)
  let p : P ⟶ P' := symmetricOrthogonalHomMap.{u, v} (b ⊗ n) k
  let h : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} a b
  let q : Q ⟶ Q' := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) (b ⊗ n)
  let r : ((A ⊗ N) ⟶[V] K) ⟶
      OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len :=
    symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k
  let cs : Q ⊗ P ⟶ ((A ⊗ N) ⟶[V] K) := eComp V (A ⊗ N) (B ⊗ N) K
  let co : Q' ⊗ P' ⟶ OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len :=
    eComp V (a.of.len + n.of.len : OrthogonalIndex)
      (b.of.len + n.of.len : OrthogonalIndex) (k.of.len : OrthogonalIndex)
  let ts : H ⟶ Q := Ts.map A B
  let to' : H' ⟶ Q' := To.map a.of.len b.of.len
  have hc : cs ≫ r = (q ⊗ₘ p) ≫ co :=
    symmetricOrthogonalHomMap_comp.{u, v} (a ⊗ n) (b ⊗ n) k
  have ht : ts ≫ q = h ≫ to' := by
    change (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V N) ≫ ds.tensorMap A B N N ≫ q =
      h ≫ (ρ_ H').inv ≫ (𝟙 H' ⊗ₘ eId V (n.of.len : OrthogonalIndex)) ≫
        do'.tensorMap a.of.len b.of.len n.of.len n.of.len
    exact symmetricOrthogonalFixedRight.{u, v} a b n
  let ws : P ⊗ H ⟶ ((A ⊗ N) ⟶[V] K) := MonoidalClosed.uncurry
    ((Enriched.SphereOperator.weight ds N K).map (op B) (op A))
  let wo : P' ⊗ H' ⟶ OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len :=
    MonoidalClosed.uncurry
      ((Enriched.SphereOperator.weight do' (n.of.len : OrthogonalIndex)
        (k.of.len : OrthogonalIndex)).map (op (b.of.len : OrthogonalIndex))
          (op (a.of.len : OrthogonalIndex)))
  have hs : ws =
    P ◁ ts ≫ (β_ P Q).hom ≫ cs :=
    Enriched.SphereOperator.weight_uncurry_map ds N K A B
  have ho : wo =
    P' ◁ to' ≫ (β_ P' Q').hom ≫ co :=
    Enriched.SphereOperator.weight_uncurry_map do' n.of.len k.of.len a.of.len b.of.len
  have hPair : P ◁ ts ≫ (p ⊗ₘ q) = (p ⊗ₘ h) ≫ P' ◁ to' := by
    rw [← id_tensorHom, ← id_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, ht]
  have hCore : P ◁ ts ≫ (β_ P Q).hom ≫ cs ≫ r =
      (p ⊗ₘ h) ≫ P' ◁ to' ≫ (β_ P' Q').hom ≫ co := by
    rw [hc, ← braiding_naturality_assoc]
    simpa only [Category.assoc] using
      congrArg (fun z => z ≫ (β_ P' Q').hom ≫ co) hPair
  change ws ≫ r = (p ⊗ₘ h) ≫ wo
  rw [hs, ho]
  simpa only [Category.assoc] using hCore

/-- The original coefficient action commutes on the complete finite-bijection Hom. -/
theorem symmetricOrthogonalCoefficientAction (a b : I) :
    (β_ (PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⟶ b))
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a)).hom ≫
      MonoidalClosed.uncurry
        (PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}.map
          ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a)
          ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj b)) ≫
      (originalSymmetricOrthogonalCoefficientIso.{u, v} b).hom =
    (symmetricOrthogonalHomMap.{u, v} a b ⊗ₘ
      (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom) ≫
      (β_ (OrthogonalIndex.hom.{u, v} a.of.len b.of.len)
        (PointedCGWH.orthogonalSphere.{u, v} a.of.len)).hom ≫
      MonoidalClosed.uncurry (orthogonalSphereFunctor.{u, v}.map a.of.len b.of.len) := by
  let V := PointedCGWH.{u, v}
  let A := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj a
  let B := (PointedCGWH.copowerRestriction.{u, v, 0} I).obj b
  let H : V := A ⟶[V] B
  let H' : V := OrthogonalIndex.hom.{u, v} a.of.len b.of.len
  let Sa : V := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let Sb : V := PointedCGWH.sphereSequence.{u, v}.functor.obj b
  let Ta : V := PointedCGWH.orthogonalSphere.{u, v} a.of.len
  let Tb : V := PointedCGWH.orthogonalSphere.{u, v} b.of.len
  let f : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} a b
  let ca : Sa ⟶ Ta := (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let cb : Sb ⟶ Tb := (originalSymmetricOrthogonalCoefficientIso.{u, v} b).hom
  let us : Sa ⊗ H ⟶ Sb := MonoidalClosed.uncurry
    (PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}.map A B)
  let t : H' ⟶ (ihom Ta).obj Tb := orthogonalSphereFunctor.{u, v}.map a.of.len b.of.len
  let ut : Ta ⊗ H' ⟶ Tb := MonoidalClosed.uncurry t
  have hn : us ≫ cb = (ca ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (f ≫ t) :=
    originalSymmetricOrthogonalCoefficientIso_fullNaturality.{u, v} a b
  have hTensor : (ca ⊗ₘ 𝟙 H) ≫ Ta ◁ f = ca ⊗ₘ f := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have hFull : us ≫ cb = (ca ⊗ₘ f) ≫ ut := by
    rw [MonoidalClosed.uncurry_natural_left] at hn
    exact hn.trans (by simpa only [Category.assoc] using congrArg (fun z => z ≫ ut) hTensor)
  change (β_ H Sa).hom ≫ us ≫ cb = (f ⊗ₘ ca) ≫ (β_ H' Ta).hom ≫ ut
  rw [hFull, ← braiding_naturality_assoc]

universe uC vC

private theorem balancedTensorFamily {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {P Q H A B P' Q' H' A' B' Z : C}
    (w : Q ⊗ H ⟶ P) (w' : Q' ⊗ H' ⟶ P')
    (s : H ⊗ A ⟶ B) (s' : H' ⊗ A' ⟶ B')
    (p : P ⟶ P') (q : Q ⟶ Q') (h : H ⟶ H') (a : A ⟶ A') (b : B ⟶ B')
    (ia : P' ⊗ A' ⟶ Z) (ib : Q' ⊗ B' ⟶ Z)
    (hw : w ≫ p = (q ⊗ₘ h) ≫ w')
    (hs : s ≫ b = (h ⊗ₘ a) ≫ s')
    (hb : (α_ Q' H' A').inv ≫ (w' ⊗ₘ 𝟙 A') ≫ ia = Q' ◁ s' ≫ ib) :
    (α_ Q H A).inv ≫ (w ⊗ₘ 𝟙 A) ≫ (p ⊗ₘ a) ≫ ia =
      Q ◁ s ≫ (q ⊗ₘ b) ≫ ib := by
  have hLeft : (w ⊗ₘ 𝟙 A) ≫ (p ⊗ₘ a) =
      ((q ⊗ₘ h) ⊗ₘ a) ≫ (w' ⊗ₘ 𝟙 A') := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, hw]
  have hRight : (q ⊗ₘ (h ⊗ₘ a)) ≫ Q' ◁ s' = Q ◁ s ≫ (q ⊗ₘ b) := by
    calc
      _ = q ⊗ₘ ((h ⊗ₘ a) ≫ s') := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      _ = q ⊗ₘ (s ≫ b) := by rw [hs]
      _ = _ := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [← Category.assoc (w ⊗ₘ 𝟙 A) (p ⊗ₘ a) ia, hLeft,
    Category.assoc, ← associator_inv_naturality_assoc, hb]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ ib) hRight

/-- The proposed integrand map satisfies every original enriched coend relation. -/
theorem symmetricOrthogonalBalance (n k a b : I) :
    let R := PointedCGWH.copowerRestriction.{u, v, 0} I
    let W := Enriched.SphereOperator.weight
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I) (R.obj n) (R.obj k)
    let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    (α_ (W.obj (op (R.obj b))) (R.obj a ⟶[PointedCGWH.{u, v}] R.obj b)
      (S.obj (R.obj a))).inv ≫
      (MonoidalClosed.uncurry (W.map (op (R.obj b)) (op (R.obj a))) ⊗ₘ
        𝟙 (S.obj (R.obj a))) ≫ symmetricOrthogonalGenerator.{u, v} n k a =
    W.obj (op (R.obj b)) ◁
      ((β_ (R.obj a ⟶[PointedCGWH.{u, v}] R.obj b) (S.obj (R.obj a))).hom ≫
        MonoidalClosed.uncurry (S.map (R.obj a) (R.obj b))) ≫
      symmetricOrthogonalGenerator.{u, v} n k b := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight
    (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I) (R.obj n) (R.obj k)
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let W' := OrthogonalOperatorIndex.weight.{u, v} n.of.len k.of.len
  let T := orthogonalSphereFunctor.{u, v}
  let Pa : V := W.obj (op (R.obj a))
  let Pb : V := W.obj (op (R.obj b))
  let H : V := R.obj a ⟶[V] R.obj b
  let Sa : V := S.obj (R.obj a)
  let Sb : V := S.obj (R.obj b)
  let Pa' : V := W'.obj (op (a.of.len : OrthogonalIndex))
  let Pb' : V := W'.obj (op (b.of.len : OrthogonalIndex))
  let H' : V := OrthogonalIndex.hom.{u, v} a.of.len b.of.len
  let Ta : V := T.obj (a.of.len : OrthogonalIndex)
  let Tb : V := T.obj (b.of.len : OrthogonalIndex)
  let wa : Pb ⊗ H ⟶ Pa := MonoidalClosed.uncurry (W.map (op (R.obj b)) (op (R.obj a)))
  let wa' : Pb' ⊗ H' ⟶ Pa' :=
    MonoidalClosed.uncurry (W'.map (op (b.of.len : OrthogonalIndex))
      (op (a.of.len : OrthogonalIndex)))
  let sa : H ⊗ Sa ⟶ Sb := (β_ H Sa).hom ≫
    MonoidalClosed.uncurry (S.map (R.obj a) (R.obj b))
  let sa' : H' ⊗ Ta ⟶ Tb := (β_ H' Ta).hom ≫
    MonoidalClosed.uncurry (T.map a.of.len b.of.len)
  let p : Pa ⟶ Pa' := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k
  let q : Pb ⟶ Pb' := symmetricOrthogonalHomMap.{u, v} (b ⊗ n) k
  let h : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} a b
  let ca : Sa ⟶ Ta := (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let cb : Sb ⟶ Tb := (originalSymmetricOrthogonalCoefficientIso.{u, v} b).hom
  let ia : Pa' ⊗ Ta ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len a.of.len
  let ib : Pb' ⊗ Tb ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len b.of.len
  have hw : wa ≫ p = (q ⊗ₘ h) ≫ wa' := symmetricOrthogonalWeight.{u, v} n k a b
  have hs : sa ≫ cb = (h ⊗ₘ ca) ≫ sa' := symmetricOrthogonalCoefficientAction.{u, v} a b
  have hb : (α_ Pb' H' Ta).inv ≫ (wa' ⊗ₘ 𝟙 Ta) ≫ ia = Pb' ◁ sa' ≫ ib :=
    Enriched.weightedCoend.condition W' T (a.of.len : OrthogonalIndex)
      (b.of.len : OrthogonalIndex)
  exact balancedTensorFamily wa wa' sa sa' p q h ca cb ia ib hw hs hb

/-- The genuine map between the full symmetric and orthogonal spectrum operator Homs. -/
def symmetricOrthogonalOperatorHomMap (n k : I) :
    (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
      PointedCGWH.symmetricOperatorObj.{u, v} k) ⟶
        OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
  Enriched.weightedCoend.desc
    (Enriched.SphereOperator.weight
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k))
    PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    (fun a => symmetricOrthogonalGenerator.{u, v} n k (show I from a))
    (fun a b => symmetricOrthogonalBalance.{u, v} n k (show I from a) (show I from b))

/-- The full Hom map agrees with the original coefficient map on every coend generator. -/
theorem symmetricOrthogonalOperatorHomMap_generator (n k a : I) :
    Enriched.weightedCoend.ι
      (Enriched.SphereOperator.weight
        (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k))
      PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a) ≫
      symmetricOrthogonalOperatorHomMap.{u, v} n k =
    symmetricOrthogonalGenerator.{u, v} n k a :=
  Enriched.weightedCoend.ι_desc _ _ _ _ _

theorem smallFiniteBijection_leftUnitor (n : I) :
    smallFiniteBijection (λ_ n).hom = finCongr (Nat.zero_add n.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_leftUnitor n
theorem smallFiniteBijection_associator (a b n : I) :
    smallFiniteBijection (α_ a b n).hom = finCongr (Nat.add_assoc a.of.len b.of.len n.of.len) :=
  CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_associator a b n

/-- The actual enriched left-unitor point maps to the original orthogonal unit point. -/
theorem symmetricOrthogonalLeftUnitor (n : I) :
    eHomEquiv PointedCGWH.{u, v}
      (λ_ ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)).hom ≫
      symmetricOrthogonalHomMap.{u, v} ((𝟙_ I) ⊗ n) n =
    eHomEquiv PointedCGWH.{u, v} (λ_ (n.of.len : OrthogonalIndex)).hom := by
  let V := PointedCGWH.{u, v}
  let H : V := ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj ((𝟙_ I) ⊗ n)) ⟶[V]
    (PointedCGWH.copowerRestriction.{u, v, 0} I).obj n
  let K : V := OrthogonalIndex.hom.{u, v} (0 + n.of.len) n.of.len
  let f : H ⟶ K := symmetricOrthogonalHomMap.{u, v} ((𝟙_ I) ⊗ n) n
  let p : 𝟙_ V ⟶ H :=
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (((𝟙_ I) ⊗ n) ⟶ n) (λ_ n).hom
  let ps : 𝟙_ V ⟶ H := eHomEquiv V
    (λ_ ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)).hom
  let po : 𝟙_ V ⟶ K := eHomEquiv V (λ_ (n.of.len : OrthogonalIndex)).hom
  have hSource : ps = p := rfl
  have hPoint : po =
      OrthogonalIndex.matrixPoint.{u, v}
        (finiteBijectionMatrix (finCongr (Nat.zero_add n.of.len))) := by
    apply congrArg (OrthogonalIndex.matrixPoint.{u, v})
    apply OrthogonalMatrixHom.ext
    change Matrix.reindex (finCongr (Nat.zero_add n.of.len))
      (Equiv.refl (Fin (0 + n.of.len))) (1 : Matrix (Fin (0 + n.of.len)) (Fin (0 + n.of.len)) ℝ) = _
    exact (finiteBijectionMatrix_reindex (finCongr (Nat.zero_add n.of.len))).symm
  have hGen : p ≫ f = OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix (λ_ n).hom) :=
    symmetricOrthogonalHomMap_generator.{u, v} (λ_ n).hom
  have hMatrix : smallBijectionMatrix (λ_ n).hom =
      finiteBijectionMatrix (finCongr (Nat.zero_add n.of.len)) := by
    rw [smallBijectionMatrix, smallFiniteBijection_leftUnitor]
    rfl
  change ps ≫ f = po
  rw [hSource, hGen, hMatrix, hPoint]
  rfl

/-- The full fixed-left tensor action respects the same original Hom inclusion. -/
theorem symmetricOrthogonalFixedLeft (a b n : I) :
    (λ_ (PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⟶ b))).inv ≫
      (eId PointedCGWH.{u, v} (PointedCGWH.copowerIndexObj.{u, v, 0} I n) ⊗ₘ 𝟙 _) ≫
      PointedCGWH.copowerTensorHom.{u, v, 0} I n n a b ≫
      symmetricOrthogonalHomMap.{u, v} (n ⊗ a) (n ⊗ b) =
    symmetricOrthogonalHomMap.{u, v} a b ≫
      (λ_ (OrthogonalIndex.hom.{u, v} a.of.len b.of.len)).inv ≫
      (eId PointedCGWH.{u, v} (n.of.len : OrthogonalIndex) ⊗ₘ 𝟙 _) ≫
      OrthogonalIndex.tensorMap.{u, v} n.of.len n.of.len a.of.len b.of.len := by
  let V := PointedCGWH.{u, v}
  let H := (PointedCGWH.copowerIndexObj.{u, v, 0} I a ⟶[V]
    PointedCGWH.copowerIndexObj.{u, v, 0} I b)
  let K := OrthogonalIndex.hom.{u, v} a.of.len b.of.len
  let f : H ⟶ K := symmetricOrthogonalHomMap.{u, v} a b
  let e : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (n ⟶ n) :=
    eId V (PointedCGWH.copowerIndexObj.{u, v, 0} I n)
  let e' : 𝟙_ V ⟶ OrthogonalIndex.hom.{u, v} n.of.len n.of.len :=
    eId V (n.of.len : OrthogonalIndex)
  let T := OrthogonalIndex.tensorMap.{u, v} n.of.len n.of.len a.of.len b.of.len
  let j : PointedCGWH.basedDiscreteObj.{u, v, 0} (n ⟶ n) ⟶
      OrthogonalIndex.hom.{u, v} n.of.len n.of.len := symmetricOrthogonalHomMap.{u, v} n n
  have hTensor : (e ⊗ₘ 𝟙 H) ≫ (j ⊗ₘ f) = e' ⊗ₘ f := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => z ⊗ₘ f) (symmetricOrthogonalHomMap_id.{u, v} n)
  have hUnit : (λ_ H).inv ≫ (e' ⊗ₘ f) =
      f ≫ (λ_ K).inv ≫ (e' ⊗ₘ 𝟙 K) := by
    rw [leftUnitor_inv_naturality_assoc]
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have ht := symmetricOrthogonalHomMap_tensor.{u, v} n n a b
  have he := congrArg (fun q => (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) ≫ q) ht
  apply he.trans
  change (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) ≫ (j ⊗ₘ f) ≫ T =
    f ≫ (λ_ K).inv ≫ (e' ⊗ₘ 𝟙 K) ≫ T
  simpa only [Category.assoc] using congrArg (fun z => z ≫ T)
    ((congrArg (fun z => (λ_ H).inv ≫ z) hTensor).trans hUnit)

/-- The original three-block associator maps to the actual orthogonal associator. -/
theorem symmetricOrthogonalAssociator (a b n : I) :
    eHomEquiv PointedCGWH.{u, v}
      (α_ ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj b)
        ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)).hom ≫
      symmetricOrthogonalHomMap.{u, v} ((a ⊗ b) ⊗ n) (a ⊗ (b ⊗ n)) =
    eHomEquiv PointedCGWH.{u, v}
      (α_ (a.of.len : OrthogonalIndex) (b.of.len : OrthogonalIndex)
        (n.of.len : OrthogonalIndex)).hom := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let H : V := R.obj ((a ⊗ b) ⊗ n) ⟶[V] R.obj (a ⊗ (b ⊗ n))
  let K : V := OrthogonalIndex.hom.{u, v}
    ((a.of.len + b.of.len) + n.of.len) (a.of.len + (b.of.len + n.of.len))
  let f : H ⟶ K := symmetricOrthogonalHomMap.{u, v} ((a ⊗ b) ⊗ n) (a ⊗ (b ⊗ n))
  let p : 𝟙_ V ⟶ H := PointedCGWH.basedDiscreteIncl.{u, v, 0}
    (((a ⊗ b) ⊗ n) ⟶ (a ⊗ (b ⊗ n))) (α_ a b n).hom
  let ps : 𝟙_ V ⟶ H := eHomEquiv V (α_ (R.obj a) (R.obj b) (R.obj n)).hom
  let po : 𝟙_ V ⟶ K := eHomEquiv V
    (α_ (a.of.len : OrthogonalIndex) (b.of.len : OrthogonalIndex)
      (n.of.len : OrthogonalIndex)).hom
  have hSource : ps = p := rfl
  have hPoint : po = OrthogonalIndex.matrixPoint.{u, v}
      (finiteBijectionMatrix (finCongr (Nat.add_assoc a.of.len b.of.len n.of.len))) := by
    apply congrArg (OrthogonalIndex.matrixPoint.{u, v})
    apply OrthogonalMatrixHom.ext
    change Matrix.reindex (finCongr (Nat.add_assoc a.of.len b.of.len n.of.len))
      (Equiv.refl (Fin ((a.of.len + b.of.len) + n.of.len)))
      (1 : Matrix (Fin ((a.of.len + b.of.len) + n.of.len))
        (Fin ((a.of.len + b.of.len) + n.of.len)) ℝ) = _
    exact (finiteBijectionMatrix_reindex
      (finCongr (Nat.add_assoc a.of.len b.of.len n.of.len))).symm
  have hGen : p ≫ f = OrthogonalIndex.matrixPoint.{u, v}
      (smallBijectionMatrix (α_ a b n).hom) :=
    symmetricOrthogonalHomMap_generator.{u, v} (α_ a b n).hom
  have hMatrix : smallBijectionMatrix (α_ a b n).hom =
      finiteBijectionMatrix (finCongr (Nat.add_assoc a.of.len b.of.len n.of.len)) := by
    rw [smallBijectionMatrix, smallFiniteBijection_associator]
    rfl
  change ps ≫ f = po
  rw [hSource, hGen, hMatrix, hPoint]
  rfl

/-- The full coend Hom map preserves the actual enriched operator identity. -/
theorem symmetricOrthogonalOperatorHomMap_id (n : I) :
    eId PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} n) ≫
      symmetricOrthogonalOperatorHomMap.{u, v} n n =
    eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len) := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let Ls := PointedCGWH.sphereCopowerLaxData.{u, v}
  let Lo := orthogonalSphereMonoidalData.{u, v}
  let H : V := R.obj ((𝟙_ I) ⊗ n) ⟶[V] R.obj n
  let H' : V := OrthogonalIndex.hom.{u, v} (0 + n.of.len) n.of.len
  let A : V := S.obj (R.obj (𝟙_ I))
  let A' : V := PointedCGWH.orthogonalSphere.{u, v} 0
  let ps : 𝟙_ V ⟶ H := eHomEquiv V (λ_ (R.obj n)).hom
  let po : 𝟙_ V ⟶ H' := eHomEquiv V (λ_ (n.of.len : OrthogonalIndex)).hom
  let es : 𝟙_ V ⟶ A := Ls.epsilon
  let eo : 𝟙_ V ⟶ A' := Lo.epsilon
  let f : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} ((𝟙_ I) ⊗ n) n
  let c : A ⟶ A' := (originalSymmetricOrthogonalCoefficientIso.{u, v} (𝟙_ I)).hom
  let Zs : V := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} n
  let Zo : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len n.of.len
  let m : Zs ⟶ Zo := symmetricOrthogonalOperatorHomMap.{u, v} n n
  let is : H ⊗ A ⟶ Zs := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight ds (R.obj n) (R.obj n))
    S (R.obj (𝟙_ I))
  let io : H' ⊗ A' ⟶ Zo := OrthogonalOperatorIndex.ι.{u, v} n.of.len n.of.len 0
  let ids : 𝟙_ V ⟶ Zs :=
    eId V (PointedCGWH.symmetricOperatorObj.{u, v} n)
  let ido : 𝟙_ V ⟶ Zo :=
    eId V (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
  have hs : ids = (λ_ (𝟙_ V)).inv ≫ (ps ⊗ₘ es) ≫ is := rfl
  have ho : ido = (λ_ (𝟙_ V)).inv ≫ (po ⊗ₘ eo) ≫ io := rfl
  have hg : is ≫ m = (f ⊗ₘ c) ≫ io :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} n n (𝟙_ I)
  have hp : ps ≫ f = po := symmetricOrthogonalLeftUnitor.{u, v} n
  have he : es ≫ c = eo := by
    have h := originalSymmetricOrthogonalCoefficientNatIso_unit.{u, v}
    rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component] at h
    exact h
  have hPair : (ps ⊗ₘ es) ≫ (f ⊗ₘ c) = po ⊗ₘ eo := by
    rw [tensorHom_comp_tensorHom, hp, he]
  change ids ≫ m = ido
  rw [hs, Category.assoc, Category.assoc, hg]
  rw [← Category.assoc (ps ⊗ₘ es) (f ⊗ₘ c) io, hPair]
  exact ho.symm

/-- The full two-arrow index generator commutes with the original native inclusion. -/
theorem symmetricOrthogonalIndexGenerator (n k l a b : I) :
    let R := PointedCGWH.copowerRestriction.{u, v, 0} I
    Enriched.SphereOperator.indexGenerator
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b) ≫
      symmetricOrthogonalHomMap.{u, v} ((b ⊗ a) ⊗ n) l =
    (symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} (b ⊗ k) l) ≫
      Enriched.SphereOperator.indexGenerator OrthogonalIndex.enrichedMonoidalData.{u, v}
        (n.of.len : OrthogonalIndex) k.of.len l.of.len a.of.len b.of.len := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let do' := OrthogonalIndex.enrichedMonoidalData.{u, v}
  let P : V := R.obj (a ⊗ n) ⟶[V] R.obj k
  let Q : V := R.obj (b ⊗ k) ⟶[V] R.obj l
  let T : V := R.obj (b ⊗ (a ⊗ n)) ⟶[V] R.obj (b ⊗ k)
  let U : V := R.obj (b ⊗ (a ⊗ n)) ⟶[V] R.obj l
  let H : V := R.obj ((b ⊗ a) ⊗ n) ⟶[V] R.obj (b ⊗ (a ⊗ n))
  let Z : V := R.obj ((b ⊗ a) ⊗ n) ⟶[V] R.obj l
  let P' : V := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len
  let Q' : V := OrthogonalIndex.hom.{u, v} (b.of.len + k.of.len) l.of.len
  let T' : V := OrthogonalIndex.hom.{u, v}
    (b.of.len + (a.of.len + n.of.len)) (b.of.len + k.of.len)
  let U' : V := OrthogonalIndex.hom.{u, v} (b.of.len + (a.of.len + n.of.len)) l.of.len
  let H' : V := OrthogonalIndex.hom.{u, v}
    ((b.of.len + a.of.len) + n.of.len) (b.of.len + (a.of.len + n.of.len))
  let Z' : V := OrthogonalIndex.hom.{u, v} ((b.of.len + a.of.len) + n.of.len) l.of.len
  let f : P ⟶ P' := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k
  let g : Q ⟶ Q' := symmetricOrthogonalHomMap.{u, v} (b ⊗ k) l
  let t : T ⟶ T' := symmetricOrthogonalHomMap.{u, v} (b ⊗ (a ⊗ n)) (b ⊗ k)
  let u : U ⟶ U' := symmetricOrthogonalHomMap.{u, v} (b ⊗ (a ⊗ n)) l
  let h : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n))
  let z : Z ⟶ Z' := symmetricOrthogonalHomMap.{u, v} ((b ⊗ a) ⊗ n) l
  let ms : P ⟶ T := (λ_ P).inv ≫ (eId V (R.obj b) ⊗ₘ 𝟙 P) ≫
    ds.tensorMap (R.obj b) (R.obj b) (R.obj (a ⊗ n)) (R.obj k)
  let mo : P' ⟶ T' := (λ_ P').inv ≫ (eId V (b.of.len : OrthogonalIndex) ⊗ₘ 𝟙 P') ≫
    do'.tensorMap b.of.len b.of.len (a.of.len + n.of.len) k.of.len
  let cs : T ⊗ Q ⟶ U := eComp V (R.obj (b ⊗ (a ⊗ n))) (R.obj (b ⊗ k)) (R.obj l)
  let co : T' ⊗ Q' ⟶ U' := eComp V
    (b.of.len + (a.of.len + n.of.len) : OrthogonalIndex)
    (b.of.len + k.of.len : OrthogonalIndex) (l.of.len : OrthogonalIndex)
  let ps : 𝟙_ V ⟶ H := eHomEquiv V (α_ (R.obj b) (R.obj a) (R.obj n)).hom
  let po : 𝟙_ V ⟶ H' := eHomEquiv V
    (α_ (b.of.len : OrthogonalIndex) (a.of.len : OrthogonalIndex)
      (n.of.len : OrthogonalIndex)).hom
  let ds' : H ⊗ U ⟶ Z := eComp V (R.obj ((b ⊗ a) ⊗ n))
    (R.obj (b ⊗ (a ⊗ n))) (R.obj l)
  let do'' : H' ⊗ U' ⟶ Z' := eComp V
    ((b.of.len + a.of.len) + n.of.len : OrthogonalIndex)
    (b.of.len + (a.of.len + n.of.len) : OrthogonalIndex) (l.of.len : OrthogonalIndex)
  let pre : U ⟶ Z := (λ_ U).inv ≫ (ps ⊗ₘ 𝟙 U) ≫ ds'
  let pre' : U' ⟶ Z' := (λ_ U').inv ≫ (po ⊗ₘ 𝟙 U') ≫ do''
  let is : P ⊗ Q ⟶ Z := Enriched.SphereOperator.indexGenerator ds
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  let io : P' ⊗ Q' ⟶ Z' := Enriched.SphereOperator.indexGenerator do'
    (n.of.len : OrthogonalIndex) k.of.len l.of.len a.of.len b.of.len
  have hm : ms ≫ t = f ≫ mo := symmetricOrthogonalFixedLeft.{u, v} (a ⊗ n) k b
  have hc : cs ≫ u = (t ⊗ₘ g) ≫ co :=
    symmetricOrthogonalHomMap_comp.{u, v} (b ⊗ (a ⊗ n)) (b ⊗ k) l
  have ht : (ms ⊗ₘ 𝟙 Q) ≫ (t ⊗ₘ g) = (f ⊗ₘ g) ≫ (mo ⊗ₘ 𝟙 Q') := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, hm]
  have hFirst : (ms ⊗ₘ 𝟙 Q) ≫ cs ≫ u = (f ⊗ₘ g) ≫ (mo ⊗ₘ 𝟙 Q') ≫ co := by
    rw [hc]
    simpa only [Category.assoc] using congrArg (fun q => q ≫ co) ht
  have hp : ps ≫ h = po := symmetricOrthogonalAssociator.{u, v} b a n
  have hd : ds' ≫ z = (h ⊗ₘ u) ≫ do'' :=
    symmetricOrthogonalHomMap_comp.{u, v} ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n)) l
  have hPointTensor : (ps ⊗ₘ 𝟙 U) ≫ (h ⊗ₘ u) = po ⊗ₘ u := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, hp]
  have hUnit : (λ_ U).inv ≫ (po ⊗ₘ u) =
      u ≫ (λ_ U').inv ≫ (po ⊗ₘ 𝟙 U') := by
    rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hPre : pre ≫ z = u ≫ pre' := by
    change ((λ_ U).inv ≫ (ps ⊗ₘ 𝟙 U) ≫ ds') ≫ z =
      u ≫ (λ_ U').inv ≫ (po ⊗ₘ 𝟙 U') ≫ do''
    simp only [Category.assoc]
    rw [hd, ← Category.assoc (ps ⊗ₘ 𝟙 U) (h ⊗ₘ u) do'', hPointTensor]
    simpa only [Category.assoc] using congrArg (fun q => q ≫ do'') hUnit
  have hs : is = (ms ⊗ₘ 𝟙 Q) ≫ cs ≫ pre := by
    change ((ms ⊗ₘ 𝟙 Q) ≫ cs) ≫ pre = (ms ⊗ₘ 𝟙 Q) ≫ cs ≫ pre
    exact Category.assoc _ _ _
  have ho : io = (mo ⊗ₘ 𝟙 Q') ≫ co ≫ pre' := by
    change ((mo ⊗ₘ 𝟙 Q') ≫ co) ≫ pre' = (mo ⊗ₘ 𝟙 Q') ≫ co ≫ pre'
    exact Category.assoc _ _ _
  change is ≫ z = (f ⊗ₘ g) ≫ io
  rw [hs, ho]
  simp only [Category.assoc]
  rw [hPre]
  simpa only [Category.assoc] using congrArg (fun q => q ≫ pre') hFirst

private theorem compositionTensorFamily {C : Type uC} [Category.{vC} C]
    [MonoidalCategory C] [BraidedCategory C]
    {P Q A B Z E P' Q' A' B' Z' E' : C}
    (i : P ⊗ Q ⟶ Z) (i' : P' ⊗ Q' ⟶ Z')
    (μ : B ⊗ A ⟶ E) (μ' : B' ⊗ A' ⟶ E')
    (f : P ⟶ P') (g : Q ⟶ Q') (z : Z ⟶ Z')
    (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E')
    (hi : i ≫ z = (f ⊗ₘ g) ≫ i') (hμ : μ ≫ e = (b ⊗ₘ a) ≫ μ') :
    tensorδ P Q A B ≫ (𝟙 (P ⊗ Q) ⊗ₘ (β_ A B).hom) ≫
      (i ⊗ₘ μ) ≫ (z ⊗ₘ e) =
    ((f ⊗ₘ a) ⊗ₘ (g ⊗ₘ b)) ≫ tensorδ P' Q' A' B' ≫
      (𝟙 (P' ⊗ Q') ⊗ₘ (β_ A' B').hom) ≫ (i' ⊗ₘ μ') := by
  have hTimes : (i ⊗ₘ μ) ≫ (z ⊗ₘ e) =
      ((f ⊗ₘ g) ⊗ₘ (b ⊗ₘ a)) ≫ (i' ⊗ₘ μ') := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hi, hμ]
  have hBraid : (𝟙 (P ⊗ Q) ⊗ₘ (β_ A B).hom) ≫ ((f ⊗ₘ g) ⊗ₘ (b ⊗ₘ a)) =
      ((f ⊗ₘ g) ⊗ₘ (a ⊗ₘ b)) ≫ (𝟙 (P' ⊗ Q') ⊗ₘ (β_ A' B').hom) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
    exact congrArg (fun q => (f ⊗ₘ g) ⊗ₘ q) (braiding_naturality a b).symm
  have hδ : ((f ⊗ₘ a) ⊗ₘ (g ⊗ₘ b)) ≫ tensorδ P' Q' A' B' =
      tensorδ P Q A B ≫ ((f ⊗ₘ g) ⊗ₘ (a ⊗ₘ b)) := by
    have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor C)
      (show (P, Q) ⟶ (P', Q') from (f, g))
      (show (A, B) ⟶ (A', B') from (a, b))
    exact h.symm
  rw [hTimes, ← Category.assoc (𝟙 (P ⊗ Q) ⊗ₘ (β_ A B).hom)
    ((f ⊗ₘ g) ⊗ₘ (b ⊗ₘ a)) (i' ⊗ₘ μ'), hBraid]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (𝟙 (P' ⊗ Q') ⊗ₘ (β_ A' B').hom) ≫ (i' ⊗ₘ μ')) hδ.symm

/-- The complete coefficient-first generator preserves original source-first composition. -/
theorem symmetricOrthogonalGenerator_comp (n k l a b : I) :
    let R := PointedCGWH.copowerRestriction.{u, v, 0} I
    Enriched.SphereOperator.compositionGenerator
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      PointedCGWH.sphereCopowerEnrichedFunctor.{u, v} PointedCGWH.sphereCopowerLaxData.{u, v}
      (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b) ≫
      symmetricOrthogonalOperatorHomMap.{u, v} n l =
    (symmetricOrthogonalGenerator.{u, v} n k a ⊗ₘ
      symmetricOrthogonalGenerator.{u, v} k l b) ≫
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
        (OrthogonalOperatorIndex.ofIndex.{u, v} l.of.len) := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let do' := OrthogonalIndex.enrichedMonoidalData.{u, v}
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let T := orthogonalSphereFunctor.{u, v}
  let Ls := PointedCGWH.sphereCopowerLaxData.{u, v}
  let Lo := orthogonalSphereMonoidalData.{u, v}
  let P : V := R.obj (a ⊗ n) ⟶[V] R.obj k
  let Q : V := R.obj (b ⊗ k) ⟶[V] R.obj l
  let Z : V := R.obj ((b ⊗ a) ⊗ n) ⟶[V] R.obj l
  let A : V := S.obj (R.obj a)
  let B : V := S.obj (R.obj b)
  let E : V := S.obj (R.obj (b ⊗ a))
  let P' : V := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len
  let Q' : V := OrthogonalIndex.hom.{u, v} (b.of.len + k.of.len) l.of.len
  let Z' : V := OrthogonalIndex.hom.{u, v} ((b.of.len + a.of.len) + n.of.len) l.of.len
  let A' : V := T.obj (a.of.len : OrthogonalIndex)
  let B' : V := T.obj (b.of.len : OrthogonalIndex)
  let E' : V := T.obj (b.of.len + a.of.len : OrthogonalIndex)
  let f : P ⟶ P' := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k
  let g : Q ⟶ Q' := symmetricOrthogonalHomMap.{u, v} (b ⊗ k) l
  let z : Z ⟶ Z' := symmetricOrthogonalHomMap.{u, v} ((b ⊗ a) ⊗ n) l
  let ca : A ⟶ A' := (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let cb : B ⟶ B' := (originalSymmetricOrthogonalCoefficientIso.{u, v} b).hom
  let ce : E ⟶ E' := (originalSymmetricOrthogonalCoefficientIso.{u, v} (b ⊗ a)).hom
  let is : P ⊗ Q ⟶ Z := Enriched.SphereOperator.indexGenerator ds
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  let io : P' ⊗ Q' ⟶ Z' := Enriched.SphereOperator.indexGenerator do'
    (n.of.len : OrthogonalIndex) k.of.len l.of.len a.of.len b.of.len
  let μs : B ⊗ A ⟶ E := Ls.mu (R.obj b) (R.obj a)
  let μo : B' ⊗ A' ⟶ E' := Lo.mu b.of.len a.of.len
  let Js : V := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[V]
    PointedCGWH.symmetricOperatorObj.{u, v} l
  let Jo : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len l.of.len
  let φ : Js ⟶ Jo := symmetricOrthogonalOperatorHomMap.{u, v} n l
  let ιs : Z ⊗ E ⟶ Js := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight ds (R.obj n) (R.obj l)) S (R.obj (b ⊗ a))
  let ιo : Z' ⊗ E' ⟶ Jo :=
    OrthogonalOperatorIndex.ι.{u, v} n.of.len l.of.len (b.of.len + a.of.len)
  let cs : (P ⊗ A) ⊗ (Q ⊗ B) ⟶ Js := Enriched.SphereOperator.compositionGenerator ds S Ls
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.obj b)
  let co : (P' ⊗ A') ⊗ (Q' ⊗ B') ⟶ Jo := Enriched.SphereOperator.compositionGenerator do' T Lo
    (n.of.len : OrthogonalIndex) k.of.len l.of.len a.of.len b.of.len
  let ga : P ⊗ A ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    symmetricOrthogonalGenerator.{u, v} n k a
  let gb : Q ⊗ B ⟶ OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len :=
    symmetricOrthogonalGenerator.{u, v} k l b
  let ιa : P' ⊗ A' ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len a.of.len
  let ιb : Q' ⊗ B' ⟶ OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len :=
    OrthogonalOperatorIndex.ι.{u, v} k.of.len l.of.len b.of.len
  let c : OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len ⊗
      OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len ⟶ Jo :=
    eComp V (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
      (OrthogonalOperatorIndex.ofIndex.{u, v} l.of.len)
  have hi : is ≫ z = (f ⊗ₘ g) ≫ io := symmetricOrthogonalIndexGenerator.{u, v} n k l a b
  have hμ : μs ≫ ce = (cb ⊗ₘ ca) ≫ μo := by
    have h := originalSymmetricOrthogonalCoefficientNatIso_tensor.{u, v} b a
    rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component,
      originalSymmetricOrthogonalCoefficientNatIso_hom_component,
      originalSymmetricOrthogonalCoefficientNatIso_hom_component] at h
    exact h
  have hg : ιs ≫ φ = (z ⊗ₘ ce) ≫ ιo :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} n l (b ⊗ a)
  have hs : cs = tensorδ P Q A B ≫ (𝟙 (P ⊗ Q) ⊗ₘ (β_ A B).hom) ≫
      (is ⊗ₘ μs) ≫ ιs := rfl
  have ho : co = tensorδ P' Q' A' B' ≫ (𝟙 (P' ⊗ Q') ⊗ₘ (β_ A' B').hom) ≫
      (io ⊗ₘ μo) ≫ ιo := rfl
  have hc : (ιa ⊗ₘ ιb) ≫ c = co :=
    OrthogonalOperatorIndex.composition_generator.{u, v}
      n.of.len k.of.len l.of.len a.of.len b.of.len
  have hCore := compositionTensorFamily is io μs μo f g z ca cb ce hi hμ
  have hWhole : tensorδ P Q A B ≫ (𝟙 (P ⊗ Q) ⊗ₘ (β_ A B).hom) ≫
      (is ⊗ₘ μs) ≫ (z ⊗ₘ ce) ≫ ιo = ((f ⊗ₘ ca) ⊗ₘ (g ⊗ₘ cb)) ≫ co := by
    rw [ho]
    simpa only [Category.assoc] using congrArg (fun q => q ≫ ιo) hCore
  have hLeft : cs ≫ φ = ((f ⊗ₘ ca) ⊗ₘ (g ⊗ₘ cb)) ≫ co := by
    rw [hs]
    simp only [Category.assoc]
    rw [hg]
    exact hWhole
  have hRight : (ga ⊗ₘ gb) ≫ c = ((f ⊗ₘ ca) ⊗ₘ (g ⊗ₘ cb)) ≫ co := by
    change (((f ⊗ₘ ca) ≫ ιa) ⊗ₘ ((g ⊗ₘ cb) ≫ ιb)) ≫ c = _
    rw [← tensorHom_comp_tensorHom_assoc, hc]
  change cs ≫ φ = (ga ⊗ₘ gb) ≫ c
  exact hLeft.trans hRight.symm

set_option maxHeartbeats 400000 in
-- Normalizing both mapped coends expands the full native colimit dictionaries.
/-- The entire native operator composition square follows from both coend extensionalities. -/
theorem symmetricOrthogonalOperatorHomMap_comp (n k l : I) :
    eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} n)
      (PointedCGWH.symmetricOperatorObj.{u, v} k) (PointedCGWH.symmetricOperatorObj.{u, v} l) ≫
      symmetricOrthogonalOperatorHomMap.{u, v} n l =
    (symmetricOrthogonalOperatorHomMap.{u, v} n k ⊗ₘ
      symmetricOrthogonalOperatorHomMap.{u, v} k l) ≫
      eComp PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
        (OrthogonalOperatorIndex.ofIndex.{u, v} l.of.len) := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let L := PointedCGWH.sphereCopowerLaxData.{u, v}
  let W₁ := Enriched.SphereOperator.weight ds (R.obj n) (R.obj k)
  let W₂ := Enriched.SphereOperator.weight ds (R.obj k) (R.obj l)
  let H₁ : V := Enriched.weightedCoend W₁ S
  let H₂ : V := Enriched.weightedCoend W₂ S
  let H₃ : V := Enriched.SphereOperator.Hom ds S (R.obj n) (R.obj l)
  let Z : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len l.of.len
  let m₁ : H₁ ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    symmetricOrthogonalOperatorHomMap.{u, v} n k
  let m₂ : H₂ ⟶ OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len :=
    symmetricOrthogonalOperatorHomMap.{u, v} k l
  let m₃ : H₃ ⟶ Z := symmetricOrthogonalOperatorHomMap.{u, v} n l
  let cs : H₁ ⊗ H₂ ⟶ H₃ := Enriched.SphereOperator.composition ds S L
    (R.obj n) (R.obj k) (R.obj l)
  let co : OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len ⊗
      OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len ⟶ Z :=
    eComp V (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
      (OrthogonalOperatorIndex.ofIndex.{u, v} l.of.len)
  let qL : H₁ ⊗ H₂ ⟶ Z := cs ≫ m₃
  let qR : H₁ ⊗ H₂ ⟶ Z := (m₁ ⊗ₘ m₂) ≫ co
  change qL = qR
  apply Enriched.weightedCoend.Mapped.hom_ext W₁ S (tensorRight H₂)
  intro a
  let P : V := Enriched.weightedCoend.objects W₁ S a
  let p : P ⟶ H₁ := Enriched.weightedCoend.ι W₁ S a
  change (p ▷ H₂) ≫ qL = (p ▷ H₂) ≫ qR
  apply Enriched.weightedCoend.Mapped.hom_ext W₂ S (tensorLeft P)
  intro b
  let Q : V := Enriched.weightedCoend.objects W₂ S b
  let q : Q ⟶ H₂ := Enriched.weightedCoend.ι W₂ S b
  let c : P ⊗ Q ⟶ H₃ := Enriched.SphereOperator.compositionGenerator ds S L
    (R.obj n) (R.obj k) (R.obj l) a b
  let ga : P ⟶ OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len :=
    symmetricOrthogonalGenerator.{u, v} n k (show I from a)
  let gb : Q ⟶ OrthogonalOperatorIndex.hom.{u, v} k.of.len l.of.len :=
    symmetricOrthogonalGenerator.{u, v} k l (show I from b)
  have hSource : (p ⊗ₘ q) ≫ cs = c := Enriched.SphereOperator.composition_generator ds S L
    (R.obj n) (R.obj k) (R.obj l) a b
  have hA : p ≫ m₁ = ga :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} n k (show I from a)
  have hB : q ≫ m₂ = gb :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} k l (show I from b)
  have hTensor : (p ⊗ₘ q) ≫ (m₁ ⊗ₘ m₂) = ga ⊗ₘ gb := by
    rw [tensorHom_comp_tensorHom, hA, hB]
  have hComp : c ≫ m₃ = (ga ⊗ₘ gb) ≫ co :=
    symmetricOrthogonalGenerator_comp.{u, v} n k l (show I from a) (show I from b)
  have hLeft : (p ⊗ₘ q) ≫ qL = c ≫ m₃ := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ m₃) hSource
  have hRight : (p ⊗ₘ q) ≫ qR = (ga ⊗ₘ gb) ≫ co := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ co) hTensor
  have hBoth : (p ⊗ₘ q) ≫ qL = (p ⊗ₘ q) ≫ qR := hLeft.trans (hComp.trans hRight.symm)
  have hPre : (p ⊗ₘ q) = (P ◁ q) ≫ (p ▷ H₂) := tensorHom_def' p q
  change (P ◁ q) ≫ (p ▷ H₂) ≫ qL = (P ◁ q) ≫ (p ▷ H₂) ≫ qR
  rw [← Category.assoc (P ◁ q) (p ▷ H₂) qL,
    ← Category.assoc (P ◁ q) (p ▷ H₂) qR, ← hPre]
  exact hBoth

/-- The actual enriched map of full symmetric and orthogonal spectrum operator indices. -/
def symmetricOrthogonalOperatorIndexFunctor :
    EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
      OrthogonalOperatorIndex.{u, v} where
  obj n := OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len
  map n k := symmetricOrthogonalOperatorHomMap.{u, v}
    (show I from n.asIndex) (show I from k.asIndex)
  map_id n := symmetricOrthogonalOperatorHomMap_id.{u, v} (show I from n.asIndex)
  map_comp n k l := symmetricOrthogonalOperatorHomMap_comp.{u, v}
    (show I from n.asIndex) (show I from k.asIndex) (show I from l.asIndex)

/-- Forget the coefficient parameters through the actual original right sphere and index action. -/
def orthogonalToSymmetricSourceGenerator
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : I) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len) ⊗
      (PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ k) ⊗
        PointedCGWH.sphereSequence.{u, v}.functor.obj a) ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len) :=
  F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len) ◁
    (symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
      (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom) ≫
    OrthogonalSourceRightModule.recoveredGenerator.{u, v} F n.of.len k.of.len a.of.len

/-- The complete original source generator is the generator of actual operator restriction. -/
theorem orthogonalToSymmetricSourceGenerator_curry
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a : I) :
    MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k a) =
      symmetricOrthogonalGenerator.{u, v} n k a ≫
        F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len) := by
  let V := PointedCGWH.{u, v}
  let X : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
  let Y : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let H : V := PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ k) ⊗
    PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let H' : V := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len ⊗
    PointedCGWH.orthogonalSphere.{u, v} a.of.len
  let K : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len
  let m : H ⟶ H' := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
    (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let i : H' ⟶ K := OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len a.of.len
  let f : K ⟶ (ihom X).obj Y :=
    F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let r : X ⊗ H' ⟶ Y :=
    OrthogonalSourceRightModule.recoveredGenerator.{u, v} F n.of.len k.of.len a.of.len
  let q : X ⊗ H ⟶ Y := orthogonalToSymmetricSourceGenerator.{u, v} F n k a
  have hr : X ◁ i ≫ MonoidalClosed.uncurry f = r :=
    OrthogonalSourceRightModule.generatorAction_eq_recoveredGenerator.{u, v} F
      n.of.len k.of.len a.of.len
  have ht : (X ◁ m) ≫ (X ◁ i) = X ◁ (m ≫ i) := (whiskerLeft_comp X m i).symm
  have hq : q = MonoidalClosed.uncurry ((m ≫ i) ≫ f) := by
    change X ◁ m ≫ r = _
    rw [← hr, ← Category.assoc (X ◁ m) (X ◁ i) (MonoidalClosed.uncurry f), ht]
    exact (MonoidalClosed.uncurry_natural_left (m ≫ i) f).symm
  change MonoidalClosed.curry q = (m ≫ i) ≫ f
  rw [hq, MonoidalClosed.curry_uncurry]

/-- All original symmetric relations hold for the concrete source forgetting fields. -/
theorem orthogonalToSymmetricSourceBalance
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k a b : I) :
    let R := PointedCGWH.copowerRestriction.{u, v, 0} I
    let W := Enriched.SphereOperator.weight
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I) (R.obj n) (R.obj k)
    let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    (α_ (W.obj (op (R.obj b))) (R.obj a ⟶[PointedCGWH.{u, v}] R.obj b)
      (S.obj (R.obj a))).inv ≫
      (MonoidalClosed.uncurry (W.map (op (R.obj b)) (op (R.obj a))) ⊗ₘ
        𝟙 (S.obj (R.obj a))) ≫
      MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k a) =
    W.obj (op (R.obj b)) ◁
      ((β_ (R.obj a ⟶[PointedCGWH.{u, v}] R.obj b) (S.obj (R.obj a))).hom ≫
        MonoidalClosed.uncurry (S.map (R.obj a) (R.obj b))) ≫
      MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k b) := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight
    (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I) (R.obj n) (R.obj k)
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let A : V := W.obj (op (R.obj a)) ⊗ S.obj (R.obj a)
  let B : V := W.obj (op (R.obj b)) ⊗ S.obj (R.obj b)
  let H : V := R.obj a ⟶[V] R.obj b
  let D : V := W.obj (op (R.obj b)) ⊗ (H ⊗ S.obj (R.obj a))
  let l : D ⟶ A := (α_ (W.obj (op (R.obj b))) H (S.obj (R.obj a))).inv ≫
    (MonoidalClosed.uncurry (W.map (op (R.obj b)) (op (R.obj a))) ⊗ₘ 𝟙 (S.obj (R.obj a)))
  let r : D ⟶ B := W.obj (op (R.obj b)) ◁
    ((β_ H (S.obj (R.obj a))).hom ≫ MonoidalClosed.uncurry (S.map (R.obj a) (R.obj b)))
  let X : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
  let Y : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let K : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len
  let f : K ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map
    (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let ga : A ⟶ K := symmetricOrthogonalGenerator.{u, v} n k a
  let gb : B ⟶ K := symmetricOrthogonalGenerator.{u, v} n k b
  let ca : A ⟶ (ihom X).obj Y :=
    MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k a)
  let cb : B ⟶ (ihom X).obj Y :=
    MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k b)
  have hBase : l ≫ ga = r ≫ gb := symmetricOrthogonalBalance.{u, v} n k a b
  have hA : ca = ga ≫ f := orthogonalToSymmetricSourceGenerator_curry.{u, v} F n k a
  have hB : cb = gb ≫ f := orthogonalToSymmetricSourceGenerator_curry.{u, v} F n k b
  change l ≫ ca = r ≫ cb
  rw [hA, hB]
  simpa only [Category.assoc] using congrArg (fun q => q ≫ f) hBase

/-- The full concrete forgetting Hom is descended from the original sphere and isometry actions. -/
def orthogonalToSymmetricSourceHom
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) (n k : I) :
    (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
      PointedCGWH.symmetricOperatorObj.{u, v} k) ⟶
    (ihom (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len))).obj
      (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)) :=
  Enriched.weightedCoend.desc
    (Enriched.SphereOperator.weight
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k))
    PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    (fun a => MonoidalClosed.curry
      (orthogonalToSymmetricSourceGenerator.{u, v} F n k (show I from a)))
    (fun a b => orthogonalToSymmetricSourceBalance.{u, v} F n k
      (show I from a) (show I from b))

/-- Every entire concrete forgetting Hom map is exactly the full operator restriction map. -/
theorem orthogonalToSymmetricSourceHom_eq
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) (n k : I) :
    orthogonalToSymmetricSourceHom.{u, v} F n k =
    symmetricOrthogonalOperatorHomMap.{u, v} n k ≫
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len) := by
  let V := PointedCGWH.{u, v}
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight
    (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I) (R.obj n) (R.obj k)
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let H : V := Enriched.weightedCoend W S
  let K : V := OrthogonalOperatorIndex.hom.{u, v} n.of.len k.of.len
  let X : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
  let Y : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let l : H ⟶ (ihom X).obj Y := orthogonalToSymmetricSourceHom.{u, v} F n k
  let m : H ⟶ K := symmetricOrthogonalOperatorHomMap.{u, v} n k
  let f : K ⟶ (ihom X).obj Y := F.toEnrichedFunctor.map
    (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  change l = m ≫ f
  apply Enriched.weightedCoend.hom_ext W S
  intro a
  let A : V := Enriched.weightedCoend.objects W S a
  let p : A ⟶ H := Enriched.weightedCoend.ι W S a
  let q : A ⟶ (ihom X).obj Y :=
    MonoidalClosed.curry (orthogonalToSymmetricSourceGenerator.{u, v} F n k (show I from a))
  let g : A ⟶ K := symmetricOrthogonalGenerator.{u, v} n k (show I from a)
  have hL : p ≫ l = q := Enriched.weightedCoend.ι_desc W S _ _ a
  have hC : q = g ≫ f := orthogonalToSymmetricSourceGenerator_curry.{u, v} F n k (show I from a)
  have hG : p ≫ m = g := symmetricOrthogonalOperatorHomMap_generator.{u, v} n k (show I from a)
  have hR : p ≫ (m ≫ f) = g ≫ f := by
    simpa only [Category.assoc] using congrArg (fun q => q ≫ f) hG
  exact hL.trans (hC.trans hR.symm)

/-- The concrete forgetting fields form a genuine spectrum functor with the original levels. -/
def orthogonalToSymmetricSourceSpectrum
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} where
  toEnrichedFunctor :=
    { obj := fun n => F.toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len)
      map := fun n k => orthogonalToSymmetricSourceHom.{u, v} F
        (show I from n.asIndex) (show I from k.asIndex)
      map_id := fun n => by
        let G := ((EnrichedFunctorCat.restriction
          symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F).toEnrichedFunctor
        let N : I := show I from n.asIndex
        have h : orthogonalToSymmetricSourceHom.{u, v} F N N = G.map n n :=
          orthogonalToSymmetricSourceHom_eq.{u, v} F N N
        exact (congrArg (fun z => eId PointedCGWH.{u, v} n ≫ z) h).trans (G.map_id n)
      map_comp := fun n k l => by
        let G := ((EnrichedFunctorCat.restriction
          symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F).toEnrichedFunctor
        let N : I := show I from n.asIndex
        let K : I := show I from k.asIndex
        let L : I := show I from l.asIndex
        have hnl : orthogonalToSymmetricSourceHom.{u, v} F N L = G.map n l :=
          orthogonalToSymmetricSourceHom_eq.{u, v} F N L
        have hnk : orthogonalToSymmetricSourceHom.{u, v} F N K = G.map n k :=
          orthogonalToSymmetricSourceHom_eq.{u, v} F N K
        have hkl : orthogonalToSymmetricSourceHom.{u, v} F K L = G.map k l :=
          orthogonalToSymmetricSourceHom_eq.{u, v} F K L
        change eComp PointedCGWH.{u, v} n k l ≫ orthogonalToSymmetricSourceHom.{u, v} F N L =
          (orthogonalToSymmetricSourceHom.{u, v} F N K ⊗ₘ
            orthogonalToSymmetricSourceHom.{u, v} F K L) ≫
            eComp PointedCGWH.{u, v} (G.obj n) (G.obj k) (G.obj l)
        rw [hnl, hnk, hkl]
        exact G.map_comp n k l }

/-- Source forgetting agrees with restriction on the entire bundled enriched spectrum. -/
theorem orthogonalToSymmetricSourceSpectrum_eq
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    orthogonalToSymmetricSourceSpectrum.{u, v} F =
      (EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F := by
  have h : (orthogonalToSymmetricSourceSpectrum.{u, v} F).toEnrichedFunctor =
      ((EnrichedFunctorCat.restriction
        symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F).toEnrichedFunctor := by
    refine EnrichedFunctor.ext PointedCGWH.{u, v}
      (F := (orthogonalToSymmetricSourceSpectrum.{u, v} F).toEnrichedFunctor)
      (G := ((EnrichedFunctorCat.restriction
        symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F).toEnrichedFunctor)
      (fun _ => rfl) ?_
    intro n k
    exact orthogonalToSymmetricSourceHom_eq.{u, v} F
      (show I from n.asIndex) (show I from k.asIndex)
  exact congrArg (fun G : EnrichedFunctor PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v} PointedCGWH.{u, v} =>
      (⟨G⟩ : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})) h

/-- Original morphism components are natural for all concrete forgetting Hom fields. -/
def orthogonalToSymmetricSourceMorphism
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}} (q : F ⟶ G) :
    orthogonalToSymmetricSourceSpectrum.{u, v} F ⟶ orthogonalToSymmetricSourceSpectrum.{u, v} G :=
  GradedNatTrans.unitOfComponents
    (fun n => EnrichedFunctorCat.component q
      (OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len)) (by
      intro n k
      have h := GradedNatTrans.uncurriedNaturality
        ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).map q) n k
      change MonoidalClosed.uncurry
          (((EnrichedFunctorCat.restriction
            symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F).toEnrichedFunctor.map n k) ≫
        EnrichedFunctorCat.component
          (EnrichedFunctorCat.restrictionMap symmetricOrthogonalOperatorIndexFunctor.{u, v} q) k =
        (EnrichedFunctorCat.component
          (EnrichedFunctorCat.restrictionMap symmetricOrthogonalOperatorIndexFunctor.{u, v} q) n ⊗ₘ
            𝟙 (n ⟶[PointedCGWH.{u, v}] k)) ≫
          MonoidalClosed.uncurry (((EnrichedFunctorCat.restriction
            symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj G).toEnrichedFunctor.map n k) at h
      rw [EnrichedFunctorCat.restrictionMap_component,
        EnrichedFunctorCat.restrictionMap_component] at h
      change MonoidalClosed.uncurry
        (orthogonalToSymmetricSourceHom.{u, v} F (show I from n.asIndex) (show I from k.asIndex)) ≫
        EnrichedFunctorCat.component q
          (OrthogonalOperatorIndex.ofIndex.{u, v} (show I from k.asIndex).of.len) =
        (EnrichedFunctorCat.component q
          (OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len) ⊗ₘ
            𝟙 (n ⟶[PointedCGWH.{u, v}] k)) ≫
          MonoidalClosed.uncurry (orthogonalToSymmetricSourceHom.{u, v} G
            (show I from n.asIndex) (show I from k.asIndex))
      rw [orthogonalToSymmetricSourceHom_eq, orthogonalToSymmetricSourceHom_eq]
      exact h)

/-- Every entire source morphism component is literally the original native component. -/
theorem orthogonalToSymmetricSourceMorphism_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}} (q : F ⟶ G)
    (n : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (orthogonalToSymmetricSourceMorphism.{u, v} q) n =
      EnrichedFunctorCat.component q
        (OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len) :=
  GradedNatTrans.unitOfComponents_component _ _ n

/-- Forgetting is the actual source functor, built from original coefficient and Hom fields. -/
def orthogonalToSymmetricSourceForget :
    EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v} where
  obj := orthogonalToSymmetricSourceSpectrum.{u, v}
  map := orthogonalToSymmetricSourceMorphism.{u, v}
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [orthogonalToSymmetricSourceMorphism_component, EnrichedFunctorCat.component_id]
    rfl
  map_comp q r := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    simp only [orthogonalToSymmetricSourceMorphism_component, EnrichedFunctorCat.component_comp]
    rfl

private theorem symmetricComponent_eqToHom
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}}
    (h : F = G) (n : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (eqToHom h) n =
      eqToHom (congrArg (fun H => H.toEnrichedFunctor.obj n) h) := by
  cases h
  exact EnrichedFunctorCat.component_id F n

/-- Restriction along the full operator index map is the concrete original forgetting functor. -/
theorem orthogonalToSymmetricSourceForget_eq_restriction :
    orthogonalToSymmetricSourceForget.{u, v} =
      EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v} := by
  refine Functor.ext (fun F => orthogonalToSymmetricSourceSpectrum_eq.{u, v} F) ?_
  intro F G q
  let SF := orthogonalToSymmetricSourceSpectrum.{u, v} F
  let SG := orthogonalToSymmetricSourceSpectrum.{u, v} G
  let RF := (EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj F
  let RG := (EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj G
  let qs : SF ⟶ SG := orthogonalToSymmetricSourceMorphism.{u, v} q
  let qr : RF ⟶ RG :=
    EnrichedFunctorCat.restrictionMap symmetricOrthogonalOperatorIndexFunctor.{u, v} q
  let f : SF ⟶ RF := eqToHom (orthogonalToSymmetricSourceSpectrum_eq.{u, v} F)
  let g : RG ⟶ SG := eqToHom (orthogonalToSymmetricSourceSpectrum_eq.{u, v} G).symm
  change qs = f ≫ qr ≫ g
  apply EnrichedFunctorCat.hom_ext
  intro n
  let N := OrthogonalOperatorIndex.ofIndex.{u, v} (show I from n.asIndex).of.len
  have hF : EnrichedFunctorCat.component f n = 𝟙 (F.toEnrichedFunctor.obj N) :=
    (symmetricComponent_eqToHom (orthogonalToSymmetricSourceSpectrum_eq.{u, v} F) n).trans (by rfl)
  have hG : EnrichedFunctorCat.component g n = 𝟙 (G.toEnrichedFunctor.obj N) :=
    (symmetricComponent_eqToHom
      (orthogonalToSymmetricSourceSpectrum_eq.{u, v} G).symm n).trans (by rfl)
  have hS : EnrichedFunctorCat.component qs n = EnrichedFunctorCat.component q N :=
    orthogonalToSymmetricSourceMorphism_component.{u, v} q n
  have hR : EnrichedFunctorCat.component qr n = EnrichedFunctorCat.component q N :=
    EnrichedFunctorCat.restrictionMap_component symmetricOrthogonalOperatorIndexFunctor.{u, v} q n
  let X := F.toEnrichedFunctor.obj N
  let Y := G.toEnrichedFunctor.obj N
  let cs : X ⟶ Y := EnrichedFunctorCat.component qs n
  let cr : X ⟶ Y := EnrichedFunctorCat.component qr n
  let cf : X ⟶ X := EnrichedFunctorCat.component f n
  let cg : Y ⟶ Y := EnrichedFunctorCat.component g n
  have hf : cf = 𝟙 X := hF
  have hg : cg = 𝟙 Y := hG
  simp only [EnrichedFunctorCat.component_comp]
  change cs = cf ≫ cr ≫ cg
  rw [hf, hg, Category.id_comp, Category.comp_id]
  exact hS.trans hR.symm

/-- The concrete generator retains the original right sphere and complete isometry action. -/
theorem orthogonalToSymmetricSourceGenerator_value
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) (n k a : I) :
    let X := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
    let H := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len
    let C := PointedCGWH.orthogonalSphere.{u, v} a.of.len
    let R := (OrthogonalSourceRightModule.restrictionFunctor.{u, v}).obj F
    orthogonalToSymmetricSourceGenerator.{u, v} F n k a =
    X ◁ (symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
      (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom) ≫
      X ◁ (β_ H C).hom ≫ (α_ X C H).inv ≫
      ((OrthogonalSourceRightModule.sphereAction.{u, v} F n.of.len a.of.len ≫
        R.toEnrichedFunctor.toOrdinaryFunctor.map
          (β_ (a.of.len : OrthogonalIndex) (n.of.len : OrthogonalIndex)).inv) ▷ H) ≫
      MonoidalClosed.uncurry (R.toEnrichedFunctor.map (a.of.len + n.of.len) k.of.len) := by
  let V := PointedCGWH.{u, v}
  let X : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
  let Y : V := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let H : V := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) k.of.len
  let C : V := PointedCGWH.orthogonalSphere.{u, v} a.of.len
  let R := (OrthogonalSourceRightModule.restrictionFunctor.{u, v}).obj F
  let A : V := PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ k) ⊗
    PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let m : A ⟶ H ⊗ C := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) k ⊗ₘ
    (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let r : X ⊗ (H ⊗ C) ⟶ Y :=
    OrthogonalSourceRightModule.recoveredGenerator.{u, v} F n.of.len k.of.len a.of.len
  let c : X ⊗ C ⟶ F.toEnrichedFunctor.obj
      (OrthogonalOperatorIndex.ofIndex.{u, v} (a.of.len + n.of.len)) :=
    OrthogonalSourceRightModule.coefficientFromRightSphere.{u, v} F n.of.len a.of.len
  let e : F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v}
      (a.of.len + n.of.len)) ⊗ H ⟶ Y :=
    MonoidalClosed.uncurry (R.toEnrichedFunctor.map (a.of.len + n.of.len) k.of.len)
  let t : X ⊗ C ⟶ F.toEnrichedFunctor.obj
      (OrthogonalOperatorIndex.ofIndex.{u, v} (a.of.len + n.of.len)) :=
    OrthogonalSourceRightModule.sphereAction.{u, v} F n.of.len a.of.len ≫
      R.toEnrichedFunctor.toOrdinaryFunctor.map
        (β_ (a.of.len : OrthogonalIndex) (n.of.len : OrthogonalIndex)).inv
  have hr : r = X ◁ (β_ H C).hom ≫ (α_ X C H).inv ≫ (c ▷ H) ≫ e :=
    OrthogonalSourceRightModule.recoveredGenerator_value.{u, v} F n.of.len k.of.len a.of.len
  have hc : c = t :=
    OrthogonalSourceRightModule.coefficientFromRightSphere_value.{u, v} F n.of.len a.of.len
  rw [hc] at hr
  change X ◁ m ≫ r = X ◁ m ≫ X ◁ (β_ H C).hom ≫ (α_ X C H).inv ≫
    (t ▷ H) ≫ e
  simpa only [Category.assoc] using congrArg (fun q => X ◁ m ≫ q) hr

end CategoryTheory.Spectra.SpectrumIndexMaps

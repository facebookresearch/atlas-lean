/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceIntersection
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Data.Fintype.Option

/-!
# Bounded compatible idempotents on original lower cell trees

An idempotent at a good tree's endpoint and an original stable lower support
extend to compatible idempotents on a bounded lower enlargement of any small
label set and its literal intersection with that support. The inclusions,
root maps and endpoint maps are the original ones.

This finite-index specialization of compatible diagram intersections gives
the fixed-geometry form of Lurie's `Higher Topos Theory`, Lemma A.1.5.9.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject CategoryTheory.SmallObject.DiagramSliceExhaustion

universe w t u v

namespace CategoryTheory.SmallObject.IdempotentIntersection

private abbrev Idem := WithZero PUnit.{1}
private abbrev Index := SingleObj Idem

variable {C : Type u} [Category.{v} C]

-- This is a monoid homomorphism, not a zero-preserving coefficient map.
private def idempotentHom {Z : C} (q : Z ⟶ Z) (hq : q ≫ q = q) :
    Idem →* End Z where
  toFun := WithZero.recZeroCoe (End.of q) (fun _ => 1)
  map_one' := rfl
  map_mul' := fun
    | 0, 0 => by
      apply End.ext
      change q = q ≫ q
      exact hq.symm
    | 0, (_ : PUnit.{1}) => by
      apply End.ext
      change q = 𝟙 Z ≫ q
      exact (Category.id_comp q).symm
    | (_ : PUnit.{1}), 0 => by
      apply End.ext
      change q = q ≫ 𝟙 Z
      exact (Category.comp_id q).symm
    | (_ : PUnit.{1}), (_ : PUnit.{1}) => by
      apply End.ext
      change 𝟙 Z = 𝟙 Z ≫ 𝟙 Z
      exact (Category.id_comp (𝟙 Z)).symm

private def idempotentFunctor {Z : C} (q : Z ⟶ Z) (hq : q ≫ q = q) : Index ⥤ C :=
  SingleObj.functor (idempotentHom q hq)

private theorem idempotentFunctor_zero {Z : C} (q : Z ⟶ Z) (hq : q ≫ q = q) :
    (idempotentFunctor q hq).map (SingleObj.toEnd Idem (0 : Idem)).asHom = q := rfl

private theorem idempotentFunctor_one {Z : C} (q : Z ⟶ Z) (hq : q ≫ q = q) :
    (idempotentFunctor q hq).map (𝟙 (SingleObj.star Idem)) = 𝟙 Z := rfl

-- Original under-root maps retain root naturality through their actual Under.w law.
private def rootTransformation {X : C} {Z : Under X} (q : Z ⟶ Z) (hq : q ≫ q = q) :
    (Functor.const Index).obj X ⟶ idempotentFunctor q hq ⋙ Under.forget X where
  app _ := Z.hom
  naturality _ _ a := by
    change 𝟙 X ≫ Z.hom = Z.hom ≫ ((idempotentFunctor q hq).map a).right
    exact (Category.id_comp _).trans (Under.w ((idempotentFunctor q hq).map a)).symm

private def idempotentComparison {X : C} {Z W : Under X}
    (qZ : Z ⟶ Z) (hqZ : qZ ≫ qZ = qZ)
    (qW : W ⟶ W) (hqW : qW ≫ qW = qW)
    (a : Z ⟶ W) (ha : qZ ≫ a = a ≫ qW) :
    idempotentFunctor qZ hqZ ⟶ idempotentFunctor qW hqW :=
  SingleObj.natTrans a (fun
    | 0 => ha
    | (_ : PUnit.{1}) => (Category.id_comp a).trans (Category.comp_id a).symm)

variable {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj) (hq : q ≫ q = q)

private def presentation :
    PointwiseCellTreePresentation (s := s) (rootTransformation q hq) (fun _ : Index => P) where
  component _ := { tree := T, endpointIso := Iso.refl _ }

private abbrev lowerData (d : Index) :
    LowerSetColimitData ((presentation T q hq).component d).tree.diagram := L

private theorem originalLeg (d : Index) (B : LowerSet P) :
    DiagramActionCapture.legUnder (presentation T q hq) (lowerData T L q hq) d B =
      (L.map (le_top : B ≤ ⊤)) ≫ (T.endpointIso L).hom := by
  change (L.map le_top ≫ (T.endpointIso L).hom) ≫ 𝟙 T.endpointObj = _
  exact Category.comp_id _

private theorem indexArrows_lt (chi : Cardinal.{w}) (hchi : Cardinal.aleph0 < chi) :
    HasCardinalLT (Arrow Index) chi := by
  let _ : Fintype Idem := by
    change Fintype (Option PUnit.{1})
    infer_instance
  let _ : FinCategory Index := SingleObj.finCategoryOfFintype Idem
  let _ : Finite (Arrow Index) :=
    Finite.of_equiv (Σ d e : Index, d ⟶ e) (Arrow.equivSigma (T := Index)).symm
  exact hasCardinalLT_of_finite (Arrow Index) chi hchi.le

private def stableSlice (B : LowerSet P) (qB : L.obj B ⟶ L.obj B)
    (hqB : qB ≫ qB = qB)
    (hB : qB ≫ (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) =
      (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q) :
    OriginalSlice (presentation T q hq) (lowerData T L q hq) where
  supports _ := B
  map a := ((idempotentFunctor qB hqB).map a).right
  map_id d := congrArg Under.Hom.right ((idempotentFunctor qB hqB).map_id d)
  map_comp a b := congrArg Under.Hom.right ((idempotentFunctor qB hqB).map_comp a b)
  map_root a := by
    change (L.obj B).hom ≫ ((idempotentFunctor qB hqB).map a).right = 𝟙 X ≫ (L.obj B).hom
    exact (Under.w ((idempotentFunctor qB hqB).map a)).trans (Category.id_comp _).symm
  map_endpoint {d e} a := by
    let h := idempotentComparison qB hqB q hq
      (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) hB
    have hh := congrArg Under.Hom.right (h.naturality a)
    change ((idempotentFunctor qB hqB).map a).right ≫
        (DiagramActionCapture.legUnder (presentation T q hq) (lowerData T L q hq) e B).right =
      (DiagramActionCapture.legUnder (presentation T q hq) (lowerData T L q hq) d B).right ≫
        ((idempotentFunctor q hq).map a).right
    rw [originalLeg T L q hq e B, originalLeg T L q hq d B]
    exact hh

private def closedSeed (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (good : T.IsGood chi) (C0 : Set P) (hC0 : HasCardinalLT C0 chi) :
    BoundedLowerSupport.Carrier (P := P) chi :=
  BoundedLowerSupport.indexedUnion chi
    (fun p : C0 => BoundedLowerSupport.principal chi good.predecessor_lt p.1) hC0

private theorem closedSeed_contains (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (good : T.IsGood chi) (C0 : Set P) (hC0 : HasCardinalLT C0 chi) :
    C0 ⊆ (closedSeed T chi good C0 hC0).1 := by
  intro p hp
  have h := BoundedLowerSupport.le_indexedUnion chi
    (fun p : C0 => BoundedLowerSupport.principal chi good.predecessor_lt p.1) hC0 ⟨p, hp⟩
  exact h (show p ∈ LowerSet.Iic p from le_rfl)

private def zeroArrow : SingleObj.star Idem ⟶ SingleObj.star Idem :=
  (SingleObj.toEnd Idem (0 : Idem)).asHom

private theorem zeroArrow_comp : zeroArrow ≫ zeroArrow = zeroArrow := by
  change (0 : Idem) * (0 : Idem) = 0
  exact zero_mul _

private def sliceIdempotent (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (S : DiagramSliceExtensions.Slice (presentation T q hq) (lowerData T L q hq) chi) :
    L.obj (S.supports (SingleObj.star Idem)).1 ⟶
      L.obj (S.supports (SingleObj.star Idem)).1 :=
  Under.homMk (S.map zeroArrow) (by
    have h := S.map_root zeroArrow
    change (L.obj (S.supports (SingleObj.star Idem)).1).hom ≫ S.map zeroArrow =
      𝟙 X ≫ (L.obj (S.supports (SingleObj.star Idem)).1).hom at h
    exact h.trans (Category.id_comp _))

private theorem sliceIdempotent_comp (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (S : DiagramSliceExtensions.Slice (presentation T q hq) (lowerData T L q hq) chi) :
    sliceIdempotent T L q hq chi S ≫ sliceIdempotent T L q hq chi S =
      sliceIdempotent T L q hq chi S := by
  apply Under.UnderMorphism.ext
  change S.map zeroArrow ≫ S.map zeroArrow = S.map zeroArrow
  have h := S.map_comp zeroArrow zeroArrow
  rw [zeroArrow_comp] at h
  exact h.symm

private theorem sliceIdempotent_endpoint (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (S : DiagramSliceExtensions.Slice (presentation T q hq) (lowerData T L q hq) chi) :
    sliceIdempotent T L q hq chi S ≫
        (L.map (le_top : (S.supports (SingleObj.star Idem)).1 ≤ ⊤) ≫ (T.endpointIso L).hom) =
      (L.map (le_top : (S.supports (SingleObj.star Idem)).1 ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q := by
  apply Under.UnderMorphism.ext
  have h := S.map_endpoint zeroArrow
  rw [show DiagramActionCapture.leg (presentation T q hq) (lowerData T L q hq)
      (SingleObj.star Idem) (S.supports (SingleObj.star Idem)).1 =
        (L.map le_top ≫ (T.endpointIso L).hom).right from
      congrArg Under.Hom.right
        (originalLeg T L q hq (SingleObj.star Idem) (S.supports (SingleObj.star Idem)).1)] at h
  exact h

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]

include hq in
private theorem existsIntermediate (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
    (B : LowerSet P) (qB : L.obj B ⟶ L.obj B) (hqB : qB ≫ qB = qB)
    (hB : qB ≫ (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) =
      (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q)
    (C0 : Set P) (hC0 : HasCardinalLT C0 chi) :
    ∃ (U V : LowerSet P), C0 ⊆ U ∧ HasCardinalLT (U : Set P) chi ∧ V = B ⊓ U ∧
      HasCardinalLT (V : Set P) chi ∧
      ∃ (hVB : V ≤ B) (hVU : V ≤ U)
        (eU : L.obj U ⟶ L.obj U) (eV : L.obj V ⟶ L.obj V),
        eU ≫ eU = eU ∧ eV ≫ eV = eV ∧
        eV ≫ L.map hVB = L.map hVB ≫ qB ∧
        eV ≫ L.map hVU = L.map hVU ≫ eU ∧
        eU ≫ (L.map (le_top : U ≤ ⊤) ≫ (T.endpointIso L).hom) =
          (L.map (le_top : U ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q ∧
        eV ≫ (L.map (le_top : V ≤ ⊤) ≫ (T.endpointIso L).hom) =
          (L.map (le_top : V ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q := by
  let theta := presentation T q hq
  let A := stableSlice T L q hq B qB hqB hB
  let seed : DiagramActionCapture.Supports (P := fun _ : Index => P) chi :=
    fun _ => closedSeed T chi good C0 hC0
  obtain ⟨N, Nprime, hseed, hlabels, ⟨pB⟩, ⟨pN⟩⟩ :=
    DiagramSliceIntersection.existsGenericBoundedCompatibleIntersection theta
      (lowerData T L q hq) A chi hUncountable (indexArrows_lt chi hUncountable)
      (fun _ => good) seed
  let U := (N.supports (SingleObj.star Idem)).1
  let V := (Nprime.supports (SingleObj.star Idem)).1
  let eU := sliceIdempotent T L q hq chi N
  let eV := sliceIdempotent T L q hq chi Nprime
  refine ⟨U, V, ?_, (N.supports (SingleObj.star Idem)).2,
    hlabels (SingleObj.star Idem), (Nprime.supports (SingleObj.star Idem)).2,
    pB.le (SingleObj.star Idem), pN.le (SingleObj.star Idem), eU, eV,
    sliceIdempotent_comp T L q hq chi N, sliceIdempotent_comp T L q hq chi Nprime,
    ?_, ?_, sliceIdempotent_endpoint T L q hq chi N,
    sliceIdempotent_endpoint T L q hq chi Nprime⟩
  · exact (closedSeed_contains T chi good C0 hC0).trans (hseed (SingleObj.star Idem))
  · apply Under.UnderMorphism.ext
    exact (pB.naturality zeroArrow).symm
  · apply Under.UnderMorphism.ext
    exact (pN.naturality zeroArrow).symm

include hq in
/-- Every original small subset has a bounded lower enlargement whose literal
intersection with an original stable lower tree carries its actual idempotent.
All comparisons retain the original root and endpoint maps. -/
theorem existsIdempotentIntersection (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
    (B : LowerSet P) (qB : L.obj B ⟶ L.obj B) (hqB : qB ≫ qB = qB)
    (hB : qB ≫ (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) =
      (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q)
    (C0 : Set P) (hC0 : HasCardinalLT C0 chi) :
    ∃ (U : LowerSet P), C0 ⊆ U ∧ HasCardinalLT (U : Set P) chi ∧
      HasCardinalLT ((B ⊓ U : LowerSet P) : Set P) chi ∧
      ∃ (eU : L.obj U ⟶ L.obj U) (eBU : L.obj (B ⊓ U) ⟶ L.obj (B ⊓ U)),
        eU ≫ eU = eU ∧ eBU ≫ eBU = eBU ∧
        eBU ≫ L.map (inf_le_left : B ⊓ U ≤ B) = L.map inf_le_left ≫ qB ∧
        eBU ≫ L.map (inf_le_right : B ⊓ U ≤ U) = L.map inf_le_right ≫ eU ∧
        eU ≫ (L.map (le_top : U ≤ ⊤) ≫ (T.endpointIso L).hom) =
          (L.map (le_top : U ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q ∧
        eBU ≫ (L.map (le_top : B ⊓ U ≤ ⊤) ≫ (T.endpointIso L).hom) =
          (L.map (le_top : B ⊓ U ≤ ⊤) ≫ (T.endpointIso L).hom) ≫ q := by
  obtain ⟨U, V, hC0U, hU, hV, hVsmall, hVB, hVU, eU, eV,
    heU, heV, heVB, heVU, heUEnd, heVEnd⟩ :=
      existsIntermediate T L q hq chi hUncountable good B qB hqB hB C0 hC0
  subst V
  exact ⟨U, hC0U, hU, hVsmall, eU, eV, heU, heV, heVB, heVU, heUEnd, heVEnd⟩

end CategoryTheory.SmallObject.IdempotentIntersection

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic
public import MathlibExt.Topology.Category.CompactlyGenerated.QuotientProduct
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Weak-Hausdorff reflection

The weak-Hausdorff reflection of a compactly generated space is its quotient
by the smallest closed equivalence relation in the native compactly generated
product.
-/

public section

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
open scoped Relator

namespace CGWH

end CGWH

namespace CompactlyGenerated

private noncomputable def binaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) ≅ X ⊗ Y := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt : Type v) ≃ₜ
        ↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y) :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun s => CartesianMonoidalCategory.lift
            (s.π.app ⟨ULift.up WalkingPair.left⟩)
            (s.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro s ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro s m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  exact
    TopCat.toCompactlyGenerated.mapIso
        (TopCat.isoOfHomeo hp.symm) ≪≫
      (piIsoPi PF).symm ≪≫ eTensor

private theorem binaryKificationIso_hom_proj
    (X Y : CompactlyGenerated.{u, v}) :
    ((binaryKificationIso X Y).hom ≫
          CartesianMonoidalCategory.fst X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodFst : TopCat.of
              (↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj X) ≫
          (asIso (adj.unit.app X)).inv) ∧
      ((binaryKificationIso X Y).hom ≫
          CartesianMonoidalCategory.snd X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodSnd : TopCat.of
              (↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj Y) ≫
          (asIso (adj.unit.app Y)).inv) := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt : Type v) ≃ₜ
        ↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y) :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun s => CartesianMonoidalCategory.lift
            (s.π.app ⟨ULift.up WalkingPair.left⟩)
            (s.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro s ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro s m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  constructor
  · let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
        (TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt :=
      (TopCat.isoOfHomeo hp.symm).hom
    have hRaw : h ≫ (TopCat.piFan (fun j => compactlyGeneratedToTop.obj
        (PF j))).π.app
        ⟨ULift.up WalkingPair.left⟩ = TopCat.prodFst := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : eTensor.hom ≫
        CartesianMonoidalCategory.fst X Y =
      Pi.π PF (ULift.up WalkingPair.left) := by
      apply (cancel_epi eTensor.inv).1
      simp [eTensor]
    have hPi : (piIsoPi PF).symm.hom ≫
          Pi.π PF (ULift.up WalkingPair.left) =
        piπ PF (ULift.up WalkingPair.left) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit PF)
        ⟨ULift.up WalkingPair.left⟩
    simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    calc
      _ = TopCat.toCompactlyGenerated.map h ≫
          piπ PF (ULift.up WalkingPair.left) := rfl
      _ = _ := by
        unfold piπ
        rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
  · let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
        (TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt :=
      (TopCat.isoOfHomeo hp.symm).hom
    have hRaw : h ≫ (TopCat.piFan (fun j => compactlyGeneratedToTop.obj
        (PF j))).π.app
        ⟨ULift.up WalkingPair.right⟩ = TopCat.prodSnd := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : eTensor.hom ≫
        CartesianMonoidalCategory.snd X Y =
      Pi.π PF (ULift.up WalkingPair.right) := by
      apply (cancel_epi eTensor.inv).1
      simp [eTensor]
    have hPi : (piIsoPi PF).symm.hom ≫
          Pi.π PF (ULift.up WalkingPair.right) =
        piπ PF (ULift.up WalkingPair.right) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit PF)
        ⟨ULift.up WalkingPair.right⟩
    simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    calc
      _ = TopCat.toCompactlyGenerated.map h ≫
          piπ PF (ULift.up WalkingPair.right) := rfl
      _ = _ := by
        unfold piπ
        rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]

end CompactlyGenerated

namespace CGWH

private theorem continuous_to_kified_max
    {S : Type w} {T : Type v}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} S]
    {h : S → T} (hh : Continuous h) :
    @Continuous S T inferInstance
      (TopologicalSpace.compactlyGenerated.{u} T) h := by
  apply continuous_from_uCompactlyGeneratedSpace.{u, w, v}
    (tY := TopologicalSpace.compactlyGenerated.{u} T) h
  intro K g
  rw [TopologicalSpace.compactlyGenerated]
  let q : @ContinuousMap K T _ tT :=
    ⟨h ∘ g, hh.comp g.continuous⟩
  let ev :
      (Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst) → T :=
    fun ⟨⟨_, i⟩, x⟩ => i x
  change @Continuous K T inferInstance
    (TopologicalSpace.coinduced ev inferInstance)
    (fun x => ev ⟨⟨K, q⟩, x⟩)
  have hmk : Continuous (fun x : K =>
      (⟨⟨K, q⟩, x⟩ :
        Σ (i : (L : CompHaus.{u}) × @ContinuousMap L T _ tT), i.fst)) :=
    continuous_sigmaMk
      (ι := (L : CompHaus.{u}) × @ContinuousMap L T _ tT)
      (σ := fun i => i.fst) (i := ⟨K, q⟩)
  let _ : TopologicalSpace T :=
    TopologicalSpace.coinduced ev inferInstance
  have hev : Continuous ev := continuous_coinduced_rng
  exact hev.comp hmk

end CGWH

namespace CompactlyGenerated

/-- A compactly generated space is weak Hausdorff exactly when its diagonal
is closed in the native compactly generated square. -/
theorem uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
    (X : CompactlyGenerated.{u, v}) :
    UWeakHausdorffSpace.{u} X ↔
      IsClosed {p : ↥((X ⊗ X).toTop) |
        CartesianMonoidalCategory.fst X X p =
          CartesianMonoidalCategory.snd X X p} := by
  constructor
  · intro hX
    let _ : UWeakHausdorffSpace.{u} X := hX
    let _ : UCompactlyGeneratedSpace.{u}
        ↥((X ⊗ X).toTop) :=
      (X ⊗ X).is_compactly_generated
    apply UCompactlyGeneratedSpace.isClosed
    intro K a
    let f : C(K, X) :=
      (ConcreteCategory.hom (CartesianMonoidalCategory.fst X X)).comp a
    let g : C(K, X) :=
      (ConcreteCategory.hom (CartesianMonoidalCategory.snd X X)).comp a
    have hfg : IsClosed {k : K | f k = g k} :=
      (uWeakHausdorffSpace_iff_isClosed_equalizer.mp hX) K f g
    change IsClosed {k : K |
      CartesianMonoidalCategory.fst X X (a k) =
        CartesianMonoidalCategory.snd X X (a k)}
    change IsClosed {k : K |
      CartesianMonoidalCategory.fst X X (a k) =
        CartesianMonoidalCategory.snd X X (a k)} at hfg
    exact hfg
  · intro hdiag
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K f g
    let _ : UCompactlyGeneratedSpace.{u} K :=
      uCompactlyGeneratedSpace_of_continuous_maps (fun h hh => by
        simpa using hh K (ContinuousMap.id K))
    let e := CompactlyGenerated.binaryKificationIso X X
    let raw : K → (↥X.toTop × ↥X.toTop) :=
      fun k => (f k, g k)
    have hRaw : Continuous raw := f.continuous.prodMk g.continuous
    have hKified : @Continuous K (↥X.toTop × ↥X.toTop)
        inferInstance (TopologicalSpace.compactlyGenerated.{u} _) raw :=
      CGWH.continuous_to_kified_max hRaw
    let RawPair : TopCat.{v} :=
      TopCat.of (↥X.toTop × ↥X.toTop)
    have hKified' : @Continuous K
        (↥X.toTop × ↥X.toTop)
        inferInstance
        (TopCat.toCompactlyGenerated.obj RawPair).toTop.str raw := by
      have ht : (TopCat.toCompactlyGenerated.obj RawPair).toTop.str =
          TopologicalSpace.compactlyGenerated.{u}
            (↥X.toTop × ↥X.toTop) := by
        change TopologicalSpace.generatedBy
          CompactlyGenerated.compactHausProbes (Y :=
          ↥X.toTop × ↥X.toTop) = _
        exact
          TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
      rw [ht]
      exact hKified
    let a : C(K, ↥((X ⊗ X).toTop)) :=
      ⟨fun k => e.hom (raw k),
        (ConcreteCategory.hom e.hom).continuous.comp hKified'⟩
    have hInvUnit (x : X) :
        (asIso (CompactlyGenerated.adj.unit.app X)).inv x = x := by
      have h := (asIso
        (CompactlyGenerated.adj.unit.app X)).hom_inv_id_apply x
      change (asIso (CompactlyGenerated.adj.unit.app X)).inv x = x at h
      exact h
    have e_fst (x y : X) :
        CartesianMonoidalCategory.fst X X (e.hom (x, y)) = x := by
      have h := ConcreteCategory.congr_hom
        (CompactlyGenerated.binaryKificationIso_hom_proj X X).1 (x, y)
      change CartesianMonoidalCategory.fst X X (e.hom (x, y)) =
        (asIso (CompactlyGenerated.adj.unit.app X)).inv x at h
      simpa only [hInvUnit] using h
    have e_snd (x y : X) :
        CartesianMonoidalCategory.snd X X (e.hom (x, y)) = y := by
      have h := ConcreteCategory.congr_hom
        (CompactlyGenerated.binaryKificationIso_hom_proj X X).2 (x, y)
      change CartesianMonoidalCategory.snd X X (e.hom (x, y)) =
        (asIso (CompactlyGenerated.adj.unit.app X)).inv y at h
      simpa only [hInvUnit] using h
    have hpre := hdiag.preimage a.continuous
    change IsClosed {k : K |
      CartesianMonoidalCategory.fst X X (a k) =
        CartesianMonoidalCategory.snd X X (a k)} at hpre
    have hfst (k : K) :
        CartesianMonoidalCategory.fst X X (a k) = f k := by
      change CartesianMonoidalCategory.fst X X
        (e.hom (f k, g k)) = f k
      exact e_fst _ _
    have hsnd (k : K) :
        CartesianMonoidalCategory.snd X X (a k) = g k := by
      change CartesianMonoidalCategory.snd X X
        (e.hom (f k, g k)) = g k
      exact e_snd _ _
    rw [show {k : K |
        CartesianMonoidalCategory.fst X X (a k) =
          CartesianMonoidalCategory.snd X X (a k)} =
        {k : K | f k = g k} by
      ext k
      change (CartesianMonoidalCategory.fst X X (a k) =
        CartesianMonoidalCategory.snd X X (a k)) ↔ f k = g k
      rw [hfst, hsnd]] at hpre
    exact hpre

end CompactlyGenerated

namespace CGWH

/-- A setoid is closed when its relation is closed in the native compactly
generated square. -/
@[expose] def closedEquivalenceRelation
    (X : CompactlyGenerated.{u, v})
    (s : Setoid ↥X.toTop) : Prop :=
  IsClosed {p : ↥((X ⊗ X).toTop) |
    s (CartesianMonoidalCategory.fst X X p)
      (CartesianMonoidalCategory.snd X X p)}

private theorem smallestClosedRelation_iff
    (X : CompactlyGenerated.{u, v})
    (x y : ↥X.toTop) :
    sInf {s : Setoid ↥X.toTop |
      closedEquivalenceRelation X s} x y ↔
      ∀ s : Setoid ↥X.toTop,
        closedEquivalenceRelation X s → s x y := by
  simp only [Setoid.sInf_iff, Set.mem_ofPred_eq]

/-- The smallest closed equivalence relation on a compactly generated
space. -/
noncomputable def smallestClosedEquivalenceRelation
    (X : CompactlyGenerated.{u, v}) :
    {s : Setoid ↥X.toTop //
      closedEquivalenceRelation X s} := by
  let S : Set (Setoid ↥X.toTop) :=
    {s | closedEquivalenceRelation X s}
  refine ⟨sInf S, ?_⟩
  unfold closedEquivalenceRelation
  rw [show {p : ↥((X ⊗ X).toTop) |
      sInf S (CartesianMonoidalCategory.fst X X p)
        (CartesianMonoidalCategory.snd X X p)} =
      ⋂ R : {s : Setoid ↥X.toTop //
          closedEquivalenceRelation X s},
        {p : ↥((X ⊗ X).toTop) |
          R.1 (CartesianMonoidalCategory.fst X X p)
            (CartesianMonoidalCategory.snd X X p)} by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h R
      exact h R.1 R.2
    · intro h s hs
      exact h ⟨s, hs⟩]
  exact isClosed_iInter (fun R => R.2)

/-- A quotient of a compactly generated space is weak Hausdorff exactly when
its defining relation is closed in the native square. -/
theorem quotient_isWeakHausdorff_iff_isClosed
    (X : CompactlyGenerated.{u, v}) (s : Setoid ↥X.toTop) :
    UWeakHausdorffSpace.{u} (Quotient s) ↔
      closedEquivalenceRelation X s := by
  let _ : UCompactlyGeneratedSpace.{u} ↥X.toTop :=
    X.is_compactly_generated
  let Q : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of (Quotient s)
  let q : X ⟶ Q := ConcreteCategory.ofHom
    ⟨(@Quotient.mk' _ s), continuous_quotient_mk'⟩
  let q2 : X ⊗ X ⟶ Q ⊗ Q := q ⊗ₘ q
  let diagonal : Set ↥((Q ⊗ Q).toTop) :=
    {p | CartesianMonoidalCategory.fst Q Q p =
      CartesianMonoidalCategory.snd Q Q p}
  let relation : Set ↥((X ⊗ X).toTop) :=
    {p | s (CartesianMonoidalCategory.fst X X p)
      (CartesianMonoidalCategory.snd X X p)}
  have hq2 : IsQuotientMap (ConcreteCategory.hom q2) :=
    CompactlyGenerated.prodQuotientMap q q
      isQuotientMap_quotient_mk' isQuotientMap_quotient_mk'
  have hfst (p : ↥((X ⊗ X).toTop)) :
      CartesianMonoidalCategory.fst Q Q (q2 p) =
        (@Quotient.mk' _ s) (CartesianMonoidalCategory.fst X X p) := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst q q) p
    exact h
  have hsnd (p : ↥((X ⊗ X).toTop)) :
      CartesianMonoidalCategory.snd Q Q (q2 p) =
        (@Quotient.mk' _ s) (CartesianMonoidalCategory.snd X X p) := by
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd q q) p
    exact h
  have hpreimage : (ConcreteCategory.hom q2) ⁻¹' diagonal = relation := by
    ext p
    change (CartesianMonoidalCategory.fst Q Q (q2 p) =
      CartesianMonoidalCategory.snd Q Q (q2 p)) ↔
        s (CartesianMonoidalCategory.fst X X p)
          (CartesianMonoidalCategory.snd X X p)
    rw [hfst, hsnd]
    exact Quotient.eq
  constructor
  · intro hQ
    have hdiag : IsClosed diagonal :=
      (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
        Q).mp hQ
    unfold closedEquivalenceRelation
    change IsClosed relation
    rw [← hpreimage]
    exact hdiag.preimage (ConcreteCategory.hom q2).continuous
  · intro hs
    have hrel : IsClosed relation := by
      unfold closedEquivalenceRelation at hs
      exact hs
    have hpre : IsClosed ((ConcreteCategory.hom q2) ⁻¹' diagonal) := by
      rw [hpreimage]
      exact hrel
    have hdiag : IsClosed diagonal :=
      hq2.isCoinducing.isClosed_preimage.mp hpre
    exact
      (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
        Q).mpr hdiag

private noncomputable def weakHausdorffificationObj
    (X : CompactlyGenerated.{u, v}) : CGWH.{u, v} := by
  let s := smallestClosedEquivalenceRelation X
  let _ : UCompactlyGeneratedSpace.{u} (Quotient s.1) := inferInstance
  let _ : UWeakHausdorffSpace.{u} (Quotient s.1) :=
    (quotient_isWeakHausdorff_iff_isClosed X s.1).mpr s.2
  exact CGWH.of (Quotient s.1)

/-- The weak-Hausdorff reflection functor. -/
noncomputable def weakHausdorffification :
    CompactlyGenerated.{u, v} ⥤ CGWH.{u, v} where
  obj X := weakHausdorffificationObj X
  map {X Y} f := by
    let sX := smallestClosedEquivalenceRelation X
    let sY := smallestClosedEquivalenceRelation Y
    let f2 : X ⊗ X ⟶ Y ⊗ Y := f ⊗ₘ f
    have hfst (p : ↥((X ⊗ X).toTop)) :
        CartesianMonoidalCategory.fst Y Y (f2 p) =
          f (CartesianMonoidalCategory.fst X X p) := by
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.tensorHom_fst f f) p
    have hsnd (p : ↥((X ⊗ X).toTop)) :
        CartesianMonoidalCategory.snd Y Y (f2 p) =
          f (CartesianMonoidalCategory.snd X X p) := by
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.tensorHom_snd f f) p
    have hcomap : closedEquivalenceRelation X
        (Setoid.comap f sY.1) := by
      unfold closedEquivalenceRelation
      rw [show {p : ↥((X ⊗ X).toTop) |
          Setoid.comap f sY.1
            (CartesianMonoidalCategory.fst X X p)
            (CartesianMonoidalCategory.snd X X p)} =
          (ConcreteCategory.hom f2) ⁻¹'
            {p : ↥((Y ⊗ Y).toTop) |
              sY.1 (CartesianMonoidalCategory.fst Y Y p)
                (CartesianMonoidalCategory.snd Y Y p)} by
        ext p
        change sY.1 (f (CartesianMonoidalCategory.fst X X p))
            (f (CartesianMonoidalCategory.snd X X p)) ↔
          sY.1 (CartesianMonoidalCategory.fst Y Y (f2 p))
            (CartesianMonoidalCategory.snd Y Y (f2 p))
        rw [hfst, hsnd]]
      exact sY.2.preimage (ConcreteCategory.hom f2).continuous
    have hle : sX.1 ≤ Setoid.comap f sY.1 := by
      change sInf {s : Setoid ↥X.toTop |
        closedEquivalenceRelation X s} ≤ Setoid.comap f sY.1
      exact sInf_le hcomap
    have hrel : (sX.1.r ⇒ sY.1.r) f f :=
      fun _ _ h => hle h
    exact ConcreteCategory.ofHom
      ⟨Quotient.map' f hrel,
        (ConcreteCategory.hom f).continuous.quotient_map'
          (s := sX.1) (t := sY.1) hrel⟩
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro q
    induction q using Quotient.inductionOn'
    rfl
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    induction q using Quotient.inductionOn'
    rfl

private noncomputable def reflectionProjection
    (X : CompactlyGenerated.{u, v}) :
    X ⟶ cgwhToCompactlyGenerated.obj (weakHausdorffification.obj X) :=
  ConcreteCategory.ofHom
    ⟨(@Quotient.mk' _ (smallestClosedEquivalenceRelation X).1),
      continuous_quotient_mk'⟩

private noncomputable def reflectionCoreHomEquiv :
    Adjunction.CoreHomEquiv weakHausdorffification
      cgwhToCompactlyGenerated := by
  let E (X : CompactlyGenerated.{u, v}) (Y : CGWH.{u, v}) :
      (weakHausdorffification.obj X ⟶ Y) ≃
        (X ⟶ cgwhToCompactlyGenerated.obj Y) := by
    let s := smallestClosedEquivalenceRelation X
    let q := reflectionProjection X
    let lift (f : X ⟶ cgwhToCompactlyGenerated.obj Y) :
        weakHausdorffification.obj X ⟶ Y := by
      let Y' : CompactlyGenerated.{u, v} :=
        cgwhToCompactlyGenerated.obj Y
      let _ : UWeakHausdorffSpace.{u} ↥Y'.toTop :=
        Y.is_weakHausdorff
      let f2 : X ⊗ X ⟶ Y' ⊗ Y' := f ⊗ₘ f
      have hfst (p : ↥((X ⊗ X).toTop)) :
          CartesianMonoidalCategory.fst Y' Y' (f2 p) =
            f (CartesianMonoidalCategory.fst X X p) := by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst f f) p
      have hsnd (p : ↥((X ⊗ X).toTop)) :
          CartesianMonoidalCategory.snd Y' Y' (f2 p) =
            f (CartesianMonoidalCategory.snd X X p) := by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd f f) p
      have hdiag : IsClosed
          {p : ↥((Y' ⊗ Y').toTop) |
            CartesianMonoidalCategory.fst Y' Y' p =
              CartesianMonoidalCategory.snd Y' Y' p} :=
        (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
          Y').mp inferInstance
      have hker : closedEquivalenceRelation X
          (Setoid.ker f) := by
        unfold closedEquivalenceRelation
        rw [show {p : ↥((X ⊗ X).toTop) |
            Setoid.ker f (CartesianMonoidalCategory.fst X X p)
              (CartesianMonoidalCategory.snd X X p)} =
            (ConcreteCategory.hom f2) ⁻¹'
              {p : ↥((Y' ⊗ Y').toTop) |
                CartesianMonoidalCategory.fst Y' Y' p =
                  CartesianMonoidalCategory.snd Y' Y' p} by
          ext p
          change (f (CartesianMonoidalCategory.fst X X p) =
              f (CartesianMonoidalCategory.snd X X p)) ↔
            CartesianMonoidalCategory.fst Y' Y' (f2 p) =
              CartesianMonoidalCategory.snd Y' Y' (f2 p)
          rw [hfst, hsnd]]
        exact hdiag.preimage (ConcreteCategory.hom f2).continuous
      have hle : s.1 ≤ Setoid.ker f := by
        change sInf {t : Setoid ↥X.toTop |
          closedEquivalenceRelation X t} ≤ Setoid.ker f
        exact sInf_le hker
      exact ConcreteCategory.ofHom
        ⟨Quotient.lift f hle,
          (ConcreteCategory.hom f).continuous.quotient_lift hle⟩
    exact
      { toFun := fun g => q ≫ cgwhToCompactlyGenerated.map g
        invFun := lift
        left_inv := fun g => by
          apply ConcreteCategory.hom_ext
          intro z
          induction z using Quotient.inductionOn'
          rfl
        right_inv := fun f => by
          apply ConcreteCategory.hom_ext
          intro x
          rfl }
  exact
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply ConcreteCategory.hom_ext
        intro z
        induction z using Quotient.inductionOn'
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ConcreteCategory.hom_ext
        intro x
        rfl }

/-- Weak-Hausdorffification is left adjoint to the fully faithful inclusion
of CGWH spaces into compactly generated spaces. -/
noncomputable def weakHausdorffificationAdjunction :
    weakHausdorffification ⊣ cgwhToCompactlyGenerated :=
  Adjunction.mkOfHomEquiv reflectionCoreHomEquiv

/-- The reflection unit. -/
@[expose] def reflectionUnit :
    (Functor.id (CompactlyGenerated.{u, v})) ⟶
      weakHausdorffification ⋙ cgwhToCompactlyGenerated :=
  weakHausdorffificationAdjunction.unit

/-- The weak-Hausdorff reflection unit is surjective on points. -/
theorem reflectionUnit_surjective
    (X : CompactlyGenerated.{u, v}) :
    Function.Surjective (reflectionUnit.app X) := by
  intro q
  induction q using Quotient.inductionOn' with
  | _ x => exact ⟨x, rfl⟩

/-- The counit of weak-Hausdorffification, as an isomorphism. -/
noncomputable def reflectionCounitIso (Y : CGWH.{u, v}) :
    weakHausdorffification.obj (cgwhToCompactlyGenerated.obj Y) ≅ Y :=
  asIso (weakHausdorffificationAdjunction.counit.app Y)

/-- The inclusion of CGWH spaces into compactly generated spaces is
reflective. -/
noncomputable instance instReflective :
    Reflective cgwhToCompactlyGenerated where
  L := weakHausdorffification
  adj := weakHausdorffificationAdjunction

/-- The reflection unit is a homeomorphism exactly on weak-Hausdorff
compactly generated spaces. -/
theorem reflectionUnit_isHomeomorph_iff
    (X : CompactlyGenerated.{u, v}) :
    IsHomeomorph (reflectionUnit.app X) ↔
      UWeakHausdorffSpace.{u} X := by
  constructor
  · intro hunit
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K f g
    let Q := cgwhToCompactlyGenerated.obj
      (weakHausdorffification.obj X)
    let _ : UWeakHausdorffSpace.{u} ↥Q.toTop :=
      (weakHausdorffification.obj X).is_weakHausdorff
    let f' : C(K, Q) :=
      (ConcreteCategory.hom (reflectionUnit.app X)).comp f
    let g' : C(K, Q) :=
      (ConcreteCategory.hom (reflectionUnit.app X)).comp g
    have hclosed : IsClosed {k : K | f' k = g' k} :=
      (uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance) K f' g'
    rw [show {k : K | f k = g k} = {k : K | f' k = g' k} by
      ext k
      change (f k = g k) ↔
        reflectionUnit.app X (f k) = reflectionUnit.app X (g k)
      exact hunit.injective.eq_iff.symm]
    exact hclosed
  · intro hX
    let s := smallestClosedEquivalenceRelation X
    have hbot : closedEquivalenceRelation X
        (⊥ : Setoid ↥X.toTop) :=
      (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
        X).mp hX
    have hle : s.1 ≤ (⊥ : Setoid ↥X.toTop) := by
      change sInf {t : Setoid ↥X.toTop |
        closedEquivalenceRelation X t} ≤ ⊥
      exact sInf_le hbot
    have hs : s.1 = (⊥ : Setoid ↥X.toTop) :=
      le_antisymm hle bot_le
    have hq : IsQuotientMap (reflectionUnit.app X) := by
      change IsQuotientMap (@Quotient.mk' ↥X.toTop s.1)
      exact isQuotientMap_quotient_mk'
    have hi : Function.Injective (reflectionUnit.app X) := by
      intro x y hxy
      change (@Quotient.mk' ↥X.toTop s.1) x =
        (@Quotient.mk' ↥X.toTop s.1) y at hxy
      have hrel : s.1 x y := Quotient.exact hxy
      rw [hs] at hrel
      exact hrel
    exact isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hi⟩

private noncomputable def compactlyGeneratedQuotient
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) :
    CompactlyGenerated.{u, v} := by
  let _ : UCompactlyGeneratedSpace.{u} ↥X.toTop :=
    X.toCompactlyGenerated.is_compactly_generated
  exact CompactlyGenerated.of (Quotient s)

/-- The native CGWH quotient, obtained by weak-Hausdorff reflection of the
ordinary topological quotient. -/
noncomputable def quotient
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) : CGWH.{u, v} :=
  weakHausdorffification.obj (compactlyGeneratedQuotient X s)

/-- Comparison from the ordinary topological quotient to the native CGWH
quotient. -/
noncomputable def quotientComparisonFromTop
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) :
    TopCat.of (Quotient s) ⟶ cgwhToTop.obj (quotient X s) := by
  let Q := compactlyGeneratedQuotient X s
  exact CompactlyGenerated.compactlyGeneratedToTop.map
    (reflectionUnit.app Q)

/-- Maps from a native CGWH quotient are equivalently maps from its ordinary
topological quotient into the included target. -/
noncomputable def quotientHomEquiv
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) (Y : CGWH.{u, v}) :
    (quotient X s ⟶ Y) ≃
      (TopCat.of (Quotient s) ⟶ cgwhToTop.obj Y) := by
  let Q := compactlyGeneratedQuotient X s
  change (weakHausdorffification.obj Q ⟶ Y) ≃
    (CompactlyGenerated.compactlyGeneratedToTop.obj Q ⟶
      CompactlyGenerated.compactlyGeneratedToTop.obj
        (cgwhToCompactlyGenerated.obj Y))
  exact
    (weakHausdorffificationAdjunction.homEquiv Q Y).trans
      CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.homEquiv

/-- The forward quotient Hom equivalence is postcomposition with the
raw-to-native quotient comparison. -/
@[simp, nolint simpNF]
theorem quotientHomEquiv_apply
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) (Y : CGWH.{u, v})
    (f : quotient X s ⟶ Y) :
    quotientHomEquiv X s Y f =
      quotientComparisonFromTop X s ≫ cgwhToTop.map f := by
  rfl

/-- The raw-to-native quotient comparison is a homeomorphism exactly for a
closed equivalence relation. -/
theorem quotientComparisonFromTop_isHomeomorph_iff
    (X : CGWH.{u, v}) (s : Setoid ↥X.toTop) :
    IsHomeomorph (quotientComparisonFromTop X s) ↔
      closedEquivalenceRelation (cgwhToCompactlyGenerated.obj X) s := by
  let Q := compactlyGeneratedQuotient X s
  change IsHomeomorph (reflectionUnit.app Q) ↔ _
  exact (reflectionUnit_isHomeomorph_iff Q).trans
    (quotient_isWeakHausdorff_iff_isClosed
      (cgwhToCompactlyGenerated.obj X) s)

end CGWH

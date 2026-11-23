/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.Products
public import MathlibExt.Topology.Compactness.CompactlyGeneratedProduct
public import Mathlib.Topology.CompactOpen
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cartesian closedness of compactly generated spaces

The internal Hom is the compact generation of the compact-open mapping
space.  Evaluation and currying are constructed directly from compact
Hausdorff probes, without a local-compactness assumption on the source.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CompactlyGenerated

/-- The compactly generated compact-open internal-Hom functor. -/
noncomputable def internalHom (X : CompactlyGenerated.{u, v}) :
    CompactlyGenerated.{u, v} ⥤ CompactlyGenerated.{u, v} where
  obj Y := TopCat.toCompactlyGenerated.obj (TopCat.of C(X, Y))
  map {Y Z} f := TopCat.toCompactlyGenerated.map
    (TopCat.ofHom
      ⟨fun g => (ConcreteCategory.hom f).comp g,
        (ConcreteCategory.hom f).continuous_postcomp⟩)
  map_id Y := by
    apply compactlyGeneratedToTop.map_injective
    apply TopCat.hom_ext
    ext f
    rfl
  map_comp {Y Z T} f g := by
    apply compactlyGeneratedToTop.map_injective
    apply TopCat.hom_ext
    ext h
    rfl

/-- The kified internal Hom maps to the raw compact-open mapping space. -/
noncomputable def internalHomToCompactOpen
    (X Y : CompactlyGenerated.{u, v}) :
    compactlyGeneratedToTop.obj ((internalHom X).obj Y) ⟶
      TopCat.of C(X, Y) :=
  adj.counit.app (TopCat.of C(X, Y))

/-- The internal-Hom comparison is the identity on continuous maps. -/
@[simp]
theorem internalHomToCompactOpen_apply
    (X Y : CompactlyGenerated.{u, v})
    (f : (internalHom X).obj Y) :
    internalHomToCompactOpen X Y f = f :=
  adjCounit_apply _ _

/-- Tensoring on the left is left adjoint to the compactly generated
compact-open internal Hom. -/
noncomputable def internalHomAdjunction
    (X : CompactlyGenerated.{u, v}) :
    tensorLeft X ⊣ internalHom X := by
  let RawPair (Y : CompactlyGenerated.{u, v}) : TopCat.{v} :=
    TopCat.of
      (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y))
  let PF (Y : CompactlyGenerated.{u, v}) :
      ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp (Y : CompactlyGenerated.{u, v}) :
      ((TopCat.piFan (fun j ↦
        compactlyGeneratedToTop.obj (PF Y j))).pt : Type v) ≃ₜ
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
  let eTensor (Y : CompactlyGenerated.{u, v}) :
      (∏ᶜ PF Y) ≅ X ⊗ Y := by
    let c : Fan (PF Y) := Fan.mk (X ⊗ Y) (fun j => match j with
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
  let binaryIso (Y : CompactlyGenerated.{u, v}) :
      TopCat.toCompactlyGenerated.obj (RawPair Y) ≅ X ⊗ Y :=
    TopCat.toCompactlyGenerated.mapIso
        (TopCat.isoOfHomeo (hp Y).symm) ≪≫
      (piIsoPi (PF Y)).symm ≪≫ eTensor Y
  have binaryIso_hom_fst (Y : CompactlyGenerated.{u, v}) :
      (binaryIso Y).hom ≫ CartesianMonoidalCategory.fst X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodFst : RawPair Y ⟶ compactlyGeneratedToTop.obj X) ≫
          inv (adj.unit.app X) := by
    let h : RawPair Y ⟶
        (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj (PF Y j))).pt :=
      (TopCat.isoOfHomeo (hp Y).symm).hom
    have hRaw : h ≫
        (TopCat.piFan (fun j ↦
          compactlyGeneratedToTop.obj (PF Y j))).π.app
            ⟨ULift.up WalkingPair.left⟩ = TopCat.prodFst := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : (eTensor Y).hom ≫
        CartesianMonoidalCategory.fst X Y =
      Pi.π (PF Y) (ULift.up WalkingPair.left) := by
      apply (cancel_epi (eTensor Y).inv).1
      simp [eTensor]
    have hPi : (piIsoPi (PF Y)).symm.hom ≫
        Pi.π (PF Y) (ULift.up WalkingPair.left) =
      piπ (PF Y) (ULift.up WalkingPair.left) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit (PF Y))
        ⟨ULift.up WalkingPair.left⟩
    simp only [binaryIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    unfold piπ
    rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
    rw [asIso_inv]
  have binaryIso_hom_snd (Y : CompactlyGenerated.{u, v}) :
      (binaryIso Y).hom ≫ CartesianMonoidalCategory.snd X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodSnd : RawPair Y ⟶ compactlyGeneratedToTop.obj Y) ≫
          inv (adj.unit.app Y) := by
    let h : RawPair Y ⟶
        (TopCat.piFan (fun j ↦ compactlyGeneratedToTop.obj (PF Y j))).pt :=
      (TopCat.isoOfHomeo (hp Y).symm).hom
    have hRaw : h ≫
        (TopCat.piFan (fun j ↦
          compactlyGeneratedToTop.obj (PF Y j))).π.app
            ⟨ULift.up WalkingPair.right⟩ = TopCat.prodSnd := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : (eTensor Y).hom ≫
        CartesianMonoidalCategory.snd X Y =
      Pi.π (PF Y) (ULift.up WalkingPair.right) := by
      apply (cancel_epi (eTensor Y).inv).1
      simp [eTensor]
    have hPi : (piIsoPi (PF Y)).symm.hom ≫
        Pi.π (PF Y) (ULift.up WalkingPair.right) =
      piπ (PF Y) (ULift.up WalkingPair.right) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit (PF Y))
        ⟨ULift.up WalkingPair.right⟩
    simp only [binaryIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    unfold piπ
    rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
    rw [asIso_inv]
  have unit_apply (Y : CompactlyGenerated.{u, v}) (y : Y) :
      adj.unit.app Y y = y := by
    rfl
  let rawPairMap {Y Z : CompactlyGenerated.{u, v}} (g : Y ⟶ Z) :
      RawPair Y ⟶ RawPair Z :=
    TopCat.ofHom
      ⟨fun p => (p.1, g p.2),
        continuous_fst.prodMk
          ((ConcreteCategory.hom g).continuous.comp continuous_snd)⟩
  let pairMap {Y Z : CompactlyGenerated.{u, v}} (g : Y ⟶ Z) :
      TopCat.toCompactlyGenerated.obj (RawPair Y) ⟶
        TopCat.toCompactlyGenerated.obj (RawPair Z) :=
    TopCat.toCompactlyGenerated.map (rawPairMap g)
  have binaryIso_naturality {Y Z : CompactlyGenerated.{u, v}}
      (g : Y ⟶ Z) :
      pairMap g ≫ (binaryIso Z).hom =
        (binaryIso Y).hom ≫ (X ◁ g) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, binaryIso_hom_fst,
        CartesianMonoidalCategory.whiskerLeft_fst]
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    · simp only [Category.assoc]
      rw [binaryIso_hom_snd,
        CartesianMonoidalCategory.whiskerLeft_snd]
      have hRawSnd : rawPairMap g ≫ TopCat.prodSnd =
          TopCat.prodSnd ≫ compactlyGeneratedToTop.map g := by
        apply TopCat.hom_ext
        ext p
        rfl
      calc
        pairMap g ≫
              (TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
                inv (adj.unit.app Z)) =
            TopCat.toCompactlyGenerated.map
                (rawPairMap g ≫ TopCat.prodSnd) ≫
              inv (adj.unit.app Z) := by
          rw [TopCat.toCompactlyGenerated.map_comp, Category.assoc]
        _ = TopCat.toCompactlyGenerated.map
                (TopCat.prodSnd ≫ compactlyGeneratedToTop.map g) ≫
              inv (adj.unit.app Z) := by rw [hRawSnd]
        _ = (TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
                TopCat.toCompactlyGenerated.map
                  (compactlyGeneratedToTop.map g)) ≫
              inv (adj.unit.app Z) := by
          rw [TopCat.toCompactlyGenerated.map_comp]
        _ = TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
              (TopCat.toCompactlyGenerated.map
                  (compactlyGeneratedToTop.map g) ≫
                inv (adj.unit.app Z)) := by
          rw [Category.assoc]
        _ = TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
              (inv (adj.unit.app Y) ≫ g) := by
          exact congrArg
            (fun q ↦ TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫ q)
            (adj.unit.naturality_inv g).symm
        _ = (TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
                inv (adj.unit.app Y)) ≫ g := by
          exact (Category.assoc _ _ _).symm
        _ = ((binaryIso Y).hom ≫
              CartesianMonoidalCategory.snd X Y) ≫ g := by
          rw [binaryIso_hom_snd]
        _ = (binaryIso Y).hom ≫
              (CartesianMonoidalCategory.snd X Y ≫ g) :=
          Category.assoc _ _ _
  let continuousToKifiedMax {S : Type max u v} {T : Type v}
      [tS : TopologicalSpace S] [tT : TopologicalSpace T]
      [UCompactlyGeneratedSpace.{u} S]
      {h : S → T} (hh : Continuous h) :
      @Continuous S T inferInstance
        (TopologicalSpace.compactlyGenerated.{u} T) h := by
    apply continuous_from_uCompactlyGeneratedSpace.{u, max u v, v}
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
  let continuousToKified {S : Type v} {T : Type v}
      [tS : TopologicalSpace S] [tT : TopologicalSpace T]
      [UCompactlyGeneratedSpace.{u} S]
      {h : S → T} (hh : Continuous h) :
      @Continuous S T inferInstance
        (TopologicalSpace.compactlyGenerated.{u} T) h := by
    apply continuous_from_uCompactlyGeneratedSpace.{u, v, v}
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
  let evalPair0 (Z : CompactlyGenerated.{u, v}) :
      TopCat.toCompactlyGenerated.obj
          (RawPair ((internalHom X).obj Z)) ⟶ Z := by
    let H := (internalHom X).obj Z
    apply ConcreteCategory.ofHom
    refine ⟨fun p => (internalHomToCompactOpen X Z p.2) p.1, ?_⟩
    apply continuous_from_uCompactlyGeneratedSpace.{u, v, v}
    intro K a
    let aRaw : C(K, X × H) :=
      ⟨fun k => adj.counit.app (RawPair H) (a k),
        (ConcreteCategory.hom (adj.counit.app (RawPair H))).continuous.comp
          a.continuous⟩
    let x : C(K, X) :=
      ⟨fun k => (aRaw k).1, continuous_fst.comp aRaw.continuous⟩
    let fNative : C(K, H) :=
      ⟨fun k => (aRaw k).2, continuous_snd.comp aRaw.continuous⟩
    let fRaw : C(K, C(X, Z)) :=
      (ConcreteCategory.hom (internalHomToCompactOpen X Z)).comp fNative
    have heval : Continuous (fun k => fRaw k (x k)) := by
      apply continuous_def.2
      intro U hU
      apply isOpen_iff_forall_mem_open.2
      intro k hk
      have hpreOpen : IsOpen (x ⁻¹' ((fRaw k) ⁻¹' U)) :=
        (hU.preimage (fRaw k).continuous).preimage x.continuous
      have hpreNhds : x ⁻¹' ((fRaw k) ⁻¹' U) ∈ 𝓝ˢ ({k} : Set K) :=
        hpreOpen.mem_nhdsSet.2 (by simpa using hk)
      obtain ⟨V, hVOpen, hkV, hClosure⟩ :=
        isCompact_singleton.exists_isOpen_closure_subset hpreNhds
      let Cset : Set X := x '' closure V
      have hCset : IsCompact Cset :=
        isClosed_closure.isCompact.image x.continuous
      let N : Set C(X, Z) := {g | Set.MapsTo g Cset U}
      have hNOpen : IsOpen N :=
        ContinuousMap.isOpen_setOfPred_mapsTo hCset hU
      have hkN : fRaw k ∈ N := by
        intro z hz
        obtain ⟨l, hl, rfl⟩ := hz
        exact hClosure hl
      refine ⟨V ∩ fRaw ⁻¹' N, ?_,
        hVOpen.inter (hNOpen.preimage fRaw.continuous),
        ⟨hkV (Set.mem_singleton k), hkN⟩⟩
      rintro l ⟨hlV, hlf⟩
      exact hlf ⟨l, subset_closure hlV, rfl⟩
    have hfun : (fun k : K => fRaw k (x k)) =
        (fun k : K =>
          (internalHomToCompactOpen X Z (a k).2) (a k).1) := by
      funext k
      have ha : aRaw k = a k :=
        adjCounit_apply.{v, u} (RawPair H) (a k)
      have hf : fRaw k = fNative k :=
        adjCounit_apply.{v, u} (TopCat.of C(X, Z)) (fNative k)
      rw [hf]
      change (internalHomToCompactOpen X Z (aRaw k).2) (aRaw k).1 =
        (internalHomToCompactOpen X Z (a k).2) (a k).1
      rw [ha]
    change Continuous (fun k : K =>
      (internalHomToCompactOpen X Z (a k).2) (a k).1)
    rw [← hfun]
    exact heval
  let eval0 (Z : CompactlyGenerated.{u, v}) :
      X ⊗ (internalHom X).obj Z ⟶ Z :=
    (binaryIso ((internalHom X).obj Z)).inv ≫ evalPair0 Z
  have evalPair0_apply (Z : CompactlyGenerated.{u, v})
      (p : X × (internalHom X).obj Z) :
      evalPair0 Z p = (internalHomToCompactOpen X Z p.2) p.1 := by
    rfl
  let rawCurry {Y Z : CompactlyGenerated.{u, v}} (f : X ⊗ Y ⟶ Z) :
      C(Y, C(X, Z)) := by
    let e := binaryIso Y
    let ψRaw : Y → C(X, Z) := fun y => by
      let hRaw : X →
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) := fun x => (x, y)
      have hRawContinuous : Continuous hRaw :=
        continuous_id.prodMk continuous_const
      have hKified : @Continuous X
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) inferInstance
          (TopologicalSpace.compactlyGenerated.{u} _) hRaw :=
        continuousToKified hRawContinuous
      let hToPair : X ⟶ TopCat.toCompactlyGenerated.obj (RawPair Y) :=
        ConcreteCategory.ofHom ⟨hRaw, by
          have ht : (TopCat.toCompactlyGenerated.obj (RawPair Y)).toTop.str =
              TopologicalSpace.compactlyGenerated.{u}
                (↥(compactlyGeneratedToTop.obj X) ×
                  ↥(compactlyGeneratedToTop.obj Y)) := by
            change TopologicalSpace.generatedBy compactHausProbes (Y :=
              ↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) = _
            exact
              TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
          rw [ht]
          exact hKified⟩
      exact ConcreteCategory.hom (hToPair ≫ e.hom ≫ f)
    have hψRaw : Continuous ψRaw := by
      apply continuous_from_uCompactlyGeneratedSpace.{u, v, v} ψRaw
      intro K g
      let _ : UCompactlyGeneratedSpace.{u} (K × X) :=
        uCompactlyGeneratedSpace_prod_of_locallyCompact_left
          (A := K) (B := X)
      let hRaw : K × X →
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) :=
        fun p => (p.2, g p.1)
      have hRawContinuous : Continuous hRaw :=
        continuous_snd.prodMk (g.continuous.comp continuous_fst)
      have hKified : @Continuous (K × X)
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) inferInstance
          (TopologicalSpace.compactlyGenerated.{u} _) hRaw :=
        continuousToKifiedMax hRawContinuous
      have hKified' : @Continuous (K × X)
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) inferInstance
          (TopCat.toCompactlyGenerated.obj (RawPair Y)).toTop.str hRaw := by
        have ht : (TopCat.toCompactlyGenerated.obj (RawPair Y)).toTop.str =
            TopologicalSpace.compactlyGenerated.{u}
              (↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) := by
          change TopologicalSpace.generatedBy compactHausProbes (Y :=
            ↥(compactlyGeneratedToTop.obj X) ×
              ↥(compactlyGeneratedToTop.obj Y)) = _
          exact
            TopologicalSpace.generatedBy_compactHausProbes_eq_compactlyGenerated
        rw [ht]
        exact hKified
      have hNative : Continuous (fun p : K × X => e.hom (hRaw p)) :=
        (ConcreteCategory.hom e.hom).continuous.comp hKified'
      have hUncurry : Continuous (fun p : K × X =>
          f (e.hom (hRaw p))) :=
        (ConcreteCategory.hom f).continuous.comp hNative
      let φ : K → C(X, Z) := fun k =>
        ⟨fun x => f (e.hom (x, g k)),
          hUncurry.comp (continuous_const.prodMk continuous_id)⟩
      have hφ : Continuous φ :=
        ContinuousMap.continuous_of_continuous_uncurry φ (by
          change Continuous (fun p : K × X => f (e.hom (p.2, g p.1)))
          exact hUncurry)
      exact hφ.congr (fun k => by
        apply ContinuousMap.ext
        intro x
        dsimp only [φ, Function.comp_apply]
        dsimp [ψRaw]
        rfl)
    exact ⟨ψRaw, hψRaw⟩
  let curry0 {Y Z : CompactlyGenerated.{u, v}} (f : X ⊗ Y ⟶ Z) :
      Y ⟶ (internalHom X).obj Z :=
    adj.homEquiv Y (TopCat.of C(X, Z)) (TopCat.ofHom (rawCurry f))
  have curry0_landing {Y Z : CompactlyGenerated.{u, v}}
      (f : X ⊗ Y ⟶ Z) :
      compactlyGeneratedToTop.map (curry0 f) ≫
          internalHomToCompactOpen X Z =
        TopCat.ofHom (rawCurry f) := by
    change (adj.homEquiv Y (TopCat.of C(X, Z))).symm
        ((adj.homEquiv Y (TopCat.of C(X, Z)))
          (TopCat.ofHom (rawCurry f))) = _
    exact (adj.homEquiv Y (TopCat.of C(X, Z))).symm_apply_apply _
  have curry0_apply {Y Z : CompactlyGenerated.{u, v}}
      (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
      (internalHomToCompactOpen X Z (curry0 f y)) x =
        f ((binaryIso Y).hom (x, y)) := by
    have hy := ConcreteCategory.congr_hom (curry0_landing f) y
    have hx := congrArg (fun q : C(X, Z) => q x) hy
    change (internalHomToCompactOpen X Z (curry0 f y)) x =
      f ((binaryIso Y).hom (x, y)) at hx
    exact hx
  let uncurry0 {Y Z : CompactlyGenerated.{u, v}}
      (g : Y ⟶ (internalHom X).obj Z) : X ⊗ Y ⟶ Z :=
    (X ◁ g) ≫ eval0 Z
  have uncurry0_after_binaryIso {Y Z : CompactlyGenerated.{u, v}}
      (g : Y ⟶ (internalHom X).obj Z) :
      (binaryIso Y).hom ≫ uncurry0 g = pairMap g ≫ evalPair0 Z := by
    change ((binaryIso Y).hom ≫ (X ◁ g)) ≫
        (binaryIso ((internalHom X).obj Z)).inv ≫ evalPair0 Z = _
    rw [← binaryIso_naturality g]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have uncurry0_apply {Y Z : CompactlyGenerated.{u, v}}
      (g : Y ⟶ (internalHom X).obj Z) (y : Y) (x : X) :
      uncurry0 g ((binaryIso Y).hom (x, y)) =
        (internalHomToCompactOpen X Z (g y)) x := by
    have h := ConcreteCategory.congr_hom
      (uncurry0_after_binaryIso g) (x, y)
    change uncurry0 g ((binaryIso Y).hom (x, y)) =
      (internalHomToCompactOpen X Z (g y)) x at h
    exact h
  have pairMap_comp {Y Z T : CompactlyGenerated.{u, v}}
      (f : Y ⟶ Z) (g : Z ⟶ T) :
      pairMap (f ≫ g) = pairMap f ≫ pairMap g := by
    change TopCat.toCompactlyGenerated.map (rawPairMap (f ≫ g)) =
      TopCat.toCompactlyGenerated.map (rawPairMap f) ≫
        TopCat.toCompactlyGenerated.map (rawPairMap g)
    rw [← TopCat.toCompactlyGenerated.map_comp]
    congr 1
  have internalHom_map_apply {Z T : CompactlyGenerated.{u, v}}
      (g : Z ⟶ T) (h : (internalHom X).obj Z) (x : X) :
      (internalHomToCompactOpen X T ((internalHom X).map g h)) x =
        g (internalHomToCompactOpen X Z h x) := by
    let post : TopCat.of C(X, Z) ⟶ TopCat.of C(X, T) :=
      TopCat.ofHom
        ⟨fun k => (ConcreteCategory.hom g).comp k,
          (ConcreteCategory.hom g).continuous_postcomp⟩
    have hn := adj.counit.naturality post
    have hh := ConcreteCategory.congr_hom hn h
    have hx := congrArg (fun k : C(X, T) => k x) hh
    change (internalHomToCompactOpen X T ((internalHom X).map g h)) x =
      g (internalHomToCompactOpen X Z h x) at hx
    exact hx
  let homEquiv (Y Z : CompactlyGenerated.{u, v}) :
      (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (internalHom X).obj Z) :=
    { toFun := curry0
      invFun := uncurry0
      left_inv := fun f => by
        apply compactlyGeneratedToTop.map_injective
        apply TopCat.hom_ext
        ext p
        let q := (binaryIso Y).inv p
        have hq : (binaryIso Y).hom (q.1, q.2) = p := by
          change (binaryIso Y).hom q = p
          exact TopCat.inv_hom_id_apply
            (compactlyGeneratedToTop.mapIso (binaryIso Y)) p
        calc
          uncurry0 (curry0 f) p =
              uncurry0 (curry0 f) ((binaryIso Y).hom (q.1, q.2)) := by
            rw [hq]
          _ = (internalHomToCompactOpen X Z (curry0 f q.2)) q.1 :=
            uncurry0_apply (curry0 f) q.2 q.1
          _ = f ((binaryIso Y).hom (q.1, q.2)) :=
            curry0_apply f q.2 q.1
          _ = f p := by rw [hq]
      right_inv := fun g => by
        apply compactlyGeneratedToTop.map_injective
        apply TopCat.hom_ext
        ext y
        apply ContinuousMap.ext
        intro x
        change (internalHomToCompactOpen X Z
            (curry0 (uncurry0 g) (show Y from y))) x =
          (internalHomToCompactOpen X Z (g (show Y from y))) x
        rw [curry0_apply, uncurry0_apply] }
  exact Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro Y' Y Z f g
        change uncurry0 (f ≫ g) = (X ◁ f) ≫ uncurry0 g
        apply (cancel_epi (binaryIso Y').hom).1
        calc
          (binaryIso Y').hom ≫ uncurry0 (f ≫ g) =
              pairMap (f ≫ g) ≫ evalPair0 Z :=
            uncurry0_after_binaryIso (f ≫ g)
          _ = (pairMap f ≫ pairMap g) ≫ evalPair0 Z := by
            rw [pairMap_comp]
          _ = pairMap f ≫ (pairMap g ≫ evalPair0 Z) :=
            Category.assoc _ _ _
          _ = pairMap f ≫ ((binaryIso Y).hom ≫ uncurry0 g) := by
            rw [uncurry0_after_binaryIso]
          _ = (pairMap f ≫ (binaryIso Y).hom) ≫ uncurry0 g :=
            (Category.assoc _ _ _).symm
          _ = ((binaryIso Y').hom ≫ (X ◁ f)) ≫ uncurry0 g := by
            rw [binaryIso_naturality]
          _ = (binaryIso Y').hom ≫ ((X ◁ f) ≫ uncurry0 g) :=
            Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro Y Z Z' f g
        apply compactlyGeneratedToTop.map_injective
        apply TopCat.hom_ext
        ext y
        apply ContinuousMap.ext
        intro x
        change (internalHomToCompactOpen X Z'
            (curry0 (f ≫ g) (show Y from y))) x =
          (internalHomToCompactOpen X Z'
            ((internalHom X).map g (curry0 f (show Y from y)))) x
        rw [curry0_apply, internalHom_map_apply, curry0_apply]
        rfl }

/-- Evaluation for the compactly generated compact-open internal Hom. -/
noncomputable def eval (X Z : CompactlyGenerated.{u, v}) :
    X ⊗ (internalHom X).obj Z ⟶ Z :=
  (internalHomAdjunction X).counit.app Z

/-- Curry a map out of a native product into the kified compact-open
internal Hom. -/
noncomputable def curry {X Y Z : CompactlyGenerated.{u, v}}
    (f : X ⊗ Y ⟶ Z) : Y ⟶ (internalHom X).obj Z :=
  (internalHomAdjunction X).homEquiv Y Z f

/-- Uncurry a map into the internal Hom. -/
noncomputable def uncurry {X Y Z : CompactlyGenerated.{u, v}}
    (g : Y ⟶ (internalHom X).obj Z) : X ⊗ Y ⟶ Z :=
  ((internalHomAdjunction X).homEquiv Y Z).symm g

/-- Compactly generated spaces form a monoidal closed category. -/
noncomputable instance instMonoidalClosed :
    MonoidalClosed CompactlyGenerated.{u, v} where
  closed X :=
    { rightAdj := internalHom X
      adj := internalHomAdjunction X }

end CompactlyGenerated

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic
public import MathlibExt.Topology.Category.CompactlyGenerated.Products
public import MathlibExt.Topology.Compactness.CompactlyGeneratedProduct
public import Mathlib.Topology.Sequences

/-!
# Products of compactly generated weak Hausdorff spaces

This file constructs arbitrary same-carrier-universe products in `CGWH` by
reusing the explicit products of `CompactlyGenerated`.  Weak Hausdorffness is
proved coordinatewise, and the native-to-ordinary comparison is exposed
without asserting that an arbitrary raw product is already compactly
generated.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CGWH

/-- The explicit native product of a family of CGWH spaces. -/
noncomputable def piObj {I : Type v} (X : I → CGWH.{u, v}) :
    CGWH.{u, v} where
  toCompactlyGenerated := CompactlyGenerated.piObj
    (fun i ↦ cgwhToCompactlyGenerated.obj (X i))
  is_weakHausdorff := by
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K f g
    let U : I → CompactlyGenerated.{u, v} :=
      fun i ↦ cgwhToCompactlyGenerated.obj (X i)
    have hEqualizer : {k | f k = g k} =
        ⋂ i, {k | CompactlyGenerated.piπ U i (f k) =
          CompactlyGenerated.piπ U i (g k)} := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i
        rw [h]
      · intro h
        let P : CompactlyGenerated.{u, v} :=
          CompactlyGenerated.of (ULift.{v, 0} PUnit)
        let cf : P ⟶ CompactlyGenerated.piObj U :=
          ConcreteCategory.ofHom
            (ContinuousMap.const (ULift.{v, 0} PUnit) (f k))
        let cg : P ⟶ CompactlyGenerated.piObj U :=
          ConcreteCategory.ofHom
            (ContinuousMap.const (ULift.{v, 0} PUnit) (g k))
        have hfg : cf = cg := by
          apply (CompactlyGenerated.piFanIsLimit U).hom_ext
          rintro ⟨i⟩
          apply ConcreteCategory.hom_ext
          intro q
          exact h i
        exact ConcreteCategory.congr_hom hfg (ULift.up PUnit.unit)
    rw [hEqualizer]
    apply isClosed_iInter
    intro i
    let _ : UWeakHausdorffSpace.{u} (U i : Type v) :=
      (X i).is_weakHausdorff
    exact (uWeakHausdorffSpace_iff_isClosed_equalizer.mp inferInstance)
      K ((ConcreteCategory.hom (CompactlyGenerated.piπ U i)).comp f)
        ((ConcreteCategory.hom (CompactlyGenerated.piπ U i)).comp g)

/-- Projection from the explicit native CGWH product. -/
noncomputable def piπ {I : Type v} (X : I → CGWH.{u, v}) (i : I) :
    piObj X ⟶ X i :=
  fullyFaithfulCgwhToCompactlyGenerated.preimage
    (CompactlyGenerated.piπ
      (fun i ↦ cgwhToCompactlyGenerated.obj (X i)) i)

/-- The explicit native CGWH product fan. -/
noncomputable abbrev piFan {I : Type v} (X : I → CGWH.{u, v}) :
    Fan X :=
  Fan.mk (piObj X) (piπ X)

/-- The explicit native CGWH product fan is limiting. -/
noncomputable def piFanIsLimit {I : Type v}
    (X : I → CGWH.{u, v}) : IsLimit (piFan X) := by
  let U : I → CompactlyGenerated.{u, v} :=
    fun i ↦ cgwhToCompactlyGenerated.obj (X i)
  let hU := CompactlyGenerated.piFanIsLimit U
  let mappedFan (s : Fan X) : Fan U :=
    Fan.mk (cgwhToCompactlyGenerated.obj s.pt)
      (fun i ↦ cgwhToCompactlyGenerated.map (s.proj i))
  have hProj (i : I) :
      cgwhToCompactlyGenerated.map (piπ X i) =
        CompactlyGenerated.piπ U i := by
    unfold piπ
    exact fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  let liftCGWH (s : Fan X) : s.pt ⟶ piObj X :=
    fullyFaithfulCgwhToCompactlyGenerated.preimage
      (hU.lift (mappedFan s))
  have hLift (s : Fan X) :
      cgwhToCompactlyGenerated.map (liftCGWH s) =
        hU.lift (mappedFan s) := by
    unfold liftCGWH
    exact fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  refine
    { lift := liftCGWH
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply cgwhToCompactlyGenerated.map_injective
    change cgwhToCompactlyGenerated.map (liftCGWH s) ≫
        cgwhToCompactlyGenerated.map (piπ X j.as) =
      cgwhToCompactlyGenerated.map (s.π.app j)
    rw [hLift, hProj]
    exact hU.fac (mappedFan s) j
  · intro s m hm
    apply cgwhToCompactlyGenerated.map_injective
    change cgwhToCompactlyGenerated.map m =
      cgwhToCompactlyGenerated.map (liftCGWH s)
    rw [hLift]
    apply hU.uniq (mappedFan s)
    intro j
    change cgwhToCompactlyGenerated.map m ≫
        CompactlyGenerated.piπ U j.as =
      (mappedFan s).π.app j
    rw [← hProj, ← cgwhToCompactlyGenerated.map_comp]
    have hmj := hm j
    change m ≫ piπ X j.as = s.π.app j at hmj
    rw [hmj]
    rfl

/-- CGWH has arbitrary products indexed in its carrier universe. -/
noncomputable instance instHasProducts : HasProducts.{v} CGWH.{u, v} :=
  hasProducts_of_limit_fans piFan piFanIsLimit

/-- Finite products are the finite specialization of the sole arbitrary
CGWH product provider. -/
noncomputable instance instHasFiniteProducts :
    HasFiniteProducts CGWH.{u, v} :=
  hasFiniteProducts_of_hasProducts.{v, v, v + 1} CGWH.{u, v}

/-- The selected product is canonically isomorphic to the explicit native
CGWH product. -/
noncomputable def piIsoPi {I : Type v} (X : I → CGWH.{u, v}) :
    (∏ᶜ X) ≅ piObj X :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit X)

/-- Inclusion of the native CGWH product into the ordinary TopCat product. -/
noncomputable def piComparisonToTop {I : Type v}
    (X : I → CGWH.{u, v}) :
    cgwhToTop.obj (piObj X) ⟶
      (TopCat.piFan (fun i ↦ cgwhToTop.obj (X i))).pt :=
  CompactlyGenerated.piComparisonToTop
    (fun i ↦ cgwhToCompactlyGenerated.obj (X i))

/-- The native-to-ordinary product comparison is the identity on points. -/
@[simp]
theorem piComparisonToTop_apply {I : Type v}
    (X : I → CGWH.{u, v}) (x : piObj X) :
    piComparisonToTop X x = x :=
  CompactlyGenerated.piComparisonToTop_apply
    (fun i ↦ cgwhToCompactlyGenerated.obj (X i)) x

/-- The explicit comparison agrees with the generic comparison from the
selected CGWH product. -/
theorem piComparisonToTop_generic_coherence {I : Type v}
    (X : I → CGWH.{u, v}) :
    cgwhToTop.map (piIsoPi X).hom ≫ piComparisonToTop X =
      Limits.piComparison cgwhToTop X ≫
        (TopCat.piIsoPi (fun i ↦ cgwhToTop.obj (X i))).hom := by
  apply (TopCat.piFanIsLimit
    (fun i ↦ cgwhToTop.obj (X i))).hom_ext
  rintro ⟨i⟩
  have hTopPi :
      (TopCat.piIsoPi (fun i ↦ cgwhToTop.obj (X i))).hom ≫
          TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i =
        Pi.π (fun i ↦ cgwhToTop.obj (X i)) i := by
    apply TopCat.hom_ext
    ext x
    exact TopCat.piIsoPi_hom_apply
      (fun i ↦ cgwhToTop.obj (X i)) i x
  have hCgwhPi : (piIsoPi X).hom ≫ piπ X i = Pi.π X i :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit X) ⟨i⟩
  let U : I → CompactlyGenerated.{u, v} :=
    fun i ↦ cgwhToCompactlyGenerated.obj (X i)
  have hCompactPi : (CompactlyGenerated.piIsoPi U).hom ≫
      CompactlyGenerated.piπ U i = Pi.π U i :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (CompactlyGenerated.piFanIsLimit U) ⟨i⟩
  have hTopCompactPi :
      (TopCat.piIsoPi (fun i ↦
          CompactlyGenerated.compactlyGeneratedToTop.obj (U i))).hom ≫
          TopCat.piπ (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i =
        Pi.π (fun i ↦
          CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i := by
    apply TopCat.hom_ext
    ext x
    exact TopCat.piIsoPi_hom_apply
      (fun i ↦ CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i x
  have hProj : cgwhToCompactlyGenerated.map (piπ X i) =
      CompactlyGenerated.piπ U i := by
    unfold piπ
    exact fullyFaithfulCgwhToCompactlyGenerated.map_preimage _
  have hComparisonPi : piComparisonToTop X ≫
      TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i =
        cgwhToTop.map (piπ X i) := by
    change CompactlyGenerated.piComparisonToTop U ≫
        TopCat.piπ (fun i ↦
          CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i =
      CompactlyGenerated.compactlyGeneratedToTop.map
        (cgwhToCompactlyGenerated.map (piπ X i))
    rw [hProj]
    apply (cancel_epi
      (CompactlyGenerated.compactlyGeneratedToTop.map
        (CompactlyGenerated.piIsoPi U).hom)).1
    calc
      CompactlyGenerated.compactlyGeneratedToTop.map
            (CompactlyGenerated.piIsoPi U).hom ≫
          (CompactlyGenerated.piComparisonToTop U ≫
            TopCat.piπ (fun i ↦
              CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i) =
        (CompactlyGenerated.compactlyGeneratedToTop.map
              (CompactlyGenerated.piIsoPi U).hom ≫
            CompactlyGenerated.piComparisonToTop U) ≫
          TopCat.piπ (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i :=
        (Category.assoc _ _ _).symm
      _ = (Limits.piComparison
            CompactlyGenerated.compactlyGeneratedToTop U ≫
          (TopCat.piIsoPi (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i))).hom) ≫
          TopCat.piπ (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i := by
        exact congrArg
          (fun q ↦ q ≫ TopCat.piπ (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i)
          (CompactlyGenerated.piComparisonToTop_generic_coherence U)
      _ = Limits.piComparison
            CompactlyGenerated.compactlyGeneratedToTop U ≫
          ((TopCat.piIsoPi (fun i ↦
              CompactlyGenerated.compactlyGeneratedToTop.obj (U i))).hom ≫
            TopCat.piπ (fun i ↦
              CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i) := by
        rw [Category.assoc]
      _ = Limits.piComparison
            CompactlyGenerated.compactlyGeneratedToTop U ≫
          Pi.π (fun i ↦
            CompactlyGenerated.compactlyGeneratedToTop.obj (U i)) i := by
        rw [hTopCompactPi]
      _ = CompactlyGenerated.compactlyGeneratedToTop.map (Pi.π U i) :=
        Limits.piComparison_comp_π
          CompactlyGenerated.compactlyGeneratedToTop U i
      _ = CompactlyGenerated.compactlyGeneratedToTop.map
          ((CompactlyGenerated.piIsoPi U).hom ≫
            CompactlyGenerated.piπ U i) := by rw [hCompactPi]
      _ = CompactlyGenerated.compactlyGeneratedToTop.map
            (CompactlyGenerated.piIsoPi U).hom ≫
          CompactlyGenerated.compactlyGeneratedToTop.map
            (CompactlyGenerated.piπ U i) := by
        rw [CompactlyGenerated.compactlyGeneratedToTop.map_comp]
  calc
    (cgwhToTop.map (piIsoPi X).hom ≫ piComparisonToTop X) ≫
          TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i =
        cgwhToTop.map (piIsoPi X).hom ≫
          (piComparisonToTop X ≫
            TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i) :=
      Category.assoc _ _ _
    _ = cgwhToTop.map (piIsoPi X).hom ≫
        cgwhToTop.map (piπ X i) := by rw [hComparisonPi]
    _ = cgwhToTop.map ((piIsoPi X).hom ≫ piπ X i) := by
      rw [cgwhToTop.map_comp]
    _ = cgwhToTop.map (Pi.π X i) := by rw [hCgwhPi]
    _ = Limits.piComparison cgwhToTop X ≫
        Pi.π (fun i ↦ cgwhToTop.obj (X i)) i := by
      exact (Limits.piComparison_comp_π cgwhToTop X i).symm
    _ = Limits.piComparison cgwhToTop X ≫
        ((TopCat.piIsoPi (fun i ↦ cgwhToTop.obj (X i))).hom ≫
          TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i) := by
      rw [hTopPi]
    _ = (Limits.piComparison cgwhToTop X ≫
        (TopCat.piIsoPi (fun i ↦ cgwhToTop.obj (X i))).hom) ≫
          TopCat.piπ (fun i ↦ cgwhToTop.obj (X i)) i := by
      rw [Category.assoc]

/-- The native-to-ordinary product comparison is a homeomorphism exactly
when the ordinary product topology is already compactly generated. -/
theorem piComparisonToTop_isHomeomorph_iff {I : Type v}
    (X : I → CGWH.{u, v}) :
    IsHomeomorph (piComparisonToTop X) ↔
      UCompactlyGeneratedSpace.{u}
        ((TopCat.piFan (fun i ↦ cgwhToTop.obj (X i))).pt : Type v) :=
  CompactlyGenerated.piComparisonToTop_isHomeomorph_iff
    (fun i ↦ cgwhToCompactlyGenerated.obj (X i))

/-- A countable product of first-countable CGWH spaces has ordinary product
topology. -/
theorem piComparisonToTop_isHomeomorph_of_firstCountable
    {I : Type v} [Countable I] (X : I → CGWH.{u, v})
    [∀ i, FirstCountableTopology (X i)] :
    IsHomeomorph (piComparisonToTop X) := by
  apply (piComparisonToTop_isHomeomorph_iff X).2
  change UCompactlyGeneratedSpace.{u} (∀ i, X i)
  infer_instance

private def walkingPairPiHomeomorphProd
    (X Y : CGWH.{u, v}) :
    ((TopCat.piFan (fun j : WalkingPair ↦
      cgwhToTop.obj (WalkingPair.casesOn j X Y))).pt : Type v) ≃ₜ
      ↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y) where
  toFun f := (f WalkingPair.left, f WalkingPair.right)
  invFun p j := WalkingPair.casesOn j p.1 p.2
  left_inv f := by
    funext j
    cases j <;> rfl
  right_inv p := by
    rcases p with ⟨x, y⟩
    rfl
  continuous_toFun :=
    (continuous_apply WalkingPair.left).prodMk
      (continuous_apply WalkingPair.right)
  continuous_invFun := by
    apply continuous_pi
    intro j
    cases j
    · exact continuous_fst
    · exact continuous_snd

private theorem walkingPairPiHomeomorphProd_apply_left
    (X Y : CGWH.{u, v})
    (x : ((TopCat.piFan (fun j : WalkingPair ↦
      cgwhToTop.obj (WalkingPair.casesOn j X Y))).pt : Type v)) :
    (walkingPairPiHomeomorphProd X Y x).1 =
      (show ↑(cgwhToTop.obj X) from x WalkingPair.left) := by
  change (x WalkingPair.left, x WalkingPair.right).1 = x WalkingPair.left
  rfl

private theorem walkingPairPiHomeomorphProd_apply_right
    (X Y : CGWH.{u, v})
    (x : ((TopCat.piFan (fun j : WalkingPair ↦
      cgwhToTop.obj (WalkingPair.casesOn j X Y))).pt : Type v)) :
    (walkingPairPiHomeomorphProd X Y x).2 =
      (show ↑(cgwhToTop.obj Y) from x WalkingPair.right) := by
  change (x WalkingPair.left, x WalkingPair.right).2 = x WalkingPair.right
  rfl

/-- Inclusion of the selected native binary product into the ordinary pair. -/
noncomputable def prodComparisonToTop (X Y : CGWH.{u, v}) :
    cgwhToTop.obj (X ⨯ Y) ⟶
      TopCat.of (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
  Limits.prodComparison cgwhToTop X Y ≫
    (TopCat.prodIsoProd (cgwhToTop.obj X) (cgwhToTop.obj Y)).hom

/-- The native-to-ordinary binary-product comparison has the expected first
projection. -/
@[reassoc]
theorem prodComparisonToTop_fst (X Y : CGWH.{u, v}) :
    prodComparisonToTop X Y ≫ TopCat.prodFst =
      cgwhToTop.map (Limits.prod.fst : X ⨯ Y ⟶ X) := by
  unfold prodComparisonToTop
  rw [Category.assoc, TopCat.prodIsoProd_hom_fst,
    Limits.prodComparison_fst]

/-- The native-to-ordinary binary-product comparison has the expected second
projection. -/
@[reassoc]
theorem prodComparisonToTop_snd (X Y : CGWH.{u, v}) :
    prodComparisonToTop X Y ≫ TopCat.prodSnd =
      cgwhToTop.map (Limits.prod.snd : X ⨯ Y ⟶ Y) := by
  unfold prodComparisonToTop
  rw [Category.assoc, TopCat.prodIsoProd_hom_snd,
    Limits.prodComparison_snd]

/-- The native-to-ordinary binary-product comparison is a bijection on
points.  This does not assert that it is a homeomorphism. -/
theorem prodComparisonToTop_bijective (X Y : CGWH.{u, v}) :
    Function.Bijective (prodComparisonToTop X Y) := by
  have hFstApply (z : (X ⨯ Y : CGWH.{u, v})) :
      (prodComparisonToTop X Y z).1 =
        (Limits.prod.fst : X ⨯ Y ⟶ X) z := by
    have hz := ConcreteCategory.congr_hom
      (prodComparisonToTop_fst X Y) z
    change (prodComparisonToTop X Y z).1 =
      cgwhToTop.map (Limits.prod.fst : X ⨯ Y ⟶ X) z at hz
    exact hz
  have hSndApply (z : (X ⨯ Y : CGWH.{u, v})) :
      (prodComparisonToTop X Y z).2 =
        (Limits.prod.snd : X ⨯ Y ⟶ Y) z := by
    have hz := ConcreteCategory.congr_hom
      (prodComparisonToTop_snd X Y) z
    change (prodComparisonToTop X Y z).2 =
      cgwhToTop.map (Limits.prod.snd : X ⨯ Y ⟶ Y) z at hz
    exact hz
  constructor
  · intro z z' h
    let Q : CGWH.{u, v} := CGWH.of PUnit.{v + 1}
    let f : Q ⟶ X ⨯ Y :=
      ConcreteCategory.ofHom (ContinuousMap.const PUnit z)
    let g : Q ⟶ X ⨯ Y :=
      ConcreteCategory.ofHom (ContinuousMap.const PUnit z')
    have hfg : f = g := by
      apply Limits.prod.hom_ext
      · apply ConcreteCategory.hom_ext
        intro q
        have h' := congrArg Prod.fst h
        change (Limits.prod.fst : X ⨯ Y ⟶ X) z =
          (Limits.prod.fst : X ⨯ Y ⟶ X) z'
        exact (hFstApply z).symm.trans (h'.trans (hFstApply z'))
      · apply ConcreteCategory.hom_ext
        intro q
        have h' := congrArg Prod.snd h
        change (Limits.prod.snd : X ⨯ Y ⟶ Y) z =
          (Limits.prod.snd : X ⨯ Y ⟶ Y) z'
        exact (hSndApply z).symm.trans (h'.trans (hSndApply z'))
    exact ConcreteCategory.congr_hom hfg PUnit.unit
  · rintro ⟨x, y⟩
    let Q : CGWH.{u, v} := CGWH.of PUnit.{v + 1}
    let fx : Q ⟶ X := ConcreteCategory.ofHom
      (ContinuousMap.const PUnit x)
    let fy : Q ⟶ Y := ConcreteCategory.ofHom
      (ContinuousMap.const PUnit y)
    let z : (X ⨯ Y : CGWH.{u, v}) :=
      Limits.prod.lift fx fy PUnit.unit
    refine ⟨z, Prod.ext ?_ ?_⟩
    · exact (hFstApply z).trans (ConcreteCategory.congr_hom
        (Limits.prod.lift_fst fx fy) PUnit.unit)
    · exact (hSndApply z).trans (ConcreteCategory.congr_hom
        (Limits.prod.lift_snd fx fy) PUnit.unit)

/-- If the left factor is locally compact Hausdorff, the selected native
binary product has the ordinary product topology. -/
theorem prodComparisonToTop_isHomeomorph_of_locallyCompact_left
    (X Y : CGWH.{u, v}) [LocallyCompactSpace X] [T2Space X] :
    IsHomeomorph (prodComparisonToTop X Y) := by
  let _ : UCompactlyGeneratedSpace.{u}
      (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
      (A := X) (B := Y)
  let liftedFamily : ULift.{v} WalkingPair → CGWH.{u, v} :=
    pairFunction X Y ∘ Equiv.ulift.{v, 0}
  let pairIso : (∏ᶜ pairFunction X Y) ≅ X ⨯ Y :=
    Pi.isoLimit (pair X Y)
  let reindexIso : (∏ᶜ liftedFamily) ≅ ∏ᶜ pairFunction X Y :=
    Limits.Pi.reindex (C := CGWH.{u, v})
      (Equiv.ulift.{v, 0}) (pairFunction X Y)
  let binaryToPi : X ⨯ Y ≅ piObj liftedFamily :=
    pairIso.symm ≪≫ reindexIso.symm ≪≫ piIsoPi liftedFamily
  have hPairFst : pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.left =
      Limits.prod.fst := Pi.isoLimit_inv_π (pair X Y) WalkingPair.left
  have hPairSnd : pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.right =
      Limits.prod.snd := Pi.isoLimit_inv_π (pair X Y) WalkingPair.right
  have hPiFst : (piIsoPi liftedFamily).hom ≫
      piπ liftedFamily (ULift.up WalkingPair.left) =
        Pi.π liftedFamily (ULift.up WalkingPair.left) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit liftedFamily)
      ⟨ULift.up WalkingPair.left⟩
  have hPiSnd : (piIsoPi liftedFamily).hom ≫
      piπ liftedFamily (ULift.up WalkingPair.right) =
        Pi.π liftedFamily (ULift.up WalkingPair.right) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit liftedFamily)
      ⟨ULift.up WalkingPair.right⟩
  have hBinaryFst : binaryToPi.hom ≫
      piπ liftedFamily (ULift.up WalkingPair.left) = Limits.prod.fst := by
    simp only [binaryToPi, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hPiFst, Limits.Pi.reindex_inv_π]
    change pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.left = _
    exact hPairFst
  have hBinarySnd : binaryToPi.hom ≫
      piπ liftedFamily (ULift.up WalkingPair.right) = Limits.prod.snd := by
    simp only [binaryToPi, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hPiSnd, Limits.Pi.reindex_inv_π]
    change pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.right = _
    exact hPairSnd
  let rawPairHomeo :
      ((TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt :
          Type v) ≃ₜ
        ↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y) :=
    (Homeomorph.piCongrLeft
      (Y := fun j : WalkingPair =>
        ↑(cgwhToTop.obj (pairFunction X Y j)))
      (Equiv.ulift.{v, 0})).trans
        (walkingPairPiHomeomorphProd X Y)
  let rawPairIso :
      (TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt ≅
        TopCat.of (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    TopCat.isoOfHomeo rawPairHomeo
  have hRawFst : rawPairIso.hom ≫ TopCat.prodFst =
      TopCat.piπ (fun j => cgwhToTop.obj (liftedFamily j))
        (ULift.up WalkingPair.left) := by
    apply TopCat.hom_ext
    ext z
    rfl
  have hRawSnd : rawPairIso.hom ≫ TopCat.prodSnd =
      TopCat.piπ (fun j => cgwhToTop.obj (liftedFamily j))
        (ULift.up WalkingPair.right) := by
    apply TopCat.hom_ext
    ext z
    rfl
  have hComparison (j : ULift.{v} WalkingPair) :
      piComparisonToTop liftedFamily ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j =
        cgwhToTop.map (piπ liftedFamily j) := by
    apply (cancel_epi (cgwhToTop.map (piIsoPi liftedFamily).hom)).1
    have hPi : (piIsoPi liftedFamily).hom ≫
        piπ liftedFamily j = Pi.π liftedFamily j :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (limit.isLimit _) (piFanIsLimit liftedFamily) ⟨j⟩
    have hTop :
        (TopCat.piIsoPi
            (fun k => cgwhToTop.obj (liftedFamily k))).hom ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j =
        Pi.π (fun k => cgwhToTop.obj (liftedFamily k)) j := by
      apply TopCat.hom_ext
      ext z
      exact TopCat.piIsoPi_hom_apply
        (fun k => cgwhToTop.obj (liftedFamily k)) j z
    calc
      cgwhToTop.map (piIsoPi liftedFamily).hom ≫
          (piComparisonToTop liftedFamily ≫
            TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j) =
        (cgwhToTop.map (piIsoPi liftedFamily).hom ≫
            piComparisonToTop liftedFamily) ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j :=
        (Category.assoc _ _ _).symm
      _ = (Limits.piComparison cgwhToTop liftedFamily ≫
            (TopCat.piIsoPi
              (fun k => cgwhToTop.obj (liftedFamily k))).hom) ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j := by
        exact congrArg
          (fun q ↦ q ≫ TopCat.piπ
            (fun k => cgwhToTop.obj (liftedFamily k)) j)
          (piComparisonToTop_generic_coherence liftedFamily)
      _ = Limits.piComparison cgwhToTop liftedFamily ≫
          ((TopCat.piIsoPi
              (fun k => cgwhToTop.obj (liftedFamily k))).hom ≫
            TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j) :=
        Category.assoc _ _ _
      _ = Limits.piComparison cgwhToTop liftedFamily ≫
          Pi.π (fun k => cgwhToTop.obj (liftedFamily k)) j := by
        rw [hTop]
      _ = cgwhToTop.map (Pi.π liftedFamily j) :=
        Limits.piComparison_comp_π cgwhToTop liftedFamily j
      _ = cgwhToTop.map
          ((piIsoPi liftedFamily).hom ≫ piπ liftedFamily j) := by
        rw [hPi]
      _ = cgwhToTop.map (piIsoPi liftedFamily).hom ≫
          cgwhToTop.map (piπ liftedFamily j) := by
        rw [cgwhToTop.map_comp]
  have hProdFst : prodComparisonToTop X Y ≫ TopCat.prodFst =
      cgwhToTop.map (Limits.prod.fst : X ⨯ Y ⟶ X) :=
    prodComparisonToTop_fst X Y
  have hProdSnd : prodComparisonToTop X Y ≫ TopCat.prodSnd =
      cgwhToTop.map (Limits.prod.snd : X ⨯ Y ⟶ Y) :=
    prodComparisonToTop_snd X Y
  have hCoherence :
      cgwhToTop.map binaryToPi.hom ≫
          piComparisonToTop liftedFamily ≫ rawPairIso.hom =
        prodComparisonToTop X Y := by
    apply TopCat.hom_ext
    ext z
    · have h₁ := ConcreteCategory.congr_hom hRawFst
          (piComparisonToTop liftedFamily (binaryToPi.hom z))
      have h₂ := ConcreteCategory.congr_hom
        (hComparison (ULift.up WalkingPair.left)) (binaryToPi.hom z)
      have h₃ := ConcreteCategory.congr_hom hBinaryFst z
      have h₄ := ConcreteCategory.congr_hom hProdFst z
      change (piComparisonToTop liftedFamily (binaryToPi.hom z))
          (ULift.up WalkingPair.left) =
        piπ liftedFamily (ULift.up WalkingPair.left)
          (binaryToPi.hom z) at h₂
      change piπ liftedFamily (ULift.up WalkingPair.left)
          (binaryToPi.hom z) = (Limits.prod.fst : X ⨯ Y ⟶ X) z at h₃
      change (prodComparisonToTop X Y z).1 =
        (Limits.prod.fst : X ⨯ Y ⟶ X) z at h₄
      exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
    · have h₁ := ConcreteCategory.congr_hom hRawSnd
          (piComparisonToTop liftedFamily (binaryToPi.hom z))
      have h₂ := ConcreteCategory.congr_hom
        (hComparison (ULift.up WalkingPair.right)) (binaryToPi.hom z)
      have h₃ := ConcreteCategory.congr_hom hBinarySnd z
      have h₄ := ConcreteCategory.congr_hom hProdSnd z
      change (piComparisonToTop liftedFamily (binaryToPi.hom z))
          (ULift.up WalkingPair.right) =
        piπ liftedFamily (ULift.up WalkingPair.right)
          (binaryToPi.hom z) at h₂
      change piπ liftedFamily (ULift.up WalkingPair.right)
          (binaryToPi.hom z) = (Limits.prod.snd : X ⨯ Y ⟶ Y) z at h₃
      change (prodComparisonToTop X Y z).2 =
        (Limits.prod.snd : X ⨯ Y ⟶ Y) z at h₄
      exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
  let P := CompactlyGenerated.compactHausProbes.{u}
  have hPairGenerated : IsGeneratedBy P
      (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    isGeneratedBy_compactHausProbes_iff.2 inferInstance
  let _ : IsGeneratedBy P
      (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    hPairGenerated
  have hPiGenerated : IsGeneratedBy P
      ((TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt :
        Type v) :=
    rawPairHomeo.symm.isQuotientMap.isGeneratedBy
  have hPiCompactlyGenerated : UCompactlyGeneratedSpace.{u}
      ((TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt :
        Type v) :=
    isGeneratedBy_compactHausProbes_iff.1 hPiGenerated
  have hPiHomeo : IsHomeomorph (piComparisonToTop liftedFamily) :=
    (piComparisonToTop_isHomeomorph_iff liftedFamily).2
      hPiCompactlyGenerated
  let _ : IsIso (piComparisonToTop liftedFamily) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr hPiHomeo
  have hComposite : IsHomeomorph
      (cgwhToTop.map binaryToPi.hom ≫
        piComparisonToTop liftedFamily ≫ rawPairIso.hom) :=
    (TopCat.isIso_iff_isHomeomorph _).mp (by infer_instance)
  rw [hCoherence] at hComposite
  exact hComposite

/-- If the right factor is locally compact Hausdorff, the selected native
binary product has the ordinary product topology. -/
theorem prodComparisonToTop_isHomeomorph_of_locallyCompact_right
    (X Y : CGWH.{u, v}) [LocallyCompactSpace Y] [T2Space Y] :
    IsHomeomorph (prodComparisonToTop X Y) := by
  have hYX : IsHomeomorph (prodComparisonToTop Y X) :=
    prodComparisonToTop_isHomeomorph_of_locallyCompact_left Y X
  let rawSwap :
      TopCat.of (↑(cgwhToTop.obj Y) × ↑(cgwhToTop.obj X)) ≅
      TopCat.of (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    TopCat.isoOfHomeo
      (Homeomorph.prodComm ↑(cgwhToTop.obj Y) ↑(cgwhToTop.obj X))
  have hRawBraiding :
      (Limits.prod.braiding (cgwhToTop.obj X) (cgwhToTop.obj Y)).hom ≫
          (TopCat.prodIsoProd (cgwhToTop.obj Y)
            (cgwhToTop.obj X)).hom ≫ rawSwap.hom =
        (TopCat.prodIsoProd (cgwhToTop.obj X)
          (cgwhToTop.obj Y)).hom := by
    apply TopCat.hom_ext
    ext z
    · change (Limits.prod.snd :
          cgwhToTop.obj Y ⨯ cgwhToTop.obj X ⟶ cgwhToTop.obj X)
          ((Limits.prod.braiding (cgwhToTop.obj X)
            (cgwhToTop.obj Y)).hom z) =
        (Limits.prod.fst :
          cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj X) z
      simpa only [Limits.prod.braiding_hom, CategoryTheory.comp_apply] using
        ConcreteCategory.congr_hom
          (Limits.prod.lift_snd
            (Limits.prod.snd :
              cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj Y)
            (Limits.prod.fst :
              cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj X)) z
    · change (Limits.prod.fst :
          cgwhToTop.obj Y ⨯ cgwhToTop.obj X ⟶ cgwhToTop.obj Y)
          ((Limits.prod.braiding (cgwhToTop.obj X)
            (cgwhToTop.obj Y)).hom z) =
        (Limits.prod.snd :
          cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj Y) z
      simpa only [Limits.prod.braiding_hom, CategoryTheory.comp_apply] using
        ConcreteCategory.congr_hom
          (Limits.prod.lift_fst
            (Limits.prod.snd :
              cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj Y)
            (Limits.prod.fst :
              cgwhToTop.obj X ⨯ cgwhToTop.obj Y ⟶ cgwhToTop.obj X)) z
  have hCoherence :
      cgwhToTop.map (Limits.prod.braiding X Y).hom ≫
          prodComparisonToTop Y X ≫ rawSwap.hom =
        prodComparisonToTop X Y := by
    unfold prodComparisonToTop
    calc
      cgwhToTop.map (Limits.prod.braiding X Y).hom ≫
          (Limits.prodComparison cgwhToTop Y X ≫
            (TopCat.prodIsoProd (cgwhToTop.obj Y)
              (cgwhToTop.obj X)).hom) ≫ rawSwap.hom =
        ((cgwhToTop.map (Limits.prod.braiding X Y).hom ≫
            Limits.prodComparison cgwhToTop Y X) ≫
          (TopCat.prodIsoProd (cgwhToTop.obj Y)
            (cgwhToTop.obj X)).hom) ≫ rawSwap.hom := by
          simp only [Category.assoc]
      _ = ((Limits.prodComparison cgwhToTop X Y ≫
            (Limits.prod.braiding (cgwhToTop.obj X)
              (cgwhToTop.obj Y)).hom) ≫
          (TopCat.prodIsoProd (cgwhToTop.obj Y)
            (cgwhToTop.obj X)).hom) ≫ rawSwap.hom := by
        rw [Limits.map_braiding_hom_comp_prodComparison
          cgwhToTop (A := Y) (B := X)]
      _ = Limits.prodComparison cgwhToTop X Y ≫
          ((Limits.prod.braiding (cgwhToTop.obj X)
              (cgwhToTop.obj Y)).hom ≫
            (TopCat.prodIsoProd (cgwhToTop.obj Y)
              (cgwhToTop.obj X)).hom ≫ rawSwap.hom) := by
        simp only [Category.assoc]
      _ = Limits.prodComparison cgwhToTop X Y ≫
          (TopCat.prodIsoProd (cgwhToTop.obj X)
            (cgwhToTop.obj Y)).hom := by
        rw [hRawBraiding]
  let _ : IsIso (prodComparisonToTop Y X) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr hYX
  have hComposite : IsHomeomorph
      (cgwhToTop.map (Limits.prod.braiding X Y).hom ≫
        prodComparisonToTop Y X ≫ rawSwap.hom) :=
    (TopCat.isIso_iff_isHomeomorph _).mp (by infer_instance)
  rw [hCoherence] at hComposite
  exact hComposite

/-- If both factors are first countable, the selected native binary product
has the ordinary product topology. -/
theorem prodComparisonToTop_isHomeomorph_of_firstCountable
    (X Y : CGWH.{u, v})
    [FirstCountableTopology X] [FirstCountableTopology Y] :
    IsHomeomorph (prodComparisonToTop X Y) := by
  let liftedFamily : ULift.{v} WalkingPair → CGWH.{u, v} :=
    pairFunction X Y ∘ Equiv.ulift.{v, 0}
  let pairIso : (∏ᶜ pairFunction X Y) ≅ X ⨯ Y :=
    Pi.isoLimit (pair X Y)
  let reindexIso : (∏ᶜ liftedFamily) ≅ ∏ᶜ pairFunction X Y :=
    Limits.Pi.reindex (C := CGWH.{u, v})
      (Equiv.ulift.{v, 0}) (pairFunction X Y)
  let binaryToPi : X ⨯ Y ≅ piObj liftedFamily :=
    pairIso.symm ≪≫ reindexIso.symm ≪≫ piIsoPi liftedFamily
  have hPairFst : pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.left =
      Limits.prod.fst := Pi.isoLimit_inv_π (pair X Y) WalkingPair.left
  have hPairSnd : pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.right =
      Limits.prod.snd := Pi.isoLimit_inv_π (pair X Y) WalkingPair.right
  have hPiFst : (piIsoPi liftedFamily).hom ≫
      piπ liftedFamily (ULift.up WalkingPair.left) =
        Pi.π liftedFamily (ULift.up WalkingPair.left) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit liftedFamily)
      ⟨ULift.up WalkingPair.left⟩
  have hPiSnd : (piIsoPi liftedFamily).hom ≫
      piπ liftedFamily (ULift.up WalkingPair.right) =
        Pi.π liftedFamily (ULift.up WalkingPair.right) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit _) (piFanIsLimit liftedFamily)
      ⟨ULift.up WalkingPair.right⟩
  have hBinaryFst : binaryToPi.hom ≫
      piπ liftedFamily (ULift.up WalkingPair.left) = Limits.prod.fst := by
    simp only [binaryToPi, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hPiFst, Limits.Pi.reindex_inv_π]
    change pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.left = _
    exact hPairFst
  have hBinarySnd : binaryToPi.hom ≫
      piπ liftedFamily (ULift.up WalkingPair.right) = Limits.prod.snd := by
    simp only [binaryToPi, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hPiSnd, Limits.Pi.reindex_inv_π]
    change pairIso.inv ≫ Pi.π (pairFunction X Y) WalkingPair.right = _
    exact hPairSnd
  let rawPairHomeo :
      ((TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt :
          Type v) ≃ₜ
        ↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y) :=
    (Homeomorph.piCongrLeft
      (Y := fun j : WalkingPair =>
        ↑(cgwhToTop.obj (pairFunction X Y j)))
      (Equiv.ulift.{v, 0})).trans
        (walkingPairPiHomeomorphProd X Y)
  let rawPairIso :
      (TopCat.piFan (fun j => cgwhToTop.obj (liftedFamily j))).pt ≅
        TopCat.of (↑(cgwhToTop.obj X) × ↑(cgwhToTop.obj Y)) :=
    TopCat.isoOfHomeo rawPairHomeo
  have hRawFst : rawPairIso.hom ≫ TopCat.prodFst =
      TopCat.piπ (fun j => cgwhToTop.obj (liftedFamily j))
        (ULift.up WalkingPair.left) := by
    apply TopCat.hom_ext
    ext z
    rfl
  have hRawSnd : rawPairIso.hom ≫ TopCat.prodSnd =
      TopCat.piπ (fun j => cgwhToTop.obj (liftedFamily j))
        (ULift.up WalkingPair.right) := by
    apply TopCat.hom_ext
    ext z
    rfl
  have hComparison (j : ULift.{v} WalkingPair) :
      piComparisonToTop liftedFamily ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j =
        cgwhToTop.map (piπ liftedFamily j) := by
    apply (cancel_epi (cgwhToTop.map (piIsoPi liftedFamily).hom)).1
    have hPi : (piIsoPi liftedFamily).hom ≫
        piπ liftedFamily j = Pi.π liftedFamily j :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        (limit.isLimit _) (piFanIsLimit liftedFamily) ⟨j⟩
    have hTop :
        (TopCat.piIsoPi
            (fun k => cgwhToTop.obj (liftedFamily k))).hom ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j =
        Pi.π (fun k => cgwhToTop.obj (liftedFamily k)) j := by
      apply TopCat.hom_ext
      ext z
      exact TopCat.piIsoPi_hom_apply
        (fun k => cgwhToTop.obj (liftedFamily k)) j z
    calc
      cgwhToTop.map (piIsoPi liftedFamily).hom ≫
          (piComparisonToTop liftedFamily ≫
            TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j) =
        (cgwhToTop.map (piIsoPi liftedFamily).hom ≫
            piComparisonToTop liftedFamily) ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j :=
        (Category.assoc _ _ _).symm
      _ = (Limits.piComparison cgwhToTop liftedFamily ≫
            (TopCat.piIsoPi
              (fun k => cgwhToTop.obj (liftedFamily k))).hom) ≫
          TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j := by
        exact congrArg
          (fun q ↦ q ≫ TopCat.piπ
            (fun k => cgwhToTop.obj (liftedFamily k)) j)
          (piComparisonToTop_generic_coherence liftedFamily)
      _ = Limits.piComparison cgwhToTop liftedFamily ≫
          ((TopCat.piIsoPi
              (fun k => cgwhToTop.obj (liftedFamily k))).hom ≫
            TopCat.piπ (fun k => cgwhToTop.obj (liftedFamily k)) j) :=
        Category.assoc _ _ _
      _ = Limits.piComparison cgwhToTop liftedFamily ≫
          Pi.π (fun k => cgwhToTop.obj (liftedFamily k)) j := by
        rw [hTop]
      _ = cgwhToTop.map (Pi.π liftedFamily j) :=
        Limits.piComparison_comp_π cgwhToTop liftedFamily j
      _ = cgwhToTop.map
          ((piIsoPi liftedFamily).hom ≫ piπ liftedFamily j) := by
        rw [hPi]
      _ = cgwhToTop.map (piIsoPi liftedFamily).hom ≫
          cgwhToTop.map (piπ liftedFamily j) := by
        rw [cgwhToTop.map_comp]
  have hProdFst : prodComparisonToTop X Y ≫ TopCat.prodFst =
      cgwhToTop.map (Limits.prod.fst : X ⨯ Y ⟶ X) :=
    prodComparisonToTop_fst X Y
  have hProdSnd : prodComparisonToTop X Y ≫ TopCat.prodSnd =
      cgwhToTop.map (Limits.prod.snd : X ⨯ Y ⟶ Y) :=
    prodComparisonToTop_snd X Y
  have hCoherence :
      cgwhToTop.map binaryToPi.hom ≫
          piComparisonToTop liftedFamily ≫ rawPairIso.hom =
        prodComparisonToTop X Y := by
    apply TopCat.hom_ext
    ext z
    · have h₁ := ConcreteCategory.congr_hom hRawFst
          (piComparisonToTop liftedFamily (binaryToPi.hom z))
      have h₂ := ConcreteCategory.congr_hom
        (hComparison (ULift.up WalkingPair.left)) (binaryToPi.hom z)
      have h₃ := ConcreteCategory.congr_hom hBinaryFst z
      have h₄ := ConcreteCategory.congr_hom hProdFst z
      change (piComparisonToTop liftedFamily (binaryToPi.hom z))
          (ULift.up WalkingPair.left) =
        piπ liftedFamily (ULift.up WalkingPair.left)
          (binaryToPi.hom z) at h₂
      change piπ liftedFamily (ULift.up WalkingPair.left)
          (binaryToPi.hom z) = (Limits.prod.fst : X ⨯ Y ⟶ X) z at h₃
      change (prodComparisonToTop X Y z).1 =
        (Limits.prod.fst : X ⨯ Y ⟶ X) z at h₄
      exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
    · have h₁ := ConcreteCategory.congr_hom hRawSnd
          (piComparisonToTop liftedFamily (binaryToPi.hom z))
      have h₂ := ConcreteCategory.congr_hom
        (hComparison (ULift.up WalkingPair.right)) (binaryToPi.hom z)
      have h₃ := ConcreteCategory.congr_hom hBinarySnd z
      have h₄ := ConcreteCategory.congr_hom hProdSnd z
      change (piComparisonToTop liftedFamily (binaryToPi.hom z))
          (ULift.up WalkingPair.right) =
        piπ liftedFamily (ULift.up WalkingPair.right)
          (binaryToPi.hom z) at h₂
      change piπ liftedFamily (ULift.up WalkingPair.right)
          (binaryToPi.hom z) = (Limits.prod.snd : X ⨯ Y ⟶ Y) z at h₃
      change (prodComparisonToTop X Y z).2 =
        (Limits.prod.snd : X ⨯ Y ⟶ Y) z at h₄
      exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
  let _ : ∀ j, FirstCountableTopology (liftedFamily j) := by
    rintro ⟨j⟩
    cases j
    · change FirstCountableTopology X
      infer_instance
    · change FirstCountableTopology Y
      infer_instance
  have hPiHomeo : IsHomeomorph (piComparisonToTop liftedFamily) :=
    piComparisonToTop_isHomeomorph_of_firstCountable liftedFamily
  let _ : IsIso (piComparisonToTop liftedFamily) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr hPiHomeo
  have hComposite : IsHomeomorph
      (cgwhToTop.map binaryToPi.hom ≫
        piComparisonToTop liftedFamily ≫ rawPairIso.hom) :=
    (TopCat.isIso_iff_isHomeomorph _).mp (by infer_instance)
  rw [hCoherence] at hComposite
  exact hComposite

end CGWH

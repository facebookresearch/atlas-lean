/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Kunneth.SpectralSequence
public import MathlibExt.Algebra.Homology.PartialTotalEdgeMaps

/-!
# The canonical zero-column edge of the Künneth spectral sequence

This file defines the canonical finite sum of homology tensor pairings.  When
the first complex is termwise flat, it identifies that map with the
zero-column edge for every explicitly supplied Cartan--Eilenberg resolution.

## Mathematical reference and scope

See Weibel, *An Introduction to Homological Algebra*, Theorem 5.6.4 and
Künneth Formula 5.6.5 for the Künneth spectral sequence and its edge map.
The complexes here are nonnegatively graded, and each comparison with the
edge is objectwise for a supplied Cartan--Eilenberg resolution.  The left map
itself is canonical, but this file does not package functoriality, prove
resolution independence of the spectral right edge, or construct either a
natural splitting or the classical noncanonical splitting.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R]

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- The finite antidiagonal indexing tensor products in total degree `n`. -/
abbrev KunnethTensorIndex (n : ℕ) := KunnethAntidiagonal n

/-- The canonical identification of Tor zero with the underived tensor
product, with Tor derived in the second factor. -/
noncomputable def torZeroIso (A D : ModuleCat.{u} R) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj A).obj D ≅ A ⊗ D :=
  (Functor.leftDerivedZeroIsoSelf
    ((tensoringLeft (ModuleCat.{u} R)).obj A)).app D

/-- The canonical finite sum of homology tensor pairings in total degree
`n`. -/
noncomputable def kunnethHomologyTensorMap
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2) ⟶
      (tensorObj K L).homology n :=
  biproduct.desc fun ij =>
    ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K L))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K L)))
        ij.val.1 ij.val.2 ≫
      (homologyIsoOfEq (tensorObj K L)
        (Finset.mem_antidiagonal.mp ij.property)).hom

/-- The selected component of the canonical Künneth homology tensor map. -/
theorem kunnethHomologyTensorMap_ι
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (ij : KunnethTensorIndex n) :
    biproduct.ι
        (fun kl : KunnethTensorIndex n =>
          K.homology kl.val.1 ⊗ L.homology kl.val.2) ij ≫
        kunnethHomologyTensorMap K L n =
      ChainGradedPairing.pairHomology
          (𝟙 (tensorObj K L))
          (ChainGradedPairing.homologyDescentData
            (𝟙 (tensorObj K L)))
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K L)
          (Finset.mem_antidiagonal.mp ij.property)).hom := by
  apply biproduct.ι_desc

private theorem termColumnZeroHomologyAugmentation_comp_torZeroIso_inv
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) (q : ℕ)
    (ij : KunnethAntidiagonal q) :
    ((tensoringLeft (ModuleCat.{u} R)).obj
          (K.homology ij.val.1)).map
          (P.termColumnZeroHomologyAugmentation ij.val.2) ≫
        (torZeroIso (K.homology ij.val.1)
          (L.homology ij.val.2)).inv ≫
        biproduct.ι
          (fun kl : KunnethAntidiagonal q =>
            ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
              (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij ≫
        (kunnethTorResolutionHomologyIso K P 0 q).inv =
      (kunnethTorResolutionSummand K P ij).pOpcycles 0 ≫
        (kunnethTorResolutionSummand K P ij).isoHomologyι₀.inv ≫
        HomologicalComplex.homologyMap
          (biproduct.ι
            (fun kl : KunnethAntidiagonal q =>
              kunnethTorResolutionSummand K P kl) ij) 0 := by
  let A : KunnethAntidiagonal q →
      ChainComplex (ModuleCat.{u} R) ℕ := fun kl =>
    kunnethTorResolutionSummand K P kl
  let TorFamily : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    (Functor.leftDerived
      ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology kl.val.1)) 0).obj
        (L.homology kl.val.2)
  let T := (tensoringLeft (ModuleCat.{u} R)).obj
    (K.homology ij.val.1)
  let rep : T.obj
      ((P.bicomplex.verticalHomologyComplex ij.val.2).X 0) ⟶
        (A ij).homology 0 :=
    (A ij).pOpcycles 0 ≫ (A ij).isoHomologyι₀.inv
  let ePublic : (⨁ A).homology 0 ≅ ⨁ TorFamily :=
    kunnethTorResolutionHomologyIso K P 0 q
  let eTor : (A ij).homology 0 ≅ TorFamily ij :=
    ((P.cartanEilenbergVerticalHomologyResolution ij.val.2).isoLeftDerivedObj
      T 0).symm
  let eZero : TorFamily ij ≅ T.obj (L.homology ij.val.2) :=
    torZeroIso (K.homology ij.val.1) (L.homology ij.val.2)
  change T.map (P.termColumnZeroHomologyAugmentation ij.val.2) ≫
        eZero.inv ≫
        biproduct.ι TorFamily ij ≫ ePublic.inv =
      rep ≫ HomologicalComplex.homologyMap (biproduct.ι A ij) 0
  have hZero := kunnethTorResolutionHomologyIso_zero_component K P q ij
  have hι := kunnethTorResolutionHomologyIso_ι K P 0 q ij
  change rep ≫ HomologicalComplex.homologyMap (biproduct.ι A ij) 0 ≫
      ePublic.hom ≫
      biproduct.π TorFamily ij ≫
      eZero.hom =
    T.map (P.termColumnZeroHomologyAugmentation ij.val.2) at hZero
  change HomologicalComplex.homologyMap (biproduct.ι A ij) 0 ≫ ePublic.hom =
    eTor.hom ≫ biproduct.ι TorFamily ij at hι
  have hRep :
      rep ≫ eTor.hom ≫ eZero.hom =
        T.map (P.termColumnZeroHomologyAugmentation ij.val.2) := by
    rw [reassoc_of% hι] at hZero
    simp only [biproduct.ι_π_self_assoc] at hZero
    exact hZero
  have hιInv : biproduct.ι TorFamily ij ≫ ePublic.inv =
      eTor.inv ≫ HomologicalComplex.homologyMap (biproduct.ι A ij) 0 := by
    apply (cancel_mono ePublic.hom).1
    calc
      (biproduct.ι TorFamily ij ≫ ePublic.inv) ≫ ePublic.hom =
          biproduct.ι TorFamily ij := by
        rw [Category.assoc, ePublic.inv_hom_id, Category.comp_id]
      _ = (eTor.inv ≫
            HomologicalComplex.homologyMap (biproduct.ι A ij) 0) ≫
          ePublic.hom := by
        rw [Category.assoc, hι, eTor.inv_hom_id_assoc]
  have hιInvTail := congrArg
    (fun f => T.map (P.termColumnZeroHomologyAugmentation ij.val.2) ≫
      eZero.inv ≫ f) hιInv
  refine hιInvTail.trans ?_
  have hAugInv :
      T.map (P.termColumnZeroHomologyAugmentation ij.val.2) ≫
          eZero.inv ≫ eTor.inv = rep := by
    calc
      T.map (P.termColumnZeroHomologyAugmentation ij.val.2) ≫
            eZero.inv ≫ eTor.inv =
          (rep ≫ eTor.hom ≫ eZero.hom) ≫
            eZero.inv ≫ eTor.inv :=
        congrArg (fun f => f ≫ eZero.inv ≫ eTor.inv) hRep.symm
      _ = rep := by
        simp only [Category.assoc, eZero.hom_inv_id_assoc]
        rw [eTor.hom_inv_id, Category.comp_id]
  have hAugInvTail := congrArg
    (fun f => f ≫ HomologicalComplex.homologyMap (biproduct.ι A ij) 0)
      hAugInv
  simpa only [Category.assoc] using hAugInvTail

/-- If the first complex is termwise flat, the canonical homology tensor map
is the literal chosen zero-column edge of the Künneth spectral sequence for
every supplied Cartan--Eilenberg resolution. -/
theorem kunnethHomologyTensorMap_eq_p_zero_edge
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    kunnethHomologyTensorMap K L n =
      (biproduct.mapIso
        (fun ij : KunnethTensorIndex n =>
          (torZeroIso
            (K.homology ij.val.1)
            (L.homology ij.val.2)).symm)).hom ≫
      (tensorCartanEilenbergSecondPageIsoAt K P 0 n).inv ≫
      (kunnethCEBicomplex K P).partialTotalZeroColumnEdge n ≫
      (tensorCartanEilenbergAbutmentIso K P hK n).hom := by
  apply biproduct.hom_ext'
  intro ij
  rw [kunnethHomologyTensorMap_ι]
  simp only [biproduct.mapIso_hom]
  rw [biproduct.ι_map_assoc]
  let B := kunnethCEBicomplex K P
  let χ := B.partialTotalFirstPageChoice
  let As : KunnethAntidiagonal n →
      ChainComplex (ModuleCat.{u} R) ℕ := fun kl =>
    kunnethTorResolutionSummand K P kl
  let Res := ⨁ As
  let A := As ij
  let T := (tensoringLeft (ModuleCat.{u} R)).obj
    (K.homology ij.val.1)
  let aug := P.termColumnZeroHomologyAugmentation ij.val.2
  let TorFamily : KunnethAntidiagonal n → ModuleCat.{u} R := fun kl =>
    (Functor.leftDerived
      ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology kl.val.1)) 0).obj
        (L.homology kl.val.2)
  let rep : A.X 0 ⟶ A.homology 0 :=
    A.pOpcycles 0 ≫ A.isoHomologyι₀.inv
  let ePublic : Res.homology 0 ≅ ⨁ TorFamily :=
    kunnethTorResolutionHomologyIso K P 0 n
  let eTor : A.homology 0 ≅ TorFamily ij :=
    ((P.cartanEilenbergVerticalHomologyResolution ij.val.2).isoLeftDerivedObj
      T 0).symm
  let eZero : TorFamily ij ≅ T.obj (L.homology ij.val.2) :=
    torZeroIso (K.homology ij.val.1) (L.homology ij.val.2)
  let augMap : A.X 0 ⟶ T.obj (L.homology ij.val.2) := T.map aug
  let ιRes : A ⟶ Res :=
    biproduct.ι As ij
  let pairRes : Res ⟶ B.verticalHomologyComplex n :=
    kunnethCEVerticalHomologyPairing K P n
  let pair₀ : A.X 0 ⟶ (B.verticalHomologyComplex n).X 0 :=
    ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K (P.bicomplex.X 0)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (P.bicomplex.X 0))))
        ij.val.1 ij.val.2 ≫
      (homologyIsoOfEq (tensorObj K (P.bicomplex.X 0))
        (Finset.mem_antidiagonal.mp ij.property)).hom
  have hZero := kunnethTorResolutionHomologyIso_zero_component K P n ij
  have hιπ := kunnethTorResolutionHomologyIso_ι_π K P 0 n ij
  change rep ≫ HomologicalComplex.homologyMap ιRes 0 ≫
      ePublic.hom ≫ biproduct.π TorFamily ij ≫ eZero.hom =
    augMap at hZero
  change HomologicalComplex.homologyMap ιRes 0 ≫
      ePublic.hom ≫ biproduct.π TorFamily ij = eTor.hom at hιπ
  rw [reassoc_of% hιπ] at hZero
  have hRep : rep ≫ eTor.hom ≫ eZero.hom = augMap := hZero
  change A.pOpcycles 0 ≫ A.isoHomologyι₀.inv ≫ eTor.hom ≫ eZero.hom =
    augMap at hRep
  have hInv :=
    termColumnZeroHomologyAugmentation_comp_torZeroIso_inv K P n ij
  change augMap ≫ eZero.inv ≫ biproduct.ι TorFamily ij ≫ ePublic.inv =
    rep ≫ HomologicalComplex.homologyMap ιRes 0 at hInv
  apply (cancel_epi eZero.hom).1
  apply (cancel_epi eTor.hom).1
  apply (cancel_epi A.isoHomologyι₀.inv).1
  apply (cancel_epi (A.pOpcycles 0)).1
  rw [reassoc_of% hRep]
  rw [reassoc_of% hRep]
  simp only [tensorCartanEilenbergSecondPageIsoAt, Iso.trans_inv,
    HomologicalComplex.homologyMapIso_inv, Iso.symm_hom, Category.assoc]
  change _ = augMap ≫ eZero.inv ≫ biproduct.ι TorFamily ij ≫
    ePublic.inv ≫
      HomologicalComplex.homologyMap
        (kunnethCEVerticalHomologyComplexIso K P n).inv 0 ≫
      (χ.secondPageVerticalHomologyIso 0 n).inv ≫
      B.partialTotalZeroColumnEdge n ≫
      (tensorCartanEilenbergAbutmentIso K P hK n).hom
  rw [reassoc_of% hInv]
  rw [kunnethCEVerticalHomologyComplexIso_inv]
  let tail := (χ.secondPageVerticalHomologyIso 0 n).inv ≫
    B.partialTotalZeroColumnEdge n ≫
    (tensorCartanEilenbergAbutmentIso K P hK n).hom
  change _ = rep ≫ HomologicalComplex.homologyMap ιRes 0 ≫
    HomologicalComplex.homologyMap pairRes 0 ≫ tail
  rw [← Category.assoc
    (HomologicalComplex.homologyMap ιRes 0)
    (HomologicalComplex.homologyMap pairRes 0)
    tail]
  rw [← HomologicalComplex.homologyMap_comp]
  dsimp only [rep]
  simp only [Category.assoc]
  rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc]
  rw [HomologicalComplex.p_opcyclesMap_assoc]
  have hιRes_f : ιRes.f 0 = (biproduct.ι As ij).f 0 := rfl
  have hPairRes_f : pairRes.f 0 =
      (kunnethCEVerticalHomologyPairing K P n).f 0 := rfl
  simp only [HomologicalComplex.comp_f]
  rw [hιRes_f, hPairRes_f]
  rw [kunnethCEVerticalHomologyPairing_ι_f]
  change _ = pair₀ ≫ (B.verticalHomologyComplex n).pOpcycles 0 ≫
    (B.verticalHomologyComplex n).isoHomologyι₀.inv ≫ tail
  have hRow :
      B.partialTotalZeroRowToTotal ≫
          tensorCartanEilenbergToTensor K P =
        tensorHom (𝟙 K) P.termColumnZeroAugmentation := by
    apply HomologicalComplex.hom_ext
    intro q
    exact tensorCartanEilenbergToTensor_ιTotal K P q
  dsimp only [tail]
  rw [reassoc_of% (B.partialTotalZeroColumnEdge_representation n)]
  rw [tensorCartanEilenbergAbutmentIso_hom]
  let rowHom : (B.verticalHomologyComplex n).X 0 ⟶
      (B.total (ComplexShape.down ℕ)).homology n :=
    HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal n
  let toOrdHom : (B.total (ComplexShape.down ℕ)).homology n ⟶
      (tensorObj K L).homology n :=
    HomologicalComplex.homologyMap (tensorCartanEilenbergToTensor K P) n
  change _ = pair₀ ≫ rowHom ≫ toOrdHom
  have hRowHomComp : rowHom ≫ toOrdHom =
      HomologicalComplex.homologyMap
        (tensorHom (𝟙 K) P.termColumnZeroAugmentation) n := by
    change HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal n ≫
        HomologicalComplex.homologyMap (tensorCartanEilenbergToTensor K P) n = _
    rw [← HomologicalComplex.homologyMap_comp, hRow]
    rfl
  rw [hRowHomComp]
  let C := P.bicomplex.X 0
  let Q := L
  let g := P.termColumnZeroAugmentation
  let PC : ChainGradedPairing K C (tensorObj K C) := 𝟙 _
  let PQ : ChainGradedPairing K Q (tensorObj K Q) := 𝟙 _
  let tg := tensorHom (𝟙 K) g
  have hpair : ∀ i j,
      PC.pair i j ≫ tg.f (i + j) =
        (𝟙 (K.X i) ⊗ₘ g.f j) ≫ PQ.pair i j := by
    intro i j
    exact (ChainGradedPairing.pair_naturality PC PQ
      (𝟙 K) g tg (by simp [PC, PQ, tg]) i j).symm
  have hnat := ChainGradedPairing.pairHomology_naturality
    PC (ChainGradedPairing.homologyDescentData PC)
    PQ (ChainGradedPairing.homologyDescentData PQ)
    (𝟙 K) g tg hpair ij.val.1 ij.val.2
  have hnat' :
      (𝟙 (K.homology ij.val.1) ⊗ₘ
          HomologicalComplex.homologyMap g ij.val.2) ≫
        ChainGradedPairing.pairHomology PQ
          (ChainGradedPairing.homologyDescentData PQ)
          ij.val.1 ij.val.2 =
      ChainGradedPairing.pairHomology PC
          (ChainGradedPairing.homologyDescentData PC)
          ij.val.1 ij.val.2 ≫
        HomologicalComplex.homologyMap tg (ij.val.1 + ij.val.2) := by
    simpa only [HomologicalComplex.homologyMap_id] using hnat
  change
    (𝟙 (K.homology ij.val.1) ⊗ₘ
          HomologicalComplex.homologyMap g ij.val.2) ≫
        ChainGradedPairing.pairHomology PQ
          (ChainGradedPairing.homologyDescentData PQ)
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K Q)
          (Finset.mem_antidiagonal.mp ij.property)).hom =
      (ChainGradedPairing.pairHomology PC
          (ChainGradedPairing.homologyDescentData PC)
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K C)
          (Finset.mem_antidiagonal.mp ij.property)).hom) ≫
        HomologicalComplex.homologyMap tg n
  slice_rhs 2 3 =>
    rw [← homologyIsoOfEq_hom_naturality tg
      (Finset.mem_antidiagonal.mp ij.property)]
  have hnatTail := congrArg
    (fun f => f ≫ (homologyIsoOfEq (tensorObj K Q)
      (Finset.mem_antidiagonal.mp ij.property)).hom) hnat'
  simpa only [Category.assoc] using hnatTail

end HomologicalComplex

end

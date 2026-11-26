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

public import MathlibExt.Algebra.Category.ModuleCat.TorPID
public import MathlibExt.Algebra.Homology.Kunneth.Edge
public import MathlibExt.Algebra.Homology.PartialTotalTwoColumn

/-!
# The Künneth short exact sequence from a supplied resolution over a PID

Let R be a commutative principal ideal domain, and K,L nonnegative chain complexes of R-modules
in universe u. Assume every K_a is flat and fix a Cartan–Eilenberg resolution P of L. For every
n≥0 there is a short exact row

0→⊕_{i+j=n}H_i(K)⊗_R H_j(L)→H_n(K⊗_R L)→⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L))→0.

The left arrow is the canonical homology tensor map. In positive degree the right arrow is the
spectral edge defined by P and the Cartan–Eilenberg abutment comparison. The Tor-one index set
is empty at n=0, where the tensor map is an isomorphism. Vanishing of Tor in degrees at least
two gives the two-column spectral computation.

For the classical chain-complex sequence, see Weibel, An Introduction to Homological Algebra,
Theorem 5.6.4, Formula 5.6.5, and Theorem 3.6.3; also May, A Concise Course in Algebraic
Topology, Chapter 17 §2. The construction here is objectwise relative to P.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- For n∈ℕ, the Tor-one index set consists of pairs (i,j) of nonnegative integers with i+j+1=n. It
is empty at n=0 and is the finite antidiagonal i+j=q when n=q+1. -/
def KunnethTorOneIndex : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | q + 1 => Finset.antidiagonal q

@[simp]
theorem mem_kunnethTorOneIndex {n : ℕ} {ij : ℕ × ℕ} :
    ij ∈ KunnethTorOneIndex n ↔ ij.1 + ij.2 + 1 = n := by
  rcases n with _ | q
  · simp [KunnethTorOneIndex]
  · simp only [KunnethTorOneIndex, Finset.mem_antidiagonal]
    omega

private theorem kunnethIsTwoColumnAtTwoOfPID
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L) :
    CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo
      ((kunnethCEBicomplex K P).partialTotalSpectralObject.spectralSequence
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat) := by
  intro p q hp
  let F : KunnethAntidiagonal q → ModuleCat.{u} R := fun ij =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
      (K.homology ij.val.1)).obj (L.homology ij.val.2)
  have hF : ∀ ij, IsZero (F ij) := fun ij =>
    CategoryTheory.isZero_Tor_of_two_le_of_pid
      (K.homology ij.val.1) (L.homology ij.val.2) p hp
  have hSum : IsZero (⨁ F) := by
    let D := Discrete.functor F
    exact (biproduct.isLimit F).isZero_pt
      (Functor.isZero D (fun X => hF X.as))
  exact IsZero.of_iso hSum
    (tensorCartanEilenbergSecondPageIsoAt K P p q)

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. For a Cartan–Eilenberg resolution P of L
and q≥0, the right edge is H_{q+1}(K⊗_R L)→U_{q+1}. It first applies the inverse abutment
isomorphism, then the one-column right edge of the two-column spectral sequence, then the
second-page identification with the Tor-one sum indexed by i+j=q. -/
noncomputable def kunnethHomologyTorOneMapOfResolution
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (q : ℕ) :
    (tensorObj K L).homology (q + 1) ⟶
      (⨁ fun ij : KunnethTorOneIndex (q + 1) =>
        ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
          (K.homology ij.val.1)).obj (L.homology ij.val.2)) := by
  let B := kunnethCEBicomplex K P
  let E := B.partialTotalSpectralObject.spectralSequence
    CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
  let h₂ :
      CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E := by
    intro p r hp
    let F : KunnethAntidiagonal r → ModuleCat.{u} R := fun ij =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
        (K.homology ij.val.1)).obj (L.homology ij.val.2)
    have hF : ∀ ij, IsZero (F ij) := fun ij =>
      CategoryTheory.isZero_Tor_of_two_le_of_pid
        (K.homology ij.val.1) (L.homology ij.val.2) p hp
    have hSum : IsZero (⨁ F) := by
      let D := Discrete.functor F
      exact (biproduct.isLimit F).isZero_pt
        (Functor.isZero D (fun X => hF X.as))
    exact IsZero.of_iso hSum
      (tensorCartanEilenbergSecondPageIsoAt K P p r)
  exact (tensorCartanEilenbergAbutmentIso K P hK (q + 1)).inv ≫
    B.partialTotalOneColumnRightEdge h₂ q ≫
    (tensorCartanEilenbergSecondPageIsoAt K P 1 q).hom

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. For a Cartan–Eilenberg resolution P of L
and n≥0, the short complex is T_n→H_n(K⊗_R L)→U_n. Its first arrow is the canonical homology
tensor map, and its second is zero at n=0 or the resolution-defined spectral right edge at
n=q+1. -/
noncomputable abbrev kunnethShortComplexOfResolution
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) where
  X₁ := ⨁ fun ij : KunnethTensorIndex n =>
    K.homology ij.val.1 ⊗ L.homology ij.val.2
  X₂ := (tensorObj K L).homology n
  X₃ := ⨁ fun ij : KunnethTorOneIndex n =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
      (K.homology ij.val.1)).obj (L.homology ij.val.2)
  f := kunnethHomologyTensorMap K L n
  g := match n with
    | 0 => 0
    | q + 1 => kunnethHomologyTorOneMapOfResolution K P hK q
  zero := by
    rcases n with _ | q
    · simp only [comp_zero]
    · let B := kunnethCEBicomplex K P
      let E := B.partialTotalSpectralObject.spectralSequence
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
      let h₂ :
          CategoryTheory.SpectralSequence.IncreasingHomological.IsTwoColumnAtTwo E := by
        intro p r hp
        let F : KunnethAntidiagonal r → ModuleCat.{u} R := fun ij =>
          ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
            (K.homology ij.val.1)).obj (L.homology ij.val.2)
        have hF : ∀ ij, IsZero (F ij) := fun ij =>
          CategoryTheory.isZero_Tor_of_two_le_of_pid
            (K.homology ij.val.1) (L.homology ij.val.2) p hp
        have hSum : IsZero (⨁ F) := by
          let D := Discrete.functor F
          exact (biproduct.isLimit F).isZero_pt
            (Functor.isZero D (fun X => hF X.as))
        exact IsZero.of_iso hSum
          (tensorCartanEilenbergSecondPageIsoAt K P p r)
      let G := B.partialTotalTwoColumnShortComplex h₂ q
      let e₀ :
          (⨁ fun ij : KunnethTensorIndex (q + 1) =>
            K.homology ij.val.1 ⊗ L.homology ij.val.2) ≅ G.X₁ :=
        biproduct.mapIso
            (fun ij : KunnethTensorIndex (q + 1) =>
              (torZeroIso (K.homology ij.val.1)
                (L.homology ij.val.2)).symm) ≪≫
          (tensorCartanEilenbergSecondPageIsoAt K P 0 (q + 1)).symm
      let e₁ : G.X₂ ≅ (tensorObj K L).homology (q + 1) :=
        tensorCartanEilenbergAbutmentIso K P hK (q + 1)
      let e₂ : G.X₃ ≅
          (⨁ fun ij : KunnethTorOneIndex (q + 1) =>
            ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
              (K.homology ij.val.1)).obj (L.homology ij.val.2)) :=
        tensorCartanEilenbergSecondPageIsoAt K P 1 q
      rw [kunnethHomologyTensorMap_eq_p_zero_edge K P hK (q + 1)]
      change e₀.hom ≫ G.f ≫ e₁.hom ≫ e₁.inv ≫ G.g ≫ e₂.hom = 0
      simp only [Iso.hom_inv_id_assoc]
      slice_lhs 2 3 => rw [G.zero]
      simp only [comp_zero, zero_comp]

theorem kunnethShortComplexOfResolution_f_eq_kunnethHomologyTensorMap
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethShortComplexOfResolution K P hK n).f =
      kunnethHomologyTensorMap K L n := by
  rfl

private theorem isZero_kunnethTorOneObject_zero
    {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) :
    IsZero (⨁ fun ij : KunnethTorOneIndex 0 =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology ij.val.1)).obj (L.homology ij.val.2)) := by
  let F : KunnethTorOneIndex 0 → ModuleCat.{u} R := fun ij =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
      (K.homology ij.val.1)).obj (L.homology ij.val.2)
  let D := Discrete.functor F
  apply (biproduct.isLimit F).isZero_pt
  apply Functor.isZero D
  intro X
  have h := (mem_kunnethTorOneIndex (n := 0) (ij := X.as.val)).mp X.as.property
  omega

private theorem isIso_kunnethHomologyTensorMap_zero
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) :
    IsIso (kunnethHomologyTensorMap K L 0) := by
  let B := kunnethCEBicomplex K P
  let h₂ := kunnethIsTwoColumnAtTwoOfPID K P
  let _ : IsIso (B.partialTotalZeroColumnPageToStable 0) :=
    B.isIso_partialTotalZeroColumnPageToStable_of_twoColumn h₂ 0
  let _ : IsIso ((B.partialTotalHomologyFiltration 0).ι.app
      ((0 : ℤ) : EInt)) :=
    B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le 0 _ (by simp)
  have hEdge : IsIso (B.partialTotalZeroColumnEdge 0) := by
    change IsIso (B.partialTotalZeroColumnPageToStable 0 ≫
      (B.partialTotalStableGradedIso 0 0).hom ≫
      (B.partialTotalHomologyGradedZeroIso 0).inv ≫
      (B.partialTotalHomologyFiltration 0).ι.app ((0 : ℤ) : EInt))
    infer_instance
  let _ : IsIso (B.partialTotalZeroColumnEdge 0) := hEdge
  rw [kunnethHomologyTensorMap_eq_p_zero_edge K P hK 0]
  infer_instance

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. For every Cartan–Eilenberg resolution P
of L and n≥0, the row 0→T_n→H_n(K⊗_R L)→U_n→0 is short exact. Its left arrow is the canonical
homology tensor map, and its positive-degree right arrow is the spectral edge constructed from
P. -/
theorem kunnethShortComplexOfResolution_shortExact
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {L : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CartanEilenbergResolution L)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethShortComplexOfResolution K P hK n).ShortExact := by
  rcases n with _ | q
  · let S := kunnethShortComplexOfResolution K P hK 0
    have hf : IsIso S.f := by
      change IsIso (kunnethHomologyTensorMap K L 0)
      exact isIso_kunnethHomologyTensorMap_zero K P hK
    have hg : IsZero S.X₃ := by
      change IsZero (⨁ fun ij : KunnethTorOneIndex 0 =>
        ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
          (K.homology ij.val.1)).obj (L.homology ij.val.2))
      exact isZero_kunnethTorOneObject_zero K L
    exact (ShortComplex.Splitting.ofIsIsoOfIsZero S hf hg).shortExact
  · let B := kunnethCEBicomplex K P
    let h₂ := kunnethIsTwoColumnAtTwoOfPID K P
    let G := B.partialTotalTwoColumnShortComplex h₂ q
    let S := kunnethShortComplexOfResolution K P hK (q + 1)
    let e₀ : S.X₁ ≅ G.X₁ := by
      exact biproduct.mapIso
          (fun ij : KunnethTensorIndex (q + 1) =>
            (torZeroIso (K.homology ij.val.1)
              (L.homology ij.val.2)).symm) ≪≫
        (tensorCartanEilenbergSecondPageIsoAt K P 0 (q + 1)).symm
    let e₁ : G.X₂ ≅ S.X₂ :=
      tensorCartanEilenbergAbutmentIso K P hK (q + 1)
    let e₂ : G.X₃ ≅ S.X₃ :=
      tensorCartanEilenbergSecondPageIsoAt K P 1 q
    have hIso : G ≅ S := ShortComplex.isoMk e₀.symm e₁ e₂
      (by
        change e₀.inv ≫ kunnethHomologyTensorMap K L (q + 1) =
          B.partialTotalZeroColumnEdge (q + 1) ≫ e₁.hom
        rw [kunnethHomologyTensorMap_eq_p_zero_edge K P hK (q + 1)]
        dsimp only [e₀, e₁]
        simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc,
          Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
        rfl)
      (by
        change e₁.hom ≫ kunnethHomologyTorOneMapOfResolution K P hK q =
          B.partialTotalOneColumnRightEdge h₂ q ≫ e₂.hom
        dsimp only [kunnethHomologyTorOneMapOfResolution, e₁, e₂]
        simp only [Iso.hom_inv_id_assoc]
        rfl)
    exact ShortComplex.shortExact_of_iso hIso
      (B.partialTotalTwoColumnShortComplex_shortExact h₂ q)

end HomologicalComplex

end

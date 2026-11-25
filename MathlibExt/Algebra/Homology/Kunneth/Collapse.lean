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

public import MathlibExt.Algebra.Category.ModuleCat.TorFlat
public import MathlibExt.Algebra.Homology.Kunneth.Edge
public import Mathlib.RingTheory.Flat.TorsionFree
import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Collapse of the Künneth spectral sequence with flat first homology

If the terms and homology objects of the first complex are flat, every
positive Tor column vanishes.  The literal zero-column edge and the literal
zero-stage filtration inclusion are therefore isomorphisms, so the existing
canonical finite Künneth homology map is an isomorphism.  Field and PID
specializations retain the same canonical map.

## Mathematical reference and scope

See Weibel, *An Introduction to Homological Algebra*, Theorem 5.6.4 and
Künneth Formula 5.6.5 for the spectral-sequence and collapse argument.
Here the complexes are nonnegatively graded and the construction is
objectwise, using the repository-chosen Cartan--Eilenberg resolution in the
proof.  This API does not provide functoriality, resolution independence of
the spectral right edge, a natural splitting, or the classical noncanonical
splitting of the Künneth short exact sequence.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace HomologicalComplex

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- If the first complex is termwise flat and has flat homology, its
canonical Künneth homology tensor map is an isomorphism. -/
theorem isIso_kunnethHomologyTensorMap_of_flat_homology
    {R : Type u} [CommRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (hHK : ∀ i : ℕ, Module.Flat R (K.homology i))
    (n : ℕ) :
    IsIso (kunnethHomologyTensorMap K L n) := by
  let P := CartanEilenbergResolution.of L
  let B := kunnethCEBicomplex K P
  let χ := B.partialTotalFirstPageChoice
  let E := B.partialTotalSpectralObject.spectralSequence
    CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
  have hPageTwo (s t : ℕ) :
      IsZero (χ.pageTwo.X (s + 1, t)) := by
    let F : KunnethAntidiagonal t → ModuleCat.{u} R := fun ij =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) (s + 1)).obj
        (K.homology ij.val.1)).obj (L.homology ij.val.2)
    have hF : ∀ ij, IsZero (F ij) := by
      intro ij
      let _ : Module.Flat R (K.homology ij.val.1) := hHK ij.val.1
      exact CategoryTheory.isZero_Tor_succ_of_flat_left
        (K.homology ij.val.1) (L.homology ij.val.2) s
    have hSum : IsZero (⨁ F) := by
      let D := Discrete.functor F
      exact (biproduct.isLimit F).isZero_pt
        (Functor.isZero D (fun X => hF X.as))
    exact IsZero.of_iso hSum
      (tensorCartanEilenbergSecondPageIsoAt K P (s + 1) t)
  have hLaterPositive (r p t : ℕ) (hr : 2 ≤ r) (hp : 0 < p) :
      IsZero ((E.page (r : ℤ) (by omega)).X (p, t)) := by
    induction r, hr using Nat.le_induction with
    | base =>
        have hp0 : p ≠ 0 := Nat.ne_of_gt hp
        obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
        exact hPageTwo p t
    | succ r hr ih =>
        have hHomology :
            IsZero ((E.page (r : ℤ) (by omega)).homology (p, t)) :=
          ((E.page (r : ℤ) (by omega)).sc (p, t))
            |>.isZero_homology_of_isZero_X₂ ih
        exact IsZero.of_iso hHomology
          (E.iso (r : ℤ) ((r + 1 : ℕ) : ℤ) (p, t)).symm
  have hC0 : IsIso (B.partialTotalZeroColumnPageToStable n) := by
    apply B.isIso_partialTotalZeroColumnPageToStable_of_isZero_incoming
    intro r s hr hrs
    exact hLaterPositive r r s hr (by omega)
  have hGraded (p : ℕ) (hp : 0 < p) (hpn : p ≤ n) :
      IsZero (B.partialTotalHomologyGradedPiece n p) := by
    let q := n - p
    have hpq : p + q = n := Nat.add_sub_of_le hpn
    have hPage :
        IsZero ((E.page (((p + q + 2 : ℕ) : ℤ)) (by omega)).X (p, q)) :=
      hLaterPositive (p + q + 2) p q (by omega) hp
    have h := IsZero.of_iso hPage
      (B.partialTotalStablePageGradedIso p q).symm
    simpa only [hpq] using h
  have hAdjacent (p : ℕ) (hp : 0 < p) (hpn : p ≤ n) :
      IsIso (B.partialTotalHomologyFiltrationAdjacentHom n p) := by
    have hS := B.partialTotalHomologyGradedShortComplex_shortExact n p
    exact (hS.isIso_f_iff).2 (hGraded p hp hpn)
  have hFinite (p : ℕ) (hpn : p ≤ n) :
      IsIso ((B.partialTotalHomologyFiltration n).diagram.map
        (homOfLE (show (((0 : ℤ) : EInt)) ≤
          (((p : ℕ) : ℤ) : EInt) by simp))) := by
    induction p with
    | zero =>
        rw [show homOfLE (show (((0 : ℤ) : EInt)) ≤
            (((0 : ℕ) : ℤ) : EInt) by simp) =
              𝟙 (((0 : ℤ) : EInt)) by subsingleton,
          (B.partialTotalHomologyFiltration n).diagram.map_id]
        infer_instance
    | succ p ih =>
        have hpn' : p ≤ n := (Nat.le_succ p).trans hpn
        let _ : IsIso ((B.partialTotalHomologyFiltration n).diagram.map
            (homOfLE (show (((0 : ℤ) : EInt)) ≤
              (((p : ℕ) : ℤ) : EInt) by simp))) := ih hpn'
        let _ : IsIso ((B.partialTotalHomologyFiltration n).diagram.map
            (homOfLE (show (((p : ℕ) : ℤ) : EInt) ≤
              (((p + 1 : ℕ) : ℤ) : EInt) by simp))) := by
          rw [← B.partialTotalHomologyFiltrationAdjacentHom_succ n p]
          exact hAdjacent (p + 1) (by omega) hpn
        rw [show homOfLE (show (((0 : ℤ) : EInt)) ≤
              ((((p + 1 : ℕ) : ℕ) : ℤ) : EInt) by
                simp only [WithBotTop.coe_le_coe]
                omega) =
            homOfLE (show (((0 : ℤ) : EInt)) ≤
              (((p : ℕ) : ℤ) : EInt) by simp) ≫
            homOfLE (show (((p : ℕ) : ℤ) : EInt) ≤
              (((p + 1 : ℕ) : ℤ) : EInt) by simp) by subsingleton,
          Functor.map_comp]
        infer_instance
  have hC1 : IsIso ((B.partialTotalHomologyFiltration n).ι.app
      (((0 : ℤ) : EInt))) := by
    let _ : IsIso ((B.partialTotalHomologyFiltration n).diagram.map
        (homOfLE (show (((0 : ℤ) : EInt)) ≤
          (((n : ℕ) : ℤ) : EInt) by simp))) := hFinite n le_rfl
    let _ : IsIso ((B.partialTotalHomologyFiltration n).ι.app
        (((n : ℕ) : ℤ) : EInt)) :=
      B.partialTotalHomologyFiltration_exhaustive_at_degree n
    have hComp : IsIso
        ((B.partialTotalHomologyFiltration n).diagram.map
            (homOfLE (show (((0 : ℤ) : EInt)) ≤
              (((n : ℕ) : ℤ) : EInt) by simp)) ≫
          (B.partialTotalHomologyFiltration n).ι.app
            (((n : ℕ) : ℤ) : EInt)) := inferInstance
    rw [B.partialTotalHomologyFiltration_map_comp_ι n
      (show (((0 : ℤ) : EInt)) ≤ (((n : ℕ) : ℤ) : EInt) by simp)] at hComp
    exact hComp
  let _ : IsIso (B.partialTotalZeroColumnPageToStable n) := hC0
  let _ : IsIso ((B.partialTotalHomologyFiltration n).ι.app
      (((0 : ℤ) : EInt))) := hC1
  have hEdge : IsIso (B.partialTotalZeroColumnEdge n) := by
    unfold HomologicalComplex₂.partialTotalZeroColumnEdge
    infer_instance
  let _ : IsIso (B.partialTotalZeroColumnEdge n) := hEdge
  rw [kunnethHomologyTensorMap_eq_p_zero_edge K P hK n]
  infer_instance

/-- Over a field, the canonical Künneth homology tensor map is an
isomorphism without additional hypotheses. -/
theorem isIso_kunnethHomologyTensorMap_of_field
    {k : Type u} [Field k]
    (K L : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    IsIso (kunnethHomologyTensorMap K L n) := by
  have hK (i : ℕ) : Module.Flat k (K.X i) := by
    let _ : Module.Free k (K.X i) := Module.Free.of_divisionRing k (K.X i)
    exact Module.Flat.of_free
  have hHK (i : ℕ) : Module.Flat k (K.homology i) := by
    let _ : Module.Free k (K.homology i) :=
      Module.Free.of_divisionRing k (K.homology i)
    exact Module.Flat.of_free
  exact isIso_kunnethHomologyTensorMap_of_flat_homology K L hK hHK n

/-- Over a commutative PID, termwise flatness and torsion-free first
homology make the canonical Künneth homology tensor map an isomorphism. -/
theorem isIso_kunnethHomologyTensorMap_of_pid_of_torsionFree_homology
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (hTF : ∀ i : ℕ, Module.IsTorsionFree R (K.homology i))
    (n : ℕ) :
    IsIso (kunnethHomologyTensorMap K L n) := by
  have hHK (i : ℕ) : Module.Flat R (K.homology i) := by
    let _ : Module.IsTorsionFree R (K.homology i) := hTF i
    infer_instance
  exact isIso_kunnethHomologyTensorMap_of_flat_homology K L hK hHK n

end HomologicalComplex

end

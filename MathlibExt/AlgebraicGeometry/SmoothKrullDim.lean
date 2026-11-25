/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.lean` and
`P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.lean`, and
`Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim.lean`
and
`P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Krull dimension bounds for smooth morphisms

A scheme smooth of relative dimension `n` over a field has topological
Krull dimension at most `n`; if it is nonempty, its dimension equals `n`.
The upper bound bounds the Krull dimension of a standard smooth algebra by
the rank of its Kähler differentials, transfers along faithfully flat maps
by going-down, and globalizes over an affine open cover. The lower bound
exhibits a maximal ideal of height `n` in a polynomial ring in `n`
variables and transports it through standard smooth presentations.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SmoothKrullDimAux

open TensorProduct IsLocalRing TopologicalSpace Topology

private theorem spanFinrank_maximalIdeal_le_finrank_kaehler
    (L P : Type*) [CommRing L] [CommRing P] [Algebra L P] [IsLocalRing P]
    [IsNoetherianRing P] [Algebra.FormallySmooth L P] [Module.Free P Ω[P⁄L]]
    [Module.Finite P Ω[P⁄L]] [Algebra.FormallySmooth L (ResidueField P)] :
    (maximalIdeal P).spanFinrank ≤ Module.finrank P Ω[P⁄L] := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hfg : (RingHom.ker (algebraMap P (ResidueField P))).FG :=
    (isNoetherianRing_iff_ideal_fg P).mp ‹_› _
  have hbot : maximalIdeal (ResidueField P) ≤
      RingHom.ker (algebraMap (ResidueField P) (ResidueField P)) := by
    rw [maximalIdeal_eq_bot]
    exact bot_le
  have hinj : Function.Injective (KaehlerDifferential.cotangentComplexBaseChange L
      (ResidueField P) P (ResidueField P)) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := L)
      (S := ResidueField P) P (ResidueField P) residue_surjective hfg hbot).mp ‹_›
  have : Module.Free (ResidueField P)
      (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) :=
    Module.Free.of_divisionRing _ _
  have h1 : Module.finrank (ResidueField P)
        (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) ≤
      Module.finrank (ResidueField P) (ResidueField P ⊗[P] Ω[P⁄L]) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank (ResidueField P) (ResidueField P ⊗[P] Ω[P⁄L]) =
      Module.finrank P Ω[P⁄L] := by
    let b := Module.Free.chooseBasis P Ω[P⁄L]
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (ResidueField P) b),
      Module.finrank_eq_card_basis b]
  have h3 : (maximalIdeal P).spanFinrank = Module.finrank (ResidueField P)
        (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) := by
    rw [Module.finrank_eq_spanFinrank_of_free,
      TensorProduct.spanFinrank_top_eq_of_residueField _ hfg, hker]
  rw [h3, ← h2]
  exact h1

private theorem ringKrullDim_le_finrank_kaehler
    (L P : Type*) [CommRing L] [CommRing P] [Algebra L P] [IsLocalRing P]
    [IsNoetherianRing P] [Algebra.FormallySmooth L P] [Module.Free P Ω[P⁄L]]
    [Module.Finite P Ω[P⁄L]] [Algebra.FormallySmooth L (ResidueField P)] :
    ringKrullDim P ≤ Module.finrank P Ω[P⁄L] :=
  (ringKrullDim_le_spanFinrank_maximalIdeal P).trans
    (by exact_mod_cast spanFinrank_maximalIdeal_le_finrank_kaehler L P)

private theorem ringKrullDim_localization_le {L : Type*} [Field L] {B : Type*} [CommRing B]
    [Algebra L B] [PerfectField L] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n L B] (m : Ideal B) [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m) ≤ n := by
  classical
  have : Algebra.IsStandardSmooth L B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FiniteType L B := inferInstance
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing L B
  have : Nontrivial B := ⟨⟨0, 1, fun h => Ideal.IsPrime.ne_top' (I := m)
    (Ideal.eq_top_of_isUnit_mem _ m.zero_mem (by rw [h]; exact isUnit_one))⟩⟩
  have : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ ‹_›
  have : Algebra.FormallySmooth B (Localization.AtPrime m) := .of_isLocalization m.primeCompl
  have : Algebra.FormallySmooth L (Localization.AtPrime m) := .comp L B _
  let b := Module.Free.chooseBasis B Ω[B⁄L]
  let bm : Module.Basis _ (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] :=
    b.ofIsLocalizedModule (Localization.AtPrime m) m.primeCompl
      (KaehlerDifferential.map L L B (Localization.AtPrime m))
  have : Module.Free (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] := .of_basis bm
  have : Module.Finite (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] := .of_basis bm
  have hrank : Module.finrank (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] = n := by
    have h := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := L)
      (S := B) n
    rw [Module.Free.rank_eq_card_chooseBasisIndex, Cardinal.mk_fintype] at h
    rw [Module.finrank_eq_card_basis bm]
    exact_mod_cast h
  have : Algebra.EssFiniteType L (ResidueField (Localization.AtPrime m)) :=
    .comp L (Localization.AtPrime m) _
  have : Algebra.FormallySmooth L (ResidueField (Localization.AtPrime m)) :=
    Algebra.FormallySmooth.of_perfectField
  rw [← hrank]
  exact ringKrullDim_le_finrank_kaehler L _

private theorem ringKrullDim_le_of_perfectField {L : Type*} [Field L] {B : Type*} [CommRing B]
    [Algebra L B] [PerfectField L] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n L B] : ringKrullDim B ≤ n := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact ringKrullDim_localization_le (L := L) n m

end SmoothKrullDimAux

/-- Krull dimension does not increase along faithfully flat ring maps. -/
theorem ringKrullDim_le_of_faithfullyFlat (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] : ringKrullDim R ≤ ringKrullDim S := by
  change (⨆ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞)) ≤ _
  refine iSup_le fun l => ?_
  obtain ⟨P, hP, hPo⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) l.last.asIdeal
  obtain ⟨L', hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown (S := S) l P
  calc ((l.length : WithBot ℕ∞)) = L'.length := by rw [hlen]
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.LTSeries.length_le_krullDim L'

/-- A standard smooth algebra of relative dimension `n` has Krull dimension
at most `n`. -/
theorem ringKrullDim_le_of_isStandardSmoothOfRelativeDimension
    {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K B] : ringKrullDim B ≤ n := by
  let L := AlgebraicClosure K
  have h1 : ringKrullDim (L ⊗[K] B) ≤ n :=
    SmoothKrullDimAux.ringKrullDim_le_of_perfectField (L := L) n
  have h2 : ringKrullDim B ≤ ringKrullDim (B ⊗[K] L) :=
    ringKrullDim_le_of_faithfullyFlat B _
  have h3 : ringKrullDim (B ⊗[K] L) = ringKrullDim (L ⊗[K] B) :=
    ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm K B L).toRingEquiv
  exact h2.trans (h3 ▸ h1)

namespace SmoothKrullDimAux

/-- A standard smooth algebra map from a field has Krull dimension at most
the relative dimension. -/
theorem ringKrullDim_le_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (hR : IsField R)
    (φ : R →+* S) (n : ℕ) (hφ : φ.IsStandardSmoothOfRelativeDimension n) :
    ringKrullDim S ≤ n := by
  let _ := hR.toField
  let _ := φ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n R S := hφ
  exact ringKrullDim_le_of_isStandardSmoothOfRelativeDimension (K := R) n

open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct

attribute [local instance] specializationOrder

private theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding
    {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X] (n : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Type u) (_ : TopologicalSpace U) (g : U → X),
      IsOpenEmbedding g ∧ x ∈ Set.range g ∧ topologicalKrullDim U ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, _, g, hg, ⟨y, rfl⟩, hU⟩ := h x
  have : QuasiSober U := hg.quasiSober
  have : T0Space U := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim U := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U))).symm
    _ ≤ n := hU

end SmoothKrullDimAux

/-- A scheme smooth of relative dimension `n` over a field has topological
Krull dimension at most `n`. -/
theorem AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] : topologicalKrullDim X ≤ n := by
  refine SmoothKrullDimAux.topologicalKrullDim_le_of_forall_exists_isOpenEmbedding
    (X := X) n fun x => ?_
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  refine ⟨↥V, inferInstance, Subtype.val, V.2.isOpenEmbedding_subtypeVal, ⟨⟨x, hxV⟩, rfl⟩, ?_⟩
  have hU' : U = ⊤ := by
    have : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hx : f.base x ∈ U := e hxV
    rwa [Subsingleton.elim y (f.base x)]
  subst hU'
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  have hring : ringKrullDim Γ(X, V) ≤ n :=
    SmoothKrullDimAux.ringKrullDim_le_of_ringHom hK _ n hf
  have hSpec : topologicalKrullDim (Spec Γ(X, V)) ≤ n := by
    change topologicalKrullDim (PrimeSpectrum Γ(X, V)) ≤ n
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph] at hSpec
  exact hSpec

namespace SmoothKrullDimLowerAux

open TopologicalSpace

private theorem height_eq_of_isMaximal_mvPolynomial (L : Type u) [Field L] :
    ∀ (n : ℕ) (𝔭 : Ideal (MvPolynomial (Fin n) L)), 𝔭.IsMaximal → 𝔭.height = n := by
  intro n
  induction n with
  | zero =>
    intro 𝔭 h𝔭
    haveI := h𝔭
    have hle : (𝔭.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) L) :=
      Ideal.height_le_ringKrullDim_of_ne_top h𝔭.ne_top
    have hkr : ringKrullDim (MvPolynomial (Fin 0) L) = 0 := by
      simp [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
    rw [hkr] at hle
    have : 𝔭.height ≤ 0 := by exact_mod_cast hle
    simpa using this
  | succ n ih =>
    intro 𝔭 h𝔭
    haveI := h𝔭
    let e : MvPolynomial (Fin (n + 1)) L ≃+* Polynomial (MvPolynomial (Fin n) L) :=
      (MvPolynomial.finSuccEquiv L n).toRingEquiv
    let 𝔭' : Ideal (Polynomial (MvPolynomial (Fin n) L)) := 𝔭.map e
    haveI : 𝔭'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) L) := 𝔭'.under (MvPolynomial (Fin n) L)
    haveI : 𝔭'.LiesOver p := ⟨rfl⟩
    have hp : p.IsMaximal := by
      have hpp : p = 𝔭'.comap (Polynomial.C : MvPolynomial (Fin n) L →+*
          Polynomial (MvPolynomial (Fin n) L)) := by
        simp only [p, Ideal.under_def, Polynomial.algebraMap_eq]
      rw [hpp]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing 𝔭'
    have h1 : 𝔭'.height = p.height + 1 := Polynomial.height_eq_height_add_one p 𝔭'
    have h2 : p.height = n := ih p hp
    have h3 : 𝔭'.height = 𝔭.height := RingEquiv.height_map e 𝔭
    rw [← h3, h1, h2]
    norm_cast

private theorem le_ringKrullDim_of_isStandardSmoothOfRelativeDimension {L R : Type u}
    [CommRing L] (hL : IsField L) [CommRing R] [Nontrivial R] (φ : L →+* R) (n : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension n) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R := by
  letI : Field L := hL.toField
  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  algebraize [g]
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let 𝔭 : Ideal (MvPolynomial (Fin n) L) := 𝔪.comap g
  haveI : 𝔭.IsMaximal := by
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : Algebra.FiniteType (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      Algebra.FiniteType.trans (S := R) inferInstance inferInstance
    haveI : Module.Finite (MvPolynomial (Fin n) L) (R ⧸ 𝔪) :=
      finite_of_finite_type_of_isJacobsonRing (MvPolynomial (Fin n) L) (R ⧸ 𝔪)
    haveI : Algebra.IsIntegral (MvPolynomial (Fin n) L) (R ⧸ 𝔪) := inferInstance
    have hbot : (⊥ : Ideal (R ⧸ 𝔪)).IsMaximal := Ideal.bot_isMaximal
    have hcomap : ((⊥ : Ideal (R ⧸ 𝔪)).under
        (MvPolynomial (Fin n) L)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (⊥ : Ideal (R ⧸ 𝔪))
    have heq : (⊥ : Ideal (R ⧸ 𝔪)).under (MvPolynomial (Fin n) L) = 𝔭 := by
      rw [Ideal.under_def,
        show algebraMap (MvPolynomial (Fin n) L) (R ⧸ 𝔪) =
          (Ideal.Quotient.mk 𝔪).comp g from rfl,
        ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [heq] at hcomap
  have hht : 𝔭.height = n := height_eq_of_isMaximal_mvPolynomial L n 𝔭 ‹𝔭.IsMaximal›
  have hle : (n : ℕ∞) ≤ Order.height (⟨𝔭, inferInstance⟩ : PrimeSpectrum
      (MvPolynomial (Fin n) L)) := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hht]
  obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle
  haveI : 𝔪.LiesOver l.last.asIdeal := ⟨by rw [hlast]; rfl⟩
  obtain ⟨l', hl'len, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔪
  calc (n : WithBot ℕ∞) = (l'.length : WithBot ℕ∞) := by rw [hl'len, hlen]
    _ ≤ ringKrullDim R := Order.LTSeries.length_le_krullDim l'

end SmoothKrullDimLowerAux

/-- A nonempty scheme smooth of relative dimension `n` over a field has
topological Krull dimension at least `n`. -/
theorem AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hU' : U = ⊤ := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hx : f.base x ∈ U := e hxV
    rwa [Subsingleton.elim y (f.base x)]
  subst hU'
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  have hne : Nonempty (PrimeSpectrum Γ(X, V)) :=
    ⟨(hV.isoSpec.hom.base ⟨x, hxV⟩ : PrimeSpectrum Γ(X, V))⟩
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
  have hring : (n : WithBot ℕ∞) ≤ ringKrullDim Γ(X, V) :=
    SmoothKrullDimLowerAux.le_ringKrullDim_of_isStandardSmoothOfRelativeDimension hK _ n hf
  have hSpec : (n : WithBot ℕ∞) ≤ topologicalKrullDim (Spec Γ(X, V)) := by
    change (n : WithBot ℕ∞) ≤ topologicalKrullDim (PrimeSpectrum Γ(X, V))
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]
    at hSpec
  exact hSpec.trans (topologicalKrullDim_subspace_le X (V : Set X))

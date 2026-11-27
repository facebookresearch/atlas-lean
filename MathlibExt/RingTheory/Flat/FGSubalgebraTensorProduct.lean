/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean`
and
`P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean`
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

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import MathlibExt.RingTheory.Flat.OpenFlatLocus
import MathlibExt.RingTheory.Flat.FGSubalgebraLocalization

/-!
# Noetherian approximation of flatness

Let `B₀` be a finitely presented `R₀`-algebra and `R` an `R₀`-algebra. If `R ⊗[R₀] B₀` is flat over
`R`, then every finite subset of `R` lies in a finitely generated `R₀`-subalgebra `R₁` of `R` such
that `R₁ ⊗[R₀] B₀` is flat over `R₁`. The proof uses the pointwise version
(`Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct`) and openness of the flat locus
(`Module.Flat.isOpen_setOf_flat_localization_atPrime`).

## Main results

* `Module.Flat.exists_fg_subalgebra_flat_tensorProduct`

## References

* [Stacks Project, Lemma 10.168.1 (Tag 02JO)](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public section

open TensorProduct

namespace Module.Flat.FGSubalgebraTensorProduct

noncomputable section

section BCL

variable {R₀ E E' B₀ : Type*} [CommRing R₀] [CommRing E] [CommRing E'] [CommRing B₀]
  [Algebra R₀ E] [Algebra R₀ E'] [Algebra R₀ B₀] [Algebra E E'] [IsScalarTower R₀ E E']

variable (R₀ E E' B₀) in
private noncomputable def trans : E ⊗[R₀] B₀ →ₐ[R₀] E' ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ E E') (AlgHom.id R₀ B₀)

private lemma trans_tmul (e : E) (b : B₀) :
    trans R₀ E E' B₀ (e ⊗ₜ b) = algebraMap E E' e ⊗ₜ b := by
  simp [trans]

private lemma trans_algebraMap (e : E) :
    trans R₀ E E' B₀ (algebraMap E (E ⊗[R₀] B₀) e) =
      algebraMap E' (E' ⊗[R₀] B₀) (algebraMap E E' e) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [trans]

private theorem flat_atPrime_baseChange (Q' : Ideal (E' ⊗[R₀] B₀)) [Q'.IsPrime]
    (hflat : Module.Flat E (Localization.AtPrime (Q'.comap (trans R₀ E E' B₀).toRingHom))) :
    Module.Flat E' (Localization.AtPrime Q') := by
  set π : E ⊗[R₀] B₀ →ₐ[R₀] E' ⊗[R₀] B₀ := trans R₀ E E' B₀ with hπ
  set Q : Ideal (E ⊗[R₀] B₀) := Q'.comap π.toRingHom with hQdef
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  let algCC' : Algebra (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) := π.toRingHom.toAlgebra
  have halgCC' : algebraMap (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) = π.toRingHom := rfl
  have : IsScalarTower E (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := E ⊗[R₀] B₀) (A := E' ⊗[R₀] B₀) fun e => by
      rw [halgCC', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hπ, trans_algebraMap,
        ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower R₀ (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) :=
    IsScalarTower.of_algebraMap_eq (R := R₀) (S := E ⊗[R₀] B₀) (A := E' ⊗[R₀] B₀) fun r => by
      rw [halgCC', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  have H1 : Algebra.IsPushout E E' (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ B₀ E E' (by
      ext b
      simp [halgCC', hπ, trans])
  have : Algebra.IsPushout E (E ⊗[R₀] B₀) E' (E' ⊗[R₀] B₀) := H1.symm
  set S : Submonoid (E ⊗[R₀] B₀) := Q.primeCompl with hS
  set T : Submonoid (E' ⊗[R₀] B₀) := Algebra.algebraMapSubmonoid (E' ⊗[R₀] B₀) S with hT
  let algCqD : Algebra (Localization.AtPrime Q) (Localization T) :=
    (IsLocalization.map (M := S) (T := T) (Localization T)
      (algebraMap (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀)) (Submonoid.le_comap_map S)).toAlgebra
  have halgCqD : algebraMap (Localization.AtPrime Q) (Localization T) =
      IsLocalization.map (M := S) (T := T) (Localization T)
        (algebraMap (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀)) (Submonoid.le_comap_map S) := rfl
  have : IsScalarTower (E ⊗[R₀] B₀) (Localization.AtPrime Q) (Localization T) :=
    IsScalarTower.of_algebraMap_eq (R := E ⊗[R₀] B₀) (S := Localization.AtPrime Q)
      (A := Localization T) fun c => by
      rw [halgCqD]
      erw [IsLocalization.map_eq]
      rw [IsScalarTower.algebraMap_apply (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) (Localization T)]
  have H2 : Algebra.IsPushout (E ⊗[R₀] B₀) (E' ⊗[R₀] B₀) (Localization.AtPrime Q)
      (Localization T) :=
    Algebra.isPushout_of_isLocalization S (Localization.AtPrime Q) (E' ⊗[R₀] B₀) (Localization T)
  have : IsScalarTower E E' (Localization T) :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := E') (A := Localization T) fun e => by
      rw [IsScalarTower.algebraMap_apply E (E' ⊗[R₀] B₀) (Localization T),
        IsScalarTower.algebraMap_apply E' (E' ⊗[R₀] B₀) (Localization T),
        ← IsScalarTower.algebraMap_apply E E']
  have : IsScalarTower E (Localization.AtPrime Q) (Localization T) :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := Localization.AtPrime Q) (A := Localization T)
      fun e => by
      rw [IsScalarTower.algebraMap_apply E (E ⊗[R₀] B₀) (Localization.AtPrime Q),
        ← IsScalarTower.algebraMap_apply (E ⊗[R₀] B₀) (Localization.AtPrime Q) (Localization T),
        IsScalarTower.algebraMap_apply E (E ⊗[R₀] B₀) (Localization T)]
  have : IsScalarTower E (E' ⊗[R₀] B₀) (Localization T) :=
    IsScalarTower.of_algebraMap_eq (R := E) (S := E' ⊗[R₀] B₀) (A := Localization T) fun e => rfl
  have H3 : Algebra.IsPushout E (Localization.AtPrime Q) E' (Localization T) :=
    (Algebra.IsPushout.comp_iff (R := E) (S := E ⊗[R₀] B₀) (R' := E') (S' := E' ⊗[R₀] B₀)
      (T := Localization.AtPrime Q) (T' := Localization T)).mpr H2.symm
  have hD : Module.Flat E' (Localization T) := by
    have : Algebra.IsPushout E E' (Localization.AtPrime Q) (Localization T) := H3.symm
    have : Module.Flat E' (E' ⊗[E] Localization.AtPrime Q) := inferInstance
    exact Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv E E' (Localization.AtPrime Q) (Localization T)).symm.toLinearEquiv
  have hle : T ≤ Q'.primeCompl := by
    rintro x ⟨s, hs, rfl⟩
    intro hx
    exact hs (show s ∈ Q from hx)
  let algDL : Algebra (Localization T) (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization T) (Localization.AtPrime Q') T
      Q'.primeCompl hle
  have : IsScalarTower (E' ⊗[R₀] B₀) (Localization T) (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization T)
      (Localization.AtPrime Q') T Q'.primeCompl hle
  have hloc := IsLocalization.isLocalization_of_submonoid_le (Localization T)
    (Localization.AtPrime Q') T Q'.primeCompl hle
  have hDL : Module.Flat (Localization T) (Localization.AtPrime Q') :=
    @IsLocalization.flat (Localization T) (Localization.AtPrime Q') _ _ _ _ hloc
  have : IsScalarTower E' (Localization T) (Localization.AtPrime Q') :=
    IsScalarTower.of_algebraMap_eq (R := E') (S := Localization T) (A := Localization.AtPrime Q')
      fun e => by
      rw [IsScalarTower.algebraMap_apply E' (E' ⊗[R₀] B₀) (Localization.AtPrime Q'),
        IsScalarTower.algebraMap_apply (E' ⊗[R₀] B₀) (Localization T) (Localization.AtPrime Q'),
        ← IsScalarTower.algebraMap_apply E' (E' ⊗[R₀] B₀) (Localization T)]
  have := hD
  have := hDL
  exact Module.Flat.trans E' (Localization T) (Localization.AtPrime Q')

end BCL

section Levels

variable {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀] [Algebra R₀ R] [Algebra R₀ B₀]

private noncomputable abbrev lv (E : Subalgebra R₀ R) : ↥E ⊗[R₀] B₀ →ₐ[R₀] R ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map E.val (AlgHom.id R₀ B₀)

private noncomputable abbrev tr {E E' : Subalgebra R₀ R} (h : E ≤ E') :
    ↥E ⊗[R₀] B₀ →ₐ[R₀] ↥E' ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id R₀ B₀)

private lemma lv_comp_tr {E E' : Subalgebra R₀ R} (h : E ≤ E') :
    (lv (B₀ := B₀) E').comp (tr h) = lv E := by
  rw [lv, tr, ← Algebra.TensorProduct.map_comp]
  rfl

private lemma lv_tr {E E' : Subalgebra R₀ R} (h : E ≤ E') (x : ↥E ⊗[R₀] B₀) :
    lv E' (tr h x) = lv E x := by
  rw [← AlgHom.comp_apply, lv_comp_tr]

private lemma tr_comp_tr {E E' E'' : Subalgebra R₀ R} (h : E ≤ E') (h' : E' ≤ E'') :
    (tr (B₀ := B₀) h').comp (tr h) = tr (h.trans h') := by
  rw [tr, tr, ← Algebra.TensorProduct.map_comp]
  rfl

private lemma tr_tr {E E' E'' : Subalgebra R₀ R} (h : E ≤ E') (h' : E' ≤ E'') (x : ↥E ⊗[R₀] B₀) :
    tr h' (tr h x) = tr (h.trans h') x := by
  rw [← AlgHom.comp_apply, tr_comp_tr]

private lemma tr_refl (E : Subalgebra R₀ R) (x : ↥E ⊗[R₀] B₀) : tr (le_refl E) x = x := by
  have : tr (B₀ := B₀) (le_refl E) = AlgHom.id R₀ _ := by
    rw [tr, ← Algebra.TensorProduct.map_id]
    rfl
  rw [this]; rfl

private def U (E : Subalgebra R₀ R) : Set (PrimeSpectrum (↥E ⊗[R₀] B₀)) :=
  {Q | Module.Flat E (Localization.AtPrime Q.asIdeal)}

private def V (E : Subalgebra R₀ R) : Set (PrimeSpectrum (R ⊗[R₀] B₀)) :=
  PrimeSpectrum.comap (lv (B₀ := B₀) E).toRingHom ⁻¹' U E

private theorem U_mono {E E' : Subalgebra R₀ R} (h : E ≤ E') (Q' : PrimeSpectrum (↥E' ⊗[R₀] B₀))
    (hQ : PrimeSpectrum.comap (tr h).toRingHom Q' ∈ U (B₀ := B₀) E) : Q' ∈ U E' := by
  let : Algebra E E' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower R₀ E E' := IsScalarTower.of_algebraMap_eq (R := R₀) (S := E) (A := E')
    fun r => Subtype.ext rfl
  have htr : trans R₀ E E' B₀ = tr h := by
    have : IsScalarTower.toAlgHom R₀ (↥E) (↥E') = Subalgebra.inclusion h := AlgHom.ext fun _ => rfl
    rw [trans, this]
  simp only [U, Set.mem_ofPred_eq, PrimeSpectrum.comap_asIdeal] at hQ ⊢
  have hQ' : Module.Flat E
      (Localization.AtPrime (Q'.asIdeal.comap (trans R₀ E E' B₀).toRingHom)) := by
    rw [htr]; exact hQ
  exact flat_atPrime_baseChange Q'.asIdeal hQ'

private lemma comap_lv_eq {E E' : Subalgebra R₀ R} (h : E ≤ E') (P : PrimeSpectrum (R ⊗[R₀] B₀)) :
    PrimeSpectrum.comap (tr (B₀ := B₀) h).toRingHom (PrimeSpectrum.comap (lv E').toRingHom P) =
      PrimeSpectrum.comap (lv E).toRingHom P := by
  have h1 : (lv (B₀ := B₀) E).toRingHom = (lv E').toRingHom.comp (tr h).toRingHom := by
    rw [← lv_comp_tr h]; rfl
  rw [h1, PrimeSpectrum.comap_comp]
  rfl

private theorem V_mono {E E' : Subalgebra R₀ R} (h : E ≤ E') : V (B₀ := B₀) E ⊆ V E' := by
  intro P hP
  simp only [V, Set.mem_preimage] at hP ⊢
  refine U_mono h _ ?_
  rw [comap_lv_eq]
  exact hP

private theorem exists_fg_mem_range_lv (b : R ⊗[R₀] B₀) :
    ∃ E : Subalgebra R₀ R, E.FG ∧ b ∈ Set.range (lv (B₀ := B₀) E) := by
  induction b using TensorProduct.inductionOn with
  | tmul r b =>
    refine ⟨Algebra.adjoin R₀ {r}, ⟨{r}, by simp⟩, ?_⟩
    refine ⟨⟨r, Algebra.subset_adjoin (Set.mem_singleton r)⟩ ⊗ₜ b, ?_⟩
    simp [lv]
  | add x y hx hy =>
    obtain ⟨E, hE, x', hx'⟩ := hx
    obtain ⟨E', hE', y', hy'⟩ := hy
    refine ⟨E ⊔ E', hE.sup hE',
      tr (le_sup_left : E ≤ E ⊔ E') x' + tr (le_sup_right : E' ≤ E ⊔ E') y', ?_⟩
    rw [map_add, lv_tr, lv_tr, hx', hy']

private lemma lv_eq_rTensor (E : Subalgebra R₀ R) (x : ↥E ⊗[R₀] B₀) :
    lv E x = LinearMap.rTensor B₀ E.val.toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul e b => simp [lv]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma tr_eq_rTensor {E E' : Subalgebra R₀ R} (h : E ≤ E') (x : ↥E ⊗[R₀] B₀) :
    tr h x = LinearMap.rTensor B₀ (Subalgebra.inclusion h).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul e b => simp [tr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem exists_fg_tr_eq_zero {E : Subalgebra R₀ R} (hE : E.FG) (x : ↥E ⊗[R₀] B₀)
    (hx : lv E x = 0) : ∃ E' : Subalgebra R₀ R, ∃ h : E ≤ E', E'.FG ∧ tr h x = 0 := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  set N : Submodule R₀ R :=
    Submodule.span R₀ ((fun i => (i.1 : R)) '' (S : Set (↥E × B₀))) with hNdef
  have hNfg : N.FG := Submodule.fg_span ((S.finite_toSet).image _)
  have hNE : ∀ n ∈ N, n ∈ E := by
    intro n hn
    have : N ≤ Subalgebra.toSubmodule E := by
      rw [hNdef, Submodule.span_le]
      rintro _ ⟨i, _, rfl⟩
      exact i.1.2
    exact this hn
  let ι : N →ₗ[R₀] ↥E :=
    { toFun := fun n => ⟨n.1, hNE n.1 n.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmemN : ∀ i ∈ S, (i.1 : R) ∈ N := fun i hi =>
    Submodule.subset_span ⟨i, hi, rfl⟩
  let xN : N ⊗[R₀] B₀ := ∑ i ∈ S.attach, (⟨(i.1.1 : R), hmemN i.1 i.2⟩ : N) ⊗ₜ i.1.2
  have hxN : LinearMap.rTensor B₀ ι xN = x := by
    simp only [xN, map_sum, LinearMap.rTensor_tmul]
    conv_rhs => rw [hS, ← Finset.sum_attach]
    rfl
  have hval : N.subtype = E.val.toLinearMap ∘ₗ ι := by ext; rfl
  have h0 : LinearMap.rTensor B₀ N.subtype xN = LinearMap.rTensor B₀ N.subtype 0 := by
    rw [map_zero, hval, LinearMap.rTensor_comp, LinearMap.comp_apply, hxN, ← lv_eq_rTensor, hx]
  obtain ⟨N', hN'fg, hNN', hzero⟩ := Submodule.FG.exists_rTensor_fg_inclusion_eq (M := B₀) hNfg h0
  rw [map_zero] at hzero
  obtain ⟨t, ht⟩ := hN'fg
  refine ⟨E ⊔ Algebra.adjoin R₀ (t : Set R), le_sup_left, hE.sup ⟨t, rfl⟩, ?_⟩
  have hN'E : ∀ n ∈ N', n ∈ E ⊔ Algebra.adjoin R₀ (t : Set R) := by
    intro n hn
    rw [← ht] at hn
    exact (le_sup_right : Algebra.adjoin R₀ (t : Set R) ≤ E ⊔ Algebra.adjoin R₀ (t : Set R))
      (Algebra.span_le_adjoin R₀ _ hn)
  let ι' : N' →ₗ[R₀] ↥(E ⊔ Algebra.adjoin R₀ (t : Set R)) :=
    { toFun := fun n => ⟨n.1, hN'E n.1 n.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcomp : (Subalgebra.inclusion (le_sup_left :
      E ≤ E ⊔ Algebra.adjoin R₀ (t : Set R))).toLinearMap ∘ₗ ι =
      ι' ∘ₗ Submodule.inclusion hNN' := by ext; rfl
  rw [tr_eq_rTensor, ← hxN, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp,
    LinearMap.rTensor_comp, LinearMap.comp_apply, hzero, map_zero]

end Levels

section Noetherian

variable {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀] [Algebra R₀ R] [Algebra R₀ B₀]

private theorem isOpen_V [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀] {E : Subalgebra R₀ R}
    (hE : E.FG) : IsOpen (V (B₀ := B₀) E) := by
  have : IsNoetherianRing E := isNoetherianRing_of_fg hE
  have : Algebra.FiniteType (↥E) (↥E ⊗[R₀] B₀) := inferInstance
  have hU : IsOpen (U (B₀ := B₀) E) := Module.Flat.isOpen_setOf_flat_localization_atPrime
  exact hU.preimage (PrimeSpectrum.continuous_comap _)

private theorem exists_fg_mem_V [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (P : PrimeSpectrum (R ⊗[R₀] B₀)) :
    ∃ E : Subalgebra R₀ R, E.FG ∧ P ∈ V (B₀ := B₀) E := by
  have : Module.Flat (R ⊗[R₀] B₀) (Localization.AtPrime P.asIdeal) :=
    IsLocalization.flat _ P.asIdeal.primeCompl
  have : Module.Flat R (Localization.AtPrime P.asIdeal) :=
    Module.Flat.trans R (R ⊗[R₀] B₀) (Localization.AtPrime P.asIdeal)
  obtain ⟨R₁, hR₁, hflat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct (R₀ := R₀) (R := R)
      (B₀ := B₀) P.asIdeal
  refine ⟨R₁, hR₁, ?_⟩
  simp only [V, U, Set.mem_preimage, Set.mem_ofPred_eq, PrimeSpectrum.comap_asIdeal]
  exact hflat

private theorem exists_fg_V_eq_univ [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ E : Subalgebra R₀ R, E.FG ∧ (↑s : Set R) ⊆ E ∧ V (B₀ := B₀) E = Set.univ := by
  classical
  let ι := {E : Subalgebra R₀ R // E.FG}
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : ι => V (B₀ := B₀) i.1)
    (fun i => isOpen_V i.2) (fun P _ => by
      obtain ⟨E, hE, hP⟩ := exists_fg_mem_V (R₀ := R₀) (B₀ := B₀) P
      exact Set.mem_iUnion.mpr ⟨⟨E, hE⟩, hP⟩)
  refine ⟨t.sup (fun i => i.1) ⊔ Algebra.adjoin R₀ (s : Set R), ?_, ?_, ?_⟩
  · refine Subalgebra.FG.sup ?_ ⟨s, rfl⟩
    refine Finset.sup_induction Subalgebra.fg_bot (fun a ha b hb => ha.sup hb) (fun i _ => i.2)
  · exact fun x hx => (le_sup_right : Algebra.adjoin R₀ (s : Set R) ≤ _) (Algebra.subset_adjoin hx)
  · refine Set.eq_univ_of_forall fun P => ?_
    obtain ⟨i, hi, hP⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ P))
    have hle : i.1 ≤ t.sup (fun i => i.1) ⊔ Algebra.adjoin R₀ (s : Set R) :=
      le_sup_of_le_left (Finset.le_sup (f := fun i : ι => i.1) hi)
    exact V_mono hle hP

private theorem noetherian_case [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) := by
  classical
  obtain ⟨E₁, hE₁, hs, hV⟩ := exists_fg_V_eq_univ (R₀ := R₀) (B₀ := B₀) (R := R) s
  have hclosed : IsClosed (U (B₀ := B₀) E₁)ᶜ := by
    have : IsNoetherianRing E₁ := isNoetherianRing_of_fg hE₁
    exact (Module.Flat.isOpen_setOf_flat_localization_atPrime).isClosed_compl
  obtain ⟨𝔞, h𝔞⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hclosed
  have htop : 𝔞.map (lv (B₀ := B₀) E₁) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let P : PrimeSpectrum (R ⊗[R₀] B₀) := ⟨M, hM.isPrime⟩
    have hP : P ∈ V (B₀ := B₀) E₁ := by rw [hV]; exact Set.mem_univ _
    have hmem : PrimeSpectrum.comap (lv (B₀ := B₀) E₁).toRingHom P ∈ (U (B₀ := B₀) E₁)ᶜ := by
      rw [h𝔞, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
      exact (Ideal.map_le_iff_le_comap.mp hle : _)
    exact hmem hP
  have h1 : (1 : R ⊗[R₀] B₀) ∈ Submodule.span (R ⊗[R₀] B₀) ((lv (B₀ := B₀) E₁) '' 𝔞) := by
    have : (𝔞.map (lv (B₀ := B₀) E₁) : Ideal (R ⊗[R₀] B₀)) =
        Submodule.span (R ⊗[R₀] B₀) ((lv (B₀ := B₀) E₁) '' 𝔞) := rfl
    rw [← this, htop]; trivial
  obtain ⟨n, c, a, hsum⟩ := Submodule.mem_span_set'.mp h1
  have hlift : ∀ i : Fin n, ∃ E : Subalgebra R₀ R, E.FG ∧ c i ∈ Set.range (lv (B₀ := B₀) E) :=
    fun i => exists_fg_mem_range_lv (c i)
  choose F hF hcF using hlift
  let E₂ : Subalgebra R₀ R := E₁ ⊔ Finset.univ.sup F
  have h12 : E₁ ≤ E₂ := le_sup_left
  have hE₂ : E₂.FG := hE₁.sup
    (Finset.sup_induction Subalgebra.fg_bot (fun a ha b hb => ha.sup hb) (fun i _ => hF i))
  have hFle : ∀ i, F i ≤ E₂ := fun i =>
    le_sup_of_le_right (Finset.le_sup (f := F) (Finset.mem_univ i))
  choose c' hc' using hcF
  have ha : ∀ i, ∃ a' ∈ 𝔞, lv (B₀ := B₀) E₁ a' = (a i : R ⊗[R₀] B₀) := fun i => by
    obtain ⟨a', ha', h⟩ := (a i).2
    exact ⟨a', ha', h⟩
  choose a' ha' hla' using ha
  let w : ↥E₂ ⊗[R₀] B₀ := ∑ i, tr (hFle i) (c' i) * tr h12 (a' i)
  have hw𝔞 : w ∈ 𝔞.map (tr (B₀ := B₀) h12) := by
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha' i))
  have hw1 : lv E₂ w = 1 := by
    simp only [w, map_sum, map_mul, lv_tr, hla', hc']
    rw [← hsum]
    simp [smul_eq_mul]
  obtain ⟨E₃, h23, hE₃, hker⟩ :=
    exists_fg_tr_eq_zero hE₂ (w - 1) (by rw [map_sub, hw1, map_one, sub_self])
  refine ⟨E₃, hE₃, hs.trans (h12.trans h23 : E₁ ≤ E₃), ?_⟩
  have h13 : E₁ ≤ E₃ := h12.trans h23
  have htop₃ : 𝔞.map (tr (B₀ := B₀) h13) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : tr h23 w = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at hker; exact hker
    rw [← this]
    have hle : (𝔞.map (tr (B₀ := B₀) h12)).map (tr h23) ≤ 𝔞.map (tr h13) := by
      refine Ideal.map_le_iff_le_comap.mpr (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
      simp only [Ideal.mem_comap, tr_tr]
      exact Ideal.mem_map_of_mem _ hx
    exact hle (Ideal.mem_map_of_mem _ hw𝔞)
  have hall : ∀ Q : PrimeSpectrum (↥E₃ ⊗[R₀] B₀), Q ∈ U (B₀ := B₀) E₃ := by
    intro Q
    refine U_mono h13 Q ?_
    by_contra hQ
    have hQ' : PrimeSpectrum.comap (tr (B₀ := B₀) h13).toRingHom Q ∈ (U (B₀ := B₀) E₁)ᶜ := hQ
    rw [h𝔞, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal] at hQ'
    have : 𝔞.map (tr (B₀ := B₀) h13) ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr hQ'
    rw [htop₃] at this
    exact Q.2.ne_top (top_le_iff.mp this)
  exact Module.flat_of_isLocalized_maximal (↥E₃ ⊗[R₀] B₀) (↥E₃ ⊗[R₀] B₀)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _)
    (fun P hP => hall ⟨P, hP.isPrime⟩)

end Noetherian

section General

variable {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀] [Algebra R₀ R] [Algebra R₀ B₀]

private theorem flat_iff_of_model {A₀ B₀₀ : Type*} [CommRing A₀] [CommRing B₀₀] [Algebra A₀ R₀]
    [Algebra A₀ B₀₀] (e₀ : R₀ ⊗[A₀] B₀₀ ≃ₐ[R₀] B₀)
    (T : Type*) [CommRing T] [Algebra R₀ T] [Algebra A₀ T] [IsScalarTower A₀ R₀ T] :
    Module.Flat T (T ⊗[R₀] B₀) ↔ Module.Flat T (T ⊗[A₀] B₀₀) := by
  let e : T ⊗[A₀] B₀₀ ≃ₗ[T] T ⊗[R₀] B₀ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ R₀ T T B₀₀).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e₀.toLinearEquiv
  exact ⟨fun _ => Module.Flat.of_linearEquiv e, fun _ => Module.Flat.of_linearEquiv e.symm⟩

private theorem general_case [Algebra.FinitePresentation R₀ B₀] [Module.Flat R (R ⊗[R₀] B₀)]
    (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R₀ B₀
  let A₀ := P.Core
  have : Algebra.FiniteType ℤ A₀ := inferInstance
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let B₀₀ := P.ModelOfHasCoeffs A₀
  have : Algebra.FinitePresentation A₀ B₀₀ := inferInstance
  have : Algebra.FiniteType A₀ B₀₀ := inferInstance
  let e₀ : R₀ ⊗[A₀] B₀₀ ≃ₐ[R₀] B₀ := P.tensorModelOfHasCoeffsEquiv A₀
  let : Algebra A₀ R := ((algebraMap R₀ R).comp (algebraMap A₀ R₀)).toAlgebra
  have : IsScalarTower A₀ R₀ R :=
    IsScalarTower.of_algebraMap_eq (R := A₀) (S := R₀) (A := R) fun _ => rfl
  have : Module.Flat R (R ⊗[A₀] B₀₀) := (flat_iff_of_model e₀ R).mp inferInstance
  obtain ⟨R₁', hfg', hs', hflat'⟩ := noetherian_case (R₀ := A₀) (R := R) (B₀ := B₀₀) s
  obtain ⟨t, ht⟩ := hfg'
  refine ⟨Algebra.adjoin R₀ (t : Set R), ⟨t, rfl⟩, ?_, ?_⟩
  · have hle : R₁' ≤ (Algebra.adjoin R₀ (t : Set R)).restrictScalars A₀ := by
      rw [← ht]
      exact Algebra.adjoin_le Algebra.subset_adjoin
    exact hs'.trans hle
  · set R₁ : Subalgebra R₀ R := Algebra.adjoin R₀ (t : Set R) with hR₁
    have hle : ∀ x ∈ R₁', x ∈ R₁ := by
      have : R₁' ≤ R₁.restrictScalars A₀ := by
        rw [← ht]
        exact Algebra.adjoin_le Algebra.subset_adjoin
      exact fun x hx => this hx
    let : Algebra A₀ R₁ := ((algebraMap R₀ R₁).comp (algebraMap A₀ R₀)).toAlgebra
    have : IsScalarTower A₀ R₀ R₁ :=
      IsScalarTower.of_algebraMap_eq (R := A₀) (S := R₀) (A := R₁) fun _ => rfl
    let j : R₁' →ₐ[A₀] R₁ :=
      { toFun := fun x => ⟨x.1, hle x.1 x.2⟩
        map_one' := rfl
        map_zero' := rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    let : Algebra R₁' R₁ := j.toRingHom.toAlgebra
    have : IsScalarTower A₀ R₁' R₁ :=
      IsScalarTower.of_algebraMap_eq (R := A₀) (S := R₁') (A := R₁) fun a => (j.commutes a).symm
    have : Module.Flat R₁ (R₁ ⊗[R₁'] (R₁' ⊗[A₀] B₀₀)) := inferInstance
    have : Module.Flat R₁ (R₁ ⊗[A₀] B₀₀) :=
      Module.Flat.of_linearEquiv
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ R₁' R₁ R₁ B₀₀).symm
    exact (flat_iff_of_model e₀ R₁).mpr inferInstance


end General

end

end Module.Flat.FGSubalgebraTensorProduct

/-- **Noetherian approximation of flatness.** If `R ⊗[R₀] B₀` is flat over `R` for a finitely
presented `R₀`-algebra `B₀`, then any finite subset of `R` lies in a finitely generated
`R₀`-subalgebra `R₁` with `R₁ ⊗[R₀] B₀` flat over `R₁`.

Source: [Stacks Project, Lemma 10.168.1 (Tag 02JO)](https://stacks.math.columbia.edu/tag/02JO),
its last assertion, for `R` as the directed union of its finitely generated `R₀`-subalgebras. -/
public theorem Module.Flat.exists_fg_subalgebra_flat_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) :=
  Module.Flat.FGSubalgebraTensorProduct.general_case s

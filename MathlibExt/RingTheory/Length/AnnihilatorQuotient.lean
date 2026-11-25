/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Support

/-!
# Finite length from an annihilating quotient

A finite module annihilated by an ideal has finite length whenever the
corresponding quotient of the base ring has finite length.  The proof regards
the module as a finite module over the quotient ring and then transports
length back along the surjective quotient map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

namespace Module

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The quotient by the annihilator of a finite-length module again has
finite length.  A finite generating family embeds the faithful quotient into
a finite product of copies of the module. -/
theorem quotient_annihilator_length_ne_top
    (hM : Module.length R M ≠ ⊤) :
    Module.length R (R ⧸ Module.annihilator R M) ≠ ⊤ := by
  have hfiniteLength : IsFiniteLength R M :=
    Module.length_ne_top_iff.mp hM
  have hNoetherian : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  let : IsNoetherian R M := hNoetherian
  let : Module.Finite R M := IsNoetherian.finite R M
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let eval : R →ₗ[R] (Fin n → M) :=
    LinearMap.pi fun i => LinearMap.toSpanSingleton R M (s i)
  have heval_apply (r : R) : eval r = fun i => r • s i := by
    rfl
  have hker : Module.annihilator R M = eval.ker := by
    ext r
    rw [LinearMap.mem_ker, Module.mem_annihilator]
    constructor
    · intro hr
      funext i
      rw [heval_apply, Pi.zero_apply]
      exact hr (s i)
    · intro hr m
      have hgenerators : ∀ i, r • s i = 0 := by
        intro i
        have hi := congrFun hr i
        simpa only [heval_apply, Pi.zero_apply] using hi
      have hann : r ∈ (Submodule.span R (Set.range s)).annihilator :=
        (Submodule.mem_annihilator_span (Set.range s) r).mpr fun x => by
          obtain ⟨i, hi⟩ := x.property
          rw [← hi]
          exact hgenerators i
      rw [hs, Submodule.annihilator_top] at hann
      exact Module.mem_annihilator.mp hann m
  let lift : (R ⧸ Module.annihilator R M) →ₗ[R] (Fin n → M) :=
    (Module.annihilator R M).liftQ eval hker.le
  have hlift : Function.Injective lift := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot'
      (Module.annihilator R M) eval hker
  have hle : Module.length R (R ⧸ Module.annihilator R M) ≤
      Module.length R (Fin n → M) :=
    Module.length_le_of_injective lift hlift
  rw [Module.length_pi, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin] at hle
  have hprod : (n : ENat) * Module.length R M ≠ ⊤ := by
    rw [← ENat.natCast_toNat_eq_self.mpr hM, ← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  exact ne_top_of_le_ne_top hprod hle

/-- Every prime in the support of a finite-length finite module is maximal. -/
theorem isMaximal_of_mem_support_of_length_ne_top
    [Module.Finite R M] (hM : Module.length R M ≠ ⊤)
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    p.asIdeal.IsMaximal := by
  let I := Module.annihilator R M
  have hIp : I ≤ p.asIdeal :=
    Module.mem_support_iff_of_finite.mp hp
  have hquot : Module.length R (R ⧸ I) ≠ ⊤ :=
    quotient_annihilator_length_ne_top R M hM
  have hfiniteLength : IsFiniteLength R (R ⧸ I) :=
    Module.length_ne_top_iff.mp hquot
  have hArtinian : IsArtinian R (R ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  let : IsArtinian R (R ⧸ I) := hArtinian
  let : IsArtinianRing (R ⧸ I) :=
    isArtinian_of_tower R hArtinian
  let q : Ideal (R ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hIp)
  let : q.IsMaximal := inferInstance
  have hcomap : q.comap (Ideal.Quotient.mk I) = p.asIdeal := by
    dsimp only [q]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIp]
  rw [← hcomap]
  exact Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- A finite module over a Noetherian ring has finite length when every
prime in its support is maximal. -/
theorem length_ne_top_of_forall_isMaximal_mem_support
    [IsNoetherianRing R] [Module.Finite R M]
    (hmax : ∀ p : PrimeSpectrum R,
      p ∈ Module.support R M → p.asIdeal.IsMaximal) :
    Module.length R M ≠ ⊤ := by
  let I := Module.annihilator R M
  let Q := R ⧸ I
  let htor : Module.IsTorsionBySet R M I := by
    simpa only [I] using Module.isTorsionBySet_annihilator R M
  let : Module Q M := htor.module
  let : IsScalarTower R Q M := htor.isScalarTower
  let : IsNoetherianRing Q := by
    dsimp only [Q]
    infer_instance
  let : Module.Finite Q M :=
    Module.Finite.of_restrictScalars_finite R Q M
  have hdim : Ring.KrullDimLE 0 Q := Ring.KrullDimLE.mk₀ fun q hq => by
    let _ : q.IsPrime := hq
    let p : PrimeSpectrum R :=
      ⟨q.comap (Ideal.Quotient.mk I), Ideal.comap_isPrime _ q⟩
    have hIp : I ≤ p.asIdeal := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.zero_mem
    have hpSupport : p ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr hIp
    have hpMax := hmax p hpSupport
    have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hpMax
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmap
    exact hmap.resolve_left hq.ne_top
  let : Ring.KrullDimLE 0 Q := hdim
  let : IsArtinianRing Q :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  rw [Module.length_eq_of_surjective
    (R := Q) (M := M) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

/-- A finite module annihilated by `I` has finite length if `R/I` has finite
length as an `R`-module. -/
theorem length_ne_top_of_finite_of_ideal_le_annihilator
    [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M)
    (hquot : Module.length R (R ⧸ I) ≠ ⊤) :
    Module.length R M ≠ ⊤ := by
  have htor : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr hI
  let : Module (R ⧸ I) M := htor.module
  have hfiniteLengthQuotient : IsFiniteLength R (R ⧸ I) :=
    Module.length_ne_top_iff.mp hquot
  have hArtinianQuotient : IsArtinian R (R ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      hfiniteLengthQuotient).2
  let : IsArtinian R (R ⧸ I) := hArtinianQuotient
  let : IsArtinianRing (R ⧸ I) :=
    isArtinian_of_tower R hArtinianQuotient
  let : Module.Finite (R ⧸ I) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  rw [Module.length_eq_of_surjective
    (R := R ⧸ I) (M := M) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Module

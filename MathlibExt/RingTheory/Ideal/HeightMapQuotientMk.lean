/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_height_map_quotientMk_span_singleton_add_one.lean`
and
`P2M/Sol/S_Ideal_height_map_quotientMk_span_singleton_add_one.lean`
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

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

universe u

open IsLocalRing
open scoped Pointwise

private theorem annihilator_self_eq_bot {R : Type*} [CommRing R] :
    Module.annihilator R R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  simpa using Module.mem_annihilator.mp hr 1

private theorem ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hkey : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
    have h1 : ringKrullDim (QuotSMulTop x R) = Module.supportDim R (QuotSMulTop x R) :=
      (Module.supportDim_quotient_eq_ringKrullDim (x • (⊤ : Submodule R R))).symm
    rw [h1, ← Module.supportDim_self_eq_ringKrullDim]
    refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
      ?_ hx
    intro p hp
    refine hxmin p ?_
    rwa [annihilator_self_eq_bot] at hp
  have hspan : Ideal.span {x} = x • (⊤ : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
    simp
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact hkey

namespace Ideal

/-- For a prime `p` of a Noetherian ring, if `x ∈ p` avoids every minimal
prime below `p`, then the height of the image of `p` in `R ⧸ (x)` plus one
equals the height of `p`. -/
public theorem height_map_quotientMk_span_singleton_add_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] {x : R}
    (hx : x ∈ p) (hxmin : ∀ q ∈ minimalPrimes R, q ≤ p → x ∉ q) :
    (p.map (Ideal.Quotient.mk (Ideal.span {x}))).height + 1 = p.height := by
  classical
  set J : Ideal R := Ideal.span {x} with hJ
  set P : Ideal (R ⧸ J) := p.map (Ideal.Quotient.mk J) with hP
  have hJp : J ≤ p := by rw [hJ, Ideal.span_singleton_le_iff_mem]; exact hx
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ p := by rw [Ideal.mk_ker]; exact hJp
  haveI hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : P.comap (Ideal.Quotient.mk J) = p := by
    rw [hP, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hJp]
  haveI : P.LiesOver p := ⟨by rw [Ideal.under_def, Ideal.Quotient.algebraMap_eq, hcomap]⟩
  let Rp := Localization.AtPrime p
  have hxm : algebraMap R Rp x ∈ maximalIdeal Rp :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p x).mpr hx
  have hxmin' : ∀ Q ∈ minimalPrimes Rp, algebraMap R Rp x ∉ Q := by
    intro Q hQ hxQ
    haveI hQp : Q.IsPrime := hQ.1.1
    let q : Ideal R := Q.comap (algebraMap R Rp)
    have hqp : q ≤ p := by
      have hle : Q ≤ maximalIdeal Rp := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hQp)
      simpa [q, IsLocalization.AtPrime.under_maximalIdeal Rp p] using
        Ideal.comap_mono (f := algebraMap R Rp) hle
    have hqmin : q ∈ minimalPrimes R := by
      rw [minimalPrimes_eq_minimals]
      refine ⟨Ideal.comap_isPrime _ Q, fun q' hq' hq'q => ?_⟩
      haveI : q'.IsPrime := hq'
      have hdisj : Disjoint (p.primeCompl : Set R) q' := by
        rw [Set.disjoint_left]
        intro r hr hr'
        exact hr (hqp (hq'q hr'))
      have hQ'p : (q'.map (algebraMap R Rp)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl Rp q' hq' hdisj
      have hle : q'.map (algebraMap R Rp) ≤ Q := by
        calc q'.map (algebraMap R Rp) ≤ q.map (algebraMap R Rp) := Ideal.map_mono hq'q
          _ = Q := IsLocalization.map_under p.primeCompl Rp Q
      have hge : Q ≤ q'.map (algebraMap R Rp) := hQ.2 ⟨hQ'p, bot_le⟩ hle
      intro r hr
      have hr' : algebraMap R Rp r ∈ q'.map (algebraMap R Rp) := hge hr
      have h' : r ∈ Ideal.under R (q'.map (algebraMap R Rp)) := hr'
      rwa [IsLocalization.under_map_of_isPrime_disjoint p.primeCompl Rp hq' hdisj] at h'
    exact hxmin q hqmin hqp hxQ
  have hdim := ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    hxm hxmin'
  have h1 : ringKrullDim Rp = p.height := IsLocalization.AtPrime.ringKrullDim_eq_height p Rp
  have hmapJ : J.map (algebraMap R Rp) = Ideal.span {algebraMap R Rp x} := by
    rw [hJ, Ideal.map_span, Set.image_singleton]
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ J) p.primeCompl = P.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective P p
      Ideal.Quotient.mk_surjective
  haveI : IsLocalization.AtPrime (Rp ⧸ J.map (algebraMap R Rp)) P := by
    rw [IsLocalization.AtPrime, ← hsub]
    infer_instance
  have h2 : ringKrullDim (Rp ⧸ J.map (algebraMap R Rp)) = P.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Rp ⧸ J.map (algebraMap R Rp))
  rw [hmapJ] at h2
  rw [h2, h1] at hdim
  exact_mod_cast hdim

end Ideal

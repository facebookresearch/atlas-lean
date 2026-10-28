/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.SetTheory.Cardinal.Finite

/-!
# foundation: regularity of polynomial rings and their localizations

Lane R1. This bank closes items (1a)–(1c) unconditionally:

* (1a) `K[X]` is regular — Mathlib has the full regularity theory
  (`Mathlib/RingTheory/RegularLocalRing/`, Nailin Guan 2025), so no
  Jacobson/Zariski development is needed: `MvPolynomial`
  over a regular ring is regular, and fields are regular.
* (1b) localization preserves regularity — definitional in Mathlib:
  `IsRegularRing` is defined as "every prime localization is regular local".
* (1c) regular ⟹ `dim = embdim` — definitional: Mathlib's `IsRegularLocalRing`
  is stated exactly as `(maximalIdeal R).spanFinrank = ringKrullDim R`.

status note: Mathlib v4.34.0 contains
`RingTheory/RegularLocalRing/{Defs,Polynomial}.lean`, and the repo itself
already banks the headline corollary
(`MultiplicityNonvanishing.mult_dim_atPrime_eq_spanFinrank`, §8, unconditional).
This file is the clean, self-contained (Mathlib-only imports) foundation with stable names for R2/R3
and H-track consumers; twin
statements in `MultiplicityNonvanishing` are noted at each site.

## Stable interface for consumers (R2/R3/H-track)

* `IsRegularLocal R` (this file, §1): the stated predicate,
  `(maximalIdeal R).spanFinrank = ringKrullDim R` for local `R`.
  Use `isRegularLocal_iff_isRegularLocalRing` to move to Mathlib's class.
* `regRing_dim_atPrime_eq_spanFinrank` (§3): SPEC-exact
  `dim R_Q = embdim R_Q` for every prime `Q` of `MvPolynomial (Fin m) K`.
* `regRing_dim_atPrime_eq_of_minimal` (§3): `dim R_Q = d` for a spanning
  family of size `d` that is minimal (`d ≤ embdim`).
* `regLocal_dim_eq_of_spanning_of_minimal` (§3): the general local-ring form.

## Sections

* (§1) `IsRegularLocal`: definition, iff with `IsRegularLocalRing`,
  the general inequality `dim ≤ embdim`, constructor from `embdim ≤ dim`.
* (§2) Basic API: fields (both sides computed: `𝔪 = ⊥`, both sides `0`),
  local PIDs, DVRs, PIDs-as-rings, cotangent-space form.
* (§3) `K[X]` regularity: field → `IsRegularRing K` → `IsRegularRing K[X]`
  → every prime (hence maximal) localization regular local; SPEC-exact
  corollaries; spanning/minimal-generator masters.
* (§4) gap-reg register: every item closed with pointer. No Zariski needed.

## Mathlib API map (as requested by the lane design note)

* Regularity: `IsRegularLocalRing` (class: local + Noetherian +
  `spanFinrank = ringKrullDim`), `isRegularLocalRing_iff`,
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`,
  `IsRegularLocalRing.of_ringEquiv`, `iff_finrank_cotangentSpace`,
  local-PID-domain instance, `IsRegularRing` (class: Noetherian + every
  prime localization regular local), `isRegularRing_iff`,
  `IsRegularLocalRing.of_isRegularRing_of_isLocalRing`,
  Dedekind→`IsRegularRing` instance, `Polynomial`/`MvPolynomial`
  `.isRegularRing_of_isRegularRing` instances — all in
  `RingTheory/RegularLocalRing/{Defs,Polynomial}.lean`.
* Krull side: `ringKrullDim` (`KrullDimension/Basic`),
  `ringKrullDim_eq_zero_of_field` (`KrullDimension/Field`),
  `ringKrullDim_le_spanFinrank_maximalIdeal`,
  `Ideal.height_le_spanFinrank` (`Ideal/KrullsHeightTheorem`).
* Jacobson side (mapped, not needed): `IsJacobsonRing` exists
  (`RingTheory/Jacobson/Ring.lean`, a class with radical/jacobson
  characterizations); `Jacobson/{Ideal,Polynomial,Artinian,Semiprimary,
  Radical}` exist. The polynomial-regularity proof in Mathlib goes through
  monic-span + `KrullDimension/Polynomial` machinery, never through Zariski
  lemmas or residue-field finiteness — so this bank takes no dependency
  on Jacobson theory and prices no Zariski gap.
-/

/-! ## §1. `IsRegularLocal`: the stated predicate and core API -/

/-- Regularity for a local ring: embedding dimension (minimal number of
generators of `𝔪`, via `spanFinrank`, to match the SPEC shapes) equals
Krull dimension. This is exactly Mathlib's `IsRegularLocalRing` (see
`isRegularLocal_iff_isRegularLocalRing`); the bare-`Prop` form keeps the
stated stable name for R2/R3 consumers.
-/
def IsRegularLocal (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  (IsLocalRing.maximalIdeal R).spanFinrank = ringKrullDim R

#print axioms IsRegularLocal

/-- `IsRegularLocal` is Mathlib's `IsRegularLocalRing`.
-/
theorem isRegularLocal_iff_isRegularLocalRing (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocal R ↔ IsRegularLocalRing R := by
  unfold IsRegularLocal
  exact (isRegularLocalRing_iff R).symm

#print axioms isRegularLocal_iff_isRegularLocalRing

/-- General inequality (Krull's Hauptidealsatz): `dim ≤ embdim` for every
Noetherian local ring. Regularity is the reverse inequality.
-/
theorem regLocal_dim_le_embdim (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ringKrullDim R ≤ (IsLocalRing.maximalIdeal R).spanFinrank :=
  ringKrullDim_le_spanFinrank_maximalIdeal R

#print axioms regLocal_dim_le_embdim

/-- Constructor: `embdim ≤ dim` forces regularity (the other direction is
always true).
-/
theorem regLocal_of_embdim_le (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hle : (IsLocalRing.maximalIdeal R).spanFinrank ≤ ringKrullDim R) :
    IsRegularLocal R := by
  rw [isRegularLocal_iff_isRegularLocalRing]
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R hle

#print axioms regLocal_of_embdim_le

/-- Regularity gives `dim = embdim` (class form).
-/
theorem regLocal_dim_eq_embdim (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    ringKrullDim R = (IsLocalRing.maximalIdeal R).spanFinrank :=
  (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm

#print axioms regLocal_dim_eq_embdim

/-- Regularity gives `dim = embdim` (predicate form).
-/
theorem regLocal_dim_eq_embdim_of (R : Type*) [CommRing R] [IsLocalRing R]
    (h : IsRegularLocal R) :
    ringKrullDim R = (IsLocalRing.maximalIdeal R).spanFinrank :=
  h.symm

#print axioms regLocal_dim_eq_embdim_of

/-- Cotangent-space form: regularity says `dim_κ 𝔪/𝔪² = dim`, matching the
phrasing `d = embdim(A) = dim_κ 𝔪/𝔪²`.
-/
theorem regLocal_iff_finrank_cotangent (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsRegularLocal R ↔
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) = ringKrullDim R := by
  rw [isRegularLocal_iff_isRegularLocalRing]
  exact IsRegularLocalRing.iff_finrank_cotangentSpace R

#print axioms regLocal_iff_finrank_cotangent

/-! ## §2. Basic API: fields, PIDs, DVRs -/

/-- For a field, `𝔪 = ⊥` so the embedding dimension is `0`.
`IsField`-explicit form (avoids overlapping `[Field K]`/`[IsLocalRing K]`
instances); field consumers discharge `hK` via `Field.toIsField`.
-/
theorem regLocal_field_spanFinrank_eq_zero (K : Type*) [CommRing K]
    [IsLocalRing K] (hK : IsField K) :
    (IsLocalRing.maximalIdeal K).spanFinrank = 0 := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hK,
    Submodule.spanFinrank_bot]

#print axioms regLocal_field_spanFinrank_eq_zero

/-- For a field, the Krull dimension is `0` (`IsField`-explicit form).
-/
theorem regLocal_field_dim_eq_zero (K : Type*) [CommRing K]
    (hK : IsField K) :
    ringKrullDim K = 0 :=
  ringKrullDim_eq_zero_of_isField hK

#print axioms regLocal_field_dim_eq_zero

/-- Fields are regular (both sides `0`; `IsField`-explicit form).
-/
theorem regLocal_field (K : Type*) [CommRing K] [IsLocalRing K]
    (hK : IsField K) :
    IsRegularLocal K := by
  unfold IsRegularLocal
  simp only [regLocal_field_spanFinrank_eq_zero K hK,
    regLocal_field_dim_eq_zero K hK, Nat.cast_zero]

#print axioms regLocal_field

/-- Fields are regular local rings (class form, via the local-PID instance;
`IsField`-explicit form).
-/
theorem regLocalRing_field (K : Type*) [CommRing K] [IsLocalRing K]
    (hK : IsField K) :
    IsRegularLocalRing K := by
  let := hK.toField
  infer_instance

#print axioms regLocalRing_field

/-- Local PID domains are regular (Mathlib instance).
-/
theorem regLocalRing_of_local_pid (R : Type*) [CommRing R] [IsLocalRing R]
    [IsDomain R] [IsPrincipalIdealRing R] :
    IsRegularLocalRing R :=
  inferInstance

#print axioms regLocalRing_of_local_pid

/-- DVRs are regular: a DVR is a local PID domain, so the instance fires.
-/
theorem regLocalRing_of_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    IsRegularLocalRing R :=
  inferInstance

#print axioms regLocalRing_of_dvr

/-- DVRs are regular (predicate form).
-/
theorem regLocal_of_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    IsRegularLocal R := by
  rw [isRegularLocal_iff_isRegularLocalRing]
  exact regLocalRing_of_dvr R

#print axioms regLocal_of_dvr

/-- PIDs are regular rings (PID → Dedekind → regular; Mathlib instances).
-/
theorem regRing_of_pid (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    IsRegularRing R :=
  inferInstance

#print axioms regRing_of_pid

/-! ## §3. `K[X]` regularity and the SPEC-exact corollaries -/

/-- Fields are regular rings (field → PID → Dedekind → regular).
Twin of `MultiplicityNonvanishing.mult_isRegularRing_of_field` (proved there by
hand; here by Mathlib instance chain).
-/
theorem regRing_field (K : Type*) [Field K] : IsRegularRing K :=
  inferInstance

#print axioms regRing_field

/-- `K[X₁,…,X_m]` is regular ((1a), closed).
-/
theorem regRing_mvPolynomial (K : Type*) [Field K] (m : ℕ) :
    IsRegularRing (MvPolynomial (Fin m) K) :=
  inferInstance

#print axioms regRing_mvPolynomial

/-- Localization at a prime of a regular ring is regular ((1b),
closed — definitional in `IsRegularRing`).
-/
theorem regRing_localization_atPrime (R : Type*) [CommRing R] [IsRegularRing R]
    (P : Ideal R) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) :=
  inferInstance

#print axioms regRing_localization_atPrime

/-- Every prime localization of `K[X₁,…,X_m]` is regular local.
-/
theorem regLocalRing_atPrime (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) :=
  inferInstance

#print axioms regLocalRing_atPrime

/-- Every prime localization of `K[X₁,…,X_m]` is regular (predicate form).
-/
theorem regLocal_atPrime (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    IsRegularLocal (Localization.AtPrime P) := by
  rw [isRegularLocal_iff_isRegularLocalRing]
  exact regLocalRing_atPrime K P

#print axioms regLocal_atPrime

/-- Every maximal-ideal localization of `K[X₁,…,X_m]` is regular local
(maximal ideals are prime via `IsMaximal.isPrime'`). This is the exact
form the lane design note asks for; the prime form above is stronger.
-/
theorem regLocalRing_atMaximal (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime P) :=
  inferInstance

#print axioms regLocalRing_atMaximal

/-- SPEC-exact `dim R_Q = embdim R_Q` for every prime `Q` ((1c),
closed). Twin of `MultiplicityNonvanishing.mult_dim_atPrime_eq_spanFinrank`.
-/
theorem regRing_dim_atPrime_eq_spanFinrank (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    ringKrullDim (Localization.AtPrime P) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank :=
  (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := Localization.AtPrime P)).symm

#print axioms regRing_dim_atPrime_eq_spanFinrank

/-- SPEC-exact `dim R_Q = embdim R_Q` at maximal ideals.
-/
theorem regRing_dim_atMaximal_eq_spanFinrank (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsMaximal] :
    ringKrullDim (Localization.AtPrime P) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank :=
  (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := Localization.AtPrime P)).symm

#print axioms regRing_dim_atMaximal_eq_spanFinrank

/-- A spanning family of size `d` bounds the embedding dimension
(general local-ring form of
`MultiplicityNonvanishing.mult_spanFinrank_maximalIdeal_atPrime_le`).
-/
theorem regLocal_spanFinrank_le_of_spanning (R : Type*) [CommRing R]
    [IsLocalRing R] (d : ℕ) (g : Fin d → R)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal R).spanFinrank ≤ d := by
  rw [← hgen]
  refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
    (Set.finite_range g)) ?_
  have h1 : Set.range g = g '' Set.univ := by rw [Set.image_univ]
  rw [h1]
  refine le_trans (Set.ncard_image_le Set.finite_univ) ?_
  rw [Set.ncard_univ, Nat.card_fin]

#print axioms regLocal_spanFinrank_le_of_spanning

/-- Minimal-generator master (general local-ring form): a spanning family of
size `d` that is minimal (`d ≤ embdim`) forces `dim = d` over a regular
local ring.
-/
theorem regLocal_dim_eq_of_spanning_of_minimal (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ)
    (g : Fin d → R)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal R)
    (hmin : d ≤ (IsLocalRing.maximalIdeal R).spanFinrank) :
    ringKrullDim R = d := by
  have hle : ringKrullDim R ≤ d := by
    refine le_trans (ringKrullDim_le_spanFinrank_maximalIdeal R) ?_
    exact_mod_cast regLocal_spanFinrank_le_of_spanning R d g hgen
  refine le_antisymm hle ?_
  rw [regLocal_dim_eq_embdim]
  exact_mod_cast hmin

#print axioms regLocal_dim_eq_of_spanning_of_minimal

/-- Minimal-generator master at `R_Q` (SPEC shape): `dim R_Q = d` for a
minimal spanning family. Twin of
`MultiplicityNonvanishing.mult_ringKrullDim_atPrime_eq_of_minimal`.
-/
theorem regRing_dim_atPrime_eq_of_minimal (K : Type*) [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hmin : d ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime P)).spanFinrank) :
    ringKrullDim (Localization.AtPrime P) = d :=
  regLocal_dim_eq_of_spanning_of_minimal (Localization.AtPrime P) d g hgen
    hmin

#print axioms regRing_dim_atPrime_eq_of_minimal

/-! ## §4. Gap-reg register: all items closed

* Gap-reg-1 (`K[X]` regular): closed by `regRing_mvPolynomial` —
  `MvPolynomial.isRegularRing_of_isRegularRing` over `regRing_field`.
* Gap-reg-2 (localization preserves regularity): closed by
  `regRing_localization_atPrime` — definitional in `IsRegularRing`.
* Gap-reg-3 (non-rational maximal ideals need Zariski facts): closed as
  unnecessary — Mathlib's polynomial-regularity proof goes through
  monic-span + `KrullDimension/Polynomial` machinery
  (`Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal`),
  quantifying over all primes at once; no rational/non-rational split
  and no Nullstellenssatz is ever needed. `regLocalRing_atMaximal` covers
  every maximal ideal uniformly.
* Gap-reg-4 (Jacobson-API sufficiency): closed as unnecessary — mapped in
  the header (`IsJacobsonRing` + instances exist) but not consumed.

Residual register: none for foundation. (1a)+(1b)+(1c) all
unconditional. R2/R3 may consume `IsRegularLocal`,
`regRing_dim_atPrime_eq_spanFinrank`, and
`regRing_dim_atPrime_eq_of_minimal` directly.
-/


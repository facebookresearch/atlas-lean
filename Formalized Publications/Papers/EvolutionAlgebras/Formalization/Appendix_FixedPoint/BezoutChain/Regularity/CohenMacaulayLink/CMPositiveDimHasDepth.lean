/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Regular.RegularSequence
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.CohenMacaulayFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment

/-!
# C3: CM + positive dimension has depth ≥ 1 (`cmlink` §3)

Formalizes the C3 block:
over a Noetherian local ring, a CM quotient `S = R ⧸ J'` of positive dimension
carries no associated prime at the maximal ideal
(`maximalIdeal_notMem_associatedPrimes_of_cm_quotient`), via C3a
(localization of CM is CM) + unmixedness + the `mk₀` close.

## Route (design note §3, F7 order C2 → C3)

* C2 interface: the sibling C2 lane is pending, so its three conclusions are
  taken as explicit hypotheses (`hC2loc`, `hC2comp`, `hC2quot`, exact design note-§2
  binders). The F7 dependency is named by `isCM_quotient_span_of_isRegular`,
  which iterates C2 along a regular sequence (list induction via the
  double-quotient iso + the `QuotSMulTop ≃ span`-quotient bridge).
* C3a (`isCM_localization_atPrime`): localization of CM is CM, derived from the
  `C3aGap` residual + GHT (`IsLocalization.AtPrime.ringKrullDim_eq_height`) +
  proved `grade_le_ringKrullDim`.
* Unmixedness (`isHunmixed_of_isCM`): every `P ∈ Ass(R ⧸ J')` is minimal over
  `J'`, via `Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes`
  (`AssociatedPrime/Localization.lean`) + proved
  `GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes` (:895).
* Close: `𝔪 ∉ minimalPrimes` (else all primes are maximal, hence
  `KrullDimLE 0` via `Ring.KrullDimLE.mk₀`, against `hpos`), hence `𝔪 ∉ Ass`.

## Residual register (exact)

* C2 (`hC2loc`/`hC2comp`/`hC2quot`): sibling lane; substitution is mechanical
  since `IsCM` below is a verbatim copy of the design note-§2 definition
  (`C2.IsCM = C3.IsCM` by `rfl` after delta).
* `C3aGap` (`hC3a_gap`): in a CM local ring `S`, regular sequences of every
  length `≤ height p` exist inside the maximal ideal of `S_p`. This is exactly
  C3a's content (C3a is derived from it below; conversely C3a gives
  `grade = height`, hence a length-`height` witness since finite `sSup` over
  `ℕ`-casts is attained, plus prefixes). The F7 route to close it: take a
  maximal regular sequence in `p`, localize it (regularity localizes),
  iterate the proved C2-step, then GHT. The maximality endgame needs prime
  avoidance + unmixedness at smaller dimension (joint dim-induction, future
  work); the gap is assumed, never sorried.

## Brief repairs applied

* F10-prefix: the design note's §2 signature writes `Module.associatedPrimes` for the
  set, but in mathlib v4.34.0 the set is root-level `associatedPrimes`
  (`AssociatedPrime/Basic.lean`); `Module.associatedPrimes` is only the lemma
  namespace of `AssociatedPrime/Localization.lean`. The brief form does not
  elaborate, so this file uses root `associatedPrimes` (same object as the
  proved `GradeDepthFragment` bank consumes).

## What this file proves

* `IsCM` (verbatim design note-§2 copy), `C3aGap`, `hC2loc`/`hC2comp`/`hC2quot` interface.
* `isCM_quotient_span_of_isRegular` (F7 C2-iteration, conditional on C2).
* `isCM_localization_atPrime` (C3a, conditional on C2 + `C3aGap`).
* `isHunmixed_of_isCM` (unmixedness of CM quotients).
* `maximalIdeal_notMem_associatedPrimes_of_cm_quotient` (C3 close).
-/

namespace EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMPositiveDimHasDepth

open RingTheory.Sequence

universe u

section C2Interface

/-- Cohen–Macaulay (local): grade w.r.t. 𝔪 equals Krull dimension.
Coercion dance matches proved `DepthEqDimAt` (GradeDepthFragment:957).
Verbatim copy of design note §2 (see module docstring for the substitution note). -/
def IsCM (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  ((GradeDepthFragment.grade R R (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞)
    = ringKrullDim R

/- C2 interface (sibling lane), exact design note-§2 shapes (see also the per-theorem
explicit binders below — Lean requires hypothesis-variables to appear in the
statement, so section-`variable` cannot carry them; see probe note):
* `hC2loc` (companion): `∀ {R} [CommRing R] [IsLocalRing R] (J'),
  J' ≤ maximalIdeal R → IsLocalRing (R ⧸ J')`.
* `hC2comp` (F5): `∀ {R} [CommRing R] [IsLocalRing R] (J') (_hle)
  [IsLocalRing (R ⧸ J')], maximalIdeal (R ⧸ J') = map (mk J') (maximalIdeal R)`.
* `hC2quot` (C2 main): `∀ {R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (_hCM: IsCM R) {x} (_hx) (_hreg) [IsLocalRing (R ⧸ span{x})],
  IsCM (R ⧸ span{x})` (modulo the `IsCM` namespace copy, `rfl`-equal).
* `hC3a_gap`: `∀ (S) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  (p) [p.IsPrime], IsCM S → C3aGap S p`. -/

/-- C3a gap (residual, see module docstring): in the Noetherian local ring `S`,
regular sequences of every length `≤ height p` exist inside the maximal ideal
of `S_p`. This is exactly C3a's content, stated where `GradeSet` consumes it. -/
def C3aGap (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (p : Ideal S) [p.IsPrime] : Prop :=
  ∀ (n : ℕ), (n : ℕ∞) ≤ p.height →
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) ∧ rs.length = n

/- Note (Lean semantics, verified by probe): a section `variable` is usable in
a tactic proof only when mentioned in the statement, and outer-section
variables are unusable in nested sections at all. Hence: one flat section,
type/instance variables only; every hypothesis (`hC2*`, `hC3a_gap`) is an
explicit per-theorem binder with the exact ∀-shape above. -/

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S]

/- ## Quotient helpers -/

/-- Kernel-quotient correspondence: pulling back the image of `K` along
`mk J'` recovers `K ⊔ J'`. -/
theorem comap_map_quotient_mk_sup (J' K : Ideal R) :
    Ideal.comap (Ideal.Quotient.mk J') (Ideal.map (Ideal.Quotient.mk J') K)
      = K ⊔ J' := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    obtain ⟨c, hcK, hcc⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    have hsub : x - c ∈ J' := by
      have h : Ideal.Quotient.mk J' x - Ideal.Quotient.mk J' c = 0 := by
        rw [hcc, sub_self]
      rwa [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
    have hxeq : x = c + (x - c) := by abel
    rw [hxeq]
    exact Submodule.add_mem_sup hcK hsub
  · rw [sup_le_iff]
    refine ⟨Ideal.le_comap_map, fun x hx => ?_⟩
    rw [Ideal.mem_comap]
    have h0 : Ideal.Quotient.mk J' x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [h0]
    exact Submodule.zero_mem _

/-- The correspondence collapses when `J' ≤ K`. -/
theorem comap_map_quotient_mk_eq_self (J' K : Ideal R) (hle : J' ≤ K) :
    Ideal.comap (Ideal.Quotient.mk J') (Ideal.map (Ideal.Quotient.mk J') K) = K := by
  rw [comap_map_quotient_mk_sup, sup_eq_left.mpr hle]

/-- Primality descends along a surjective hom from a prime comap. Used to push
minimality back and forth across `R ⧸ J'`. -/
theorem isPrime_of_comap_isPrime_of_surjective {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (P : Ideal S)
    (hP : (Ideal.comap f P).IsPrime) : P.IsPrime := by
  constructor
  · intro htop
    apply hP.ne_top
    rw [htop]
    ext x
    simp
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    have hab : a * b ∈ Ideal.comap f P := by
      rw [Ideal.mem_comap, map_mul]
      exact hxy
    rcases hP.mem_or_mem hab with ha | hb
    · left
      rw [← Ideal.map_comap_of_surjective f hf P]
      exact Ideal.mem_map_of_mem f ha
    · right
      rw [← Ideal.map_comap_of_surjective f hf P]
      exact Ideal.mem_map_of_mem f hb

/-- In a `KrullDimLE 0` ring, every prime is maximal (the ⟹ half of
`Ring.krullDimLE_zero_iff`). -/
theorem isMaximal_of_krullDimLE_zero {S : Type*} [CommRing S]
    [Ring.KrullDimLE 0 S] (P : Ideal S) [P.IsPrime] : P.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp inferInstance P inferInstance

/- ## Base equiv: localized module vs localized ring -/

/-- Canonical `S`-linear identification of the localized module `S_p` (module
side) with the localized ring (ring side), from uniqueness of localized
modules. -/
noncomputable def localizedModule_atPrime_self_equiv_base (p : Ideal S) [p.IsPrime] :
    LocalizedModule.AtPrime p S ≃ₗ[S] Localization.AtPrime p :=
  IsLocalizedModule.iso p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))

/-- The canonical identification is `S_p`-linear: both sides compute to
`mk' f (r • m) (s * t)` via `mk_smul_mk` / `mk'_smul_mk'`. -/
theorem localizedModule_atPrime_self_equiv_base_smul (p : Ideal S) [p.IsPrime]
    (c : Localization.AtPrime p) (z : LocalizedModule.AtPrime p S) :
    localizedModule_atPrime_self_equiv_base p (c • z)
      = c • localizedModule_atPrime_self_equiv_base p z := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl c
  refine LocalizedModule.induction_on (fun m t => ?_) z
  have e_mk : ∀ (m : S) (t : p.primeCompl),
      localizedModule_atPrime_self_equiv_base p (LocalizedModule.mk m t)
        = IsLocalizedModule.mk' (Algebra.linearMap S (Localization.AtPrime p)) m t :=
    fun m t => rfl
  have hsmul : ∀ w : LocalizedModule.AtPrime p S,
      (IsLocalization.mk' (Localization.AtPrime p) r s) • w
        = (Localization.mk r s) • w := by
    intro w
    rw [show IsLocalization.mk' (Localization.AtPrime p) r s = Localization.mk r s
      from (Localization.mk_eq_mk'_apply r s).symm]
  rw [hsmul]
  rw [LocalizedModule.mk_smul_mk, e_mk, e_mk]
  rw [IsLocalizedModule.mk'_smul_mk']

/-- Canonical `S_p`-linear identification of `LocalizedModule.AtPrime p S`
with `Localization.AtPrime p` (rebuild of the base equiv with the `S_p`
scalar law). Transports grade/regularity between the module- and ring-side. -/
noncomputable def localizedModule_atPrime_self_equiv (p : Ideal S) [p.IsPrime] :
    LocalizedModule.AtPrime p S ≃ₗ[Localization.AtPrime p] Localization.AtPrime p where
  toFun := localizedModule_atPrime_self_equiv_base p
  map_add' := (localizedModule_atPrime_self_equiv_base p).map_add'
  map_smul' := localizedModule_atPrime_self_equiv_base_smul p
  invFun := (localizedModule_atPrime_self_equiv_base p).invFun
  left_inv := (localizedModule_atPrime_self_equiv_base p).left_inv
  right_inv := (localizedModule_atPrime_self_equiv_base p).right_inv

/- ## C3a: localization of CM is CM -/

/-- C3a (conditional on `C3aGap`): localization of a CM local ring is CM.
`grade ≤ dim` is proved; `dim ≤ grade` runs the gap witness at
`n = height.toNat` through `GradeSet` and GHT. -/
theorem isCM_localization_atPrime [IsLocalRing S] [IsNoetherianRing S]
    (hCM : IsCM S) (p : Ideal S) [p.IsPrime]
    (hC3a_gap : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (p : Ideal S) [p.IsPrime], ringKrullDim S < ⊤ → IsCM S → C3aGap S p)
    (hfinS : ringKrullDim S < ⊤) :
    IsCM (Localization.AtPrime p) := by
  have hne : p.height ≠ ⊤ :=
    Ideal.height_ne_top (inferInstance : p.IsPrime).ne_top
  obtain ⟨rs, hreg, hmem, hlen⟩ :=
    hC3a_gap S p hfinS hCM p.height.toNat (ENat.natCast_toNat_le_self p.height)
  have hgrade : ((p.height.toNat : ℕ) : ℕ∞)
      ≤ GradeDepthFragment.grade _ _ (IsLocalRing.maximalIdeal _) :=
    GradeDepthFragment.le_grade_of_mem_gradeSet _
      (GradeDepthFragment.mem_gradeSet_of_isRegular _ rs hlen hmem hreg)
  have htn : ((p.height.toNat : ℕ) : ℕ∞) = p.height := ENat.natCast_toNat hne
  have hGHT : ringKrullDim (Localization.AtPrime p) = ((p.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  unfold IsCM
  apply le_antisymm
  · exact GradeDepthFragment.grade_le_ringKrullDim _
  · rw [hGHT, ← htn]
    exact WithBot.coe_le_coe.mpr hgrade

/- ## Unmixedness, part 1: associated primes live over `J'` and descend -/

/-- Associated primes of `R ⧸ J'` contain `J'` (which kills the quotient, hence
lies in every `colon ⊥ {x}` and its radical). -/
theorem le_of_mem_associatedPrimes_quotient (J' P : Ideal R)
    (hP : P ∈ associatedPrimes R (R ⧸ J')) : J' ≤ P := by
  rw [AssociatedPrimes.mem_iff] at hP
  obtain ⟨-, x, hx⟩ := hP
  rw [hx]
  intro r hr
  rw [Ideal.mem_radical_iff]
  refine ⟨1, ?_⟩
  rw [pow_one, Submodule.mem_colon_singleton, Submodule.mem_bot]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right a J' hr

/-- Associated primes of the `R`-module `R ⧸ J'` descend to associated primes
of the ring `R ⧸ J'`: colon and radical both commute with `mk J'`. -/
theorem mem_associatedPrimes_self_of_mem_associatedPrimes_quotient (J' P : Ideal R)
    (hP : P ∈ associatedPrimes R (R ⧸ J')) :
    Ideal.map (Ideal.Quotient.mk J') P ∈ associatedPrimes (R ⧸ J') (R ⧸ J') := by
  have hle : J' ≤ P := le_of_mem_associatedPrimes_quotient J' P hP
  rw [AssociatedPrimes.mem_iff] at hP ⊢
  obtain ⟨hprime, x, hx⟩ := hP
  have hcomap : Ideal.comap (Ideal.Quotient.mk J')
      (Ideal.map (Ideal.Quotient.mk J') P) = P :=
    comap_map_quotient_mk_eq_self J' P hle
  have hP' : (Ideal.comap (Ideal.Quotient.mk J')
      (Ideal.map (Ideal.Quotient.mk J') P)).IsPrime := hcomap.symm ▸ hprime
  refine ⟨isPrime_of_comap_isPrime_of_surjective _ Ideal.Quotient.mk_surjective _
    hP', x, ?_⟩
  have hcolon : Ideal.map (Ideal.Quotient.mk J')
        (Submodule.colon (⊥ : Submodule R (R ⧸ J')) {x})
      = Submodule.colon (⊥ : Submodule (R ⧸ J') (R ⧸ J')) {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, hcC, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hcC ⊢
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [smul_eq_mul, ← map_mul, ← Ideal.Quotient.mk_eq_mk]
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul] at hcC
      exact hcC
    · intro s hs
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hs
      apply Ideal.mem_map_of_mem
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [smul_eq_mul, ← map_mul, ← Ideal.Quotient.mk_eq_mk] at hs
      exact hs
  have hrad : ∀ C : Ideal R, J' ≤ C → Ideal.map (Ideal.Quotient.mk J') C.radical
      = (Ideal.map (Ideal.Quotient.mk J') C).radical := by
    intro C hC
    apply le_antisymm
    · intro y hy
      obtain ⟨c, hcC, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Ideal.mem_radical_iff] at hcC ⊢
      obtain ⟨n, hn⟩ := hcC
      exact ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    · intro y hy
      rw [Ideal.mem_radical_iff] at hy
      obtain ⟨n, hn⟩ := hy
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow] at hn
      have hmem : c ^ n ∈ Ideal.comap (Ideal.Quotient.mk J')
          (Ideal.map (Ideal.Quotient.mk J') C) :=
        Ideal.mem_comap.mpr hn
      rw [comap_map_quotient_mk_eq_self J' C hC] at hmem
      have hcrad : c ∈ C.radical := Ideal.mem_radical_iff.mpr ⟨n, hmem⟩
      exact Ideal.mem_map_of_mem _ hcrad
  have hJ'colon : J' ≤ Submodule.colon (⊥ : Submodule R (R ⧸ J')) {x} := by
    intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right a J' hr
  calc Ideal.map (Ideal.Quotient.mk J') P
      = Ideal.map (Ideal.Quotient.mk J')
          (Submodule.colon (⊥ : Submodule R (R ⧸ J')) {x}).radical := by rw [hx]
    _ = (Ideal.map (Ideal.Quotient.mk J')
          (Submodule.colon (⊥ : Submodule R (R ⧸ J')) {x})).radical :=
        hrad _ hJ'colon
    _ = (Submodule.colon (⊥ : Submodule (R ⧸ J') (R ⧸ J')) {x}).radical := by
        rw [hcolon]

/- ## Unmixedness, part 2: grade zero at associated localizations -/

/-- Grade of `S_p` is zero at `p ∈ Ass(S)`: `Ass` localizes (:70), grade at
`Ass` is zero (GradeDepthFragment:895), transported along the module/ring
identification. -/
theorem grade_localization_atPrime_eq_zero_of_mem_associatedPrimes
    [IsLocalRing S] [IsNoetherianRing S] (p : Ideal S) [p.IsPrime]
    (hp : p ∈ associatedPrimes S S) :
    GradeDepthFragment.grade (Localization.AtPrime p) (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) = 0 := by
  have hA :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  have h0 := GradeDepthFragment.grade_eq_zero_of_mem_associatedPrimes hA
  have hGradeSet : GradeDepthFragment.GradeSet (Localization.AtPrime p)
        (LocalizedModule.AtPrime p S)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      = GradeDepthFragment.GradeSet (Localization.AtPrime p) (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem,
        ((localizedModule_atPrime_self_equiv p).isRegular_congr rs).mp hreg⟩
    · rintro ⟨rs, hlen, hmem, hreg⟩
      exact ⟨rs, hlen, hmem,
        ((localizedModule_atPrime_self_equiv p).isRegular_congr rs).mpr hreg⟩
  have hgrade_eq : GradeDepthFragment.grade (Localization.AtPrime p)
        (LocalizedModule.AtPrime p S)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      = GradeDepthFragment.grade (Localization.AtPrime p) (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
    unfold GradeDepthFragment.grade
    rw [hGradeSet]
  rw [hgrade_eq] at h0
  exact h0

/-- Core unmixedness: in a CM local ring, associated primes are minimal
(C3a + grade zero forces `dim S_p = 0`, so nothing lies strictly below `p`). -/
theorem mem_minimalPrimes_bot_of_mem_associatedPrimes_of_isCM
    [IsLocalRing S] [IsNoetherianRing S] (hCM : IsCM S)
    (p : Ideal S) [p.IsPrime] (hp : p ∈ associatedPrimes S S)
    (hC3a_gap : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (p : Ideal S) [p.IsPrime], ringKrullDim S < ⊤ → IsCM S → C3aGap S p)
    (hfinS : ringKrullDim S < ⊤) :
    p ∈ (⊥ : Ideal S).minimalPrimes := by
  have hCMp : IsCM (Localization.AtPrime p) :=
    isCM_localization_atPrime hCM p hC3a_gap hfinS
  have h0 := grade_localization_atPrime_eq_zero_of_mem_associatedPrimes p hp
  have hdim : ringKrullDim (Localization.AtPrime p) = 0 := by
    have h := hCMp
    unfold IsCM at h
    rw [h0] at h
    simpa using h.symm
  have hLE : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim, Nat.cast_zero])
  change (⊥ : Ideal S).IsMinimalPrime p
  refine ⟨⟨inferInstance, bot_le⟩, fun q hq hle => ?_⟩
  obtain ⟨hqprime, -⟩ := hq
  have hdisj : Disjoint (p.primeCompl : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    intro a ha hqa
    exact ha (hle hqa)
  have hqSprime : (Ideal.map (algebraMap S (Localization.AtPrime p)) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ q hqprime hdisj
  have _hqSprimeI := hqSprime
  have _hLEI := hLE
  have hqSmax : (Ideal.map (algebraMap S (Localization.AtPrime p)) q).IsMaximal :=
    isMaximal_of_krullDimLE_zero _
  have hqSeq : Ideal.map (algebraMap S (Localization.AtPrime p)) q
      = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalRing.eq_maximalIdeal hqSmax
  have hcomap : Ideal.comap (algebraMap S (Localization.AtPrime p))
      (Ideal.map (algebraMap S (Localization.AtPrime p)) q) = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ hqprime hdisj
  have hcomapM : Ideal.comap (algebraMap S (Localization.AtPrime p))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) = p :=
    Localization.AtPrime.under_maximalIdeal
  have hqp : q = p :=
    calc q = Ideal.comap (algebraMap S (Localization.AtPrime p))
            (Ideal.map (algebraMap S (Localization.AtPrime p)) q) := hcomap.symm
      _ = Ideal.comap (algebraMap S (Localization.AtPrime p))
            (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by rw [hqSeq]
      _ = p := hcomapM
  exact hqp.symm.le

/- ## Unmixedness, part 3: pullback and the `mk₀` close -/

/-- Minimality over `⊥` pulls back to minimality over `J'` along `mk J'`. -/
theorem mem_minimalPrimes_of_map_mem_minimalPrimes_bot (J' P : Ideal R)
    (hle : J' ≤ P)
    (hPmap : Ideal.map (Ideal.Quotient.mk J') P ∈ (⊥ : Ideal (R ⧸ J')).minimalPrimes) :
    P ∈ J'.minimalPrimes := by
  change (⊥ : Ideal (R ⧸ J')).IsMinimalPrime _ at hPmap
  have hmapprime : (Ideal.map (Ideal.Quotient.mk J') P).IsPrime := hPmap.isPrime
  have hPcomap : Ideal.comap (Ideal.Quotient.mk J')
      (Ideal.map (Ideal.Quotient.mk J') P) = P :=
    comap_map_quotient_mk_eq_self J' P hle
  have hPprime : P.IsPrime := by
    rw [← hPcomap]
    exact Ideal.IsPrime.comap (f := Ideal.Quotient.mk J')
      (K := Ideal.map (Ideal.Quotient.mk J') P) (hK := hmapprime)
  change J'.IsMinimalPrime P
  refine ⟨⟨hPprime, hle⟩, fun Q hQ hQP => ?_⟩
  obtain ⟨hQprime, hQle⟩ := hQ
  have hQcomap : Ideal.comap (Ideal.Quotient.mk J')
      (Ideal.map (Ideal.Quotient.mk J') Q) = Q :=
    comap_map_quotient_mk_eq_self J' Q hQle
  have hQmapprime : (Ideal.map (Ideal.Quotient.mk J') Q).IsPrime :=
    isPrime_of_comap_isPrime_of_surjective _ Ideal.Quotient.mk_surjective _
      (hQcomap.symm ▸ hQprime)
  have hle_map : Ideal.map (Ideal.Quotient.mk J') P
      ≤ Ideal.map (Ideal.Quotient.mk J') Q := by
    have heq : Ideal.map (Ideal.Quotient.mk J') Q
        = Ideal.map (Ideal.Quotient.mk J') P :=
      Minimal.eq_of_le hPmap ⟨hQmapprime, bot_le⟩ (Ideal.map_mono hQP)
    exact heq.symm.le
  calc P = Ideal.comap (Ideal.Quotient.mk J')
          (Ideal.map (Ideal.Quotient.mk J') P) := hPcomap.symm
    _ ≤ Ideal.comap (Ideal.Quotient.mk J')
          (Ideal.map (Ideal.Quotient.mk J') Q) := Ideal.comap_mono hle_map
    _ = Q := hQcomap

/-- Unmixedness of CM quotients: every `P ∈ Ass(R ⧸ J')` is minimal over `J'`. -/
theorem isHunmixed_quotient_of_isCM [IsLocalRing R] [IsNoetherianRing R]
    (J' : Ideal R) [IsLocalRing (R ⧸ J')] (hCM : IsCM (R ⧸ J'))
    (hC3a_gap : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (p : Ideal S) [p.IsPrime], ringKrullDim S < ⊤ → IsCM S → C3aGap S p)
    (hfinR : ringKrullDim R < ⊤) :
    EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.IsHunmixed R J' := by
  intro P hP
  have hle : J' ≤ P := le_of_mem_associatedPrimes_quotient J' P hP
  have hpass : Ideal.map (Ideal.Quotient.mk J') P
      ∈ associatedPrimes (R ⧸ J') (R ⧸ J') :=
    mem_associatedPrimes_self_of_mem_associatedPrimes_quotient J' P hP
  have _iS := (AssociatedPrimes.mem_iff.mp hpass).isPrime
  have hfinQ : ringKrullDim (R ⧸ J') < ⊤ :=
    lt_of_le_of_lt (ringKrullDim_quotient_le _) hfinR
  have hmin : Ideal.map (Ideal.Quotient.mk J') P ∈ (⊥ : Ideal (R ⧸ J')).minimalPrimes :=
    mem_minimalPrimes_bot_of_mem_associatedPrimes_of_isCM hCM _ hpass hC3a_gap hfinQ
  exact mem_minimalPrimes_of_map_mem_minimalPrimes_bot J' P hle hmin

/-- C3 close: a CM quotient of positive dimension has `𝔪 ∉ Ass`. If `𝔪 ∈ Ass`,
unmixedness puts it in `minimalPrimes`, forcing every prime maximal, hence
`KrullDimLE 0` — against `hpos`. -/
theorem maximalIdeal_notMem_associatedPrimes_of_cm_quotient
    [IsLocalRing R] [IsNoetherianRing R] (J' : Ideal R) [IsLocalRing (R ⧸ J')]
    (hCM : IsCM (R ⧸ J')) (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hC3a_gap : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (p : Ideal S) [p.IsPrime], ringKrullDim S < ⊤ → IsCM S → C3aGap S p)
    (hfinR : ringKrullDim R < ⊤) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J') := by
  intro hmem
  have hunmixed := isHunmixed_quotient_of_isCM J' hCM hC3a_gap hfinR
  have hmin : IsLocalRing.maximalIdeal R ∈ J'.minimalPrimes := hunmixed _ hmem
  have hmin' : J'.IsMinimalPrime (IsLocalRing.maximalIdeal R) := hmin
  have hLE0 : Ring.KrullDimLE 0 (R ⧸ J') := by
    apply Ring.KrullDimLE.mk₀
    intro Q hQprime
    have hQcomap : (Ideal.comap (Ideal.Quotient.mk J') Q).IsPrime :=
      Ideal.IsPrime.comap (f := Ideal.Quotient.mk J') (K := Q) (hK := hQprime)
    have _iQ := hQcomap
    have hJQ : J' ≤ Ideal.comap (Ideal.Quotient.mk J') Q := by
      intro x hx
      rw [Ideal.mem_comap]
      have h0 : Ideal.Quotient.mk J' x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [h0]
      exact Q.zero_mem
    obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le hJQ
    have hqmin' : J'.IsMinimalPrime q := hqmin
    have hqm : q ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hqmin'.isPrime.ne_top
    have hqeq : q = IsLocalRing.maximalIdeal R :=
      Minimal.eq_of_le hmin' ⟨hqmin'.isPrime, hqmin'.le⟩ hqm
    have hcomap_le : Ideal.comap (Ideal.Quotient.mk J') Q
        ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hQcomap.ne_top
    have hcomap_eq : Ideal.comap (Ideal.Quotient.mk J') Q
        = IsLocalRing.maximalIdeal R := by
      apply le_antisymm hcomap_le
      rw [← hqeq]
      exact hqle
    have hQeq : Ideal.map (Ideal.Quotient.mk J')
        (Ideal.comap (Ideal.Quotient.mk J') Q) = Q :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q
    have hmax : (Ideal.comap (Ideal.Quotient.mk J') Q).IsMaximal := by
      rw [hcomap_eq]
      exact inferInstance
    have hor := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective hmax
    rw [hQeq] at hor
    exact hor.resolve_left hQprime.ne_top
  exact hpos hLE0

/- ## F7: C2 iteration along a regular sequence (names the C2 dependency).

`isCM_quotient_span_of_isRegular` iterates the C2 single-element step
(`hC2quot`) along a maximal-ideal regular sequence via the mathlib
double-quotient iso, bridging `QuotSMulTop`-regularity to `span`-quotient
regularity and `span`-of-list to `map`-of-`span`. It binds all three C2
conclusions (`hC2loc`, `hC2comp`, `hC2quot`) with the exact design note-§2 shapes,
so C2 substitution stays mechanical. Lists are tracked as the
`DecidableEq`-free membership set `{x | x ∈ ls}` (`List.toFinset` needs
`DecidableEq`, unavailable for general quotients). -/

open scoped Pointwise in
/-- `x • ⊤ = span {x}`: bridge from the `QuotSMulTop`/smul quotient shape
to `Ideal.span`. -/
theorem smul_top_eq_span_singleton {S : Type u} [CommRing S] (x : S) :
    (x • (⊤ : Submodule S S) : Submodule S S)
      = Submodule.span S {x} := by
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨b, -, hbx⟩ := hy
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    have hcomm : b • x = x • b := by rw [smul_eq_mul, smul_eq_mul, mul_comm]
    exact hcomm.trans hbx
  · intro hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, hax⟩ := hy
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨a, Submodule.mem_top, ?_⟩
    have hcomm : x • a = a • x := by rw [smul_eq_mul, smul_eq_mul, mul_comm]
    exact hcomm.trans hax

/-- The list-membership set of a cons is an insert. -/
theorem memSet_cons {S : Type u} (a : S) (l : List S) :
    {x | x ∈ a :: l} = insert a {x | x ∈ l} := by
  ext x
  rw [Set.mem_insert_iff]
  change (x ∈ a :: l) ↔ (x = a ∨ x ∈ l)
  rw [List.mem_cons]

/-- The list-membership set of `[]` is empty. -/
theorem memSet_nil {S : Type u} : {x : S | x ∈ ([] : List S)} = ∅ := by
  ext x
  change (x ∈ ([] : List S)) ↔ x ∈ (∅ : Set S)
  rw [iff_false_intro List.not_mem_nil, Set.mem_empty_iff_false x]

/-- The list-membership set of a mapped list is the image
(`DecidableEq`-free; `Multiset.toFinset_map` needs `DecidableEq`). -/
theorem memSet_map {A B : Type u} (f : A → B) (l : List A) :
    {y | y ∈ l.map f} = f '' {x | x ∈ l} := by
  ext y
  change (y ∈ l.map f) ↔ y ∈ f '' {x | x ∈ l}
  rw [List.mem_map, Set.mem_image]
  exact Iff.rfl

/-- `span` commutes with `map` along a ring hom (image form; manual so no
`RingHomSurjective` instance is needed). -/
theorem map_span_image {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (s : Set A) :
    Ideal.map f (Ideal.span s) = Ideal.span (f '' s) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span ⟨x, hx, rfl⟩
  · rw [Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    exact Ideal.mem_map_of_mem f (Ideal.subset_span hx)

/-- Regularity descends from `QuotSMulTop` to the `span`-quotient ring, in
the mapped-list form matching `isRegular_cons_iff'`. The quotient
identification is taken as explicit hypotheses (`eₗ`, `hmk`) so no
definitional unfolding is needed here. -/
theorem isRegular_spanQuotient_of_isRegular_quotSMulTop {S : Type u}
    [CommRing S] (a : S) (l : List S)
    (eₗ : QuotSMulTop a S ≃ₗ[S] (S ⧸ Ideal.span {a}))
    (hmk : ∀ s, eₗ.toAddEquiv (Submodule.Quotient.mk s)
      = Submodule.Quotient.mk s)
    (hreg : IsRegular (QuotSMulTop a S) l) :
    IsRegular (S ⧸ Ideal.span {a})
      (l.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
  have h2 : List.Forall₂
      (fun (r : S) (s : S ⧸ Ideal.span {a}) =>
        ∀ x, eₗ.toAddEquiv (r • x) = s • eₗ.toAddEquiv x)
      l (l.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro r _ x
    refine Submodule.Quotient.induction_on _ x ?_
    intro s
    have hL : eₗ.toAddEquiv (r • Submodule.Quotient.mk s)
        = Ideal.Quotient.mk (Ideal.span {a}) (r * s) := by
      rw [← Submodule.Quotient.mk_smul, hmk, Ideal.Quotient.mk_eq_mk,
        smul_eq_mul]
    have hR : (Ideal.Quotient.mk (Ideal.span {a}) r) • eₗ.toAddEquiv
          (Submodule.Quotient.mk s)
        = Ideal.Quotient.mk (Ideal.span {a}) (r * s) := by
      rw [hmk, Ideal.Quotient.mk_eq_mk, smul_eq_mul, map_mul]
    rw [hL, hR]
  exact (eₗ.toAddEquiv.isRegular_congr h2).mp hreg

/-- `IsCM` transports across a ring equivalence preserving the maximal
ideal (forward direction of the C2-application transport). -/
theorem isCM_ringEquiv_congr {A B : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B)
    (hmap : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A)
      = IsLocalRing.maximalIdeal B)
    (hCM : IsCM A) : IsCM B := by
  have hmaxB : (IsLocalRing.maximalIdeal B).IsMaximal := inferInstance
  have hne : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap]
    exact hmaxB.ne_top
  have hcc : (Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A)).comap
        e.toRingHom
      = IsLocalRing.maximalIdeal A :=
    Ideal.comap_map_eq_self_of_isMaximal e.toRingHom hne
  have hGradeSet : GradeDepthFragment.GradeSet B B (IsLocalRing.maximalIdeal B)
      = GradeDepthFragment.GradeSet A A (IsLocalRing.maximalIdeal A) := by
    ext n
    constructor
    · rintro ⟨rs, hlen, hmem, hreg⟩
      refine ⟨rs.map ⇑e.symm, by rw [List.length_map]; exact hlen, ?_, ?_⟩
      · intro a ha
        rw [List.mem_map] at ha
        obtain ⟨r, hr, rfl⟩ := ha
        rw [← hcc, Ideal.mem_comap]
        change ⇑e (⇑e.symm r) ∈ Ideal.map e.toRingHom
          (IsLocalRing.maximalIdeal A)
        rw [e.apply_symm_apply, hmap]
        exact hmem r hr
      · have h2 : List.Forall₂
            (fun (b : B) (a : A) => ∀ x,
              e.symm.toAddEquiv (b • x) = a • e.symm.toAddEquiv x)
            rs (rs.map ⇑e.symm) := by
          rw [List.forall₂_map_right_iff, List.forall₂_same]
          intro b _ x
          change ⇑e.symm (b • x) = (⇑e.symm b) • ⇑e.symm x
          rw [smul_eq_mul, smul_eq_mul, map_mul]
        exact (e.symm.toAddEquiv.isRegular_congr h2).mp hreg
    · rintro ⟨rs, hlen, hmem, hreg⟩
      refine ⟨rs.map ⇑e, by rw [List.length_map]; exact hlen, ?_, ?_⟩
      · intro b hb
        rw [List.mem_map] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        rw [← hmap]
        exact Ideal.mem_map_of_mem e.toRingHom (hmem a ha)
      · have h2 : List.Forall₂
            (fun (a : A) (b : B) => ∀ x,
              e.toAddEquiv (a • x) = b • e.toAddEquiv x)
            rs (rs.map ⇑e) := by
          rw [List.forall₂_map_right_iff, List.forall₂_same]
          intro a _ x
          change ⇑e (a • x) = (⇑e a) • ⇑e x
          rw [smul_eq_mul, smul_eq_mul, map_mul]
        exact (e.toAddEquiv.isRegular_congr h2).mp hreg
  have hgrade : GradeDepthFragment.grade B B (IsLocalRing.maximalIdeal B)
      = GradeDepthFragment.grade A A (IsLocalRing.maximalIdeal A) := by
    unfold GradeDepthFragment.grade
    rw [hGradeSet]
  have hdim : ringKrullDim B = ringKrullDim A :=
    ringKrullDim_eq_of_ringEquiv e.symm
  unfold IsCM at hCM ⊢
  rw [hgrade, hdim]
  exact hCM

/-- The double-quotient iso preserves maximal ideals, via three `hC2comp`
(F5) identifications. -/
theorem map_quotQuotEquiv_maximal {A : Type u} [CommRing A] [IsLocalRing A]
    (I J : Ideal A) [IsLocalRing (A ⧸ I)]
    [IsLocalRing ((A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J)]
    [IsLocalRing (A ⧸ I ⊔ J)]
    (hC2comp : ∀ {R : Type u} [CommRing R] [IsLocalRing R] (J' : Ideal R)
      (_hle : J' ≤ IsLocalRing.maximalIdeal R) [IsLocalRing (R ⧸ J')],
      IsLocalRing.maximalIdeal (R ⧸ J')
        = Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R))
    (hIle : I ≤ IsLocalRing.maximalIdeal A)
    (hJle : Ideal.map (Ideal.Quotient.mk I) J
      ≤ IsLocalRing.maximalIdeal (A ⧸ I))
    (hsuple : I ⊔ J ≤ IsLocalRing.maximalIdeal A) :
    Ideal.map (DoubleQuot.quotQuotEquivQuotSup I J).toRingHom
        (IsLocalRing.maximalIdeal
          ((A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J))
      = IsLocalRing.maximalIdeal (A ⧸ I ⊔ J) := by
  rw [hC2comp _ hJle, hC2comp _ hIle, Ideal.map_map, Ideal.map_map,
    hC2comp _ hsuple]
  have hFG : ((DoubleQuot.quotQuotEquivQuotSup I J).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J))).comp
        (Ideal.Quotient.mk I)
      = Ideal.Quotient.mk (I ⊔ J) := by
    ext x
    change (DoubleQuot.quotQuotEquivQuotSup I J)
        (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)
          (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk (I ⊔ J) x
    exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J x
  rw [hFG]

/-- The symmetric double-quotient-style transport for `quotEquivOfEq`:
`map` along the symmetric iso sends the target maximal ideal back to the
source one. Used twice (nil case, cons `sup` bridge). -/
theorem map_quotEquivOfEq_symm_maximal {A : Type u} [CommRing A]
    [IsLocalRing A] (I J : Ideal A) [IsLocalRing (A ⧸ I)]
    [IsLocalRing (A ⧸ J)] (h : I = J)
    (hC2comp : ∀ {R : Type u} [CommRing R] [IsLocalRing R] (J' : Ideal R)
      (_hle : J' ≤ IsLocalRing.maximalIdeal R) [IsLocalRing (R ⧸ J')],
      IsLocalRing.maximalIdeal (R ⧸ J')
        = Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R))
    (hleI : I ≤ IsLocalRing.maximalIdeal A)
    (hleJ : J ≤ IsLocalRing.maximalIdeal A) :
    Ideal.map (Ideal.quotEquivOfEq h).symm.toRingHom
        (IsLocalRing.maximalIdeal (A ⧸ J))
      = IsLocalRing.maximalIdeal (A ⧸ I) := by
  rw [hC2comp _ hleJ, hC2comp _ hleI, Ideal.map_map]
  have hFG : (Ideal.quotEquivOfEq h).symm.toRingHom.comp
        (Ideal.Quotient.mk J)
      = Ideal.Quotient.mk I := by
    ext x
    change (Ideal.quotEquivOfEq h).symm (Ideal.Quotient.mk J x)
      = Ideal.Quotient.mk I x
    have h1 := Ideal.quotEquivOfEq_mk h x
    rw [← h1, RingEquiv.symm_apply_apply]
  rw [hFG]

/-- F7 (C2 iteration): the quotient of a CM ring by the span of a
maximal-ideal regular sequence is CM. Strong induction on a length bound
(the IH fires at the single-element quotient `T ⧸ span{a}` with the mapped
list); the nil case transports across `quotientBot`, the cons case across
the double-quotient iso. Binds `hC2loc`/`hC2comp`/`hC2quot` with the exact
design note-§2 shapes. -/
theorem isCM_quotient_span_of_isRegular [IsLocalRing S] [IsNoetherianRing S]
    (rs : List S) (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S rs) (hCM : IsCM S)
    [IsLocalRing (S ⧸ Ideal.span {x | x ∈ rs})]
    (hC2loc : ∀ {R : Type u} [CommRing R] [IsLocalRing R] (J' : Ideal R),
      J' ≤ IsLocalRing.maximalIdeal R → IsLocalRing (R ⧸ J'))
    (hC2comp : ∀ {R : Type u} [CommRing R] [IsLocalRing R] (J' : Ideal R)
      (_hle : J' ≤ IsLocalRing.maximalIdeal R) [IsLocalRing (R ⧸ J')],
      IsLocalRing.maximalIdeal (R ⧸ J')
        = Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R))
    (hC2quot : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] (_hCM : IsCM R) {x : R}
      (_hx : x ∈ IsLocalRing.maximalIdeal R) (_hreg : IsSMulRegular R x)
      [IsLocalRing (R ⧸ Ideal.span {x})],
      IsCM (R ⧸ Ideal.span {x})) :
    IsCM (S ⧸ Ideal.span {x | x ∈ rs}) := by
  have hnil : ∀ (T : Type u) [CommRing T] [IsLocalRing T]
      [IsNoetherianRing T]
      [IsLocalRing (T ⧸ Ideal.span {x | x ∈ ([] : List T)})],
      IsCM T → IsCM (T ⧸ Ideal.span {x | x ∈ ([] : List T)}) := by
    intro T _ _ _ _ hCMnil
    have hspan : Ideal.span {x : T | x ∈ ([] : List T)} = ⊥ := by
      rw [memSet_nil, Ideal.span_empty]
    have hlocBot : IsLocalRing (T ⧸ (⊥ : Ideal T)) := hC2loc ⊥ bot_le
    have hleNil : Ideal.span {x : T | x ∈ ([] : List T)}
        ≤ IsLocalRing.maximalIdeal T := by
      rw [Ideal.span_le]
      intro x hx
      exact absurd hx List.not_mem_nil
    have hmapQ : Ideal.map (RingEquiv.quotientBot T).symm.toRingHom
          (IsLocalRing.maximalIdeal T)
        = IsLocalRing.maximalIdeal (T ⧸ (⊥ : Ideal T)) := by
      rw [hC2comp _ bot_le]
      have hFG : (RingEquiv.quotientBot T).symm.toRingHom
          = Ideal.Quotient.mk ⊥ := by
        ext x
        change (RingEquiv.quotientBot T).symm x = Ideal.Quotient.mk ⊥ x
        apply (RingEquiv.quotientBot T).injective
        rw [(RingEquiv.quotientBot T).apply_symm_apply,
          RingEquiv.quotientBot_mk]
      rw [hFG]
    have hCMbot : IsCM (T ⧸ (⊥ : Ideal T)) :=
      isCM_ringEquiv_congr (RingEquiv.quotientBot T).symm hmapQ hCMnil
    have hmapBot' : Ideal.map (Ideal.quotEquivOfEq hspan).symm.toRingHom
          (IsLocalRing.maximalIdeal (T ⧸ (⊥ : Ideal T)))
        = IsLocalRing.maximalIdeal
          (T ⧸ Ideal.span {x | x ∈ ([] : List T)}) :=
      map_quotEquivOfEq_symm_maximal _ _ hspan hC2comp hleNil bot_le
    exact isCM_ringEquiv_congr (Ideal.quotEquivOfEq hspan).symm hmapBot'
      hCMbot
  suffices haux : ∀ (n : ℕ) (T : Type u) [CommRing T] [IsLocalRing T]
      [IsNoetherianRing T] (ls : List T)
      [IsLocalRing (T ⧸ Ideal.span {x | x ∈ ls})],
      ls.length ≤ n → (∀ r ∈ ls, r ∈ IsLocalRing.maximalIdeal T) →
      IsRegular T ls → IsCM T → IsCM (T ⧸ Ideal.span {x | x ∈ ls}) by
    exact haux rs.length S rs le_rfl hmem hreg hCM
  intro n
  induction n with
  | zero =>
      intro T _ _ _ ls hloc hlen hmem hreg hCM
      have hnil' : ls = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hnil'
      clear hlen hmem hreg
      exact hnil _ hCM
  | succ n ih =>
      intro T _ _ _ ls hloc hlen hmem hreg hCM
      cases ls with
      | nil =>
          clear hlen hmem hreg
          exact hnil _ hCM
      | cons a l =>
          rw [isRegular_cons_iff] at hreg
          obtain ⟨ha_reg, htail⟩ := hreg
          have ha_mem : a ∈ IsLocalRing.maximalIdeal T :=
            hmem a (List.mem_cons.mpr (Or.inl rfl))
          have hmem_tail : ∀ r ∈ l, r ∈ IsLocalRing.maximalIdeal T :=
            fun r hr => hmem r (List.mem_cons.mpr (Or.inr hr))
          have hspan_le : Ideal.span {a} ≤ IsLocalRing.maximalIdeal T := by
            rw [Ideal.span_le]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact ha_mem
          have hloc1 : IsLocalRing (T ⧸ Ideal.span {a}) :=
            hC2loc _ hspan_le
          have hCM1 : IsCM (T ⧸ Ideal.span {a}) :=
            hC2quot hCM ha_mem ha_reg
          have hmem1 : ∀ s ∈ l.map (Ideal.Quotient.mk (Ideal.span {a})),
              s ∈ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {a}) := by
            intro s hs
            rw [List.mem_map] at hs
            obtain ⟨r, hr, rfl⟩ := hs
            rw [hC2comp _ hspan_le]
            exact Ideal.mem_map_of_mem _ (hmem_tail r hr)
          have hreg1 : IsRegular (T ⧸ Ideal.span {a})
              (l.map (Ideal.Quotient.mk (Ideal.span {a}))) :=
            isRegular_spanQuotient_of_isRegular_quotSMulTop a l
              (Submodule.quotEquivOfEq _ _ (smul_top_eq_span_singleton a))
              (fun s => Submodule.quotEquivOfEq_mk _ _
                (smul_top_eq_span_singleton a) s) htail
          have hlen1 : (l.map (Ideal.Quotient.mk (Ideal.span {a}))).length
              ≤ n := by
            rw [List.length_map]
            rw [List.length_cons] at hlen
            exact Nat.le_of_succ_le_succ hlen
          have hle_l : Ideal.span {x : T | x ∈ l}
              ≤ IsLocalRing.maximalIdeal T := by
            rw [Ideal.span_le]
            intro y hy
            exact hmem_tail y hy
          have hle_cons : Ideal.span {x : T | x ∈ a :: l}
              ≤ IsLocalRing.maximalIdeal T := by
            rw [Ideal.span_le]
            intro y hy
            exact hmem y hy
          have hle_sup : Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l}
              ≤ IsLocalRing.maximalIdeal T :=
            sup_le hspan_le hle_l
          have hspancons : Ideal.span {x : T | x ∈ a :: l}
              = Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l} := by
            rw [memSet_cons, Ideal.span_insert]
          have hspanmap : Ideal.span {x : T ⧸ Ideal.span {a} | x ∈ l.map
                (Ideal.Quotient.mk (Ideal.span {a}))}
              = Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                (Ideal.span {x : T | x ∈ l}) := by
            rw [memSet_map, map_span_image]
          have hle_mapL : Ideal.span {x : T ⧸ Ideal.span {a} | x ∈ l.map
                (Ideal.Quotient.mk (Ideal.span {a}))}
              ≤ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {a}) := by
            rw [Ideal.span_le]
            intro s hs
            exact hmem1 s hs
          have hle_mapR : Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                (Ideal.span {x : T | x ∈ l})
              ≤ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {a}) := by
            rw [hC2comp _ hspan_le]
            exact Ideal.map_mono hle_l
          have hloc1span : IsLocalRing ((T ⧸ Ideal.span {a})
              ⧸ Ideal.span {x | x ∈ l.map
                (Ideal.Quotient.mk (Ideal.span {a}))}) :=
            hC2loc _ hle_mapL
          have hloc1map : IsLocalRing ((T ⧸ Ideal.span {a})
              ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                (Ideal.span {x : T | x ∈ l})) :=
            hC2loc _ hle_mapR
          have hlocSup : IsLocalRing
              (T ⧸ (Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l})) :=
            hC2loc _ hle_sup
          have hCM1span : IsCM ((T ⧸ Ideal.span {a})
              ⧸ Ideal.span {x | x ∈ l.map
                (Ideal.Quotient.mk (Ideal.span {a}))}) :=
            ih _ _ hlen1 hmem1 hreg1 hCM1
          have hmapMap : Ideal.map (Ideal.quotEquivOfEq hspanmap).toRingHom
              (IsLocalRing.maximalIdeal ((T ⧸ Ideal.span {a})
                ⧸ Ideal.span {x | x ∈ l.map
                  (Ideal.Quotient.mk (Ideal.span {a}))}))
              = IsLocalRing.maximalIdeal ((T ⧸ Ideal.span {a})
                ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                  (Ideal.span {x : T | x ∈ l})) := by
            rw [hC2comp _ hle_mapL, hC2comp _ hle_mapR, Ideal.map_map]
            have hFG : (Ideal.quotEquivOfEq hspanmap).toRingHom.comp
                  (Ideal.Quotient.mk (Ideal.span {x : T ⧸ Ideal.span {a} |
                    x ∈ l.map (Ideal.Quotient.mk (Ideal.span {a}))}))
                = Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk
                  (Ideal.span {a})) (Ideal.span {x : T | x ∈ l})) := by
              ext x
              change (Ideal.quotEquivOfEq hspanmap)
                  (Ideal.Quotient.mk (Ideal.span {x : T ⧸ Ideal.span {a} |
                    x ∈ l.map (Ideal.Quotient.mk (Ideal.span {a}))}) x)
                = Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk
                    (Ideal.span {a})) (Ideal.span {x : T | x ∈ l})) x
              exact Ideal.quotEquivOfEq_mk hspanmap x
            rw [hFG]
          have hCMmap : IsCM ((T ⧸ Ideal.span {a})
              ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                (Ideal.span {x : T | x ∈ l})) :=
            isCM_ringEquiv_congr (Ideal.quotEquivOfEq hspanmap) hmapMap
              hCM1span
          have hmapDQ : Ideal.map (DoubleQuot.quotQuotEquivQuotSup
                (Ideal.span {a}) (Ideal.span {x : T | x ∈ l})).toRingHom
              (IsLocalRing.maximalIdeal ((T ⧸ Ideal.span {a})
                ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
                  (Ideal.span {x : T | x ∈ l})))
              = IsLocalRing.maximalIdeal
                (T ⧸ (Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l})) :=
            map_quotQuotEquiv_maximal _ _ hC2comp hspan_le hle_mapR hle_sup
          have hCMsup : IsCM
              (T ⧸ (Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l})) :=
            isCM_ringEquiv_congr
              (DoubleQuot.quotQuotEquivQuotSup _ _) hmapDQ hCMmap
          have hmapSup' : Ideal.map
              (Ideal.quotEquivOfEq hspancons).symm.toRingHom
              (IsLocalRing.maximalIdeal
                (T ⧸ (Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l})))
              = IsLocalRing.maximalIdeal
                (T ⧸ Ideal.span {x : T | x ∈ a :: l}) :=
            map_quotEquivOfEq_symm_maximal _ _ hspancons hC2comp hle_cons
              hle_sup
          exact isCM_ringEquiv_congr (Ideal.quotEquivOfEq hspancons).symm
            hmapSup' hCMsup

#print axioms smul_top_eq_span_singleton
#print axioms memSet_cons
#print axioms memSet_nil
#print axioms memSet_map
#print axioms map_span_image
#print axioms isRegular_spanQuotient_of_isRegular_quotSMulTop
#print axioms isCM_ringEquiv_congr
#print axioms map_quotQuotEquiv_maximal
#print axioms map_quotEquivOfEq_symm_maximal
#print axioms isCM_quotient_span_of_isRegular
#print axioms maximalIdeal_notMem_associatedPrimes_of_cm_quotient

end C2Interface

end EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMPositiveDimHasDepth

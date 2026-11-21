/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-!
# Unramifiedness in intermediate fields

This file isolates the tower argument used in the proof of ATLAS
`NumberTheoryI` target N390, Proposition 19.14. The primary source is
[`v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, especially
`isUnramifiedAtPrime_of_le`, lines 1433--1460](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1433-L1460),
which proves the same descent for intermediate fields of a
cyclotomic field and the prime ideal `(p)`. It is used in the maximality argument
at the end of `proposition_19_14`.

The source predicate `IsUnramifiedAtPrime F p` says that every prime of `𝓞 F`
above `(p)` has ramification index one. Here it is represented by
`Algebra.IsUnramifiedIn (𝓞 F) 𝔭`; we generalize from the cyclotomic ambient field
and `(p)` to an arbitrary number field `L` and ideal `𝔭` of `ℤ`. For `E ≤ F`,
going up supplies a prime `Q` of `𝓞 F` above a given prime `P` of `𝓞 E`.
Transitivity puts `Q` above `𝔭`, and `Algebra.IsUnramifiedAt.of_liesOver`
descends unramifiedness from `Q` to `P`, encoding the ramification-index tower
calculation in the source proof.

The second theorem is a reusable bridge for the compositum step
[`isUnramifiedAtPrime_sup`, lines 1588--1625](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1588-L1625),
in that same primary source. The source proves that two
cyclotomic subfields unramified at `(p)` have unramified compositum, prime by
prime, using
[`baseChange_ramificationIdx_eq_one`, lines 1561--1586](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1561-L1586).
Here localization at the image
of `p.primeCompl` retains all primes above `p` simultaneously. Its primes
correspond to primes `q` of the integer ring whose contraction is at most `p`;
the nonzero contractions equal `p`, so `Algebra.IsUnramifiedIn` supplies formal
unramifiedness at every retained factor (the generic prime is automatic).
Flatness and finite presentation then upgrade this to semilocal étaleness.

This semilocal statement packages exactly the unramified local input needed for
N390's compositum/base-change argument. It does not by itself identify a
base-changed factor with the localization of the compositum's integer ring, nor
does it prove `isUnramifiedAtPrime_sup` or the maximality conclusion of
`proposition_19_14`.

The normalization equivalence below develops the same compositum/base-change
stage one level further. In the source, `baseChange_ramificationIdx_eq_one`
shows that a prime in `E ⊔ E'` over a prime of `E` has relative ramification
index one when `E'` is unramified, and `isUnramifiedAtPrime_sup` feeds that into
the ramification tower formula. Our alternative algebraic route localizes at
`(p)`, writes `R = ℤ_(p)` and the semilocal integer rings as `S_E` and `S_F`,
and uses the étaleness of `S_F/R` to commute normalization with base change:
`S_F ⊗[R] S_E` is the integral closure of `S_F` in
`S_F ⊗[R] Frac(𝓞 E)`. Thus `Algebra.IsUnramifiedIn (𝓞 F) p` is the source
assumption `IsUnramifiedAtPrime F p`, expressed for an arbitrary number field
and prime ideal.

This equivalence is not itself a theorem stated in `AnalyticClassNumber.lean`;
it is a replacement bridge toward its two cited compositum lemmas. Identifying
the appropriate normalized tensor factor with the localization of
`𝓞 (E ⊔ F)` is intentionally deferred, so no claim of compositum
unramifiedness or of Proposition 19.14's maximality is made here.

The final map in this file selects a prime `Q` of the compositum and maps the
normalized tensor algebra to `Localization.AtPrime Q`. In the source proof this
is the primewise stage where `baseChange_ramificationIdx_eq_one` fixes `Q` over
a prime of one intermediate field before `isUnramifiedAtPrime_sup` applies the
tower formula. `semilocalizationToAtPrime` sends each localized integer-ring
factor into that chosen local ring, and
`normalizedTensorToCompositumAtPrime` transports the resulting tensor map
through the normalization equivalence. Its prime kernel selects the generic
component, while the prime for the local ring is the contraction of the target
maximal ideal. The assertion that this localization is the compositum factor—and
hence an equivalence—is still deliberately absent.
-/

/-- Unramifiedness descends along intermediate fields: if `𝔭` is unramified in the
ring of integers of `F`, it is unramified in the ring of integers of any smaller
intermediate field `E ≤ F`.

This is the generic form of `isUnramifiedAtPrime_of_le` from the primary Lean
source for ATLAS `NumberTheoryI` target N390, Proposition 19.14. -/
theorem isUnramifiedIn_mono (E F : IntermediateField ℚ L) (hEF : E ≤ F)
    (𝔭 : Ideal ℤ) (hF : Algebra.IsUnramifiedIn (𝓞 F) 𝔭) :
    Algebra.IsUnramifiedIn (𝓞 E) 𝔭 := by
  let _alg : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  intro P hP hPE
  obtain ⟨Q, _, hQprime, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F) P ⊥
      (Ideal.comap_bot_le_of_injective _
        (NumberField.RingOfIntegers.algebraMap.injective E F))
  have hQP' : Q.LiesOver P := ⟨hQP.symm⟩
  have hQp : Q.LiesOver 𝔭 := ⟨by rw [hPE.over, hQP'.over, Ideal.under_under]⟩
  have hQ : Algebra.IsUnramifiedAt ℤ Q := hF Q hQprime hQp
  let _ : Q.IsPrime := hQprime
  let _ : Q.LiesOver P := hQP'
  let _ : Algebra.IsUnramifiedAt ℤ Q := hQ
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ P Q

/-- Semilocal étaleness above an unramified prime: localizing the whole finite
algebra `𝓞 K` at the prime-complement of `p` (inverting everything outside `p`,
keeping all local factors above `p` simultaneously) is étale over the local
base `Localization.AtPrime p`.

This packages the primewise unramified hypothesis used by
`isUnramifiedAtPrime_sup` in the primary Lean source for ATLAS `NumberTheoryI`
target N390, Proposition 19.14. It is the semilocal algebra, not a single local
factor `Localization.AtPrime Q`. -/
theorem IsUnramifiedIn.etale_localization {K : Type*} [Field K] [NumberField K]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 K) p) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)) := by
  let S_p := Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)
  have hFP : Algebra.FinitePresentation (Localization.AtPrime p) S_p :=
    (Algebra.FinitePresentation.of_finiteType (R := Localization.AtPrime p)
      (A := S_p)).mp inferInstance
  have hFU : Algebra.FormallyUnramified (Localization.AtPrime p) S_p := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro x
    let q := x.asIdeal.under (𝓞 K)
    have hqprime : q.IsPrime := inferInstance
    have hmem : (⟨q, hqprime⟩ : PrimeSpectrum (𝓞 K)) ∈ Set.range
        (PrimeSpectrum.comap (algebraMap (𝓞 K) S_p)) := by
      refine ⟨x, ?_⟩
      apply PrimeSpectrum.ext
      change (x.asIdeal.under (𝓞 K)) = _
      rfl
    rw [PrimeSpectrum.localization_comap_range
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl))
      (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)] at hmem
    have hle : q.under ℤ ≤ p := by
      apply Ideal.disjoint_map_primeCompl_iff_comap_le.mp
      exact Disjoint.symm hmem
    have hunram : Algebra.IsUnramifiedAt ℤ q := by
      by_cases hq0 : q = ⊥
      · simpa only [hq0] using
          (Algebra.isUnramifiedAt_bot (R := ℤ) (S := 𝓞 K))
      · have heq : p = q.under ℤ :=
          ((hqprime.under ℤ).isMaximal (q.under_ne_bot ℤ hq0) |>.eq_of_le
            (inferInstance : p.IsPrime).ne_top hle).symm
        have hlie : q.LiesOver p := ⟨heq⟩
        exact h q hqprime hlie
    let _ : Algebra.IsUnramifiedAt (𝓞 K) x.asIdeal :=
      Algebra.FormallyUnramified.of_isLocalization q.primeCompl
    let _ : Algebra.IsUnramifiedAt ℤ q := hunram
    have hlie2 : x.asIdeal.LiesOver q := ⟨rfl⟩
    let _ : x.asIdeal.LiesOver q := hlie2
    have hbase : Algebra.IsUnramifiedAt ℤ x.asIdeal :=
      Algebra.IsUnramifiedAt.comp q x.asIdeal
    let _ : Algebra.IsUnramifiedAt ℤ x.asIdeal := hbase
    exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ x.asIdeal
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Global normalization base-change bridge above an unramified prime: for number
fields `E` and `F` and `p` unramified in `𝓞 F`, tensoring the semilocal
integral-closure identification of `E` with the semilocal ring of `F` identifies
`S_F ⊗[R] S_E` with the integral closure of `S_F` in the base-changed fraction
ring.

This is the normalization-under-étale-base-change route toward the compositum
step `baseChange_ramificationIdx_eq_one` and `isUnramifiedAtPrime_sup` in the
primary Lean source for ATLAS N390. The local-factor/compositum identification
needed to recover those source theorems is not claimed here. -/
noncomputable def IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure
    {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    TensorProduct R S_F S_E ≃ₐ[S_F]
      integralClosure S_F (TensorProduct R S_F (FractionRing (𝓞 E))) := by
  let R := Localization.AtPrime p
  let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
  let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
  let _ : Algebra.Etale R S_F := IsUnramifiedIn.etale_localization p h
  letI : Algebra S_E (FractionRing (𝓞 E)) :=
    Localization.AtPrime.liftAlgebra (𝓞 E)
  let e : S_E ≃ₐ[R] integralClosure R (FractionRing (𝓞 E)) :=
    IsIntegralClosure.equiv R S_E (FractionRing (𝓞 E)) _
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S_F ≃ₐ[S_F] S_F) e).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S_F
      (FractionRing (𝓞 E))) TensorProduct.toIntegralClosure_bijective_of_smooth)

end NumberField

namespace Localization

/-- Semilocal-to-local factor map: localize the semilocal ring away from `p`
further at the prime `Q` lying over `p`. -/
noncomputable def semilocalizationToAtPrime
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p] :
    Localization (Algebra.algebraMapSubmonoid S p.primeCompl) →ₐ[S]
      Localization.AtPrime Q :=
  IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := Q.primeCompl)
        (Localization.AtPrime Q) ⟨algebraMap R T x, by
          simp_all [Q.over_def p]
        ⟩)

/-- Characteristic equation for `semilocalizationToAtPrime` on a localization
representative. It avoids exposing the implementation's chosen inverse unit. -/
theorem semilocalizationToAtPrime_mk'_eq_iff
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p]
    (x : S) (y : Algebra.algebraMapSubmonoid S p.primeCompl)
    (z : Localization.AtPrime Q) :
    semilocalizationToAtPrime p Q
        (IsLocalization.mk'
          (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x y) = z ↔
      algebraMap S (Localization.AtPrime Q) x =
        algebraMap S (Localization.AtPrime Q) y * z := by
  rw [semilocalizationToAtPrime, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_mk'_spec]
  change algebraMap S (Localization.AtPrime Q) x =
      algebraMap S (Localization.AtPrime Q) y * z ↔ _
  rfl

end Localization

namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

namespace IsUnramifiedIn

/-- This maps the normalized tensor algebra to the local ring at `Q` and
selects the compositum component, but does NOT yet claim the induced
localization is an equivalence.

It is the normalized, prime-selected map corresponding to the fixed-`Q` stage
of `baseChange_ramificationIdx_eq_one` in the primary Lean source for ATLAS
N390. -/
noncomputable def normalizedTensorToCompositumAtPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let C := integralClosure S_F
      (TensorProduct R S_F (FractionRing (𝓞 E)))
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    C →ₐ[R] T := by
  let R := Localization.AtPrime p
  let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
  let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
  let M := (E ⊔ F : IntermediateField ℚ L)
  let _algE : Algebra E M := (IntermediateField.inclusion le_sup_left).toAlgebra
  let _algF : Algebra F M := (IntermediateField.inclusion le_sup_right).toAlgebra
  let T := Localization.AtPrime Q
  letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
  let fF : S_F →ₐ[𝓞 F] T := Localization.semilocalizationToAtPrime _ _
  let fE : S_E →ₐ[𝓞 E] T := Localization.semilocalizationToAtPrime _ _
  algebraize [fF.toRingHom, fE.toRingHom]
  letI : IsScalarTower R S_F T := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext z
    simp
  letI : IsScalarTower R S_E T := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext z
    simp
  let g : TensorProduct R S_F S_E →ₐ[R] T :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S_F T)
      (IsScalarTower.toAlgHom R S_E T) fun _ _ => .all _ _
  let e := tensorProductLocalizationEquivIntegralClosure
    (E := E) (F := F) p h
  exact g.comp (e.symm.restrictScalars R).toAlgHom

/-- Characteristic formula on normalized simple tensors: after transporting a
tensor generator through the normalization equivalence, the selected component
is the product of its two semilocal images. -/
theorem normalizedTensorToCompositumAtPrime_equiv_tmul
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p]
    (x : Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
    (y : Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    let M := (E ⊔ F : IntermediateField ℚ L)
    letI _algE : Algebra E M := (IntermediateField.inclusion le_sup_left).toAlgebra
    letI _algF : Algebra F M := (IntermediateField.inclusion le_sup_right).toAlgebra
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    let fF : S_F →ₐ[𝓞 F] T := Localization.semilocalizationToAtPrime p Q
    let fE : S_E →ₐ[𝓞 E] T := Localization.semilocalizationToAtPrime p Q
    let e := tensorProductLocalizationEquivIntegralClosure (E := E) (F := F) p h
    normalizedTensorToCompositumAtPrime E F p h Q (e (x ⊗ₜ[R] y)) =
      fF x * fE y := by
  dsimp
  simp [normalizedTensorToCompositumAtPrime]
  congr 1

/-- The kernel of the compositum-component map is prime because the target
localization at `Q` is a domain. The kernel selects the generic component,
while the prime for the local ring is the contraction of the target maximal
ideal. No localization equivalence or maximality is claimed. -/
theorem normalizedTensorToCompositumAtPrime_ker_isPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    (RingHom.ker (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom).IsPrime := by
  dsimp
  exact RingHom.ker_isPrime _

/-- Contracted maximal prime: the correct prime of the normalized tensor algebra
at which to localize to obtain the local factor `Localization.AtPrime Q`.

Let `g := normalizedTensorToCompositumAtPrime E F p h Q` and
`T := Localization.AtPrime Q`. This is the comap of the maximal ideal of the
local ring `T` under `g`. It contains the prime kernel of `g` (see
`normalizedTensorToCompositumAtPrime_ker_le`), but it is in general strictly
larger: for a nonzero prime below `Q`, a nonzero uniformizer lies outside
`RingHom.ker g` yet maps to a nonunit of `T`.

This is a named alternative-normalization prerequisite stage for the missing
`cyclotomic_ramIdx_eq_of_unramified` and
[`baseChange_ramificationIdx_eq_one`, lines 1549--1586](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1549-L1586)
in the primary Lean source for ATLAS `NumberTheoryI` target N390,
Proposition 19.14. It does not prove
compositum unramifiedness, any `IsLocalization` identification, or the final
maximality theorem. -/
noncomputable def normalizedTensorCompositumPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    Ideal (integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :=
  let T := Localization.AtPrime Q
  letI : Algebra (Localization.AtPrime p) T :=
    Localization.AtPrime.algebraOfLiesOver p Q
  (IsLocalRing.maximalIdeal T).comap
    (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom

/-- The contracted maximal prime is prime, as the comap of the maximal (hence
prime) ideal of the local factor. -/
theorem normalizedTensorCompositumPrime_isPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    (normalizedTensorCompositumPrime E F p h Q).IsPrime := by
  unfold normalizedTensorCompositumPrime
  infer_instance

attribute [instance] normalizedTensorCompositumPrime_isPrime

/-- Defining membership characterization of the contracted maximal prime: an
element lies in the contracted prime exactly when its image lies in the maximal
ideal of the local target. -/
theorem normalizedTensorCompositumPrime_mem_iff
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :
    x ∈ normalizedTensorCompositumPrime E F p h Q ↔
      normalizedTensorToCompositumAtPrime E F p h Q x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  unfold normalizedTensorCompositumPrime
  rfl

/-- The kernel of the normalized-tensor-to-compositum map is contained in the
contracted maximal prime. -/
theorem normalizedTensorToCompositumAtPrime_ker_le
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    RingHom.ker (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom ≤
      normalizedTensorCompositumPrime E F p h Q := by
  unfold normalizedTensorCompositumPrime
  exact Ideal.ker_le_comap _

/-- Canonical localization map: the universal property of
`Localization.AtPrime` applied at the contracted maximal prime. An element
outside the contracted prime maps outside the maximal ideal of the local target
`T`, hence to a unit.

This is a plain `RingHom`, not an `AlgHom`: no `Algebra A S` or
`IsScalarTower A C S` data is installed, since that instance search is fragile.
No `IsLocalization` or `AlgEquiv` claim is made here: the missing
bijection/local-factor identification remains a later infrastructure problem,
and localization at `RingHom.ker g` is in general false. -/
noncomputable def normalizedTensorLocalizationToCompositumAtPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let qC := normalizedTensorCompositumPrime E F p h Q
    let S := Localization.AtPrime qC
    let T := Localization.AtPrime Q
    S →+* T := by
  have hprime : (normalizedTensorCompositumPrime E F p h Q).IsPrime :=
    normalizedTensorCompositumPrime_isPrime E F p h Q
  letI := hprime
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  exact IsLocalization.lift
    (M := (normalizedTensorCompositumPrime E F p h Q).primeCompl)
    (g := (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom)
    (fun y => by
      have hy' : (normalizedTensorToCompositumAtPrime E F p h Q) y.val ∉
          IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
        intro hmem
        exact y.property (by
          unfold normalizedTensorCompositumPrime
          exact hmem)
      exact IsLocalRing.notMem_maximalIdeal.mp hy')

/-- The canonical localization map extends the normalized-tensor map: it sends
each algebraMap image to the value of `normalizedTensorToCompositumAtPrime`. -/
theorem normalizedTensorLocalizationToCompositumAtPrime_algebraMap
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :
    normalizedTensorLocalizationToCompositumAtPrime E F p h Q
        (algebraMap _ _ x) =
      normalizedTensorToCompositumAtPrime E F p h Q x := by
  unfold normalizedTensorLocalizationToCompositumAtPrime
  rw [IsLocalization.lift_eq]
  rfl

/-- Characteristic equation for the canonical localization map on a
localization representative: the value at `IsLocalization.mk' _ x y` is
characterized by cross multiplication against the base map. This is the stable
`IsLocalization.lift_mk'`-style form; it avoids exposing the
implementation-only unit proof inside
`normalizedTensorLocalizationToCompositumAtPrime`. -/
theorem normalizedTensorLocalizationToCompositumAtPrime_mk'_spec
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E))))
    (y : (normalizedTensorCompositumPrime E F p h Q).primeCompl)
    (v : Localization.AtPrime Q) :
    normalizedTensorLocalizationToCompositumAtPrime E F p h Q
        (IsLocalization.mk'
          (Localization.AtPrime (normalizedTensorCompositumPrime E F p h Q)) x y) =
      v ↔
      normalizedTensorToCompositumAtPrime E F p h Q x =
        normalizedTensorToCompositumAtPrime E F p h Q ↑y * v := by
  unfold normalizedTensorLocalizationToCompositumAtPrime
  rw [IsLocalization.lift_mk'_spec]
  exact Iff.rfl

end IsUnramifiedIn

end NumberField

end

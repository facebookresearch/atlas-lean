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

/-- **Unramifiedness descends to smaller intermediate fields.** Let $L$ be a number field, let
$E \subseteq F$ be intermediate fields of $L/\mathbb{Q}$, and let $\mathfrak{p}$ be an ideal of
$\mathbb{Z}$. If $\mathfrak{p}$ is unramified in $\mathcal{O}_F$, that is, every prime ideal of
$\mathcal{O}_F$ lying over $\mathfrak{p}$ is unramified over $\mathbb{Z}$, then $\mathfrak{p}$ is
unramified in $\mathcal{O}_E$.

Source: generic form of `isUnramifiedAtPrime_of_le` in the primary Lean source for ATLAS
`NumberTheoryI` target N390, Proposition 19.14. -/
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

/-- **Localizing the ring of integers at an unramified prime gives an étale algebra.** Let $K$ be
a number field with ring of integers $\mathcal{O}_K$, and let $p$ be a prime ideal of $\mathbb{Z}$
that is unramified in $\mathcal{O}_K$, that is, every prime ideal of $\mathcal{O}_K$ lying over $p$
is unramified over $\mathbb{Z}$. Let $S$ be the localization of $\mathcal{O}_K$ at the image of
the multiplicative set $\mathbb{Z} \setminus p$. Then $S$ is an étale algebra over the local ring
$\mathbb{Z}_{(p)}$.

The ring $S$ is semilocal: it keeps every prime of $\mathcal{O}_K$ above $p$ at once, rather than
the localization $(\mathcal{O}_K)_Q$ at a single such prime $Q$.

Source: packages the primewise unramified hypothesis used by `isUnramifiedAtPrime_sup` in the
primary Lean source for ATLAS `NumberTheoryI` target N390, Proposition 19.14. -/
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

/-- **Normalization commutes with base change along an unramified prime.** Let $E$ and $F$ be
number fields and let $\mathfrak p$ be a prime ideal of $\mathbb Z$ that is unramified in the ring
of integers $\mathcal O_F$. Write $R = \mathbb Z_{\mathfrak p}$ for the localization of $\mathbb Z$
at $\mathfrak p$, and for $K = E, F$ write $S_K$ for the localization of $\mathcal O_K$ at the
image of $\mathbb Z \setminus \mathfrak p$. Let $K_E$ be the fraction field of $\mathcal O_E$ and
let $\iota : S_E \to K_E$ be the canonical map. This is the isomorphism of $S_F$-algebras from
$S_F \otimes_R S_E$ onto the integral closure of $S_F$ in $S_F \otimes_R K_E$ that, for
$s \in S_F$ and $t \in S_E$, sends $s \otimes t$ to $s \otimes \iota(t)$.

It is obtained from the identification of $S_E$ with the integral closure of $R$ in $K_E$, using
that $S_F$ is étale over $R$. -/
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

/-- **Map from the localization away from a prime to the local ring at a prime above it.** Let
$R \to S \to T$ be homomorphisms of commutative rings whose algebra structures form a scalar
tower, let $\mathfrak p$ be a prime ideal of $R$, and let $\mathfrak Q$ be a prime ideal of $T$
lying over $\mathfrak p$. Write $S_{\mathfrak p}$ for the localization of $S$ at the image of
$R \setminus \mathfrak p$. This is the homomorphism of $S$-algebras
$S_{\mathfrak p} \to T_{\mathfrak Q}$ extending the composite $S \to T \to T_{\mathfrak Q}$; it
exists because elements of $R \setminus \mathfrak p$ map outside $\mathfrak Q$, hence to units of
$T_{\mathfrak Q}$. -/
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

/-- **Values of the localization-to-local-ring map on fractions.** Let $R \to S \to T$ be
homomorphisms of commutative rings whose algebra structures form a scalar tower, let
$\mathfrak p$ be a prime ideal of $R$, and let $\mathfrak Q$ be a prime ideal of $T$ lying over
$\mathfrak p$. Write $S_{\mathfrak p}$ for the localization of $S$ at the image of
$R \setminus \mathfrak p$, and let $\varphi : S_{\mathfrak p} \to T_{\mathfrak Q}$ be the
$S$-algebra homomorphism extending the composite $S \to T \to T_{\mathfrak Q}$. For $x \in S$,
$y$ in the image of $R \setminus \mathfrak p$ in $S$, and $z \in T_{\mathfrak Q}$, we have
$\varphi(x/y) = z$ if and only if $x = yz$ in $T_{\mathfrak Q}$, where $x$ and $y$ stand for
their images under $S \to T \to T_{\mathfrak Q}$. -/
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

/-- **Map from the normalized tensor algebra to the local ring of the compositum.** Let $E$ and
$F$ be intermediate fields of a number field $L$ over $\mathbb Q$, let $\mathfrak p$ be a prime
ideal of $\mathbb Z$ that is unramified in $\mathcal O_F$, and let $\mathfrak Q$ be a prime ideal of
the ring of integers $\mathcal O_{EF}$ of the compositum $EF$ of $E$ and $F$ in $L$ lying over
$\mathfrak p$. Write $R = \mathbb Z_{\mathfrak p}$ for the localization of $\mathbb Z$ at
$\mathfrak p$; for $K = E, F$ write $S_K$ for the localization of $\mathcal O_K$ at the image of
$\mathbb Z \setminus \mathfrak p$ and $\varphi_K : S_K \to (\mathcal O_{EF})_{\mathfrak Q}$ for the
map induced by the inclusion $\mathcal O_K \subseteq \mathcal O_{EF}$; and let $C$ be the integral
closure of $S_F$ in $S_F \otimes_R \operatorname{Frac}(\mathcal O_E)$. This is the $R$-algebra
homomorphism $C \to (\mathcal O_{EF})_{\mathfrak Q}$ obtained by composing the inverse of the
canonical isomorphism $S_F \otimes_R S_E \cong C$ with the map
$S_F \otimes_R S_E \to (\mathcal O_{EF})_{\mathfrak Q}$ that, for $s \in S_F$ and $t \in S_E$,
sends $s \otimes t$ to $\varphi_F(s) \varphi_E(t)$.

No claim is made that this map induces an isomorphism from a localization of $C$ onto
$(\mathcal O_{EF})_{\mathfrak Q}$. -/
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

/-- **The normalized tensor map on simple tensors.** Let $L$ be a number field, let $E$ and $F$ be
intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ and $S_E$ be the
localizations of $\mathcal{O}_F$ and $\mathcal{O}_E$ at the image of $\mathbb{Z} \setminus p$, let
$C$ be the integral closure of $S_F$ in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let
$T = (\mathcal{O}_{EF})_Q$, and let $g \colon C \to T$ be the normalized tensor map to the
compositum at $Q$. Let $e \colon S_F \otimes_R S_E \to C$ be the normalization isomorphism, and
let $f_F \colon S_F \to T$ and $f_E \colon S_E \to T$ be the maps induced by the inclusions of
$\mathcal{O}_F$ and $\mathcal{O}_E$ into $\mathcal{O}_{EF}$. Then for all $x \in S_F$ and
$y \in S_E$, we have $g(e(x \otimes y)) = f_F(x)\,f_E(y)$. -/
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

/-- **The kernel of the normalized tensor map is prime.** Let $L$ be a number field, let $E$ and
$F$ be intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, and let
$g \colon C \to (\mathcal{O}_{EF})_Q$ be the normalized tensor map to the compositum at $Q$. Then
the kernel of $g$ is a prime ideal of $C$.

This holds because $(\mathcal{O}_{EF})_Q$ is an integral domain. The kernel of $g$ is in general
strictly smaller than the preimage under $g$ of the maximal ideal of the local ring
$(\mathcal{O}_{EF})_Q$, which is the prime of $C$ at which to localize. -/
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

/-- **The contracted maximal prime of the normalized tensor algebra.** Let $L$ be a number field,
let $E$ and $F$ be intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime
ideal of $\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let $T = (\mathcal{O}_{EF})_Q$ be the
localization of $\mathcal{O}_{EF}$ at $Q$, and let $g \colon C \to T$ be the normalized tensor map
to the compositum at $Q$. The contracted maximal prime is the ideal $g^{-1}(\mathfrak{m}_T)$ of
$C$, where $\mathfrak{m}_T$ is the maximal ideal of the local ring $T$.

It contains the kernel of $g$, and is in general strictly larger. It is intended as the prime of
$C$ at which to localize in order to recover the local factor $T$.

Source: prerequisite stage for `cyclotomic_ramIdx_eq_of_unramified` and
`baseChange_ramificationIdx_eq_one` in the primary Lean source for ATLAS `NumberTheoryI`
target N390, Proposition 19.14; the identification of this localization with the local factor $T$,
compositum unramifiedness and the maximality theorem are not proved here. -/
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

/-- **The contracted maximal prime is prime.** Let $L$ be a number field, let $E$ and $F$ be
intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Then the contracted maximal prime of the normalized tensor
algebra at $Q$ is a prime ideal.

It is the preimage of the maximal ideal of the local ring $(\mathcal{O}_{EF})_Q$, which is
prime. -/
theorem normalizedTensorCompositumPrime_isPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    (normalizedTensorCompositumPrime E F p h Q).IsPrime := by
  unfold normalizedTensorCompositumPrime
  infer_instance

attribute [instance] normalizedTensorCompositumPrime_isPrime

/-- **Membership in the contracted maximal prime.** Let $L$ be a number field, let $E$ and $F$ be
intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let $T = (\mathcal{O}_{EF})_Q$, and let
$g \colon C \to T$ be the normalized tensor map to the compositum at $Q$. An element $x \in C$
lies in the contracted maximal prime if and only if $g(x)$ lies in the maximal ideal of the local
ring $T$. -/
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

/-- **The kernel lies in the contracted maximal ideal.** Let $E$ and $F$ be intermediate fields of
a number field $L$ over $\mathbb Q$, let $\mathfrak p$ be a prime ideal of $\mathbb Z$ that is
unramified in $\mathcal O_F$, and let $\mathfrak Q$ be a prime ideal of the ring of integers
$\mathcal O_{EF}$ of the compositum $EF$ of $E$ and $F$ in $L$ lying over $\mathfrak p$. Write
$R = \mathbb Z_{\mathfrak p}$ for the localization of $\mathbb Z$ at $\mathfrak p$; for
$K = E, F$ let $S_K$ be the localization of $\mathcal O_K$ at the image of
$\mathbb Z \setminus \mathfrak p$ and let $\varphi_K : S_K \to (\mathcal O_{EF})_{\mathfrak Q}$ be
the map induced by the inclusion $\mathcal O_K \subseteq \mathcal O_{EF}$; let $C$ be the integral
closure of $S_F$ in $S_F \otimes_R \operatorname{Frac}(\mathcal O_E)$; and let
$g : C \to (\mathcal O_{EF})_{\mathfrak Q}$ be the $R$-algebra homomorphism that, for $s \in S_F$
and $t \in S_E$, sends the image of $s \otimes t$ under the canonical isomorphism
$S_F \otimes_R S_E \cong C$ to $\varphi_F(s) \varphi_E(t)$. Then the kernel of $g$ is contained in
the preimage under $g$ of the maximal ideal of $(\mathcal O_{EF})_{\mathfrak Q}$. -/
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

/-- **The localization map to the compositum at a prime.** Let $L$ be a number field, let $E$ and
$F$ be intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let $T = (\mathcal{O}_{EF})_Q$, let
$g \colon C \to T$ be the normalized tensor map to the compositum at $Q$, and let $\mathfrak{q}$
be the contracted maximal prime of $C$. Since $g$ sends every element of $C \setminus \mathfrak{q}$
outside the maximal ideal of the local ring $T$, hence to a unit, $g$ induces by the universal
property of localization a ring homomorphism $C_{\mathfrak{q}} \to T$, sending $x/s$ to
$g(x)\,g(s)^{-1}$. -/
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

/-- **The localization map restricts to the normalized tensor map.** Let $L$ be a number field,
let $E$ and $F$ be intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime
ideal of $\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let $T = (\mathcal{O}_{EF})_Q$, let
$g \colon C \to T$ be the normalized tensor map to the compositum at $Q$, let $\mathfrak{q}$ be the
contracted maximal prime of $C$, and let $\varphi \colon C_{\mathfrak{q}} \to T$ be the
localization map to the compositum at $Q$. Then for every $x \in C$, $\varphi$ sends the image of
$x$ in $C_{\mathfrak{q}}$ to $g(x)$. -/
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

/-- **Value of the localization map on fractions.** Let $L$ be a number field, let $E$ and $F$ be
intermediate fields of $L/\mathbb{Q}$ with compositum $EF$, let $p$ be a prime ideal of
$\mathbb{Z}$ that is unramified in $\mathcal{O}_F$, and let $Q$ be a prime ideal of
$\mathcal{O}_{EF}$ lying over $p$. Write $R = \mathbb{Z}_{(p)}$, let $S_F$ be the localization of
$\mathcal{O}_F$ at the image of $\mathbb{Z} \setminus p$, let $C$ be the integral closure of $S_F$
in $S_F \otimes_R \operatorname{Frac}(\mathcal{O}_E)$, let $T = (\mathcal{O}_{EF})_Q$, let
$g \colon C \to T$ be the normalized tensor map to the compositum at $Q$, let $\mathfrak{q}$ be the
contracted maximal prime of $C$, and let $\varphi \colon C_{\mathfrak{q}} \to T$ be the
localization map to the compositum at $Q$. Then for all $x \in C$, $s \in C \setminus \mathfrak{q}$
and $v \in T$, we have $\varphi(x/s) = v$ if and only if $g(x) = g(s)\,v$. -/
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

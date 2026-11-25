/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.SemistableAdicMonodromy
public import MathlibExt.AlgebraicGeometry.RapoportZinkContracts

/-!
# Unipotence of inertia for proper strictly semistable degenerations

For a proper strictly semistable scheme over a henselian discrete valuation ring with residue
characteristic `p` and a prime `ℓ ≠ p`, every inertia element `σ` acts unipotently on the rational
`ℓ`-adic cohomology `H^n` of the geometric generic fibre, with `(σ - 1)^(n+1) = 0` (Illusie,
Corollary 3.3; the hypotheses are those of §3.1), first over `ℤ_p` and then over a general trait.
On the nearby object, the inertia operators satisfy `(σ - 1)^(d+1) = 0` in relative dimension `d`.
The last request is the normalized Weil–Deligne association for the semistable cohomology.

The Rapoport–Zink part (the perverse nearby object, its monodromy filtration and the filtered
resolution with its stratum grades) is not included: it needs a constructible coefficient category
over the continuous coefficient ring sheaf, which is left for later work.

Source: Illusie, *Autour du théorème de monodromie locale*, Astérisque 223 (1994), Exposé I,
Corollary 3.3, p. 35, and §3.1, pp. 33–34, https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace WantedExt.AlgebraicGeometry.SemistableAdicMonodromy

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PadicNeronModels
open MathlibExt.AlgebraicGeometry.SemistableAdicMonodromy

/-- Illusie's monodromy theorem over $ℤ_p$ (Illusie, Corollary 3.3): let $p$ and $ℓ$ be primes
with $ℓ ≠ p$, and $X$ a proper scheme over $ℤ_p$ that is strictly semistable with respect to the
uniformizer $p$. Then for every $n ∈ ℕ$ and every element $σ$ of the inertia subgroup of
$\mathrm{Gal}(\bar{ℚ}_p/ℚ_p)$, the operator of $σ$ on the rational $ℓ$-adic cohomology $H^n$ of
the geometric generic fibre $X_{\bar{ℚ}_p}$ satisfies $(σ - 1)^{n+1} = 0$. -/
public theorem_wanted inertia_unipotent
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (ellNeResidueCharacteristic : ell ≠ p)
    (X : Over (trait p)) [IsProper X.hom]
    (semistable : IsStrictlySemistable p X)
    (n : ℕ) (σ : Galois p) (inertiaElement : σ ∈ inertia p) :
    (galoisOperator p X ell σ n - 1) ^ (n + 1) = 0

end WantedExt.AlgebraicGeometry.SemistableAdicMonodromy

namespace WantedExt.AlgebraicGeometry.GeneralSemistableDegeneration

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open GeometricSemistableTraits AdicDerivedContracts
open SemistableWeilDeligne

attribute [local instance] HasDerivedCategory.standard

/-!
## General traits

The same bounds over a henselian discrete valuation ring with algebraically closed fraction field
extension `L`, for its geometric trait `T`, and the Weil–Deligne association. The residue
characteristic is a prime `p`, as in Illusie's §3.
-/

/-- Illusie's monodromy theorem over a henselian trait: let $ℓ$ and $p$ be primes with $ℓ ≠ p$,
$R$ a henselian discrete valuation ring whose residue field has characteristic $p$, $K$ its
fraction field, $L$ an algebraic closure of $K$, $π ∈ R$ with geometric-trait data $T$
(`GeometricTrait`: the integral closure of $R$ in $L$ is henselian local with algebraically closed
residue field, and inverting $π$ in it gives $L$), and $X$ a proper $R$-scheme that is strictly
semistable with respect to $π$ (in particular $π$ is a uniformizer). Then for every $n ∈ ℕ$ and
every inertia element $σ$ (`Inertia π T`), the operator of $σ$ on the rational $ℓ$-adic
cohomology $H^n$ of the geometric generic fibre $X_L$ satisfies $(σ - 1)^{n+1} = 0$. -/
public theorem_wanted generalInertiaUnipotent
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (n : ℕ) (σ : Inertia π T) :
    (operator ell R K L X σ.1.1 n - 1) ^ (n + 1) = 0

/-- Nilpotence of inertia on nearby cycles: let $ℓ$ and $p$ be primes with $ℓ ≠ p$, $R$ a
henselian discrete valuation ring whose residue field has characteristic $p$, $K$ its fraction
field, $L$ an algebraic closure of $K$, $π ∈ R$ with geometric-trait data $T$ (`GeometricTrait`),
and $X$ a proper $R$-scheme, strictly semistable with respect to $π$, whose generic fibre is
smooth of relative dimension $d$. Assume the given derived-functor data for $ℚ_ℓ$-coefficients
(`DerivedFunctorTheory`), and that for every $σ ∈ \mathrm{Gal}(L/K)$ the comparison of continuous
$ℚ_ℓ$-coefficient sheaves along the automorphism of the geometric generic fibre induced by $σ$ is
an isomorphism. Then every inertia element $σ$ acts on the nearby-cycle object
(`RapoportZinkContracts.inertiaOperator`) with $(σ - 1)^{d+1} = 0$. -/
public theorem_wanted nearbyInertiaNilpotent
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (d : ℕ) [SmoothOfRelativeDimension d ((SemistableModels.genericFunctor R
      K).obj X).hom]
    [DerivedFunctorTheory ℚ_[ell]]
    [∀ σ : Galois K L, IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell) (genericGalois (K := K) X σ))]
    (σ : Inertia π T) :
    (RapoportZinkContracts.inertiaOperator ell R K L π T X σ - 1) ^ (d + 1) = 0

/-- Weil–Deligne structure of semistable cohomology: let $ℓ$ be a prime, $R$ a henselian discrete
valuation ring whose residue field has characteristic $p ≠ ℓ$, $K$ its fraction field, $L$ an
algebraic closure of $K$, $π ∈ R$ with geometric-trait data $T$ (`GeometricTrait`), $X$ a proper
$R$-scheme that is strictly semistable with respect to $π$, and $n ∈ ℕ$. Assume that the Galois
operators on the rational $ℓ$-adic cohomology $H^n$ of $X_L$ form an action
(`CohomologyFunctoriality`), and fix an arithmetic Frobenius $A$ (`ArithmeticFrobenius`, which
includes finiteness of the residue field) and a tame coordinate $B$ (`TameCoordinate`). Then, for
$N$ the logarithm of the operator of the tame generator: $N^{n+1} = 0$, every inertia element $σ$
acts by $\exp(t_B(σ) N)$, and $ρ(w) N = q^{\deg w} N ρ(w)$ for every $w$ in the Weil group, where
$ρ(w)$ is the Frobenius operator to the power $\deg w$ and $q$ is the cardinality of the residue
field (`SemistableWeilDeligneLaws`). -/
public theorem_wanted semistableWeilDeligne
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X) (n : ℕ)
    [CohomologyFunctoriality ell R K L X n]
    (A : ArithmeticFrobenius R K L π T) (B : TameCoordinate ell R K L π T) :
    SemistableWeilDeligneLaws ell R K L X n A B

end WantedExt.AlgebraicGeometry.GeneralSemistableDegeneration

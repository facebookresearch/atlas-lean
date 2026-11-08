/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Prime factors with given multiplicity in h-free and h-full polynomials (statements)

Statement-only targets from Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given
Multiplicity in h-Free and h-Full Polynomials over Function Fields*, over a finite field `F`
with `q = Fintype.card F` elements: Erdős–Kac laws for `ω_1` on `h`-free and `ω_h` on `h`-full
monic polynomials, the absence of a normal order for the other `ω_k`, a coprime count, and
Perron's formula. `ω_k(f)` counts the monic irreducible `P` with `P^k ∥ f` (the title's "prime
factors with given multiplicity").
-/

open scoped Interval
open Filter Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt

attribute [local instance] Classical.propDecidable

@[expose] public section

/--
`fixedDegreeMonic F n` is the finite collection `M_n` of monic polynomials over `F`
of degree `n`.  A coefficient vector `c : Fin n → F` is sent to
`X ^ n + ∑ i, C (c i) * X ^ i`; thus the formal collection is explicitly finite and
contains exactly the possible lower coefficients of a monic degree-`n` polynomial.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public noncomputable def fixedDegreeMonic (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) :
    Finset (Polynomial F) :=
  Finset.univ.image fun c : Fin n → F =>
    X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

/--
Membership in `fixedDegreeMonic F n` is exactly representability by the displayed
coefficient-vector construction.  This records the defining finite parametrization of
`M_n` without appealing to an ambient infinite set of polynomials.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem mem_fixedDegreeMonic_iff (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (f : Polynomial F) :
    f ∈ fixedDegreeMonic F n ↔
      ∃ c : Fin n → F, X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ) = f := by
  simp [fixedDegreeMonic]

/--
The degree-zero slice `M_0` consists only of the constant monic polynomial `1`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem fixedDegreeMonic_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    fixedDegreeMonic F 0 = {1} := by
  ext f
  simp [fixedDegreeMonic]

/--
`monicIrreducible F` is the paper's set `𝒫` of prime polynomials: its two formal clauses
say respectively that the polynomial is monic and irreducible.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def monicIrreducible (F : Type*) [Field F] : Set (Polynomial F) :=
  {P | P.Monic ∧ Irreducible P}

/--
A polynomial belongs to `monicIrreducible F` precisely when it is both monic and
irreducible, exposing the two clauses used for `P ∈ 𝒫` in later statements.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem mem_monicIrreducible_iff (F : Type*) [Field F] (P : Polynomial F) :
    P ∈ monicIrreducible F ↔ P.Monic ∧ Irreducible P := by
  rfl

/--
`hFree F h` is `S_h`: a member is monic, and no monic irreducible `P` has its `h`th
power dividing the member.  The condition is intentionally meaningful for every
natural `h`; the paper's asymptotic theorems separately assume `2 ≤ h`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def hFree (F : Type*) [Field F] (h : ℕ) : Set (Polynomial F) :=
  {f | f.Monic ∧ ∀ P ∈ monicIrreducible F, ¬P ^ h ∣ f}

/--
The unit polynomial is `h`-free for positive `h`: a hypothetical irreducible factor
would become a unit after taking a positive power, contradicting irreducibility.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem one_mem_hFree (F : Type*) [Field F] (h : ℕ) (hh : 0 < h) :
    (1 : Polynomial F) ∈ hFree F h := by
  refine ⟨monic_one, ?_⟩
  intro P hP hdiv
  have hpow : IsUnit (P ^ h) := isUnit_iff_dvd_one.mpr hdiv
  exact hP.2.not_isUnit ((isUnit_pow_iff hh.ne').mp hpow)

/--
`hFull F h` is `N_h`: a member is monic, and whenever a monic irreducible `P` divides
it, `P ^ h` also divides it.  As in the source, theorem statements impose `2 ≤ h`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public def hFull (F : Type*) [Field F] (h : ℕ) : Set (Polynomial F) :=
  {f | f.Monic ∧ ∀ P ∈ monicIrreducible F, P ∣ f → P ^ h ∣ f}

/--
The unit polynomial is `h`-full for every `h`, because no irreducible polynomial can
divide `1`; the divisibility implication in the definition is therefore vacuous.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem one_mem_hFull (F : Type*) [Field F] (h : ℕ) :
    (1 : Polynomial F) ∈ hFull F h := by
  refine ⟨monic_one, ?_⟩
  intro P hP hdiv
  exact False.elim (hP.2.not_isUnit (isUnit_iff_dvd_one.mpr hdiv))

/--
`omegaMult F k f` is `ω_k(f)`, the number of distinct normalized irreducible factors
of the nonzero polynomial `f` whose multiplicity in `normalizedFactors f` is exactly
`k`.  The exceptional input `f = 0`, for which normalized factorization is not the
paper's finite prime factorization, is assigned value `0` explicitly.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public noncomputable def omegaMult (F : Type*) [Field F] (k : ℕ) (f : Polynomial F) : ℕ := by
  classical
  exact if f = 0 then 0 else
    ((normalizedFactors f).toFinset.filter fun P => (normalizedFactors f).count P = k).card

/--
The explicit exceptional convention in `omegaMult` gives `ω_k(0) = 0` for every
multiplicity `k`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem omegaMult_zero (F : Type*) [Field F] (k : ℕ) :
    omegaMult F k 0 = 0 := by
  simp [omegaMult]

/--
The unit polynomial has no normalized irreducible factors, so `ω_k(1) = 0` for every
multiplicity `k`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Definitions.
-/
public theorem omegaMult_one (F : Type*) [Field F] (k : ℕ) :
    omegaMult F k 1 = 0 := by
  simp [omegaMult, normalizedFactors_one]

/--
`IsDegreeNondecreasing U G` formalizes the source's reversed-looking monotonicity
convention: for `f₁,f₂ ∈ U`, the inequality `deg f₂ ≤ deg f₁` implies
`G f₂ ≤ G f₁`.  Natural degree is adequate because `U` will consist of monic, hence
nonzero, polynomials.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public def IsDegreeNondecreasing (F : Type*) [Field F] (U : Set (Polynomial F))
    (G : Polynomial F → ℝ) : Prop :=
  ∀ ⦃f₁ f₂ : Polynomial F⦄, f₁ ∈ U → f₂ ∈ U → f₂.natDegree ≤ f₁.natDegree →
    G f₂ ≤ G f₁

/--
Every constant real-valued function is degree-nondecreasing on every polynomial set;
the degree premise is irrelevant because both function values coincide.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public theorem isDegreeNondecreasing_const (F : Type*) [Field F]
    (U : Set (Polynomial F)) (c : ℝ) :
    IsDegreeNondecreasing F U (fun _ => c) := by
  intro f₁ f₂ hf₁ hf₂ hdeg
  exact le_rfl

/--
`HasNormalOrder F U g G` says first that `g` and `G` are nonnegative on `U` and that `G`
is degree-nondecreasing there.  It then says that for each `ε > 0`, the real-valued count
of degree-`n` members of `U` outside
`(1-ε)G(f) < g(f) < (1+ε)G(f)` is little-o of the count of `U ∩ M_n` as `n → ∞`.
The paper writes `g,G : U → ℝ≥0`; total real-valued functions are used here, with
nonnegativity of both imposed on `U`, so that finite-set filtering remains direct.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public noncomputable def HasNormalOrder (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (U : Set (Polynomial F)) (g G : Polynomial F → ℝ) : Prop := by
  classical
  exact
    (∀ f ∈ U, 0 ≤ g f) ∧ (∀ f ∈ U, 0 ≤ G f) ∧ IsDegreeNondecreasing F U G ∧
      ∀ ε : ℝ, 0 < ε →
        Asymptotics.IsLittleO atTop
          (fun n : ℕ =>
            (((fixedDegreeMonic F n).filter fun f =>
              f ∈ U ∧ ¬((1 - ε) * G f < g f ∧ g f < (1 + ε) * G f)).card : ℝ))
          (fun n : ℕ => (((fixedDegreeMonic F n).filter fun f => f ∈ U).card : ℝ))

/--
Any asserted normal order has a nonnegative comparison function on `U`; this is the
second defining clause of `HasNormalOrder`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3 (definition preceding the requested normal-order results).
-/
public theorem HasNormalOrder.nonnegative (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (U : Set (Polynomial F)) (g G : Polynomial F → ℝ)
    (horder : HasNormalOrder F U g G) (f : Polynomial F) (hf : f ∈ U) :
    0 ≤ G f := by
  exact horder.2.1 f hf

/--
For `2 ≤ h` and `α ≤ β`, the proportion of `h`-free monic degree-`n` polynomials for
which the standardized value `(ω₁(f) - log n) / sqrt (log n)` lies in `[α,β]` tends
to the standard Gaussian mass of that interval.  Both finite counts are cast to `ℝ`;
division by a zero denominator retains ordinary field semantics.  The logarithm sees
the real cast of `n`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 2.
-/
public theorem_wanted erdosKac_omegaOne_hFree
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 2 ≤ h) (α β : ℝ) (hαβ : α ≤ β) :
    Tendsto
      (fun n : ℕ =>
        (((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFree F h ∧
            α ≤ ((omegaMult F 1 f : ℝ) - Real.log (n : ℝ)) /
              Real.sqrt (Real.log (n : ℝ)) ∧
            ((omegaMult F 1 f : ℝ) - Real.log (n : ℝ)) /
              Real.sqrt (Real.log (n : ℝ)) ≤ β).card : ℝ) /
          (((fixedDegreeMonic F n).filter fun f => f ∈ hFree F h).card : ℝ))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ t : ℝ in α..β, Real.exp (-(t ^ 2) / 2)))

/--
If `2 ≤ h` and `1 < k < h`, then `ω_k`, viewed as a real-valued function, has no
normal order on the `h`-free monic polynomials with respect to any nonnegative,
degree-nondecreasing real comparison function `G`.  Encoding `G` on all polynomials
rather than as a subtype function is the documented total-function convention of
`HasNormalOrder`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 4.
-/
public theorem_wanted omegaMult_no_normalOrder_hFree
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k : ℕ) (hh : 2 ≤ h) (hk₁ : 1 < k) (hkh : k < h)
    (G : Polynomial F → ℝ)
    (hGnonneg : ∀ f ∈ hFree F h, 0 ≤ G f)
    (hGmono : IsDegreeNondecreasing F (hFree F h) G) :
    ¬HasNormalOrder F (hFree F h) (fun f => (omegaMult F k f : ℝ)) G

/--
For `2 ≤ h` and `α ≤ β`, the proportion of `h`-full monic degree-`n` polynomials for
which `(ω_h(f) - log (n/h)) / sqrt (log (n/h))` lies in `[α,β]` tends to the standard
Gaussian mass of the interval.  Crucially, `(n : ℝ) / (h : ℝ)` is real division, not
truncated natural-number division.  Counts are cast to `ℝ`, with ordinary zero-
denominator field behavior left unchanged.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 6.
-/
public theorem_wanted erdosKac_omegaH_hFull
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 2 ≤ h) (α β : ℝ) (hαβ : α ≤ β) :
    Tendsto
      (fun n : ℕ =>
        (((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFull F h ∧
            α ≤ ((omegaMult F h f : ℝ) - Real.log ((n : ℝ) / (h : ℝ))) /
              Real.sqrt (Real.log ((n : ℝ) / (h : ℝ))) ∧
            ((omegaMult F h f : ℝ) - Real.log ((n : ℝ) / (h : ℝ))) /
              Real.sqrt (Real.log ((n : ℝ) / (h : ℝ))) ≤ β).card : ℝ) /
          (((fixedDegreeMonic F n).filter fun f => f ∈ hFull F h).card : ℝ))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) *
        ∫ t : ℝ in α..β, Real.exp (-(t ^ 2) / 2)))

/--
If `2 ≤ h` and `h < k`, then `ω_k`, cast to a real-valued function, has no normal
order on the `h`-full monic polynomials for any nonnegative degree-nondecreasing
comparison function `G`.  As elsewhere, `G` is total on polynomials and its sign and
monotonicity requirements are restricted to `N_h`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 8.
-/
public theorem_wanted omegaMult_no_normalOrder_hFull
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (G : Polynomial F → ℝ)
    (hGnonneg : ∀ f ∈ hFull F h, 0 ≤ G f)
    (hGmono : IsDegreeNondecreasing F (hFull F h) G) :
    ¬HasNormalOrder F (hFull F h) (fun f => (omegaMult F k f : ℝ)) G

/--
For a finite field of size `q`, `ℓ ≥ 2`, and `P ∈ 𝒫`, the real count of degree-`n`
members of `S_ℓ` coprime to `P` differs by a uniformly bounded amount from
`q^n (1-q^(1-ℓ)) (1-|P|⁻¹)/(1-|P|⁻ℓ)`, where `|P| = q^(deg P)`.  The existential
constant follows `F`, `ℓ`, and the degree `d = deg P` but precedes `P` and `n`, so it is
uniform over irreducibles of the same degree (`O_{ℓ, deg P}(1)`).  `IsCoprime f P` encodes `(f,P)=1`.  The source says `ℓ > 0`, but the
displayed zeta factor has a pole at `ℓ = 1`, so the formal statement restricts to
`ℓ ≥ 2`; `1-q^(1-ℓ)` is the explicit reciprocal of `ζ_q(ℓ)`.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 3.
-/
public theorem_wanted card_hFree_coprime_irreducible_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P ∈ monicIrreducible F, P.natDegree = d → ∀ n : ℕ,
      |(((fixedDegreeMonic F n).filter fun f =>
          f ∈ hFree F ℓ ∧ IsCoprime f P).card : ℝ) -
        ((Fintype.card F : ℝ) ^ n *
          (1 - (Fintype.card F : ℝ) ^ (1 - (ℓ : ℤ))) *
          (1 - ((Fintype.card F : ℝ) ^ P.natDegree)⁻¹) /
          (1 - (((Fintype.card F : ℝ) ^ P.natDegree) ^ ℓ)⁻¹))| ≤ C

/--
Let `A(u)` be the `tsum` of the degree-slice coefficients
`(∑ f ∈ M_m, a f)u^m`.  If the prescribed scalar norm series is summable at a real
radius `0 < r < 1`, then the degree-`n` coefficient sum equals `1/(2πi)` times the
counterclockwise `circleIntegral` of `A(u)/u^(n+1)` around the circle centered at zero
with radius `r`.  The supplied summability hypothesis is exactly the task-requested
encoding; it is weaker in wording than uniform absolute convergence on the whole
closed disk, and this formal statement does not silently strengthen it. `A` is only
required to agree with the series on the circle `‖u‖ = r`, the only values the contour
integral sees.
Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 9.
-/
public theorem_wanted perron_formula_polynomial_degree_slice
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a : Polynomial F → ℂ) (A : ℂ → ℂ) (r : ℝ)
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hsum : Summable fun n : ℕ =>
      ‖∑ f ∈ fixedDegreeMonic F n, a f‖ * r ^ n)
    (hA : ∀ u : ℂ, ‖u‖ = r → A u = ∑' m : ℕ,
      (∑ f ∈ fixedDegreeMonic F m, a f) * u ^ m)
    (n : ℕ) :
    (∑ f ∈ fixedDegreeMonic F n, a f) =
      (1 / (2 * Real.pi * Complex.I)) *
        ∮ u in C(0, r), A u / u ^ (n + 1)


/-- The norm `|f| = q^{deg f}` of a polynomial over a finite field with `q` elements, with
`|0| = 0`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public noncomputable def polyNorm (F : Type*) [Field F] [Fintype F] (f : Polynomial F) : ℝ :=
  if f = 0 then 0 else (Fintype.card F : ℝ) ^ f.natDegree

/-- `|0| = 0`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem polyNorm_zero (F : Type*) [Field F] [Fintype F] : polyNorm F 0 = 0 := by
  simp [polyNorm]

/-- `|f| = q^{deg f}` for `f ≠ 0`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem polyNorm_of_ne_zero (F : Type*) [Field F] [Fintype F] {f : Polynomial F}
    (hf : f ≠ 0) : polyNorm F f = (Fintype.card F : ℝ) ^ f.natDegree := by
  simp [polyNorm, hf]

/-- The function field analogue of the first Mertens constant,
`B_1 = γ + ∑_P (log(1 - 1/|P|) + 1/|P|)`, the sum over monic irreducible `P`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public noncomputable def functionFieldMertensConstant (F : Type*) [Field F] [Fintype F] : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' P : monicIrreducible F, (Real.log (1 - 1 / polyNorm F P) + 1 / polyNorm F P)

/-- Unfolding `B_1`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Introduction. -/
public theorem functionFieldMertensConstant_eq (F : Type*) [Field F] [Fintype F] :
    functionFieldMertensConstant F = Real.eulerMascheroniConstant +
      ∑' P : monicIrreducible F, (Real.log (1 - 1 / polyNorm F P) + 1 / polyNorm F P) := rfl

/-- The `j`-th moment of `ω_k` over the `h`-free monic polynomials of degree `n`,
`|S_h ∩ M_n|^{-1} ∑_{f ∈ S_h ∩ M_n} ω_k(f)^j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 1 and 3. -/
public noncomputable def hFreeMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : ℝ :=
  (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFree F h), (omegaMult F k f : ℝ) ^ j) /
    (((fixedDegreeMonic F n).filter (· ∈ hFree F h)).card : ℝ)

/-- Unfolding the moment.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 1 and 3. -/
public theorem hFreeMoment_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : hFreeMoment F h k j n =
      (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFree F h), (omegaMult F k f : ℝ) ^ j) /
        (((fixedDegreeMonic F n).filter (· ∈ hFree F h)).card : ℝ) := rfl

/-- `T_h = ∑_P (|P|^{h-1} - 1)/(|P|(|P|^h - 1))`, the prime sum in `C_1(S_h, 1)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public noncomputable def hFreeOmegaOneSum (F : Type*) [Field F] [Fintype F] (h : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - 1) - 1) / (polyNorm F P * (polyNorm F P ^ h - 1))

/-- Unfolding `T_h`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public theorem hFreeOmegaOneSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) :
    hFreeOmegaOneSum F h = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - 1) - 1) / (polyNorm F P * (polyNorm F P ^ h - 1)) := rfl

/-- `U_h = ∑_P (|P|^{h-2}(|P| - 1)/(|P|^h - 1))^2`, the squared prime sum in
`C_3(S_h, 1)` and `C_4(S_h, 1)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public noncomputable def hFreeOmegaOneSqSum (F : Type*) [Field F] [Fintype F] (h : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - 2) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2

/-- Unfolding `U_h`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1. -/
public theorem hFreeOmegaOneSqSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) :
    hFreeOmegaOneSqSum F h = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - 2) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2 := rfl

/-- `S_{h,k} = ∑_P a_P` with `a_P = |P|^{h-k-1}(|P| - 1)/(|P|^h - 1)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public noncomputable def hFreeOmegaMultSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)

/-- Unfolding `S_{h,k}`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public theorem hFreeOmegaMultSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) :
    hFreeOmegaMultSum F h k = ∑' P : monicIrreducible F,
      polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1) := rfl

/-- `∑_P a_P^2` with `a_P = |P|^{h-k-1}(|P| - 1)/(|P|^h - 1)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public noncomputable def hFreeOmegaMultSqSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) : ℝ :=
  ∑' P : monicIrreducible F,
    (polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2

/-- Unfolding `∑_P a_P^2`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3. -/
public theorem hFreeOmegaMultSqSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) :
    hFreeOmegaMultSqSum F h k = ∑' P : monicIrreducible F,
      (polyNorm F P ^ (h - k - 1) * (polyNorm F P - 1) / (polyNorm F P ^ h - 1)) ^ 2 := rfl

/-- Theorem 1, first moment: for `h ≥ 2`, the mean of `ω_1` over `S_h ∩ M_n` is
`log n + C_1(S_h, 1) + O(1/n)` with `C_1(S_h, 1) = B_1 - T_h`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1, Equation (4) (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) :
    (fun n : ℕ => hFreeMoment F h 1 1 n -
        (Real.log n + (functionFieldMertensConstant F - hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => 1 / (n : ℝ))

/-- Theorem 1, second moment: for `h ≥ 2` and every `ε > 0`, the mean of `ω_1^2` over
`S_h ∩ M_n` is `log^2 n + C_2 log n + C_3 + O_ε(n^{ε-1})` with `C_2 = 2(B_1 - T_h) + 1` and
`C_3 = B_1^2 + B_1 - ζ(2) - U_h + T_h^2 - (2B_1 + 1) T_h`, `ζ(2) = π^2/6`. The printed error
`O_ε(q^n/n^{1-ε})` is the error of the unnormalized sum in the paper's proof; divided by
`|S_h ∩ M_n| = q^n/ζ_q(h)` it is `O_ε(n^{ε-1})`, the order the paper's remark (an extra factor
`n^ε` over the first moment's `O(1/n)`) and its variance formula state.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1, Equation (5) (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ε : ℝ)
    (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h 1 2 n -
        (Real.log n ^ 2 +
          (2 * (functionFieldMertensConstant F - hFreeOmegaOneSum F h) + 1) * Real.log n +
          (functionFieldMertensConstant F ^ 2 + functionFieldMertensConstant F - Real.pi ^ 2 / 6 -
            hFreeOmegaOneSqSum F h + hFreeOmegaOneSum F h ^ 2 -
            (2 * functionFieldMertensConstant F + 1) * hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 1, variance: for `h ≥ 2` and every `ε > 0`, the variance of `ω_1` over
`S_h ∩ M_n` is `log n + C_4(S_h, 1) + O_ε(n^{ε-1})` with
`C_4(S_h, 1) = B_1 - ζ(2) - U_h - T_h`, `ζ(2) = π^2/6`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 1 (`integers-2025-A9-thm-1`). -/
public theorem_wanted omegaOne_hFree_variance_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ε : ℝ)
    (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h 1 2 n - hFreeMoment F h 1 1 n ^ 2 -
        (Real.log n + (functionFieldMertensConstant F - Real.pi ^ 2 / 6 -
          hFreeOmegaOneSqSum F h - hFreeOmegaOneSum F h)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 3, first moment: for `1 < k < h` and every `ε > 0`, the mean of `ω_k` over
`S_h ∩ M_n` is `S_{h,k} + O_ε(q^{n/k - n + εn})`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3, Equation (6) (`integers-2025-A9-thm-3`). -/
public theorem_wanted omegaMult_hFree_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hk : 1 < k) (hkh : k < h)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h k 1 n - hFreeOmegaMultSum F h k)
      =O[atTop] (fun n : ℕ => (Fintype.card F : ℝ) ^ ((n : ℝ) / k - n + ε * n))

/-- Theorem 3, second moment: for `1 < k < h` and every `ε > 0`, the mean of `ω_k^2` over
`S_h ∩ M_n` is `S_{h,k}^2 - ∑_P a_P^2 + S_{h,k} + O_ε(q^{n/k - n + εn})`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 3, Equation (7) (`integers-2025-A9-thm-3`). -/
public theorem_wanted omegaMult_hFree_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hk : 1 < k) (hkh : k < h)
    (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => hFreeMoment F h k 2 n -
        (hFreeOmegaMultSum F h k ^ 2 - hFreeOmegaMultSqSum F h k + hFreeOmegaMultSum F h k))
      =O[atTop] (fun n : ℕ => (Fintype.card F : ℝ) ^ ((n : ℝ) / k - n + ε * n))

/-- Lemma 1 (corrected version of Lalín and Zhang's Lemma 3.2): let `G_n`, `f` be analytic
on a common disk around `1` with `G_n(z) = f(z) n^{z-1} + O(n^{Re z - 2})` uniformly there.
Then for every `k` and `ε > 0`, `G_n^{(k)}(1) = ∂_z^k (f(z) n^{z-1})|_{z=1} + O_ε(n^{ε-1})`
(Equation (11) is `k = 1`). The paper's "analytic at `z = 1`" with an error term "in a
neighborhood of `z = 1`" is read as analyticity on a fixed disk on which the bound holds with
one constant for all `n ≥ 1`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 1 (`integers-2025-A9-lem-1`). -/
public theorem_wanted iteratedDeriv_sub_isBigO_of_uniform_approx
    (G : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) (Metric.ball 1 r))
    (hf : AnalyticOnNhd ℂ f (Metric.ball 1 r))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (1 : ℂ) r,
      ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ C * (n : ℝ) ^ (z.re - 2))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => iteratedDeriv k (G n) 1 -
        iteratedDeriv k (fun z => f z * (n : ℂ) ^ (z - 1)) 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 10 (quoted Selberg–Delange-type theorem): let `C(u, z) = B(u, z) Z_q(u)^z` with
`Z_q(u) = (1 - qu)^{-1}`, i.e. `C_z(n) = ∑_{a ≤ n} B_z(a) q^{n-a} (z)_{n-a}/(n-a)!`
(`(z)_m` the rising factorial; these are the coefficients of `(1 - qu)^{-z}`). If
`∑_n |B_z(n)| n^{2A+2}/q^n ≪_A 1` uniformly for `|z| ≤ A`, then uniformly for `|z| ≤ A` and
`n ≥ 1`, `C_z(n) = q^n n^{z-1} B(1/q, z)/Γ(z) + O_A(q^n n^{Re z - 2})`. The paper's `q` is the
size of the field; the statement is for any real `q > 1`. The weight is `(n+1)^{2A+2}` instead
of `n^{2A+2}`: equivalent for `n ≥ 1`, and it also bounds `B_z(0)` uniformly, without which the
conclusion fails (unbounded `B_z(0)` along `z → 2` with `A = 2`).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 10 (`integers-2025-A9-thm-10`). -/
public theorem_wanted selbergDelange_functionField
    (q : ℝ) (hq : 1 < q) (A : ℝ) (hA : 0 < A) (B Cz : ℂ → ℕ → ℂ)
    (hC : ∀ z n, Cz z n = ∑ a ∈ Finset.range (n + 1),
      B z a * (q : ℂ) ^ (n - a) * (ascPochhammer ℂ (n - a)).eval z / ((n - a).factorial : ℂ))
    (hB : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ A →
      Summable (fun n : ℕ => ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ n) ∧
        ∑' n : ℕ, ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ n ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 1 ≤ n →
      ‖Cz z n - (q : ℂ) ^ n * (n : ℂ) ^ (z - 1) / Complex.Gamma z *
          ∑' a : ℕ, B z a / (q : ℂ) ^ a‖ ≤ K * q ^ n * (n : ℝ) ^ (z.re - 2)

/-- Theorem 11 (quoted extension to `Z_q(u^h)`): let `C(u, z) = B(u, z) Z_q(u^h)^z`, i.e.
`C_z(n) = ∑ B_z(a) q^m (z)_m/m!` over `a ≤ n` with `h ∣ n - a`, `m = (n - a)/h`. If
`∑_n |B_z(n)| n^{2A+2}/q^{n/h} ≪_A 1` uniformly for `|z| ≤ A`, then uniformly for `|z| ≤ A`
and `n ≥ 1`, `C_z(n) = q^{n/h} n^{z-1}/(h^z Γ(z)) ∑_{j<h} ξ^{jn} B((q^{1/h} ξ^j)^{-1}, z)
+ O_A(q^{n/h} n^{Re z - 2})` for `ξ` a primitive `h`-th root of unity; any real `q > 1`. As in
Theorem 10 the weight is `(n+1)^{2A+2}`, so that `B_z(0)` is bounded uniformly.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 11 (`integers-2025-A9-thm-11`). -/
public theorem_wanted selbergDelange_functionField_pow
    (q : ℝ) (hq : 1 < q) (h : ℕ) (hh : 1 ≤ h) (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h)
    (A : ℝ) (hA : 0 < A) (B Cz : ℂ → ℕ → ℂ)
    (hC : ∀ z n, Cz z n = ∑ a ∈ (Finset.range (n + 1)).filter (fun a => h ∣ n - a),
      B z a * (q : ℂ) ^ ((n - a) / h) * (ascPochhammer ℂ ((n - a) / h)).eval z /
        (((n - a) / h).factorial : ℂ))
    (hB : ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ A →
      Summable (fun n : ℕ => ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ ((n : ℝ) / h)) ∧
        ∑' n : ℕ, ‖B z n‖ * ((n : ℝ) + 1) ^ (2 * A + 2) / q ^ ((n : ℝ) / h) ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 1 ≤ n →
      ‖Cz z n - ((q ^ ((n : ℝ) / h) : ℝ) : ℂ) * (n : ℂ) ^ (z - 1) /
          ((h : ℂ) ^ z * Complex.Gamma z) *
          ∑ j ∈ Finset.range h, ξ ^ (j * n) *
            ∑' a : ℕ, B z a * (((q ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j)⁻¹ ^ a‖
        ≤ K * q ^ ((n : ℝ) / h) * (n : ℝ) ^ (z.re - 2)


/-- The coefficient `B_z(n)` of `u^n` in `B_{1,S_h}(u, z) = Z_q(u)^{-z} C_{1,S_h}(u, z)`, where
`C_{1,S_h}(u, z) = ∑_{f ∈ S_h} z^{ω_1(f)} u^{deg f}` and `Z_q(u)^{-z} = (1 - qu)^z` has
coefficients `q^m (-z)_m / m!` (`(x)_m` the rising factorial): the Cauchy product of the two
coefficient sequences.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 3.1 (definition preceding Lemma 2). -/
public noncomputable def hFreeOmegaOneB (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (n + 1),
    (∑ f ∈ (fixedDegreeMonic F a).filter (· ∈ hFree F h), z ^ omegaMult F 1 f) *
      (Fintype.card F : ℂ) ^ (n - a) * (ascPochhammer ℂ (n - a)).eval (-z) /
        ((n - a).factorial : ℂ)

/-- `B_z(0) = 1` for `B_{1,S_h}`, `h > 0`: the only monic polynomial of degree `0` is `1`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 3.1 (definition preceding Lemma 2). -/
public theorem hFreeOmegaOneB_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (hh : 0 < h) (z : ℂ) : hFreeOmegaOneB F h z 0 = 1 := by
  simp only [hFreeOmegaOneB, zero_add, Finset.range_one, Finset.sum_singleton, fixedDegreeMonic_zero]
  rw [Finset.filter_singleton]
  simp [one_mem_hFree F h hh, omegaMult_one]

/-- The coefficient `B_z(n)` of `u^n` in `B_{h,N_h}(u, z) = Z_q(u^h)^{-z} C_{h,N_h}(u, z)`, where
`C_{h,N_h}(u, z) = ∑_{f ∈ N_h} z^{ω_h(f)} u^{deg f}` and `Z_q(u^h)^{-z} = (1 - qu^h)^z` has
coefficient `q^m (-z)_m / m!` at `u^{hm}`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4.1 (definition preceding Lemma 4). -/
public noncomputable def hFullOmegaHB (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range (n + 1)).filter (fun a => h ∣ n - a),
    (∑ f ∈ (fixedDegreeMonic F a).filter (· ∈ hFull F h), z ^ omegaMult F h f) *
      (Fintype.card F : ℂ) ^ ((n - a) / h) * (ascPochhammer ℂ ((n - a) / h)).eval (-z) /
        (((n - a) / h).factorial : ℂ)

/-- `B_z(0) = 1` for `B_{h,N_h}`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4.1 (definition preceding Lemma 4). -/
public theorem hFullOmegaHB_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (z : ℂ) : hFullOmegaHB F h z 0 = 1 := by
  simp only [hFullOmegaHB, zero_add, Finset.range_one, Finset.filter_singleton, Nat.sub_self,
    dvd_zero, ite_true, Finset.sum_singleton, fixedDegreeMonic_zero]
  simp [one_mem_hFull F h, omegaMult_one]

/-- Lemma 2: for `h ≥ 2`, `A`, and `σ > 1/2` there is a constant `c` with
`∑_{0 ≤ a ≤ n} |B_z(a)| q^{-σa} ≤ c` for all `|z| ≤ A` and `n ≥ 2`, where `B_z(a)` are the
coefficients of `B_{1,S_h}(u, z)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 2 (`integers-2025-A9-lem-2`). -/
public theorem_wanted hFreeOmegaOneB_weighted_sum_bounded
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (A σ : ℝ)
    (hσ : 1 / 2 < σ) :
    ∃ c : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 2 ≤ n →
      ∑ a ∈ Finset.range (n + 1),
        ‖hFreeOmegaOneB F h z a‖ / (Fintype.card F : ℝ) ^ (σ * a) ≤ c

/-- Lemma 4: for `h ≥ 2`, `A`, and `σ > 1/(h+1)` there is a constant `c` with
`∑_{0 ≤ a ≤ n} |B_z(a)| q^{-σa} ≤ c` for all `|z| ≤ A` and `n ≥ 2`, where `B_z(a)` are the
coefficients of `B_{h,N_h}(u, z)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 4 (`integers-2025-A9-lem-4`). -/
public theorem_wanted hFullOmegaHB_weighted_sum_bounded
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (A σ : ℝ)
    (hσ : 1 / ((h : ℝ) + 1) < σ) :
    ∃ c : ℝ, ∀ z : ℂ, ‖z‖ ≤ A → ∀ n : ℕ, 2 ≤ n →
      ∑ a ∈ Finset.range (n + 1),
        ‖hFullOmegaHB F h z a‖ / (Fintype.card F : ℝ) ^ (σ * a) ≤ c

/-- `q^{1/h} ξ^j`, with the real `h`-th root of `q`; its inverses are the poles
`u = (q^{1/h} ξ_h^j)^{-1}` of `Z_q(u^h)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4. -/
public noncomputable def hFullRoot (F : Type*) [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) : ℂ :=
  (((Fintype.card F : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j

/-- Unfolding `q^{1/h} ξ^j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 4. -/
public theorem hFullRoot_eq (F : Type*) [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullRoot F h ξ j = (((Fintype.card F : ℝ) ^ ((1 : ℝ) / h) : ℝ) : ℂ) * ξ ^ j := rfl

/-- `H_{N_h,S_ℓ}(u) = ∏_P (1 + (x^{h+1} - x^ℓ - x^{2h} + x^{h+ℓ})/(1 - x))` with `x = u^{deg P}`,
the product over monic irreducible `P` (Equation (53)).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (53). -/
public noncomputable def hFullFreeEulerH (F : Type*) [Field F] [Fintype F] (h ℓ : ℕ) (u : ℂ) :
    ℂ :=
  ∏' P : monicIrreducible F,
    (1 + ((u ^ (P : Polynomial F).natDegree) ^ (h + 1) - (u ^ (P : Polynomial F).natDegree) ^ ℓ -
        (u ^ (P : Polynomial F).natDegree) ^ (2 * h) +
        (u ^ (P : Polynomial F).natDegree) ^ (h + ℓ)) / (1 - u ^ (P : Polynomial F).natDegree))

/-- Unfolding `H_{N_h,S_ℓ}`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (53). -/
public theorem hFullFreeEulerH_eq (F : Type*) [Field F] [Fintype F] (h ℓ : ℕ) (u : ℂ) :
    hFullFreeEulerH F h ℓ u = ∏' P : monicIrreducible F,
      (1 + ((u ^ (P : Polynomial F).natDegree) ^ (h + 1) - (u ^ (P : Polynomial F).natDegree) ^ ℓ -
          (u ^ (P : Polynomial F).natDegree) ^ (2 * h) +
          (u ^ (P : Polynomial F).natDegree) ^ (h + ℓ)) /
        (1 - u ^ (P : Polynomial F).natDegree)) := rfl

/-- Lemma 5, Equation (51): for `0 < h < ℓ`, a primitive `h`-th root of unity `ξ` and `ε > 0`,
`|N_h ∩ M_n ∩ S_ℓ| = (q^{n/h}/h) ∑_{j<h} ξ^{jn} H_{N_h,S_ℓ}((q^{1/h}ξ^j)^{-1})
+ O_ε(q^{n/(h+1) + εn})` for `n ≥ ℓ`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (51) (`integers-2025-A9-lem-5`). -/
public theorem_wanted card_hFull_hFree_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h ℓ : ℕ) (hh : 0 < h) (hhℓ : h < ℓ)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, ℓ ≤ n →
      ‖((((fixedDegreeMonic F n).filter fun f => f ∈ hFull F h ∧ f ∈ hFree F ℓ).card : ℂ)) -
          (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) *
            ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullFreeEulerH F h ℓ (hFullRoot F h ξ j)⁻¹‖ ≤
        C * (Fintype.card F : ℝ) ^ ((n : ℝ) / (h + 1) + ε * n)

/-- Lemma 5, Equation (52): for a fixed monic irreducible `P₀`, the count of
`f ∈ N_h ∩ M_n ∩ S_ℓ` coprime to `P₀` is
`(q^{n/h}/h) ∑_{j<h} ξ^{jn} H_{N_h,S_ℓ}((q^{1/h}ξ^j)^{-1}) (1 - y_j)/(1 - y_j + y_j^h - y_j^ℓ)
+ O_ε(q^{n/(h+1) + εn})` with `y_j = (q^{1/h}ξ^j)^{-deg P₀}`; the constant may depend on `P₀`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 5, Equation (52) (`integers-2025-A9-lem-5`). -/
public theorem_wanted card_hFull_hFree_coprime_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h ℓ : ℕ) (hh : 0 < h) (hhℓ : h < ℓ)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (P₀ : Polynomial F) (hP₀ : P₀ ∈ monicIrreducible F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, ℓ ≤ n →
      ‖((((fixedDegreeMonic F n).filter fun f =>
            f ∈ hFull F h ∧ f ∈ hFree F ℓ ∧ IsCoprime f P₀).card : ℂ)) -
          (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) *
            ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullFreeEulerH F h ℓ (hFullRoot F h ξ j)⁻¹ *
              ((1 - (hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) /
                (1 - (hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree +
                  ((hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) ^ h -
                  ((hFullRoot F h ξ j)⁻¹ ^ P₀.natDegree) ^ ℓ))‖ ≤
        C * (Fintype.card F : ℝ) ^ ((n : ℝ) / (h + 1) + ε * n)

/-- The `j`-th moment of `ω_k` over the `h`-full monic polynomials of degree `n`,
`|N_h ∩ M_n|^{-1} ∑_{f ∈ N_h ∩ M_n} ω_k(f)^j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public noncomputable def hFullMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : ℝ :=
  (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFull F h), (omegaMult F k f : ℝ) ^ j) /
    (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℝ)

/-- Unfolding the `h`-full moment.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public theorem hFullMoment_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h k j n : ℕ) : hFullMoment F h k j n =
      (∑ f ∈ (fixedDegreeMonic F n).filter (· ∈ hFull F h), (omegaMult F k f : ℝ) ^ j) /
        (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℝ) := rfl

/-- `K(P, h, j) = (1 - y)/(|P|(1 - y) + 1)` with `y = (q^{1/h} ξ^j)^{-deg P}`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (notation preceding Theorem 5). -/
public noncomputable def hFullK (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ)
    (P : Polynomial F) : ℂ :=
  (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) /
    ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) + 1)

/-- Unfolding `K(P, h, j)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (notation preceding Theorem 5). -/
public theorem hFullK_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ)
    (P : Polynomial F) : hFullK F h ξ j P = (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) /
      ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ P.natDegree) + 1) := rfl

/-- `Π_j = ∏_P (1 - 1/|P|)(1 + 1/(|P|(1 - (q^{1/h}ξ^j)^{-deg P})))`, the product over monic
irreducible `P` taken factor by factor (Equation (46)).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (asymptotic for `|N_h ∩ M_n|` preceding Theorem 5). -/
public noncomputable def hFullEulerProduct (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∏' P : monicIrreducible F, (1 - 1 / (polyNorm F P : ℂ)) *
    (1 + 1 / ((polyNorm F P : ℂ) * (1 - (hFullRoot F h ξ j)⁻¹ ^ (P : Polynomial F).natDegree)))

/-- Unfolding `Π_j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Section 1 (asymptotic for `|N_h ∩ M_n|` preceding Theorem 5). -/
public theorem hFullEulerProduct_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullEulerProduct F h ξ j = ∏' P : monicIrreducible F,
      (1 - 1 / (polyNorm F P : ℂ)) *
        (1 + 1 / ((polyNorm F P : ℂ) *
          (1 - (hFullRoot F h ξ j)⁻¹ ^ (P : Polynomial F).natDegree))) := rfl

/-- The weighted combination
`|N_h ∩ M_n|^{-1} (q^{n/h}/h) ∑_{j<h} ξ^{jn} Π_j X_j` that carries every `n`-dependent constant
in Theorems 5 and 7.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public noncomputable def hFullWeightedMean (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (ξ : ℂ) (n : ℕ) (X : ℕ → ℂ) : ℂ :=
  (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) /
      (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℂ) *
    ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullEulerProduct F h ξ j * X j

/-- Unfolding the weighted combination.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorems 5 and 7. -/
public theorem hFullWeightedMean_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h : ℕ) (ξ : ℂ) (n : ℕ) (X : ℕ → ℂ) : hFullWeightedMean F h ξ n X =
      (((Fintype.card F : ℝ) ^ ((n : ℝ) / h) / h : ℝ) : ℂ) /
          (((fixedDegreeMonic F n).filter (· ∈ hFull F h)).card : ℂ) *
        ∑ j ∈ Finset.range h, ξ ^ (j * n) * hFullEulerProduct F h ξ j * X j := rfl

/-- `κ_j = ∑_P (K(P, h, j) - 1/|P|)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public noncomputable def hFullKSum (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, (hFullK F h ξ j P - 1 / (polyNorm F P : ℂ))

/-- Unfolding `κ_j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public theorem hFullKSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullKSum F h ξ j =
      ∑' P : monicIrreducible F, (hFullK F h ξ j P - 1 / (polyNorm F P : ℂ)) := rfl

/-- `∑_P K(P, h, j)^2`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public noncomputable def hFullKSqSum (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, hFullK F h ξ j P ^ 2

/-- Unfolding `∑_P K(P, h, j)^2`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5. -/
public theorem hFullKSqSum_eq (F : Type*) [Field F] [Fintype F] (h : ℕ) (ξ : ℂ) (j : ℕ) :
    hFullKSqSum F h ξ j = ∑' P : monicIrreducible F, hFullK F h ξ j P ^ 2 := rfl

/-- `∑_P b_P` with `b_P = |P| (q^{1/h}ξ^j)^{-k deg P} K(P, h, j)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public noncomputable def hFullOmegaMultSum (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, (polyNorm F P : ℂ) *
    (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P

/-- Unfolding `∑_P b_P`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public theorem hFullOmegaMultSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullOmegaMultSum F h k ξ j = ∑' P : monicIrreducible F, (polyNorm F P : ℂ) *
      (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P := rfl

/-- `∑_P b_P^2` with `b_P = |P| (q^{1/h}ξ^j)^{-k deg P} K(P, h, j)`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public noncomputable def hFullOmegaMultSqSum (F : Type*) [Field F] [Fintype F] (h k : ℕ)
    (ξ : ℂ) (j : ℕ) : ℂ :=
  ∑' P : monicIrreducible F, ((polyNorm F P : ℂ) *
    (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P) ^ 2

/-- Unfolding `∑_P b_P^2`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7. -/
public theorem hFullOmegaMultSqSum_eq (F : Type*) [Field F] [Fintype F] (h k : ℕ) (ξ : ℂ)
    (j : ℕ) : hFullOmegaMultSqSum F h k ξ j = ∑' P : monicIrreducible F, ((polyNorm F P : ℂ) *
      (hFullRoot F h ξ j)⁻¹ ^ (k * (P : Polynomial F).natDegree) * hFullK F h ξ j P) ^ 2 := rfl

/-- Theorem 5, Equation (8): for `h ≥ 2`, a primitive `h`-th root of unity `ξ` and `ε > 0`, the
mean of `ω_h` over `N_h ∩ M_n` is `log(n/h) + C_1(N_h, h) + O_ε(n^{ε-1})` with
`C_1(N_h, h) = B_1 + |N_h ∩ M_n|^{-1} (q^{n/h}/h) ∑_j ξ^{jn} Π_j κ_j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5, Equation (8) (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 1 n : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) + (functionFieldMertensConstant F : ℂ) +
          hFullWeightedMean F h ξ n (hFullKSum F h ξ)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 5, Equation (9), in the reading of the paper's proof: the mean of `ω_h^2` over
`N_h ∩ M_n` is `log^2(n/h) + C_2 log(n/h) + C_3 + O_ε(n^{ε-1})` with
`C_2 = 2B_1 + 1 + 2W(κ)` and `C_3 = B_1^2 + B_1 - ζ(2) + W(-∑_P K^2 + κ^2 + (2B_1 + 1)κ)`,
where `W(X) = |N_h ∩ M_n|^{-1} (q^{n/h}/h) ∑_j ξ^{jn} Π_j X_j` and `ζ(2) = π^2/6`. The printed
`C_3` has `-W(∑_P K^2 + κ^2 + (2B_1 + 1)κ)`, which contradicts the final display of the proof
(page 29) and the printed variance.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5, Equation (9) (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 2 n : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) ^ 2 +
          (2 * (functionFieldMertensConstant F : ℂ) + 1 +
            2 * hFullWeightedMean F h ξ n (hFullKSum F h ξ)) * (Real.log ((n : ℝ) / h) : ℂ) +
          ((functionFieldMertensConstant F : ℂ) ^ 2 + (functionFieldMertensConstant F : ℂ) -
              (Real.pi : ℂ) ^ 2 / 6 +
            hFullWeightedMean F h ξ n (fun j => -hFullKSqSum F h ξ j + hFullKSum F h ξ j ^ 2 +
              (2 * (functionFieldMertensConstant F : ℂ) + 1) * hFullKSum F h ξ j))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 5, variance: the variance of `ω_h` over `N_h ∩ M_n` is
`log(n/h) + B_1 - ζ(2) + W(-∑_P K^2 + κ^2 + κ) - W(κ)^2 + O_ε(n^{ε-1})`, with `W` as in
`omegaH_hFull_secondMoment_asymptotic`. The printed display writes `ω_1` for `ω_h` in the
definition of the variance and omits the factor `q^{n/h}/h` in both weighted sums; both are
restored as in Equations (8) and (9), from which the paper derives the variance.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 5 (`integers-2025-A9-thm-5`). -/
public theorem_wanted omegaH_hFull_variance_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h : ℕ) (hh : 2 ≤ h) (ξ : ℂ)
    (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h h 2 n - hFullMoment F h h 1 n ^ 2 : ℝ) : ℂ) -
        ((Real.log ((n : ℝ) / h) : ℂ) + (functionFieldMertensConstant F : ℂ) -
            (Real.pi : ℂ) ^ 2 / 6 +
          hFullWeightedMean F h ξ n
            (fun j => -hFullKSqSum F h ξ j + hFullKSum F h ξ j ^ 2 + hFullKSum F h ξ j) -
          hFullWeightedMean F h ξ n (hFullKSum F h ξ) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1))

/-- Theorem 7, first moment: for `2 ≤ h < k`, a primitive `h`-th root of unity `ξ` and `ε > 0`,
the mean of `ω_k` over `N_h ∩ M_n` is `W(∑_P b_P) + O_ε(q^{-n/(h(h+1)) + εn})`, with
`b_P = |P|(q^{1/h}ξ^j)^{-k deg P} K(P, h, j)` and
`W(X) = |N_h ∩ M_n|^{-1} (q^{n/h}/h) ∑_j ξ^{jn} Π_j X_j`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7 (`integers-2025-A9-thm-7`). -/
public theorem_wanted omegaMult_hFull_mean_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h k 1 n : ℝ) : ℂ) -
        hFullWeightedMean F h ξ n (hFullOmegaMultSum F h k ξ))
      =O[atTop] (fun n : ℕ =>
        (Fintype.card F : ℝ) ^ (-((n : ℝ) / (h * (h + 1))) + ε * n))

/-- Theorem 7, second moment, in the reading of the paper's proof: the mean of `ω_k^2` over
`N_h ∩ M_n` is `W((∑_P b_P)^2 - ∑_P b_P^2 + ∑_P b_P) + O_ε(q^{-n/(h(h+1)) + εn})`. The printed
statement has `∑_P b_P^2 - (∑_P b_P)^2` with the signs swapped, contradicting the computation of
`∂²B_{k,N_h}/∂z²` at the end of the proof (page 31).

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Theorem 7 (`integers-2025-A9-thm-7`). -/
public theorem_wanted omegaMult_hFull_secondMoment_asymptotic
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (h k : ℕ) (hh : 2 ≤ h) (hhk : h < k)
    (ξ : ℂ) (hξ : IsPrimitiveRoot ξ h) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => ((hFullMoment F h k 2 n : ℝ) : ℂ) -
        hFullWeightedMean F h ξ n (fun j => hFullOmegaMultSum F h k ξ j ^ 2 -
          hFullOmegaMultSqSum F h k ξ j + hFullOmegaMultSum F h k ξ j))
      =O[atTop] (fun n : ℕ =>
        (Fintype.card F : ℝ) ^ (-((n : ℝ) / (h * (h + 1))) + ε * n))

end

end MetaMathlibExt

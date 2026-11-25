/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section

/-!
# Artin L-functions

This module defines a raw local determinant factor and formal Euler product from
supplied decomposition, inertia, and Frobenius data for a finite group.
Constructing that arithmetic local data from a number field and proving
absolute convergence for `Re s > 1` are separate problems not asserted here.

The definitions follow the Artin L-function setup in
[K. Krishnamoorthy, *Moments of non-normal number fields -- II*][krishnamoorthy2024],
arXiv:2310.09768, Section 2, § "Artin L functions", Equation
"Artin L function definition" (lines 223-227):
`L(s,ξ) = ∏_{v<∞} det(Id - p^{-s} ξ(σ_w) | V^{I_w})^{-1}` where
`G = Gal(L/ℚ)`, `G_w` is the decomposition subgroup at `w|v`, `I_w ⊲ G_w` is
inertia, `σ_w ∈ G_w/I_w` is Frobenius, and `ξ : G → Aut(V)` is a
finite-dimensional complex representation acting on inertia invariants
`V^{I_w}`.

## Main definitions

* `Representation.ArtinLocalDatum`: decomposition subgroup `G_w ≤ G`, its
  normal inertia subgroup `I_w ≤ G_w`, and Frobenius `σ_w ∈ G_w/I_w` at a
  rational prime `p`.
* `Representation.artinLocalFactorRaw`: the totalized determinant inverse
  `det(Id - p^{-s} ρ(σ_w) | V^{I_w})^{-1}`.
* `Representation.ArtinLocalFactorRegular`: the denominator-nonvanishing domain.
* `Representation.artinEulerProductOfLocalData`: the formal `tprod` over supplied data.
* `Representation.HasArtinEulerProduct`: the explicit convergence/value interface.
* `Representation.HasNonzeroArtinEulerProduct`: convergence to a genuine nonzero value.

## References

[krishnamoorthy2024]: https://doi.org/10.1007/s00605-024-02050-1
-/

namespace Representation

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- **Artin local datum.** For a finite group $G$, an Artin local datum consists of a subgroup
$D \le G$ (the decomposition group), a normal subgroup $I$ of $D$ (the inertia group), and an
element $\sigma$ of the quotient group $D/I$ (the Frobenius coset).

In the arithmetic application, $L/\mathbb{Q}$ is a finite Galois extension with
$G = \mathrm{Gal}(L/\mathbb{Q})$, $D$ is the decomposition group at a place $w$ of $L$ above a
prime $p$, $I$ is its inertia group and $\sigma$ is the Frobenius. A complex representation of
$G$ restricted to $D$ then gives an action of $D/I$ on the $I$-invariant vectors, on which
$\sigma$ acts as the local operator. The definition does not require the data to arise this way. -/
structure ArtinLocalDatum (G : Type u) [Group G] [Finite G] where
  decomposition : Subgroup G
  inertia : Subgroup decomposition
  [isNormal : inertia.Normal]
  frobenius : decomposition ⧸ inertia

attribute [instance] ArtinLocalDatum.isNormal

/-- **Artin local denominator.** Let $\rho$ be a representation of a finite group $G$ on a
finite-dimensional complex vector space $V$, let $p$ be a prime, let $(D, I, \sigma)$ be an Artin
local datum for $G$, and let $s \in \mathbb{C}$. Let $V^{I}$ be the subspace of vectors fixed by
$\rho(I)$, on which $D/I$ acts, and let $\rho(\sigma)$ be the action of $\sigma$ on $V^{I}$. The
Artin local denominator is

$$\det\left(\mathrm{id} - p^{-s}\,\rho(\sigma) \mid V^{I}\right).$$
-/
noncomputable def artinLocalDenominator (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : ℂ :=
  LinearMap.det
    (LinearMap.id - ((p.1 : ℂ) ^ (-s)) •
      ((Representation.quotientToInvariants
        (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
        d.inertia) d.frobenius))

/-- **Regularity of the Artin local factor.** Let $\rho$ be a representation of a finite group $G$
on a finite-dimensional complex vector space $V$, let $p$ be a prime, let $d$ be an Artin local
datum for $G$, and let $s \in \mathbb{C}$. The Artin local factor of $\rho$ at $p$, $d$ is regular
at $s$ when the Artin local denominator of $\rho$ at $p$, $d$ and $s$ is nonzero, that is, when
the local factor has no pole at $s$. -/
def ArtinLocalFactorRegular (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : Prop :=
  artinLocalDenominator ρ p d s ≠ 0

/-- **Artin local factor.** Let $\rho$ be a representation of a finite group $G$ on a
finite-dimensional complex vector space $V$, let $p$ be a prime, let $(D, I, \sigma)$ be an Artin
local datum for $G$, and let $s \in \mathbb{C}$. Let $V^{I}$ be the subspace of vectors fixed by
$\rho(I)$ and $\rho(\sigma)$ the induced action of $\sigma \in D/I$ on it. The Artin local factor
is the inverse of the Artin local denominator,

$$\det\left(\mathrm{id} - p^{-s}\,\rho(\sigma) \mid V^{I}\right)^{-1},$$

with the value $0$ when the denominator vanishes.

Where the denominator vanishes the true factor has a pole; the regularity condition picks out
the $s$ at which this value is a genuine finite Euler factor. -/
noncomputable def artinLocalFactorRaw (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) : ℂ :=
  (artinLocalDenominator ρ p d s)⁻¹

/-- **Euler product of Artin local factors.** Let $\rho$ be a representation of a finite group
$G$ on a finite-dimensional complex vector space $V$, and suppose that for every prime $p$ an Artin
local datum $d_p$ for $G$ is given. For $s \in \mathbb{C}$, this is the product over all primes
$p$ of the Artin local factors of $\rho$ at $p$, $d_p$ and $s$, taken as an unconditional infinite
product (the limit of the products over finite sets of primes); when this product does not
converge, the value is $1$ by convention.

The data need not come from the places of a number field, and no independence of the choice of
place above $p$ is asserted. -/
noncomputable def artinEulerProductOfLocalData (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s : ℂ) : ℂ :=
  ∏' p, artinLocalFactorRaw ρ p (localData p) s

/-- **Convergent Artin Euler product.** Let $\rho$ be a representation of a finite group $G$ on a
finite-dimensional complex vector space $V$, let $d_p$ be an Artin local datum for $G$ for every
prime $p$, and let $s, z \in \mathbb{C}$. The Artin Euler product of $\rho$ and $(d_p)$ has value
$z$ at $s$ when the products of the Artin local factors of $\rho$ at $p$, $d_p$ and $s$ over
finite sets of primes $p$ converge to $z$ as the finite set grows to all primes (unconditional
convergence). The value $z = 0$ is allowed. -/
def HasArtinEulerProduct (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ) : Prop :=
  HasProd (fun p => artinLocalFactorRaw ρ p (localData p) s) z

/-- **Nonzero convergent Artin Euler product.** Let $\rho$ be a representation of a finite group
$G$ on a finite-dimensional complex vector space $V$, let $d_p$ be an Artin local datum for $G$ for
every prime $p$, and let $s, z \in \mathbb{C}$. The Artin Euler product of $\rho$ and $(d_p)$ has
nonzero value $z$ at $s$ when it has value $z$ at $s$ and $z \ne 0$.

In particular every local factor is then regular at $s$: a factor whose denominator vanishes has
value $0$ and would force the product to be $0$, so this describes a genuine finite Euler-product
value rather than a pole. -/
def HasNonzeroArtinEulerProduct (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ) : Prop :=
  HasArtinEulerProduct ρ localData s z ∧ z ≠ 0

theorem artinEulerProductOfLocalData_eq_of_hasProd (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ)
    (h : HasArtinEulerProduct ρ localData s z) :
    artinEulerProductOfLocalData ρ localData s = z :=
  h.tprod_eq

theorem HasNonzeroArtinEulerProduct.hasArtinEulerProduct
    {ρ : Representation ℂ G V} [Module.Free ℂ V] [Module.Finite ℂ V]
    {localData : Nat.Primes → ArtinLocalDatum G} {s z : ℂ}
    (h : HasNonzeroArtinEulerProduct ρ localData s z) :
    HasArtinEulerProduct ρ localData s z :=
  h.1

theorem HasNonzeroArtinEulerProduct.ne_zero
    {ρ : Representation ℂ G V} [Module.Free ℂ V] [Module.Finite ℂ V]
    {localData : Nat.Primes → ArtinLocalDatum G} {s z : ℂ}
    (h : HasNonzeroArtinEulerProduct ρ localData s z) : z ≠ 0 :=
  h.2

theorem artinEulerProductOfLocalData_eq_of_hasNonzeroProd
    (ρ : Representation ℂ G V) [Module.Free ℂ V] [Module.Finite ℂ V]
    (localData : Nat.Primes → ArtinLocalDatum G) (s z : ℂ)
    (h : HasNonzeroArtinEulerProduct ρ localData s z) :
    artinEulerProductOfLocalData ρ localData s = z :=
  h.hasArtinEulerProduct.tprod_eq

@[simp]
theorem artinLocalFactorRaw_zero (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) :
    artinLocalFactorRaw ρ p d 0 =
      (LinearMap.det (LinearMap.id -
        ((Representation.quotientToInvariants
          (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
          d.inertia) d.frobenius)))⁻¹ := by
  simp [artinLocalFactorRaw, artinLocalDenominator]

@[simp]
theorem artinLocalFactorRaw_eq_zero_iff (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) :
    artinLocalFactorRaw ρ p d s = 0 ↔ ¬ArtinLocalFactorRegular ρ p d s := by
  simp [artinLocalFactorRaw, ArtinLocalFactorRegular]

theorem artinLocalFactorRaw_ne_zero (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ) (h : ArtinLocalFactorRegular ρ p d s) :
    artinLocalFactorRaw ρ p d s ≠ 0 := by
  intro hzero
  exact (artinLocalFactorRaw_eq_zero_iff ρ p d s).mp hzero h

theorem HasNonzeroArtinEulerProduct.localFactorRegular
    {ρ : Representation ℂ G V} [Module.Free ℂ V] [Module.Finite ℂ V]
    {localData : Nat.Primes → ArtinLocalDatum G} {s z : ℂ}
    (h : HasNonzeroArtinEulerProduct ρ localData s z) (p : Nat.Primes) :
    ArtinLocalFactorRegular ρ p (localData p) s := by
  by_contra hp
  have hfactor : artinLocalFactorRaw ρ p (localData p) s = 0 :=
    (artinLocalFactorRaw_eq_zero_iff ρ p (localData p) s).2 hp
  have hzero : HasProd (fun q => artinLocalFactorRaw ρ q (localData q) s) 0 :=
    hasProd_zero_of_exists_eq_zero ⟨p, hfactor⟩
  exact h.ne_zero (h.hasArtinEulerProduct.unique hzero)

/-- **Artin local factor when Frobenius acts trivially.** Let $\rho$ be a representation of a
finite group $G$ on a finite-dimensional complex vector space $V$, let $p$ be a prime, let
$(D, I, \sigma)$ be an Artin local datum for $G$, and let $s \in \mathbb{C}$. Let $V^{I}$ be the
subspace of vectors fixed by $\rho(I)$ and $n = \dim V^{I}$. If $\sigma$ acts as the identity on
$V^{I}$, then the Artin local factor of $\rho$ at $p$, $(D, I, \sigma)$ and $s$ equals
$\left((1 - p^{-s})^{n}\right)^{-1}$, where the inverse of $0$ is read as $0$. -/
theorem artinLocalFactorRaw_of_action_eq_id_general (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ)
    (hact : (Representation.quotientToInvariants
      (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
      d.inertia) d.frobenius = LinearMap.id) :
    artinLocalFactorRaw ρ p d s =
      ((1 - (p.1 : ℂ) ^ (-s)) ^ Module.finrank ℂ (invariants
      ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp
        d.inertia.subtype)))⁻¹ := by
  rw [artinLocalFactorRaw, artinLocalDenominator, hact]
  let W := invariants
    ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp
      d.inertia.subtype)
  have hlin : (LinearMap.id : W →ₗ[ℂ] W) -
      (p.1 : ℂ) ^ (-s) • LinearMap.id =
      (1 - (p.1 : ℂ) ^ (-s)) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.1 - (p.1 : ℂ) ^ (-s) • x.1 =
      (1 - (p.1 : ℂ) ^ (-s)) • x.1
    rw [sub_smul, one_smul]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- **Artin local factor of a one-dimensional trivial Frobenius action.** Let $\rho$ be a
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, let $p$ be
a prime, let $(D, I, \sigma)$ be an Artin local datum for $G$, and let $s \in \mathbb{C}$. Let
$V^{I}$ be the subspace of vectors fixed by $\rho(I)$. If $\sigma$ acts as the identity on $V^{I}$
and $V^{I}$ is one-dimensional, then the Artin local factor of $\rho$ at $p$, $(D, I, \sigma)$
and $s$ equals $(1 - p^{-s})^{-1}$, where the inverse of $0$ is read as $0$.

This is the unramified trivial-character case, which gives the local factor of the Riemann zeta
function. -/
theorem artinLocalFactorRaw_of_action_eq_id (ρ : Representation ℂ G V)
    [Module.Free ℂ V] [Module.Finite ℂ V] (p : Nat.Primes)
    (d : ArtinLocalDatum G) (s : ℂ)
    (hact : (Representation.quotientToInvariants
      (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
      d.inertia) d.frobenius = LinearMap.id)
    (hdim : Module.finrank ℂ (invariants
      ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp
        d.inertia.subtype)) = 1) :
    artinLocalFactorRaw ρ p d s = (1 - (p.1 : ℂ) ^ (-s))⁻¹ := by
  rw [artinLocalFactorRaw_of_action_eq_id_general ρ p d s hact, hdim, pow_one]

end Representation

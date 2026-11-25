/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ResidueField.DVR
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Separable
import MathlibExt.RingTheory.AdjoinRoot.LocalMaximal
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Lifting irreducible residue polynomials over a DVR

This file develops the accumulated N211 AdjoinRoot construction: a monic
irreducible residue polynomial is lifted to a finite domain, its coefficient
quotient and residue field are identified, the lifted ring is made local and
then a discrete valuation ring, and finite separable residue extensions are
realized by finite local DVR extensions. These are the D1--D4 and object-
realization prerequisites, not the full categorical N211 equivalence.

Source map: this is ATLAS NumberTheoryI item N211, Theorem 10.13
(Section 10.2), Stage D1, at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`; it is a prerequisite stage and
not the full N211 target. The
[English target is `v1/Atlas/NumberTheoryI/targets.yaml`, lines 1466-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483);
its essential-surjectivity clause says every finite separable residue-field
extension is realized by an unramified extension. The implementation target is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean):
the source construction helper
[`adjoinRoot_dvr_of_irreducible_lift` (lines 349-453)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L349-L453)
and the caller
[`residueFieldFunctor_essential_surjectivity` (lines 1174-1203)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1174-L1203),
which chooses
a primitive element and its monic irreducible separable minimal polynomial
([lines 1187-1193](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1187-L1193))
and then invokes the construction helper
([lines 1196-1198](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1196-L1198)).

The D1 theorem below extracts exactly
[lines 364-377 of the source helper](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L364-L377).
`DVRResidue.exists_monic_lift_adjoinRoot_domain` takes a monic irreducible
polynomial `gbar` over `IsLocalRing.ResidueField A` and returns a monic
`g : A[X]` with exact reduction `g.map (IsLocalRing.residue A) = gbar`, plus
`IsDomain (AdjoinRoot g)` and `Module.Finite A (AdjoinRoot g)`. The proof
chain is: coefficientwise residue surjectivity yields
`gbar ∈ Polynomial.lifts`; `lifts_and_natDegree_eq_and_monic` produces `g`;
the exact reduction transports irreducibility;
`Polynomial.Monic.irreducible_of_irreducible_map`, DVR/UFD
irreducible-to-prime, and `AdjoinRoot.isDomain_of_prime` produce the domain;
`g.Monic.finite_adjoinRoot` gives finiteness.

The source helper's `HenselianLocalRing A` and `gbar.Separable` hypotheses
are unused in this extracted portion and are therefore omitted. The unused
returned natDegree equality is also not exposed. Those omitted hypotheses are not needed for D1
itself. The subsequent sections
provide locality, quotient/residue-field equivalences, the DVR structure, and
the finite-separable object-realization package. They still do not prove the
unramified/étale structure or the full categorical equivalence. Monic plus
irreducible reduction alone need not imply separability, and domain plus
finiteness alone does not imply `Algebra.Etale`.

Stage D2 corresponds exactly to the quotient construction in
[`ResidueFieldFunctor.adjoinRoot_dvr_of_irreducible_lift`, lines
386--407](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L386-L407).
There the source first identifies the maximal ideal of `AdjoinRoot g` with
the image of the coefficient-ring maximal ideal (`e1`), then factors the
residue-field equivalence into

1. `e2`, lines 396--399: quotienting `AdjoinRoot g` coefficientwise gives
   the quotient polynomial ring over `ResidueField A`; and
2. `e3`, lines 401--404: the exact reduction equation
   `g.map (residue A) = gbar` identifies that reduced polynomial with `gbar`.

`adjoinRootQuotientEquivOfMapEq` is precisely the canonical composite
`e2.trans e3`, exposed before the local/DVR step. Its domain is
`AdjoinRoot g` modulo the image of `maximalIdeal A`, its codomain is
`AdjoinRoot gbar`, and `adjoinRootQuotientEquivOfMapEq_mk` records its action
on a polynomial representative: reduce every coefficient and then apply
`AdjoinRoot.mk`. The required reduction equality is the final fact returned
by Stage D1. The source's `e1` (identifying this coefficient quotient with the
actual residue field of `AdjoinRoot g`) is deliberately not claimed here; it
requires the locality/maximal-ideal stage that follows.

Stage D3 supplies exactly that missing local layer. Its primary source is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
at the same commit:

* [`adjoinRoot_isLocalRing_of_irred_map`, lines 211--244](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L211-L244), constructs the unique
  maximal ideal of `AdjoinRoot g` from monicity, finiteness, and irreducibility
  of the reduced polynomial;
* [`adjoinRoot_map_maximalIdeal_isMaximal`, lines 279--293](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L279-L293), proves that the image
  of the coefficient-ring maximal ideal is maximal;
* [`adjoinRoot_maxIdeal_eq_map_of_irred`, lines 339--347](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L339-L347), identifies it with the
  actual maximal ideal upstairs; and
* [`e1` followed by `e2.trans e3`, lines 386--407](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L386-L407), identifies the residue field
  of `AdjoinRoot g` with `AdjoinRoot gbar`.

The `adjoinRoot_*` declarations below specialize those three source helpers to
an arbitrary local coefficient ring using the stronger N209 classification
provided by `MathlibExt.RingTheory.AdjoinRoot.LocalMaximal`.
`residueFieldEquivAdjoinRootOfMapEq` is source `e1.trans (e2.trans e3)`:
the D3 maximal-ideal equality supplies `e1`, while D2 supplies `e2.trans e3`.
Its `_residue_mk` theorem records the canonical action on polynomial
representatives. D1 supplies monicity, finiteness, domainhood, and the exact
reduction equation; D2 supplies the coefficient quotient equivalence; N209
supplies maximal-ideal classification. This stage still does not construct
the DVR, local-hom, finite-dimensional, separable, or full
essential-surjectivity packages returned later in
[source lines 349--453](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L349-L453).

Stage D4 is the DVR conclusion for a monic `AdjoinRoot` whose residue
reduction is irreducible, after the domain and local-ring structures are
installed. Its exact source is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`, helper
`adjoinRoot_isDVR_of_irred_map`, lines 295--321](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L295-L321).
The source hypothesis that
`A` is a DVR maps to `[CommRing A] [IsDomain A]
[IsDiscreteValuationRing A]`; source monicity maps to `hg : g.Monic`; and
irreducibility of the residue reduction maps to
`hirr : Irreducible (g.map (IsLocalRing.residue A))`. The instance
`[IsDomain (AdjoinRoot g)]` is supplied by D1 and
`[IsLocalRing (AdjoinRoot g)]` by D3. The source's explicit finite-module
hypothesis is derived here from `hg.finite_adjoinRoot`, after which the proof
derives Noetherianity, excludes the field case, identifies the maximal ideal
using D3, proves it principal, and applies `IsDiscreteValuationRing.TFAE`.
The exact conclusion is
`DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map`.
D4 is only a prerequisite stage and does not prove the later local-hom,
finite-dimensional, separable, essential-surjectivity, full-faithfulness, or
categorical equivalence clauses.

The essential-surjectivity object stage is the finite-separable
residue-extension object-realization step only. Its source module is
`Atlas.NumberTheoryI.ResidueFieldFunctor`, source file
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`, matched declaration
`residueFieldFunctor_essential_surjectivity`, lines 1174--1203](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1174-L1203).
The source
chooses a primitive element and its monic irreducible separable minimal
polynomial at lines 1187--1193, invokes `adjoinRoot_dvr_of_irreducible_lift`
at lines 1196--1198, and composes the resulting residue-field equivalence at
lines 1200--1203.

The source data maps to
`DVRResidue.exists_finite_dvr_extension_residueField_algEquiv` as follows:
the finite-dimensional separable residue-field extension is `L` with
`[Field L]`, `[Algebra (IsLocalRing.ResidueField A) L]`,
`[FiniteDimensional (IsLocalRing.ResidueField A) L]`, and
`[Algebra.IsSeparable (IsLocalRing.ResidueField A) L]`; the constructed ring
is `B` with `[CommRing B]`, `[IsDomain B]`, `[Algebra A B]`,
`[Module.Finite A B]`, `[IsDiscreteValuationRing B]`, and
`[IsLocalHom (algebraMap A B)]`; the residue comparison is
`Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L)`.

The source assumes `[HenselianLocalRing A]`, with completeness supplying that
upstream. This stage omits Henselianity/completeness only because it proves
the weaker ring-level object realization and does not package or prove an
unramified extension object. It therefore does not yet establish the full
categorical essential-surjectivity clause, full faithfulness, or the N211
equivalence.

Public theorems:
* `DVRResidue.exists_monic_lift_adjoinRoot_domain`
* `DVRResidue.adjoinRootQuotientEquivOfMapEq`
* `DVRResidue.adjoinRootQuotientEquivOfMapEq_mk`
* `DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map`
* `DVRResidue.adjoinRoot_map_maximalIdeal_isMaximal`
* `DVRResidue.maximalIdeal_adjoinRoot_eq_map`
* `DVRResidue.residueFieldEquivAdjoinRootOfMapEq`
* `DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map`
* `DVRResidue.adjoinRoot_isLocalHom_of_irreducible_map`
* `DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq`
* `DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk`
* `DVRResidue.exists_finite_dvr_extension_residueField_algEquiv`
-/

@[expose] public section

open Polynomial

namespace DVRResidue

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **Monic lifts of irreducible residue polynomials.** Let $A$ be a discrete valuation ring with
residue field $k$, and let $\bar g \in k[X]$ be monic and irreducible. Then there is a monic
polynomial $g \in A[X]$ whose reduction modulo the maximal ideal of $A$ is $\bar g$, such that
$A[X]/(g)$ is an integral domain and is finitely generated as an $A$-module. -/
theorem exists_monic_lift_adjoinRoot_domain
    (gbar : (IsLocalRing.ResidueField A)[X]) (hmonic : gbar.Monic)
    (hirr : Irreducible gbar) :
    ∃ (g : A[X]) (_ : g.Monic) (_ : IsDomain (AdjoinRoot g))
      (_ : Module.Finite A (AdjoinRoot g)),
      g.map (IsLocalRing.residue A) = gbar := by
  have hlift : gbar ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro c
    exact IsLocalRing.residue_surjective (gbar.coeff c)
  obtain ⟨g, hmap, _hdeg, hg⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmonic
  have hirr_map : Irreducible (g.map (IsLocalRing.residue A)) := hmap ▸ hirr
  have hgirr : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue A) g
      hg hirr_map
  have hprime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hgirr
  have hdom : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hprime
  have hfin : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  exact ⟨g, hg, hdom, hfin, hmap⟩

section QuotientEquiv

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **Reducing $R[X]/(g)$ modulo the maximal ideal of $R$.** Let $R$ be a local ring with maximal
ideal $\mathfrak m$ and residue field $k$, let $g \in R[X]$, and let $\bar g \in k[X]$ be a
polynomial equal to the reduction of $g$ modulo $\mathfrak m$. This is the canonical ring
isomorphism from the quotient of $R[X]/(g)$ by the ideal generated by the image of $\mathfrak m$
onto $k[X]/(\bar g)$; it sends the class of the image of $p \in R[X]$ to the class of the
reduction $\bar p \in k[X]$. -/
noncomputable def adjoinRootQuotientEquivOfMapEq
    (g : R[X]) (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) :
    AdjoinRoot g ⧸ Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal R) ≃+*
      AdjoinRoot gbar := by
  subst gbar
  exact AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
    (IsLocalRing.maximalIdeal R) g

@[simp]
theorem adjoinRootQuotientEquivOfMapEq_mk
    (g : R[X]) (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) (p : R[X]) :
    adjoinRootQuotientEquivOfMapEq g gbar hmap
        (Ideal.Quotient.mk _ (AdjoinRoot.mk g p)) =
      AdjoinRoot.mk gbar (p.map (IsLocalRing.residue R)) := by
  subst gbar
  exact AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of
    (I := IsLocalRing.maximalIdeal R) (f := g) p

end QuotientEquiv

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A] {g : A[X]}

/-- **The extended maximal ideal is maximal for irreducible reduction.** Let $A$ be a local ring
with maximal ideal $\mathfrak m$ and residue field $k$, and let $g \in A[X]$ be a polynomial whose
reduction $\bar g \in k[X]$ modulo $\mathfrak m$ is irreducible. Then the ideal of $A[X]/(g)$
generated by the image of $\mathfrak m$ under the canonical map $A \to A[X]/(g)$ is maximal. -/
theorem adjoinRoot_map_maximalIdeal_isMaximal
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    (Ideal.map (algebraMap A (AdjoinRoot g))
      (IsLocalRing.maximalIdeal A)).IsMaximal := by
  have h := AdjoinRoot.is_maximal_of_irreducible_factor g g hirr dvd_rfl
  simpa [AdjoinRoot.mk_self] using h

/-- **Monic polynomials with irreducible reduction give local rings.** Let $A$ be a local ring
with residue field $k$, and let $g \in A[X]$ be a monic polynomial whose reduction
$\bar g \in k[X]$ modulo the maximal ideal of $A$ is irreducible. Then $A[X]/(g)$ is a local
ring. -/
theorem adjoinRoot_isLocalRing_of_monic_of_irreducible_map (hg : g.Monic)
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    IsLocalRing (AdjoinRoot g) := by
  let _ : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  let _ : Algebra.IsIntegral A (AdjoinRoot g) :=
    Algebra.IsIntegral.of_finite A (AdjoinRoot g)
  refine IsLocalRing.of_unique_max_ideal ⟨_,
    adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr, fun M hM => ?_⟩
  let _ : M.IsMaximal := hM
  have hc : (M.comap (algebraMap A (AdjoinRoot g))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A (AdjoinRoot g))
      (algebraMap_isIntegral_iff.mpr inferInstance) M
  have hle :
      Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ≤
        M :=
    IsLocalRing.eq_maximalIdeal hc ▸ Ideal.map_comap_le
  exact ((adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr).eq_of_le
    hM.ne_top hle).symm

/-- **The maximal ideal of $A[X]/(g)$ is extended from $A$.** Let $A$ be a local ring with maximal
ideal $\mathfrak m$ and residue field $k$, and let $g \in A[X]$ be a polynomial whose reduction
$\bar g \in k[X]$ modulo $\mathfrak m$ is irreducible. If $A[X]/(g)$ is a local ring, then its
maximal ideal is the ideal generated by the image of $\mathfrak m$ under the canonical map
$A \to A[X]/(g)$. -/
theorem maximalIdeal_adjoinRoot_eq_map [IsLocalRing (AdjoinRoot g)]
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) := by
  have h : (Ideal.map (algebraMap A (AdjoinRoot g))
      (IsLocalRing.maximalIdeal A)).IsMaximal :=
    adjoinRoot_map_maximalIdeal_isMaximal (g := g) hirr
  have heq : IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal h).symm
  simpa only [AdjoinRoot.algebraMap_eq] using heq

/-- **Residue field of $A[X]/(g)$.** Let $A$ be a local ring with residue field $\kappa(A)$, let
$g \in A[X]$ be such that $A[X]/(g)$ is a local ring, and let $\bar g \in \kappa(A)[X]$ be the
reduction of $g$ modulo the maximal ideal of $A$, assumed irreducible. This is the ring
isomorphism from the residue field of $A[X]/(g)$ onto $\kappa(A)[X]/(\bar g)$ that sends the residue
class of the image of each $p \in A[X]$ to the class of $\bar p$, the reduction of the coefficients
of $p$ modulo the maximal ideal of $A$. -/
noncomputable def residueFieldEquivAdjoinRootOfMapEq
    [IsLocalRing (AdjoinRoot g)] (gbar : (IsLocalRing.ResidueField A)[X])
    (hirr : Irreducible (g.map (IsLocalRing.residue A)))
    (hmap : g.map (IsLocalRing.residue A) = gbar) :
    IsLocalRing.ResidueField (AdjoinRoot g) ≃+* AdjoinRoot gbar := by
  change (AdjoinRoot g ⧸ IsLocalRing.maximalIdeal (AdjoinRoot g)) ≃+*
    AdjoinRoot gbar
  exact (Ideal.quotEquivOfEq
    (maximalIdeal_adjoinRoot_eq_map (g := g) hirr)).trans
    (adjoinRootQuotientEquivOfMapEq g gbar hmap)

/-- **Residue field of $A[X]/(g)$ on representatives.** Let $A$ be a local ring with residue field
$\kappa(A)$, let $g \in A[X]$ be such that $A[X]/(g)$ is a local ring, and let
$\bar g \in \kappa(A)[X]$ be the reduction of $g$ modulo the maximal ideal of $A$, assumed
irreducible. Then for every $p \in A[X]$, the ring isomorphism from the residue field of
$A[X]/(g)$ onto $\kappa(A)[X]/(\bar g)$ sends the residue class of the image of $p$ in $A[X]/(g)$
to the class of $\bar p$, the reduction of the coefficients of $p$ modulo the maximal ideal of
$A$. -/
@[simp]
theorem residueFieldEquivAdjoinRootOfMapEq_residue_mk
    [IsLocalRing (AdjoinRoot g)] (gbar : (IsLocalRing.ResidueField A)[X])
    (hirr : Irreducible (g.map (IsLocalRing.residue A)))
    (hmap : g.map (IsLocalRing.residue A) = gbar) (p : A[X]) :
    residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap
        (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g p)) =
      AdjoinRoot.mk gbar (p.map (IsLocalRing.residue A)) := by
  have hEq : IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) :=
    maximalIdeal_adjoinRoot_eq_map (g := g) hirr
  change ((Ideal.quotEquivOfEq hEq).trans
      (adjoinRootQuotientEquivOfMapEq g gbar hmap))
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot g))
        (AdjoinRoot.mk g p)) =
      AdjoinRoot.mk gbar (p.map (IsLocalRing.residue A))
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    adjoinRootQuotientEquivOfMapEq_mk]

/-- **Local base map for polynomials with irreducible reduction.** Let $A$ be a local ring with
residue field $k$, and let $g \in A[X]$ be a polynomial whose reduction $\bar g \in k[X]$ modulo
the maximal ideal of $A$ is irreducible. If $A[X]/(g)$ is a local ring, then the canonical map
$A \to A[X]/(g)$ is a local ring homomorphism: an element of $A$ whose image in $A[X]/(g)$ is a
unit is itself a unit. -/
theorem adjoinRoot_isLocalHom_of_irreducible_map [IsLocalRing (AdjoinRoot g)]
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    IsLocalHom (AdjoinRoot.of g) := by
  have h := ((IsLocalRing.local_hom_TFAE (AdjoinRoot.of g)).out 4 1).mp
  apply h
  rw [maximalIdeal_adjoinRoot_eq_map (g := g) hirr]
  exact Ideal.le_comap_map

/-- **The residue field of $A[X]/(g)$ as a $k$-algebra.** Let $A$ be a local ring with maximal
ideal $\mathfrak m$ and residue field $k$, and let $g \in A[X]$ be a polynomial such that
$A[X]/(g)$ is a local ring, the canonical map $A \to A[X]/(g)$ is a local homomorphism, and the
reduction $\bar g \in k[X]$ of $g$ modulo $\mathfrak m$ is irreducible. This is the isomorphism of
$k$-algebras from the residue field of $A[X]/(g)$ (a $k$-algebra via $A \to A[X]/(g)$) onto
$k[X]/(\bar g)$ that sends the residue class of the image of each $p \in A[X]$ to the class of its
reduction $\bar p \in k[X]$. -/
noncomputable def residueFieldAlgEquivAdjoinRootOfMapEq [IsLocalRing (AdjoinRoot g)]
    [IsLocalHom (algebraMap A (AdjoinRoot g))]
    (gbar : (IsLocalRing.ResidueField A)[X])
    (hirr : Irreducible (g.map (IsLocalRing.residue A)))
    (hmap : g.map (IsLocalRing.residue A) = gbar) :
    IsLocalRing.ResidueField (AdjoinRoot g) ≃ₐ[IsLocalRing.ResidueField A]
      AdjoinRoot gbar :=
  AlgEquiv.ofRingEquiv
    (f := residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap)
    (fun x => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      have hmap_res : algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (AdjoinRoot g)) (IsLocalRing.residue A a) =
          IsLocalRing.residue (AdjoinRoot g) (algebraMap A (AdjoinRoot g) a) :=
        rfl
      rw [hmap_res, AdjoinRoot.algebraMap_eq,
        AdjoinRoot.algebraMap_eq,
        show AdjoinRoot.of g a = AdjoinRoot.mk g (C a) from rfl,
        show AdjoinRoot.of gbar (IsLocalRing.residue A a) =
          AdjoinRoot.mk gbar (C (IsLocalRing.residue A a)) from rfl,
        residueFieldEquivAdjoinRootOfMapEq_residue_mk,
        Polynomial.map_C])

/-- **The residue-field algebra isomorphism on polynomial classes.** Let $A$ be a local ring with
maximal ideal $\mathfrak m$ and residue field $k$, let $g \in A[X]$ be a polynomial such that
$A[X]/(g)$ is a local ring, the canonical map $A \to A[X]/(g)$ is a local homomorphism, and the
reduction $\bar g \in k[X]$ of $g$ modulo $\mathfrak m$ is irreducible. Then for every
$p \in A[X]$, the canonical $k$-algebra isomorphism from the residue field of $A[X]/(g)$
onto $k[X]/(\bar g)$ sends the residue class of the image of $p$ in $A[X]/(g)$ to the class
of the reduction $\bar p \in k[X]$ of $p$. -/
@[simp]
theorem residueFieldAlgEquivAdjoinRootOfMapEq_residue_mk
    [IsLocalRing (AdjoinRoot g)] [IsLocalHom (algebraMap A (AdjoinRoot g))]
    (gbar : (IsLocalRing.ResidueField A)[X])
    (hirr : Irreducible (g.map (IsLocalRing.residue A)))
    (hmap : g.map (IsLocalRing.residue A) = gbar) (p : A[X]) :
    residueFieldAlgEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap
        (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g p)) =
      AdjoinRoot.mk gbar (p.map (IsLocalRing.residue A)) := by
  change (residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap)
      (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g p)) = _
  exact residueFieldEquivAdjoinRootOfMapEq_residue_mk (g := g) gbar hirr hmap p

end Local

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {g : A[X]} [IsDomain (AdjoinRoot g)] [IsLocalRing (AdjoinRoot g)]

/-- **Monic lifts of irreducible residue polynomials give DVRs.** Let $A$ be a discrete valuation
ring with residue field $k$, and let $g \in A[X]$ be a monic polynomial whose reduction
$\bar g \in k[X]$ modulo the maximal ideal of $A$ is irreducible. If $A[X]/(g)$ is an integral
domain and a local ring, then $A[X]/(g)$ is a discrete valuation ring. -/
theorem adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
    (hg : g.Monic)
    (hirr : Irreducible (g.map (IsLocalRing.residue A))) :
    IsDiscreteValuationRing (AdjoinRoot g) := by
  let _ : Module.Finite A (AdjoinRoot g) := hg.finite_adjoinRoot
  let _ : IsNoetherianRing (AdjoinRoot g) :=
    IsNoetherianRing.of_finite A (AdjoinRoot g)
  have hdeg : g.degree ≠ 0 := by
    intro hzero
    have hpos := Polynomial.degree_pos_of_irreducible hirr
    have hle : (g.map (IsLocalRing.residue A)).degree ≤ g.degree :=
      Polynomial.degree_map_le
    rw [hzero] at hle
    exact (lt_irrefl _) (hpos.trans_le hle)
  have hinj : Function.Injective (algebraMap A (AdjoinRoot g)) := by
    have h := AdjoinRoot.of.injective_of_degree_ne_zero hdeg
    rwa [← AdjoinRoot.algebraMap_eq] at h
  have hnotfield : ¬IsField (AdjoinRoot g) := by
    intro hfield
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)
  have hprincipal : (IsLocalRing.maximalIdeal (AdjoinRoot g)).IsPrincipal := by
    rw [maximalIdeal_adjoinRoot_eq_map (g := g) hirr]
    have hbase : (IsLocalRing.maximalIdeal A).IsPrincipal := inferInstance
    exact hbase.map_ringHom (AdjoinRoot.of g)
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot g) hnotfield).out 5 1).mp
    hprincipal

end DVR

section EssentialSurjectivity

universe u v

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **Finite separable residue extensions lift to finite DVR extensions.** Let $A$ be a discrete
valuation ring with residue field $k$, and let $L$ be a finite separable field extension of $k$.
Then there is a discrete valuation ring $B$ with an $A$-algebra structure such that $B$ is
finitely generated as an $A$-module and the structure map $A \to B$ is a local homomorphism,
together with an isomorphism of $k$-algebras between the residue field of $B$ (a $k$-algebra
via $A \to B$) and $L$.

Source: ATLAS NumberTheoryI N211, Theorem 10.13, essential-surjectivity object-construction
stage only (a prerequisite, not the full N211 target): completeness and Henselianity of $A$
are not assumed, and neither full faithfulness nor the categorical equivalence is proved. -/
theorem exists_finite_dvr_extension_residueField_algEquiv
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [FiniteDimensional (IsLocalRing.ResidueField A) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
      (_ : IsLocalHom (algebraMap A B)),
      Nonempty (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (IsLocalRing.ResidueField A) L
  have hint : IsIntegral (IsLocalRing.ResidueField A) α :=
    (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  obtain ⟨g, hg, hdom, hfin, hmap⟩ := exists_monic_lift_adjoinRoot_domain (A := A)
    (minpoly (IsLocalRing.ResidueField A) α) (minpoly.monic hint)
    (minpoly.irreducible hint)
  have hirr_map : Irreducible (g.map (IsLocalRing.residue A)) :=
    hmap ▸ minpoly.irreducible hint
  let hComm : CommRing (AdjoinRoot g) := inferInstance
  let _ : CommRing (AdjoinRoot g) := hComm
  let hAlg : Algebra A (AdjoinRoot g) := inferInstance
  let _ : Algebra A (AdjoinRoot g) := hAlg
  have hDom : IsDomain (AdjoinRoot g) := hdom
  let _ : IsDomain (AdjoinRoot g) := hDom
  have hFin : Module.Finite A (AdjoinRoot g) := hfin
  let _ : Module.Finite A (AdjoinRoot g) := hFin
  let _ : IsLocalRing (AdjoinRoot g) :=
    adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr_map
  have hDVR : IsDiscreteValuationRing (AdjoinRoot g) :=
    adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
      (g := g) hg hirr_map
  let _ : IsDiscreteValuationRing (AdjoinRoot g) := hDVR
  have hLocMap : IsLocalHom (algebraMap A (AdjoinRoot g)) := by
    simpa only [AdjoinRoot.algebraMap_eq] using
      adjoinRoot_isLocalHom_of_irreducible_map (g := g) hirr_map
  let _ : IsLocalHom (algebraMap A (AdjoinRoot g)) := hLocMap
  have hadj : Algebra.adjoin (IsLocalRing.ResidueField A) ({α} : Set L) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun _ _ => Algebra.IsAlgebraic.isAlgebraic _) hα
  have e1 : AdjoinRoot (minpoly (IsLocalRing.ResidueField A) α)
      ≃ₐ[IsLocalRing.ResidueField A] L :=
    (minpoly.equivAdjoin hint).trans
      ((Subalgebra.equivOfEq _ _ hadj).trans Subalgebra.topEquiv)
  have e0 : IsLocalRing.ResidueField (AdjoinRoot g)
      ≃ₐ[IsLocalRing.ResidueField A]
      AdjoinRoot (minpoly (IsLocalRing.ResidueField A) α) :=
    residueFieldAlgEquivAdjoinRootOfMapEq (g := g) _ hirr_map hmap
  refine ⟨AdjoinRoot g, hComm, hDom, hAlg, hFin, hDVR, hLocMap, ?_⟩
  exact Nonempty.intro (e0.trans e1)

end EssentialSurjectivity

end DVRResidue

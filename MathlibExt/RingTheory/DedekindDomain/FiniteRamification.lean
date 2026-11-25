/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Only finitely many primes ramify (ATLAS Corollary 12.20)

This module formalizes ATLAS `NumberTheoryI` Corollary 12.20: in an extension
`B / A` of Dedekind domains, only finitely many primes of `A` (or of `B`)
ramify.

The proof goes through the different ideal. A prime `𝔮` of `B` is ramified
exactly when it divides the different ideal (`dvd_differentIdeal_iff`), and
only finitely many (height-one) primes divide a nonzero ideal
(`Ideal.finite_factors`), the different ideal being nonzero
(`differentIdeal_ne_bot`). The statement for primes of `A` follows: a ramified
prime of `A` is the contraction of a ramified prime of `B`, hence the set of
ramified primes of `A` is contained in the image of the finite set of ramified
primes of `B` under contraction.

This is the general Dedekind-domain version. The number-field version
(`NumberField.finite_ramified_primes`, for rings of integers of number fields
and `Algebra.IsUnramifiedIn`) is already in
`MathlibExt/NumberTheory/NumberField/FiniteRamification.lean`.
-/

@[expose] public section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open IsDedekindDomain

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **Only finitely many primes of the extension ramify.** Let $A$ and $B$ be Dedekind domains,
where $B$ is an $A$-algebra that is finitely generated and torsion-free as an $A$-module and the
field of fractions of $B$ is separable over the field of fractions of $A$. Then only finitely many
nonzero prime ideals $\mathfrak P$ of $B$ are ramified over $A$. Here $\mathfrak P$ is unramified
over $A$ when the localization $B_{\mathfrak P}$ is formally unramified over $A$.

Source: ATLAS `NumberTheoryI` Corollary 12.20, the statement for primes of $B$. -/
theorem Ideal.finite_ramified_primes :
    {P : HeightOneSpectrum B | ¬ Algebra.IsUnramifiedAt A P.asIdeal}.Finite := by
  have hne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  apply Set.Finite.subset (Ideal.finite_factors hne)
  intro P hP
  exact (dvd_differentIdeal_iff (A := A) (B := B) (P := P.asIdeal)).mpr hP

/-- **Only finitely many primes of the base ramify.** Let $A$ and $B$ be Dedekind domains, where
$B$ is an $A$-algebra that is finitely generated and torsion-free as an $A$-module and the field of
fractions of $B$ is separable over the field of fractions of $A$. Then only finitely many nonzero
prime ideals $\mathfrak p$ of $A$ are ramified in $B$. Here $\mathfrak p$ is unramified in $B$ when
every prime ideal $\mathfrak P$ of $B$ lying over $\mathfrak p$ is unramified over $A$, that is, the
localization $B_{\mathfrak P}$ is formally unramified over $A$.

Source: ATLAS `NumberTheoryI` Corollary 12.20, the statement for primes of $A$. -/
theorem Ideal.finite_ramified_primes_below :
    {p : HeightOneSpectrum A | ¬ Algebra.IsUnramifiedIn B p.asIdeal}.Finite := by
  classical
  apply (Ideal.finite_ramified_primes (A := A) (B := B).image
    (fun P : HeightOneSpectrum B =>
      ⟨P.asIdeal.under A, inferInstance, mt Ideal.eq_bot_of_under_eq_bot P.ne_bot⟩)).subset
  intro p hp
  change ¬ Algebra.IsUnramifiedIn B p.asIdeal at hp
  simp only [Algebra.IsUnramifiedIn, Classical.not_forall] at hp
  obtain ⟨P, hPprime, hPLies, hPram⟩ := hp
  let _ : P.IsPrime := hPprime
  let _ : P.LiesOver p.asIdeal := hPLies
  let Q : HeightOneSpectrum B :=
    ⟨P, hPprime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  refine ⟨Q, hPram, ?_⟩
  apply HeightOneSpectrum.ext
  exact hPLies.over.symm

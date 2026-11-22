/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Eigenvalues of elements of prime order in finite linear groups (Kourovka Notebook Problem 11.35)

Kourovka Notebook, Archive of Solved Problems, Problem 11.35 (A. E. Zalesskiĭ): if `H` is a finite
linear group over `ℂ` and `h ∈ H` of prime order `p` is not contained in any abelian normal subgroup
of `H`, does `h` have at least `(p - 1) / 2` different eigenvalues?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace MathlibExt.GroupTheory.LinearGroupPrimeOrderEigenvaluesKourovka11Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.35 (A. E.
Zalesskiĭ). UnsolvedMath record UM-00700728 (`KOU-11.35`), dataset ulamai/UnsolvedMath v1.8.0.

`H` is a finite subgroup of `GL_n(ℂ)`. "Abelian normal subgroup" is a subgroup `A ≤ H`, normal in
`H`, whose elements commute. The eigenvalues of `h` are the distinct roots of its characteristic
polynomial, and "at least `(p - 1) / 2`" is `p - 1 ≤ 2 · #eigenvalues`, exact for `p = 2` as well.
-/

/-- Kourovka 11.35 (A. E. Zalesskiĭ): if `H` is a finite subgroup of `GL_n(ℂ)` and `h ∈ H` has
prime order `p` and lies in no abelian normal subgroup of `H`, then `h` has at least `(p - 1) / 2`
distinct eigenvalues (stated as `p - 1 ≤ 2 · #eigenvalues`; the eigenvalues are the distinct
roots of the characteristic polynomial). -/
def primeOrderElementManyEigenvalues : Prop :=
  ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)),
    (H : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)).Finite → ∀ h ∈ H, (orderOf h).Prime →
    (∀ A : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ), A ≤ H →
      (∀ x ∈ H, ∀ a ∈ A, x * a * x⁻¹ ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → h ∉ A) →
    orderOf h - 1 ≤ 2 * (h : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.toFinset.card

/--
Resolved true: the Kourovka Archive answers 11.35 "Yes, it is" (Robinson): an element of prime order
`p` of a finite subgroup of `GL_n(ℂ)` that lies in no abelian normal subgroup has at least `(p - 1)
/ 2` distinct eigenvalues. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 11.35 (A. E. Zalesskiĭ); resolution: G. R. Robinson, J. Algebra 178, no. 2 (1995),
635-642, Kourovka Archive, Problem 11.35: "Yes, it is", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted primeOrderElementManyEigenvalues_holds : primeOrderElementManyEigenvalues

end MathlibExt.GroupTheory.LinearGroupPrimeOrderEigenvaluesKourovka11Problem35Wanted

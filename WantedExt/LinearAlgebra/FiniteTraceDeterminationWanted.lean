/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Trace

/-!
# Determining an invertible endomorphism from finitely many power traces

Two invertible endomorphisms of vector spaces of dimensions at most `r` have
the same characteristic polynomial if their traces agree on any `2 * r`
consecutive positive powers. For semisimple endomorphisms this also determines
their linear conjugacy class. The vector spaces may have different dimensions;
no equality of dimensions is assumed.

Invertibility matters when the interval starts after the zeroth power: zero
eigenvalues do not contribute to any positive power trace. Characteristic zero
ensures that traces detect eigenvalue multiplicities. Semisimplicity is needed
for conjugacy, since traces do not detect the sizes of Jordan blocks.

## References

* P. Deligne, *Finitude de l'extension de Q engendrée par des traces de Frobenius,
  en caractéristique finie*, Moscow Mathematical Journal 12 (2012), 497–514,
  Lemma 2.9.
* A. Rojas León, *An effective criterion for finite monodromy of ℓ-adic sheaves*,
  https://arxiv.org/abs/2207.07155, proof of Theorem 4, which applies Deligne's
  lemma to the geometrically constant factors of semisimple sheaves.

These statements use Mathlib's actual trace, characteristic polynomial and
`Module.End.IsSemisimple`; they introduce no additional cohomology or sheaf
interface. No source code has been copied from the references.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.LinearAlgebra.FiniteTraceDeterminationWanted

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The characteristic polynomial of an invertible endomorphism on a space of
dimension at most `r` is determined by traces on `2 * r` consecutive positive
powers. The starting offset `start` is arbitrary, and the two dimensions need
not be supplied as equal. This is the power-sum determination underlying
Deligne's Lemma 2.9, as used in Rojas León's proof of Theorem 4. -/
public theorem_wanted charpoly_eq_of_trace_powers
    (A : Module.End K V) (B : Module.End K W) (r start : ℕ)
    (hV : Module.finrank K V ≤ r) (hW : Module.finrank K W ≤ r)
    (hA : IsUnit A) (hB : IsUnit B)
    (htrace : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * r →
      LinearMap.trace K V (A ^ (start + k)) =
        LinearMap.trace K W (B ^ (start + k))) :
    A.charpoly = B.charpoly

/-- **Deligne, Lemma 2.9**, in terms of linear conjugacy: two invertible
semisimple endomorphisms on spaces of dimensions at most `r` are linearly
conjugate exactly when their traces agree on any `2 * r` consecutive positive
powers. Over a general characteristic-zero field, semisimplicity is understood
as semisimplicity of the induced `K[X]`-module, as in Mathlib. -/
public theorem_wanted trace_powers_iff_linear_conjugate
    (A : Module.End K V) (B : Module.End K W) (r start : ℕ)
    (hV : Module.finrank K V ≤ r) (hW : Module.finrank K W ≤ r)
    (hA : IsUnit A) (hB : IsUnit B)
    (hsemisimpleA : A.IsSemisimple) (hsemisimpleB : B.IsSemisimple) :
    (∀ k : ℕ, 1 ≤ k → k ≤ 2 * r →
      LinearMap.trace K V (A ^ (start + k)) =
        LinearMap.trace K W (B ^ (start + k))) ↔
      ∃ e : V ≃ₗ[K] W, e.conj A = B

end MathlibExt.LinearAlgebra.FiniteTraceDeterminationWanted

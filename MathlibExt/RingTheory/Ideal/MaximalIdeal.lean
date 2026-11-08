/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Corrected maximal-ideal containment under integrality

Let `A` be a local ring and `B` an integral `A`-algebra. Every maximal ideal
of `B` contains the extension of the maximal ideal of `A`. This module proves
this corrected integrality theorem and its integral/monic `AdjoinRoot` forms.

The raw ATLAS `NumberTheoryI` Corollary 10.10 target (Section 10.1) states
containment for arbitrary `g ∈ A[x]`, with `A` local Noetherian. As written it
omits a necessary substantive hypothesis: for `A = ℤ_(p)` and `g = pX - 1`,
`A[X]/(g)` is `ℚ`, and its maximal ideal `0` does not contain `pB = B`.
The archived `maximal_ideal_contains_image_of_finite_algebra` instead assumes
`Module.Finite A B`, which implies integrality. The theorem here generalizes
that valid finite-algebra statement; it does not formalize the raw arbitrary-
polynomial target as written. The archived source and target are preserved.

The contraction of a maximal ideal is maximal under integrality, hence equals
the unique maximal ideal of `A`; `Ideal.map_comap_le` then proves containment.
Noetherianity and module finiteness are unnecessary for this corrected theorem.
Monicity is a sufficient way to establish integrality of `AdjoinRoot g`;
no equivalence between monicity and integrality is claimed.

The companion `AdjoinRoot` classification API in
`MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean` is reused under its explicit
integrality/monicity hypotheses; no unrestricted Corollary 10.11 claim is made.
-/

@[expose] public section

namespace Ideal

/-- Corrected containment theorem: every maximal ideal of an integral extension
of a local ring contains the extension of the base maximal ideal. -/
theorem IsMaximal.map_maximalIdeal_le {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {m : Ideal B} (hm : m.IsMaximal) :
    Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤ m := by
  have hcomap : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have hcomap_eq : m.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hcomap
  rw [← hcomap_eq]
  exact Ideal.map_comap_le

end Ideal

namespace AdjoinRoot

/-- Corrected `AdjoinRoot` containment statement under explicit integrality:
every maximal ideal contains the extension of the base maximal ideal. -/
theorem isMaximal_map_maximalIdeal_le {A : Type*} [CommRing A] [IsLocalRing A]
    {g : Polynomial A} [Algebra.IsIntegral A (AdjoinRoot g)]
    {m : Ideal (AdjoinRoot g)} (hm : m.IsMaximal) :
    Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ≤ m :=
  Ideal.IsMaximal.map_maximalIdeal_le hm

/-- Monic specialization of the corrected statement: monicity supplies integrality,
so every maximal ideal contains the extension of the base maximal ideal. -/
theorem isMaximal_map_maximalIdeal_le_of_monic {A : Type*} [CommRing A]
    [IsLocalRing A] {g : Polynomial A} (hg : g.Monic)
    {m : Ideal (AdjoinRoot g)} (hm : m.IsMaximal) :
    Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ≤ m := by
  have : Algebra.IsIntegral A (AdjoinRoot g) := AdjoinRoot.isIntegral_of_monic hg
  exact Ideal.IsMaximal.map_maximalIdeal_le hm

end AdjoinRoot

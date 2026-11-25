/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverResidueNaturality
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Inertia degree under finite-place completion

The canonical map between finite-place completion integer rings preserves the
inertia degree of the corresponding global prime ideals.

ATLAS source map: this module is a supporting finite-place stage toward ATLAS
`NumberTheoryI` item N265, Theorem 13.5, Section 13.1, whose primary Lean
declaration is `TensorProductDecomposition.theorem_13_5_finite_place_Kv` in
`v1/Atlas/NumberTheoryI/code/GlobalFields.lean` lines 1152--1211:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1211>.

Its exact source counterpart is `KroneckerWeber.part_3b_inertia_deg_preserved` in
`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean` lines 2362--2399:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2362-L2399>.

Object and hypothesis map: native `v : HeightOneSpectrum (O K)` and
`w : HeightOneSpectrum (O L)` with `[w.asIdeal.LiesOver v.asIdeal]` are the
source global primes `p` and `q` with `q` over `p`; the local primes are
`IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)` and the analogous ideal
for `w`; the scoped `Algebra` instance is induced by
`adicCompletionIntegersMap v w`.

Proof correspondence: `completionResidueFieldEquiv_naturality v w` is the native
naturality square corresponding to source `completion_residueFieldEquiv_compat`
(lines 2248--2318). The two uses of `Ideal.inertiaDeg_eq_of_isMaximal` identify
the local and global inertia degrees with the respective residue-field finranks;
`Algebra.finrank_eq_of_equiv_equiv` transports equality across the compatible
residue-field equivalences, corresponding to source
`completion_residueField_finrank_eq` (lines 2324--2358).

Scope: this module proves only preservation of inertia degree under the
finite-place completion map, a dimension input toward N265; it does not construct
or prove the full tensor-product-to-product equivalence of Theorem 13.5.
-/

@[expose] public section

namespace NumberField.LiesOver

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
variable {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
variable [w.asIdeal.LiesOver v.asIdeal]

noncomputable scoped instance : Algebra (v.adicCompletionIntegers K)
    (w.adicCompletionIntegers L) :=
  (adicCompletionIntegersMap v w).toAlgebra

end NumberField.LiesOver

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **Completion preserves the inertia degree.** Let $L/K$ be an extension of number fields, let
$v$ be a nonzero prime ideal of $\mathcal{O}_K$ and $w$ a nonzero prime ideal of $\mathcal{O}_L$
lying over $v$. Let $\mathcal{O}_{K_v}$ and $\mathcal{O}_{L_w}$ be the rings of integers of the
completions $K_v$ and $L_w$, with $\mathcal{O}_{L_w}$ an algebra over $\mathcal{O}_{K_v}$ via the
canonical map. Then the inertia degree of the maximal ideal of $\mathcal{O}_{L_w}$ over
$\mathcal{O}_{K_v}$ equals the inertia degree of $w$ over $v$. -/
theorem inertiaDeg_adicCompletionIntegersMap :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg
      (v.adicCompletionIntegers K) =
      w.asIdeal.inertiaDeg (𝓞 K) := by
  have hcomp := comap_maximalIdeal_adicCompletionIntegersMap v w
  let _ : (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := ⟨hcomp.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)),
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  apply Algebra.finrank_eq_of_equiv_equiv
    (completionResidueFieldEquiv (K := K) v)
    (completionResidueFieldEquiv (K := L) w)
  change (ringOfIntegersResidueQuotientMap v w).comp
      (completionResidueFieldEquiv (K := K) v).toRingHom =
    (completionResidueFieldEquiv (K := L) w).toRingHom.comp
      (adicCompletionResidueQuotientMap v w)
  exact completionResidueFieldEquiv_naturality v w

end IsDedekindDomain.HeightOneSpectrum

-- End of file.

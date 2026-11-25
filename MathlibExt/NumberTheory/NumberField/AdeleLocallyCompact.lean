/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import MathlibExt.RingTheory.DedekindDomain.AdicCompletionResidueField
import Mathlib.Topology.Algebra.Module.Compact

/-!
# Local compactness of number-field adeles

For a number field `K`, the adic-completion integers are compact, each local
completion is proper, and the finite adele ring and the adele ring are `T2`
and locally compact.

## ATLAS source correspondence

The adic-completeness instance below supplies a prerequisite for ATLAS
NumberTheoryI N265, Theorem 13.5. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, N265 is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879).
Its finite-place proof
uses completed integer rings, notably in
`KroneckerWeber.adicCompletionIntegers_isIntegralClosure_aux` and
`adicCompletionIntegers_module_finite`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 1661--1714](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1661-L1714).
The repaired
integral-closure route requires the base completion integer ring to be complete
for its maximal-ideal adic topology.

`isAdicComplete_adicCompletionIntegers` proves exactly that prerequisite from
the compactness established immediately above. Given a compatible sequence
`f n` modulo powers of the maximal ideal, it forms the cosets
`S n = f n + (maximalIdeal)^n`. Compatibility makes these nonempty closed
cosets nested. Compactness gives a point in their intersection, and membership
in every `S n` says precisely that this point is congruent to `f n` modulo
`(maximalIdeal)^n`. This is `IsAdicComplete.prec'`; no separate metric
normalization or unstated completeness assumption is used.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField Valued.integer
open scoped Valued Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]

/-- **Finite residue field of a completed number ring.** Let $K$ be a number field and $v$ a
nonzero prime ideal of its ring of integers $\mathcal{O}_K$. The residue field of the ring of
integers $\mathcal{O}_v$ of the $v$-adic completion $K_v$ of $K$ is finite. -/
theorem finite_residueField (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  have : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hfin : Finite (𝓞 K ⧸ v.asIdeal) := inferInstance
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (v.completionResidueFieldEquiv (K := K)).symm.toEquiv

/-- The adic completion integers form a compact space. -/
noncomputable instance compactSpace (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  rw [compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    finite_residueField K v⟩

/-- The adic completion integers are complete for the maximal-ideal adic topology. -/
noncomputable instance isAdicComplete_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 K)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) where
  prec' f hf := by
    let _ : CompactSpace (v.adicCompletionIntegers K) := compactSpace K v
    let S n : Set (v.adicCompletionIntegers K) :=
      f n +ᵥ ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
        Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr
        (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) :=
      (IsNoetherianRing.isClosed_ideal
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hS (by simp [S]) h
    refine ⟨L, fun n ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

/-- Each finite local completion of a number field is a proper space. -/
noncomputable instance properSpace (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr (compactSpace K v)

/-- **Compactness of the completed ring of integers.** Let $K$ be a number field and $v$ a
nonzero prime ideal of its ring of integers $\mathcal{O}_K$. The ring of integers $\mathcal{O}_v$
of the $v$-adic completion $K_v$ of $K$ is a compact subset of $K_v$. -/
theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have hcomp := (compactSpace K v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at hcomp

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.InfiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The infinite adele ring is a `T2` space. -/
instance t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

end NumberField.InfiniteAdeleRing

namespace IsDedekindDomain.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The finite adele ring is a `T2` space. -/
instance t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

/-- The finite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  let wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
      (Filter.Eventually.of_forall
        (fun v => HeightOneSpectrum.isCompact_adicCompletionIntegers K v))
  let : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs
  infer_instance

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The adele ring is a `T2` space. -/
instance t2Space : T2Space (AdeleRing (𝓞 K) K) := Prod.t2Space

/-- The adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  Prod.locallyCompactSpace _ _

end NumberField.AdeleRing

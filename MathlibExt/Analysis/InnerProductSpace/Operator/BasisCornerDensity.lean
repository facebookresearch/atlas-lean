/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Operator.FiniteCoordinateCorner
public import Mathlib.Analysis.InnerProductSpace.l2Space

import MathlibExt.Analysis.InnerProductSpace.Operator.FiniteCoordinateExpansion
import MathlibExt.Analysis.InnerProductSpace.CompactOperator.BasisApproximation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Initial-segment coefficient corners and compact density

For a genuine natural-number Hilbert basis, the literal finite matrix of
operator coefficients maps to the corresponding finite projection sandwich.
The finite identity applies to every bounded operator, including empty
coordinates. Positive-size corner images are dense only in the actual compact
ideal, using the existing operator-norm compact-sandwich convergence.

Completeness is derived from the basis representation before constructing the
compact C-star target. No new projection, norm, raw limit or completion is used.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace HilbertBasis

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The literal target-row/source-column coefficient matrix maps to the actual
initial-segment sandwich of an arbitrary bounded operator. Empty size is legal;
compactness and separate ambient completeness are not assumptions. -/
theorem compactCorner_coefficients
    (b : HilbertBasis ℕ ℂ H) (N : ℕ) (T : H →L[ℂ] H) :
    letI : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace;
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    let J := compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let v : Fin N → H := fun i => b i.val;
    let hv : Orthonormal ℂ v :=
      b.orthonormal.comp (fun i : Fin N => i.val)
        (fun _ _ h => Fin.ext h);
    let X : CStarMatrix (Fin N) (Fin N) ℂ :=
      CStarMatrix.ofMatrix
        (fun i j : Fin N => inner ℂ (b i.val) (T (b j.val)));
    (hv.compactCorner X : H →L[ℂ] H) =
      (b.toUnconditionalSchauderBasis.proj (Finset.range N)).comp
        (T.comp (b.toUnconditionalSchauderBasis.proj (Finset.range N))) := by
  classical
  let : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  let v : Fin N → H := fun i => b i.val
  let hv : Orthonormal ℂ v :=
    b.orthonormal.comp (fun i : Fin N => i.val)
      (fun _ _ h => Fin.ext h)
  let X : CStarMatrix (Fin N) (Fin N) ℂ :=
    CStarMatrix.ofMatrix
      (fun i j : Fin N => inner ℂ (b i.val) (T (b j.val)))
  let c : ℕ → ℕ → (H →L[ℂ] H) :=
    fun i j => inner ℂ (b i) (T (b j)) •
      InnerProductSpace.rankOne ℂ (b i) (b j)
  change (hv.compactCorner X : H →L[ℂ] H) =
    (b.toUnconditionalSchauderBasis.proj (Finset.range N)).comp
      (T.comp (b.toUnconditionalSchauderBasis.proj (Finset.range N)))
  have hX (i j : Fin N) :
      X i j = inner ℂ (b i.val) (T (b j.val)) := rfl
  have hCorner :
      (hv.compactCorner X : H →L[ℂ] H) =
        ∑ i : Fin N, ∑ j : Fin N, c i.val j.val := by
    rw [hv.compactCorner_coe]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    change X i j • InnerProductSpace.rankOne ℂ (b i.val) (b j.val) =
      inner ℂ (b i.val) (T (b j.val)) •
        InnerProductSpace.rankOne ℂ (b i.val) (b j.val)
    rw [hX]
  have hSum :
      (∑ i : Fin N, ∑ j : Fin N, c i.val j.val) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j := by
    calc
      _ = ∑ i ∈ Finset.range N, ∑ j : Fin N, c i j.val :=
        (Finset.sum_range (n := N)
          (fun i : ℕ => ∑ j : Fin N, c i j.val)).symm
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (Finset.sum_range (n := N) (fun j : ℕ => c i j)).symm
  have hProj :
      (b.toUnconditionalSchauderBasis.proj (Finset.range N)).comp
          (T.comp (b.toUnconditionalSchauderBasis.proj (Finset.range N))) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j :=
    HilbertBasis.proj_comp_proj_eq_sum_rankOne b b T
      (Finset.range N) (Finset.range N)
  exact hCorner.trans (hSum.trans hProj.symm)

/-- The positive initial-segment corner images are dense in the existing
compact closed star ideal with its inherited operator norm. The basis derives
completeness; no density or convergence statement is supplied by the caller. -/
theorem dense_iUnion_range_compactCorner
    (b : HilbertBasis ℕ ℂ H) :
    letI : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace;
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    let J := compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let hv : ∀ n : ℕ, Orthonormal ℂ
        (fun i : Fin (n + 1) => b i.val) :=
      fun n => b.orthonormal.comp (fun i : Fin (n + 1) => i.val)
        (fun _ _ h => Fin.ext h);
    let σ : ∀ n : ℕ, CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
        →⋆ₙₐ[ℂ] J.carrier :=
      fun n => (hv n).compactCorner;
    Dense (⋃ n : ℕ, Set.range (σ n)) := by
  classical
  let : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  let hv : ∀ n : ℕ, Orthonormal ℂ
      (fun i : Fin (n + 1) => b i.val) :=
    fun n => b.orthonormal.comp (fun i : Fin (n + 1) => i.val)
      (fun _ _ h => Fin.ext h)
  let σ : ∀ n : ℕ, CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
      →⋆ₙₐ[ℂ] J.carrier :=
    fun n => (hv n).compactCorner
  change ∀ T : J.carrier, T ∈ closure (⋃ n : ℕ, Set.range (σ n))
  intro T
  have hT : IsCompactOperator (T : H →L[ℂ] H) :=
    (mem_compactEndomorphismIdeal (𝕜 := ℂ) (E := H)
      (T : H →L[ℂ] H)).mp T.property
  let X (N : ℕ) : CStarMatrix (Fin N) (Fin N) ℂ :=
    CStarMatrix.ofMatrix
      (fun i j : Fin N => inner ℂ (b i.val) ((T : H →L[ℂ] H) (b j.val)))
  let a : ℕ → J.carrier := fun n => σ n (X (n + 1))
  have hA (n : ℕ) :
      (a n : H →L[ℂ] H) =
        (b.toUnconditionalSchauderBasis.proj (Finset.range (n + 1))).comp
          ((T : H →L[ℂ] H).comp
            (b.toUnconditionalSchauderBasis.proj (Finset.range (n + 1)))) :=
    compactCorner_coefficients b (n + 1) (T : H →L[ℂ] H)
  have hRange : Tendsto (fun n : ℕ => Finset.range (n + 1)) atTop atTop :=
    tendsto_finset_range.comp (tendsto_add_atTop_nat 1)
  have hDiagonal :
      Tendsto (fun n : ℕ => (Finset.range (n + 1), Finset.range (n + 1)))
        atTop atTop :=
    tendsto_atTop_diagonal.comp hRange
  have hLimitOp :
      Tendsto (fun n : ℕ => (a n : H →L[ℂ] H)) atTop
        (𝓝 (T : H →L[ℂ] H)) := by
    refine Filter.Tendsto.congr' ?_
      ((HilbertBasis.tendsto_compact_sandwich b b hT).comp hDiagonal)
    exact Eventually.of_forall (fun n : ℕ => by
      simpa only [Function.comp_apply] using (hA n).symm)
  have hLimit : Tendsto a atTop (𝓝 T) := tendsto_subtype_rng.mpr hLimitOp
  have hMember (n : ℕ) : a n ∈ ⋃ m : ℕ, Set.range (σ m) :=
    Set.mem_iUnion.mpr ⟨n, X (n + 1), rfl⟩
  exact mem_closure_of_tendsto hLimit (Eventually.of_forall hMember)

end HilbertBasis

end

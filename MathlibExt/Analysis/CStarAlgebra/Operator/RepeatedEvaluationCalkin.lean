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

public import MathlibExt.Analysis.CStarAlgebra.HilbertDirectSum
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.ULift
import Mathlib.Tactic.NormNum

/-!
# Faithful split Calkin representation by repeated dense evaluations

The actual scalar Hilbert sum is indexed by `ULift ℕ`, retaining its stock
lp-two norm, inner product and completeness at any requested Hilbert universe.
The canonical Hilbert basis has a countable dense span and infinitely many
linearly independent vectors, giving the required separability and infinite
dimension internally.

Each point of the canonical dense sequence of the coefficient space is
repeated at all paired indices. A nonzero coefficient at such a point gives
uniformly separated images of infinitely many original unit vectors. The
stock compact-image subsequence theorem therefore proves faithfulness
modulo the actual compact ideal. The operator representation is the existing
`StarAlgHom.hilbertDirectSum`, with its original coordinate action.

This strict split representation supplies the full target summand needed by
the original Ext(X) pushforward for a continuous map whose image can be a
proper subset of its target. No faithful representation, output extension,
normal-operator existence theorem or naturality witness is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace CalkinAlgebra.RepeatedEvaluation

universe uH uY

/-- The countable coordinate index is lifted only to preserve the requested carrier universe. -/
private abbrev Index := ULift.{uH, 0} ℕ

/-- The original scalar Hilbert sum keeps the standard lp-two norm and inner product. -/
abbrev ScalarHilbert : Type uH := lp (fun _ : ULift.{uH, 0} ℕ => ℂ) 2

private def scalarHilbertBasis : HilbertBasis Index.{uH} ℂ ScalarHilbert.{uH} :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Countably many original basis vectors have dense span, so the actual scalar sum is separable. -/
instance scalarHilbertSeparable : SeparableSpace ScalarHilbert.{uH} := by
  apply isSeparable_univ_iff.mp
  have hs : IsSeparable
      (Submodule.span ℂ (Set.range scalarHilbertBasis) : Set ScalarHilbert.{uH}) :=
    (Set.countable_range scalarHilbertBasis).isSeparable.span
  have hc := hs.closure
  change IsSeparable
    ((Submodule.span ℂ (Set.range scalarHilbertBasis)).topologicalClosure :
      Set ScalarHilbert.{uH}) at hc
  simpa only [HilbertBasis.dense_span, Submodule.top_coe] using hc

/-- The actual infinite coordinate family rules out finite dimension of the original scalar sum. -/
theorem scalarHilbert_infinite : ¬ FiniteDimensional ℂ ScalarHilbert.{uH} := by
  intro h
  let : FiniteDimensional ℂ ScalarHilbert.{uH} := h
  exact Module.Finite.not_linearIndependent_of_infinite (R := ℂ)
    (scalarHilbertBasis : Index.{uH} → ScalarHilbert.{uH})
    scalarHilbertBasis.orthonormal.linearIndependent

variable {Y : Type uY} [TopologicalSpace Y]

/-- Point evaluation followed by the actual canonical scalar operator action. -/
private def pointRepresentation (y : Y) : C(Y, ℂ) →⋆ₐ[ℂ] (ℂ →L[ℂ] ℂ) :=
  (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).comp
    (ContinuousMap.evalStarAlgHom ℂ ℂ y)

@[simp]
private theorem pointRepresentation_apply (y : Y) (a : C(Y, ℂ)) (z : ℂ) :
    pointRepresentation y a z = a y * z := by
  change algebraMap ℂ (ℂ →L[ℂ] ℂ) (a y) z = a y * z
  rw [Algebra.algebraMap_eq_smul_one]
  simp

variable [Nonempty Y] [SeparableSpace Y]

/-- Every canonical dense point appears at infinitely many genuine scalar coordinates. -/
private def repeatedPoint (n : Index.{uH}) : Y :=
  denseSeq Y (Nat.unpair n.down).1

variable [CompactSpace Y]

/-- The actual repeated-evaluation operator representation is the existing canonical Hilbert sum. -/
def representation : C(Y, ℂ) →⋆ₐ[ℂ] (ScalarHilbert.{uH} →L[ℂ] ScalarHilbert.{uH}) :=
  StarAlgHom.hilbertDirectSum
    (fun n : ULift.{uH, 0} ℕ =>
      (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).comp
        (ContinuousMap.evalStarAlgHom ℂ ℂ (denseSeq Y (Nat.unpair n.down).1)))

@[simp]
theorem representation_apply (a : C(Y, ℂ)) (x : ScalarHilbert.{uH}) (n : ULift.{uH, 0} ℕ) :
    representation a x n = a (denseSeq Y (Nat.unpair n.down).1) * x n := by
  change pointRepresentation (repeatedPoint (Y := Y) n) a (x n) = _
  exact pointRepresentation_apply _ _ _

private def unitVector (n : Index.{uH}) : ScalarHilbert.{uH} := lp.single 2 n (1 : ℂ)

private theorem norm_unitVector (n : Index.{uH}) : ‖unitVector n‖ = 1 := by
  simpa only [unitVector, norm_one] using
    lp.norm_single (E := fun _ : Index.{uH} => ℂ) (p := (2 : ENNReal))
      (by norm_num) n (1 : ℂ)

private theorem unitVector_mem_closedBall (n : Index.{uH}) :
    unitVector n ∈ Metric.closedBall (0 : ScalarHilbert.{uH}) 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_unitVector] using
    (le_refl (1 : ℝ))

/-- Compactness forces each repeated coefficient to vanish in the original lp-two norm. -/
private theorem evaluation_eq_zero_of_isCompactOperator (a : C(Y, ℂ))
    (hCompact : IsCompactOperator
      (representation a : ScalarHilbert.{uH} →L[ℂ] ScalarHilbert.{uH})) (k : ℕ) :
    a (denseSeq Y k) = 0 := by
  by_contra ha
  let v : ℕ → ScalarHilbert.{uH} := fun n =>
    representation a (unitVector (ULift.up (Nat.pair k n)))
  have hsep {m n : ℕ} (hmn : m ≠ n) :
      ‖a (denseSeq Y k)‖ ≤ dist (v m) (v n) := by
    have hp : (ULift.up (Nat.pair k m) : Index.{uH}) ≠ ULift.up (Nat.pair k n) := by
      intro h
      have hs := congrArg (fun r : Index.{uH} => (Nat.unpair r.down).2) h
      exact hmn (by simpa only [Nat.unpair_pair] using hs)
    have hself : unitVector (ULift.up (Nat.pair k m)) (ULift.up (Nat.pair k m)) = (1 : ℂ) :=
      lp.single_apply_self 2 _ _
    have hother : unitVector (ULift.up (Nat.pair k n)) (ULift.up (Nat.pair k m)) = (0 : ℂ) :=
      lp.single_apply_ne 2 _ _ hp
    have hvm : v m (ULift.up (Nat.pair k m)) = a (denseSeq Y k) := by
      change representation a (unitVector (ULift.up (Nat.pair k m)))
        (ULift.up (Nat.pair k m)) = a (denseSeq Y k)
      rw [representation_apply, hself]
      simp only [Nat.unpair_pair, mul_one]
    have hvn : v n (ULift.up (Nat.pair k m)) = 0 := by
      change representation a (unitVector (ULift.up (Nat.pair k n)))
        (ULift.up (Nat.pair k m)) = 0
      rw [representation_apply, hother, mul_zero]
    have hcoord : (v m - v n) (ULift.up (Nat.pair k m)) = a (denseSeq Y k) := by
      change v m (ULift.up (Nat.pair k m)) - v n (ULift.up (Nat.pair k m)) = _
      rw [hvm, hvn, sub_zero]
    calc
      ‖a (denseSeq Y k)‖ = ‖(v m - v n) (ULift.up (Nat.pair k m))‖ := by rw [hcoord]
      _ ≤ ‖v m - v n‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ = dist (v m) (v n) := (dist_eq_norm _ _).symm
  obtain ⟨K, hK, hImage⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := (representation a : ScalarHilbert.{uH} →L[ℂ] ScalarHilbert.{uH}).toLinearMap) hCompact 1
  have hv : ∀ n, v n ∈ K := fun n =>
    hImage ⟨unitVector (ULift.up (Nat.pair k n)), unitVector_mem_closedBall _, rfl⟩
  obtain ⟨z, _hz, φ, hφ, hLimit⟩ := hK.tendsto_subseq hv
  have hCauchy : CauchySeq (v ∘ φ) := hLimit.cauchy_map
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hCauchy
    ‖a (denseSeq Y k)‖ (norm_pos_iff.mpr ha)
  have hSmall := hN N (le_refl N) (N + 1) (Nat.le_succ N)
  have hLarge := hsep (hφ (Nat.lt_succ_self N)).ne
  exact (not_lt_of_ge hLarge) hSmall

/-- Only the zero continuous coefficient gives a compact repeated-evaluation operator. -/
theorem eq_zero_of_isCompactOperator (a : C(Y, ℂ))
    (hCompact : IsCompactOperator
      (representation a : ScalarHilbert.{uH} →L[ℂ] ScalarHilbert.{uH})) : a = 0 := by
  have hDense : (a : Y → ℂ) ∘ denseSeq Y = (fun _ : Y => (0 : ℂ)) ∘ denseSeq Y := by
    funext k
    exact evaluation_eq_zero_of_isCompactOperator a hCompact k
  have hEqual := (denseRange_denseSeq Y).equalizer a.continuous continuous_const hDense
  apply ContinuousMap.ext
  intro y
  exact congrFun hEqual y

/-- The genuine split representation in the original compact-operator quotient. -/
def calkinRepresentation : C(Y, ℂ) →⋆ₐ[ℂ] CalkinAlgebra ℂ ScalarHilbert.{uH} :=
  (classStarMap (H := ScalarHilbert.{uH})).comp representation

/-- Repeating every dense point makes the actual Calkin representation faithful. -/
theorem calkinRepresentation_injective :
    Function.Injective
      (calkinRepresentation (Y := Y) : C(Y, ℂ) →⋆ₐ[ℂ] CalkinAlgebra ℂ ScalarHilbert.{uH}) := by
  intro a b hab
  have hc : IsCompactOperator
      (representation (a - b) : ScalarHilbert.{uH} →L[ℂ] ScalarHilbert.{uH}) := by
    apply (classStarMap_eq_zero_iff _).mp
    change (calkinRepresentation (a - b) : CalkinAlgebra ℂ ScalarHilbert.{uH}) = 0
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_isCompactOperator (a - b) hc)

/-- The split Calkin representation retains the exact full range of each continuous coefficient. -/
theorem spectrum_calkinRepresentation (a : C(Y, ℂ)) :
    spectrum ℂ (calkinRepresentation a : CalkinAlgebra ℂ ScalarHilbert.{uH}) = Set.range a := by
  let φ : C(Y, ℂ) →⋆ₐ[ℂ] CalkinAlgebra ℂ ScalarHilbert.{uH} := calkinRepresentation
  let S := φ.range
  have : IsClosed (S : Set (CalkinAlgebra ℂ ScalarHilbert.{uH})) := by
    change IsClosed (Set.range φ)
    exact (NonUnitalStarAlgHom.isometry φ calkinRepresentation_injective).isClosedEmbedding.isClosed_range
  let e := StarAlgEquiv.ofInjective φ calkinRepresentation_injective
  calc
    spectrum ℂ (φ a) = spectrum ℂ (e a : S) := (S.spectrum_eq (a := e a)).symm
    _ = spectrum ℂ a := AlgEquiv.spectrum_eq e.toAlgEquiv a
    _ = Set.range a := ContinuousMap.spectrum_eq_range a

end CalkinAlgebra.RepeatedEvaluation

end

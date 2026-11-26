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
# Repeated dense evaluations in a Calkin algebra

Let `Y` be a nonempty compact separable topological space and `y_k = denseSeq Y k`. On `H_u = lp
(fun _ : ULift ℕ => ℂ) 2`, define the diagonal representation `π(f)x_n = f(y_(Nat.unpair
n.down).1) * x_n` for `f : C(Y,ℂ)`. Each dense point appears at infinitely many paired indices.

If `π(f)` is compact, every repeated coefficient vanishes; density and continuity then give
`f=0`. Therefore the Calkin representation `C(Y,ℂ) → Q(H_u)` is injective and has spectrum
`σ(π̄(f)) = f(Y)`. It lifts through the bounded operator representation `π`. The Hilbert space
is separable and infinite-dimensional, with its lp-two norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace CalkinAlgebra.RepeatedEvaluation

universe uH uY

/-- **Lifted countable coordinate index.** `Index = ULift ℕ` preserves the natural-number
coordinate set in the selected Hilbert-space universe. -/
private abbrev Index := ULift.{uH, 0} ℕ

/-- **Countable scalar Hilbert space.** `ScalarHilbert = lp (fun _ : ULift ℕ => ℂ) 2`, with the
square-summable scalar norm and inner product. -/
abbrev ScalarHilbert : Type uH := lp (fun _ : ULift.{uH, 0} ℕ => ℂ) 2

private def scalarHilbertBasis : HilbertBasis Index.{uH} ℂ ScalarHilbert.{uH} :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- **Separability of the lifted scalar Hilbert sum.** The space `lp(ULift ℕ,ℂ,2)` is separable
because its countable coordinate vectors have dense complex span. -/
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

/-- **Infinite dimension of the scalar Hilbert sum.** `lp(ULift ℕ,ℂ,2)` is not finite-dimensional
over `ℂ`, as its infinitely many coordinate vectors are linearly independent. -/
theorem scalarHilbert_infinite : ¬ FiniteDimensional ℂ ScalarHilbert.{uH} := by
  intro h
  let : FiniteDimensional ℂ ScalarHilbert.{uH} := h
  exact Module.Finite.not_linearIndependent_of_infinite (R := ℂ)
    (scalarHilbertBasis : Index.{uH} → ScalarHilbert.{uH})
    scalarHilbertBasis.orthonormal.linearIndependent

variable {Y : Type uY} [TopologicalSpace Y]

/-- **Point-evaluation operator representation.** At a point `y : Y`, the unital complex star
homomorphism sends `f : C(Y,ℂ)` to the scalar operator `z ↦ f(y)*z` on `ℂ`. -/
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

/-- **Repeated dense point at a scalar coordinate.** For a nonempty compact separable topological
space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. the point at `n :
ULift ℕ` is `y_(Nat.unpair n.down).1`, so each dense point occurs infinitely many times. -/
private def repeatedPoint (n : Index.{uH}) : Y :=
  denseSeq Y (Nat.unpair n.down).1

variable [CompactSpace Y]

/-- **Diagonal representation by repeated evaluations.** For a nonempty compact separable
topological space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. the
unital star homomorphism `C(Y,ℂ) → B(H_u)` acts by `(π(f)x)_n = f(y_(Nat.unpair n.down).1) *
x_n`. -/
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

/-- **Vanishing of repeated compact coefficients.** For a nonempty compact separable topological
space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. if
`representation f` is compact on `H_u`, then `f(y_k)=0` for each `k : ℕ`. -/
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

/-- **Zero coefficient of a compact evaluation operator.** For a nonempty compact separable
topological space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. if
the repeated-evaluation operator `representation f` is compact, then `f : C(Y,ℂ)` is zero. -/
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

/-- **Calkin representation of continuous functions.** For a nonempty compact separable
topological space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. the
unital star homomorphism `C(Y,ℂ) → Q(H_u)` is the compact-ideal class of the
repeated-evaluation operator `π(f)`. -/
def calkinRepresentation : C(Y, ℂ) →⋆ₐ[ℂ] CalkinAlgebra ℂ ScalarHilbert.{uH} :=
  (classStarMap (H := ScalarHilbert.{uH})).comp representation

/-- **Faithfulness of repeated evaluations modulo compacts.** For a nonempty compact separable
topological space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`.
`calkinRepresentation` is injective because only `f=0` gives a compact repeated-evaluation
operator. -/
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

/-- **Spectrum of a repeated-evaluation Calkin class.** For a nonempty compact separable
topological space `Y`, let `H_u = lp (fun _ : ULift ℕ => ℂ) 2` and `y_k = denseSeq Y k`. for
every `f : C(Y,ℂ)`, `spectrum ℂ (calkinRepresentation f) = Set.range f`. -/
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

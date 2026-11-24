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

public import MathlibExt.Analysis.InnerProductSpace.Operator.CompactBasisEquivalence

/-!
# Values of the computed compact matrix completion equivalence

The basis equivalence has the original completed compact embedding as its
forward function. Its two inverse equations are the ordinary inverse laws of
that same equivalence, with the forward characteristic substituted.

The raw normed-ring, group, metric, scalar, completion and compact-ideal
parents are unchanged. Ambient completeness comes from the genuine basis;
no inverse, target model, density or raw completeness is an input.
-/

@[expose] public section

noncomputable section

namespace HilbertBasis

universe uH

/-- The computed basis equivalence has the original completed forward values
and both inverse identities on the same completion and actual compact ideal. -/
theorem compactMatrixCompletionEquiv_characteristics
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) :
    letI : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace;
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    let G : ℕ → Type :=
      fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ;
    let f : ∀ n m (_h : n ≤ m), G n →⋆ₙₐ[ℂ] G m :=
      fun _ _ h => CStarMatrix.zeroExtendStarAlgHom (Nat.succ_le_succ h);
    letI : ∀ n, NonUnitalCStarAlgebra (G n) := fun _ => inferInstance;
    letI : DirectedSystem G (f · · ·) :=
      CStarMatrix.positive_stage_directed_system ℂ;
    let D := _root_.DirectLimit G f;
    let hNorm : ∀ n m (h : n ≤ m) (X : G n), ‖f n m h X‖ = ‖X‖ :=
      fun n m h X =>
        (CStarMatrix.zeroExtendStarAlgHom_isometry
          (A := ℂ) (Nat.succ_le_succ h)).norm_map_of_map_zero
            (map_zero (f n m h)) X;
    let nr : NonUnitalNormedRing D :=
      DirectLimit.nonUnitalNormedRingOfNormPreserving f hNorm;
    letI : NonUnitalNormedRing D := nr;
    let ng : NormedAddCommGroup D :=
      @NonUnitalNormedRing.toNormedAddCommGroup D nr;
    letI : NormedAddCommGroup D := ng;
    let us : UniformSpace D :=
      ng.toMetricSpace.toPseudoMetricSpace.toUniformSpace;
    letI : UniformSpace D := us;
    let ts : TopologicalSpace D := us.toTopologicalSpace;
    letI : TopologicalSpace D := ts;
    let ns : NormedSpace ℂ D :=
      DirectLimit.normedSpaceOfNormPreserving (𝕜 := ℂ) f hNorm;
    letI : NormedSpace ℂ D := ns;
    letI : CStarRing D :=
      DirectLimit.cstar_ring_of_norm_preserving f hNorm;
    let C := UniformSpace.Completion D;
    let completedCStar : NonUnitalCStarAlgebra C :=
      CStarAlgebra.completionNonUnitalCStarAlgebra D;
    letI : NonUnitalCStarAlgebra C := completedCStar;
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let e : C ≃⋆ₐ[ℂ] J.carrier := b.compactMatrixCompletionEquiv;
    let Φ : C →⋆ₙₐ[ℂ] J.carrier := b.orthonormal.completedCompactEmbedding;
    (∀ x : C, e x = Φ x) ∧
      (∀ x : C, e.symm (Φ x) = x) ∧
        ∀ T : J.carrier, Φ (e.symm T) = T := by
  let : CompleteSpace H := b.repr.toIsometryEquiv.completeSpace
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let G : ℕ → Type :=
    fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  let f : ∀ n m (_h : n ≤ m), G n →⋆ₙₐ[ℂ] G m :=
    fun _ _ h => CStarMatrix.zeroExtendStarAlgHom (Nat.succ_le_succ h)
  let : ∀ n, NonUnitalCStarAlgebra (G n) := fun _ => inferInstance
  let : DirectedSystem G (f · · ·) :=
    CStarMatrix.positive_stage_directed_system ℂ
  let D := _root_.DirectLimit G f
  let hNorm : ∀ n m (h : n ≤ m) (X : G n), ‖f n m h X‖ = ‖X‖ :=
    fun n m h X =>
      (CStarMatrix.zeroExtendStarAlgHom_isometry
        (A := ℂ) (Nat.succ_le_succ h)).norm_map_of_map_zero
          (map_zero (f n m h)) X
  let nr : NonUnitalNormedRing D :=
    DirectLimit.nonUnitalNormedRingOfNormPreserving f hNorm
  let : NonUnitalNormedRing D := nr
  let ng : NormedAddCommGroup D :=
    @NonUnitalNormedRing.toNormedAddCommGroup D nr
  let : NormedAddCommGroup D := ng
  let us : UniformSpace D :=
    ng.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : UniformSpace D := us
  let ts : TopologicalSpace D := us.toTopologicalSpace
  let : TopologicalSpace D := ts
  let ns : NormedSpace ℂ D :=
    DirectLimit.normedSpaceOfNormPreserving (𝕜 := ℂ) f hNorm
  let : NormedSpace ℂ D := ns
  let : CStarRing D :=
    DirectLimit.cstar_ring_of_norm_preserving f hNorm
  let C := UniformSpace.Completion D
  let completedCStar : NonUnitalCStarAlgebra C :=
    CStarAlgebra.completionNonUnitalCStarAlgebra D
  let : NonUnitalCStarAlgebra C := completedCStar
  let J : ClosedStarIdeal (H →L[ℂ] H) :=
    compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  let e : C ≃⋆ₐ[ℂ] J.carrier := b.compactMatrixCompletionEquiv
  let Φ : C →⋆ₙₐ[ℂ] J.carrier := b.orthonormal.completedCompactEmbedding
  change (∀ x : C, e x = Φ x) ∧
    (∀ x : C, e.symm (Φ x) = x) ∧ ∀ T : J.carrier, Φ (e.symm T) = T
  have hForward (x : C) : e x = Φ x := by
    rfl
  refine ⟨hForward, ?_, ?_⟩
  · intro x
    rw [← hForward x]
    exact e.symm_apply_apply x
  · intro T
    rw [← hForward (e.symm T)]
    exact e.apply_symm_apply T

end HilbertBasis

end

end

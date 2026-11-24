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

public import MathlibExt.Analysis.InnerProductSpace.Operator.CompactCompletion
public import MathlibExt.Analysis.InnerProductSpace.Operator.BasisCornerDensity

/-!
# Surjectivity of the completed compact map for a Hilbert basis

A genuine natural-number complex Hilbert basis derives ambient completeness.
The positive matrix corners lie in the original completed compact map's range,
so their proved density makes that range dense. The same completed isometry
has closed range because its source is the ordinary completion.

All raw, metric, scalar, completion and compact-ideal dictionaries are retained.
No raw completeness, target density, inverse or replacement carrier is assumed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace HilbertBasis

universe uH

/-- The single completed compact embedding is surjective for a genuine
natural-number Hilbert basis. Completeness is derived from its representation;
the closed-range argument applies to the completion, not to the raw limit. -/
theorem completedCompactEmbedding_surjective
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
    Function.Surjective (b.orthonormal.completedCompactEmbedding : C → J.carrier) := by
  classical
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
  let μ : D →⋆ₙₐ[ℂ] J.carrier := b.orthonormal.rawCompactEmbedding
  let Φ : C →⋆ₙₐ[ℂ] J.carrier := b.orthonormal.completedCompactEmbedding
  change Function.Surjective (Φ : C → J.carrier)
  let hv : ∀ n : ℕ, Orthonormal ℂ (fun i : Fin (n + 1) => b i.val) :=
    fun _ => b.orthonormal.comp (fun i => i.val) (fun _ _ h => Fin.ext h)
  let σ : ∀ n : ℕ, G n →⋆ₙₐ[ℂ] J.carrier := fun n => (hv n).compactCorner
  have hCoe (z : D) : Φ (z : C) = μ z :=
    b.orthonormal.completedCompactEmbedding_coe z
  have hRep (n : ℕ) (X : G n) :
      Φ ((⟦⟨n, X⟩⟧ : D) : C) = σ n X := by
    apply Subtype.ext
    exact
      (congrArg (fun T : J.carrier => (T : H →L[ℂ] H))
        (hCoe (⟦⟨n, X⟩⟧ : D))).trans
        ((b.orthonormal.rawCompactEmbedding_mk n X).trans
          ((hv n).compactCorner_coe X).symm)
  have hSubset : (⋃ n : ℕ, Set.range (σ n)) ⊆ Set.range (Φ : C → J.carrier) := by
    intro T hT
    obtain ⟨n, X, hX⟩ := Set.mem_iUnion.mp hT
    exact ⟨((⟦⟨n, X⟩⟧ : D) : C), (hRep n X).trans hX⟩
  have hDense : Dense (⋃ n : ℕ, Set.range (σ n)) :=
    b.dense_iUnion_range_compactCorner
  have hDenseRange : Dense (Set.range (Φ : C → J.carrier)) :=
    Dense.mono hSubset hDense
  have hIso : Isometry (Φ : C → J.carrier) :=
    b.orthonormal.completedCompactEmbedding_norm_isometry.2
  have hClosed : IsClosed (Set.range (Φ : C → J.carrier)) :=
    hIso.isClosedEmbedding.isClosed_range
  intro T
  have hT : T ∈ closure (Set.range (Φ : C → J.carrier)) := hDenseRange T
  rw [hClosed.closure_eq] at hT
  exact hT

end HilbertBasis

end

end

/-! ## The equivalence determined by the same completed map -/

@[expose] public section

noncomputable section

namespace HilbertBasis

universe uH

/-- The actual positive matrix completion is star-algebra equivalent to the
compact ideal for a genuine natural-number Hilbert basis. The forward function
is the original completed compact embedding; its inverse uses only that map's
proved injectivity and surjectivity. All norm and completion parents remain fixed. -/
noncomputable def compactMatrixCompletionEquiv
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
    C ≃⋆ₐ[ℂ] J.carrier := by
  classical
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
  let Φ : C →⋆ₙₐ[ℂ] J.carrier := b.orthonormal.completedCompactEmbedding
  change C ≃⋆ₐ[ℂ] J.carrier
  have hIso : Isometry (Φ : C → J.carrier) :=
    b.orthonormal.completedCompactEmbedding_norm_isometry.2
  have hSurj : Function.Surjective (Φ : C → J.carrier) :=
    b.completedCompactEmbedding_surjective
  exact StarAlgEquiv.ofBijective Φ ⟨hIso.injective, hSurj⟩

end HilbertBasis

end

end

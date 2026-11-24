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

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.DirectLimit
public import MathlibExt.Analysis.InnerProductSpace.Operator.FiniteCoordinateCorner
public import MathlibExt.Analysis.Normed.Ring.DirectLimit
public import MathlibExt.Analysis.Normed.Module.DirectLimit

/-!
# The literal raw compact embedding of an infinite orthonormal family

The positive C-star matrix stages are glued by their actual top-left padding.
The raw carrier and its normed ring, group, metric, topology and scalar values
are the existing norm-preserving direct-limit dictionaries. The target is the
actual compact closed star ideal with its inherited operator norm.

Finite-corner compatibility is proved, not supplied. The family need not
span the complete complex Hilbert space. No completeness of the raw limit,
completion map, target density, surjectivity or spatial identification is used.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Orthonormal

universe uH

/-- The actual nonunital star-algebra map from the positive matrix raw limit
into compact operators, constructed from the given orthonormal family. -/
noncomputable def rawCompactEmbedding
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {β : ℕ → H} (hβ : Orthonormal ℂ β) :
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
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    D →⋆ₙₐ[ℂ] J.carrier := by
  classical
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let G : ℕ → Type :=
    fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  let f : ∀ n m (h : n ≤ m), G n →⋆ₙₐ[ℂ] G m :=
    fun _ _ h => CStarMatrix.zeroExtendStarAlgHom (Nat.succ_le_succ h)
  let : ∀ n, NonUnitalCStarAlgebra (G n) := fun n => inferInstance
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
  let J : ClosedStarIdeal (H →L[ℂ] H) :=
    compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  change D →⋆ₙₐ[ℂ] J.carrier
  let βn : ∀ n : ℕ, Fin (n + 1) → H := fun _ i => β i.val
  have hβn : ∀ n : ℕ, Orthonormal ℂ (βn n) := fun n =>
    hβ.comp (fun i : Fin (n + 1) => i.val) (fun _ _ hij => Fin.ext hij)
  let σ : ∀ n, G n →⋆ₙₐ[ℂ] J.carrier := fun n => (hβn n).compactCorner
  have hCompat : ∀ n m (h : n ≤ m) (X : G n), σ m (f n m h X) = σ n X := by
    intro n m h X
    simpa only [σ, f, βn, Function.comp_apply, Fin.val_castLE] using
      (hβn m).compactCorner_zeroExtend (Nat.succ_le_succ h) X
  let rawAlgebra : D →ₙₐ[ℂ] J.carrier :=
    DirectLimit.NonUnitalAlgebra.lift G f J.carrier
      (fun n => (σ n).toNonUnitalAlgHom) hCompat
  refine
    { toNonUnitalAlgHom := rawAlgebra
      map_star' := ?_ }
  intro z
  refine _root_.DirectLimit.induction (f := f) (fun n X => ?_) z
  rw [_root_.DirectLimit.star_def]
  change σ n (star X) = star (σ n X)
  exact map_star (σ n) X

/-- Every genuine raw stage representative has the literal column-ordered
finite rank-one value in the ambient bounded operators. -/
theorem rawCompactEmbedding_mk
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {β : ℕ → H} (hβ : Orthonormal ℂ β) :
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
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    ∀ (n : ℕ) (X : G n),
      (hβ.rawCompactEmbedding (⟦⟨n, X⟩⟧ : D) : H →L[ℂ] H) =
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          X i j • InnerProductSpace.rankOne ℂ (β i.val) (β j.val) := by
  classical
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let G : ℕ → Type :=
    fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  let f : ∀ n m (h : n ≤ m), G n →⋆ₙₐ[ℂ] G m :=
    fun _ _ h => CStarMatrix.zeroExtendStarAlgHom (Nat.succ_le_succ h)
  let : ∀ n, NonUnitalCStarAlgebra (G n) := fun n => inferInstance
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
  let J : ClosedStarIdeal (H →L[ℂ] H) :=
    compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  change ∀ (n : ℕ) (X : G n),
    (hβ.rawCompactEmbedding (⟦⟨n, X⟩⟧ : D) : H →L[ℂ] H) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        X i j • InnerProductSpace.rankOne ℂ (β i.val) (β j.val)
  intro n X
  let βn : Fin (n + 1) → H := fun i => β i.val
  have hβn : Orthonormal ℂ βn :=
    hβ.comp (fun i : Fin (n + 1) => i.val) (fun _ _ hij => Fin.ext hij)
  change (hβn.compactCorner X : H →L[ℂ] H) =
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      X i j • InnerProductSpace.rankOne ℂ (β i.val) (β j.val)
  exact hβn.compactCorner_coe X

/-- The constructed raw map preserves the existing representative norm and
is an isometry for that same norm-induced metric. -/
theorem rawCompactEmbedding_norm_isometry
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {β : ℕ → H} (hβ : Orthonormal ℂ β) :
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
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    (∀ z : D, ‖hβ.rawCompactEmbedding z‖ = ‖z‖) ∧
      Isometry (hβ.rawCompactEmbedding : D → J.carrier) := by
  classical
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let G : ℕ → Type :=
    fun n => CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  let f : ∀ n m (h : n ≤ m), G n →⋆ₙₐ[ℂ] G m :=
    fun _ _ h => CStarMatrix.zeroExtendStarAlgHom (Nat.succ_le_succ h)
  let : ∀ n, NonUnitalCStarAlgebra (G n) := fun n => inferInstance
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
  let J : ClosedStarIdeal (H →L[ℂ] H) :=
    compactEndomorphismClosedStarIdeal (H := H)
  let : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra
  change (∀ z : D, ‖hβ.rawCompactEmbedding z‖ = ‖z‖) ∧
    Isometry (hβ.rawCompactEmbedding : D → J.carrier)
  let μ : D →⋆ₙₐ[ℂ] J.carrier := hβ.rawCompactEmbedding
  let βn : ∀ n : ℕ, Fin (n + 1) → H := fun _ i => β i.val
  have hβn : ∀ n : ℕ, Orthonormal ℂ (βn n) := fun n =>
    hβ.comp (fun i : Fin (n + 1) => i.val) (fun _ _ hij => Fin.ext hij)
  have hRawNorm : ∀ z : D, ‖μ z‖ = ‖z‖ := by
    intro z
    refine _root_.DirectLimit.induction (f := f) (fun n X => ?_) z
    have hCorner : μ (⟦⟨n, X⟩⟧ : D) = (hβn n).compactCorner X := by
      apply Subtype.ext
      exact (hβ.rawCompactEmbedding_mk n X).trans
        ((hβn n).compactCorner_coe X).symm
    calc
      ‖μ (⟦⟨n, X⟩⟧ : D)‖ = ‖(hβn n).compactCorner X‖ := congrArg norm hCorner
      _ = ‖X‖ := (hβn n).compactCorner_norm X
      _ = ‖(⟦⟨n, X⟩⟧ : D)‖ :=
        (DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk f hNorm n X).symm
  exact ⟨hRawNorm, AddMonoidHomClass.isometry_of_norm μ hRawNorm⟩

end Orthonormal

end

end

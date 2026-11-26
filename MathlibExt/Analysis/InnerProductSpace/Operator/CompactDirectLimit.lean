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
# Algebraic matrix direct limit inside Hilbert-space compacts

Let `β_n` be an orthonormal family in a complete complex Hilbert space `H`. The matrix algebras
`M_(n+1)(ℂ)` form a direct system under top-left zero padding. Their algebraic direct limit `D`
has the norm `‖[n,X]‖=‖X‖`.

The nonunital star homomorphism `Φ_β : D → K(H)` sends `[n,X]` to `Σ_i,j<n+1 X_ij θ_(β_i,β_j)`.
It preserves norm and is an isometry. The family need not span `H`; neither completeness of `D`
nor surjectivity of `Φ_β` is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Orthonormal

universe uH

/-- **Algebraic matrix direct-limit map to compacts.** Let `H` be a complete complex Hilbert
space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let `D=lim_n
M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. `rawCompactEmbedding β : D →⋆ₙₐ[ℂ] K(H)` is the nonunital complex star
homomorphism `Φ_β`. -/
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

/-- **Finite matrix representative in the compact direct limit.** Let `H` be a complete
complex Hilbert space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let
`D=lim_n M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. for `X ∈ M_(n+1)(ℂ)`, the bounded operator representing
`rawCompactEmbedding β [n,X]` is the finite rank-one sum `Σ_i,j<n+1 X_ij θ_(β_i,β_j)`. -/
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

/-- **Isometry of the algebraic compact matrix embedding.** Let `H` be a complete complex
Hilbert space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let `D=lim_n
M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. the map `Φ_β=rawCompactEmbedding β` satisfies `‖Φ_β(z)‖=‖z‖` for every
`z ∈ D` and is an isometry from `D` to `K(H)`. -/
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

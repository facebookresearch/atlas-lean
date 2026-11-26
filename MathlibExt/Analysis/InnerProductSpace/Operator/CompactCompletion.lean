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

public import MathlibExt.Analysis.InnerProductSpace.Operator.CompactDirectLimit
public import MathlibExt.Analysis.CStarAlgebra.DirectLimit
public import MathlibExt.Analysis.CStarAlgebra.NonUnitalCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completed matrix embedding into Hilbert-space compacts

For an orthonormal family `β_n` in a complete complex Hilbert space, let `D=lim_n M_(n+1)(ℂ)`
along top-left zero padding, with its stage-preserving norm. Complete this normed algebra to
`C`.

The isometric star map `Φ_β : D → K(H)` given by its finite rank-one corners extends to an
isometric nonunital complex star homomorphism `Φ̂_β : C → K(H)`, with `Φ̂_β(ι z)=Φ_β(z)`. The
family need not span `H`; no density in the whole compact ideal or surjectivity is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Orthonormal

universe uH

/-- **Completed star embedding of matrix stages into compacts.** Let `H` be a complete complex
Hilbert space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let `D=lim_n
M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. for `C=Completion D`, `completedCompactEmbedding β : C →⋆ₙₐ[ℂ] K(H)`
is the extension `Φ̂_β` of the matrix-corner map `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)`. -/
noncomputable def completedCompactEmbedding
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
    letI : CStarRing D :=
      DirectLimit.cstar_ring_of_norm_preserving f hNorm;
    let C := UniformSpace.Completion D;
    let completedCStar : NonUnitalCStarAlgebra C :=
      CStarAlgebra.completionNonUnitalCStarAlgebra D;
    letI : NonUnitalCStarAlgebra C := completedCStar;
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    C →⋆ₙₐ[ℂ] J.carrier := by
  classical
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
  change C →⋆ₙₐ[ℂ] J.carrier
  let μ : D →⋆ₙₐ[ℂ] J.carrier := hβ.rawCompactEmbedding
  let μli : D →ₗᵢ[ℂ] J.carrier :=
    { LinearMap.ofClass μ with
      norm_map' := hβ.rawCompactEmbedding_norm_isometry.1 }
  let Φ : C →ₗᵢ[ℂ] J.carrier := μli.fromCompletion
  have hCoe : ∀ a : D, Φ (a : C) = μ a := by
    intro a
    exact μli.fromCompletion_apply_coe a
  have hΦ : Continuous (fun x : C => Φ x) := Φ.continuous
  have hMul : ∀ x y : C, Φ (x * y) = Φ x * Φ y := by
    intro x y
    have hLeft : Continuous (fun p : C × C => Φ (p.1 * p.2)) :=
      hΦ.comp (continuous_fst.mul continuous_snd)
    have hRight : Continuous (fun p : C × C => Φ p.1 * Φ p.2) :=
      (hΦ.comp continuous_fst).mul (hΦ.comp continuous_snd)
    refine UniformSpace.Completion.induction_on₂
      (α := D) (β := D) (p := fun x y => Φ (x * y) = Φ x * Φ y)
      x y (isClosed_eq hLeft hRight) ?_
    intro a b
    calc
      Φ ((a : C) * (b : C)) = Φ ((a * b : D) : C) :=
        congrArg (fun z : C => Φ z)
          (UniformSpace.Completion.nonUnitalCompletion_coe_mul D a b).symm
      _ = μ (a * b) := hCoe (a * b)
      _ = μ a * μ b := map_mul μ a b
      _ = Φ (a : C) * Φ (b : C) :=
        congrArg₂ (fun v w : J.carrier => v * w) (hCoe a).symm (hCoe b).symm
  have hStar : ∀ x : C, Φ (star x) = star (Φ x) := by
    intro x
    have hLeft : Continuous (fun x : C => Φ (star x)) :=
      hΦ.comp continuous_star
    have hRight : Continuous (fun x : C => star (Φ x)) :=
      continuous_star.comp hΦ
    refine UniformSpace.Completion.induction_on
      (α := D) (p := fun x => Φ (star x) = star (Φ x))
      x (isClosed_eq hLeft hRight) ?_
    intro a
    calc
      Φ (star (a : C)) = Φ ((star a : D) : C) :=
        congrArg (fun z : C => Φ z)
          (CStarAlgebra.completionNonUnitalCStarAlgebra_star_coe D a)
      _ = μ (star a) := hCoe (star a)
      _ = star (μ a) := map_star μ a
      _ = star (Φ (a : C)) := congrArg (star : J.carrier → J.carrier) (hCoe a).symm
  exact
    { toNonUnitalAlgHom :=
        { toFun := Φ
          map_zero' := map_zero Φ
          map_add' := fun x y => map_add Φ x y
          map_mul' := hMul
          map_smul' := fun c x => map_smul Φ c x }
      map_star' := hStar }

/-- **Completed compact embedding on an algebraic limit element.** Let `H` be a complete
complex Hilbert space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let
`D=lim_n M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. for `C=Completion D` and `z ∈ D`, `completedCompactEmbedding β (z :
C)=rawCompactEmbedding β z`. -/
theorem completedCompactEmbedding_coe
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
    letI : CStarRing D :=
      DirectLimit.cstar_ring_of_norm_preserving f hNorm;
    let C := UniformSpace.Completion D;
    let completedCStar : NonUnitalCStarAlgebra C :=
      CStarAlgebra.completionNonUnitalCStarAlgebra D;
    letI : NonUnitalCStarAlgebra C := completedCStar;
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    ∀ z : D, hβ.completedCompactEmbedding (z : C) = hβ.rawCompactEmbedding z := by
  classical
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
  change ∀ z : D,
    hβ.completedCompactEmbedding (z : C) = hβ.rawCompactEmbedding z
  let μ : D →⋆ₙₐ[ℂ] J.carrier := hβ.rawCompactEmbedding
  let μli : D →ₗᵢ[ℂ] J.carrier :=
    { LinearMap.ofClass μ with
      norm_map' := hβ.rawCompactEmbedding_norm_isometry.1 }
  let Φ : C →ₗᵢ[ℂ] J.carrier := μli.fromCompletion
  change ∀ z : D, Φ (z : C) = μ z
  intro z
  exact μli.fromCompletion_apply_coe z

/-- **Norm and metric preservation of the completed compact embedding.** Let `H` be a complete
complex Hilbert space and `β : ℕ → H` an orthonormal family, which need not span `H`. Let
`D=lim_n M_(n+1)(ℂ)` be the algebraic direct limit along top-left zero padding, with norm
`‖[n,X]‖=‖X‖`. Write `θ_(x,y)z=⟨y,z⟩x` and `Φ_β([n,X])=Σ_i,j<n+1 X_ij θ_(β_i,β_j)` for the
compact matrix map. on `C=Completion D`, `Φ̂_β=completedCompactEmbedding β` satisfies
`‖Φ̂_β(x)‖=‖x‖` for every `x ∈ C` and is an isometry into `K(H)`. -/
theorem completedCompactEmbedding_norm_isometry
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
    letI : CStarRing D :=
      DirectLimit.cstar_ring_of_norm_preserving f hNorm;
    let C := UniformSpace.Completion D;
    let completedCStar : NonUnitalCStarAlgebra C :=
      CStarAlgebra.completionNonUnitalCStarAlgebra D;
    letI : NonUnitalCStarAlgebra C := completedCStar;
    let J : ClosedStarIdeal (H →L[ℂ] H) :=
      compactEndomorphismClosedStarIdeal (H := H);
    letI : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    (∀ x : C, ‖hβ.completedCompactEmbedding x‖ = ‖x‖) ∧
      Isometry (hβ.completedCompactEmbedding : C → J.carrier) := by
  classical
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
  change (∀ x : C, ‖hβ.completedCompactEmbedding x‖ = ‖x‖) ∧
    Isometry (hβ.completedCompactEmbedding : C → J.carrier)
  let μ : D →⋆ₙₐ[ℂ] J.carrier := hβ.rawCompactEmbedding
  let μli : D →ₗᵢ[ℂ] J.carrier :=
    { LinearMap.ofClass μ with
      norm_map' := hβ.rawCompactEmbedding_norm_isometry.1 }
  let Φ : C →ₗᵢ[ℂ] J.carrier := μli.fromCompletion
  change (∀ x : C, ‖Φ x‖ = ‖x‖) ∧ Isometry (Φ : C → J.carrier)
  exact ⟨fun x => Φ.norm_map x, Φ.isometry⟩

end Orthonormal

end

end

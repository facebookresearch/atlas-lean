/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.OnePointAction
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The inherited orthogonal complement bundle and its actual frame quotient

The base consists of one-sided isometric embeddings. A frame is the original
two-sided `OrthogonalMatrixHom (a + n) k`, with the coefficient block first.
The total space is the closed matrix/vector subspace with the two equations
`A.transpose * A = 1` and `A.transpose *ᵥ v = 0`. No bundle trivialization,
CW structure, cofibrancy hypothesis, or operator right-module equivalence is
supplied. Every map in this module uses these inherited topologies.

The finite generator sends a frame `g` and a coefficient `x` to the final
columns of `g` and its first columns applied to `x`. Its graph identifies its
domain with a closed pullback of the compact frame parameter. This proves
properness directly. Orthogonal completion gives surjectivity in the actual
residual dimension. Its fibers are precisely the original first-block
orthogonal action, including its inverse-precomposition order.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Matrix Filter TopologicalSpace Topology
open scoped InnerProductSpace

namespace CategoryTheory.Spectra.OrthogonalComplementBundle

open CategoryTheory.Spectra

/-- Standard real Euclidean coordinates, with their original `PiLp` topology. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The actual one-sided matrix base of the complement bundle. -/
abbrev EmbeddingMatrix (n k : ℕ) :=
  {A : Matrix (Fin k) (Fin n) ℝ // A.transpose * A = 1}

/-- The actual inherited matrix/vector complement total space. -/
abbrev ComplementBundle (n k : ℕ) :=
  {p : Matrix (Fin k) (Fin n) ℝ × Euclidean k //
    p.1.transpose * p.1 = 1 ∧ p.1.transpose *ᵥ p.2.ofLp = 0}

/-- The frame parameter is the original two-sided matrix hom. -/
abbrev Frame (n k a : ℕ) := OrthogonalMatrixHom (a + n) k

instance matrix_locallyCompactSpace (m k : ℕ) :
    LocallyCompactSpace (Matrix (Fin k) (Fin m) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin k → Fin m → ℝ))

/-- The inherited one-sided base projection. -/
def bundleBase {n k : ℕ} (p : ComplementBundle n k) : EmbeddingMatrix n k :=
  ⟨p.1.1, p.2.1⟩

/-- The actual Euclidean vector in the complement fiber. -/
def bundleVector {n k : ℕ} (p : ComplementBundle n k) : Euclidean k := p.1.2

@[ext]
theorem embeddingMatrix_ext {n k : ℕ} {A B : EmbeddingMatrix n k}
    (h : A.1 = B.1) : A = B := Subtype.ext h

@[ext]
theorem complementBundle_ext {n k : ℕ} {p q : ComplementBundle n k}
    (hA : p.1.1 = q.1.1) (hv : p.1.2 = q.1.2) : p = q :=
  Subtype.ext (Prod.ext hA hv)

/-- The actual matrix base is a closed subspace of a finite real matrix space. -/
theorem embeddingMatrix_isClosed (n k : ℕ) :
    IsClosed {A : Matrix (Fin k) (Fin n) ℝ | A.transpose * A = 1} :=
  isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
    continuous_const

/-- The total space has the closed inherited matrix/vector topology. -/
theorem complementBundle_isClosed (n k : ℕ) :
    IsClosed {p : Matrix (Fin k) (Fin n) ℝ × Euclidean k |
      p.1.transpose * p.1 = 1 ∧ p.1.transpose *ᵥ p.2.ofLp = 0} := by
  apply IsClosed.inter
  · exact isClosed_eq
      (continuous_fst.matrix_transpose.matrix_mul continuous_fst)
      continuous_const
  · exact isClosed_eq
      (continuous_fst.matrix_transpose.matrix_mulVec
        ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp continuous_snd))
      continuous_const

instance embeddingMatrix_locallyCompact (n k : ℕ) :
    LocallyCompactSpace (EmbeddingMatrix n k) :=
  (embeddingMatrix_isClosed n k).locallyCompactSpace

instance complementBundle_locallyCompact (n k : ℕ) :
    LocallyCompactSpace (ComplementBundle n k) :=
  (complementBundle_isClosed n k).locallyCompactSpace

instance embeddingMatrix_pseudoMetrizable (n k : ℕ) :
    PseudoMetrizableSpace (EmbeddingMatrix n k) := by
  let _ : PseudoMetrizableSpace (Matrix (Fin k) (Fin n) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin k → Fin n → ℝ))
  exact IsInducing.subtypeVal.pseudoMetrizableSpace

instance complementBundle_pseudoMetrizable (n k : ℕ) :
    PseudoMetrizableSpace (ComplementBundle n k) := by
  let _ : PseudoMetrizableSpace (Matrix (Fin k) (Fin n) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin k → Fin n → ℝ))
  exact IsInducing.subtypeVal.pseudoMetrizableSpace

/-- Each entry of a matrix with orthonormal columns lies in the real unit interval. -/
theorem embeddingMatrix_entry_bound {n k : ℕ} (A : EmbeddingMatrix n k)
    (i : Fin k) (j : Fin n) : |A.1 i j| ≤ 1 := by
  have hdiag := congrFun (congrFun A.2 j) j
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ) j j = 1 := by simp
  rw [hone] at hdiag
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hdiag
  have hterm : A.1 i j ^ 2 ≤ ∑ l, A.1 l j ^ 2 := by
    exact Finset.single_le_sum (fun l _ ↦ sq_nonneg (A.1 l j))
      (Finset.mem_univ i)
  apply (sq_le_one_iff_abs_le_one _).mp
  calc
    A.1 i j ^ 2 ≤ ∑ l, A.1 l j ^ 2 := hterm
    _ = 1 := by simpa [pow_two] using hdiag

/-- Compactness is obtained from the actual closed bounded matrix base. -/
theorem embeddingMatrix_compact (n k : ℕ) : CompactSpace (EmbeddingMatrix n k) := by
  let T : Set (Matrix (Fin k) (Fin n) ℝ) := {A | A.transpose * A = 1}
  have hsubset : T ⊆ (Set.Icc (-1 : ℝ) 1).matrix := by
    intro A hA
    rw [Set.mem_matrix]
    intro i j
    exact abs_le.mp (embeddingMatrix_entry_bound (⟨A, hA⟩ : EmbeddingMatrix n k) i j)
  exact isCompact_iff_compactSpace.mp
    (isCompact_Icc.matrix.of_isClosed_subset (embeddingMatrix_isClosed n k) hsubset)

instance embeddingMatrix_compactSpace (n k : ℕ) :
    CompactSpace (EmbeddingMatrix n k) := embeddingMatrix_compact n k

/-- The actual coefficient-first frame retains the genuine bare matrix compactness supplier. -/
theorem frame_compact (n k a : ℕ) : CompactSpace (Frame n k a) :=
  OrthogonalMatrixHom.compact (a + n) k

theorem continuous_bundleBase {n k : ℕ} :
    Continuous (bundleBase : ComplementBundle n k → EmbeddingMatrix n k) := by
  apply Continuous.subtype_mk
  exact continuous_fst.comp continuous_subtype_val

theorem continuous_bundleVector {n k : ℕ} :
    Continuous (bundleVector : ComplementBundle n k → Euclidean k) :=
  continuous_snd.comp continuous_subtype_val

@[simp]
theorem bundleBase_val {n k : ℕ} (p : ComplementBundle n k) :
    (bundleBase p).1 = p.1.1 := rfl

@[simp]
theorem bundleVector_val {n k : ℕ} (p : ComplementBundle n k) :
    bundleVector p = p.1.2 := rfl

/-- The standard matrix linear map, with the original Euclidean coordinate dictionaries. -/
abbrev matrixLinear {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ) :
    Euclidean m →ₗ[ℝ] Euclidean k := Matrix.toLpLin 2 2 A

@[simp]
theorem matrixLinear_ofLp {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (x : Euclidean m) : (matrixLinear A x).ofLp = A *ᵥ x.ofLp := by
  exact Matrix.ofLp_toLpLin 2 2 A x

theorem matrixLinear_one {n : ℕ} (x : Euclidean n) :
    matrixLinear (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  apply WithLp.ofLp_injective
  rw [matrixLinear_ofLp, Matrix.one_mulVec]

theorem matrixLinear_zero {m k : ℕ} (x : Euclidean m) :
    matrixLinear (0 : Matrix (Fin k) (Fin m) ℝ) x = 0 := by
  apply WithLp.ofLp_injective
  rw [matrixLinear_ofLp, Matrix.zero_mulVec]
  rfl

/-- Matrix composition acts in the original left-multiplication order. -/
theorem matrixLinear_mul {l m k : ℕ}
    (A : Matrix (Fin k) (Fin m) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (x : Euclidean l) : matrixLinear (A * B) x = matrixLinear A (matrixLinear B x) := by
  apply WithLp.ofLp_injective
  simp only [matrixLinear_ofLp]
  exact (Matrix.mulVec_mulVec x.ofLp A B).symm

/-- A one-sided Gram equation proves preservation of the genuine Euclidean inner product. -/
theorem matrixLinear_inner {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (hA : A.transpose * A = 1) (x y : Euclidean m) :
    ⟪matrixLinear A x, matrixLinear A y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial, matrixLinear_ofLp]
  change (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ y.ofLp) = x.ofLp ⬝ᵥ y.ofLp
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

/-- The one-sided base matrix determines an actual Euclidean linear isometry. -/
def matrixIsometry {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (hA : A.transpose * A = 1) : Euclidean m →ₗᵢ[ℝ] Euclidean k :=
  (matrixLinear A).isometryOfInner (matrixLinear_inner A hA)

@[simp]
theorem matrixIsometry_apply {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (hA : A.transpose * A = 1) (x : Euclidean m) :
    matrixIsometry A hA x = matrixLinear A x := rfl

/-- The inherited one-sided equation is sufficient for norm preservation. -/
theorem matrixLinear_norm {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (hA : A.transpose * A = 1) (x : Euclidean m) : ‖matrixLinear A x‖ = ‖x‖ :=
  (matrixIsometry A hA).norm_map x

/-- A genuine one-sided embedding can exist only in increasing dimension. -/
theorem embeddingMatrix_dimension {n k : ℕ} (A : EmbeddingMatrix n k) : n ≤ k := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (matrixIsometry A.1 A.2).toLinearMap) (matrixIsometry A.1 A.2).injective
  simpa using h

/-- The actual total space is empty below source dimension. -/
theorem complementBundle_empty {n k : ℕ} (h : k < n) :
    IsEmpty (ComplementBundle n k) :=
  ⟨fun p => (Nat.not_le_of_lt h) (embeddingMatrix_dimension (bundleBase p))⟩

/-- Any original frame forces precisely its coefficient-first dimension equation. -/
theorem frame_dimension {n k a : ℕ} (g : Frame n k a) : a + n = k :=
  (OrthogonalMatrixHom.nonempty_iff (a + n) k).1 ⟨g⟩

/-- Every nonempty generator has the unique original residual coefficient dimension. -/
theorem frame_residual_dimension {n k a : ℕ} (g : Frame n k a) : a = k - n := by
  have h := frame_dimension g
  omega

/-- The final columns retain the source block of the original coefficient-first frame. -/
def finalPart {n k a : ℕ} (g : Frame n k a) : Matrix (Fin k) (Fin n) ℝ :=
  g.1.submatrix id (Fin.natAdd a)

/-- The first columns carry the original sphere coefficient. -/
def coefficientPart {n k a : ℕ} (g : Frame n k a) : Matrix (Fin k) (Fin a) ℝ :=
  g.1.submatrix id (Fin.castAdd n)

@[simp]
theorem finalPart_apply {n k a : ℕ} (g : Frame n k a) (i : Fin k) (j : Fin n) :
    finalPart g i j = g.1 i (Fin.natAdd a j) := rfl

@[simp]
theorem coefficientPart_apply {n k a : ℕ} (g : Frame n k a) (i : Fin k) (j : Fin a) :
    coefficientPart g i j = g.1 i (Fin.castAdd n j) := rfl

/-- The original full Gram equation supplies the final-block Gram equation. -/
theorem finalPart_gram {n k a : ℕ} (g : Frame n k a) :
    (finalPart g).transpose * finalPart g = 1 := by
  ext i j
  have h := congrFun (congrFun g.2.1 (Fin.natAdd a i)) (Fin.natAdd a j)
  simpa [finalPart, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The original full Gram equation supplies the coefficient-block Gram equation. -/
theorem coefficientPart_gram {n k a : ℕ} (g : Frame n k a) :
    (coefficientPart g).transpose * coefficientPart g = 1 := by
  ext i j
  have h := congrFun (congrFun g.2.1 (Fin.castAdd n i)) (Fin.castAdd n j)
  simpa [coefficientPart, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The two original column blocks are orthogonal, with the coefficient block first. -/
theorem finalPart_transpose_mul_coefficientPart {n k a : ℕ} (g : Frame n k a) :
    (finalPart g).transpose * coefficientPart g = 0 := by
  ext i j
  have hne : Fin.natAdd a i ≠ Fin.castAdd n j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  have h := congrFun (congrFun g.2.1 (Fin.natAdd a i)) (Fin.castAdd n j)
  simpa [finalPart, coefficientPart, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, hne] using h

/-- The reverse cross Gram equation is the literal transpose of the original one. -/
theorem coefficientPart_transpose_mul_finalPart {n k a : ℕ} (g : Frame n k a) :
    (coefficientPart g).transpose * finalPart g = 0 := by
  have h := congrArg Matrix.transpose (finalPart_transpose_mul_coefficientPart g)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h

/-- Both frame blocks together give the actual full target identity projector. -/
theorem frame_projector {n k a : ℕ} (g : Frame n k a) :
    coefficientPart g * (coefficientPart g).transpose +
      finalPart g * (finalPart g).transpose = 1 := by
  ext i j
  have h := congrFun (congrFun g.2.2 i) j
  simpa [coefficientPart, finalPart, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_add] using h

/-- A frame is determined by both ordered column blocks. -/
theorem frame_ext_parts {n k a : ℕ} {g h : Frame n k a}
    (hB : coefficientPart g = coefficientPart h) (hA : finalPart g = finalPart h) : g = h := by
  apply OrthogonalMatrixHom.ext
  ext i j
  rcases (finSumFinEquiv : Fin a ⊕ Fin n ≃ Fin (a + n)).surjective j with ⟨j, rfl⟩
  rcases j with j | j
  · simpa only [finSumFinEquiv_apply_left, coefficientPart_apply] using
      congrFun (congrFun hB i) j
  · simpa only [finSumFinEquiv_apply_right, finalPart_apply] using
      congrFun (congrFun hA i) j

theorem continuous_finalPart {n k a : ℕ} :
    Continuous (finalPart : Frame n k a → Matrix (Fin k) (Fin n) ℝ) := by
  exact continuous_subtype_val.matrix_submatrix id (Fin.natAdd a)

theorem continuous_coefficientPart {n k a : ℕ} :
    Continuous (coefficientPart : Frame n k a → Matrix (Fin k) (Fin a) ℝ) := by
  exact continuous_subtype_val.matrix_submatrix id (Fin.castAdd n)

/-- The actual one-sided embedding associated to an original full frame. -/
def frameBase {n k a : ℕ} (g : Frame n k a) : EmbeddingMatrix n k :=
  ⟨finalPart g, finalPart_gram g⟩

theorem continuous_frameBase {n k a : ℕ} :
    Continuous (frameBase : Frame n k a → EmbeddingMatrix n k) := by
  apply Continuous.subtype_mk
  exact continuous_finalPart

/-- The original coefficient-first finite matrix/vector comparison. -/
def rawMap (n k a : ℕ) : Frame n k a × Euclidean a → ComplementBundle n k := fun p =>
  ⟨(finalPart p.1, matrixLinear (coefficientPart p.1) p.2), finalPart_gram p.1, by
    simp only [matrixLinear_ofLp]
    rw [Matrix.mulVec_mulVec, finalPart_transpose_mul_coefficientPart,
      Matrix.zero_mulVec]⟩

@[simp]
theorem rawMap_matrix (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (rawMap n k a (g, x)).1.1 = finalPart g := rfl

@[simp]
theorem rawMap_vector (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (rawMap n k a (g, x)).1.2 = matrixLinear (coefficientPart g) x := rfl

@[simp]
theorem rawMap_base (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    bundleBase (rawMap n k a (g, x)) = frameBase g := rfl

/-- The finite comparison is jointly continuous for the inherited topologies. -/
theorem rawMap_continuous (n k a : ℕ) : Continuous (rawMap n k a) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_finalPart.comp continuous_fst
  · exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp
      ((continuous_coefficientPart.comp continuous_fst).matrix_mulVec
        ((EuclideanSpace.equiv (Fin a) ℝ).continuous.comp continuous_snd))

/-- The finite vector comparison preserves the norm exactly. -/
theorem rawMap_norm (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    ‖bundleVector (rawMap n k a (g, x))‖ = ‖x‖ :=
  matrixLinear_norm (coefficientPart g) (coefficientPart_gram g) x

/-- Recover the coefficient by the transpose of the original first block. -/
def recover (n k a : ℕ) : Frame n k a × ComplementBundle n k → Euclidean a :=
  fun p => matrixLinear (coefficientPart p.1).transpose p.2.1.2

theorem recover_continuous (n k a : ℕ) : Continuous (recover n k a) := by
  exact (EuclideanSpace.equiv (Fin a) ℝ).symm.continuous.comp
    (((continuous_coefficientPart.comp continuous_fst).matrix_transpose).matrix_mulVec
      ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp
        (continuous_bundleVector.comp continuous_snd)))

/-- Recovery uses the first-block Gram equation and returns the exact input coefficient. -/
theorem recover_rawMap (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    recover n k a (g, rawMap n k a (g, x)) = x := by
  apply WithLp.ofLp_injective
  simp only [recover, rawMap_vector, matrixLinear_ofLp]
  rw [Matrix.mulVec_mulVec, coefficientPart_gram, Matrix.one_mulVec]

/-- The target vector is the coefficient projector whenever the final frame block matches. -/
theorem coefficientPart_project_bundleVector {n k a : ℕ} (g : Frame n k a)
    (p : ComplementBundle n k) (hA : finalPart g = p.1.1) :
    coefficientPart g *ᵥ ((coefficientPart g).transpose *ᵥ p.1.2.ofLp) = p.1.2.ofLp := by
  have hzero : (finalPart g).transpose *ᵥ p.1.2.ofLp = 0 := by
    rw [hA]
    exact p.2.2
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M *ᵥ p.1.2.ofLp)
    (frame_projector g)
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at h
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzero,
    Matrix.mulVec_zero, add_zero] at h
  exact h

/-- The inverse finite function recovers every bundle point over its matching frame. -/
theorem rawMap_recover (n k a : ℕ) (g : Frame n k a) (p : ComplementBundle n k)
    (hA : finalPart g = p.1.1) : rawMap n k a (g, recover n k a (g, p)) = p := by
  apply complementBundle_ext
  · exact hA
  · apply WithLp.ofLp_injective
    simp only [rawMap_vector, recover, matrixLinear_ofLp]
    exact coefficientPart_project_bundleVector g p hA

/-- The actual pullback of the compact frame parameter over the one-sided base. -/
abbrev FramePullback (n k a : ℕ) :=
  {p : Frame n k a × ComplementBundle n k // finalPart p.1 = p.2.1.1}

/-- Equality of actual base matrices gives a closed pullback subspace. -/
theorem framePullback_isClosed (n k a : ℕ) :
    IsClosed {p : Frame n k a × ComplementBundle n k | finalPart p.1 = p.2.1.1} :=
  isClosed_eq (continuous_finalPart.comp continuous_fst)
    (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))

/-- The complete graph homeomorphism uses recovery in both inverse laws. -/
def rawGraphHomeomorph (n k a : ℕ) :
    Frame n k a × Euclidean a ≃ₜ FramePullback n k a where
  toFun p := ⟨(p.1, rawMap n k a p), rfl⟩
  invFun p := (p.1.1, recover n k a p.1)
  left_inv p := by
    rcases p with ⟨g, x⟩
    exact Prod.ext rfl (recover_rawMap n k a g x)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact rawMap_recover n k a p.1.1 p.1.2 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (rawMap_continuous n k a)
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((recover_continuous n k a).comp continuous_subtype_val)

/-- Projection from the closed frame pullback is proper because the original frame is compact. -/
theorem framePullback_projection_proper (n k a : ℕ) :
    IsProperMap (fun p : FramePullback n k a => p.1.2) :=
  isProperMap_snd_of_compactSpace.comp (framePullback_isClosed n k a).isProperMap_subtypeVal

/-- Properness of the actual finite matrix/vector comparison, without a supplied topology. -/
theorem rawMap_proper (n k a : ℕ) : IsProperMap (rawMap n k a) := by
  exact (framePullback_projection_proper n k a).comp
    (rawGraphHomeomorph n k a).isProperMap

/-- The original coclosed-compact filter is preserved, including empty frame spaces. -/
theorem rawMap_tendsto_coclosedCompact (n k a : ℕ) :
    Tendsto (rawMap n k a) (coclosedCompact (Frame n k a × Euclidean a))
      (coclosedCompact (ComplementBundle n k)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp (rawMap_proper n k a)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The proper finite map as an actual continuous-map value. -/
def rawContinuousMap (n k a : ℕ) : C(Frame n k a × Euclidean a, ComplementBundle n k) :=
  ⟨rawMap n k a, rawMap_continuous n k a⟩

/-- Orthonormal columns of an actual one-sided embedding, in original Euclidean coordinates. -/
theorem embeddingMatrix_columns_orthonormal {n k : ℕ} (A : EmbeddingMatrix n k) :
    Orthonormal ℝ (fun j : Fin n => matrixLinear A.1 ((EuclideanSpace.basisFun (Fin n) ℝ) j)) := by
  exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp_linearIsometry
    (matrixIsometry A.1 A.2)

/-- Matrix evaluation on the standard Euclidean basis gives the literal matrix column. -/
theorem matrixLinear_basis_coordinate {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℝ)
    (j : Fin m) (i : Fin k) :
    (matrixLinear A ((EuclideanSpace.basisFun (Fin m) ℝ) j)).ofLp i = A i j := by
  rw [matrixLinear_ofLp, EuclideanSpace.basisFun_apply]
  exact congrFun (Matrix.mulVec_single_one A j) i

/-- Complete the prescribed final columns to an original two-sided frame.
Only existence is asserted; the topology of the comparison never uses a continuous choice. -/
theorem exists_frame_completion (n k a : ℕ) (ha : a + n = k) (A : EmbeddingMatrix n k) :
    ∃ g : Frame n k a, finalPart g = A.1 := by
  classical
  subst k
  let s : Set (Fin (a + n)) := Set.range (Fin.natAdd a : Fin n → Fin (a + n))
  let w : Fin (a + n) → Euclidean (a + n) :=
    Fin.addCases (fun _ : Fin a => 0)
      (fun j : Fin n => matrixLinear A.1 ((EuclideanSpace.basisFun (Fin n) ℝ) j))
  have hw : Orthonormal ℝ (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rcases hi with ⟨i, rfl⟩
    rcases hj with ⟨j, rfl⟩
    have h := orthonormal_iff_ite.mp (embeddingMatrix_columns_orthonormal A) i j
    let zi : s := ⟨Fin.natAdd a i, Set.mem_range_self i⟩
    let zj : s := ⟨Fin.natAdd a j, Set.mem_range_self j⟩
    have hij : zi = zj ↔ i = j := by
      constructor
      · intro hz
        apply Fin.ext
        have hv := congrArg (fun z : s => z.1.val) hz
        change a + i.val = a + j.val at hv
        omega
      · intro hz
        subst j
        rfl
    change ⟪w (Fin.natAdd a i), w (Fin.natAdd a j)⟫_ℝ = if zi = zj then 1 else 0
    simp only [w, Fin.addCases_right]
    simpa only [hij] using h
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := Euclidean (a + n)) (ι := Fin (a + n)) (by simp) hw
  let M : Matrix (Fin (a + n)) (Fin (a + n)) ℝ := fun i j => (b j).ofLp i
  have hM : M.transpose * M = 1 := by
    ext i j
    change (∑ l, (b i).ofLp l * (b j).ofLp l) = if i = j then 1 else 0
    have h := orthonormal_iff_ite.mp b.orthonormal j i
    simpa [PiLp.inner_apply, RCLike.inner_apply', eq_comm, mul_comm] using h
  have hM' : M * M.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin (a + n)) (R := ℝ)).1
      ((Matrix.mem_orthogonalGroup_iff' (n := Fin (a + n)) (R := ℝ)).2 hM)
  refine ⟨⟨M, hM, hM'⟩, ?_⟩
  ext i j
  change (b (Fin.natAdd a j)).ofLp i = A.1 i j
  have hcol := hb (Fin.natAdd a j) (Set.mem_range_self j)
  have hcoordinate := congrArg (fun x : Euclidean (a + n) => x.ofLp i) hcol
  simpa [w, matrixLinear_basis_coordinate] using hcoordinate

/-- The raw finite map is onto in its actual residual dimension. -/
theorem rawMap_surjective (n k a : ℕ) (ha : a + n = k) :
    Function.Surjective (rawMap n k a) := by
  intro p
  obtain ⟨g, hg⟩ := exists_frame_completion n k a ha (bundleBase p)
  exact ⟨(g, recover n k a (g, p)), rawMap_recover n k a g p hg⟩

/-- The original first-block change of coefficient frame is categorical precomposition. -/
def changeCoefficient {n k a : ℕ} (g : Frame n k a) (r : OrthogonalMatrixHom a a) :
    Frame n k a := OrthogonalMatrixHom.comp
      (OrthogonalMatrixHom.blockSum r (OrthogonalMatrixHom.id n)) g

/-- First-block precomposition fixes the final source block. -/
theorem changeCoefficient_finalPart {n k a : ℕ} (g : Frame n k a)
    (r : OrthogonalMatrixHom a a) : finalPart (changeCoefficient g r) = finalPart g := by
  ext i j
  simpa [changeCoefficient, finalPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add] using congrFun (congrFun (Matrix.mul_one (finalPart g)) i) j

/-- First-block precomposition multiplies the coefficient block in the original order. -/
theorem changeCoefficient_coefficientPart {n k a : ℕ} (g : Frame n k a)
    (r : OrthogonalMatrixHom a a) :
    coefficientPart (changeCoefficient g r) = coefficientPart g * r.1 := by
  ext i j
  simp [changeCoefficient, coefficientPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add]

/-- The finite map obeys the original coefficient-first balancing relation. -/
theorem rawMap_balanced (n k a : ℕ) (g : Frame n k a)
    (r : OrthogonalMatrixHom a a) (x : Euclidean a) :
    rawMap n k a (changeCoefficient g r, x) = rawMap n k a (g, matrixLinear r.1 x) := by
  apply complementBundle_ext
  · exact changeCoefficient_finalPart g r
  · change matrixLinear (coefficientPart (changeCoefficient g r)) x =
      matrixLinear (coefficientPart g) (matrixLinear r.1 x)
    rw [changeCoefficient_coefficientPart, matrixLinear_mul]

/-- Continuity of the entire first-block precomposition, with the continuous group parameter. -/
theorem changeCoefficient_continuous (n k a : ℕ) :
    Continuous (fun p : Frame n k a × OrthogonalMatrixHom a a => changeCoefficient p.1 p.2) := by
  exact OrthogonalMatrixHom.continuous_comp.comp
    ((OrthogonalMatrixHom.continuous_blockSum.comp
      (continuous_snd.prodMk continuous_const)).prodMk continuous_fst)

/-- Equal final blocks imply equality after projection onto the coefficient span. -/
theorem coefficientProjection_sameBase {n k a : ℕ} (g h : Frame n k a)
    (hA : finalPart g = finalPart h) :
    coefficientPart g * ((coefficientPart g).transpose * coefficientPart h) =
      coefficientPart h := by
  have hp := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M * coefficientPart h)
    (frame_projector g)
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc] at hp
  rw [hA, finalPart_transpose_mul_coefficientPart, Matrix.mul_zero, add_zero] at hp
  exact hp

/-- The actual change of first-block basis between two completions of the same embedding. -/
def frameChange {n k a : ℕ} (g h : Frame n k a) (hA : finalPart g = finalPart h) :
    OrthogonalMatrixHom a a := by
  let R := (coefficientPart g).transpose * coefficientPart h
  refine ⟨R, ?_, ?_⟩
  · dsimp only [R]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      ((coefficientPart h).transpose * coefficientPart g) *
          ((coefficientPart g).transpose * coefficientPart h) =
        (coefficientPart h).transpose *
          (coefficientPart g * ((coefficientPart g).transpose * coefficientPart h)) := by
            simp only [Matrix.mul_assoc]
      _ = (coefficientPart h).transpose * coefficientPart h := by
        rw [coefficientProjection_sameBase g h hA]
      _ = 1 := coefficientPart_gram h
  · dsimp only [R]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      ((coefficientPart g).transpose * coefficientPart h) *
          ((coefficientPart h).transpose * coefficientPart g) =
        (coefficientPart g).transpose *
          (coefficientPart h * ((coefficientPart h).transpose * coefficientPart g)) := by
            simp only [Matrix.mul_assoc]
      _ = (coefficientPart g).transpose * coefficientPart g := by
        rw [coefficientProjection_sameBase h g hA.symm]
      _ = 1 := coefficientPart_gram g

@[simp]
theorem frameChange_val {n k a : ℕ} (g h : Frame n k a)
    (hA : finalPart g = finalPart h) :
    (frameChange g h hA).1 = (coefficientPart g).transpose * coefficientPart h := rfl

/-- The chosen algebraic frame change gives back the entire other original frame. -/
theorem changeCoefficient_frameChange {n k a : ℕ} (g h : Frame n k a)
    (hA : finalPart g = finalPart h) : changeCoefficient g (frameChange g h hA) = h := by
  apply frame_ext_parts
  · rw [changeCoefficient_coefficientPart, frameChange_val]
    exact coefficientProjection_sameBase g h hA
  · exact (changeCoefficient_finalPart g (frameChange g h hA)).trans hA

/-- The change of completion is unique, derived by the original transpose recovery. -/
theorem changeCoefficient_unique {n k a : ℕ} (g h : Frame n k a)
    (hA : finalPart g = finalPart h) (r : OrthogonalMatrixHom a a)
    (hr : changeCoefficient g r = h) : r = frameChange g h hA := by
  apply OrthogonalMatrixHom.ext
  have hB := congrArg coefficientPart hr
  rw [changeCoefficient_coefficientPart] at hB
  have h := congrArg (fun B : Matrix (Fin k) (Fin a) ℝ => (coefficientPart g).transpose * B) hB
  rw [← Matrix.mul_assoc, coefficientPart_gram, Matrix.one_mul] at h
  exact h

/-- The full finite map has exactly the original first-block action as its kernel. -/
theorem rawMap_eq_iff (n k a : ℕ) (g h : Frame n k a) (x y : Euclidean a) :
    rawMap n k a (g, x) = rawMap n k a (h, y) ↔
      ∃ r : OrthogonalMatrixHom a a,
        h = changeCoefficient g r ∧ x = matrixLinear r.1 y := by
  constructor
  · intro hp
    have hA : finalPart g = finalPart h := congrArg (fun p => p.1.1) hp
    let r := frameChange g h hA
    refine ⟨r, (changeCoefficient_frameChange g h hA).symm, ?_⟩
    calc
      x = recover n k a (g, rawMap n k a (g, x)) := (recover_rawMap n k a g x).symm
      _ = recover n k a (g, rawMap n k a (h, y)) := by rw [hp]
      _ = matrixLinear ((coefficientPart g).transpose * coefficientPart h) y := by
        exact (matrixLinear_mul (coefficientPart g).transpose (coefficientPart h) y).symm
      _ = matrixLinear r.1 y := rfl
  · rintro ⟨r, rfl, rfl⟩
    exact (rawMap_balanced n k a g r y).symm

/-- The raw comparison is injective on each coefficient fiber over a fixed original frame. -/
theorem rawMap_fixedFrame_injective (n k a : ℕ) (g : Frame n k a) :
    Function.Injective (fun x : Euclidean a => rawMap n k a (g, x)) := by
  intro x y h
  exact (recover_rawMap n k a g x).symm.trans
    ((congrArg (fun p => recover n k a (g, p)) h).trans (recover_rawMap n k a g y))

/-- Postcompose an actual one-sided embedding and its complement vector by a bare isometry. -/
def targetMap {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) : ComplementBundle n l :=
  ⟨(t.1 * p.1.1, matrixLinear t.1 p.1.2), by
    rw [Matrix.transpose_mul]
    calc
      (p.1.1.transpose * t.1.transpose) * (t.1 * p.1.1) =
        p.1.1.transpose * ((t.1.transpose * t.1) * p.1.1) := by
          simp only [Matrix.mul_assoc]
      _ = p.1.1.transpose * p.1.1 := by rw [t.2.1]; simp
      _ = 1 := p.2.1, by
    simp only [matrixLinear_ofLp, Matrix.transpose_mul]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, t.2.1, Matrix.mul_one, p.2.2]⟩

/-- Precompose the one-sided source embedding by a bare isometry.
Its complement vector stays put. -/
def sourceMap {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) : ComplementBundle m k :=
  ⟨(p.1.1 * s.1, p.1.2), by
    rw [Matrix.transpose_mul]
    calc
      (s.1.transpose * p.1.1.transpose) * (p.1.1 * s.1) =
        s.1.transpose * ((p.1.1.transpose * p.1.1) * s.1) := by
          simp only [Matrix.mul_assoc]
      _ = s.1.transpose * s.1 := by rw [p.2.1]; simp
      _ = 1 := s.2.1, by
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, p.2.2, Matrix.mulVec_zero]⟩

@[simp]
theorem targetMap_matrix {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) : (targetMap t p).1.1 = t.1 * p.1.1 := rfl

@[simp]
theorem targetMap_vector {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) : (targetMap t p).1.2 = matrixLinear t.1 p.1.2 := rfl

@[simp]
theorem sourceMap_matrix {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) : (sourceMap s p).1.1 = p.1.1 * s.1 := rfl

@[simp]
theorem sourceMap_vector {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) : (sourceMap s p).1.2 = p.1.2 := rfl

/-- The whole target parameter action is jointly continuous in the actual matrix topology. -/
theorem targetMap_joint_continuous (n k l : ℕ) :
    Continuous (fun p : OrthogonalMatrixHom k l × ComplementBundle n k =>
      targetMap p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_fst.subtype_val.matrix_mul
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  · exact (EuclideanSpace.equiv (Fin l) ℝ).symm.continuous.comp
      (continuous_fst.subtype_val.matrix_mulVec
        ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp
          (continuous_bundleVector.comp continuous_snd)))

/-- The whole source parameter action is jointly continuous for one-sided embeddings. -/
theorem sourceMap_joint_continuous (m n k : ℕ) :
    Continuous (fun p : OrthogonalMatrixHom m n × ComplementBundle n k =>
      sourceMap p.1 p.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).matrix_mul
    continuous_fst.subtype_val).prodMk (continuous_bundleVector.comp continuous_snd)

theorem targetMap_continuous {n k l : ℕ} (t : OrthogonalMatrixHom k l) :
    Continuous (targetMap (n := n) t) :=
  (targetMap_joint_continuous n k l).comp (continuous_const.prodMk continuous_id)

theorem sourceMap_continuous {m n k : ℕ} (s : OrthogonalMatrixHom m n) :
    Continuous (sourceMap (k := k) s) :=
  (sourceMap_joint_continuous m n k).comp (continuous_const.prodMk continuous_id)

/-- Target isometries preserve the complement-vector norm. -/
theorem targetMap_norm {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) : ‖bundleVector (targetMap t p)‖ = ‖bundleVector p‖ :=
  matrixLinear_norm t.1 t.2.1 p.1.2

/-- Source precomposition preserves the complement vector itself. -/
theorem sourceMap_norm {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) : ‖bundleVector (sourceMap s p)‖ = ‖bundleVector p‖ := rfl

@[simp]
theorem targetMap_id {n k : ℕ} (p : ComplementBundle n k) :
    targetMap (OrthogonalMatrixHom.id k) p = p := by
  apply complementBundle_ext
  · exact Matrix.one_mul p.1.1
  · exact matrixLinear_one p.1.2

@[simp]
theorem sourceMap_id {n k : ℕ} (p : ComplementBundle n k) :
    sourceMap (OrthogonalMatrixHom.id n) p = p := by
  apply complementBundle_ext
  · exact Matrix.mul_one p.1.1
  · rfl

/-- Target naturality retains categorical late-first matrix composition. -/
theorem targetMap_comp {n k l q : ℕ} (t : OrthogonalMatrixHom k l)
    (t' : OrthogonalMatrixHom l q) (p : ComplementBundle n k) :
    targetMap (OrthogonalMatrixHom.comp t t') p = targetMap t' (targetMap t p) := by
  apply complementBundle_ext
  · exact Matrix.mul_assoc t'.1 t.1 p.1.1
  · exact matrixLinear_mul t'.1 t.1 p.1.2

/-- Source naturality is the original inverse-precomposition variance. -/
theorem sourceMap_comp {l m n k : ℕ} (s : OrthogonalMatrixHom l m)
    (s' : OrthogonalMatrixHom m n) (p : ComplementBundle n k) :
    sourceMap (OrthogonalMatrixHom.comp s s') p = sourceMap s (sourceMap s' p) := by
  apply complementBundle_ext
  · exact (Matrix.mul_assoc p.1.1 s'.1 s.1).symm
  · rfl

/-- Source and target changes commute on the full complement total space. -/
theorem targetMap_sourceMap {m n k l : ℕ} (s : OrthogonalMatrixHom m n)
    (t : OrthogonalMatrixHom k l) (p : ComplementBundle n k) :
    targetMap t (sourceMap s p) = sourceMap s (targetMap t p) := by
  apply complementBundle_ext
  · exact (Matrix.mul_assoc t.1 p.1.1 s.1).symm
  · rfl

/-- Transpose gives the true inverse of the target action. -/
theorem targetMap_transpose_left {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n k) : targetMap t.transpose (targetMap t p) = p := by
  rw [← targetMap_comp, OrthogonalMatrixHom.comp_transpose, targetMap_id]

/-- Both target inverse laws use the original two-sided frame equations. -/
theorem targetMap_transpose_right {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (p : ComplementBundle n l) : targetMap t (targetMap t.transpose p) = p := by
  rw [← targetMap_comp, OrthogonalMatrixHom.transpose_comp_self, targetMap_id]

/-- Transpose gives the true inverse of contravariant source precomposition. -/
theorem sourceMap_transpose_left {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle n k) : sourceMap s.transpose (sourceMap s p) = p := by
  rw [← sourceMap_comp, OrthogonalMatrixHom.transpose_comp_self, sourceMap_id]

/-- Both source inverse laws retain the original inverse-precomposition order. -/
theorem sourceMap_transpose_right {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (p : ComplementBundle m k) : sourceMap s (sourceMap s.transpose p) = p := by
  rw [← sourceMap_comp, OrthogonalMatrixHom.comp_transpose, sourceMap_id]

/-- An actual target isometry gives a homeomorphism of inherited complement total spaces. -/
def targetHomeomorph {n k l : ℕ} (t : OrthogonalMatrixHom k l) :
    ComplementBundle n k ≃ₜ ComplementBundle n l where
  toFun := targetMap t
  invFun := targetMap t.transpose
  left_inv := targetMap_transpose_left t
  right_inv := targetMap_transpose_right t
  continuous_toFun := targetMap_continuous t
  continuous_invFun := targetMap_continuous t.transpose

/-- An actual source isometry gives the contravariant inherited-total-space homeomorphism. -/
def sourceHomeomorph {m n k : ℕ} (s : OrthogonalMatrixHom m n) :
    ComplementBundle n k ≃ₜ ComplementBundle m k where
  toFun := sourceMap s
  invFun := sourceMap s.transpose
  left_inv := sourceMap_transpose_left s
  right_inv := sourceMap_transpose_right s
  continuous_toFun := sourceMap_continuous s
  continuous_invFun := sourceMap_continuous s.transpose

/-- Postcompose the original full frame in the target variable. -/
def targetFrame {n k l a : ℕ} (t : OrthogonalMatrixHom k l) (g : Frame n k a) :
    Frame n l a := OrthogonalMatrixHom.comp g t

/-- Precompose only the source block, with the coefficient block first and unchanged. -/
def sourceFrame {m n k a : ℕ} (s : OrthogonalMatrixHom m n) (g : Frame n k a) :
    Frame m k a := OrthogonalMatrixHom.comp
      (OrthogonalMatrixHom.blockSum (OrthogonalMatrixHom.id a) s) g

theorem targetFrame_finalPart {n k l a : ℕ} (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) : finalPart (targetFrame t g) = t.1 * finalPart g := by
  ext i j
  rfl

theorem targetFrame_coefficientPart {n k l a : ℕ} (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) : coefficientPart (targetFrame t g) = t.1 * coefficientPart g := by
  ext i j
  rfl

theorem sourceFrame_finalPart {m n k a : ℕ} (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) : finalPart (sourceFrame s g) = finalPart g * s.1 := by
  ext i j
  simp [sourceFrame, finalPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add]

theorem sourceFrame_coefficientPart {m n k a : ℕ} (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) : coefficientPart (sourceFrame s g) = coefficientPart g := by
  ext i j
  simpa [sourceFrame, coefficientPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add] using congrFun (congrFun (Matrix.mul_one (coefficientPart g)) i) j

/-- Raw comparison naturality in the target, on every original continuous frame. -/
theorem rawMap_target_naturality {n k l a : ℕ} (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) (x : Euclidean a) :
    rawMap n l a (targetFrame t g, x) = targetMap t (rawMap n k a (g, x)) := by
  apply complementBundle_ext
  · exact targetFrame_finalPart t g
  · change matrixLinear (coefficientPart (targetFrame t g)) x =
      matrixLinear t.1 (matrixLinear (coefficientPart g) x)
    rw [targetFrame_coefficientPart, matrixLinear_mul]

/-- Raw comparison naturality in the source, with original coefficient-first precomposition. -/
theorem rawMap_source_naturality {m n k a : ℕ} (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) (x : Euclidean a) :
    rawMap m k a (sourceFrame s g, x) = sourceMap s (rawMap n k a (g, x)) := by
  apply complementBundle_ext
  · exact sourceFrame_finalPart s g
  · change matrixLinear (coefficientPart (sourceFrame s g)) x =
      matrixLinear (coefficientPart g) x
    rw [sourceFrame_coefficientPart]

/-- Both actual endpoint variables retain their independent original actions. -/
theorem rawMap_endpoint_naturality {m n k l a : ℕ} (s : OrthogonalMatrixHom m n)
    (t : OrthogonalMatrixHom k l) (g : Frame n k a) (x : Euclidean a) :
    rawMap m l a (targetFrame t (sourceFrame s g), x) =
      sourceMap s (targetMap t (rawMap n k a (g, x))) := by
  rw [rawMap_target_naturality, rawMap_source_naturality, targetMap_sourceMap]

/-- The literal proper one-point extension of the finite matrix/vector comparison. -/
def rawOnePointMap (n k a : ℕ) :
    OnePoint (Frame n k a × Euclidean a) → OnePoint (ComplementBundle n k) :=
  OnePoint.map (rawMap n k a)

/-- One-point continuity includes the whole infinity face, uniformly in the original frame. -/
theorem rawOnePointMap_continuous (n k a : ℕ) : Continuous (rawOnePointMap n k a) :=
  OnePoint.continuous_map (rawMap_continuous n k a) (rawMap_tendsto_coclosedCompact n k a)

@[simp]
theorem rawOnePointMap_infty (n k a : ℕ) :
    rawOnePointMap n k a OnePoint.infty = OnePoint.infty := rfl

@[simp]
theorem rawOnePointMap_coe (n k a : ℕ) (p : Frame n k a × Euclidean a) :
    rawOnePointMap n k a (p : OnePoint (Frame n k a × Euclidean a)) =
      (rawMap n k a p : OnePoint (ComplementBundle n k)) := rfl

/-- The one-point comparison is onto in exactly the original residual grade. -/
theorem rawOnePointMap_surjective (n k a : ℕ) (ha : a + n = k) :
    Function.Surjective (rawOnePointMap n k a) := by
  intro p
  induction p using OnePoint.rec with
  | infty => exact ⟨OnePoint.infty, rfl⟩
  | coe p =>
      obtain ⟨q, hq⟩ := rawMap_surjective n k a ha p
      exact ⟨(q : OnePoint (Frame n k a × Euclidean a)), congrArg ((↑) :
        ComplementBundle n k → OnePoint (ComplementBundle n k)) hq⟩

/-- No finite point is identified with infinity by the proper comparison. -/
theorem rawOnePointMap_eq_infty_iff (n k a : ℕ)
    (p : OnePoint (Frame n k a × Euclidean a)) :
    rawOnePointMap n k a p = OnePoint.infty ↔ p = OnePoint.infty := by
  induction p using OnePoint.rec <;> simp

/-- The finite kernel of the proper compactification is the original continuous balancing orbit. -/
theorem rawOnePointMap_coe_eq_iff (n k a : ℕ) (g h : Frame n k a)
    (x y : Euclidean a) :
    rawOnePointMap n k a ((g, x) : OnePoint (Frame n k a × Euclidean a)) =
        rawOnePointMap n k a ((h, y) : OnePoint (Frame n k a × Euclidean a)) ↔
      ∃ r : OrthogonalMatrixHom a a,
        h = changeCoefficient g r ∧ x = matrixLinear r.1 y := by
  rw [rawOnePointMap_coe, rawOnePointMap_coe, OnePoint.coe_eq_coe, rawMap_eq_iff]

/-- The actual compact frame/vector source gives the quotient topology on the Thom carrier. -/
theorem rawOnePointMap_quotient (n k a : ℕ) (ha : a + n = k) :
    IsQuotientMap (rawOnePointMap n k a) :=
  IsQuotientMap.of_surjective_continuous (rawOnePointMap_surjective n k a ha)
    (rawOnePointMap_continuous n k a)

/-- The exact one-point kernel setoid; its finite classes are proved original orthogonal orbits. -/
def rawOnePointSetoid (n k a : ℕ) : Setoid (OnePoint (Frame n k a × Euclidean a)) :=
  Setoid.ker (rawOnePointMap n k a)

/-- The forward raw orbit-quotient comparison is induced by the actual proper map. -/
def rawQuotientToThom (n k a : ℕ) :
    Quotient (rawOnePointSetoid n k a) → OnePoint (ComplementBundle n k) :=
  Quotient.lift (rawOnePointMap n k a) (fun _ _ h => h)

theorem rawQuotientToThom_continuous (n k a : ℕ) :
    Continuous (rawQuotientToThom n k a) :=
  Continuous.quotient_lift (rawOnePointMap_continuous n k a) (fun _ _ h => h)

/-- The original proper map has a bijective descended map in the exact residual grade. -/
theorem rawQuotientToThom_bijective (n k a : ℕ) (ha : a + n = k) :
    Function.Bijective (rawQuotientToThom n k a) := by
  constructor
  · intro p q h
    induction p using Quotient.inductionOn with
    | _ p =>
        induction q using Quotient.inductionOn with
        | _ q => exact Quotient.sound h
  · intro p
    obtain ⟨q, hq⟩ := rawOnePointMap_surjective n k a ha p
    exact ⟨Quotient.mk (rawOnePointSetoid n k a) q, hq⟩

/-- The complete raw matrix-orbit Thom homeomorphism, for the actual quotient topology. -/
def rawQuotientThomHomeomorph (n k a : ℕ) (ha : a + n = k) :
    Quotient (rawOnePointSetoid n k a) ≃ₜ OnePoint (ComplementBundle n k) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (rawQuotientToThom n k a) (rawQuotientToThom_bijective n k a ha))
    (rawQuotientToThom_continuous n k a)

/-- The raw forward keeps every actual frame/vector generator. -/
theorem rawQuotientThomHomeomorph_generator (n k a : ℕ) (ha : a + n = k)
    (g : Frame n k a) (x : Euclidean a) :
    rawQuotientThomHomeomorph n k a ha
        (Quotient.mk (rawOnePointSetoid n k a)
          ((g, x) : OnePoint (Frame n k a × Euclidean a))) =
      (rawMap n k a (g, x) : OnePoint (ComplementBundle n k)) := rfl

/-- The raw inverse class is independent of every orthogonal completion choice. -/
theorem rawThom_inverse_of_completion (n k a : ℕ) (ha : a + n = k)
    (p : ComplementBundle n k) (g : Frame n k a) (hg : finalPart g = p.1.1) :
    (rawQuotientThomHomeomorph n k a ha).symm (p : OnePoint (ComplementBundle n k)) =
      Quotient.mk (rawOnePointSetoid n k a)
        ((g, recover n k a (g, p)) : OnePoint (Frame n k a × Euclidean a)) := by
  apply (rawQuotientThomHomeomorph n k a ha).injective
  rw [(rawQuotientThomHomeomorph n k a ha).apply_symm_apply]
  exact (congrArg ((↑) : ComplementBundle n k → OnePoint (ComplementBundle n k))
    (rawMap_recover n k a g p hg)).symm

/-- Both raw inverse functions are proved on the entire compactified quotient. -/
theorem rawThom_inverse_laws (n k a : ℕ) (ha : a + n = k) :
    Function.LeftInverse (rawQuotientThomHomeomorph n k a ha).symm
        (rawQuotientThomHomeomorph n k a ha) ∧
      Function.RightInverse (rawQuotientThomHomeomorph n k a ha).symm
        (rawQuotientThomHomeomorph n k a ha) :=
  ⟨(rawQuotientThomHomeomorph n k a ha).symm_apply_apply,
    (rawQuotientThomHomeomorph n k a ha).apply_symm_apply⟩

/-- Both raw quotient directions are continuous, not merely mutually inverse point functions. -/
theorem rawThom_both_continuous (n k a : ℕ) (ha : a + n = k) :
    Continuous (rawQuotientThomHomeomorph n k a ha) ∧
      Continuous (rawQuotientThomHomeomorph n k a ha).symm :=
  ⟨(rawQuotientThomHomeomorph n k a ha).continuous,
    (rawQuotientThomHomeomorph n k a ha).symm.continuous⟩

/-- The lifted complement carrier uses the same original independent ambient universe. -/
abbrev LiftedBundle (n k : ℕ) := ULift.{v, 0} (ComplementBundle n k)

/-- The lifted frame uses the original native bare-hom carrier, without changing its topology. -/
abbrev LiftedFrame (n k a : ℕ) := ULift.{v, 0} (Frame n k a)

/-- The lifted coefficient is exactly the original orthogonal representation carrier. -/
abbrev LiftedEuclidean (a : ℕ) := ULift.{v, 0} (Euclidean a)

instance liftedBundle_pseudoMetrizable (n k : ℕ) :
    PseudoMetrizableSpace (LiftedBundle.{v} n k) :=
  Homeomorph.ulift.isInducing.pseudoMetrizableSpace

instance liftedOrthogonalMatrixHom_pseudoMetrizable (m k : ℕ) :
    PseudoMetrizableSpace (ULift.{v, 0} (OrthogonalMatrixHom m k)) :=
  Homeomorph.ulift.isInducing.pseudoMetrizableSpace

instance liftedBundle_locallyCompactSpace (n k : ℕ) :
    LocallyCompactSpace (LiftedBundle.{v} n k) :=
  (Homeomorph.ulift (X := ComplementBundle n k)).locallyCompactSpace_iff.mpr inferInstance

instance liftedEuclidean_locallyCompactSpace (a : ℕ) :
    LocallyCompactSpace (LiftedEuclidean.{v} a) :=
  (Homeomorph.ulift (X := Euclidean a)).locallyCompactSpace_iff.mpr inferInstance

instance liftedOrthogonalMatrixHom_locallyCompactSpace (m k : ℕ) :
    LocallyCompactSpace (ULift.{v, 0} (OrthogonalMatrixHom m k)) :=
  (Homeomorph.ulift (X := OrthogonalMatrixHom m k)).locallyCompactSpace_iff.mpr inferInstance

/-- The exact original lifted frame/coefficient function into the lifted
matrix complement bundle. -/
def liftedRawMap (n k a : ℕ) :
    LiftedFrame.{v} n k a × LiftedEuclidean.{v} a → LiftedBundle.{v} n k :=
  fun p => ULift.up (rawMap n k a (p.1.down, p.2.down))

/-- The lifted finite comparison is jointly continuous through the original
`ULift` homeomorphisms. -/
theorem liftedRawMap_continuous (n k a : ℕ) : Continuous (liftedRawMap.{v} n k a) :=
  continuous_uliftUp.comp ((rawMap_continuous n k a).comp
    ((continuous_uliftDown.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd)))

/-- Properness is transported through the actual source and target lift homeomorphisms. -/
theorem liftedRawMap_proper (n k a : ℕ) : IsProperMap (liftedRawMap.{v} n k a) :=
  (Homeomorph.ulift (X := ComplementBundle n k)).symm.isProperMap.comp
    ((rawMap_proper n k a).comp
      ((Homeomorph.ulift (X := Frame n k a)).prodCongr
        (Homeomorph.ulift (X := Euclidean a))).isProperMap)

theorem liftedRawMap_tendsto_coclosedCompact (n k a : ℕ) :
    Tendsto (liftedRawMap.{v} n k a)
      (coclosedCompact (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a))
      (coclosedCompact (LiftedBundle.{v} n k)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp (liftedRawMap_proper.{v} n k a)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The continuous map of the full lifted frame/coefficient comparison. -/
def liftedContinuousMap (n k a : ℕ) :
    C(LiftedFrame.{v} n k a × LiftedEuclidean.{v} a, LiftedBundle.{v} n k) :=
  ⟨liftedRawMap n k a, liftedRawMap_continuous n k a⟩

/-- The actual pointed Thom carrier is the original one-point CGWH construction
on this total space. -/
def thom (n k : ℕ) : PointedCGWH.{u, v} :=
  PointedCGWH.onePointOf (LiftedBundle.{v} n k)

/-- The original proper-map extension of the entire lifted frame/coefficient comparison. -/
def liftedOnePointComparison (n k a : ℕ) :
    PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a) ⟶
      thom.{u, v} n k :=
  PointedCGWH.onePointMapOfProper (liftedContinuousMap n k a)
    (liftedRawMap_tendsto_coclosedCompact n k a)

/-- The proper pointed comparison fixes infinity with the original basepoint dictionary. -/
theorem liftedOnePointComparison_infty (n k a : ℕ) :
    (liftedOnePointComparison.{u, v} n k a).right OnePoint.infty = OnePoint.infty :=
  PointedCGWH.onePointMapOfProper_infty.{u, v} (liftedContinuousMap n k a)
    (liftedRawMap_tendsto_coclosedCompact n k a)

/-- The proper pointed comparison retains the actual lifted finite matrix/vector formula. -/
theorem liftedOnePointComparison_coe (n k a : ℕ)
    (g : LiftedFrame.{v} n k a) (x : LiftedEuclidean.{v} a) :
    (liftedOnePointComparison.{u, v} n k a).right
        ((g, x) : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) =
      ((ULift.up (rawMap n k a (g.down, x.down)) : LiftedBundle.{v} n k) :
        OnePoint (LiftedBundle.{v} n k)) :=
  PointedCGWH.onePointMapOfProper_coe.{u, v} (liftedContinuousMap n k a)
    (liftedRawMap_tendsto_coclosedCompact n k a) (g, x)

/-- The actual finite disk-bundle sublevel has compact inherited topology. -/
theorem bundleNormSublevel_isCompact (n k : ℕ) (R : ℝ) :
    IsCompact {p : ComplementBundle n k | ‖bundleVector p‖ ≤ R} := by
  have hbase : IsCompact {A : Matrix (Fin k) (Fin n) ℝ | A.transpose * A = 1} :=
    isCompact_iff_compactSpace.mpr (embeddingMatrix_compact n k)
  have hball : IsCompact {x : Euclidean k | ‖x‖ ≤ R} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : Euclidean k) R
  let K : Set (Matrix (Fin k) (Fin n) ℝ × Euclidean k) :=
    {A | A.transpose * A = 1} ×ˢ {x | ‖x‖ ≤ R}
  have hcompact : IsCompact (((↑) : ComplementBundle n k →
      Matrix (Fin k) (Fin n) ℝ × Euclidean k) ⁻¹' K) :=
    (complementBundle_isClosed n k).isProperMap_subtypeVal.isCompact_preimage
      (hbase.prod hball)
  have hpre : ((↑) : ComplementBundle n k →
      Matrix (Fin k) (Fin n) ℝ × Euclidean k) ⁻¹' K =
      {p : ComplementBundle n k | ‖bundleVector p‖ ≤ R} := by
    ext p
    simp only [K, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq,
      p.2.1, true_and, bundleVector]
  rwa [hpre] at hcompact

/-- The actual sphere-bundle level has compact inherited topology. -/
theorem bundleNormLevel_isCompact (n k : ℕ) (R : ℝ) :
    IsCompact {p : ComplementBundle n k | ‖bundleVector p‖ = R} := by
  apply (bundleNormSublevel_isCompact n k R).of_isClosed_subset
  · exact isClosed_eq (continuous_bundleVector.norm) continuous_const
  · intro p hp
    exact le_of_eq hp

/-- The geometric disk bundle is the genuine unit-norm sublevel, before any cell structure. -/
abbrev DiskBundle (n k : ℕ) :=
  {p : ComplementBundle n k // ‖bundleVector p‖ ≤ 1}

/-- The geometric sphere bundle is the genuine unit-norm level, before any cell structure. -/
abbrev SphereBundle (n k : ℕ) :=
  {p : ComplementBundle n k // ‖bundleVector p‖ = 1}

instance diskBundle_compactSpace (n k : ℕ) : CompactSpace (DiskBundle n k) :=
  isCompact_iff_compactSpace.mp (bundleNormSublevel_isCompact n k 1)

instance sphereBundle_compactSpace (n k : ℕ) : CompactSpace (SphereBundle n k) :=
  isCompact_iff_compactSpace.mp (bundleNormLevel_isCompact n k 1)

/-- The genuine sphere-bundle inclusion into the disk bundle. -/
def sphereToDisk (n k : ℕ) : SphereBundle n k → DiskBundle n k :=
  fun p => ⟨p.1, le_of_eq p.2⟩

theorem sphereToDisk_continuous (n k : ℕ) : Continuous (sphereToDisk n k) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The actual sphere inclusion is a closed embedding. Its q-cofibration
property remains a separate geometric cell obligation. -/
theorem sphereToDisk_closedEmbedding (n k : ℕ) : IsClosedEmbedding (sphereToDisk n k) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (sphereToDisk_continuous n k) _ (sphereToDisk_continuous n k).isClosedMap
  intro p q h
  apply Subtype.ext
  exact congrArg (fun p : DiskBundle n k => p.1) h

/-- The zero section is the actual zero complement vector over the one-sided base. -/
def zeroSection (n k : ℕ) : EmbeddingMatrix n k → ComplementBundle n k :=
  fun A => ⟨(A.1, 0), A.2, by simp⟩

theorem zeroSection_continuous (n k : ℕ) : Continuous (zeroSection n k) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk continuous_const

@[simp]
theorem zeroSection_base (n k : ℕ) (A : EmbeddingMatrix n k) :
    bundleBase (zeroSection n k A) = A := rfl

theorem zeroSection_vector (n k : ℕ) (A : EmbeddingMatrix n k) :
    bundleVector (zeroSection n k A) = 0 := rfl

/-- Zero-section target naturality holds for the full original isometry parameter. -/
theorem zeroSection_targetMap {n k l : ℕ} (t : OrthogonalMatrixHom k l)
    (A : EmbeddingMatrix n k) :
    targetMap t (zeroSection n k A) =
      zeroSection n l (bundleBase (targetMap t (zeroSection n k A))) := by
  apply complementBundle_ext
  · rfl
  · change matrixLinear t.1 0 = 0
    exact map_zero (matrixLinear t.1)

/-- Zero-section source naturality retains the original source-precomposition action. -/
theorem zeroSection_sourceMap {m n k : ℕ} (s : OrthogonalMatrixHom m n)
    (A : EmbeddingMatrix n k) :
    sourceMap s (zeroSection n k A) =
      zeroSection m k (bundleBase (sourceMap s (zeroSection n k A))) := by
  apply complementBundle_ext <;> rfl

/-- The whole finite inverse is continuous once the actual frame is retained. -/
theorem recover_target_naturality {n k l a : ℕ} (t : OrthogonalMatrixHom k l)
    (g : Frame n k a) (p : ComplementBundle n k) :
    recover n l a (targetFrame t g, targetMap t p) = recover n k a (g, p) := by
  change matrixLinear (coefficientPart (targetFrame t g)).transpose
      (matrixLinear t.1 p.1.2) = matrixLinear (coefficientPart g).transpose p.1.2
  rw [targetFrame_coefficientPart, Matrix.transpose_mul]
  apply WithLp.ofLp_injective
  simp only [matrixLinear_ofLp]
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, t.2.1, Matrix.mul_one]

/-- Source precomposition leaves the exact recovered coefficient unchanged. -/
theorem recover_source_naturality {m n k a : ℕ} (s : OrthogonalMatrixHom m n)
    (g : Frame n k a) (p : ComplementBundle n k) :
    recover m k a (sourceFrame s g, sourceMap s p) = recover n k a (g, p) := by
  change matrixLinear (coefficientPart (sourceFrame s g)).transpose p.1.2 =
    matrixLinear (coefficientPart g).transpose p.1.2
  rw [sourceFrame_coefficientPart]

/-- Recovery transforms by the inverse of original coefficient precomposition. -/
theorem recover_changeCoefficient {n k a : ℕ} (g : Frame n k a)
    (r : OrthogonalMatrixHom a a) (p : ComplementBundle n k) :
    recover n k a (changeCoefficient g r, p) =
      matrixLinear r.1.transpose (recover n k a (g, p)) := by
  change matrixLinear (coefficientPart (changeCoefficient g r)).transpose p.1.2 =
    matrixLinear r.1.transpose (matrixLinear (coefficientPart g).transpose p.1.2)
  rw [changeCoefficient_coefficientPart, Matrix.transpose_mul, matrixLinear_mul]

/-- First-block precomposition across arbitrary original coefficient degrees. -/
def changeCoefficientAcross {n k a b : ℕ} (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) : Frame n k a :=
  OrthogonalMatrixHom.comp (OrthogonalMatrixHom.blockSum r (OrthogonalMatrixHom.id n)) g

/-- The entire original coefficient morphism fixes the final source block. -/
theorem changeCoefficientAcross_finalPart {n k a b : ℕ} (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) :
    finalPart (changeCoefficientAcross g r) = finalPart g := by
  ext i j
  simpa [changeCoefficientAcross, finalPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add] using congrFun (congrFun (Matrix.mul_one (finalPart g)) i) j

/-- The entire original coefficient morphism multiplies the coefficient block on the right. -/
theorem changeCoefficientAcross_coefficientPart {n k a b : ℕ} (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) :
    coefficientPart (changeCoefficientAcross g r) = coefficientPart g * r.1 := by
  ext i j
  simp [changeCoefficientAcross, coefficientPart, OrthogonalMatrixHom.comp,
    OrthogonalMatrixHom.blockSum, OrthogonalMatrixHom.id, Matrix.mul_apply,
    Fin.sum_univ_add]

/-- All original coefficient-degree balancing equations hold, before
any residual-grade reduction. -/
theorem rawMap_allGrade_balanced (n k a b : ℕ) (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) (x : Euclidean a) :
    rawMap n k a (changeCoefficientAcross g r, x) =
      rawMap n k b (g, matrixLinear r.1 x) := by
  apply complementBundle_ext
  · exact changeCoefficientAcross_finalPart g r
  · change matrixLinear (coefficientPart (changeCoefficientAcross g r)) x =
      matrixLinear (coefficientPart g) (matrixLinear r.1 x)
    rw [changeCoefficientAcross_coefficientPart, matrixLinear_mul]

/-- Joint continuity of all original coefficient-degree precomposition parameters. -/
theorem changeCoefficientAcross_continuous (n k a b : ℕ) :
    Continuous (fun p : Frame n k b × OrthogonalMatrixHom a b =>
      changeCoefficientAcross p.1 p.2) :=
  OrthogonalMatrixHom.continuous_comp.comp
    ((OrthogonalMatrixHom.continuous_blockSum.comp
      (continuous_snd.prodMk continuous_const)).prodMk continuous_fst)

/-- Uniform comparison on the whole sphere infinity face, with its compact frame parameter. -/
def liftedJointComparison (n k a : ℕ) :
    LiftedFrame.{v} n k a × OnePoint (LiftedEuclidean.{v} a) →
      OnePoint (LiftedBundle.{v} n k) := fun p =>
  OnePoint.rec OnePoint.infty (fun x =>
    (liftedRawMap n k a (p.1, x) : OnePoint (LiftedBundle.{v} n k))) p.2

/-- Joint continuity at infinity comes from the actual proper compactification
and product collapse. -/
theorem liftedJointComparison_continuous (n k a : ℕ) :
    Continuous (liftedJointComparison.{v} n k a) := by
  let K := LiftedFrame.{v} n k a
  let E := LiftedEuclidean.{v} a
  let T := LiftedBundle.{v} n k
  let embed : K × OnePoint E → OnePoint K × OnePoint E := fun p => ((p.1 : OnePoint K), p.2)
  have he : Continuous embed :=
    (OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (PointedCGWH.rawCollapse K E ∘ embed) :=
    (PointedCGWH.rawCollapse_continuous K E).comp he
  have hm : Continuous (OnePoint.map (liftedRawMap.{v} n k a)) :=
    OnePoint.continuous_map (liftedRawMap_continuous n k a)
      (liftedRawMap_tendsto_coclosedCompact n k a)
  convert hm.comp hc using 1
  funext p
  rcases p with ⟨g, p⟩
  induction p using OnePoint.rec <;> rfl

@[simp]
theorem liftedJointComparison_infty (n k a : ℕ) (g : LiftedFrame.{v} n k a) :
    liftedJointComparison.{v} n k a (g, OnePoint.infty) = OnePoint.infty := rfl

@[simp]
theorem liftedJointComparison_coe (n k a : ℕ) (g : LiftedFrame.{v} n k a)
    (x : LiftedEuclidean.{v} a) :
    liftedJointComparison.{v} n k a (g, (x : OnePoint (LiftedEuclidean.{v} a))) =
      (liftedRawMap n k a (g, x) : OnePoint (LiftedBundle.{v} n k)) := rfl

/-- The finite comparison remains onto after the exact original universe lift. -/
theorem liftedRawMap_surjective (n k a : ℕ) (ha : a + n = k) :
    Function.Surjective (liftedRawMap.{v} n k a) := by
  rintro ⟨p⟩
  obtain ⟨⟨g, x⟩, h⟩ := rawMap_surjective n k a ha p
  exact ⟨(ULift.up g, ULift.up x), congrArg ULift.up h⟩

/-- The actual lifted one-point map used by the native pointed comparison. -/
def liftedRawOnePointMap (n k a : ℕ) :
    OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a) →
      OnePoint (LiftedBundle.{v} n k) := OnePoint.map (liftedRawMap n k a)

theorem liftedRawOnePointMap_continuous (n k a : ℕ) :
    Continuous (liftedRawOnePointMap.{v} n k a) :=
  OnePoint.continuous_map (liftedRawMap_continuous n k a)
    (liftedRawMap_tendsto_coclosedCompact n k a)

theorem liftedRawOnePointMap_surjective (n k a : ℕ) (ha : a + n = k) :
    Function.Surjective (liftedRawOnePointMap.{v} n k a) := by
  intro p
  induction p using OnePoint.rec with
  | infty => exact ⟨OnePoint.infty, rfl⟩
  | coe p =>
      obtain ⟨q, hq⟩ := liftedRawMap_surjective.{v} n k a ha p
      exact ⟨(q : OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)),
        congrArg ((↑) : LiftedBundle.{v} n k → OnePoint (LiftedBundle.{v} n k)) hq⟩

/-- The lifted map supplies the actual compact quotient topology on the native Thom carrier. -/
theorem liftedRawOnePointMap_quotient (n k a : ℕ) (ha : a + n = k) :
    IsQuotientMap (liftedRawOnePointMap.{v} n k a) :=
  IsQuotientMap.of_surjective_continuous (liftedRawOnePointMap_surjective n k a ha)
    (liftedRawOnePointMap_continuous n k a)

/-- Compact generation of the genuine compact lifted-frame compactification. -/
theorem liftedFrameOnePoint_generated (n k a : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedFrame.{v} n k a)) := by
  let K := LiftedFrame.{v} n k a
  let e := PointedCGWH.compactFreePointRawHomeo K
  let _ : UCompactlyGeneratedSpace.{u} K := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ K) := inferInstance
  exact uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- Compact generation of the original lifted Euclidean one-point representation sphere. -/
theorem liftedEuclideanOnePoint_generated (a : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedEuclidean.{v} a)) := by
  let eLift : OnePoint (LiftedEuclidean.{v} a) ≃ₜ OnePoint (Euclidean a) :=
    Homeomorph.onePointCongr (Homeomorph.ulift (X := Euclidean a))
  let eSphere := onePointEquivSphereOfFinrankEq
    (V := Euclidean a) (ι := Fin (Module.finrank ℝ (Euclidean a) + 1)) (by simp)
  let e := eLift.trans eSphere
  let _ : SequentialSpace (OnePoint (LiftedEuclidean.{v} a)) :=
    e.symm.isQuotientMap.sequentialSpace
  infer_instance

/-- The original product compactification is compactly generated for both independent universes. -/
theorem liftedFrameProductOnePoint_generated (n k a : ℕ) :
    UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :=
  PointedCGWH.onePointProduct_generated _ _
    (liftedFrameOnePoint_generated n k a) (liftedEuclideanOnePoint_generated a)

/-- The genuine Thom compactification is compactly generated from the proved proper quotient. -/
theorem liftedBundleOnePoint_generated (n k : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k)) := by
  by_cases h : n ≤ k
  · let a := k - n
    have ha : a + n = k := Nat.sub_add_cancel h
    let _ : UCompactlyGeneratedSpace.{u}
        (OnePoint (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a)) :=
      liftedFrameProductOnePoint_generated n k a
    exact uCompactlyGeneratedSpace_of_coinduced
      (liftedRawOnePointMap_continuous n k a)
      (liftedRawOnePointMap_quotient n k a ha).eq_coinduced
  · let _ : IsEmpty (ComplementBundle n k) := complementBundle_empty (Nat.lt_of_not_ge h)
    let _ : IsEmpty (LiftedBundle.{v} n k) := inferInstance
    let _ : Subsingleton (OnePoint (LiftedBundle.{v} n k)) := inferInstance
    infer_instance

/-- The actual freely based matrix Hom identifies with its compact one-point model. -/
def frameHomOnePointIso (n k a : ℕ) :
    OrthogonalIndex.hom.{u, v} (a + n) k ≅
      PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a) := by
  let K : CGWH.{u, v} := CGWH.of (LiftedFrame.{v} n k a)
  change (Under.costar CGWH.point).obj K ≅ PointedCGWH.onePointOf.{u, v} (K : Type v)
  exact PointedCGWH.addBasepointIsoOnePointOfCompact K

/-- The native frame-Hom comparison preserves its actual categorical basepoint. -/
theorem frameHomOnePointIso_basepoint (n k a : ℕ) (t : CGWH.point.{u, v}) :
    (frameHomOnePointIso.{u, v} n k a).hom.right
        ((OrthogonalIndex.hom.{u, v} (a + n) k).hom t) = OnePoint.infty :=
  by
    have h : (OrthogonalIndex.hom.{u, v} (a + n) k).hom ≫
        (frameHomOnePointIso.{u, v} n k a).hom.right =
        (PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a)).hom :=
      Under.w (f := OrthogonalIndex.hom.{u, v} (a + n) k)
        (g := PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a))
        (frameHomOnePointIso.{u, v} n k a).hom
    have ht := ConcreteCategory.congr_hom (C := CGWH.{u, v}) (X := CGWH.point.{u, v})
      (Y := (PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a)).right) h t
    rw [ConcreteCategory.comp_apply] at ht
    exact ht

/-- The native Hom comparison retains the actual original matrix generalized point. -/
theorem frameHomOnePointIso_matrixPoint (n k a : ℕ) (g : Frame n k a) :
    let t : (𝟙_ PointedCGWH.{u, v}).right :=
      (coprod.inr : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
    (frameHomOnePointIso.{u, v} n k a).hom.right
        ((OrthogonalIndex.matrixPoint.{u, v} g).right t) =
      ((ULift.up g : LiftedFrame.{v} n k a) : OnePoint (LiftedFrame.{v} n k a)) := by
  let X : CGWH.{u, v} := CGWH.of (LiftedFrame.{v} n k a)
  let f : CGWH.point.{u, v} ⟶ X := (CGWH.pointHomEquiv X).symm (ULift.up g)
  let t : CGWH.point.{u, v} := PUnit.unit
  have h := ConcreteCategory.congr_hom (coprod.inr_map (𝟙 CGWH.point.{u, v}) f) t
  simp only [ConcreteCategory.comp_apply] at h
  have hf : f t = (ULift.up g : X) := CGWH.pointHomEquiv_symm_apply_apply X (ULift.up g) t
  rw [hf] at h
  change (PointedCGWH.addBasepointIsoOnePointOfCompact X).hom.right
      ((coprod.map (𝟙 CGWH.point.{u, v}) f)
        ((coprod.inr : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) t)) = _
  rw [h]
  exact PointedCGWH.compactFreePointIso_coe X (ULift.up g)

/-- The actual complete native frame-Hom/sphere tensor becomes its proper
product compactification. -/
def frameSphereProductIso (n k a : ℕ) :
    OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a ≅
      PointedCGWH.onePointOf.{u, v} (LiftedFrame.{v} n k a × LiftedEuclidean.{v} a) :=
  tensorIso (frameHomOnePointIso n k a) (Iso.refl _) ≪≫
    (PointedCGWH.onePointProdSmashIso _ _
      (liftedFrameOnePoint_generated n k a) (liftedEuclideanOnePoint_generated a)).symm

/-- The actual pointed Thom leg from every complete original coend integrand. -/
def generatorThomLeg (n k a : ℕ) :
    OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a ⟶
      thom.{u, v} n k :=
  (frameSphereProductIso n k a).hom ≫ liftedOnePointComparison n k a

/-- The full original integrand leg preserves its categorical basepoint. -/
theorem generatorThomLeg_basepoint (n k a : ℕ) (t : CGWH.point.{u, v}) :
    (generatorThomLeg.{u, v} n k a).right
        ((OrthogonalIndex.hom.{u, v} (a + n) k ⊗
          PointedCGWH.orthogonalSphere.{u, v} a).hom t) = OnePoint.infty :=
  by
    have h : (OrthogonalIndex.hom.{u, v} (a + n) k ⊗
        PointedCGWH.orthogonalSphere.{u, v} a).hom ≫
        (generatorThomLeg.{u, v} n k a).right = (thom.{u, v} n k).hom :=
      Under.w (f := OrthogonalIndex.hom.{u, v} (a + n) k ⊗
        PointedCGWH.orthogonalSphere.{u, v} a) (g := thom.{u, v} n k)
        (generatorThomLeg.{u, v} n k a)
    have ht := ConcreteCategory.congr_hom (C := CGWH.{u, v}) (X := CGWH.point.{u, v})
      (Y := (thom.{u, v} n k).right) h t
    rw [ConcreteCategory.comp_apply] at ht
    exact ht

/-- Finite orthogonal completion choices give exactly the same compactified raw class. -/
theorem rawInverse_choice_independent (n k a : ℕ) (p : ComplementBundle n k)
    (g h : Frame n k a) (hg : finalPart g = p.1.1) (hh : finalPart h = p.1.1) :
    Quotient.mk (rawOnePointSetoid n k a)
        ((g, recover n k a (g, p)) : OnePoint (Frame n k a × Euclidean a)) =
      Quotient.mk (rawOnePointSetoid n k a)
        ((h, recover n k a (h, p)) : OnePoint (Frame n k a × Euclidean a)) := by
  apply Quotient.sound
  change (rawMap n k a (g, recover n k a (g, p)) : OnePoint (ComplementBundle n k)) =
    (rawMap n k a (h, recover n k a (h, p)) : OnePoint (ComplementBundle n k))
  rw [rawMap_recover n k a g p hg, rawMap_recover n k a h p hh]

/-- Each pointed Thom leg is a continuous native CGWH arrow on the full integrand. -/
theorem generatorThomLeg_continuous (n k a : ℕ) :
    Continuous (ConcreteCategory.hom (generatorThomLeg.{u, v} n k a).right) :=
  (ConcreteCategory.hom (generatorThomLeg.{u, v} n k a).right).continuous

/-- The original finite matrix/sphere generator in the actual native smash presentation. -/
def finiteGeneratorInput (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a).right :=
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
  (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
    ((CGWH.tensorEquivProd H.right S.right).symm
      ((OrthogonalIndex.matrixPoint.{u, v} g).right t,
        ((ULift.up x : LiftedEuclidean.{v} a) : OnePoint (LiftedEuclidean.{v} a))))

/-- The full original finite generator has the exact coefficient-first matrix-complement formula. -/
theorem generatorThomLeg_coe (n k a : ℕ) (g : Frame n k a) (x : Euclidean a) :
    (generatorThomLeg.{u, v} n k a).right (finiteGeneratorInput.{u, v} n k a g x) =
      ((ULift.up (rawMap n k a (g, x)) : LiftedBundle.{v} n k) :
        OnePoint (LiftedBundle.{v} n k)) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let K := LiftedFrame.{v} n k a
  let E := LiftedEuclidean.{v} a
  let I := frameHomOnePointIso.{u, v} n k a
  let hK := liftedFrameOnePoint_generated.{u, v} n k a
  let hE := liftedEuclideanOnePoint_generated.{u, v} a
  let μ := PointedCGWH.onePointProdSmashIso.{u, v} K E hK hE
  let t : (𝟙_ PointedCGWH.{u, v}).right :=
    (coprod.inr : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit
  let pg : H.right := (OrthogonalIndex.matrixPoint.{u, v} g).right t
  let x' : E := ULift.up x
  let g' : K := ULift.up g
  let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
  let q' : (PointedCGWH.onePointOf.{u, v} K).right ⊗ S.right ⟶
      (PointedCGWH.onePointOf.{u, v} K ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal
      (PointedCGWH.onePointOf.{u, v} K) S).2.1.inl
  let c := (CGWH.tensorEquivProd H.right S.right).symm (pg, (x' : OnePoint E))
  let c' := (CGWH.tensorEquivProd (PointedCGWH.onePointOf.{u, v} K).right S.right).symm
    ((g' : OnePoint K), (x' : OnePoint E))
  have hnat := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom (𝟙 S)) c
  change (I.hom ⊗ₘ 𝟙 S).right (q c) = q' ((I.hom.right ⊗ₘ 𝟙 S.right) c) at hnat
  have hg : I.hom.right pg = (g' : OnePoint K) :=
    frameHomOnePointIso_matrixPoint n k a g
  have hc : (I.hom.right ⊗ₘ 𝟙 S.right) c = c' := by
    have h := CGWH.tensorEquivProd_symm_map I.hom.right (𝟙 S.right) pg (x' : OnePoint E)
    rw [hg] at h
    exact h
  have hμ : μ.hom.right ((g', x') : OnePoint (K × E)) = q' c' :=
    PointedCGWH.onePointProdSmashIso_coe K E hK hE g' x'
  have hcancel := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id) ((g', x') : OnePoint (K × E))
  simp only [Under.comp_right, Under.id_right] at hcancel
  have hμInv : μ.inv.right (q' c') = ((g', x') : OnePoint (K × E)) := by
    rw [← hμ]
    exact hcancel
  change (liftedOnePointComparison.{u, v} n k a).right
    (μ.inv.right ((I.hom ⊗ₘ 𝟙 S).right (q c))) = _
  rw [hnat, hc, hμInv]
  exact liftedOnePointComparison_coe.{u, v} n k a g' x'

/-- The whole sphere infinity face is absorbing for the actual native pointed Thom leg. -/
theorem generatorThomLeg_infty (n k a : ℕ)
    (h : (OrthogonalIndex.hom.{u, v} (a + n) k).right) :
    let H := OrthogonalIndex.hom.{u, v} (a + n) k
    let S := PointedCGWH.orthogonalSphere.{u, v} a
    (generatorThomLeg.{u, v} n k a).right
      ((CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
        ((CGWH.tensorEquivProd H.right S.right).symm (h, OnePoint.infty))) = OnePoint.infty := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let S := PointedCGWH.orthogonalSphere.{u, v} a
  let K := LiftedFrame.{v} n k a
  let E := LiftedEuclidean.{v} a
  let I := frameHomOnePointIso.{u, v} n k a
  let hK := liftedFrameOnePoint_generated.{u, v} n k a
  let hE := liftedEuclideanOnePoint_generated.{u, v} a
  let μ := PointedCGWH.onePointProdSmashIso.{u, v} K E hK hE
  let q : H.right ⊗ S.right ⟶ (H ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal H S).2.1.inl
  let q' : (PointedCGWH.onePointOf.{u, v} K).right ⊗ S.right ⟶
      (PointedCGWH.onePointOf.{u, v} K ⊗ S).right :=
    (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal
      (PointedCGWH.onePointOf.{u, v} K) S).2.1.inl
  let c := (CGWH.tensorEquivProd H.right S.right).symm (h, OnePoint.infty)
  let c' := (CGWH.tensorEquivProd (PointedCGWH.onePointOf.{u, v} K).right S.right).symm
    (I.hom.right h, OnePoint.infty)
  have hnat := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality
      CGWH.point CGWH.point_isTerminal I.hom (𝟙 S)) c
  change (I.hom ⊗ₘ 𝟙 S).right (q c) = q' ((I.hom.right ⊗ₘ 𝟙 S.right) c) at hnat
  have hc : (I.hom.right ⊗ₘ 𝟙 S.right) c = c' :=
    CGWH.tensorEquivProd_symm_map I.hom.right (𝟙 S.right) h OnePoint.infty
  have hμ : μ.hom.right OnePoint.infty = q' c' :=
    PointedCGWH.onePointProdSmashIso_infty_right K E hK hE (I.hom.right h)
  have hcancel := ConcreteCategory.congr_hom
    (congrArg Under.Hom.right μ.hom_inv_id) OnePoint.infty
  simp only [Under.comp_right, Under.id_right] at hcancel
  have hμInv : μ.inv.right (q' c') =
      (show (PointedCGWH.onePointOf.{u, v} (K × E)).right from OnePoint.infty) := by
    rw [← hμ]
    exact hcancel
  change (liftedOnePointComparison.{u, v} n k a).right
    (μ.inv.right ((I.hom ⊗ₘ 𝟙 S).right (q c))) = _
  rw [hnat, hc, hμInv]
  exact liftedOnePointComparison_infty.{u, v} n k a

end CategoryTheory.Spectra.OrthogonalComplementBundle

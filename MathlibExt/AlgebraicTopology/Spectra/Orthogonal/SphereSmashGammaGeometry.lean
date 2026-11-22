/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ComplementBundle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UnitInterval

/-!
# The actual frame rotation for orthogonal sphere smash

The rotation uses the original inherited matrix topology and preserves
both orthogonal equations. The coefficient block comes first, as in the
existing complement bundle. Its inverse quarter rotation fixes the
appropriate final-frame coset and gives the original transposition
endpoint after the coefficient-block sign change.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory Matrix Filter TopologicalSpace Topology
open scoped InnerProductSpace

namespace CategoryTheory.Spectra.OrthogonalSmashGammaGeometry

open OrthogonalComplementBundle

/-- The complete real two-block rotation, with coefficient columns first. -/
def rotationBlocks (n : ℕ) (c s : ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (c • (1 : Matrix (Fin n) (Fin n) ℝ))
    (s • (1 : Matrix (Fin n) (Fin n) ℝ))
    ((-s) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (c • (1 : Matrix (Fin n) (Fin n) ℝ))

private theorem scalarIdentity_mul (n : ℕ) (a b : ℝ) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ)) * (b • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (a * b) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm a b]

/-- The original source Gram equation holds for every exact unit-circle parameter. -/
theorem rotationBlocks_transpose_mul (n : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotationBlocks n c s).transpose * rotationBlocks n c s = 1 := by
  have h₀ : c * c + (-s) * (-s) = 1 := by nlinarith [h]
  have h₁ : s * s + c * c = 1 := by nlinarith [h]
  have h₂ : c * s + (-s) * c = 0 := by ring
  have h₃ : s * c + c * (-s) = 0 := by ring
  simp only [rotationBlocks, Matrix.fromBlocks_transpose, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.fromBlocks_multiply, scalarIdentity_mul, ← add_smul]
  simp only [h₀, h₁, h₂, h₃, one_smul, zero_smul, Matrix.fromBlocks_one]

/-- The original target Gram equation is retained as well. -/
theorem rotationBlocks_mul_transpose (n : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rotationBlocks n c s * (rotationBlocks n c s).transpose = 1 := by
  have h₀ : c * c + s * s = 1 := by nlinarith [h]
  have h₁ : (-s) * (-s) + c * c = 1 := by nlinarith [h]
  have h₂ : c * (-s) + s * c = 0 := by ring
  have h₃ : (-s) * c + c * s = 0 := by ring
  simp only [rotationBlocks, Matrix.fromBlocks_transpose, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.fromBlocks_multiply, scalarIdentity_mul, ← add_smul]
  simp only [h₀, h₁, h₂, h₃, one_smul, zero_smul, Matrix.fromBlocks_one]

/-- Reindex the original two real coordinate blocks in the native finite-dimensional skeleton. -/
def rotationMatrix (n : ℕ) (c s : ℝ) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (rotationBlocks n c s)

/-- The native reindexed source Gram equation is the whole original block equation. -/
theorem rotationMatrix_transpose_mul (n : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotationMatrix n c s).transpose * rotationMatrix n c s = 1 := by
  let e : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv
  dsimp only [rotationMatrix]
  rw [Matrix.transpose_reindex]
  change (Matrix.reindexLinearEquiv ℝ ℝ e e) (rotationBlocks n c s).transpose *
    (Matrix.reindexLinearEquiv ℝ ℝ e e) (rotationBlocks n c s) = 1
  rw [Matrix.reindexLinearEquiv_mul, rotationBlocks_transpose_mul n c s h,
    Matrix.reindexLinearEquiv_one]

/-- The native reindexed target equation retains the original two-sided isometry value. -/
theorem rotationMatrix_mul_transpose (n : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rotationMatrix n c s * (rotationMatrix n c s).transpose = 1 := by
  let e : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv
  dsimp only [rotationMatrix]
  rw [Matrix.transpose_reindex]
  change (Matrix.reindexLinearEquiv ℝ ℝ e e) (rotationBlocks n c s) *
    (Matrix.reindexLinearEquiv ℝ ℝ e e) (rotationBlocks n c s).transpose = 1
  rw [Matrix.reindexLinearEquiv_mul, rotationBlocks_mul_transpose n c s h,
    Matrix.reindexLinearEquiv_one]

/-- The complete actual orthogonal matrix value, with both original inverse equations. -/
def rotation (n : ℕ) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    OrthogonalMatrixHom (n + n) (n + n) :=
  ⟨rotationMatrix n c s, rotationMatrix_transpose_mul n c s h,
    rotationMatrix_mul_transpose n c s h⟩

/-- The actual angle of the inverse quarter rotation. -/
def angle (t : ℝ) : ℝ := (Real.pi / 2) * t

/-- The actual complete orthogonal path, including both coefficient and retained frame blocks. -/
def quarterRotation (n : ℕ) (t : ℝ) : OrthogonalMatrixHom (n + n) (n + n) :=
  rotation n (Real.cos (angle t)) (Real.sin (angle t)) (by
    nlinarith [Real.sin_sq_add_cos_sq (angle t)])

/-- Joint continuity uses the inherited finite matrix topology, not a chosen coset topology. -/
theorem quarterRotation_continuous (n : ℕ) : Continuous (quarterRotation n) := by
  apply Continuous.subtype_mk
  have ha : Continuous angle := continuous_const.mul continuous_id
  have hc := Real.continuous_cos.comp ha
  have hs := Real.continuous_sin.comp ha
  exact (Continuous.matrix_fromBlocks (hc.smul continuous_const) (hs.smul continuous_const)
    (hs.neg.smul continuous_const) (hc.smul continuous_const)).matrix_reindex
      finSumFinEquiv finSumFinEquiv

/-- The entire actual start matrix is the original native identity. -/
theorem quarterRotation_zero (n : ℕ) : quarterRotation n 0 = OrthogonalMatrixHom.id (n + n) := by
  apply OrthogonalMatrixHom.ext
  simp only [quarterRotation, rotation, rotationMatrix, rotationBlocks, angle, mul_zero,
    Real.cos_zero, Real.sin_zero, one_smul, zero_smul, neg_zero, Matrix.fromBlocks_one]
  exact Matrix.reindexLinearEquiv_one ℝ ℝ finSumFinEquiv

/-- The exact inverse-quarter endpoint in both complete coordinate blocks. -/
def quarterEndpoint (n : ℕ) : OrthogonalMatrixHom (n + n) (n + n) :=
  rotation n 0 1 (by norm_num)

/-- The entire actual endpoint is the original inverse-quarter matrix value. -/
theorem quarterRotation_one (n : ℕ) : quarterRotation n 1 = quarterEndpoint n := by
  apply OrthogonalMatrixHom.ext
  simp only [quarterRotation, quarterEndpoint, rotation, angle, mul_one,
    Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The original final n columns of the complete moving frame. -/
def framePath (n : ℕ) (t : ℝ) : EmbeddingMatrix n (n + n) :=
  ⟨finalPart (quarterRotation n t), finalPart_gram (quarterRotation n t)⟩

/-- The complete inherited n-frame path is continuous on every real parameter. -/
theorem framePath_continuous (n : ℕ) : Continuous (framePath n) := by
  apply Continuous.subtype_mk
  exact (continuous_finalPart (n := n) (k := n + n) (a := n)).comp
    (quarterRotation_continuous n)

/-- The original retained final columns at the identity frame. -/
def identityFrame (n : ℕ) : EmbeddingMatrix n (n + n) :=
  ⟨finalPart (OrthogonalMatrixHom.id (n + n)),
    finalPart_gram (OrthogonalMatrixHom.id (n + n))⟩

/-- The original retained final columns at the actual native block transposition. -/
def transpositionFrame (n : ℕ) : EmbeddingMatrix n (n + n) :=
  ⟨finalPart (OrthogonalIndex.blockSwap n n), finalPart_gram (OrthogonalIndex.blockSwap n n)⟩

/-- The complete original start-frame readback in the stored final-column convention. -/
theorem framePath_zero (n : ℕ) : framePath n 0 = identityFrame n := by
  simp only [framePath, identityFrame, quarterRotation_zero]

/-- The inverse quarter endpoint has the same actual final n columns as the original transpose. -/
theorem quarterEndpoint_finalPart (n : ℕ) :
    finalPart (quarterEndpoint n) = finalPart (OrthogonalIndex.blockSwap n n) := by
  ext i j
  rw [finalPart_apply, finalPart_apply, OrthogonalIndex.blockSwap_matrix,
    finAddFlip_apply_natAdd]
  let e : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv
  obtain ⟨i, rfl⟩ := e.surjective i
  cases i with
  | inl i =>
    simp only [quarterEndpoint, rotation, rotationMatrix, rotationBlocks, e,
      Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd, zero_smul, one_smul,
      Matrix.fromBlocks, Matrix.of_apply, Fin.castAdd_inj]
    change (1 : Matrix (Fin n) (Fin n) ℝ) i j = if i = j then 1 else 0
    exact Matrix.one_apply
  | inr i =>
    have hn : Fin.natAdd n i ≠ Fin.castAdd n j := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    simp only [quarterEndpoint, rotation, rotationMatrix, rotationBlocks, e,
      Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right,
      finSumFinEquiv_symm_apply_natAdd, zero_smul, one_smul,
      Matrix.fromBlocks, Matrix.of_apply, hn, ite_false]
    change (0 : Matrix (Fin n) (Fin n) ℝ) i j = 0
    rfl

/-- The entire first coefficient block is the negative of the original transposition block. -/
theorem quarterEndpoint_coefficientPart (n : ℕ) :
    coefficientPart (quarterEndpoint n) = -coefficientPart (OrthogonalIndex.blockSwap n n) := by
  ext i j
  change (quarterEndpoint n).1 i (Fin.castAdd n j) =
    -(OrthogonalIndex.blockSwap n n).1 i (Fin.castAdd n j)
  rw [OrthogonalIndex.blockSwap_matrix, finAddFlip_apply_castAdd]
  let e : (Fin n ⊕ Fin n) ≃ Fin (n + n) := finSumFinEquiv
  obtain ⟨i, rfl⟩ := e.surjective i
  cases i with
  | inl i =>
    have hn : Fin.castAdd n i ≠ Fin.natAdd n j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp only [quarterEndpoint, rotation, rotationMatrix, rotationBlocks, e,
      Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_symm_apply_castAdd, zero_smul, one_smul, neg_one_smul,
      Matrix.fromBlocks, Matrix.of_apply, hn, ite_false, neg_zero]
    rfl
  | inr i =>
    simp only [quarterEndpoint, rotation, rotationMatrix, rotationBlocks, e,
      Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right,
      finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
      zero_smul, one_smul, neg_one_smul, Matrix.fromBlocks, Matrix.of_apply, Fin.natAdd_inj]
    change -(1 : Matrix (Fin n) (Fin n) ℝ) i j = -(if i = j then 1 else 0)
    exact congrArg (fun x : ℝ => -x) Matrix.one_apply

/-- The actual original first-block isotropy element determined by both complete frames. -/
def coefficientReflection (n : ℕ) : OrthogonalMatrixHom n n :=
  frameChange (OrthogonalIndex.blockSwap n n) (quarterEndpoint n)
    (quarterEndpoint_finalPart n).symm

/-- The whole coefficient isotropy matrix is exactly minus the original identity. -/
theorem coefficientReflection_matrix (n : ℕ) :
    (coefficientReflection n).1 = -(1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [coefficientReflection, frameChange_val, quarterEndpoint_coefficientPart,
    Matrix.mul_neg, coefficientPart_gram]

/-- The complete endpoint is the actual transposition composed with the first-block isotropy. -/
theorem quarterEndpoint_eq_changeCoefficient (n : ℕ) :
    quarterEndpoint n = changeCoefficient (OrthogonalIndex.blockSwap n n)
      (coefficientReflection n) :=
  (changeCoefficient_frameChange (OrthogonalIndex.blockSwap n n) (quarterEndpoint n)
    (quarterEndpoint_finalPart n).symm).symm

/-- The entire native matrix readback is the original transposition times diag(-I,I). -/
theorem quarterEndpoint_matrix (n : ℕ) :
    (quarterEndpoint n).1 = (OrthogonalIndex.blockSwap n n).1 *
      (OrthogonalMatrixHom.blockSum (coefficientReflection n)
        (OrthogonalMatrixHom.id n)).1 :=
  congrArg Subtype.val (quarterEndpoint_eq_changeCoefficient n)

/-- The entire endpoint frame is the actual native transposition frame, including dimension zero. -/
theorem framePath_one (n : ℕ) : framePath n 1 = transpositionFrame n := by
  apply embeddingMatrix_ext
  change finalPart (quarterRotation n 1) = finalPart (OrthogonalIndex.blockSwap n n)
  rw [quarterRotation_one, quarterEndpoint_finalPart]

/-- The actual unit-interval path in the inherited n-frame space. -/
def frameUnitPath (n : ℕ) : C(unitInterval, EmbeddingMatrix n (n + n)) where
  toFun t := framePath n t.val
  continuous_toFun := (framePath_continuous n).comp continuous_subtype_val

/-- Both original matrix-frame endpoint maps are joined by this actual continuous path. -/
def framePathBetween (n : ℕ) : Path (identityFrame n) (transpositionFrame n) where
  toFun := frameUnitPath n
  continuous_toFun := (frameUnitPath n).continuous
  source' := framePath_zero n
  target' := framePath_one n

/-- The exact first-block coordinates of a vector in the original frame. -/
def coefficientCoordinates (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) : Euclidean a :=
  matrixLinear (coefficientPart g).transpose x

/-- The exact retained final-block coordinates, in the original ordered source basis. -/
def retainedCoordinates (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) : Euclidean n :=
  matrixLinear (finalPart g).transpose x

/-- The complete coefficient/retained coordinate pair of the original target vector. -/
def coordinatePair (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    Euclidean a × Euclidean n :=
  (coefficientCoordinates n k a g x, retainedCoordinates n k a g x)

/-- Reconstruct the target vector using both original orthogonal column blocks. -/
def coordinateJoin (n k a : ℕ) (g : Frame n k a) (p : Euclidean a × Euclidean n) :
    Euclidean k :=
  matrixLinear (coefficientPart g) p.1 + matrixLinear (finalPart g) p.2

/-- The original full projector equation reconstructs every complete target vector. -/
theorem coordinateJoin_pair (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    coordinateJoin n k a g (coordinatePair n k a g x) = x := by
  apply WithLp.ofLp_injective
  simp only [coordinateJoin, coordinatePair, coefficientCoordinates, retainedCoordinates,
    WithLp.ofLp_add, matrixLinear_ofLp]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    frame_projector, Matrix.one_mulVec]

/-- Both original Gram equations and both cross equations recover the complete coordinate pair. -/
theorem coordinatePair_join (n k a : ℕ) (g : Frame n k a)
    (p : Euclidean a × Euclidean n) :
    coordinatePair n k a g (coordinateJoin n k a g p) = p := by
  apply Prod.ext
  · apply WithLp.ofLp_injective
    simp only [coordinatePair, coordinateJoin, coefficientCoordinates, WithLp.ofLp_add,
      matrixLinear_ofLp]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      coefficientPart_gram, coefficientPart_transpose_mul_finalPart,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  · apply WithLp.ofLp_injective
    simp only [coordinatePair, coordinateJoin, retainedCoordinates, WithLp.ofLp_add,
      matrixLinear_ofLp]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      finalPart_transpose_mul_coefficientPart, finalPart_gram,
      Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]

/-- The whole original coordinate decomposition preserves the exact sum of squared norms. -/
theorem coordinatePair_norm_sq (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    ‖(coordinatePair n k a g x).1‖ ^ 2 + ‖(coordinatePair n k a g x).2‖ ^ 2 = ‖x‖ ^ 2 := by
  let y : Euclidean (a + n) := matrixLinear g.1.transpose x
  have hy : ‖y‖ = ‖x‖ := matrixLinear_norm g.1.transpose (by
    simpa only [Matrix.transpose_transpose] using g.2.2) x
  have hc (i : Fin a) : (coefficientCoordinates n k a g x).ofLp i =
      y.ofLp (Fin.castAdd n i) := by
    dsimp only [coefficientCoordinates, y]
    rw [matrixLinear_ofLp, matrixLinear_ofLp]
    rfl
  have hf (i : Fin n) : (retainedCoordinates n k a g x).ofLp i =
      y.ofLp (Fin.natAdd a i) := by
    dsimp only [retainedCoordinates, y]
    rw [matrixLinear_ofLp, matrixLinear_ofLp]
    rfl
  rw [← hy]
  simp only [coordinatePair, EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_add]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : ℝ => z ^ 2) (hc i)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : ℝ => z ^ 2) (hf i)

/-- Both actual coordinate functions vary continuously with the full inherited frame and vector. -/
theorem coordinatePair_continuous (n k a : ℕ) :
    Continuous (fun p : Frame n k a × Euclidean k => coordinatePair n k a p.1 p.2) := by
  apply Continuous.prodMk
  · exact (EuclideanSpace.equiv (Fin a) ℝ).symm.continuous.comp
      (((continuous_coefficientPart.comp continuous_fst).matrix_transpose).matrix_mulVec
        ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp continuous_snd))
  · exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
      (((continuous_finalPart.comp continuous_fst).matrix_transpose).matrix_mulVec
        ((EuclideanSpace.equiv (Fin k) ℝ).continuous.comp continuous_snd))

/-- The complete finite complement/sphere split, using the original proper bundle generator. -/
def splitVector (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    ComplementBundle n k × Euclidean n :=
  (rawMap n k a (g, coefficientCoordinates n k a g x), retainedCoordinates n k a g x)

/-- The actual finite split keeps the original retained n-frame as its bundle base. -/
theorem splitVector_base (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    bundleBase (splitVector n k a g x).1 = frameBase g := rfl

/-- The split preserves the exact combined complement and sphere norm, at every original vector. -/
theorem splitVector_norm_sq (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    ‖bundleVector (splitVector n k a g x).1‖ ^ 2 + ‖(splitVector n k a g x).2‖ ^ 2 =
      ‖x‖ ^ 2 := by
  rw [splitVector, rawMap_norm]
  exact coordinatePair_norm_sq n k a g x

/-- The whole finite complement/sphere split is continuous on the inherited frame/vector space. -/
theorem splitVector_continuous (n k a : ℕ) :
    Continuous (fun p : Frame n k a × Euclidean k => splitVector n k a p.1 p.2) := by
  exact ((rawMap_continuous n k a).comp
    (continuous_fst.prodMk (continuous_fst.comp (coordinatePair_continuous n k a)))).prodMk
      (continuous_snd.comp (coordinatePair_continuous n k a))

/-- The actual real-parameter split along the original quarter-rotation frame. -/
def rotatingSplit (n : ℕ) (p : ℝ × Euclidean (n + n)) :
    ComplementBundle n (n + n) × Euclidean n :=
  splitVector n (n + n) n (quarterRotation n p.1) p.2

/-- The whole actual rotating split is jointly continuous, including all original vector values. -/
theorem rotatingSplit_continuous (n : ℕ) : Continuous (rotatingSplit n) :=
  (splitVector_continuous n (n + n) n).comp
    (((quarterRotation_continuous n).comp continuous_fst).prodMk continuous_snd)

/-- Every parameter of the actual rotation keeps the entire source sphere coordinate's norm. -/
theorem rotatingSplit_norm_sq (n : ℕ) (t : ℝ) (x : Euclidean (n + n)) :
    ‖bundleVector (rotatingSplit n (t, x)).1‖ ^ 2 + ‖(rotatingSplit n (t, x)).2‖ ^ 2 =
      ‖x‖ ^ 2 := splitVector_norm_sq n (n + n) n (quarterRotation n t) x

/-- Reconstruct the actual ambient sphere coordinate from a complement vector and source vector. -/
def vectorJoin (n k : ℕ) (p : ComplementBundle n k × Euclidean n) : Euclidean k :=
  bundleVector p.1 + matrixLinear (bundleBase p.1).1 p.2

/-- Every finite split retains exactly the entire original ambient sphere vector. -/
theorem vectorJoin_splitVector (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    vectorJoin n k (splitVector n k a g x) = x :=
  coordinateJoin_pair n k a g x

/-- The whole rotating split keeps the original sphere coordinate fixed at every parameter. -/
theorem vectorJoin_rotatingSplit (n : ℕ) (t : ℝ) (x : Euclidean (n + n)) :
    vectorJoin n (n + n) (rotatingSplit n (t, x)) = x :=
  vectorJoin_splitVector n (n + n) n (quarterRotation n t) x

/-- The reconstructed ambient vector is jointly continuous for all actual bundle/source points. -/
theorem vectorJoin_continuous (n k : ℕ) : Continuous (vectorJoin n k) := by
  exact (continuous_bundleVector.comp continuous_fst).add
    ((EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp
      (((continuous_bundleBase.comp continuous_fst).subtype_val).matrix_mulVec
        ((EuclideanSpace.equiv (Fin n) ℝ).continuous.comp continuous_snd)))

/-- The original complement equation gives exact orthogonality to every retained source vector. -/
theorem vectorJoin_inner (n k : ℕ) (p : ComplementBundle n k × Euclidean n) :
    ⟪bundleVector p.1, matrixLinear (bundleBase p.1).1 p.2⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial, matrixLinear_ofLp]
  change p.1.1.2.ofLp ⬝ᵥ (p.1.1.1 *ᵥ p.2.ofLp) = 0
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, p.1.2.2]
  simp

/-- The whole reconstructed coordinate has precisely the original orthogonal sum norm. -/
theorem vectorJoin_norm_sq (n k : ℕ) (p : ComplementBundle n k × Euclidean n) :
    ‖vectorJoin n k p‖ ^ 2 = ‖bundleVector p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  simp only [pow_two]
  rw [vectorJoin, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (bundleVector p.1) (matrixLinear (bundleBase p.1).1 p.2) (vectorJoin_inner n k p),
    matrixLinear_norm (bundleBase p.1).1 p.1.2.1]

/-- For the actual matching n-frame, the full split recovers every complement/source pair. -/
theorem splitVector_vectorJoin (n k a : ℕ) (g : Frame n k a)
    (p : ComplementBundle n k × Euclidean n) (hbase : bundleBase p.1 = frameBase g) :
    splitVector n k a g (vectorJoin n k p) = p := by
  have hA : p.1.1.1 = finalPart g := congrArg Subtype.val hbase
  have hj : vectorJoin n k p = bundleVector p.1 + matrixLinear (finalPart g) p.2 := by
    rw [vectorJoin, hbase]
    rfl
  have hp : matrixLinear (finalPart g).transpose (bundleVector p.1) = 0 := by
    apply WithLp.ofLp_injective
    rw [matrixLinear_ofLp]
    change (finalPart g).transpose *ᵥ p.1.1.2.ofLp = 0
    rw [← hA]
    exact p.1.2.2
  have hc : coefficientCoordinates n k a g (vectorJoin n k p) = recover n k a (g, p.1) := by
    change matrixLinear (coefficientPart g).transpose (vectorJoin n k p) = _
    rw [hj, map_add, ← matrixLinear_mul, coefficientPart_transpose_mul_finalPart,
      matrixLinear_zero, add_zero]
    rfl
  have hf : retainedCoordinates n k a g (vectorJoin n k p) = p.2 := by
    change matrixLinear (finalPart g).transpose (vectorJoin n k p) = _
    rw [hj, map_add, hp, ← matrixLinear_mul, finalPart_gram, matrixLinear_one, zero_add]
  change (rawMap n k a (g, coefficientCoordinates n k a g (vectorJoin n k p)),
    retainedCoordinates n k a g (vectorJoin n k p)) = p
  rw [hc, hf, rawMap_recover n k a g p.1 hA.symm]

/-- All coefficient frames over the same actual retained base give the same entire split. -/
theorem splitVector_eq_of_frameBase_eq (n k a b : ℕ) (g : Frame n k a) (h : Frame n k b)
    (hbase : frameBase g = frameBase h) (x : Euclidean k) :
    splitVector n k a g x = splitVector n k b h x := by
  calc
    splitVector n k a g x =
        splitVector n k a g (vectorJoin n k (splitVector n k b h x)) := by
      rw [vectorJoin_splitVector]
    _ = splitVector n k b h x :=
      splitVector_vectorJoin n k a g (splitVector n k b h x)
        ((splitVector_base n k b h x).trans hbase.symm)

/-- The whole original coefficient precomposition acts trivially on the full complement split. -/
theorem splitVector_changeCoefficient (n k a : ℕ) (g : Frame n k a)
    (r : OrthogonalMatrixHom a a) (x : Euclidean k) :
    splitVector n k a (changeCoefficient g r) x = splitVector n k a g x := by
  apply splitVector_eq_of_frameBase_eq
  apply embeddingMatrix_ext
  exact changeCoefficient_finalPart g r

/-- All original coefficient-degree arrows retain the whole split, not only endomorphisms. -/
theorem splitVector_changeCoefficientAcross (n k a b : ℕ) (g : Frame n k b)
    (r : OrthogonalMatrixHom a b) (x : Euclidean k) :
    splitVector n k a (changeCoefficientAcross g r) x = splitVector n k b g x := by
  apply splitVector_eq_of_frameBase_eq
  apply embeddingMatrix_ext
  exact changeCoefficientAcross_finalPart g r

/-- The inherited fiber of the complete complement/source pair over one actual frame. -/
abbrev SplitFiber (n k a : ℕ) (g : Frame n k a) :=
  {p : ComplementBundle n k × Euclidean n // bundleBase p.1 = frameBase g}

/-- The actual fixed-frame fiber is closed in the original full product. -/
theorem splitFiber_isClosed (n k a : ℕ) (g : Frame n k a) :
    IsClosed {p : ComplementBundle n k × Euclidean n | bundleBase p.1 = frameBase g} :=
  isClosed_eq (continuous_bundleBase.comp continuous_fst) continuous_const

/-- Both complete split functions identify the retained-base fiber
with the original ambient vector. -/
def splitFiberHomeomorph (n k a : ℕ) (g : Frame n k a) : Euclidean k ≃ₜ SplitFiber n k a g where
  toFun x := ⟨splitVector n k a g x, rfl⟩
  invFun p := vectorJoin n k p.1
  left_inv := vectorJoin_splitVector n k a g
  right_inv p := Subtype.ext (splitVector_vectorJoin n k a g p.1 p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (splitVector_continuous n k a).comp (continuous_const.prodMk continuous_id)
  continuous_invFun := (vectorJoin_continuous n k).comp continuous_subtype_val

/-- Every complete actual fixed-frame split is a proper map into the original full product. -/
theorem splitVector_proper (n k a : ℕ) (g : Frame n k a) :
    IsProperMap (splitVector n k a g) :=
  (splitFiber_isClosed n k a g).isProperMap_subtypeVal.comp
    (splitFiberHomeomorph n k a g).isProperMap

/-- Every original fixed-frame split preserves the compactification filter. -/
theorem splitVector_tendsto_coclosedCompact (n k a : ℕ) (g : Frame n k a) :
    Tendsto (splitVector n k a g) (coclosedCompact (Euclidean k))
      (coclosedCompact (ComplementBundle n k × Euclidean n)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp (splitVector_proper n k a g)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The complete actual fixed-frame sphere map, before the original product-to-smash comparison. -/
def onePointSplit (n k a : ℕ) (g : Frame n k a) :
    C(OnePoint (Euclidean k), OnePoint (ComplementBundle n k × Euclidean n)) :=
  ⟨OnePoint.map (splitVector n k a g),
    OnePoint.continuous_map
      ((splitVector_continuous n k a).comp (continuous_const.prodMk continuous_id))
      (splitVector_tendsto_coclosedCompact n k a g)⟩

@[simp]
theorem onePointSplit_infty (n k a : ℕ) (g : Frame n k a) :
    onePointSplit n k a g OnePoint.infty = OnePoint.infty := rfl

@[simp]
theorem onePointSplit_coe (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    onePointSplit n k a g (x : OnePoint (Euclidean k)) =
      (splitVector n k a g x : OnePoint (ComplementBundle n k × Euclidean n)) := rfl

/-- The whole compactified map is independent of all original coefficient frame choices. -/
theorem onePointSplit_eq_of_frameBase_eq (n k a b : ℕ) (g : Frame n k a) (h : Frame n k b)
    (hbase : frameBase g = frameBase h) : onePointSplit n k a g = onePointSplit n k b h := by
  apply ContinuousMap.ext
  intro x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
      exact congrArg ((↑) : ComplementBundle n k × Euclidean n →
        OnePoint (ComplementBundle n k × Euclidean n))
        (splitVector_eq_of_frameBase_eq n k a b g h hbase x)

/-- The full finite split on the actual compact unit-interval parameter. -/
def unitRotatingSplit (n : ℕ) (p : unitInterval × Euclidean (n + n)) :
    ComplementBundle n (n + n) × Euclidean n :=
  rotatingSplit n (p.1.val, p.2)

/-- Both the interval parameter and every original vector vary jointly continuously. -/
theorem unitRotatingSplit_continuous (n : ℕ) : Continuous (unitRotatingSplit n) :=
  (rotatingSplit_continuous n).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- The full closed pullback of the moving retained frame, with both original vector factors. -/
abbrev MovingFramePullback (n : ℕ) :=
  {p : unitInterval × (ComplementBundle n (n + n) × Euclidean n) //
    bundleBase p.2.1 = framePath n p.1.val}

/-- The actual matching-base condition is closed in the inherited product topology. -/
theorem movingFramePullback_isClosed (n : ℕ) :
    IsClosed {p : unitInterval × (ComplementBundle n (n + n) × Euclidean n) |
      bundleBase p.2.1 = framePath n p.1.val} :=
  isClosed_eq (continuous_bundleBase.comp (continuous_fst.comp continuous_snd))
    ((framePath_continuous n).comp (continuous_subtype_val.comp continuous_fst))

/-- The complete moving-frame graph homeomorphism uses
the original ambient vector in its inverse. -/
def movingFrameGraphHomeomorph (n : ℕ) :
    unitInterval × Euclidean (n + n) ≃ₜ MovingFramePullback n where
  toFun p := ⟨(p.1, unitRotatingSplit n p), rfl⟩
  invFun p := (p.1.1, vectorJoin n (n + n) p.1.2)
  left_inv p := Prod.ext rfl (vectorJoin_rotatingSplit n p.1.val p.2)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact splitVector_vectorJoin n (n + n) n (quarterRotation n p.1.1.val) p.1.2 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (unitRotatingSplit_continuous n)
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((vectorJoin_continuous n (n + n)).comp
        (continuous_snd.comp continuous_subtype_val))

/-- Projection from the closed moving-frame pullback is proper using the actual compact interval. -/
theorem movingFramePullback_projection_proper (n : ℕ) :
    IsProperMap (fun p : MovingFramePullback n => p.1.2) :=
  isProperMap_snd_of_compactSpace.comp
    (movingFramePullback_isClosed n).isProperMap_subtypeVal

/-- The whole finite parameter/vector split is proper, without a supplied properness premise. -/
theorem unitRotatingSplit_proper (n : ℕ) : IsProperMap (unitRotatingSplit n) :=
  (movingFramePullback_projection_proper n).comp (movingFrameGraphHomeomorph n).isProperMap

/-- The actual original compactification filter is preserved jointly in the full interval. -/
theorem unitRotatingSplit_tendsto_coclosedCompact (n : ℕ) :
    Tendsto (unitRotatingSplit n) (coclosedCompact (unitInterval × Euclidean (n + n)))
      (coclosedCompact (ComplementBundle n (n + n) × Euclidean n)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp (unitRotatingSplit_proper n)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The entire pointed homotopy before the original product-to-smash comparison. -/
def onePointRotatingSplit (n : ℕ) :
    unitInterval × OnePoint (Euclidean (n + n)) →
      OnePoint (ComplementBundle n (n + n) × Euclidean n) := fun p =>
  OnePoint.rec OnePoint.infty (fun x =>
    (unitRotatingSplit n (p.1, x) :
      OnePoint (ComplementBundle n (n + n) × Euclidean n))) p.2

/-- Joint continuity at the whole sphere infinity face follows from the proved proper graph. -/
theorem onePointRotatingSplit_continuous (n : ℕ) : Continuous (onePointRotatingSplit n) := by
  let K := unitInterval
  let E := Euclidean (n + n)
  let embed : K × OnePoint E → OnePoint K × OnePoint E := fun p => ((p.1 : OnePoint K), p.2)
  have he : Continuous embed :=
    (OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (PointedCGWH.rawCollapse K E ∘ embed) :=
    (PointedCGWH.rawCollapse_continuous K E).comp he
  have hm : Continuous (OnePoint.map (unitRotatingSplit n)) :=
    OnePoint.continuous_map (unitRotatingSplit_continuous n)
      (unitRotatingSplit_tendsto_coclosedCompact n)
  convert hm.comp hc using 1
  funext p
  rcases p with ⟨t, x⟩
  induction x using OnePoint.rec <;> rfl

@[simp]
theorem onePointRotatingSplit_infty (n : ℕ) (t : unitInterval) :
    onePointRotatingSplit n (t, OnePoint.infty) = OnePoint.infty := rfl

@[simp]
theorem onePointRotatingSplit_coe (n : ℕ) (t : unitInterval) (x : Euclidean (n + n)) :
    onePointRotatingSplit n (t, (x : OnePoint (Euclidean (n + n)))) =
      (rotatingSplit n (t.val, x) :
        OnePoint (ComplementBundle n (n + n) × Euclidean n)) := rfl

/-- The entire start map is the actual identity-frame compactified split. -/
theorem onePointRotatingSplit_zero (n : ℕ) (x : OnePoint (Euclidean (n + n))) :
    onePointRotatingSplit n (0, x) =
      onePointSplit n (n + n) n (OrthogonalMatrixHom.id (n + n)) x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
      change (splitVector n (n + n) n (quarterRotation n 0) x :
        OnePoint (ComplementBundle n (n + n) × Euclidean n)) = _
      rw [quarterRotation_zero]
      rfl

/-- The entire endpoint map is the actual native transposition split
with the same ambient sphere. -/
theorem onePointRotatingSplit_one (n : ℕ) (x : OnePoint (Euclidean (n + n))) :
    onePointRotatingSplit n (1, x) =
      onePointSplit n (n + n) n (OrthogonalIndex.blockSwap n n) x := by
  have hbase : frameBase (quarterEndpoint n) = frameBase (OrthogonalIndex.blockSwap n n) := by
    apply embeddingMatrix_ext
    exact quarterEndpoint_finalPart n
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
      change (splitVector n (n + n) n (quarterRotation n 1) x :
        OnePoint (ComplementBundle n (n + n) × Euclidean n)) = _
      rw [quarterRotation_one]
      exact congrArg ((↑) : ComplementBundle n (n + n) × Euclidean n →
        OnePoint (ComplementBundle n (n + n) × Euclidean n))
        (splitVector_eq_of_frameBase_eq n (n + n) n n
          (quarterEndpoint n) (OrthogonalIndex.blockSwap n n) hbase x)

/-- A full actual based homotopy joins the original identity and transposition sphere maps. -/
def onePointSplitHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (onePointSplit n (n + n) n (OrthogonalMatrixHom.id (n + n)))
      (onePointSplit n (n + n) n (OrthogonalIndex.blockSwap n n)) where
  toFun := onePointRotatingSplit n
  continuous_toFun := onePointRotatingSplit_continuous n
  map_zero_left := onePointRotatingSplit_zero n
  map_one_left := onePointRotatingSplit_one n

/-- The whole homotopy fixes the original sphere basepoint at every interval value. -/
theorem onePointSplitHomotopy_infty (n : ℕ) (t : unitInterval) :
    onePointSplitHomotopy n (t, OnePoint.infty) = OnePoint.infty := rfl

/-- The original interval parameter lifted into the independent native carrier universe. -/
abbrev LiftedInterval := ULift.{v, 0} unitInterval

/-- Lift both actual output vector factors without changing their original finite split. -/
def liftedSplitVector (n k a : ℕ) (g : Frame n k a) (x : LiftedEuclidean.{v} k) :
    LiftedBundle.{v} n k × LiftedEuclidean.{v} n :=
  let p := splitVector n k a g x.down
  (ULift.up p.1, ULift.up p.2)

/-- The full original finite map is continuous through the exact lift homeomorphisms. -/
theorem liftedSplitVector_continuous (n k a : ℕ) (g : Frame n k a) :
    Continuous (liftedSplitVector.{v} n k a g) :=
  ((continuous_uliftUp.comp continuous_fst).prodMk
    (continuous_uliftUp.comp continuous_snd)).comp
      (((splitVector_continuous n k a).comp (continuous_const.prodMk continuous_id)).comp
        continuous_uliftDown)

/-- The full lifted proper map retains both original output factors and the source vector. -/
theorem liftedSplitVector_proper (n k a : ℕ) (g : Frame n k a) :
    IsProperMap (liftedSplitVector.{v} n k a g) :=
  ((Homeomorph.ulift (X := ComplementBundle n k)).symm.prodCongr
    (Homeomorph.ulift (X := Euclidean n)).symm).isProperMap.comp
      ((splitVector_proper n k a g).comp (Homeomorph.ulift (X := Euclidean k)).isProperMap)

/-- Every original lifted frame split preserves the actual native compactification filter. -/
theorem liftedSplitVector_tendsto_coclosedCompact (n k a : ℕ) (g : Frame n k a) :
    Tendsto (liftedSplitVector.{v} n k a g) (coclosedCompact (LiftedEuclidean.{v} k))
      (coclosedCompact (LiftedBundle.{v} n k × LiftedEuclidean.{v} n)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp (liftedSplitVector_proper.{v} n k a g)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The actual lifted source and both lifted output factors of the entire interval split. -/
def liftedUnitRotatingSplit (n : ℕ)
    (p : LiftedInterval.{v} × LiftedEuclidean.{v} (n + n)) :
    LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n :=
  let q := unitRotatingSplit n (p.1.down, p.2.down)
  (ULift.up q.1, ULift.up q.2)

/-- The whole native-universe interval/vector function is jointly continuous. -/
theorem liftedUnitRotatingSplit_continuous (n : ℕ) :
    Continuous (liftedUnitRotatingSplit.{v} n) :=
  ((continuous_uliftUp.comp continuous_fst).prodMk
    (continuous_uliftUp.comp continuous_snd)).comp
      ((unitRotatingSplit_continuous n).comp
        ((continuous_uliftDown.comp continuous_fst).prodMk
          (continuous_uliftDown.comp continuous_snd)))

/-- Properness uses the exact compact interval, source lift and both original output lifts. -/
theorem liftedUnitRotatingSplit_proper (n : ℕ) :
    IsProperMap (liftedUnitRotatingSplit.{v} n) :=
  ((Homeomorph.ulift (X := ComplementBundle n (n + n))).symm.prodCongr
    (Homeomorph.ulift (X := Euclidean n)).symm).isProperMap.comp
      ((unitRotatingSplit_proper n).comp
        ((Homeomorph.ulift (X := unitInterval)).prodCongr
          (Homeomorph.ulift (X := Euclidean (n + n)))).isProperMap)

/-- The whole lifted parameter/vector map preserves the original compactification filter. -/
theorem liftedUnitRotatingSplit_tendsto_coclosedCompact (n : ℕ) :
    Tendsto (liftedUnitRotatingSplit.{v} n)
      (coclosedCompact (LiftedInterval.{v} × LiftedEuclidean.{v} (n + n)))
      (coclosedCompact (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) := by
  have h := (isProperMap_iff_tendsto_cocompact.mp
    (liftedUnitRotatingSplit_proper.{v} n)).2
  simpa only [coclosedCompact_eq_cocompact] using h

/-- The actual whole native-universe compactified homotopy before the product-to-smash map. -/
def liftedOnePointRotatingSplit (n : ℕ) :
    LiftedInterval.{v} × OnePoint (LiftedEuclidean.{v} (n + n)) →
      OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n) := fun p =>
  OnePoint.rec OnePoint.infty (fun x =>
    (liftedUnitRotatingSplit n (p.1, x) :
      OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n))) p.2

/-- All infinity parameters remain jointly continuous in the independent native universe. -/
theorem liftedOnePointRotatingSplit_continuous (n : ℕ) :
    Continuous (liftedOnePointRotatingSplit.{v} n) := by
  let K := LiftedInterval.{v}
  let E := LiftedEuclidean.{v} (n + n)
  let embed : K × OnePoint E → OnePoint K × OnePoint E := fun p => ((p.1 : OnePoint K), p.2)
  have he : Continuous embed :=
    (OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (PointedCGWH.rawCollapse K E ∘ embed) :=
    (PointedCGWH.rawCollapse_continuous K E).comp he
  have hm : Continuous (OnePoint.map (liftedUnitRotatingSplit.{v} n)) :=
    OnePoint.continuous_map (liftedUnitRotatingSplit_continuous n)
      (liftedUnitRotatingSplit_tendsto_coclosedCompact n)
  convert hm.comp hc using 1
  funext p
  rcases p with ⟨t, x⟩
  induction x using OnePoint.rec <;> rfl

@[simp]
theorem liftedOnePointRotatingSplit_infty (n : ℕ) (t : LiftedInterval.{v}) :
    liftedOnePointRotatingSplit.{v} n (t, OnePoint.infty) = OnePoint.infty := rfl

@[simp]
theorem liftedOnePointRotatingSplit_coe (n : ℕ) (t : LiftedInterval.{v})
    (x : LiftedEuclidean.{v} (n + n)) :
    liftedOnePointRotatingSplit.{v} n (t, (x : OnePoint (LiftedEuclidean.{v} (n + n)))) =
      (liftedUnitRotatingSplit n (t, x) :
        OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) := rfl

/-- The complete native product-compactification comparison, with both actual factor topologies. -/
def targetProductIso (n k : ℕ) :
    PointedCGWH.onePointOf.{u, v} (LiftedBundle.{v} n k × LiftedEuclidean.{v} n) ≅
      thom.{u, v} n k ⊗ PointedCGWH.orthogonalSphere.{u, v} n :=
  PointedCGWH.onePointProdSmashIso _ _
    (liftedBundleOnePoint_generated n k) (liftedEuclideanOnePoint_generated n)

/-- The genuine original based sphere-to-complement smash map at every complete actual frame. -/
def pointedSplit (n k a : ℕ) (g : Frame n k a) :
    PointedCGWH.orthogonalSphere.{u, v} k ⟶
      thom.{u, v} n k ⊗ PointedCGWH.orthogonalSphere.{u, v} n :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedSplitVector n k a g, liftedSplitVector_continuous n k a g⟩
    (liftedSplitVector_tendsto_coclosedCompact n k a g) ≫ (targetProductIso n k).hom

/-- The whole original proper-map extension and actual product comparison are retained. -/
theorem pointedSplit_eq (n k a : ℕ) (g : Frame n k a) :
    pointedSplit.{u, v} n k a g =
      PointedCGWH.onePointMapOfProper
        ⟨liftedSplitVector n k a g, liftedSplitVector_continuous n k a g⟩
        (liftedSplitVector_tendsto_coclosedCompact n k a g) ≫
          (targetProductIso n k).hom := rfl

/-- Every finite native source sphere point has the exact original complement/sphere formula. -/
theorem pointedSplit_coe (n k a : ℕ) (g : Frame n k a) (x : LiftedEuclidean.{v} k) :
    (pointedSplit.{u, v} n k a g).right (x : OnePoint (LiftedEuclidean.{v} k)) =
      (targetProductIso n k).hom.right
        (liftedSplitVector n k a g x :
          OnePoint (LiftedBundle.{v} n k × LiftedEuclidean.{v} n)) := rfl

/-- The actual sphere basepoint maps to the original target smash basepoint. -/
theorem pointedSplit_infty (n k a : ℕ) (g : Frame n k a) :
    (pointedSplit.{u, v} n k a g).right OnePoint.infty =
      (thom.{u, v} n k ⊗ PointedCGWH.orthogonalSphere.{u, v} n).hom PUnit.unit :=
  PointedCGWH.mapOnePoint_infty (pointedSplit n k a g)

/-- The entire native based map is independent of all original coefficient frame choices. -/
theorem pointedSplit_eq_of_frameBase_eq (n k a b : ℕ) (g : Frame n k a) (h : Frame n k b)
    (hbase : frameBase g = frameBase h) :
    pointedSplit.{u, v} n k a g = pointedSplit.{u, v} n k b h := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
      rw [pointedSplit_coe, pointedSplit_coe]
      apply congrArg (targetProductIso n k).hom.right
      apply congrArg ((↑) : LiftedBundle.{v} n k × LiftedEuclidean.{v} n →
        OnePoint (LiftedBundle.{v} n k × LiftedEuclidean.{v} n))
      exact congrArg (fun p : ComplementBundle n k × Euclidean n =>
        (ULift.up p.1, ULift.up p.2)) (splitVector_eq_of_frameBase_eq n k a b g h hbase x.down)

/-- The complete actual lifted fixed-frame compactified map with its proved ordinary continuity. -/
def liftedOnePointSplit (n k a : ℕ) (g : Frame n k a) :
    C(OnePoint (LiftedEuclidean.{v} k),
      OnePoint (LiftedBundle.{v} n k × LiftedEuclidean.{v} n)) :=
  ⟨OnePoint.map (liftedSplitVector n k a g),
    OnePoint.continuous_map (liftedSplitVector_continuous n k a g)
      (liftedSplitVector_tendsto_coclosedCompact n k a g)⟩

/-- The entire lifted sphere homotopy joins the two original complete native frame maps. -/
def liftedOnePointSplitHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (liftedOnePointSplit.{v} n (n + n) n (OrthogonalMatrixHom.id (n + n)))
      (liftedOnePointSplit.{v} n (n + n) n (OrthogonalIndex.blockSwap n n)) where
  toFun p := liftedOnePointRotatingSplit n (ULift.up p.1, p.2)
  continuous_toFun := (liftedOnePointRotatingSplit_continuous n).comp
    ((continuous_uliftUp.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe x =>
        change ((ULift.up (splitVector n (n + n) n (quarterRotation n 0) x.down).1,
          ULift.up (splitVector n (n + n) n (quarterRotation n 0) x.down).2) :
            OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) = _
        rw [quarterRotation_zero]
        rfl
  map_one_left x := by
    have hbase : frameBase (quarterEndpoint n) = frameBase (OrthogonalIndex.blockSwap n n) := by
      apply embeddingMatrix_ext
      exact quarterEndpoint_finalPart n
    induction x using OnePoint.rec with
    | infty => rfl
    | coe x =>
        change ((ULift.up (splitVector n (n + n) n (quarterRotation n 1) x.down).1,
          ULift.up (splitVector n (n + n) n (quarterRotation n 1) x.down).2) :
            OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) = _
        rw [quarterRotation_one,
          splitVector_eq_of_frameBase_eq n (n + n) n n
            (quarterEndpoint n) (OrthogonalIndex.blockSwap n n) hbase]
        rfl

/-- The whole lifted homotopy is stationary at the original sphere infinity. -/
theorem liftedOnePointSplitHomotopy_infty (n : ℕ) (t : unitInterval) :
    liftedOnePointSplitHomotopy.{v} n (t, OnePoint.infty) = OnePoint.infty := rfl

private def properOnePointNativeHomotopy
    {E F : Type v} [TopologicalSpace E] [LocallyCompactSpace E] [T2Space E]
    [TopologicalSpace F] [LocallyCompactSpace F] [T2Space F]
    [UCompactlyGeneratedSpace.{u} (OnePoint E)]
    [UCompactlyGeneratedSpace.{u} (OnePoint F)]
    (f₀ f₁ : C(E, F))
    (hf₀ : Tendsto f₀ (coclosedCompact E) (coclosedCompact F))
    (hf₁ : Tendsto f₁ (coclosedCompact E) (coclosedCompact F))
    (H : ContinuousMap.Homotopy
      ⟨OnePoint.map f₀, OnePoint.continuous_map f₀.continuous hf₀⟩
      ⟨OnePoint.map f₁, OnePoint.continuous_map f₁.continuous hf₁⟩) :
    ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, v})
        (PointedCGWH.onePointMapOfProper.{u, v} f₀ hf₀).right)
      (ConcreteCategory.hom (C := CGWH.{u, v})
        (PointedCGWH.onePointMapOfProper.{u, v} f₁ hf₁).right) := by
  let cE := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint E)
  let cF := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint F)
  have hE (x : (PointedCGWH.onePointOf.{u, v} E).right) : cE.1 x = x := cE.2 x
  have hF (x : OnePoint F) : cF.1.symm x = x :=
    (cF.2 (cF.1.symm x)).symm.trans (cF.1.apply_symm_apply x)
  exact
    { toFun := fun p => cF.1.symm (H (p.1, cE.1 p.2))
      continuous_toFun := cF.1.symm.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (cE.1.continuous.comp continuous_snd)))
      map_zero_left := by
        intro x
        exact (congrArg cF.1.symm (H.map_zero_left (cE.1 x))).trans
          ((hF (OnePoint.map f₀ (cE.1 x))).trans
            (congrArg (OnePoint.map f₀) (hE x)))
      map_one_left := by
        intro x
        exact (congrArg cF.1.symm (H.map_one_left (cE.1 x))).trans
          ((hF (OnePoint.map f₁ (cE.1 x))).trans
            (congrArg (OnePoint.map f₁) (hE x))) }

private theorem properOnePointNativeHomotopy_apply
    {E F : Type v} [TopologicalSpace E] [LocallyCompactSpace E] [T2Space E]
    [TopologicalSpace F] [LocallyCompactSpace F] [T2Space F]
    [UCompactlyGeneratedSpace.{u} (OnePoint E)]
    [UCompactlyGeneratedSpace.{u} (OnePoint F)]
    (f₀ f₁ : C(E, F))
    (hf₀ : Tendsto f₀ (coclosedCompact E) (coclosedCompact F))
    (hf₁ : Tendsto f₁ (coclosedCompact E) (coclosedCompact F))
    (H : ContinuousMap.Homotopy
      ⟨OnePoint.map f₀, OnePoint.continuous_map f₀.continuous hf₀⟩
      ⟨OnePoint.map f₁, OnePoint.continuous_map f₁.continuous hf₁⟩)
    (t : unitInterval) (x : (PointedCGWH.onePointOf.{u, v} E).right) :
    properOnePointNativeHomotopy f₀ f₁ hf₀ hf₁ H (t, x) = H (t, x) := by
  let cE := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint E)
  let cF := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint F)
  change cF.1.symm (H (t, cE.1 x)) = H (t, x)
  exact ((cF.2 (cF.1.symm (H (t, cE.1 x)))).symm.trans
    (cF.1.apply_symm_apply (H (t, cE.1 x)))).trans
      (congrArg (fun z => H (t, z)) (cE.2 x))

/-- The complete sphere-product compactification has the actual inherited generated topology. -/
theorem liftedSplitProductOnePoint_generated (n k : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k × LiftedEuclidean.{v} n)) :=
  PointedCGWH.onePointProduct_generated _ _
    (liftedBundleOnePoint_generated n k) (liftedEuclideanOnePoint_generated n)

/-- The entire original proper-map homotopy as a homotopy of genuine native based arrows. -/
def pointedSplitHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, v}) (pointedSplit.{u, v} n (n + n) n
        (OrthogonalMatrixHom.id (n + n))).right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) (pointedSplit.{u, v} n (n + n) n
        (OrthogonalIndex.blockSwap n n)).right) := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedEuclidean.{v} (n + n))) :=
    liftedEuclideanOnePoint_generated (n + n)
  letI : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) :=
    liftedSplitProductOnePoint_generated n (n + n)
  let H := properOnePointNativeHomotopy
    ⟨liftedSplitVector n (n + n) n (OrthogonalMatrixHom.id (n + n)),
      liftedSplitVector_continuous n (n + n) n (OrthogonalMatrixHom.id (n + n))⟩
    ⟨liftedSplitVector n (n + n) n (OrthogonalIndex.blockSwap n n),
      liftedSplitVector_continuous n (n + n) n (OrthogonalIndex.blockSwap n n)⟩
    (liftedSplitVector_tendsto_coclosedCompact n (n + n) n
      (OrthogonalMatrixHom.id (n + n)))
    (liftedSplitVector_tendsto_coclosedCompact n (n + n) n (OrthogonalIndex.blockSwap n n))
    (liftedOnePointSplitHomotopy n)
  exact (ContinuousMap.Homotopy.refl
    (ConcreteCategory.hom (C := CGWH.{u, v}) (targetProductIso n (n + n)).hom.right)).comp H

/-- Every native interval/sphere point retains the complete original compactified split formula. -/
theorem pointedSplitHomotopy_apply (n : ℕ) (t : unitInterval)
    (x : (PointedCGWH.orthogonalSphere.{u, v} (n + n)).right) :
    pointedSplitHomotopy.{u, v} n (t, x) =
      (targetProductIso n (n + n)).hom.right (liftedOnePointSplitHomotopy.{v} n (t, x)) := by
  let : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedEuclidean.{v} (n + n))) :=
    liftedEuclideanOnePoint_generated (n + n)
  let : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) :=
    liftedSplitProductOnePoint_generated n (n + n)
  exact congrArg (targetProductIso n (n + n)).hom.right
    (properOnePointNativeHomotopy_apply
      ⟨liftedSplitVector n (n + n) n (OrthogonalMatrixHom.id (n + n)),
        liftedSplitVector_continuous n (n + n) n (OrthogonalMatrixHom.id (n + n))⟩
      ⟨liftedSplitVector n (n + n) n (OrthogonalIndex.blockSwap n n),
        liftedSplitVector_continuous n (n + n) n (OrthogonalIndex.blockSwap n n)⟩
      (liftedSplitVector_tendsto_coclosedCompact n (n + n) n
        (OrthogonalMatrixHom.id (n + n)))
      (liftedSplitVector_tendsto_coclosedCompact n (n + n) n (OrthogonalIndex.blockSwap n n))
      (liftedOnePointSplitHomotopy n) t x)

/-- Every original finite native sphere point has the entire moving complement/sphere formula. -/
theorem pointedSplitHomotopy_coe (n : ℕ) (t : unitInterval)
    (x : LiftedEuclidean.{v} (n + n)) :
    pointedSplitHomotopy.{u, v} n (t, (x : OnePoint (LiftedEuclidean.{v} (n + n)))) =
      (targetProductIso n (n + n)).hom.right
        (liftedUnitRotatingSplit n (ULift.up t, x) :
          OnePoint (LiftedBundle.{v} n (n + n) × LiftedEuclidean.{v} n)) :=
  pointedSplitHomotopy_apply n t (x : OnePoint (LiftedEuclidean.{v} (n + n)))

/-- The native based homotopy fixes the original source basepoint for the whole interval. -/
theorem pointedSplitHomotopy_infty (n : ℕ) (t : unitInterval) :
    pointedSplitHomotopy.{u, v} n (t, OnePoint.infty) =
      (thom.{u, v} n (n + n) ⊗ PointedCGWH.orthogonalSphere.{u, v} n).hom PUnit.unit := by
  exact (pointedSplitHomotopy_apply n t OnePoint.infty).trans
    ((congrArg (targetProductIso n (n + n)).hom.right
      (liftedOnePointSplitHomotopy_infty n t)).trans
        (PointedCGWH.mapOnePoint_infty (targetProductIso n (n + n)).hom))

/-- Both whole native frame maps are homotopic relative to the actual source basepoint image. -/
def pointedSplitHomotopyRel (n : ℕ) :
    ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) (pointedSplit.{u, v} n (n + n) n
        (OrthogonalMatrixHom.id (n + n))).right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) (pointedSplit.{u, v} n (n + n) n
        (OrthogonalIndex.blockSwap n n)).right)
      (Set.range (ConcreteCategory.hom (C := CGWH.{u, v})
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)).hom)) where
  toHomotopy := pointedSplitHomotopy n
  prop' := by
    intro t x hx
    obtain ⟨p, rfl⟩ := hx
    cases p
    exact (pointedSplitHomotopy_infty n t).trans
      (pointedSplit_infty n (n + n) n (OrthogonalMatrixHom.id (n + n))).symm

end CategoryTheory.Spectra.OrthogonalSmashGammaGeometry

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

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import MathlibExt.Algebra.Star.CuntzFamily.Finite

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Positive finite amplification from actual Hilbert coordinates

An actual Hilbert basis and a bijection Fin2×ι≃ι determine coordinate
isometries, both binary Cuntz laws and the computed positive finite family.
The countable coordinates of a Hilbert basis are genuine square-summable lp;
only the finite outer sum uses PiLp. The existing norms and metrics are reused.
No frame, totality, fold or desired output law is supplied by the caller.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProduct lp

namespace HilbertAmplification

universe u𝕜 uI uH

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {ι : Type uI} {H : Type uH}

/-- The actual singleton inclusion at an embedded coefficient index. -/
def coefficientFiber [DecidableEq ι] (f : ι ↪ ι) (j : ι) :
    𝕜 →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2 where
  __ := lp.lsingle (𝕜 := 𝕜) (E := fun _ : ι => 𝕜) 2 (f j)
  norm_map' z := lp.norm_single (E := fun _ : ι => 𝕜) (p := 2) (by norm_num) (f j) z

/-- Distinct embedded singleton coordinates are orthogonal. -/
theorem coefficientFiber_orthogonal [DecidableEq ι] (f : ι ↪ ι) :
    OrthogonalFamily 𝕜 (fun _ : ι => 𝕜) (coefficientFiber f) := by
  intro i j hij z w
  change inner 𝕜 (lp.single (E := fun _ : ι => 𝕜) 2 (f i) z)
    (lp.single (E := fun _ : ι => 𝕜) 2 (f j) w) = 0
  rw [lp.inner_single_left,
    lp.single_apply_ne (E := fun _ : ι => 𝕜) 2 (f j) w (f.injective.ne hij)]
  exact inner_zero_right _

/-- The native orthogonal sum of the embedded scalar coefficients. -/
def coefficientEmbedding [DecidableEq ι] (f : ι ↪ ι) :
    lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  (coefficientFiber_orthogonal f).linearIsometry

/-- A singleton coefficient has its literal embedded-coordinate value. -/
@[simp]
theorem coefficientEmbedding_single [DecidableEq ι] (f : ι ↪ ι) (j : ι) (z : 𝕜) :
    coefficientEmbedding f (lp.single (E := fun _ : ι => 𝕜) 2 j z) =
      lp.single (E := fun _ : ι => 𝕜) 2 (f j) z :=
  (coefficientFiber_orthogonal (𝕜 := 𝕜) f).linearIsometry_apply_single (i := j) z

variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Scalar singleton coefficients represent the corresponding scalar basis multiple. -/
private theorem repr_symm_single_smul [DecidableEq ι] (b : HilbertBasis ι 𝕜 H)
    (j : ι) (z : 𝕜) :
    b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 j z) = z • b j := by
  have h : lp.single (E := fun _ : ι => 𝕜) 2 j z =
      z • lp.single (E := fun _ : ι => 𝕜) 2 j (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ι => 𝕜) 2 j z (1 : 𝕜)
  rw [h, map_smul, b.repr_symm_single]

/-- The actual basis-coordinate inclusion associated to an index injection. -/
def coordinateEmbedding (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) :
    H →ₗᵢ[𝕜] H := by
  classical
  exact b.repr.symm.toLinearIsometry.comp
    ((coefficientEmbedding f).comp b.repr.toLinearIsometry)

/-- Coordinate inclusion sends each actual basis vector to the indexed vector. -/
@[simp]
theorem coordinateEmbedding_basis (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) (j : ι) :
    coordinateEmbedding b f (b j) = b (f j) := by
  classical
  change b.repr.symm (coefficientEmbedding f (b.repr (b j))) = b (f j)
  rw [b.repr_self, coefficientEmbedding_single, b.repr_symm_single]

/-- Basis transport preserves the literal singleton coefficients. -/
theorem coordinateEmbedding_repr_symm_single [DecidableEq ι]
    (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) (j : ι) (z : 𝕜) :
    coordinateEmbedding b f (b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 j z)) =
      b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 (f j) z) := by
  rw [repr_symm_single_smul, map_smul, coordinateEmbedding_basis,
    ← repr_symm_single_smul b (f j) z]

/-- With the identity basis the coordinate embedding is the native coefficient embedding. -/
theorem coordinateEmbedding_ofRepr_refl [DecidableEq ι] (f : ι ↪ ι) :
    coordinateEmbedding (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f =
      coefficientEmbedding f := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply lp.ext_continuousLinearMap (𝕜 := 𝕜) (E := fun _ : ι => 𝕜) (p := 2) (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro z
  exact (coordinateEmbedding_repr_symm_single
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f j z).trans
    (coefficientEmbedding_single f j z).symm

variable [CompleteSpace H]

/-- In basis coordinates the adjoint selects the original embedded coefficient. -/
theorem coordinateEmbedding_adjoint_repr (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι)
    (x : H) (j : ι) :
    b.repr ((coordinateEmbedding b f).toContinuousLinearMap.adjoint x) j =
      b.repr x (f j) := by
  rw [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_basis,
    ← b.repr_apply_apply]

/-- The coefficient adjoint extracts exactly the embedded coordinate. -/
theorem coefficientEmbedding_adjoint_apply [DecidableEq ι] (f : ι ↪ ι)
    (x : lp (fun _ : ι => 𝕜) 2) (j : ι) :
    ((coefficientEmbedding f).toContinuousLinearMap.adjoint x) j = x (f j) := by
  have h := coordinateEmbedding_adjoint_repr
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f x j
  rw [coordinateEmbedding_ofRepr_refl] at h
  exact h

/-- The coefficient adjoint returns a singleton from its embedded position. -/
@[simp]
theorem coefficientEmbedding_adjoint_single_image [DecidableEq ι] (f : ι ↪ ι)
    (j : ι) (z : 𝕜) :
    (coefficientEmbedding f).toContinuousLinearMap.adjoint
        (lp.single (E := fun _ : ι => 𝕜) 2 (f j) z) =
      lp.single (E := fun _ : ι => 𝕜) 2 j z := by
  ext k
  rw [coefficientEmbedding_adjoint_apply]
  simp only [lp.single_apply, Pi.single_apply, f.injective.eq_iff]

/-- The coefficient adjoint kills a singleton outside the embedded range. -/
theorem coefficientEmbedding_adjoint_single_off [DecidableEq ι] (f : ι ↪ ι)
    (k : ι) (z : 𝕜) (hk : ∀ j, f j ≠ k) :
    (coefficientEmbedding f).toContinuousLinearMap.adjoint
        (lp.single (E := fun _ : ι => 𝕜) 2 k z) = 0 := by
  ext j
  rw [coefficientEmbedding_adjoint_apply]
  simpa only [lp.coeFn_zero, Pi.zero_apply] using
    lp.single_apply_ne (E := fun _ : ι => 𝕜) 2 k z (hk j)

omit [CompleteSpace H] in
/-- The two coordinate inclusions determined by the actual index bijection. -/
def binaryEmbedding (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (i : Fin 2) : H →ₗᵢ[𝕜] H :=
  coordinateEmbedding b
    ⟨fun j => e (i, j), fun _j _k h => congrArg Prod.snd (e.injective h)⟩

omit [CompleteSpace H] in
/-- Literal basis action of the binary coordinate inclusions. -/
@[simp]
theorem binaryEmbedding_basis (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i : Fin 2) (j : ι) :
    binaryEmbedding b e i (b j) = b (e (i, j)) :=
  coordinateEmbedding_basis b _ j

omit [CompleteSpace H] in
private theorem basis_inner_ext (b : HilbertBasis ι 𝕜 H) {x y : H}
    (h : ∀ j, inner 𝕜 (b j) x = inner 𝕜 (b j) y) : x = y := by
  apply b.repr.injective
  ext j
  simpa only [b.repr_apply_apply] using h j

omit [CompleteSpace H] in
private theorem basis_map_ext (b : HilbertBasis ι 𝕜 H) {A B : H →L[𝕜] H}
    (h : ∀ j, A (b j) = B (b j)) : A = B := by
  have hd : Dense (Submodule.span 𝕜 (Set.range b) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  apply ContinuousLinearMap.ext_on hd
  rintro x ⟨j, rfl⟩
  exact h j

/-- The adjoint selects the corresponding binary coordinate and kills the other. -/
theorem binaryEmbedding_adjoint_basis (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i j : Fin 2) (m : ι) :
    (binaryEmbedding b e i).toContinuousLinearMap.adjoint (b (e (j, m))) =
      if i = j then b m else 0 := by
  classical
  apply basis_inner_ext b
  intro k
  rw [ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, binaryEmbedding_basis]
  rw [orthonormal_iff_ite.mp b.orthonormal]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, orthonormal_iff_ite.mp b.orthonormal]
    simp only [e.injective.eq_iff, Prod.mk.injEq, true_and]
  · rw [ite_eq_right hij, inner_zero_right]
    simp only [e.injective.eq_iff, Prod.mk.injEq, hij, false_and, ite_false]

omit [CompleteSpace H] in
/-- The literal binary operators, with no separately supplied frame data. -/
def binaryFamily (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι) :
    Fin 2 → (H →L[𝕜] H) :=
  fun i => (binaryEmbedding b e i).toContinuousLinearMap

/-- The actual binary operators have both diagonal and off-diagonal Gram laws. -/
theorem binaryFamily_orthogonal (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i j : Fin 2) :
    star (binaryFamily b e i) * binaryFamily b e j =
      if i = j then 1 else 0 := by
  classical
  apply basis_map_ext b
  intro m
  change (binaryEmbedding b e i).toContinuousLinearMap.adjoint
      (binaryEmbedding b e j (b m)) =
    (if i = j then (1 : H →L[𝕜] H) else 0) (b m)
  rw [binaryEmbedding_basis, binaryEmbedding_adjoint_basis]
  by_cases hij : i = j <;> simp [hij]

/-- The ranges of the two actual inclusions partition the whole Hilbert space. -/
theorem binaryFamily_partition (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) :
    binaryFamily b e 0 * star (binaryFamily b e 0) +
      binaryFamily b e 1 * star (binaryFamily b e 1) = 1 := by
  apply basis_map_ext b
  intro m
  obtain ⟨⟨j, k⟩, rfl⟩ := e.surjective m
  fin_cases j <;>
    simp [binaryFamily, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      binaryEmbedding_adjoint_basis, binaryEmbedding_basis]

/-- The existing constructive positive-family algorithm on the actual binary operators. -/
def finiteFamily (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (N : ℕ+) : Fin N → (H →L[𝕜] H) :=
  CuntzFamily.ofBinaryPositive (binaryFamily b e) N

/-- Both finite Cuntz laws follow from the computed binary coordinates. -/
theorem finiteFamily_relations (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    (∀ i j : Fin N,
      star (finiteFamily b e N i) * finiteFamily b e N j =
        if i = j then 1 else 0) ∧
    (∑ i : Fin N, finiteFamily b e N i * star (finiteFamily b e N i)) = 1 :=
  CuntzFamily.ofBinaryPositive_relations (binaryFamily b e)
    (binaryFamily_orthogonal b e) (binaryFamily_partition b e) N

/-- Each computed positive-family operator is a genuine bundled linear isometry. -/
def finiteEmbedding (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (N : ℕ+) (i : Fin N) : H →ₗᵢ[𝕜] H where
  toLinearMap := (finiteFamily b e N i).toLinearMap
  norm_map' := by
    have h : star (finiteFamily b e N i) * finiteFamily b e N i = 1 :=
      ((finiteFamily_relations b e N).1 i i).trans (ite_eq_left rfl)
    rw [ContinuousLinearMap.star_eq_adjoint] at h
    exact (finiteFamily b e N i).norm_map_iff_adjoint_comp_self.mpr h

/-- Bundling does not alter the actual finite operator action. -/
theorem finiteEmbedding_apply (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (i : Fin N) (x : H) :
    finiteEmbedding b e N i x = finiteFamily b e N i x :=
  rfl

/-- The computed finite embeddings are an orthogonal, total Hilbert sum. -/
theorem finiteFamily_isHilbertSum (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    IsHilbertSum 𝕜 (fun _ : Fin N => H) (finiteEmbedding b e N) := by
  classical
  refine IsHilbertSum.mk ?_ ?_
  · intro i j hij x y
    have hzero : star (finiteFamily b e N i) * finiteFamily b e N j = 0 := by
      simpa only [ite_eq_right hij] using (finiteFamily_relations b e N).1 i j
    change inner 𝕜 (finiteFamily b e N i x) (finiteFamily b e N j y) = 0
    calc
      _ = inner 𝕜 x
          ((finiteFamily b e N i).adjoint (finiteFamily b e N j y)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = 0 := by
        have h := congrArg (fun T : H →L[𝕜] H => T y) hzero
        change (finiteFamily b e N i).adjoint (finiteFamily b e N j y) = 0 at h
        rw [h, inner_zero_right]
  · intro x _
    apply (Submodule.le_topologicalClosure _)
    have h := congrArg (fun T : H →L[𝕜] H => T x) (finiteFamily_relations b e N).2
    have hsum : (∑ i : Fin N,
        finiteFamily b e N i (star (finiteFamily b e N i) x)) = x := by
      simpa only [_root_.sum_apply, mul_apply_eq_comp, one_apply_eq_self] using h
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mem_iSup_of_mem i
      ⟨star (finiteFamily b e N i) x, rfl⟩

/-- The actual positive finite Hilbert amplification, with the stock finite l² norm. -/
def finiteAmplification (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    PiLp 2 (fun _ : Fin N => H) ≃ₗᵢ[𝕜] H :=
  (lpPiLpₗᵢ (fun _ : Fin N => H) 𝕜 (p := 2)).symm.trans
    (finiteFamily_isHilbertSum b e N).linearIsometryEquiv.symm

/-- Amplification is the literal finite ordered sum of the computed operators. -/
theorem finiteAmplification_apply (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (x : PiLp 2 (fun _ : Fin N => H)) :
    finiteAmplification b e N x = ∑ i : Fin N, finiteFamily b e N i (x i) := by
  change (finiteFamily_isHilbertSum b e N).linearIsometryEquiv.symm
    ((lpPiLpₗᵢ (fun _ : Fin N => H) 𝕜 (p := 2)).symm x) = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply, tsum_fintype]
  rfl

end HilbertAmplification

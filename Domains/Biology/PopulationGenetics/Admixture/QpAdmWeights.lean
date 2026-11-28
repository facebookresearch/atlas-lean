/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.ADMIXTOOLS
public import Domains.Biology.PopulationGenetics.QpGraph
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Identifiability and least-squares form of qpAdm weights

In qpAdm form, an affine representation of a target frequency by source
frequencies gives the linear system `target = A *ᵥ w`, where `A` is the matrix
of `f4` statistics between non-reference sources and right populations. The
weights are unique iff `A` has full column rank; otherwise every solution lies
on a nontrivial line of solutions, so weights outside `[0, 1]` occur already
in one-edge drift models. Under full column rank the weights have the normal
equation form `w = (Aᵀ A)⁻¹ Aᵀ target`, and an exact solution maximizes the
unweighted qpGraph score.

## Main results

* `ADMIXTOOLS.qpAdmSourceMatrix`, `ADMIXTOOLS.qpAdmTargetVector`: the qpAdm
  linear system.
* `ADMIXTOOLS.qpAdmTargetVector_eq_qpAdmSourceMatrix_mulVec`: the model
  equation.
* `ADMIXTOOLS.qpAdm_unique_iff_rank_eq`,
  `ADMIXTOOLS.exists_line_of_rank_ne`: identifiability.
* `ADMIXTOOLS.qpAdm_weights_eq_inv_gram_mulVec`,
  `ADMIXTOOLS.qpAdm_weights_maximize_scoreS1_one`: least-squares form.

## References

* W. Haak et al., "Massive migration from the steppe was a source for
  Indo-European languages in Europe", *Nature* 522 (2015), 207–211 (qpAdm).
* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192
  (2012), 1065–1093.
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

variable {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}

/-- A real matrix has injective `mulVec` iff it has full column rank. -/
private theorem injective_mulVec_iff_rank_eq_card {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) : Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  rw [Matrix.mulVec_injective_iff, Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  exact eq_comm

variable (μ p) in
/-- The qpAdm source matrix: row `j`, column `l` is
`f4 (S (l+1)) (S 0) (R (j+1)) (R 0)`. An entry whose integrand is not integrable is `0`, by the
convention of `f4`. -/
noncomputable def qpAdmSourceMatrix {k r : ℕ} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) : Matrix (Fin r) (Fin k) ℝ :=
  Matrix.of fun j l => f4 μ p (S l.succ) (S 0) (R j.succ) (R 0)

variable (μ p) in
/-- The qpAdm target vector: entry `j` is `f4 T (S 0) (R (j+1)) (R 0)`. An entry whose integrand
is not integrable is `0`, by the convention of `f4`. -/
noncomputable def qpAdmTargetVector {k r : ℕ} (T : P) (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) : Fin r → ℝ :=
  fun j => f4 μ p T (S 0) (R j.succ) (R 0)

/-- The qpAdm model equation: for square-integrable frequencies, an affine frequency
representation `p T = ∑ l, w l * p (S l)` of the target (pointwise, weights of any sign with
`∑ l, w l = 1`) gives the linear system `target = sourceMatrix *ᵥ w` on the non-reference
weights. -/
theorem qpAdmTargetVector_eq_qpAdmSourceMatrix_mulVec
    (hp : ∀ X, MemLp (p X) 2 μ) {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) (w : Fin (k + 1) → ℝ) (hw : ∑ l, w l = 1)
    (hT : ∀ ω, p T ω = ∑ l, w l * p (S l) ω) :
    qpAdmTargetVector μ p T S R =
      qpAdmSourceMatrix μ p S R *ᵥ (fun l : Fin k => w l.succ) := by
  have hself : ∀ (A C D : P), f4 μ p A A C D = 0 := by
    intro A C D
    simp [f4]
  funext j
  have h := f4_affine_combination hp S w hw hT (X := S 0) (Y := R j.succ) (Z := R 0)
  simp only [qpAdmTargetVector, qpAdmSourceMatrix, Matrix.mulVec, Matrix.of_apply,
    dotProduct]
  rw [h, Fin.sum_univ_succ, hself, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Given a solution `w` of the qpAdm system `sourceMatrix *ᵥ w = target`, it is the only solution
iff the source matrix has full column rank `k`. -/
theorem qpAdm_unique_iff_rank_eq {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R) :
    (∀ v : Fin k → ℝ, qpAdmSourceMatrix μ p S R *ᵥ v = qpAdmTargetVector μ p T S R →
      v = w) ↔ (qpAdmSourceMatrix μ p S R).rank = k := by
  have hcard : (qpAdmSourceMatrix μ p S R).rank = k ↔
      Function.Injective (qpAdmSourceMatrix μ p S R).mulVec := by
    simpa only [Fintype.card_fin] using
      (injective_mulVec_iff_rank_eq_card (qpAdmSourceMatrix μ p S R)).symm
  rw [hcard]
  constructor
  · intro huniq x y hxy
    -- uniqueness applied to the solution translated by a kernel vector
    by_contra hne
    have hd : qpAdmSourceMatrix μ p S R *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hv : qpAdmSourceMatrix μ p S R *ᵥ (w + (x - y)) = qpAdmTargetVector μ p T S R := by
      rw [Matrix.mulVec_add, hd, hw, add_zero]
    have := huniq _ hv
    rw [add_eq_left] at this
    exact hne (sub_eq_zero.mp this)
  · intro hinj v hv
    exact hinj (hv.trans hw.symm)

/-- Without full column rank, a solution extends to a nontrivial line of solutions. -/
theorem exists_line_of_rank_ne {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R)
    (hrank : (qpAdmSourceMatrix μ p S R).rank ≠ k) :
    ∃ d : Fin k → ℝ, d ≠ 0 ∧ ∀ s : ℝ,
      qpAdmSourceMatrix μ p S R *ᵥ (w + s • d) = qpAdmTargetVector μ p T S R := by
  have hnotinj : ¬ Function.Injective (qpAdmSourceMatrix μ p S R).mulVec := by
    intro h
    apply hrank
    have h' := (injective_mulVec_iff_rank_eq_card _).mp h
    simpa only [Fintype.card_fin] using h'
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨x, y, hxy, hne⟩ := hnotinj
  refine ⟨x - y, fun h => hne (sub_eq_zero.mp h), fun s => ?_⟩
  have hd : qpAdmSourceMatrix μ p S R *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hd, smul_zero, hw, add_zero]

/-- Under full column rank, a solution `w` of the qpAdm system has the ordinary least-squares
(normal-equation) form `w = (Aᵀ A)⁻¹ Aᵀ target`, where `A` is the source matrix. -/
theorem qpAdm_weights_eq_inv_gram_mulVec {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R)
    (hrank : (qpAdmSourceMatrix μ p S R).rank = k) :
    w = ((qpAdmSourceMatrix μ p S R)ᵀ * qpAdmSourceMatrix μ p S R)⁻¹ *ᵥ
      ((qpAdmSourceMatrix μ p S R)ᵀ *ᵥ qpAdmTargetVector μ p T S R) := by
  set A := qpAdmSourceMatrix μ p S R with hA
  have hinj : Function.Injective A.mulVec := by
    have hrank' : A.rank = Fintype.card (Fin k) := by
      rw [Fintype.card_fin]; exact hrank
    exact (injective_mulVec_iff_rank_eq_card A).mpr hrank'
  have hgram : IsUnit (Aᵀ * A).det := by
    have h := QpGraph.isUnit_det_gram (Q := (1 : Matrix (Fin r) (Fin r) ℝ)) Matrix.PosDef.one hinj
    simpa using h
  have hnorm : (Aᵀ * A) *ᵥ w = Aᵀ *ᵥ qpAdmTargetVector μ p T S R := by
    rw [← Matrix.mulVec_mulVec, hw]
  calc w = (Aᵀ * A)⁻¹ *ᵥ ((Aᵀ * A) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hgram, Matrix.one_mulVec]
    _ = (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ qpAdmTargetVector μ p T S R) := by rw [hnorm]

/-- An exact solution `w` of the qpAdm system maximizes the unweighted qpGraph score `scoreS1` at
`Q = 1`: `scoreS1 1 target (A *ᵥ v) ≤ scoreS1 1 target (A *ᵥ w)` for every `v`, where `A` is the
source matrix. -/
theorem qpAdm_weights_maximize_scoreS1_one {k r : ℕ} {T : P} (S : Fin (k + 1) → P)
    (R : Fin (r + 1) → P) {w : Fin k → ℝ}
    (hw : qpAdmSourceMatrix μ p S R *ᵥ w = qpAdmTargetVector μ p T S R) (v : Fin k → ℝ) :
    QpGraph.scoreS1 1 (qpAdmTargetVector μ p T S R)
        (qpAdmSourceMatrix μ p S R *ᵥ v) ≤
      QpGraph.scoreS1 1 (qpAdmTargetVector μ p T S R)
        (qpAdmSourceMatrix μ p S R *ᵥ w) := by
  apply QpGraph.scoreS1_le_of_normal_eq Matrix.PosDef.one
  simp only [inv_one, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, hw]

end MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
public import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.Paving
public import MathlibExt.Algebra.Polynomial.RealRooted

import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.Barrier
import MathlibExt.Analysis.CStarAlgebra.KadisonSinger.RealStable
import MathlibExt.Algebra.Polynomial.Interlacing
import MathlibExt.Analysis.Matrix.Spectrum

/-!
# The finite Marcus--Spielman--Srivastava bound

This file assembles interlacing families, mixed characteristic polynomials, and the barrier
estimate for finitely supported independent random vectors.
-/

@[expose] public section

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

universe u

private noncomputable def ksOuter {d : Type*} (u : d → ℂ) : Matrix d d ℂ :=
  Matrix.vecMulVec u (star u)

private noncomputable def ksCovariance
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (i : Fin m) : Matrix d d ℂ :=
  ∑ a, p i a • ksOuter (v i a)

private noncomputable def ksPartialMatrix
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (k : ℕ)
    (ω : (i : Fin m) → Fin (s i)) (i : Fin m) : Matrix d d ℂ :=
  if i.val < k then ksOuter (v i (ω i)) else ksCovariance p v i

private lemma ksOuter_posSemidef {d : Type*} [Finite d] (u : d → ℂ) :
    (ksOuter u).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star u

private lemma ksCovariance_posSemidef
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ)
    (hp : ∀ i a, 0 ≤ p i a) (i : Fin m) : (ksCovariance p v i).PosSemidef := by
  unfold ksCovariance
  apply Matrix.posSemidef_sum Finset.univ
  intro a ha
  exact (ksOuter_posSemidef (v i a)).smul (hp i a)

private lemma ksPartialMatrix_posSemidef
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (hp : ∀ i a, 0 ≤ p i a)
    (k : ℕ) (ω : (i : Fin m) → Fin (s i)) (i : Fin m) :
    (ksPartialMatrix p v k ω i).PosSemidef := by
  rw [ksPartialMatrix]
  split_ifs
  · exact ksOuter_posSemidef _
  · exact ksCovariance_posSemidef p v hp i

private lemma ksCovariance_eq_sum_complex
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (i : Fin m) :
    ksCovariance p v i = ∑ a, (p i a : ℂ) • ksOuter (v i a) := by
  unfold ksCovariance
  apply Finset.sum_congr rfl
  intro a ha
  ext x y
  simp [Complex.real_smul]

private lemma ksPartialMatrix_succ_update
    {m : ℕ} {d : Type*} [Fintype d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) {k : ℕ} (hk : k < m)
    (ω : (i : Fin m) → Fin (s i)) (a : Fin (s ⟨k, hk⟩)) :
    ksPartialMatrix p v (k + 1) (Function.update ω ⟨k, hk⟩ a) =
      Function.update (ksPartialMatrix p v k ω) ⟨k, hk⟩ (ksOuter (v ⟨k, hk⟩ a)) := by
  funext j
  by_cases hji : j = ⟨k, hk⟩
  · subst j
    simp [ksPartialMatrix]
  · have hjk : j.val ≠ k := by
      intro hval
      apply hji
      apply Fin.ext
      simpa using hval
    by_cases hjlt : j.val < k
    · have hjsucc : j.val < k + 1 := lt_trans hjlt (Nat.lt_succ_self k)
      simp [ksPartialMatrix, hji, hjlt, hjsucc, Function.update_of_ne]
    · have hjnot : ¬j.val < k + 1 := by omega
      simp [ksPartialMatrix, hji, hjlt, hjnot, Function.update_of_ne]

private lemma ksMixedCharacteristicPolynomial_isMonicOfDegree
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) :
    Polynomial.IsMonicOfDegree (mixedCharacteristicPolynomial A) (Fintype.card d) :=
  ⟨mixedCharacteristicPolynomial_natDegree A, mixedCharacteristicPolynomial_monic A⟩

private lemma ksPartial_polynomial_eq_weighted_sum
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ)
    (hsum : ∀ i, ∑ a, p i a = 1) {k : ℕ} (hk : k < m)
    (ω : (i : Fin m) → Fin (s i)) :
    mixedCharacteristicPolynomial (ksPartialMatrix p v k ω) =
      ∑ a, (p ⟨k, hk⟩ a : ℂ) • mixedCharacteristicPolynomial
        (ksPartialMatrix p v (k + 1) (Function.update ω ⟨k, hk⟩ a)) := by
  let i : Fin m := ⟨k, hk⟩
  let B := ksPartialMatrix p v k ω
  have hchildren (a : Fin (s i)) :
      ksPartialMatrix p v (k + 1) (Function.update ω i a) =
        Function.update B i (ksOuter (v i a)) := by
    exact ksPartialMatrix_succ_update p v hk ω a
  have hparent : Function.update B i
      (∑ a, (p i a : ℂ) • ksOuter (v i a)) = B := by
    funext j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      change (∑ a, (p i a : ℂ) • ksOuter (v i a)) =
        ksPartialMatrix p v k ω i
      rw [ksPartialMatrix]
      simp only [i, lt_self_iff_false, ↓reduceIte]
      exact (ksCovariance_eq_sum_complex p v i).symm
    · rw [Function.update_of_ne hji]
  calc
    mixedCharacteristicPolynomial B =
        mixedCharacteristicPolynomial
          (Function.update B i (∑ a, (p i a : ℂ) • ksOuter (v i a))) := by
      rw [hparent]
    _ = ∑ a, (p i a : ℂ) •
        mixedCharacteristicPolynomial (Function.update B i (ksOuter (v i a))) :=
      mixedCharacteristicPolynomial_update_sum B i (p i) (fun a ↦ ksOuter (v i a))
        (hsum i)
    _ = ∑ a, (p i a : ℂ) • mixedCharacteristicPolynomial
        (ksPartialMatrix p v (k + 1) (Function.update ω i a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hchildren]

private lemma ksPartial_segment_isRealRooted
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] {s : Fin m → ℕ}
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ) (hp : ∀ i a, 0 ≤ p i a)
    {k : ℕ} (hk : k < m) (ω : (i : Fin m) → Fin (s i))
    (a : Fin (s ⟨k, hk⟩)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - (t : ℂ)) • mixedCharacteristicPolynomial (ksPartialMatrix p v k ω) +
      (t : ℂ) • mixedCharacteristicPolynomial
        (ksPartialMatrix p v (k + 1) (Function.update ω ⟨k, hk⟩ a))).IsRealRooted := by
  let i : Fin m := ⟨k, hk⟩
  let B := ksPartialMatrix p v k ω
  have hchild : ksPartialMatrix p v (k + 1) (Function.update ω i a) =
      Function.update B i (ksOuter (v i a)) :=
    ksPartialMatrix_succ_update p v hk ω a
  have hparent : Function.update B i (ksCovariance p v i) = B := by
    funext j
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      simp [B, ksPartialMatrix, i]
    · rw [Function.update_of_ne hji]
  change ((1 - (t : ℂ)) • mixedCharacteristicPolynomial B +
    (t : ℂ) • mixedCharacteristicPolynomial
      (ksPartialMatrix p v (k + 1) (Function.update ω i a))).IsRealRooted
  rw [hchild]
  have haffine := mixedCharacteristicPolynomial_update_affine B i
    (ksCovariance p v i) (ksOuter (v i a)) t
  rw [hparent] at haffine
  rw [← haffine]
  apply mixedCharacteristicPolynomial_isRealRooted_of_posSemidef
  intro j
  by_cases hji : j = i
  · subst j
    rw [Function.update_self]
    have hleft := (ksCovariance_posSemidef p v hp i).smul (sub_nonneg.mpr ht.2)
    have hright := (ksOuter_posSemidef (v i a)).smul ht.1
    rw [show (1 - (t : ℂ)) • ksCovariance p v i + (t : ℂ) • ksOuter (v i a) =
        (1 - t) • ksCovariance p v i + t • ksOuter (v i a) by
      ext x y
      simp [Complex.real_smul]]
    exact hleft.add hright
  · rw [Function.update_of_ne hji]
    exact ksPartialMatrix_posSemidef p v hp k ω j

private lemma ksExists_partial_succ_maxRealRoot_le
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {s : Fin m → ℕ} (hs : ∀ i, 0 < s i)
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ)
    (hp : ∀ i a, 0 ≤ p i a) (hsum : ∀ i, ∑ a, p i a = 1)
    {k : ℕ} (hk : k < m) (ω : (i : Fin m) → Fin (s i)) :
    ∃ a : Fin (s ⟨k, hk⟩),
      (mixedCharacteristicPolynomial
        (ksPartialMatrix p v (k + 1) (Function.update ω ⟨k, hk⟩ a))).maxRealRoot ≤
      (mixedCharacteristicPolynomial (ksPartialMatrix p v k ω)).maxRealRoot := by
  let i : Fin m := ⟨k, hk⟩
  let P : Fin (s i) → Polynomial ℂ := fun a ↦ mixedCharacteristicPolynomial
    (ksPartialMatrix p v (k + 1) (Function.update ω i a))
  let hne : Nonempty (Fin (s i)) := ⟨⟨0, hs i⟩⟩
  have hsumPoly : mixedCharacteristicPolynomial (ksPartialMatrix p v k ω) =
      ∑ a, (p i a : ℂ) • P a := by
    exact ksPartial_polynomial_eq_weighted_sum p v hsum hk ω
  change ∃ a, (P a).maxRealRoot ≤
    (mixedCharacteristicPolynomial (ksPartialMatrix p v k ω)).maxRealRoot
  rw [hsumPoly]
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_segment_realRooted
    hne (w := p i) (P := P) (n := Fintype.card d) Fintype.card_pos
  · exact hp i
  · intro a
    exact ksMixedCharacteristicPolynomial_isMonicOfDegree _
  · rw [← hsumPoly]
    exact ksMixedCharacteristicPolynomial_isMonicOfDegree _
  · intro a t ht
    rw [← hsumPoly]
    exact ksPartial_segment_isRealRooted p v hp hk ω a t ht

private lemma ksExists_partial_maxRealRoot_le
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {s : Fin m → ℕ} (hs : ∀ i, 0 < s i)
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ)
    (hp : ∀ i a, 0 ≤ p i a) (hsum : ∀ i, ∑ a, p i a = 1)
    (k : ℕ) (hk : k ≤ m) :
    ∃ ω : (i : Fin m) → Fin (s i),
      (mixedCharacteristicPolynomial (ksPartialMatrix p v k ω)).maxRealRoot ≤
        (mixedCharacteristicPolynomial (ksCovariance p v)).maxRealRoot := by
  induction k with
  | zero =>
      let ω : (i : Fin m) → Fin (s i) := fun i ↦ ⟨0, hs i⟩
      refine ⟨ω, ?_⟩
      have hmatrix : ksPartialMatrix p v 0 ω = ksCovariance p v := by
        funext i
        simp [ksPartialMatrix]
      rw [hmatrix]
  | succ k ih =>
      have hklt : k < m := by omega
      obtain ⟨ω, hω⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨a, ha⟩ := ksExists_partial_succ_maxRealRoot_le hs p v hp hsum hklt ω
      refine ⟨Function.update ω ⟨k, hklt⟩ a, ha.trans hω⟩

private lemma ksTrace_real_smul_outer {d : Type*} [Fintype d]
    (p : ℝ) (v : d → ℂ) :
    (Matrix.trace (p • Matrix.vecMulVec v (star v))).re =
      p * ∑ k, ‖v k‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, Complex.real_smul, Complex.re_sum,
    Complex.mul_re, Complex.sq_norm, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, zero_mul, sub_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- **An outcome bounded by the mixed characteristic polynomial.** Let $d$ be a nonempty finite
index set. For $i = 1, \dots, m$ let $s_i \ge 1$, let $v_{i,1}, \dots, v_{i,s_i} \in \mathbb{C}^d$,
let $p_{i,1}, \dots, p_{i,s_i} \ge 0$ be reals with $\sum_a p_{i,a} = 1$, and put
$A_i = \sum_a p_{i,a} v_{i,a} v_{i,a}^*$. Then there is a choice of indices
$\omega_i \in \{1, \dots, s_i\}$, one for each $i$, such that the largest real part of a root of
the characteristic polynomial of $\sum_i v_{i,\omega_i} v_{i,\omega_i}^*$ is at most the largest
real part of a root of the mixed characteristic polynomial of $A_1, \dots, A_m$. -/
public theorem exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {s : Fin m → ℕ} (hs : ∀ i, 0 < s i)
    (p : (i : Fin m) → Fin (s i) → ℝ)
    (v : (i : Fin m) → Fin (s i) → d → ℂ)
    (hp : ∀ i a, 0 ≤ p i a) (hsum : ∀ i, ∑ a, p i a = 1) :
    ∃ ω : (i : Fin m) → Fin (s i),
      (Matrix.charpoly
        (∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i))))).maxRealRoot ≤
      (mixedCharacteristicPolynomial (fun i ↦
        ∑ a, p i a • Matrix.vecMulVec (v i a) (star (v i a)))).maxRealRoot := by
  obtain ⟨ω, hω⟩ := ksExists_partial_maxRealRoot_le hs p v hp hsum m le_rfl
  change (mixedCharacteristicPolynomial (ksPartialMatrix p v m ω)).maxRealRoot ≤
    (mixedCharacteristicPolynomial (fun i ↦
      ∑ a, p i a • Matrix.vecMulVec (v i a) (star (v i a)))).maxRealRoot at hω
  have hend : ksPartialMatrix p v m ω = fun i ↦ ksOuter (v i (ω i)) := by
    funext i
    simp [ksPartialMatrix, i.isLt]
  rw [hend] at hω
  have hcharpoly : mixedCharacteristicPolynomial (fun i ↦ ksOuter (v i (ω i))) =
      Matrix.charpoly (∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i)))) := by
    apply mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec
      (fun i ↦ ksOuter (v i (ω i))) (fun i ↦ v i (ω i)) (fun i ↦ star (v i (ω i)))
    intro i
    rfl
  refine ⟨ω, ?_⟩
  rwa [hcharpoly] at hω

/-- **Marcus--Spielman--Srivastava bound, finite-support form.** Let $d$ be a finite index set
and, for $i = 1, \dots, m$, let $s_i \ge 1$, let $v_{i,1}, \dots, v_{i,s_i} \in \mathbb{C}^d$, and
let $p_{i,1}, \dots, p_{i,s_i} \ge 0$ be reals with $\sum_a p_{i,a} = 1$. Let $\eta \ge 0$ be a real
number, and suppose that $\sum_i \sum_a p_{i,a} v_{i,a} v_{i,a}^* = I$ and
$\sum_a p_{i,a} \|v_{i,a}\|^2 \le \eta$ for every $i$, where $\|\cdot\|$ is the Euclidean norm.
Then there is a choice of indices $\omega_i \in \{1, \dots, s_i\}$, one for each $i$, such that
the operator norm of $\sum_i v_{i,\omega_i} v_{i,\omega_i}^*$ with respect to the Euclidean norm
on $\mathbb{C}^d$ is at most $(1 + \sqrt{\eta})^2$. -/
public theorem finiteMSSBound : FiniteMSSBound.{u} := by
  intro m d hdft hddec s hs p v η hη hp hpsum hframe htrace
  cases isEmpty_or_nonempty d with
  | inl hdempty =>
      let ω : (i : Fin m) → Fin (s i) := fun i ↦ ⟨0, hs i⟩
      refine ⟨ω, ?_⟩
      have hzero :
          (∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i))) : Matrix d d ℂ) = 0 :=
        Subsingleton.elim _ _
      rw [hzero, norm_zero]
      positivity
  | inr hdnonempty =>
      let A : Fin m → Matrix d d ℂ := fun i ↦
        ∑ a, p i a • Matrix.vecMulVec (v i a) (star (v i a))
      have hA (i : Fin m) : (A i).PosSemidef := by
        dsimp only [A]
        apply Matrix.posSemidef_sum Finset.univ
        intro a ha
        exact (Matrix.posSemidef_vecMulVec_self_star (v i a)).smul (hp i a)
      have hAsum : ∑ i, A i = 1 := by
        rw [← hframe]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [A]
        apply Finset.sum_congr rfl
        intro a ha
        ext x y
        simp [Complex.real_smul]
      have hAtrace (i : Fin m) : (Matrix.trace (A i)).re ≤ η := by
        calc
          (Matrix.trace (A i)).re =
              ∑ a, p i a * ∑ k, ‖v i a k‖ ^ 2 := by
            dsimp only [A]
            rw [Matrix.trace_sum, Complex.re_sum]
            apply Finset.sum_congr rfl
            intro a ha
            exact ksTrace_real_smul_outer (p i a) (v i a)
          _ ≤ η := htrace i
      obtain ⟨ω, hω⟩ :=
        exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial hs p v hp hpsum
      refine ⟨ω, ?_⟩
      let M : Matrix d d ℂ :=
        ∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i)))
      have hM : M.PosSemidef := by
        dsimp only [M]
        apply Matrix.posSemidef_sum Finset.univ
        intro i hi
        exact Matrix.posSemidef_vecMulVec_self_star _
      calc
        ‖M‖ = M.charpoly.maxRealRoot := hM.l2_opNorm_eq_maxRealRoot_charpoly
        _ ≤ (mixedCharacteristicPolynomial A).maxRealRoot := by
          change (Matrix.charpoly
            (∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i))))).maxRealRoot ≤
              (mixedCharacteristicPolynomial (fun i ↦
                ∑ a, p i a • Matrix.vecMulVec (v i a) (star (v i a)))).maxRealRoot
          exact hω
        _ ≤ (1 + Real.sqrt η) ^ 2 := by
          exact mixedCharacteristicPolynomial_maxRealRoot_le A η hη hA hAsum hAtrace

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

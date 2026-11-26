/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order

/-!
# Epsilon-light vertex subsets

Let `G` be a simple graph on a finite vertex set, with real Laplacian matrix `L`. A set `S` of
vertices is `ε`-light (`IsEpsilonLight`) if `ε L - L_S` is positive semidefinite, where `L_S` is
the Laplacian matrix of the graph on all the vertices whose edges are the edges of `G` with both
endpoints in `S`.

The main result, `epsilonLightSubsetExists_holds`, proves `epsilonLightSubsetExists`: there is a
constant `c > 0` such that for every graph on `n` vertices and every `0 < ε < 1`, some `ε`-light
set has at least `c ε n` vertices. This is Lemma B.1 of Appendix B.6 (by D. Spielman) of the
First Proof paper, proved there for weighted graphs with `c = 1/42`; we take `c = 1/100`.

## Proof outline

The proof follows the barrier argument of the source, which adapts the upper barrier function of
Batson, Spielman and Srivastava. With `k = ⌊ε n / 50⌋ ≥ 1` (a single vertex suffices when
`ε n < 50`), the vertices of `S` are chosen one at a time.

* **Normalization.** For `η > 0`, conjugating by `W = (L + η)^{-1/2}` turns the Laplacian of
  the edges inside `S` into a matrix `A_S` with `A_V ⪯ 1`, and `L_S ⪯ ε (L + η)` becomes
  `A_S ⪯ ε`. The leverage of the edges leaving `S` is the trace of the image of their Laplacian.
  Since there are finitely many vertex sets, a set that works for arbitrarily small `η` is
  `ε`-light. This replaces the pseudo-inverse of `L` used in the source.
* **Potential.** The source sums `1 / (u - λ)` over the `k` largest eigenvalues `λ` of `A_S`. As
  `A_S` has rank at most `|S| ≤ k`, this equals `tr (u - A_S)⁻¹ - (n - k) / u`, which we use
  instead, so that every estimate reduces to a sum over the eigenvalues of `A_S`.
* **Barrier step** (Lemma B.7 of the source). If `M ≻ 0`, `B ⪰ 0` and `τ = tr (M⁻¹ B) < 1`, then
  `M - B ≻ 0` and `tr (M - B)⁻¹ ≤ tr M⁻¹ + tr (M⁻² B) / (1 - τ)`. We prove it with the square
  root of `M` rather than the Sherman-Morrison-Woodbury formula.
* **Greedy step** (Lemmas B.3, B.4 and B.8 of the source). Averaging over the vertices outside
  `S` gives a vertex `t` that keeps the potential below `2k / ε` when the barrier moves from `u`
  to `u + ε / (2k)`, and adds leverage at most `4`.
* **Induction.** Starting from the empty set and the barrier `ε / 2` (the source starts from a
  single vertex), `k` steps give `|S| = k` and `A_S ≺ ε`.

We use Mathlib's continuous functional calculus for Hermitian matrices. In an eigenbasis of
`A`, the trace of `f(A) B` is a sum of the eigenvalues of `f(A)` weighted by the corresponding
diagonal entries of `B`.

## References

* First Proof authors, *First Proof*, arXiv:2602.05192v2, Appendix B.6 (D. Spielman, *Light Sets
  of Vertices*), Lemma B.1 and its proof, Lemmas B.3-B.8 and Claims B.2-B.10.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.EpsilonLightSubsetWanted

open SimpleGraph

open Matrix

section Definitions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **ε-light vertex sets.** Let $G$ be a simple graph on a finite vertex set $V$, let
$\varepsilon$ be a real number and let $S \subseteq V$. Let $L$ be the real Laplacian matrix of
$G$ and $L_S$ the real Laplacian matrix of the graph on $V$ whose edges are the edges of $G$ with
both endpoints in $S$. The set $S$ is $\varepsilon$-light in $G$ if $\varepsilon L - L_S$ is
positive semidefinite. -/
def IsEpsilonLight (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  open Classical in
  letI G_S := G.induce S |>.spanningCoe
  letI L := lapMatrix ℝ G
  letI L_S := lapMatrix ℝ (G_S)
  PosSemidef (ε • L - L_S)

/-- **The large ε-light subset property.** The statement that there is a real constant $c > 0$
such that for every natural number $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ and every real number $\varepsilon$ with $0 < \varepsilon < 1$, some set $S$
of vertices that is $\varepsilon$-light in $G$ has at least $c \varepsilon n$ elements. -/
def epsilonLightSubsetExists : Prop :=
  ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℝ),
  0 < ε → ε < 1 →
  ∃ (S : Finset (Fin n)), IsEpsilonLight G ε S ∧ (S.card : ℝ) ≥ c * ε * n

end Definitions

section FunctionalCalculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The orthogonal matrix of eigenvectors of a symmetric real matrix. -/
private noncomputable def eU (hA : A.IsHermitian) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ)

private lemma eU_transpose_mul (hA : A.IsHermitian) : (eU hA)ᵀ * eU hA = 1 := by
  have h := mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

private lemma fc_congr (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) : hA.cfc f = hA.cfc g := by
  rw [← hA.cfc_eq, ← hA.cfc_eq]
  apply cfc_congr
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact fun _ ⟨i, hi⟩ => hi ▸ h i

private lemma fc_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun x => f x * g x) := by
  simpa only [hA.cfc_eq] using (cfc_mul f g A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)).symm

private lemma fc_const (hA : A.IsHermitian) (c : ℝ) : hA.cfc (fun _ => c) = c • 1 := by
  rw [← hA.cfc_eq, cfc_const c A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

private lemma fc_id (hA : A.IsHermitian) : hA.cfc (fun x => x) = A :=
  (hA.cfc_eq _).symm.trans (cfc_id' ℝ A hA.isSelfAdjoint)

private lemma fc_sub (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc (fun x => f x - g x) = hA.cfc f - hA.cfc g := by
  simpa only [hA.cfc_eq] using cfc_sub f g A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)

private lemma fc_add (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc (fun x => f x + g x) = hA.cfc f + hA.cfc g := by
  simpa only [hA.cfc_eq] using cfc_add A f g (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)

private lemma fc_smul (hA : A.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    hA.cfc (fun x => c * f x) = c • hA.cfc f := by
  simpa only [hA.cfc_eq] using cfc_const_mul c f A (A.finite_real_spectrum.continuousOn _)

private lemma fc_isHermitian (hA : A.IsHermitian) (f : ℝ → ℝ) : (hA.cfc f).IsHermitian := by
  rw [← hA.cfc_eq]
  exact cfc_predicate f A

private lemma fc_transpose (hA : A.IsHermitian) (f : ℝ → ℝ) : (hA.cfc f)ᵀ = hA.cfc f := by
  simpa only [← conjTranspose_eq_transpose_of_trivial] using (fc_isHermitian hA f).eq

open scoped MatrixOrder in
private lemma fc_posSemidef (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (hA.cfc f).PosSemidef := by
  rw [← hA.cfc_eq, ← nonneg_iff_posSemidef]
  apply cfc_nonneg
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact fun _ ⟨i, hi⟩ => hi ▸ hf i

private lemma fc_inv (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) * g (hA.eigenvalues i) = 1) : (hA.cfc f)⁻¹ = hA.cfc g := by
  apply inv_eq_right_inv
  rw [fc_mul, fc_congr hA (g := fun _ => 1) h, fc_const, one_smul]

/-- The diagonal entries of a matrix in the eigenbasis. -/
private noncomputable def dg (hA : A.IsHermitian) (B : Matrix ι ι ℝ) (i : ι) : ℝ :=
  ((eU hA)ᵀ * B * eU hA) i i

private lemma dg_one (hA : A.IsHermitian) (i : ι) : dg hA 1 i = 1 := by
  simp [dg, eU_transpose_mul]

private lemma dg_nonneg (hA : A.IsHermitian) {B : Matrix ι ι ℝ} (hB : B.PosSemidef) (i : ι) :
    0 ≤ dg hA B i := by
  simpa only [dg, ← conjTranspose_eq_transpose_of_trivial] using
    (hB.conjTranspose_mul_mul_same (eU hA)).diag_nonneg (i := i)

private lemma dg_sub (hA : A.IsHermitian) (B C : Matrix ι ι ℝ) (i : ι) :
    dg hA (B - C) i = dg hA B i - dg hA C i := by
  simp [dg, Matrix.mul_sub, Matrix.sub_mul]

private lemma dg_le_of_posSemidef_sub (hA : A.IsHermitian) {B C : Matrix ι ι ℝ}
    (h : (C - B).PosSemidef) (i : ι) : dg hA B i ≤ dg hA C i := by
  have := dg_nonneg hA h i
  rw [dg_sub] at this
  linarith

private lemma trace_fc_mul (hA : A.IsHermitian) (f : ℝ → ℝ) (B : Matrix ι ι ℝ) :
    (hA.cfc f * B).trace = ∑ i, f (hA.eigenvalues i) * dg hA B i := by
  change (eU hA * diagonal (fun i => f (hA.eigenvalues i)) * (eU hA)ᵀ * B).trace = _
  unfold dg
  rw [show eU hA * diagonal (fun i => f (hA.eigenvalues i)) * (eU hA)ᵀ * B =
      eU hA * (diagonal (fun i => f (hA.eigenvalues i)) * ((eU hA)ᵀ * B)) by
    simp only [Matrix.mul_assoc], trace_mul_comm, Matrix.mul_assoc]
  simp only [trace, diag_apply, diagonal_mul, Matrix.mul_assoc]

private lemma trace_fc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).trace = ∑ i, f (hA.eigenvalues i) := by
  have := trace_fc_mul hA f 1
  simpa [dg_one] using this

open scoped MatrixOrder

private lemma fc_posDef (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 < f (hA.eigenvalues i)) : (hA.cfc f).PosDef := by
  rw [← hA.cfc_eq, ← isStrictlyPositive_iff_posDef,
    cfc_isStrictlyPositive_iff f A (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint,
    hA.spectrum_real_eq_range_eigenvalues]
  exact fun _ ⟨i, hi⟩ => hi ▸ hf i

private lemma eigenvalues_lt_of_posDef (hA : A.IsHermitian) {c : ℝ} (h : (c • 1 - A).PosDef)
    (i : ι) : hA.eigenvalues i < c := by
  have hpos : (hA.cfc (fun x => c - x)).PosDef := by rwa [fc_sub, fc_const, fc_id]
  rw [← hA.cfc_eq, ← isStrictlyPositive_iff_posDef,
    cfc_isStrictlyPositive_iff _ A (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint] at hpos
  exact sub_pos.mp (hpos _ (hA.eigenvalues_mem_spectrum_real i))

private lemma eigenvalues_le_of_posSemidef (hA : A.IsHermitian) {c : ℝ}
    (h : (c • 1 - A).PosSemidef) (i : ι) : hA.eigenvalues i ≤ c := by
  have hnonneg : (hA.cfc (fun x => c - x)).PosSemidef := by rwa [fc_sub, fc_const, fc_id]
  rw [← hA.cfc_eq, ← nonneg_iff_posSemidef,
    cfc_nonneg_iff _ A (A.finite_real_spectrum.continuousOn _) hA.isSelfAdjoint] at hnonneg
  exact sub_nonneg.mp (hnonneg _ (hA.eigenvalues_mem_spectrum_real i))

end FunctionalCalculus

section BarrierStep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma trace_le_trace_of_posSemidef_sub {X Y : Matrix ι ι ℝ} (h : (Y - X).PosSemidef) :
    X.trace ≤ Y.trace := by
  have := h.trace_nonneg
  rw [trace_sub] at this
  linarith

/-- **Barrier step.** If `M` is positive definite, `B` is positive semidefinite and
`τ = tr (M⁻¹ B) < 1`, then `M - B` is positive definite and
`tr (M - B)⁻¹ ≤ tr M⁻¹ + tr (M⁻² B) / (1 - τ)`. -/
private lemma barrier_step {M B : Matrix ι ι ℝ} (hM : M.PosDef) (hB : B.PosSemidef)
    (hτ : (M⁻¹ * B).trace < 1) :
    (M - B).PosDef ∧
      (M - B)⁻¹.trace ≤ M⁻¹.trace + (M⁻¹ * M⁻¹ * B).trace / (1 - (M⁻¹ * B).trace) := by
  set τ := (M⁻¹ * B).trace with hτdef
  have hMh : M.IsHermitian := hM.isHermitian
  have hpos : ∀ i, 0 < hMh.eigenvalues i := fun i => hM.eigenvalues_pos i
  set R := hMh.cfc (fun x => Real.sqrt x) with hRdef
  set Ri := hMh.cfc (fun x => (Real.sqrt x)⁻¹) with hRidef
  have hsq : ∀ i, Real.sqrt (hMh.eigenvalues i) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (hpos i)).ne'
  have hRRi : R * Ri = 1 := by
    rw [hRdef, hRidef, fc_mul, fc_congr hMh (g := fun _ => 1) (fun i => mul_inv_cancel₀ (hsq i)),
      fc_const, one_smul]
  have hRiR : Ri * R = 1 := by
    rw [hRdef, hRidef, fc_mul, fc_congr hMh (g := fun _ => 1) (fun i => inv_mul_cancel₀ (hsq i)),
      fc_const, one_smul]
  have hRR : R * R = M := by
    rw [hRdef, fc_mul, fc_congr hMh (g := fun x => x)
      (fun i => Real.mul_self_sqrt (hpos i).le), fc_id]
  have hMinv : M⁻¹ = hMh.cfc (fun x => x⁻¹) := by
    conv_lhs => rw [← fc_id hMh]
    exact fc_inv hMh (fun i => mul_inv_cancel₀ (hpos i).ne')
  have hRiRi : Ri * Ri = M⁻¹ := by
    rw [hRidef, fc_mul, hMinv]
    refine fc_congr hMh fun i => ?_
    rw [← mul_inv, Real.mul_self_sqrt (hpos i).le]
  have hRt : Rᵀ = R := fc_transpose hMh _
  have hRit : Riᵀ = Ri := fc_transpose hMh _
  set X := Ri * B * Ri with hXdef
  have hX : X.PosSemidef := by
    have := hB.mul_mul_conjTranspose_same Ri
    rwa [conjTranspose_eq_transpose_of_trivial, hRit] at this
  have hXh : X.IsHermitian := hX.isHermitian
  have htrX : X.trace = τ := by
    rw [hXdef, hτdef, ← hRiRi, trace_mul_comm, ← Matrix.mul_assoc]
  have hev0 : ∀ i, 0 ≤ hXh.eigenvalues i := fun i => hX.eigenvalues_nonneg i
  have hevτ : ∀ i, hXh.eigenvalues i ≤ τ := by
    intro i
    have htr : X.trace = ∑ j, hXh.eigenvalues j := by
      conv_lhs => rw [← fc_id hXh]
      rw [trace_fc]
    rw [← htrX, htr]
    exact Finset.single_le_sum (fun j _ => hev0 j) (Finset.mem_univ i)
  have h1τ : 0 < 1 - τ := by linarith
  have h1X : 1 - X = hXh.cfc (fun x => 1 - x) := by
    rw [fc_sub, fc_const, fc_id, one_smul]
  have h1Xpd : (1 - X).PosDef := by
    rw [h1X]
    exact fc_posDef hXh fun i => by linarith [hevτ i]
  have hMB : M - B = R * (1 - X) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRR, hXdef]
    congr 1
    calc B = (R * Ri) * B * (Ri * R) := by rw [hRRi, hRiR, Matrix.one_mul, Matrix.mul_one]
      _ = R * (Ri * B * Ri) * R := by simp only [Matrix.mul_assoc]
  have hRinj : Function.Injective R.mulVec := by
    intro x y hxy
    have := congrArg (fun z => Ri *ᵥ z) hxy
    simpa [mulVec_mulVec, hRiR] using this
  refine ⟨?_, ?_⟩
  · rw [hMB]
    have := h1Xpd.conjTranspose_mul_mul_same hRinj
    rwa [conjTranspose_eq_transpose_of_trivial, hRt] at this
  · -- the inverse of `M - B`
    have hinv1X : (1 - X)⁻¹ = hXh.cfc (fun x => (1 - x)⁻¹) := by
      rw [h1X]
      exact fc_inv hXh fun i => mul_inv_cancel₀ (by linarith [hevτ i])
    have hMBinv : (M - B)⁻¹ = Ri * (1 - X)⁻¹ * Ri := by
      apply inv_eq_right_inv
      rw [hMB]
      have hu : (1 - X) * (1 - X)⁻¹ = 1 := by
        rw [hinv1X, h1X, fc_mul,
          fc_congr hXh (g := fun _ => 1) (fun i => mul_inv_cancel₀ (by linarith [hevτ i])),
          fc_const, one_smul]
      calc R * (1 - X) * R * (Ri * (1 - X)⁻¹ * Ri)
          = R * (1 - X) * (R * Ri) * (1 - X)⁻¹ * Ri := by simp only [Matrix.mul_assoc]
        _ = R * ((1 - X) * (1 - X)⁻¹) * Ri := by
          rw [hRRi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hu, Matrix.mul_one, hRRi]
    -- `(1 - X)⁻¹ ≤ 1 + (1 - τ)⁻¹ X`
    have hle : (1 + (1 - τ)⁻¹ • X - (1 - X)⁻¹).PosSemidef := by
      rw [hinv1X]
      have : 1 + (1 - τ)⁻¹ • X - hXh.cfc (fun x => (1 - x)⁻¹) =
          hXh.cfc (fun x => 1 + (1 - τ)⁻¹ * x - (1 - x)⁻¹) := by
        rw [fc_sub, fc_add, fc_smul, fc_const, fc_id, one_smul]
      rw [this]
      refine fc_posSemidef hXh fun i => ?_
      have h0 := hev0 i
      have h1 := hevτ i
      have hx : 0 < 1 - hXh.eigenvalues i := by linarith
      rw [sub_nonneg, inv_eq_one_div, div_le_iff₀ hx]
      have key : 1 ≤ (1 - τ)⁻¹ * (1 - hXh.eigenvalues i) := by
        rw [inv_mul_eq_div, le_div_iff₀ h1τ]; linarith
      nlinarith [mul_le_mul_of_nonneg_left key h0]
    have hle' : (Ri * (1 + (1 - τ)⁻¹ • X) * Ri - Ri * (1 - X)⁻¹ * Ri).PosSemidef := by
      have := hle.mul_mul_conjTranspose_same Ri
      rw [conjTranspose_eq_transpose_of_trivial, hRit] at this
      simpa only [Matrix.mul_sub, Matrix.sub_mul] using this
    have htr := trace_le_trace_of_posSemidef_sub hle'
    rw [← hMBinv] at htr
    refine htr.trans (le_of_eq ?_)
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRiRi, trace_add, Matrix.mul_smul,
      Matrix.smul_mul, trace_smul, smul_eq_mul, div_eq_inv_mul]
    congr 2
    rw [hXdef, show Ri * (Ri * B * Ri) * Ri = (Ri * Ri) * B * (Ri * Ri) by
      simp only [Matrix.mul_assoc], hRiRi, trace_mul_comm, Matrix.mul_assoc]

end BarrierStep

section Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma inv_sub_inv_sub_eq (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    a⁻¹ - (a + δ)⁻¹ - δ * ((a + δ)⁻¹ * (a + δ)⁻¹) = δ ^ 2 / (a * (a + δ) ^ 2) := by
  have : 0 < a + δ := by linarith
  field_simp
  ring

omit [DecidableEq ι] in
/-- If at most `k` of the numbers `lam i` are nonzero, `g ≥ 0`, and `g i = c` whenever
`lam i = 0`, then `(card ι - k) * c ≤ ∑ i, g i`. -/
private lemma sub_mul_le_sum {lam : ι → ℝ} {k : ℕ}
    (hk : (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ k)
    {g : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ i, 0 ≤ g i) (hg0 : ∀ i, lam i = 0 → g i = c) :
    ((Fintype.card ι : ℝ) - k) * c ≤ ∑ i, g i := by
  set Z := Finset.univ.filter (fun i => ¬ lam i ≠ 0) with hZdef
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => lam i ≠ 0)
  have hZ : ((Fintype.card ι : ℝ) - k) ≤ Z.card := by
    have h1 : ((Finset.univ.filter (fun i => lam i ≠ 0)).card : ℝ) + Z.card = Fintype.card ι := by
      exact_mod_cast hsplit
    have hk' : ((Finset.univ.filter (fun i => lam i ≠ 0)).card : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc ((Fintype.card ι : ℝ) - k) * c ≤ Z.card * c := mul_le_mul_of_nonneg_right hZ hc
    _ = ∑ i ∈ Z, g i := by
        rw [Finset.sum_congr rfl (fun i hi => hg0 i (by simpa [hZdef] using hi)),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

/-- **Spectral estimates for the barrier potential.** Let `A ⪰ 0` have rank at most `k` and
`A ≺ u`, let `M = (u + δ) - A`, and write `Φ(v) = tr (v - A)⁻¹ - (N - k) / v` and
`T₂ = tr M⁻² - (N - k) / (u + δ)²`. Then `δ T₂ ≤ Φ(u) - Φ(u + δ)`, `T₂ ≥ k / (u + δ)²`,
`Φ(u + δ) ≥ k / (u + δ)`, and for `0 ⪯ B ⪯ 1` the traces `tr (M⁻¹ B)` and `tr (M⁻² B)` are at
most `tr B / (u + δ) + Φ(u + δ)` and `tr B / (u + δ)² + T₂`. -/
private lemma potential_estimates {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {k : ℕ}
    (hrank : A.rank ≤ k) {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hPD : (u • 1 - A).PosDef) :
    (δ * ((((u + δ) • 1 - A)⁻¹ * ((u + δ) • 1 - A)⁻¹).trace -
        ((Fintype.card ι : ℝ) - k) / (u + δ) ^ 2) ≤
      ((u • 1 - A)⁻¹.trace - ((Fintype.card ι : ℝ) - k) / u) -
        (((u + δ) • 1 - A)⁻¹.trace - ((Fintype.card ι : ℝ) - k) / (u + δ))) ∧
    (k / (u + δ) ^ 2 ≤ (((u + δ) • 1 - A)⁻¹ * ((u + δ) • 1 - A)⁻¹).trace -
        ((Fintype.card ι : ℝ) - k) / (u + δ) ^ 2) ∧
    (k / (u + δ) ≤ ((u + δ) • 1 - A)⁻¹.trace - ((Fintype.card ι : ℝ) - k) / (u + δ)) ∧
    ∀ B : Matrix ι ι ℝ, B.PosSemidef → (1 - B).PosSemidef →
      (((u + δ) • 1 - A)⁻¹ * B).trace ≤
          B.trace / (u + δ) + (((u + δ) • 1 - A)⁻¹.trace - ((Fintype.card ι : ℝ) - k) / (u + δ))
        ∧ (((u + δ) • 1 - A)⁻¹ * ((u + δ) • 1 - A)⁻¹ * B).trace ≤
          B.trace / (u + δ) ^ 2 + ((((u + δ) • 1 - A)⁻¹ * ((u + δ) • 1 - A)⁻¹).trace -
            ((Fintype.card ι : ℝ) - k) / (u + δ) ^ 2) := by
  have hAh : A.IsHermitian := hA.isHermitian
  set lam := hAh.eigenvalues with hlam
  have hl0 : ∀ i, 0 ≤ lam i := fun i => hA.eigenvalues_nonneg i
  have hlu : ∀ i, lam i < u := fun i => eigenvalues_lt_of_posDef hAh hPD i
  have hcount : (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ k := by
    have h := hAh.rank_eq_card_non_zero_eigs
    rw [Fintype.card_subtype] at h
    rw [← h]; exact hrank
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  set v := u + δ with hv
  have hv0 : 0 < v := by positivity
  have hfc : ∀ c : ℝ, hAh.cfc (fun x => c - x) = c • 1 - A := fun c => by
    rw [fc_sub, fc_const, fc_id]
  have hinv : ∀ c : ℝ, (∀ i, lam i < c) →
      (c • (1 : Matrix ι ι ℝ) - A)⁻¹ = hAh.cfc (fun x => (c - x)⁻¹) := fun c hc => by
    rw [← hfc]
    exact fc_inv hAh fun i => mul_inv_cancel₀ (sub_pos.mpr (hc i)).ne'
  have hlv : ∀ i, lam i < v := fun i => by linarith [hlu i]
  have hMinv := hinv v hlv
  have hUinv := hinv u hlu
  have hM2 : (v • (1 : Matrix ι ι ℝ) - A)⁻¹ * (v • 1 - A)⁻¹ =
      hAh.cfc (fun x => (v - x)⁻¹ * (v - x)⁻¹) := by
    rw [hMinv, fc_mul]
  -- traces as sums
  have htrM : (v • (1 : Matrix ι ι ℝ) - A)⁻¹.trace = ∑ i, (v - lam i)⁻¹ := by
    rw [hMinv, trace_fc]
  have htrU : (u • (1 : Matrix ι ι ℝ) - A)⁻¹.trace = ∑ i, (u - lam i)⁻¹ := by
    rw [hUinv, trace_fc]
  have htrM2 : ((v • (1 : Matrix ι ι ℝ) - A)⁻¹ * (v • 1 - A)⁻¹).trace =
      ∑ i, (v - lam i)⁻¹ * (v - lam i)⁻¹ := by
    rw [hM2, trace_fc]
  have hcard : (∑ _i : ι, (1 : ℝ)) = N := by simp [hN]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `δ T₂ ≤ Φ(u) - Φ(v)`
    rw [htrM2, htrU, htrM]
    have key := sub_mul_le_sum (lam := lam) hcount
      (g := fun i => (u - lam i)⁻¹ - (v - lam i)⁻¹ - δ * ((v - lam i)⁻¹ * (v - lam i)⁻¹))
      (c := u⁻¹ - v⁻¹ - δ * (v⁻¹ * v⁻¹)) ?_ ?_ ?_
    · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at key
      have e1 : ((N - k) / v ^ 2) = (N - k) * (v⁻¹ * v⁻¹) := by field_simp
      have e2 : (N - k) / u = (N - k) * u⁻¹ := by field_simp
      have e3 : (N - k) / v = (N - k) * v⁻¹ := by field_simp
      rw [e1, e2, e3]
      nlinarith [key]
    · -- `c ≥ 0`
      rw [hv, inv_sub_inv_sub_eq u δ hu hδ]; positivity
    · intro i
      have ha : 0 < u - lam i := sub_pos.mpr (hlu i)
      have : v - lam i = (u - lam i) + δ := by rw [hv]; ring
      rw [this, inv_sub_inv_sub_eq _ δ ha hδ]; positivity
    · intro i hi
      simp only [hi, sub_zero]
  · -- `T₂ ≥ k / v²`
    rw [htrM2]
    have h1 : ∀ i, v⁻¹ * v⁻¹ ≤ (v - lam i)⁻¹ * (v - lam i)⁻¹ := fun i => by
      have hb : 0 < v - lam i := sub_pos.mpr (hlv i)
      have : (v - lam i)⁻¹ ≥ v⁻¹ := inv_anti₀ hb (by linarith [hl0 i])
      exact mul_le_mul this this (by positivity) (by positivity)
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have e1 : (k : ℝ) / v ^ 2 + (N - k) / v ^ 2 = N * (v⁻¹ * v⁻¹) := by
      field_simp; ring
    linarith
  · -- `Φ(v) ≥ k / v`
    rw [htrM]
    have h1 : ∀ i, v⁻¹ ≤ (v - lam i)⁻¹ := fun i =>
      inv_anti₀ (sub_pos.mpr (hlv i)) (by linarith [hl0 i])
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have e1 : (k : ℝ) / v + (N - k) / v = N * v⁻¹ := by
      field_simp; ring
    linarith
  · intro B hB hB1
    have hb0 : ∀ i, 0 ≤ dg hAh B i := fun i => dg_nonneg hAh hB i
    have hb1 : ∀ i, dg hAh B i ≤ 1 := fun i => by
      have := dg_le_of_posSemidef_sub hAh hB1 i
      rwa [dg_one] at this
    have htrB : B.trace = ∑ i, dg hAh B i := by
      have := trace_fc_mul hAh (fun _ => 1) B
      rw [fc_const, one_smul, Matrix.one_mul] at this
      simpa using this
    have hgen : ∀ a : ℝ → ℝ, (∀ i, 0 ≤ a (lam i)) → (∀ i, lam i = 0 → a (lam i) = a 0) →
        0 ≤ a 0 →
        ∑ i, a (lam i) * dg hAh B i ≤
          (∑ i, dg hAh B i) * a 0 + (∑ i, a (lam i) - (N - k) * a 0) := by
      intro a ha ha0 ha00
      have key := sub_mul_le_sum (lam := lam) hcount
        (g := fun i => a (lam i) * (1 - dg hAh B i) + dg hAh B i * a 0) (c := a 0) ha00
        (fun i => add_nonneg (mul_nonneg (ha i) (by linarith [hb1 i]))
          (mul_nonneg (hb0 i) ha00))
        (fun i hi => by simp only [ha0 i hi]; ring)
      simp only [mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul] at key
      linarith
    refine ⟨?_, ?_⟩
    · rw [hMinv, trace_fc_mul, ← hMinv, htrM, htrB]
      have := hgen (fun x => (v - x)⁻¹) (fun i => (inv_pos.mpr (sub_pos.mpr (hlv i))).le)
        (fun i hi => by simp only [hi]) (by simp only [sub_zero]; positivity)
      simp only [sub_zero] at this
      have e : (∑ i, dg hAh B i) / v = (∑ i, dg hAh B i) * v⁻¹ := div_eq_mul_inv _ _
      have e3 : (N - k) / v = (N - k) * v⁻¹ := div_eq_mul_inv _ _
      rw [e, e3]
      linarith
    · rw [hM2, trace_fc_mul, ← hM2, htrM2, htrB]
      have := hgen (fun x => (v - x)⁻¹ * (v - x)⁻¹)
        (fun i => by have := (inv_pos.mpr (sub_pos.mpr (hlv i))).le; positivity)
        (fun i hi => by simp only [hi]) (by simp only [sub_zero]; positivity)
      simp only [sub_zero] at this
      have e : (∑ i, dg hAh B i) / v ^ 2 = (∑ i, dg hAh B i) * (v⁻¹ * v⁻¹) := by
        field_simp
      have e3 : (N - k) / v ^ 2 = (N - k) * (v⁻¹ * v⁻¹) := by field_simp
      rw [e, e3]
      linarith

end Potential

section TraceFacts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma trace_mul_nonneg {P Q : Matrix ι ι ℝ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace := by
  classical
  have hPh := hP.isHermitian
  have : P * Q = hPh.cfc (fun x => x) * Q := by rw [fc_id]
  rw [this, trace_fc_mul]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hP.eigenvalues_nonneg i) (dg_nonneg hPh hQ i)

/-- A positive semidefinite matrix below the identity has trace at most its rank. -/
private lemma trace_le_rank {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (h1 : (1 - A).PosSemidef) :
    A.trace ≤ A.rank := by
  have hAh := hA.isHermitian
  have htr : A.trace = ∑ i, hAh.eigenvalues i := by
    conv_lhs => rw [← fc_id hAh]
    rw [trace_fc]
  have hle : ∀ i, hAh.eigenvalues i ≤ 1 := fun i =>
    eigenvalues_le_of_posSemidef hAh (by rwa [one_smul]) i
  rw [htr, hAh.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    ← Finset.sum_filter_ne_zero]
  calc ∑ i ∈ Finset.univ.filter (fun i => hAh.eigenvalues i ≠ 0), hAh.eigenvalues i
      ≤ ∑ i ∈ Finset.univ.filter (fun i => hAh.eigenvalues i ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = _ := by simp

end TraceFacts

section EdgeMatrices

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → V → ℝ)

/-- The sum, over ordered pairs `(s, t) ∈ S × T` of adjacent vertices, of the rank-one matrices
`(w s - w t) (w s - w t)ᵀ`. -/
private noncomputable def edgeMat (S T : Finset V) : Matrix V V ℝ :=
  ∑ s ∈ S, ∑ t ∈ T, if G.Adj s t then vecMulVec (w s - w t) (w s - w t) else 0

/-- The image of the Laplacian of the edges inside `S`. -/
private noncomputable def lapS (S : Finset V) : Matrix V V ℝ := (1 / 2 : ℝ) • edgeMat G w S S

private lemma edgeMat_posSemidef (S T : Finset V) : (edgeMat G w S T).PosSemidef := by
  refine posSemidef_sum _ fun s _ => posSemidef_sum _ fun t _ => ?_
  split_ifs
  · simpa using posSemidef_vecMulVec_self_star (w s - w t)
  · exact PosSemidef.zero

private lemma lapS_posSemidef (S : Finset V) : (lapS G w S).PosSemidef :=
  (edgeMat_posSemidef G w S S).smul (by norm_num)

private lemma edgeMat_comm (S T : Finset V) : edgeMat G w S T = edgeMat G w T S := by
  unfold edgeMat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  by_cases h : G.Adj s t
  · simp only [h, h.symm, ↓reduceIte]
    rw [← neg_sub (w s) (w t), neg_vecMulVec, vecMulVec_neg, neg_neg]
  · simp only [h, show ¬G.Adj t s from fun h' => h h'.symm, ↓reduceIte]

private lemma edgeMat_singleton_self (t : V) : edgeMat G w {t} {t} = 0 := by
  simp [edgeMat]

private lemma edgeMat_empty_left (T : Finset V) : edgeMat G w ∅ T = 0 := by
  simp [edgeMat]

private lemma sum_edgeMat_singleton_right (S T : Finset V) :
    ∑ t ∈ T, edgeMat G w S {t} = edgeMat G w S T := by
  unfold edgeMat
  rw [Finset.sum_comm]
  simp

private lemma sum_edgeMat_singleton_left (S T : Finset V) :
    ∑ s ∈ S, edgeMat G w {s} T = edgeMat G w S T := by
  simp [edgeMat]

section DecidableEq

variable [DecidableEq V]

private lemma edgeMat_union_left {S₁ S₂ : Finset V} (h : Disjoint S₁ S₂) (T : Finset V) :
    edgeMat G w (S₁ ∪ S₂) T = edgeMat G w S₁ T + edgeMat G w S₂ T := by
  unfold edgeMat
  rw [Finset.sum_union h]

private lemma edgeMat_union_right (S : Finset V) {T₁ T₂ : Finset V} (h : Disjoint T₁ T₂) :
    edgeMat G w S (T₁ ∪ T₂) = edgeMat G w S T₁ + edgeMat G w S T₂ := by
  rw [edgeMat_comm, edgeMat_union_left G w h, edgeMat_comm G w T₁, edgeMat_comm G w T₂]

private lemma lapS_insert {S : Finset V} {t : V} (ht : t ∉ S) :
    lapS G w (insert t S) = lapS G w S + edgeMat G w S {t} := by
  unfold lapS
  have hd : Disjoint {t} S := Finset.disjoint_singleton_left.mpr ht
  rw [Finset.insert_eq, edgeMat_union_left G w hd, edgeMat_union_right G w _ hd,
    edgeMat_union_right G w _ hd, edgeMat_singleton_self, edgeMat_comm G w {t} S]
  module

end DecidableEq

variable [Fintype V]

/-- The leverage of an ordered pair of vertices. -/
private noncomputable def lev (s t : V) : ℝ :=
  if G.Adj s t then (w s - w t) ⬝ᵥ (w s - w t) else 0

private lemma lev_nonneg (s t : V) : 0 ≤ lev G w s t := by
  unfold lev
  split_ifs
  · exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  · exact le_rfl

private lemma trace_edgeMat (S T : Finset V) :
    (edgeMat G w S T).trace = ∑ s ∈ S, ∑ t ∈ T, lev G w s t := by
  unfold edgeMat lev
  simp only [trace_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact trace_vecMulVec _ _
  · exact trace_zero _ _

private lemma trace_edgeMat_mono (S : Finset V) {T₁ T₂ : Finset V} (h : T₁ ⊆ T₂) :
    (edgeMat G w S T₁).trace ≤ (edgeMat G w S T₂).trace := by
  rw [trace_edgeMat, trace_edgeMat]
  exact Finset.sum_le_sum fun s _ =>
    Finset.sum_le_sum_of_subset_of_nonneg h fun t _ _ => lev_nonneg G w s t

private lemma dotProduct_edgeMat (S T : Finset V) (x : V → ℝ) :
    x ⬝ᵥ (edgeMat G w S T *ᵥ x) =
      ∑ s ∈ S, ∑ t ∈ T, if G.Adj s t then ((w s - w t) ⬝ᵥ x) ^ 2 else 0 := by
  unfold edgeMat
  simp only [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm x, sq]
  · simp

private lemma rank_lapS_le (S : Finset V) : (lapS G w S).rank ≤ S.card := by
  -- `lapS S = Y * Z` with `Y` having columns `w s`, `s ∈ S`
  let Y : Matrix V S ℝ := fun i s => w s i
  let Z : Matrix S V ℝ := fun s j => ∑ t ∈ S, if G.Adj s t then (w s j - w t j) else 0
  have hYZ : lapS G w S = Y * Z := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Y, Z]
    rw [Finset.sum_coe_sort S (fun s => w s i * ∑ t ∈ S, if G.Adj s t then w s j - w t j else 0)]
    simp only [lapS, edgeMat, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    have h2 : ∀ s t, (if G.Adj s t then vecMulVec (w s - w t) (w s - w t) else 0 :
        Matrix V V ℝ) i j = (if G.Adj s t then w s i * (w s j - w t j) else 0) -
          (if G.Adj s t then w t i * (w s j - w t j) else 0) := by
      intro s t
      split_ifs
      · simp only [vecMulVec_apply, Pi.sub_apply]; ring
      · simp
    have h1 : ∑ s ∈ S, ∑ t ∈ S, (if G.Adj s t then w t i * (w s j - w t j) else 0) =
        - ∑ s ∈ S, ∑ t ∈ S, (if G.Adj s t then w s i * (w s j - w t j) else 0) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : G.Adj s t
      · simp only [h, h.symm, ↓reduceIte]; ring
      · simp only [h, show ¬G.Adj t s from fun h' => h h'.symm, ↓reduceIte]; ring
    simp only [h2, Finset.sum_sub_distrib, h1]
    rw [show ∀ x : ℝ, 1 / 2 * (x - -x) = x by intro x; ring, Finset.sum_congr rfl fun s _ => ?_]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  rw [hYZ]
  calc (Y * Z).rank ≤ Y.rank := rank_mul_le_left _ _
    _ ≤ Fintype.card S := rank_le_card_width _
    _ = S.card := Fintype.card_coe S

variable [DecidableEq V]

private lemma lapS_univ (S : Finset V) :
    lapS G w Finset.univ = lapS G w S + lapS G w Sᶜ + edgeMat G w S Sᶜ := by
  unfold lapS
  have hd : Disjoint S Sᶜ := disjoint_compl_right
  rw [← Finset.union_compl S, edgeMat_union_left G w hd, edgeMat_union_right G w _ hd,
    edgeMat_union_right G w _ hd, edgeMat_comm G w Sᶜ S]
  module

end EdgeMatrices

section Greedy

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (w : V → V → ℝ)

/-- The barrier potential `tr (v - L_S)⁻¹ - (n - k) / v`. -/
private noncomputable def pot (k : ℕ) (S : Finset V) (v : ℝ) : ℝ :=
  ((v • (1 : Matrix V V ℝ) - lapS G w S)⁻¹).trace - ((Fintype.card V : ℝ) - k) / v

private lemma one_sub_edgeMat_compl (hnorm : (1 - lapS G w Finset.univ).PosSemidef)
    (S : Finset V) : (1 - edgeMat G w S Sᶜ).PosSemidef := by
  have : 1 - edgeMat G w S Sᶜ = (1 - lapS G w Finset.univ) + lapS G w S + lapS G w Sᶜ := by
    rw [lapS_univ G w S]; abel
  rw [this]
  exact (hnorm.add (lapS_posSemidef G w S)).add (lapS_posSemidef G w Sᶜ)

private lemma one_sub_lapS (hnorm : (1 - lapS G w Finset.univ).PosSemidef) (T : Finset V) :
    (1 - lapS G w T).PosSemidef := by
  have : 1 - lapS G w T = (1 - lapS G w Finset.univ) + lapS G w Tᶜ + edgeMat G w T Tᶜ := by
    rw [lapS_univ G w T]; abel
  rw [this]
  exact (hnorm.add (lapS_posSemidef G w Tᶜ)).add (edgeMat_posSemidef G w T Tᶜ)

private lemma trace_lapS_le (hnorm : (1 - lapS G w Finset.univ).PosSemidef) (T : Finset V) :
    (lapS G w T).trace ≤ T.card :=
  (trace_le_rank (lapS_posSemidef G w T) (one_sub_lapS G w hnorm T)).trans
    (by exact_mod_cast rank_lapS_le G w T)

/-- **One greedy step** (Lemma B.3 of the source): a vertex `t ∉ S` can be added to `S` while
the barrier moves from `u` to `u + ε / (2k)`, the potential stays at most `2k / ε` and the
leverage of the edges leaving the set stays at most `4` per vertex. -/
private lemma greedy_step (hnorm : (1 - lapS G w Finset.univ).PosSemidef) {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k) (hkn : 50 * (k : ℝ) ≤ ε * Fintype.card V) (hε : 0 < ε) (hε1 : ε < 1)
    {S : Finset V} (hS : S.card < k) {u : ℝ} (hu : 0 < u)
    (hPD : (u • 1 - lapS G w S).PosDef) (hΦ : pot G w k S u ≤ 2 * k / ε)
    (hℓ : (edgeMat G w S Sᶜ).trace ≤ 4 * S.card) :
    ∃ t ∉ S, ((u + ε / (2 * k)) • 1 - lapS G w (insert t S)).PosDef ∧
      pot G w k (insert t S) (u + ε / (2 * k)) ≤ 2 * k / ε ∧
      (edgeMat G w (insert t S) (insert t S)ᶜ).trace ≤ 4 * (insert t S).card := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set δ := ε / (2 * k) with hδdef
  have hδ : 0 < δ := by positivity
  have hA : (lapS G w S).PosSemidef := lapS_posSemidef G w S
  have hrank : (lapS G w S).rank ≤ k := (rank_lapS_le G w S).trans hS.le
  obtain ⟨e1, e2, e3, e4⟩ := potential_estimates hA hrank hu hδ hPD
  unfold pot at hΦ ⊢
  set A := lapS G w S with hAdef
  set v := u + δ with hv
  set M := v • (1 : Matrix V V ℝ) - A with hM
  set N : ℝ := (Fintype.card V : ℝ) with hN
  set Φu := (u • (1 : Matrix V V ℝ) - A)⁻¹.trace - (N - k) / u with hΦu
  set Φv := M⁻¹.trace - (N - k) / v with hΦv
  set T2 := (M⁻¹ * M⁻¹).trace - (N - k) / v ^ 2 with hT2
  have hv0 : 0 < v := by positivity
  have hT2pos : 0 < T2 := lt_of_lt_of_le (by positivity) e2
  have hΔpos : 0 < Φu - Φv := lt_of_lt_of_le (by positivity) e1
  -- `M` is positive definite
  have hMpd : M.PosDef := by
    have : M = (u • 1 - A) + δ • 1 := by rw [hM, hv, add_smul]; abel
    rw [this]
    exact hPD.add_posSemidef (PosSemidef.one.smul hδ.le)
  have hMinvpsd : M⁻¹.PosSemidef := hMpd.inv.posSemidef
  have hMinv2psd : (M⁻¹ * M⁻¹).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self M⁻¹
    rwa [hMpd.inv.isHermitian.eq] at this
  -- the two scores of a candidate vertex
  set f : V → ℝ := fun t => (edgeMat G w {t} Sᶜ).trace with hf
  set U : V → ℝ := fun t => (M⁻¹ * M⁻¹ * edgeMat G w S {t}).trace / (Φu - Φv) +
    (M⁻¹ * edgeMat G w S {t}).trace with hU
  have hf0 : ∀ t, 0 ≤ f t := fun t => (edgeMat_posSemidef G w {t} Sᶜ).trace_nonneg
  have hU0 : ∀ t, 0 ≤ U t := fun t =>
    add_nonneg (div_nonneg (trace_mul_nonneg hMinv2psd (edgeMat_posSemidef G w S {t}))
      hΔpos.le) (trace_mul_nonneg hMinvpsd (edgeMat_posSemidef G w S {t}))
  -- the sum of the first scores
  have hsumf : ∑ t ∈ Sᶜ, f t ≤ 2 * Sᶜ.card := by
    have h1 : ∑ t ∈ Sᶜ, f t = (edgeMat G w Sᶜ Sᶜ).trace := by
      simp only [hf, ← trace_sum, sum_edgeMat_singleton_left]
    have h2 : (edgeMat G w Sᶜ Sᶜ).trace = 2 * (lapS G w Sᶜ).trace := by
      simp only [lapS, trace_smul, smul_eq_mul]; ring
    rw [h1, h2]
    linarith [trace_lapS_le G w hnorm Sᶜ]
  -- the sum of the second scores
  have hC := e4 (edgeMat G w S Sᶜ) (edgeMat_posSemidef G w S Sᶜ)
    (one_sub_edgeMat_compl G w hnorm S)
  have hcardS : (S.card : ℝ) ≤ k := by exact_mod_cast hS.le
  have hTrC : (edgeMat G w S Sᶜ).trace ≤ 4 * k := by linarith
  have hsumU : ∑ t ∈ Sᶜ, U t ≤ 20 * k / ε := by
    have hsplit : ∑ t ∈ Sᶜ, U t = (M⁻¹ * M⁻¹ * edgeMat G w S Sᶜ).trace / (Φu - Φv) +
        (M⁻¹ * edgeMat G w S Sᶜ).trace := by
      simp only [hU, Finset.sum_add_distrib, ← Finset.sum_div, ← trace_sum, ← Matrix.mul_sum,
        sum_edgeMat_singleton_right]
    rw [hsplit]
    have h1 : (M⁻¹ * M⁻¹ * edgeMat G w S Sᶜ).trace ≤ 5 * T2 := by
      have h := hC.2
      have : (edgeMat G w S Sᶜ).trace / v ^ 2 ≤ 4 * T2 := by
        calc (edgeMat G w S Sᶜ).trace / v ^ 2 ≤ 4 * k / v ^ 2 := by gcongr
          _ = 4 * (k / v ^ 2) := by ring
          _ ≤ 4 * T2 := by gcongr
      linarith
    have h2 : (M⁻¹ * edgeMat G w S Sᶜ).trace ≤ 5 * Φv := by
      have h := hC.1
      have : (edgeMat G w S Sᶜ).trace / v ≤ 4 * Φv := by
        calc (edgeMat G w S Sᶜ).trace / v ≤ 4 * k / v := by gcongr
          _ = 4 * (k / v) := by ring
          _ ≤ 4 * Φv := by gcongr
      linarith
    have h3 : 5 * T2 / (Φu - Φv) ≤ 5 / δ := by
      rw [div_le_div_iff₀ hΔpos hδ]
      nlinarith [e1]
    have h4 : Φv ≤ 2 * k / ε := by linarith
    calc (M⁻¹ * M⁻¹ * edgeMat G w S Sᶜ).trace / (Φu - Φv) + (M⁻¹ * edgeMat G w S Sᶜ).trace
        ≤ 5 * T2 / (Φu - Φv) + 5 * Φv := by gcongr
      _ ≤ 5 / δ + 5 * (2 * k / ε) := by gcongr
      _ = 20 * k / ε := by rw [hδdef]; field_simp; ring
  -- averaging over the vertices outside `S`
  have hcomp : (S.card : ℝ) + Sᶜ.card = N := by
    rw [hN]; exact_mod_cast Finset.card_add_card_compl S
  have hbig : 40 * (k : ℝ) < ε * Sᶜ.card := by
    have hc : (k : ℝ) ≤ Sᶜ.card + k - (N - k) := by linarith
    nlinarith
  have hlt : ∑ t ∈ Sᶜ, (f t / 4 + U t) < ∑ t ∈ Sᶜ, (1 : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : 20 * k / ε < Sᶜ.card / 2 := by
      rw [div_lt_div_iff₀ hε (by norm_num)]; linarith
    linarith
  obtain ⟨t, htS, ht⟩ := Finset.exists_lt_of_sum_lt hlt
  have htS' : t ∉ S := Finset.mem_compl.mp htS
  have hUt : U t < 1 := by linarith [hf0 t]
  have hft : f t ≤ 4 := by linarith [hU0 t]
  -- the barrier step
  set B := edgeMat G w S {t} with hB
  have hB0 : 0 ≤ (M⁻¹ * M⁻¹ * B).trace / (Φu - Φv) :=
    div_nonneg (trace_mul_nonneg hMinv2psd (edgeMat_posSemidef G w S {t})) hΔpos.le
  have hτ : (M⁻¹ * B).trace < 1 := by
    have : U t = (M⁻¹ * M⁻¹ * B).trace / (Φu - Φv) + (M⁻¹ * B).trace := rfl
    linarith
  obtain ⟨hNpd, hNtr⟩ := barrier_step hMpd (edgeMat_posSemidef G w S {t}) hτ
  have hgain : (M⁻¹ * M⁻¹ * B).trace / (1 - (M⁻¹ * B).trace) ≤ Φu - Φv := by
    have h1τ : 0 < 1 - (M⁻¹ * B).trace := by linarith
    have : (M⁻¹ * M⁻¹ * B).trace / (Φu - Φv) < 1 - (M⁻¹ * B).trace := by
      have : U t = (M⁻¹ * M⁻¹ * B).trace / (Φu - Φv) + (M⁻¹ * B).trace := rfl
      linarith
    rw [div_lt_iff₀ hΔpos] at this
    rw [div_le_iff₀ h1τ]
    linarith
  have hins : v • (1 : Matrix V V ℝ) - lapS G w (insert t S) = M - B := by
    rw [lapS_insert G w htS', hM, hB, hAdef, sub_add_eq_sub_sub]
  refine ⟨t, htS', ?_, ?_, ?_⟩
  · rw [hins]; exact hNpd
  · rw [hins]
    have : (M - B)⁻¹.trace - (N - k) / v ≤ Φu := by linarith
    linarith
  · rw [Finset.card_insert_of_notMem htS', Finset.compl_insert, Finset.insert_eq,
      edgeMat_union_left G w (Finset.disjoint_singleton_left.mpr htS'), trace_add]
    have h1 := trace_edgeMat_mono G w {t} (Finset.erase_subset t Sᶜ)
    have h2 := trace_edgeMat_mono G w S (Finset.erase_subset t Sᶜ)
    push_cast
    have : f t = (edgeMat G w {t} Sᶜ).trace := rfl
    linarith

/-- **The greedy construction.** After `j ≤ k` steps from the empty set and the barrier `ε / 2`,
some set of `j` vertices satisfies the invariants with the barrier `ε / 2 + j ε / (2k)`. -/
private lemma greedy_iterate (hnorm : (1 - lapS G w Finset.univ).PosSemidef) {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k) (hkn : 50 * (k : ℝ) ≤ ε * Fintype.card V) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ j ≤ k, ∃ S : Finset V, S.card = j ∧
      ((ε / 2 + j * (ε / (2 * k))) • 1 - lapS G w S).PosDef ∧
      pot G w k S (ε / 2 + j * (ε / (2 * k))) ≤ 2 * k / ε ∧
      (edgeMat G w S Sᶜ).trace ≤ 4 * S.card := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  intro j
  induction j with
  | zero =>
    intro _
    have hl0 : lapS G w ∅ = 0 := by simp [lapS, edgeMat_empty_left]
    refine ⟨∅, rfl, ?_, ?_, ?_⟩
    · rw [hl0, sub_zero]
      exact PosDef.one.smul (by positivity)
    · unfold pot
      rw [hl0, sub_zero]
      have hinv : ((ε / 2 + ((0 : ℕ) : ℝ) * (ε / (2 * k))) • (1 : Matrix V V ℝ))⁻¹ =
          (ε / 2)⁻¹ • 1 := by
        apply inv_eq_right_inv
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
        push_cast
        rw [zero_mul, add_zero, mul_inv_cancel₀ (by positivity), one_smul]
      rw [hinv, trace_smul, trace_one, smul_eq_mul]
      push_cast
      apply le_of_eq
      field_simp
      ring
    · simp [edgeMat_empty_left]
  | succ j ih =>
    intro hj
    obtain ⟨S, hScard, hPD, hΦ, hℓ⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨t, ht, h1, h2, h3⟩ := greedy_step G w hnorm hk hkn hε hε1
      (by omega : S.card < k) (by positivity) hPD hΦ hℓ
    have he : ε / 2 + j * (ε / (2 * k)) + ε / (2 * k) =
        ε / 2 + ((j + 1 : ℕ) : ℝ) * (ε / (2 * k)) := by push_cast; ring
    refine ⟨insert t S, by rw [Finset.card_insert_of_notMem ht, hScard], ?_, ?_, h3⟩
    · rw [← he]; exact h1
    · rw [← he]; exact h2

/-- **The normalized lemma.** If `L_V ⪯ 1` and `1 ≤ k ≤ ε n / 50`, some set of `k` vertices
satisfies `L_S ⪯ ε`. -/
private lemma exists_light (hnorm : (1 - lapS G w Finset.univ).PosSemidef) {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k) (hkn : 50 * (k : ℝ) ≤ ε * Fintype.card V) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : Finset V, S.card = k ∧ ∀ x : V → ℝ, x ⬝ᵥ (lapS G w S *ᵥ x) ≤ ε * (x ⬝ᵥ x) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨S, hS, hPD, -, -⟩ := greedy_iterate G w hnorm hk hkn hε hε1 k le_rfl
  have he : ε / 2 + k * (ε / (2 * k)) = ε := by field_simp; ring
  rw [he] at hPD
  refine ⟨S, hS, fun x => ?_⟩
  have := hPD.posSemidef.dotProduct_mulVec_nonneg x
  rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul] at this
  linarith

end Greedy

section Glue

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quadratic form of a Laplacian matrix. -/
private lemma dotProduct_lapMatrix (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) :
    x ⬝ᵥ (H.lapMatrix ℝ *ᵥ x) = (∑ i, ∑ j, if H.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  rw [← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']

open Classical in
/-- A set is `ε`-light as soon as the quadratic form of its edges is at most `ε` times the
quadratic form of all edges. -/
private lemma isEpsilonLight_of_forall (G : SimpleGraph V) {ε : ℝ} (S : Finset V)
    (h : ∀ x : V → ℝ, (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then (x i - x j) ^ 2 else 0) ≤
      ε * ∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0) :
    IsEpsilonLight G ε S := by
  unfold IsEpsilonLight
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact ((posSemidef_lapMatrix ℝ G).isHermitian.smul (IsSelfAdjoint.all ε)).sub
      (posSemidef_lapMatrix ℝ _).isHermitian
  · rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_lapMatrix, dotProduct_lapMatrix]
    have hS : ∀ inst : DecidableRel (G.induce (S : Set V)).spanningCoe.Adj,
        (∑ i, ∑ j, @ite ℝ ((G.induce (S : Set V)).spanningCoe.Adj i j) (inst i j)
          ((x i - x j) ^ 2) 0) =
        ∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then (x i - x j) ^ 2 else 0 := by
      intro inst
      have hadj : ∀ i j, (G.induce (S : Set V)).spanningCoe.Adj i j ↔
          i ∈ S ∧ j ∈ S ∧ G.Adj i j := by
        intro i j
        simp only [map_adj, Function.Embedding.subtype_apply, comap_adj, Subtype.exists,
          Finset.mem_coe]
        constructor
        · rintro ⟨a, ha, b, hb, hab, rfl, rfl⟩
          exact ⟨ha, hb, hab⟩
        · rintro ⟨ha, hb, hab⟩
          exact ⟨i, ha, j, hb, hab, rfl, rfl⟩
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        · refine Finset.sum_congr rfl fun j hj => ?_
          by_cases hij : G.Adj i j
          · rw [ite_eq_left ((hadj i j).mpr ⟨hi, hj, hij⟩), ite_eq_left hij]
          · rw [ite_eq_right (fun h' => hij ((hadj i j).mp h').2.2), ite_eq_right hij]
        · intro j _ hj
          rw [ite_eq_right (fun h' => hj ((hadj i j).mp h').2.1)]
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [ite_eq_right (fun h' => hi ((hadj i j).mp h').1)]
    have hG : ∀ inst : DecidableRel G.Adj,
        (∑ i, ∑ j, @ite ℝ (G.Adj i j) (inst i j) ((x i - x j) ^ 2) 0) =
        ∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0 := by
      intro inst
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by congr
    rw [hS, hG]
    linarith [h x]

omit [DecidableEq V] in
/-- The quadratic form of `lapS` for the rows of a matrix `W`. -/
private lemma dotProduct_lapS_rows (G : SimpleGraph V) [DecidableRel G.Adj] (W : Matrix V V ℝ)
    (S : Finset V) (x : V → ℝ) :
    x ⬝ᵥ (lapS G (fun s i => W s i) S *ᵥ x) =
      (∑ s ∈ S, ∑ t ∈ S, if G.Adj s t then ((W *ᵥ x) s - (W *ᵥ x) t) ^ 2 else 0) / 2 := by
  unfold lapS
  rw [smul_mulVec, dotProduct_smul, dotProduct_edgeMat, smul_eq_mul]
  have : ∀ s t, ((fun i => W s i) - fun i => W t i) ⬝ᵥ x = (W *ᵥ x) s - (W *ᵥ x) t := by
    intro s t
    rw [sub_dotProduct]
    rfl
  simp only [this]
  ring

omit [DecidableEq V] in
/-- **The perturbed lemma.** For `η > 0` and `1 ≤ k ≤ ε n / 50`, some set `S` of `k` vertices
has `L_S ⪯ ε (L + η)`. -/
private lemma exists_light_perturbed (G : SimpleGraph V) [DecidableRel G.Adj] {η : ℝ}
    (hη : 0 < η) {k : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hkn : 50 * (k : ℝ) ≤ ε * Fintype.card V)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : Finset V, S.card = k ∧ ∀ y : V → ℝ,
      (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then (y i - y j) ^ 2 else 0) ≤
        ε * ((∑ i, ∑ j, if G.Adj i j then (y i - y j) ^ 2 else 0) + 2 * η * (y ⬝ᵥ y)) := by
  classical
  set L := G.lapMatrix ℝ with hL
  have hLpsd : L.PosSemidef := posSemidef_lapMatrix ℝ G
  set Lη := L + η • (1 : Matrix V V ℝ) with hLη
  have hLηpd : Lη.PosDef := Matrix.PosDef.posSemidef_add hLpsd (PosDef.one.smul hη)
  have hLh : Lη.IsHermitian := hLηpd.isHermitian
  have hpos : ∀ i, 0 < hLh.eigenvalues i := fun i => hLηpd.eigenvalues_pos i
  have hsq : ∀ i, Real.sqrt (hLh.eigenvalues i) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (hpos i)).ne'
  set W := hLh.cfc (fun x => (Real.sqrt x)⁻¹) with hW
  set W' := hLh.cfc (fun x => Real.sqrt x) with hW'
  have hWt : Wᵀ = W := fc_transpose hLh _
  have hWLW : W * Lη * W = 1 := by
    have : W * Lη * W = W * hLh.cfc (fun x => x) * W := by rw [fc_id]
    rw [this, hW, fc_mul, fc_mul]
    rw [fc_congr hLh (g := fun _ => 1) (fun i => by
      rw [mul_comm _ (Real.sqrt _)⁻¹, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hpos i).le,
        inv_mul_cancel₀ (hpos i).ne']), fc_const, one_smul]
  have hWW' : W * W' = 1 := by
    rw [hW, hW', fc_mul, fc_congr hLh (g := fun _ => 1) (fun i => inv_mul_cancel₀ (hsq i)),
      fc_const, one_smul]
  have hquad : ∀ y : V → ℝ, y ⬝ᵥ (Lη *ᵥ y) =
      (∑ i, ∑ j, if G.Adj i j then (y i - y j) ^ 2 else 0) / 2 + η * (y ⬝ᵥ y) := by
    intro y
    rw [hLη, add_mulVec, dotProduct_add, hL, dotProduct_lapMatrix, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul]
  have hconj : ∀ x : V → ℝ, x ⬝ᵥ x = (W *ᵥ x) ⬝ᵥ (Lη *ᵥ (W *ᵥ x)) := by
    intro x
    have hvW : x ᵥ* W = W *ᵥ x := by
      conv_lhs => rw [← hWt]
      exact vecMul_transpose W x
    calc x ⬝ᵥ x = x ⬝ᵥ ((W * Lη * W) *ᵥ x) := by rw [hWLW, one_mulVec]
      _ = (W *ᵥ x) ⬝ᵥ (Lη *ᵥ (W *ᵥ x)) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hvW]
  set w : V → V → ℝ := fun s i => W s i with hw
  have hnorm : (1 - lapS G w Finset.univ).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_one.sub (lapS_posSemidef G w Finset.univ).isHermitian) fun x => ?_
    rw [star_trivial, sub_mulVec, dotProduct_sub, one_mulVec, hw, dotProduct_lapS_rows,
      hconj x, hquad]
    have : 0 ≤ η * ((W *ᵥ x) ⬝ᵥ (W *ᵥ x)) :=
      mul_nonneg hη.le (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    linarith
  obtain ⟨S, hS, hSx⟩ := exists_light G w hnorm hk hkn hε hε1
  refine ⟨S, hS, fun y => ?_⟩
  set x := W' *ᵥ y with hx
  have hWx : W *ᵥ x = y := by rw [hx, mulVec_mulVec, hWW', one_mulVec]
  have h1 := hSx x
  rw [hw, dotProduct_lapS_rows, hWx, hconj x, hWx, hquad] at h1
  nlinarith

end Glue

/--
**Every graph has a large ε-light vertex set.** There is a real constant $c > 0$ such that for
every natural number $n$, every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ and every
real number $\varepsilon$ with $0 < \varepsilon < 1$, there is a set $S$ of vertices with at least
$c \varepsilon n$ elements that is $\varepsilon$-light in $G$: the matrix $\varepsilon L - L_S$ is
positive semidefinite, where $L$ is the real Laplacian matrix of $G$ and $L_S$ is the real
Laplacian matrix of the graph on all $n$ vertices whose edges are the edges of $G$ with both
endpoints in $S$.

Appendix B.6 of the source proves this, with $c = 1/42$, as Lemma B.1 (stated for weighted graphs).

Source: First Proof authors, arXiv:2602.05192v2, Appendix B.6 (Lemma B.1),
https://arxiv.org/html/2602.05192v2. Moved from
`OpenConjectures/Combinatorics/EpsilonLightSubset`.
-/
public theorem epsilonLightSubsetExists_holds : epsilonLightSubsetExists := by
  refine ⟨1 / 100, by norm_num, fun n G ε hε hε1 => ?_⟩
  classical
  by_cases hsmall : ε * n < 50
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, isEpsilonLight_of_forall G ∅ fun x => by simp, by simp⟩
    · refine ⟨{⟨0, hn⟩}, isEpsilonLight_of_forall G _ fun x => ?_, ?_⟩
      · simp only [Finset.sum_singleton, G.irrefl, ↓reduceIte]
        exact mul_nonneg hε.le (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          split_ifs <;> positivity)
      · simp only [Finset.card_singleton, Nat.cast_one]
        nlinarith
  · push Not at hsmall
    obtain ⟨k, hk1, hkn, hkc⟩ : ∃ k : ℕ, 1 ≤ k ∧ 50 * (k : ℝ) ≤ ε * n ∧ ε * n / 100 ≤ k := by
      have h1 : (1 : ℝ) ≤ ε * n / 50 := by linarith
      refine ⟨⌊ε * n / 50⌋₊, (Nat.one_le_floor_iff _).mpr h1, ?_, ?_⟩
      · have := Nat.floor_le (show 0 ≤ ε * n / 50 by positivity)
        linarith
      · have h2 := Nat.lt_floor_add_one (ε * n / 50)
        have h3 : (1 : ℝ) ≤ ⌊ε * n / 50⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).mpr h1
        linarith
    have hkn' : 50 * (k : ℝ) ≤ ε * Fintype.card (Fin n) := by rwa [Fintype.card_fin]
    choose! Sf hSf using fun m : ℕ =>
      exists_light_perturbed G (η := 1 / (m + 1)) (by positivity) hk1 hkn' hε hε1
    obtain ⟨S, hS⟩ : ∃ S, ∀ N : ℕ, ∃ m ≥ N, Sf m = S := by
      by_contra hcon
      push Not at hcon
      choose N hN using hcon
      exact hN (Sf (Finset.univ.sup N)) _ (Finset.le_sup (Finset.mem_univ _)) rfl
    obtain ⟨m0, -, hm0⟩ := hS 0
    refine ⟨S, isEpsilonLight_of_forall G S fun x => ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      set a := x ⬝ᵥ x with ha
      have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      set gap := (∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then (x i - x j) ^ 2 else 0) -
        ε * ∑ i, ∑ j, if G.Adj i j then (x i - x j) ^ 2 else 0 with hgap
      have hgap0 : 0 < gap := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * ε * a / gap)
      obtain ⟨m, hm, hmS⟩ := hS N
      have h1 := (hSf m).2 x
      rw [hmS] at h1
      have hm1 : 2 * ε * a < gap * (m + 1) := by
        have : (N : ℝ) ≤ m := by exact_mod_cast hm
        rw [div_lt_iff₀ hgap0] at hN
        nlinarith
      have hm2 : ε * (2 * (1 / ((m : ℝ) + 1)) * a) < gap := by
        rw [show ε * (2 * (1 / ((m : ℝ) + 1)) * a) = 2 * ε * a / (m + 1) by ring,
          div_lt_iff₀ (by positivity)]
        linarith
      nlinarith
    · rw [← hm0, (hSf m0).1]
      linarith

end MathlibExt.Combinatorics.EpsilonLightSubsetWanted

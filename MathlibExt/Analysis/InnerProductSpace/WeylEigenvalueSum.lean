/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weyl inequalities for eigenvalues of a sum

For self-adjoint operators `T, S` on a finite-dimensional inner product space,
let `λ₀ ≥ λ₁ ≥ ⋯ ≥ λ_{n-1}` be the eigenvalues in decreasing order
(`LinearMap.IsSymmetric.eigenvalues`). Weyl's inequalities relate the
eigenvalues of the sum `T + S` to those of the summands:

* **Upper bound:** `λ_{a+b}(T + S) ≤ λ_a(T) + λ_b(S)` whenever `a + b < n`.
* **Lower bound:** `λ_a(T) + λ_b(S) ≤ λ_{a+b-(n-1)}(T + S)` whenever `n - 1 ≤ a + b`.

In one-indexed form these are the classical statements
`λ_{i+j-1}(T + S) ≤ λ_i(T) + λ_j(S)` and
`λ_{i+j-n}(T + S) ≥ λ_i(T) + λ_j(S)`.

Both bounds are proved by the same dimension-counting argument: intersect
the span of the head (resp. tail) of the eigenbasis of `T + S` with the
spans of the tails (resp. heads) of the eigenbases of `T` and `S`. The three
spans have finranks summing to `2n + 1`, so their intersection contains a
nonzero vector, and the Rayleigh-quotient bounds on the three spans give
the inequality.

This is a companion to the self-adjoint spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the maximum principle for compact self-adjoint operators). It is not one
of the 72 v1 targets. It is distinct from the results already in base
MathlibExt: `WeylPerturbation.lean` bounds `|λ_i(A) - λ_i(B)|` by `‖A - B‖`
(the perturbation/difference form, not the sum form), and `KyFan.lean`
bounds sums of the top `k` eigenvalues of `A + B` (the summed form, not
the individual-eigenvalue form proved here). Pinned Mathlib has the
eigenvalue API but no Weyl sum inequality.

## Main declarations

* `weyl_eigenvalue_add_le` : the upper Weyl inequality, operator form.
* `le_weyl_eigenvalue_add` : the lower Weyl inequality, operator form.
* `Matrix.IsHermitian.eigenvalues₀_add_le` : the upper inequality, matrix form.
* `Matrix.IsHermitian.le_eigenvalues₀_add` : the lower inequality, matrix form.
* `Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone` : eigenvalues of a
  diagonal Hermitian matrix whose diagonal entries are already decreasing.
* `Matrix.IsHermitian.eigenvalues₀_congr` : eigenvalues are unchanged when the
  matrix is replaced by an equal matrix.

Sources: H. Weyl, "Das asymptotische Verteilungsgesetz der Eigenwerte
linearer partieller Differentialgleichungen", Math. Ann. 71 (1912);
Horn–Johnson, *Matrix Analysis*, 2nd ed., Theorem 4.3.7.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum

open Finset Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A vector in the span of a subfamily of an orthonormal basis can be
written as a linear combination of that subfamily. -/
private lemma repr_of_mem_span {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (s : Finset (Fin n)) (x : E)
    (hx : x ∈ Submodule.span 𝕜 (Set.range (fun j : ↥s => b (j : Fin n)))) :
    ∃ r : ↥s → 𝕜, x = ∑ j, r j • b (j : Fin n) := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨c, ?_⟩
  rw [← hc]
  exact Finsupp.sum_fintype _ _ (fun j => zero_smul 𝕜 (b ↑j))

/-- The finrank of the span of a subfamily of an orthonormal basis is the
cardinality of the subfamily. -/
private lemma finrank_span_basis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (s : Finset (Fin n)) :
    Module.finrank 𝕜
        (Submodule.span 𝕜 (Set.range (fun j : ↥s => b (j : Fin n)))) = s.card := by
  have hLI : LinearIndependent 𝕜 (fun j : ↥s => b (j : Fin n)) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [finrank_span_eq_card hLI, Fintype.card_coe]

/-- The quadratic form of an operator diagonal in an orthonormal basis,
expanded in the coefficients of `x` over a subfamily of the basis. -/
private lemma expand_inner {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (ev : Fin n → ℝ) (T : E →ₗ[𝕜] E)
    (hTv : ∀ j, T (b j) = (ev j : 𝕜) • b j)
    (s : Finset (Fin n)) (r : ↥s → 𝕜) (x : E)
    (hx : x = ∑ j : ↥s, r j • b (j : Fin n)) :
    inner 𝕜 (T x) x =
      ∑ j : ↥s, (ev (j : Fin n) : 𝕜) * ((starRingEnd 𝕜) (r j) * r j) := by
  have horth : ∀ j k : ↥s,
      inner 𝕜 (b (j : Fin n)) (b (k : Fin n)) = if j = k then 1 else 0 := by
    intro j k
    have h := orthonormal_iff_ite.mp b.orthonormal (j : Fin n) (k : Fin n)
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true] at h ⊢
      exact h
    · have hjk2 : (j : Fin n) ≠ k := fun hc => hjk (Subtype.ext hc)
      rw [ite_eq_right hjk2] at h
      rw [ite_eq_right hjk]
      exact h
  have hTx : T x = ∑ j : ↥s, (r j * (ev (j : Fin n) : 𝕜)) • b (j : Fin n) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, hTv (j : Fin n), ← mul_smul]
  rw [hTx, hx, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [inner_smul_left, inner_smul_right, horth j j]
    simp only [ite_true]
    rw [map_mul, RCLike.conj_ofReal]
    ring
  · intro k _ hjk
    have hjk' : j ≠ k := Ne.symm hjk
    simp [inner_smul_left, inner_smul_right, horth j k, hjk']
  · simp

/-- The squared norm of a vector, expanded in the coefficients over a
subfamily of an orthonormal basis. -/
private lemma norm_sq_expand {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (s : Finset (Fin n)) (r : ↥s → 𝕜) (x : E)
    (hx : x = ∑ j, r j • b (j : Fin n)) :
    ‖x‖ ^ 2 = ∑ j : ↥s, RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
  have hTv : ∀ j, (LinearMap.id : E →ₗ[𝕜] E) (b j) = ((1 : ℝ) : 𝕜) • b j := by
    intro j
    rw [LinearMap.id_apply, RCLike.ofReal_one, one_smul]
  have h1 := expand_inner b (fun _ => 1) _ hTv s r x hx
  rw [LinearMap.id_apply] at h1
  calc ‖x‖ ^ 2 = RCLike.re (inner 𝕜 x x) := norm_sq_eq_re_inner x
    _ = ∑ j, RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
        rw [h1, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [RCLike.mul_re]

/-- Nonnegativity of the weight `re (conj w * w)` appearing in the expansion. -/
private lemma weight_nonneg (w : 𝕜) :
    0 ≤ RCLike.re ((starRingEnd 𝕜) w * w) := by
  rw [← RCLike.inner_apply']
  exact inner_self_nonneg

/-- Lower Rayleigh bound on a span of eigenvectors whose eigenvalues are
all at least `c`. -/
private lemma re_inner_ge_of_mem_span {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (ev : Fin n → ℝ) (T : E →ₗ[𝕜] E)
    (hTv : ∀ j, T (b j) = (ev j : 𝕜) • b j)
    (s : Finset (Fin n)) (c : ℝ) (x : E)
    (hx : x ∈ Submodule.span 𝕜 (Set.range (fun j : ↥s => b (j : Fin n))))
    (hc : ∀ j ∈ s, c ≤ ev j) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
  obtain ⟨r, hr⟩ := repr_of_mem_span b s x hx
  have hexp := expand_inner b ev T hTv s r x hr
  have hnorm := norm_sq_expand b s r x hr
  have h1 : c * ‖x‖ ^ 2 =
      ∑ j : ↥s, c * RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
    rw [hnorm, Finset.mul_sum]
  have h2 : RCLike.re (inner 𝕜 (T x) x) =
      ∑ j : ↥s, RCLike.re ((ev (j : Fin n) : 𝕜) *
        ((starRingEnd 𝕜) (r j) * r j)) := by
    rw [hexp, map_sum]
  rw [h1, h2]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw := weight_nonneg (r j)
  have hcj : c ≤ ev (j : Fin n) := hc _ j.property
  have hterm : RCLike.re ((ev (j : Fin n) : 𝕜) *
      ((starRingEnd 𝕜) (r j) * r j)) =
      ev (j : Fin n) * RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
    simp [RCLike.mul_re, RCLike.ofReal_re]
  rw [hterm]
  exact mul_le_mul_of_nonneg_right hcj hw

/-- Upper Rayleigh bound on a span of eigenvectors whose eigenvalues are
all at most `C`. -/
private lemma re_inner_le_of_mem_span {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E)
    (ev : Fin n → ℝ) (T : E →ₗ[𝕜] E)
    (hTv : ∀ j, T (b j) = (ev j : 𝕜) • b j)
    (s : Finset (Fin n)) (C : ℝ) (x : E)
    (hx : x ∈ Submodule.span 𝕜 (Set.range (fun j : ↥s => b (j : Fin n))))
    (hC : ∀ j ∈ s, ev j ≤ C) :
    RCLike.re (inner 𝕜 (T x) x) ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨r, hr⟩ := repr_of_mem_span b s x hx
  have hexp := expand_inner b ev T hTv s r x hr
  have hnorm := norm_sq_expand b s r x hr
  have h1 : C * ‖x‖ ^ 2 =
      ∑ j : ↥s, C * RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
    rw [hnorm, Finset.mul_sum]
  have h2 : RCLike.re (inner 𝕜 (T x) x) =
      ∑ j : ↥s, RCLike.re ((ev (j : Fin n) : 𝕜) *
        ((starRingEnd 𝕜) (r j) * r j)) := by
    rw [hexp, map_sum]
  rw [h2, h1]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw := weight_nonneg (r j)
  have hCj : ev (j : Fin n) ≤ C := hC _ j.property
  have hterm : RCLike.re ((ev (j : Fin n) : 𝕜) *
      ((starRingEnd 𝕜) (r j) * r j)) =
      ev (j : Fin n) * RCLike.re ((starRingEnd 𝕜) (r j) * r j) := by
    simp [RCLike.mul_re, RCLike.ofReal_re]
  rw [hterm]
  exact mul_le_mul_of_nonneg_right hCj hw

variable [FiniteDimensional 𝕜 E]

/-- Three subspaces whose finranks sum to `2n + 1` have a nonzero vector
in their common intersection. -/
private lemma exists_ne_zero_mem_inf_inf {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (S₁ S₂ S₃ : Submodule 𝕜 E)
    (hsum : Module.finrank 𝕜 S₁ + Module.finrank 𝕜 S₂ + Module.finrank 𝕜 S₃ = 2 * n + 1) :
    ∃ x : E, x ≠ 0 ∧ x ∈ S₁ ∧ x ∈ S₂ ∧ x ∈ S₃ := by
  have hle1 : Module.finrank 𝕜 ↥(S₁ ⊔ S₂) ≤ n := by
    calc Module.finrank 𝕜 ↥(S₁ ⊔ S₂)
        ≤ Module.finrank 𝕜 ↥(⊤ : Submodule 𝕜 E) := Submodule.finrank_mono le_top
      _ = Module.finrank 𝕜 E := Submodule.topEquiv.finrank_eq
      _ = n := hn
  have hle2 : Module.finrank 𝕜 ↥((S₁ ⊓ S₂) ⊔ S₃) ≤ n := by
    calc Module.finrank 𝕜 ↥((S₁ ⊓ S₂) ⊔ S₃)
        ≤ Module.finrank 𝕜 ↥(⊤ : Submodule 𝕜 E) := Submodule.finrank_mono le_top
      _ = Module.finrank 𝕜 E := Submodule.topEquiv.finrank_eq
      _ = n := hn
  have hform1 := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂
  have hform2 := Submodule.finrank_sup_add_finrank_inf_eq (S₁ ⊓ S₂) S₃
  have h1 : 1 ≤ Module.finrank 𝕜 ↥((S₁ ⊓ S₂) ⊓ S₃) := by omega
  have hne : (S₁ ⊓ S₂) ⊓ S₃ ≠ ⊥ := by
    intro hcon
    have h0 : Module.finrank 𝕜 ↥((S₁ ⊓ S₂) ⊓ S₃) = 0 := by
      rw [hcon]; exact finrank_bot _ _
    omega
  obtain ⟨x, hxm, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h12 := (Submodule.mem_inf.mp hxm).1
  have h3 := (Submodule.mem_inf.mp hxm).2
  have h1' := (Submodule.mem_inf.mp h12).1
  have h2' := (Submodule.mem_inf.mp h12).2
  exact ⟨x, hxn, h1', h2', h3⟩

/-- **Weyl's inequality (upper bound).** For self-adjoint operators `T, S`,
`λ_{a+b}(T + S) ≤ λ_a(T) + λ_b(S)` whenever `a + b < n`. -/
theorem weyl_eigenvalue_add_le {n : ℕ} {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a + b < n) :
    (hT.add hS).eigenvalues hn ⟨a + b, hab⟩ ≤
      hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩ := by
  -- Eigensystems of the three operators.
  set bC := (hT.add hS).eigenvectorBasis hn with hbC
  set bT := hT.eigenvectorBasis hn with hbT
  set bS := hS.eigenvectorBasis hn with hbS
  set evC := (hT.add hS).eigenvalues hn with hevC
  set evT := hT.eigenvalues hn with hevT
  set evS := hS.eigenvalues hn with hevS
  have hTvC : ∀ j, (T + S) (bC j) = (evC j : 𝕜) • bC j :=
    fun j => (hT.add hS).apply_eigenvectorBasis hn j
  have hTvT : ∀ j, T (bT j) = (evT j : 𝕜) • bT j :=
    fun j => hT.apply_eigenvectorBasis hn j
  have hTvS : ∀ j, S (bS j) = (evS j : 𝕜) • bS j :=
    fun j => hS.apply_eigenvectorBasis hn j
  have hantiC : Antitone evC := (hT.add hS).eigenvalues_antitone hn
  have hantiT : Antitone evT := hT.eigenvalues_antitone hn
  have hantiS : Antitone evS := hS.eigenvalues_antitone hn
  -- The three index sets: head of `T + S`, tails of `T` and `S`.
  set sC : Finset (Fin n) := Finset.Iic ⟨a + b, hab⟩ with hsC
  set sT : Finset (Fin n) := Finset.Ici ⟨a, ha⟩ with hsT
  set sS : Finset (Fin n) := Finset.Ici ⟨b, hb⟩ with hsS
  have hcardC : sC.card = a + b + 1 := by rw [hsC]; exact Fin.card_Iic _
  have hcardT : sT.card = n - a := by rw [hsT]; exact Fin.card_Ici _
  have hcardS : sS.card = n - b := by rw [hsS]; exact Fin.card_Ici _
  set SC : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sC => bC (j : Fin n))) with hSC
  set ST : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sT => bT (j : Fin n))) with hST
  set SS : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sS => bS (j : Fin n))) with hSS
  have hsum : Module.finrank 𝕜 SC + Module.finrank 𝕜 ST + Module.finrank 𝕜 SS
      = 2 * n + 1 := by
    rw [hSC, hST, hSS, finrank_span_basis bC sC, finrank_span_basis bT sT,
      finrank_span_basis bS sS, hcardC, hcardT, hcardS]
    omega
  obtain ⟨x, hxn, hxC, hxT, hxS⟩ := exists_ne_zero_mem_inf_inf hn SC ST SS hsum
  -- Rayleigh bounds on the three spans.
  have hC : evC ⟨a + b, hab⟩ * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 ((T + S) x) x) := by
    apply re_inner_ge_of_mem_span bC evC (T + S) hTvC sC _ x hxC
    intro j hj
    apply hantiC
    rw [Finset.mem_Iic] at hj
    exact hj
  have hTle : RCLike.re (inner 𝕜 (T x) x) ≤ evT ⟨a, ha⟩ * ‖x‖ ^ 2 := by
    apply re_inner_le_of_mem_span bT evT T hTvT sT _ x hxT
    intro j hj
    apply hantiT
    rw [Finset.mem_Ici] at hj
    exact hj
  have hSle : RCLike.re (inner 𝕜 (S x) x) ≤ evS ⟨b, hb⟩ * ‖x‖ ^ 2 := by
    apply re_inner_le_of_mem_span bS evS S hTvS sS _ x hxS
    intro j hj
    apply hantiS
    rw [Finset.mem_Ici] at hj
    exact hj
  have hsplit : RCLike.re (inner 𝕜 ((T + S) x) x) =
      RCLike.re (inner 𝕜 (T x) x) + RCLike.re (inner 𝕜 (S x) x) := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxn) 2
  have hchain : evC ⟨a + b, hab⟩ * ‖x‖ ^ 2 ≤
      (evT ⟨a, ha⟩ + evS ⟨b, hb⟩) * ‖x‖ ^ 2 := by
    rw [hsplit] at hC
    have : (evT ⟨a, ha⟩ + evS ⟨b, hb⟩) * ‖x‖ ^ 2 =
        evT ⟨a, ha⟩ * ‖x‖ ^ 2 + evS ⟨b, hb⟩ * ‖x‖ ^ 2 := by ring
    rw [this]
    linarith
  exact le_of_mul_le_mul_right hchain hpos

/-- **Weyl's inequality (lower bound).** For self-adjoint operators `T, S`,
`λ_a(T) + λ_b(S) ≤ λ_{a+b-(n-1)}(T + S)` whenever `n - 1 ≤ a + b`. -/
theorem le_weyl_eigenvalue_add {n : ℕ} {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : n - 1 ≤ a + b) :
    hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩ ≤
      (hT.add hS).eigenvalues hn ⟨a + b - (n - 1), by omega⟩ := by
  set bC := (hT.add hS).eigenvectorBasis hn with hbC
  set bT := hT.eigenvectorBasis hn with hbT
  set bS := hS.eigenvectorBasis hn with hbS
  set evC := (hT.add hS).eigenvalues hn with hevC
  set evT := hT.eigenvalues hn with hevT
  set evS := hS.eigenvalues hn with hevS
  have hTvC : ∀ j, (T + S) (bC j) = (evC j : 𝕜) • bC j :=
    fun j => (hT.add hS).apply_eigenvectorBasis hn j
  have hTvT : ∀ j, T (bT j) = (evT j : 𝕜) • bT j :=
    fun j => hT.apply_eigenvectorBasis hn j
  have hTvS : ∀ j, S (bS j) = (evS j : 𝕜) • bS j :=
    fun j => hS.apply_eigenvectorBasis hn j
  have hantiC : Antitone evC := (hT.add hS).eigenvalues_antitone hn
  have hantiT : Antitone evT := hT.eigenvalues_antitone hn
  have hantiS : Antitone evS := hS.eigenvalues_antitone hn
  -- The three index sets: tail of `T + S`, heads of `T` and `S`.
  have hk : a + b - (n - 1) < n := by omega
  set sC : Finset (Fin n) := Finset.Ici ⟨a + b - (n - 1), hk⟩ with hsC
  set sT : Finset (Fin n) := Finset.Iic ⟨a, ha⟩ with hsT
  set sS : Finset (Fin n) := Finset.Iic ⟨b, hb⟩ with hsS
  have hcardC : sC.card = n - (a + b - (n - 1)) := by rw [hsC]; exact Fin.card_Ici _
  have hcardT : sT.card = a + 1 := by rw [hsT]; exact Fin.card_Iic _
  have hcardS : sS.card = b + 1 := by rw [hsS]; exact Fin.card_Iic _
  set SC : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sC => bC (j : Fin n))) with hSC
  set ST : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sT => bT (j : Fin n))) with hST
  set SS : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (fun j : ↥sS => bS (j : Fin n))) with hSS
  have hsum : Module.finrank 𝕜 SC + Module.finrank 𝕜 ST + Module.finrank 𝕜 SS
      = 2 * n + 1 := by
    rw [hSC, hST, hSS, finrank_span_basis bC sC, finrank_span_basis bT sT,
      finrank_span_basis bS sS, hcardC, hcardT, hcardS]
    omega
  obtain ⟨x, hxn, hxC, hxT, hxS⟩ := exists_ne_zero_mem_inf_inf hn SC ST SS hsum
  -- Rayleigh bounds on the three spans.
  have hCle : RCLike.re (inner 𝕜 ((T + S) x) x) ≤
      evC ⟨a + b - (n - 1), hk⟩ * ‖x‖ ^ 2 := by
    apply re_inner_le_of_mem_span bC evC (T + S) hTvC sC _ x hxC
    intro j hj
    apply hantiC
    rw [Finset.mem_Ici] at hj
    exact hj
  have hTge : evT ⟨a, ha⟩ * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
    apply re_inner_ge_of_mem_span bT evT T hTvT sT _ x hxT
    intro j hj
    apply hantiT
    rw [Finset.mem_Iic] at hj
    exact hj
  have hSge : evS ⟨b, hb⟩ * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (S x) x) := by
    apply re_inner_ge_of_mem_span bS evS S hTvS sS _ x hxS
    intro j hj
    apply hantiS
    rw [Finset.mem_Iic] at hj
    exact hj
  have hsplit : RCLike.re (inner 𝕜 ((T + S) x) x) =
      RCLike.re (inner 𝕜 (T x) x) + RCLike.re (inner 𝕜 (S x) x) := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxn) 2
  have hchain : (evT ⟨a, ha⟩ + evS ⟨b, hb⟩) * ‖x‖ ^ 2 ≤
      evC ⟨a + b - (n - 1), hk⟩ * ‖x‖ ^ 2 := by
    rw [hsplit] at hCle
    have hdist : (evT ⟨a, ha⟩ + evS ⟨b, hb⟩) * ‖x‖ ^ 2 =
        evT ⟨a, ha⟩ * ‖x‖ ^ 2 + evS ⟨b, hb⟩ * ‖x‖ ^ 2 := by ring
    rw [hdist]
    linarith
  have hgoal : (evT ⟨a, ha⟩ + evS ⟨b, hb⟩) * ‖x‖ ^ 2 ≤
      evC ⟨a + b - (n - 1), by omega⟩ * ‖x‖ ^ 2 := hchain
  exact le_of_mul_le_mul_right hgoal hpos

/-- Eigenvalues are unchanged when the operator is replaced by an equal
operator (proofs of symmetry are irrelevant). -/
private lemma eigenvalues_congr {n : ℕ} {T S : E →ₗ[𝕜] E} (h : T = S)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    hT.eigenvalues hn = hS.eigenvalues hn := by
  subst h
  rfl

section Matrix

open Matrix

/-- **Weyl's inequality (upper bound), matrix form.** For Hermitian matrices
`A, B`, `λ_{a+b}(A + B) ≤ λ_a(A) + λ_b(B)` whenever `a + b < n`. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_add_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a + b < n) :
    _root_.Matrix.IsHermitian.eigenvalues₀ (_root_.Matrix.IsHermitian.add hA hB)
        ⟨a + b, by simpa using hab⟩ ≤
      _root_.Matrix.IsHermitian.eigenvalues₀ hA ⟨a, by simpa using ha⟩ +
        _root_.Matrix.IsHermitian.eigenvalues₀ hB ⟨b, by simpa using hb⟩ := by
  show (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (_root_.Matrix.IsHermitian.add hA hB)).eigenvalues
      finrank_euclideanSpace ⟨a + b, by simpa using hab⟩ ≤ _
  have hmap : Matrix.toEuclideanLin (A + B) =
      Matrix.toEuclideanLin A + Matrix.toEuclideanLin B := map_add _ _ _
  have hce := eigenvalues_congr (E := EuclideanSpace 𝕜 (Fin n)) hmap
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (_root_.Matrix.IsHermitian.add hA hB))
    (LinearMap.IsSymmetric.add (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB))
    finrank_euclideanSpace
  rw [hce]
  exact weyl_eigenvalue_add_le
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (by simpa using ha) (by simpa using hb)
    (by simpa using hab)

/-- **Weyl's inequality (lower bound), matrix form.** For Hermitian matrices
`A, B`, `λ_a(A) + λ_b(B) ≤ λ_{a+b-(n-1)}(A + B)` whenever `n - 1 ≤ a + b`. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues₀_add {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : n - 1 ≤ a + b) :
    _root_.Matrix.IsHermitian.eigenvalues₀ hA ⟨a, by simpa using ha⟩ +
        _root_.Matrix.IsHermitian.eigenvalues₀ hB ⟨b, by simpa using hb⟩ ≤
      _root_.Matrix.IsHermitian.eigenvalues₀ (_root_.Matrix.IsHermitian.add hA hB)
        ⟨a + b - (n - 1), by simpa using (by omega : a + b - (n - 1) < n)⟩ := by
  show _ ≤ (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (_root_.Matrix.IsHermitian.add hA hB)).eigenvalues
      finrank_euclideanSpace ⟨a + b - (n - 1), by simpa using
        (by omega : a + b - (n - 1) < n)⟩
  have hmap : Matrix.toEuclideanLin (A + B) =
      Matrix.toEuclideanLin A + Matrix.toEuclideanLin B := map_add _ _ _
  have hce := eigenvalues_congr (E := EuclideanSpace 𝕜 (Fin n)) hmap
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (_root_.Matrix.IsHermitian.add hA hB))
    (LinearMap.IsSymmetric.add (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB))
    finrank_euclideanSpace
  rw [hce]
  have hle := le_weyl_eigenvalue_add
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (by simpa using ha) (by simpa using hb)
    (by simpa using hab)
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hidx : (⟨a + b - (n - 1), by simpa using
        (by omega : a + b - (n - 1) < n)⟩ : Fin (Fintype.card (Fin n))) =
      ⟨a + b - (Fintype.card (Fin n) - 1), by omega⟩ := by
    apply Fin.ext
    simp [Fintype.card_fin]
  rw [hidx]
  exact hle

/-- Eigenvalues are unchanged when the matrix is replaced by an equal
matrix (useful to transport eigenvalue computations along identities such
as `diagonal d₁ + diagonal d₂ = diagonal (d₁ + d₂)`). -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_congr {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    _root_.Matrix.IsHermitian.eigenvalues₀ hA = _root_.Matrix.IsHermitian.eigenvalues₀ hB := by
  subst h
  rfl

/-- The eigenvalues of a diagonal Hermitian matrix whose diagonal entries
are already in decreasing order are exactly those entries. -/
theorem isSelfAdjoint_ofReal_fun {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (d : Fin n → ℝ) : IsSelfAdjoint (fun i => (d i : 𝕜)) := by
  funext i
  rw [Pi.star_apply, RCLike.star_def]
  exact RCLike.conj_ofReal _

private lemma heq_apply {m n : ℕ} {f : Fin m → ℝ} {g : Fin n → ℝ} (h : HEq f g)
    (hmn : m = n) (i : Fin m) : f i = g (Fin.cast hmn i) := by
  subst hmn
  exact congrFun (eq_of_heq h) i

theorem _root_.Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone {n : ℕ}
    {d : Fin n → ℝ} (hd : Antitone d) (i : Fin (Fintype.card (Fin n))) :
    _root_.Matrix.IsHermitian.eigenvalues₀
        (Matrix.isHermitian_diagonal_of_self_adjoint (fun i => (d i : 𝕜))
          (isSelfAdjoint_ofReal_fun d)) i =
      d ⟨i.val, by simpa using i.isLt⟩ := by
  classical
  set hD := Matrix.isHermitian_diagonal_of_self_adjoint (fun i => (d i : 𝕜))
    (isSelfAdjoint_ofReal_fun d) with hhD
  have hsort := _root_.Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hD
  have hroots : (Matrix.diagonal (fun i => (d i : 𝕜))).charpoly.roots.map
      RCLike.re = Finset.univ.val.map d := by
    rw [Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by
        refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
        exact Polynomial.X_sub_C_ne_zero _)]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def, RCLike.ofReal_re]
  rw [hroots] at hsort
  have hperm : List.Perm ((Finset.univ.val.map d).sort (· ≥ ·)) (List.ofFn d) := by
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq]
    exact Fin.univ_val_map d
  have hsorted1 : List.SortedGE ((Finset.univ.val.map d).sort (· ≥ ·)) :=
    (Multiset.pairwise_sort _ _).sortedGE
  have hsorted2 : List.SortedGE (List.ofFn d) := hd.sortedGE_ofFn
  have hsort_eq : (Finset.univ.val.map d).sort (· ≥ ·) = List.ofFn d :=
    List.Perm.eq_of_sortedGE hsorted1 hsorted2 hperm
  have hlist : List.ofFn
      (_root_.Matrix.IsHermitian.eigenvalues₀ hD) = List.ofFn d :=
    hsort.symm.trans hsort_eq
  obtain ⟨hcard, hHEq⟩ :=
    Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp hlist)
  have hpt := heq_apply hHEq hcard i
  rw [hpt]
  congr 1

end Matrix

end MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum

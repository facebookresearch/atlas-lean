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

import MathlibExt.Analysis.InnerProductSpace.CourantFischer
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
nonzero vector. The public head/tail span finrank and Rayleigh-form
bounds in `CourantFischer.lean` then give the inequality.

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
open MathlibExt.Analysis.InnerProductSpace.CourantFischer

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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
  set SC : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (headFamily (hT.add hS) hn hab)) with hSC
  set ST : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (tailFamily hT hn ha)) with hST
  set SS : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (tailFamily hS hn hb)) with hSS
  have hsum : Module.finrank 𝕜 SC + Module.finrank 𝕜 ST + Module.finrank 𝕜 SS
      = 2 * n + 1 := by
    rw [hSC, hST, hSS, finrank_span_headFamily (hT.add hS) hn hab,
      finrank_span_tailFamily hT hn ha, finrank_span_tailFamily hS hn hb]
    omega
  obtain ⟨x, hxn, hxC, hxT, hxS⟩ := exists_ne_zero_mem_inf_inf hn SC ST SS hsum
  have hC := rayleighForm_ge_of_mem_head (hT.add hS) hn hab hxC
  have hTle := rayleighForm_le_of_mem_tail hT hn ha hxT
  have hSle := rayleighForm_le_of_mem_tail hS hn hb hxS
  simp only [rayleighForm] at hC hTle hSle
  have hsplit : RCLike.re (inner 𝕜 ((T + S) x) x) =
      RCLike.re (inner 𝕜 (T x) x) + RCLike.re (inner 𝕜 (S x) x) := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxn) 2
  have hchain : (hT.add hS).eigenvalues hn ⟨a + b, hab⟩ * ‖x‖ ^ 2 ≤
      (hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩) * ‖x‖ ^ 2 := by
    rw [hsplit] at hC
    have : (hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩) * ‖x‖ ^ 2 =
        hT.eigenvalues hn ⟨a, ha⟩ * ‖x‖ ^ 2 + hS.eigenvalues hn ⟨b, hb⟩ * ‖x‖ ^ 2 := by ring
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
  have hk : a + b - (n - 1) < n := by omega
  set SC : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (tailFamily (hT.add hS) hn hk)) with hSC
  set ST : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (headFamily hT hn ha)) with hST
  set SS : Submodule 𝕜 E :=
    Submodule.span 𝕜 (Set.range (headFamily hS hn hb)) with hSS
  have hsum : Module.finrank 𝕜 SC + Module.finrank 𝕜 ST + Module.finrank 𝕜 SS
      = 2 * n + 1 := by
    rw [hSC, hST, hSS, finrank_span_tailFamily (hT.add hS) hn hk,
      finrank_span_headFamily hT hn ha, finrank_span_headFamily hS hn hb]
    omega
  obtain ⟨x, hxn, hxC, hxT, hxS⟩ := exists_ne_zero_mem_inf_inf hn SC ST SS hsum
  have hCle := rayleighForm_le_of_mem_tail (hT.add hS) hn hk hxC
  have hTge := rayleighForm_ge_of_mem_head hT hn ha hxT
  have hSge := rayleighForm_ge_of_mem_head hS hn hb hxS
  simp only [rayleighForm] at hCle hTge hSge
  have hsplit : RCLike.re (inner 𝕜 ((T + S) x) x) =
      RCLike.re (inner 𝕜 (T x) x) + RCLike.re (inner 𝕜 (S x) x) := by
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxn) 2
  have hchain : (hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩) * ‖x‖ ^ 2 ≤
      (hT.add hS).eigenvalues hn ⟨a + b - (n - 1), hk⟩ * ‖x‖ ^ 2 := by
    rw [hsplit] at hCle
    have hdist : (hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩) * ‖x‖ ^ 2 =
        hT.eigenvalues hn ⟨a, ha⟩ * ‖x‖ ^ 2 + hS.eigenvalues hn ⟨b, hb⟩ * ‖x‖ ^ 2 := by ring
    rw [hdist]
    linarith
  have hgoal : (hT.eigenvalues hn ⟨a, ha⟩ + hS.eigenvalues hn ⟨b, hb⟩) * ‖x‖ ^ 2 ≤
      (hT.add hS).eigenvalues hn ⟨a + b - (n - 1), by omega⟩ * ‖x‖ ^ 2 := hchain
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

private theorem isSelfAdjoint_ofReal_fun {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (d : Fin n → ℝ) : IsSelfAdjoint (fun i => (d i : 𝕜)) := by
  funext i
  rw [Pi.star_apply, RCLike.star_def]
  exact RCLike.conj_ofReal _

private lemma heq_apply {m n : ℕ} {f : Fin m → ℝ} {g : Fin n → ℝ} (h : HEq f g)
    (hmn : m = n) (i : Fin m) : f i = g (Fin.cast hmn i) := by
  subst hmn
  exact congrFun (eq_of_heq h) i

/-- The eigenvalues of a diagonal Hermitian matrix whose diagonal entries
are already in decreasing order are exactly those entries. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone {n : ℕ}
    {d : Fin n → ℝ} (hd : Antitone d) (i : Fin (Fintype.card (Fin n))) :
    _root_.Matrix.IsHermitian.eigenvalues₀
        (Matrix.isHermitian_diagonal_of_self_adjoint (fun i => (d i : 𝕜))
          (by
            funext j
            rw [Pi.star_apply, RCLike.star_def]
            exact RCLike.conj_ofReal _)) i =
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

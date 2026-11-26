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

public import MathlibExt.LinearAlgebra.MatrixSpace.Wong
public import MathlibExt.LinearAlgebra.MatrixSpace.Blowup
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Push

/-!
# Escaping chains in the second Wong sequence

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) with f ∈ B and u ∈ U. If Wₖ
⊆ im A but Wₖ₊₁ is not contained in im A, there are C₀,…,Cₖ ∈ B and v₀,…,vₖ ∈ V with Av₀ = 0,
Avᵢ₊₁ = Cᵢvᵢ, and Cₖvₖ outside im A. For finite-dimensional W, failure of stable containment
gives k ≤ rank A. For a square blow-up and rank A = r|D| with D nonempty, k ≤ r; Kronecker
shift matrices lift the chain to A ⊗ I_q for q > r.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Non-commutative Edmonds' problem and
matrix semi-invariants*, §2.2 and Algorithm 2, lines 9–12.
-/

@[expose] public section

universe u v w z

namespace LinearMap

variable {K : Type u} [Field K] {V : Type v} {W : Type w}
variable [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

private theorem exists_range_section (A : V →ₗ[K] W) :
    ∃ P : W →ₗ[K] V, ∀ w ∈ A.range, A (P w) = w := by
  classical
  obtain ⟨s, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  refine ⟨s.comp A.range.subtype.leftInverse, ?_⟩
  intro w hw
  have hl : A.range.subtype.leftInverse w = (⟨w, hw⟩ : A.range) :=
    leftInverse_apply_of_inj A.range.ker_subtype ⟨w, hw⟩
  change A (s (A.range.subtype.leftInverse w)) = w
  rw [hl]
  exact congrArg (fun y : A.range => (y : W)) (LinearMap.congr_fun hs ⟨w, hw⟩)

private theorem exists_observed_wong_chain {T : Type z} [AddCommGroup T] [Module K T]
    (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W))
    (P : W →ₗ[K] V) (hP : ∀ w ∈ A.range, A (P w) = w) (k : ℕ) (F : W →ₗ[K] T)
    (hRange : secondWongSeq A B k ≤ A.range)
    (hZero : secondWongSeq A B k ≤ F.ker)
    (hNonzero : ¬secondWongSeq A B (k + 1) ≤ F.ker) :
    ∃ (C : Fin (k + 1) → B) (v : Fin (k + 1) → V),
      A (v 0) = 0 ∧
      (∀ i : Fin k, A (v i.succ) = (C i.castSucc : V →ₗ[K] W) (v i.castSucc)) ∧
      (∀ i : Fin (k + 1), v i ∈ (secondWongSeq A B i.val).comap A) ∧
      F ((C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k))) ≠ 0 := by
  classical
  induction k generalizing F with
  | zero =>
    simp only [secondWongSeq_succ, secondWongSeq_zero, Submodule.comap_bot,
      Submodule.map₂_le, LinearMap.id_apply, LinearMap.mem_ker] at hNonzero
    push Not at hNonzero
    obtain ⟨D, hD, x, hx, hFx⟩ := hNonzero
    refine ⟨fun _ => ⟨D, hD⟩, fun _ => x, hx, ?_, ?_, hFx⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      have hi : i.val = 0 := by have h := i.isLt; omega
      change A x ∈ secondWongSeq A B i.val
      rw [hi, secondWongSeq_zero]
      simpa only [Submodule.mem_bot] using hx
  | succ k ih =>
    simp only [secondWongSeq_succ, Submodule.map₂_le, LinearMap.id_apply,
      LinearMap.mem_ker] at hNonzero
    push Not at hNonzero
    obtain ⟨D, hD, x, hx, hFx⟩ := hNonzero
    let w := A x
    have hw : w ∈ secondWongSeq A B (k + 1) := hx
    have hAP : A (P w) = w := hP w (hRange hw)
    have hkernel : x - P w ∈ A.ker := by
      rw [mem_ker, map_sub, hAP]
      exact sub_self _
    have hW1 : D (x - P w) ∈ secondWongSeq A B 1 := by
      rw [secondWongSeq_one]
      exact Submodule.apply_mem_map₂ LinearMap.id hD hkernel
    have hkill : F (D (x - P w)) = 0 :=
      mem_ker.mp (hZero ((secondWongSeq_monotone A B (Nat.succ_le_succ (Nat.zero_le k))) hW1))
    have hobs : F (D (P w)) ≠ 0 := by
      have heq : F (D x) = F (D (P w)) := sub_eq_zero.mp (by simpa only [map_sub] using hkill)
      exact fun h => hFx (heq.trans h)
    let L : W →ₗ[K] T := F.comp (D.comp P)
    have hRange' : secondWongSeq A B k ≤ A.range :=
      (secondWongSeq_monotone A B (Nat.le_succ k)).trans hRange
    have hLzero : secondWongSeq A B k ≤ L.ker := by
      intro y hy
      have hAy : A (P y) = y := hP y (hRange' hy)
      have hPy : P y ∈ (secondWongSeq A B k).comap A := by
        change A (P y) ∈ secondWongSeq A B k
        rwa [hAy]
      have hDy : D (P y) ∈ secondWongSeq A B (k + 1) := by
        rw [secondWongSeq_succ]
        exact Submodule.apply_mem_map₂ LinearMap.id hD hPy
      exact mem_ker.mpr (mem_ker.mp (hZero hDy))
    have hLnonzero : ¬secondWongSeq A B (k + 1) ≤ L.ker := by
      intro h
      exact hobs (mem_ker.mp (h hw))
    obtain ⟨C, v, h0, hstep, hmem, hlast⟩ := ih L hRange' hLzero hLnonzero
    let lastV := P ((C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)))
    have hout : (C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)) ∈
        secondWongSeq A B (k + 1) := by
      rw [secondWongSeq_succ]
      exact Submodule.apply_mem_map₂ LinearMap.id (C (Fin.last k)).2 (hmem (Fin.last k))
    have hlift : A lastV = (C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)) :=
      hP _ (hRange hout)
    refine ⟨Fin.snoc C ⟨D, hD⟩, Fin.snoc v lastV, ?_, ?_, ?_, ?_⟩
    · simpa only [Fin.snoc_apply_zero] using h0
    · intro i
      cases i using Fin.lastCases with
      | last =>
        rw [show (Fin.last k).succ = Fin.last (k + 1) from rfl, Fin.snoc_last]
        simpa only [Fin.snoc_castSucc] using hlift
      | cast i => simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using hstep i
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.val_last]
        change A lastV ∈ secondWongSeq A B (k + 1)
        rwa [hlift]
      | cast i => simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using hmem i
    · simpa only [Fin.snoc_last, L, lastV, LinearMap.comp_apply] using hlast

/-- **A chain from the first escaping Wong step.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) with f ∈ B and u ∈ U. Assume
Wₖ ⊆ im A and Wₖ₊₁ is not contained in im A. Then there exist C₀,…,Cₖ ∈ B and v₀,…,vₖ ∈ V such
that Av₀ = 0, Avᵢ₊₁ = Cᵢvᵢ for i < k, Avᵢ ∈ Wᵢ for i ≤ k, and Cₖvₖ ∉ im A.
-/
theorem exists_secondWongSeq_escape_chain (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W))
    (k : ℕ) (hRange : secondWongSeq A B k ≤ A.range)
    (hExit : ¬secondWongSeq A B (k + 1) ≤ A.range) :
    ∃ (C : Fin (k + 1) → B) (v : Fin (k + 1) → V),
      A (v 0) = 0 ∧
      (∀ i : Fin k, A (v i.succ) = (C i.castSucc : V →ₗ[K] W) (v i.castSucc)) ∧
      (∀ i : Fin (k + 1), v i ∈ (secondWongSeq A B i.val).comap A) ∧
      (C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)) ∉ A.range := by
  obtain ⟨P, hP⟩ := exists_range_section A
  let F := A.range.mkQ
  have hZero : secondWongSeq A B k ≤ F.ker := by
    rwa [Submodule.ker_mkQ]
  have hNonzero : ¬secondWongSeq A B (k + 1) ≤ F.ker := by
    rwa [Submodule.ker_mkQ]
  obtain ⟨C, v, h0, hstep, hmem, hlast⟩ :=
    exists_observed_wong_chain A B P hP k F hRange hZero hNonzero
  refine ⟨C, v, h0, hstep, hmem, ?_⟩
  intro hy
  apply hlast
  exact mem_ker.mp (show (C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)) ∈ F.ker by
    rwa [Submodule.ker_mkQ])

private theorem stable_of_contained_multiple [FiniteDimensional K W]
    (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) (δ r : ℕ) (hδ : 0 < δ)
    (hRank : Module.finrank K A.range = r * δ)
    (hDim : ∀ j, δ ∣ Module.finrank K (secondWongSeq A B j))
    (hRange : secondWongSeq A B (r + 1) ≤ A.range) :
    secondWongSeq A B (r + 1) = secondWongSeq A B r := by
  by_contra hlast
  have hneq : ∀ j, j ≤ r → secondWongSeq A B (j + 1) ≠ secondWongSeq A B j := by
    intro j hj heq
    have hconst : ∀ m, j ≤ m → secondWongSeq A B m = secondWongSeq A B j := by
      intro m hm
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact secondWongSeq_add_eq_of_eq_succ A B heq t
    exact hlast ((hconst (r + 1) (hj.trans (Nat.le_succ r))).trans (hconst r hj).symm)
  have hdim : ∀ j, j ≤ r + 1 → j * δ ≤ Module.finrank K (secondWongSeq A B j) := by
    intro j
    induction j with
    | zero => intro _; simp only [Nat.zero_mul, Nat.zero_le]
    | succ j ih =>
      intro hj
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (secondWongSeq_le_succ A B j)
          (Ne.symm (hneq j (Nat.le_of_succ_le_succ hj))))
      obtain ⟨a, ha⟩ := hDim j
      obtain ⟨b, hb⟩ := hDim (j + 1)
      have hab : a < b := by
        rw [ha, hb] at hlt
        exact lt_of_mul_lt_mul_left hlt (Nat.zero_le δ)
      have hgrow : Module.finrank K (secondWongSeq A B j) + δ ≤
          Module.finrank K (secondWongSeq A B (j + 1)) := by
        rw [ha, hb]
        simpa only [Nat.succ_eq_add_one, mul_add, mul_one] using
          Nat.mul_le_mul_left δ (Nat.succ_le_of_lt hab)
      calc
        (j + 1) * δ = j * δ + δ := by simp only [add_mul, one_mul]
        _ ≤ Module.finrank K (secondWongSeq A B j) + δ :=
          Nat.add_le_add_right (ih (Nat.le_of_succ_le hj)) δ
        _ ≤ Module.finrank K (secondWongSeq A B (j + 1)) := hgrow
  have hmul : (r + 1) * δ ≤ r * δ :=
    ((hdim (r + 1) le_rfl).trans (Submodule.finrank_mono hRange)).trans_eq hRank
  exact Nat.not_succ_le_self r (le_of_mul_le_mul_right hmul hδ)

private theorem limit_contained_of_contained_multiple [FiniteDimensional K W]
    (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W)) (δ r : ℕ) (hδ : 0 < δ)
    (hRank : Module.finrank K A.range = r * δ)
    (hDim : ∀ j, δ ∣ Module.finrank K (secondWongSeq A B j))
    (hRange : secondWongSeq A B (r + 1) ≤ A.range) : secondWongLimit A B ≤ A.range := by
  have heq := stable_of_contained_multiple A B δ r hδ hRank hDim hRange
  have hpref : Submodule.map₂ LinearMap.id B ((secondWongSeq A B r).comap A) ≤
      secondWongSeq A B r := heq.le
  exact (secondWongSeq_le_of_prefixed A B hpref _).trans
    ((secondWongSeq_monotone A B (Nat.le_succ r)).trans hRange)

private theorem exists_first_exit_index (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W))
    (j : ℕ) (hExit : ¬secondWongSeq A B j ≤ A.range) :
    ∃ k, k < j ∧ secondWongSeq A B k ≤ A.range ∧
      ¬secondWongSeq A B (k + 1) ≤ A.range := by
  induction j with
  | zero => exact False.elim (hExit bot_le)
  | succ j ih =>
    by_cases hprev : secondWongSeq A B j ≤ A.range
    · exact ⟨j, Nat.lt_succ_self j, hprev, hExit⟩
    · obtain ⟨k, hk, hprev, hexit⟩ := ih hprev
      exact ⟨k, hk.trans (Nat.lt_succ_self j), hprev, hexit⟩

/-- **An escaping chain bounded by the starting rank.**

Let K be a field, V,W K-vector spaces, A : V → W linear and B a subspace of linear maps V → W.
Define W₀ = 0 and Wⱼ₊₁ = B(A⁻¹Wⱼ), where B(U) is the span of f(u) with f ∈ B and u ∈ U. Assume
W is finite-dimensional and the stable value W∞ is not contained in im A. There exist k ≤ rank
A, C₀,…,Cₖ ∈ B and v₀,…,vₖ ∈ V with Av₀ = 0, Avᵢ₊₁ = Cᵢvᵢ for i < k, Avᵢ ∈ Wᵢ, and Cₖvₖ ∉ im
A.
-/
theorem exists_secondWongLimit_escape_chain [FiniteDimensional K W]
    (A : V →ₗ[K] W) (B : Submodule K (V →ₗ[K] W))
    (hExit : ¬secondWongLimit A B ≤ A.range) :
    ∃ (k : ℕ), k ≤ Module.finrank K A.range ∧
      ∃ (C : Fin (k + 1) → B) (v : Fin (k + 1) → V),
        A (v 0) = 0 ∧
        (∀ i : Fin k, A (v i.succ) = (C i.castSucc : V →ₗ[K] W) (v i.castSucc)) ∧
        (∀ i : Fin (k + 1), v i ∈ (secondWongSeq A B i.val).comap A) ∧
        (C (Fin.last k) : V →ₗ[K] W) (v (Fin.last k)) ∉ A.range := by
  have hnext : ¬secondWongSeq A B (Module.finrank K A.range + 1) ≤ A.range := by
    intro h
    exact hExit (limit_contained_of_contained_multiple A B 1 (Module.finrank K A.range)
      (by decide) (by simp only [mul_one]) (fun _ => one_dvd _) h)
  obtain ⟨k, hk, hprev, hexit⟩ := exists_first_exit_index A B _ hnext
  exact ⟨k, Nat.le_of_lt_succ hk, exists_secondWongSeq_escape_chain A B k hprev hexit⟩

end LinearMap

namespace Matrix

variable {K : Type u} [Field K] {n : Type v} {d : Type w}
variable [Fintype n] [Fintype d]

/-- **Divisibility of blow-up Wong dimensions.**

Let K be a field, N,D finite index types and B ⊆ Mat(N,N;K) a subspace. Put E = B^[D] = span{X
⊗ T : X ∈ B, T ∈ Mat(D,D;K)} and let A be a matrix on N × D. Define W₀ = 0 and Wⱼ₊₁ =
E(A⁻¹Wⱼ). For every j, the dimension of Wⱼ is divisible by |D|.
-/
theorem secondWongSeq_blowup_finrank_dvd (A : Matrix (n × d) (n × d) K)
    (B : Submodule K (Matrix n n K)) (j : ℕ) :
    Fintype.card d ∣ Module.finrank K
      (LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) j) := by
  cases j with
  | zero =>
    rw [LinearMap.secondWongSeq_zero, finrank_bot]
    exact dvd_zero (Fintype.card d)
  | succ j =>
    rw [LinearMap.secondWongSeq_succ, Submodule.map₂_map_left, LinearMap.id_comp,
      kroneckerBlowup_image, Submodule.finrank_columnAmplification]
    exact ⟨_, mul_comm _ _⟩

/-- **A stabilization bound inside a blow-up range.**

Let K be a field, N,D finite index types and B ⊆ Mat(N,N;K) a subspace. Put E = B^[D] = span{X
⊗ T : X ∈ B, T ∈ Mat(D,D;K)} and let A be a matrix on N × D. Define W₀ = 0 and Wⱼ₊₁ =
E(A⁻¹Wⱼ). Assume D is nonempty, rank A = r|D| and Wᵣ₊₁ ⊆ im A. Then Wᵣ₊₁ = Wᵣ.
-/
theorem secondWongSeq_blowup_stable_of_contained [Nonempty d]
    (A : Matrix (n × d) (n × d) K) (B : Submodule K (Matrix n n K)) (r : ℕ)
    (hRank : A.rank = r * Fintype.card d)
    (hRange : LinearMap.secondWongSeq A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (r + 1) ≤ A.mulVecLin.range) :
    LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (r + 1) =
      LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) r :=
  LinearMap.stable_of_contained_multiple A.mulVecLin
    ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (Fintype.card d) r
    Fintype.card_pos hRank (secondWongSeq_blowup_finrank_dvd A B) hRange

/-- **The first blow-up exit occurs within the rank bound.**

Let K be a field, N,D finite index types and B ⊆ Mat(N,N;K) a subspace. Put E = B^[D] = span{X
⊗ T : X ∈ B, T ∈ Mat(D,D;K)} and let A be a matrix on N × D. Define W₀ = 0 and Wⱼ₊₁ =
E(A⁻¹Wⱼ). Assume D is nonempty, rank A = r|D| and W∞ is not contained in im A. There exists k
≤ r with Wₖ ⊆ im A but Wₖ₊₁ not contained in im A.
-/
theorem exists_secondWongSeq_blowup_first_exit [Nonempty d]
    (A : Matrix (n × d) (n × d) K) (B : Submodule K (Matrix n n K)) (r : ℕ)
    (hRank : A.rank = r * Fintype.card d)
    (hExit : ¬LinearMap.secondWongLimit A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) ≤ A.mulVecLin.range) :
    ∃ k, k ≤ r ∧
      LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) k ≤ A.mulVecLin.range ∧
      ¬LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (k + 1) ≤ A.mulVecLin.range := by
  have hnext : ¬LinearMap.secondWongSeq A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (r + 1) ≤ A.mulVecLin.range := by
    intro h
    exact hExit (LinearMap.limit_contained_of_contained_multiple A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (Fintype.card d) r
      Fintype.card_pos hRank (secondWongSeq_blowup_finrank_dvd A B) h)
  obtain ⟨k, hk, hprev, hexit⟩ := LinearMap.exists_first_exit_index A.mulVecLin
    ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (r + 1) hnext
  exact ⟨k, Nat.le_of_lt_succ hk, hprev, hexit⟩

/-- **A bounded escaping chain in a blow-up.**

Let K be a field, N,D finite index types and B ⊆ Mat(N,N;K) a subspace. Put E = B^[D] = span{X
⊗ T : X ∈ B, T ∈ Mat(D,D;K)} and let A be a matrix on N × D. Define W₀ = 0 and Wⱼ₊₁ =
E(A⁻¹Wⱼ). Assume D is nonempty, rank A = r|D| and W∞ is not contained in im A. There exist k ≤
r, C₀,…,Cₖ ∈ E and v₀,…,vₖ ∈ K^(N × D) with Wₖ ⊆ im A, Wₖ₊₁ not contained in im A, Av₀ = 0,
Avᵢ₊₁ = Cᵢvᵢ, Avᵢ ∈ Wᵢ and Cₖvₖ ∉ im A.
-/
theorem exists_secondWong_blowup_escape_chain [Nonempty d]
    (A : Matrix (n × d) (n × d) K) (B : Submodule K (Matrix n n K)) (r : ℕ)
    (hRank : A.rank = r * Fintype.card d)
    (hExit : ¬LinearMap.secondWongLimit A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) ≤ A.mulVecLin.range) :
    ∃ k, k ≤ r ∧
      LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) k ≤ A.mulVecLin.range ∧
      ¬LinearMap.secondWongSeq A.mulVecLin
        ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) (k + 1) ≤ A.mulVecLin.range ∧
      ∃ (C : Fin (k + 1) → kroneckerBlowup B d) (v : Fin (k + 1) → (n × d → K)),
        A *ᵥ v 0 = 0 ∧
        (∀ i : Fin k, A *ᵥ v i.succ = (C i.castSucc : Matrix (n × d) (n × d) K) *ᵥ v i.castSucc) ∧
        (∀ i : Fin (k + 1), v i ∈
          (LinearMap.secondWongSeq A.mulVecLin
            ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) i.val).comap A.mulVecLin) ∧
        (C (Fin.last k) : Matrix (n × d) (n × d) K) *ᵥ v (Fin.last k) ∉ A.mulVecLin.range := by
  classical
  obtain ⟨k, hk, hprev, hexit⟩ := exists_secondWongSeq_blowup_first_exit A B r hRank hExit
  let H := (kroneckerBlowup B d).map (Matrix.mulVecBilin K K)
  obtain ⟨C, v, h0, hstep, hmem, hlast⟩ :=
    LinearMap.exists_secondWongSeq_escape_chain A.mulVecLin H k hprev hexit
  have hchoose : ∀ i : Fin (k + 1), ∃ M : Matrix (n × d) (n × d) K,
      M ∈ kroneckerBlowup B d ∧ Matrix.mulVecBilin K K M = (C i : (n × d → K) →ₗ[K] (n × d → K)) := by
    intro i
    exact Submodule.mem_map.mp (C i).2
  let M : Fin (k + 1) → Matrix (n × d) (n × d) K := fun i => Classical.choose (hchoose i)
  have hM : ∀ i, M i ∈ kroneckerBlowup B d := fun i => (Classical.choose_spec (hchoose i)).1
  have hEq : ∀ i, Matrix.mulVecBilin K K (M i) =
      (C i : (n × d → K) →ₗ[K] (n × d → K)) := fun i => (Classical.choose_spec (hchoose i)).2
  refine ⟨k, hk, hprev, hexit, fun i => ⟨M i, hM i⟩, v, h0, ?_, hmem, ?_⟩
  · intro i
    change A.mulVecLin (v i.succ) = Matrix.mulVecBilin K K (M i.castSucc) (v i.castSucc)
    rw [hEq]
    exact hstep i
  · change Matrix.mulVecBilin K K (M (Fin.last k)) (v (Fin.last k)) ∉ A.mulVecLin.range
    rwa [hEq]

end Matrix

namespace Matrix

section Shift

variable {R : Type u} [CommSemiring R] {n : Type v} {k q r : ℕ}

/-- **A cyclic shift matrix unit.**

Let R be a commutative semiring, k,q ∈ ℕ and k+1 ≤ q. Embed i ∈ Fin(k+1) in Fin q and write
σ(i) = i+1 modulo q. Define Sᵢ = E_{σ(i),i} ∈ Mat(q,q;R), the matrix unit taking slot i to its
successor and annihilating the other slots.
-/
def wongShift (h : k + 1 ≤ q) (i : Fin (k + 1)) : Matrix (Fin q) (Fin q) R :=
  Matrix.single (finRotate q (Fin.castLE h i)) (Fin.castLE h i) 1

/-- **When a bounded chain shift wraps around.**

Let R be a commutative semiring, k,q ∈ ℕ and k+1 ≤ q. Embed i ∈ Fin(k+1) in Fin q and write
σ(i) = i+1 modulo q. Suppose k ≤ r < q. Then σ(i) = 0 if and only if i = k, k = r and q = r+1.
-/
theorem wongShift_wrap_iff (h : k + 1 ≤ q) (hk : k ≤ r) (hq : r < q) (i : Fin (k + 1)) :
    (finRotate q (Fin.castLE h i)).val = 0 ↔ i = Fin.last k ∧ k = r ∧ q = r + 1 := by
  cases q with
  | zero => omega
  | succ q =>
    rw [coe_finRotate]
    split_ifs with hlast
    · have hval : i.val = q := congrArg Fin.val hlast
      constructor
      · intro _
        have hi : i = Fin.last k := by
          apply Fin.ext
          change i.val = k
          have hi := i.isLt
          omega
        exact ⟨hi, by omega, by omega⟩
      · intro _
        rfl
    · constructor
      · intro hz
        exact False.elim hz
      · rintro ⟨hi, hkr, hqr⟩
        apply False.elim
        apply hlast
        apply Fin.ext
        simp only [Fin.val_castLE, Fin.val_last]
        rw [hi]
        simp only [Fin.val_last]
        omega

private theorem rotate_castLE_castSucc (h : k + 1 ≤ q) (i : Fin k) :
    finRotate q (Fin.castLE h i.castSucc) = Fin.castLE h i.succ := by
  cases q with
  | zero => omega
  | succ q => exact finRotate_of_lt (i.isLt.trans_le (Nat.le_of_succ_le_succ h))

@[simp]
theorem wongShift_full_last (k : ℕ) :
    wongShift (R := R) (Nat.le_refl (k + 1)) (Fin.last k) = Matrix.single 0 (Fin.last k) 1 := by
  simp only [wongShift, Fin.castLE_rfl, id_eq, finRotate_last]

open scoped Kronecker

/-- **The Kronecker shift sum of a chain.**

Let R be a commutative semiring, k,q ∈ ℕ and k+1 ≤ q. Embed i ∈ Fin(k+1) in Fin q and write
σ(i) = i+1 modulo q. For matrices C₀,…,Cₖ on an index set N, define D_C = ∑ᵢ₌₀ᵏ Cᵢ ⊗
E_{σ(i),i}, a matrix on N × Fin q.
-/
def wongShiftSum (C : Fin (k + 1) → Matrix n n R) (h : k + 1 ≤ q) :
    Matrix (n × Fin q) (n × Fin q) R :=
  ∑ i : Fin (k + 1), C i ⊗ₖ wongShift h i

theorem wongShiftSum_mem_kroneckerBlowup (B : Submodule R (Matrix n n R))
    (C : Fin (k + 1) → Matrix n n R) (hC : ∀ i, C i ∈ B) (h : k + 1 ≤ q) :
    wongShiftSum C h ∈ kroneckerBlowup B (Fin q) := by
  unfold wongShiftSum
  apply Submodule.sum_mem
  intro i _
  exact kronecker_mem_kroneckerBlowup (hC i) _

/-- **Action of the chain shift sum on a single slot.**

Let R be a commutative semiring, k,q ∈ ℕ and k+1 ≤ q. Embed i ∈ Fin(k+1) in Fin q and write
σ(i) = i+1 modulo q. Let N be finite and C₀,…,Cₖ ∈ Mat(N,N;R). For D_C = ∑ᵢ Cᵢ ⊗ E_{σ(i),i}
and the insertion Iⱼ(x) into slot j, one has D_C Iⱼ(x) = I_{σ(j)}(Cⱼx).
-/
theorem wongShiftSum_columnInsert [Fintype n] (C : Fin (k + 1) → Matrix n n R)
    (h : k + 1 ≤ q) (j : Fin (k + 1)) (x : n → R) :
    wongShiftSum C h *ᵥ LinearMap.columnInsert (Fin.castLE h j) x =
      LinearMap.columnInsert (finRotate q (Fin.castLE h j)) (C j *ᵥ x) := by
  have hsum : wongShiftSum C h *ᵥ LinearMap.columnInsert (Fin.castLE h j) x =
      ∑ i : Fin (k + 1), (C i ⊗ₖ wongShift h i) *ᵥ LinearMap.columnInsert (Fin.castLE h j) x := by
    change ((Matrix.mulVecBilin R R).flip (LinearMap.columnInsert (Fin.castLE h j) x))
      (∑ i : Fin (k + 1), C i ⊗ₖ wongShift h i) = _
    rw [map_sum]
    simp only [LinearMap.flip_apply, Matrix.mulVecBilin_apply]
  rw [hsum, Finset.sum_eq_single j]
  · rw [wongShift, kronecker_single_mulVec]
    simp [LinearMap.columnInsert_apply]
  · intro i _ hij
    have hslot : Fin.castLE h i ≠ Fin.castLE h j := fun heq => hij (Fin.castLE_injective h heq)
    rw [wongShift, kronecker_single_mulVec]
    have hproj : (fun a : n => LinearMap.columnInsert (Fin.castLE h j) x (a, Fin.castLE h i)) = 0 := by
      ext a
      simp [LinearMap.columnInsert_apply, hslot]
    rw [hproj, Matrix.mulVec_zero, map_zero]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

private theorem kronecker_one_project [Fintype n] (A : Matrix n n R)
    (x : n × Fin q → R) (j : Fin q) :
    (fun i : n => ((A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ x) (i, j)) =
      A *ᵥ (fun i : n => x (i, j)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

private theorem kronecker_one_insert [Fintype n] (A : Matrix n n R)
    (j : Fin q) (x : n → R) :
    (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ LinearMap.columnInsert j x =
      LinearMap.columnInsert j (A *ᵥ x) := by
  ext ⟨i, l⟩
  have hc := congrFun (kronecker_one_project A (LinearMap.columnInsert j x) l) i
  by_cases h : l = j
  · subst l
    simpa [LinearMap.columnInsert_apply] using hc
  · have hp : (fun a : n => LinearMap.columnInsert j x (a, l)) = 0 := by
      ext a
      simp [LinearMap.columnInsert_apply, h]
    rw [hp, Matrix.mulVec_zero] at hc
    simpa [LinearMap.columnInsert_apply, h] using hc

private theorem inserted_not_range_kronecker_one [Fintype n] (A : Matrix n n R)
    (x : n → R) (j : Fin q) (hx : x ∉ A.mulVecLin.range) :
    LinearMap.columnInsert j x ∉ (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)).mulVecLin.range := by
  rintro ⟨y, hy⟩
  change (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ y = LinearMap.columnInsert j x at hy
  have hc : (fun i : n => ((A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ y) (i, j)) = x := by
    rw [hy]
    simp [LinearMap.columnInsert_apply]
  exact hx ⟨fun i : n => y (i, j), (kronecker_one_project A y j).symm.trans hc⟩

private theorem wongShift_lifts_escape [Fintype n] (A : Matrix n n R)
    (C : Fin (k + 1) → Matrix n n R) (v : Fin (k + 1) → (n → R)) (h : k + 1 ≤ q)
    (h0 : A *ᵥ v 0 = 0)
    (hstep : ∀ i : Fin k, A *ᵥ v i.succ = C i.castSucc *ᵥ v i.castSucc)
    (hout : C (Fin.last k) *ᵥ v (Fin.last k) ∉ A.mulVecLin.range) :
    (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ LinearMap.columnInsert (Fin.castLE h 0) (v 0) = 0 ∧
      (∀ i : Fin k,
        (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)) *ᵥ
          LinearMap.columnInsert (Fin.castLE h i.succ) (v i.succ) =
        wongShiftSum C h *ᵥ LinearMap.columnInsert (Fin.castLE h i.castSucc) (v i.castSucc)) ∧
      wongShiftSum C h *ᵥ LinearMap.columnInsert (Fin.castLE h (Fin.last k)) (v (Fin.last k)) ∉
        (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) R)).mulVecLin.range := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kronecker_one_insert, h0, map_zero]
  · intro i
    rw [kronecker_one_insert, wongShiftSum_columnInsert, rotate_castLE_castSucc, hstep i]
  · rw [wongShiftSum_columnInsert]
    exact inserted_not_range_kronecker_one A _ _ hout

end Shift

section ExtractedShift

variable {K : Type u} [Field K] {n : Type v} {d : Type w}
variable [Fintype n] [Fintype d] [Nonempty d]

open scoped Kronecker

/-- **Lifting a Wong escape to a uniform shift chain.**

Let K be a field, N,D finite index types and B ⊆ Mat(N,N;K) a subspace. Put E = B^[D] = span{X
⊗ T : X ∈ B, T ∈ Mat(D,D;K)} and let A be a matrix on N × D. Define W₀ = 0 and Wⱼ₊₁ =
E(A⁻¹Wⱼ). Assume D is nonempty, A ∈ E, rank A = r|D|, W∞ is not contained in im A, and q > r.
There exist k ≤ r, matrices C₀,…,Cₖ ∈ E, and vectors w₀,…,wₖ on (N × D) × Fin q. Put A′ = A ⊗
I_q and D_C = ∑ᵢ Cᵢ ⊗ E_{i+1 mod q,i}. Both A′ and D_C belong to E^[Fin q], and A′w₀ = 0,
A′wᵢ₊₁ = D_Cwᵢ, and D_Cwₖ ∉ im A′.
-/
theorem exists_wongShift_blowup_escape (A : Matrix (n × d) (n × d) K)
    (B : Submodule K (Matrix n n K)) (r q : ℕ) (hA : A ∈ kroneckerBlowup B d)
    (hRank : A.rank = r * Fintype.card d)
    (hExit : ¬LinearMap.secondWongLimit A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) ≤ A.mulVecLin.range)
    (hq : r < q) :
    ∃ k, k ≤ r ∧ ∃ (C : Fin (k + 1) → kroneckerBlowup B d) (h : k + 1 ≤ q),
      A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K) ∈ kroneckerBlowup (kroneckerBlowup B d) (Fin q) ∧
      let D := wongShiftSum (fun i => (C i : Matrix (n × d) (n × d) K)) h
      D ∈ kroneckerBlowup (kroneckerBlowup B d) (Fin q) ∧
      ∃ w : Fin (k + 1) → ((n × d) × Fin q → K),
        (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) *ᵥ w 0 = 0 ∧
        (∀ i : Fin k, (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) *ᵥ w i.succ = D *ᵥ w i.castSucc) ∧
        D *ᵥ w (Fin.last k) ∉ (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)).mulVecLin.range := by
  obtain ⟨k, hk, _hprev, _hexit, C, v, h0, hstep, _hmem, hlast⟩ :=
    exists_secondWong_blowup_escape_chain A B r hRank hExit
  have h : k + 1 ≤ q := (Nat.succ_le_succ hk).trans (Nat.succ_le_of_lt hq)
  let M : Fin (k + 1) → Matrix (n × d) (n × d) K := fun i => C i
  have hM : ∀ i, M i ∈ kroneckerBlowup B d := fun i => (C i).2
  let w : Fin (k + 1) → ((n × d) × Fin q → K) := fun i => LinearMap.columnInsert (Fin.castLE h i) (v i)
  have hlift := wongShift_lifts_escape A M v h h0 hstep hlast
  exact ⟨k, hk, C, h, kronecker_mem_kroneckerBlowup hA _,
    wongShiftSum_mem_kroneckerBlowup (kroneckerBlowup B d) M hM h, w, hlift⟩

end ExtractedShift

end Matrix

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MatrixDiscrepancy
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Euclidean vector discrepancy

Unit-vector colorings relax the finite sign minimum. The optimizer and completed
proofs are reference-guided by the retained Codex `audit_c1a_final` model;
current API author is Codex `finish_c32_saved`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace MatrixDiscrepancy

noncomputable section

variable {m n : ℕ}

/-- **Vector discrepancy.** For a real $m \times n$ matrix $A$, the vector discrepancy of $A$ is
the infimum, over all families $u_1, \dots, u_n$ of unit vectors in the Euclidean space
$\mathbb{R}^n$, of $\max_{1 \le i \le m} \lVert \sum_{j=1}^{n} A_{ij} u_j \rVert$ (taken to be $0$
when $m = 0$), where $\lVert \cdot \rVert$ is the Euclidean norm; it is an element of
$[0, \infty]$. -/
def vectorDiscrepancy (A : Matrix (Fin m) (Fin n) ℝ) : ENNReal :=
  ⨅ u : {u : Fin n → EuclideanSpace ℝ (Fin n) // ∀ j, ‖u j‖ = 1},
    ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u.1 j‖

theorem vectorDiscrepancy_le_coloring (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin n → EuclideanSpace ℝ (Fin n)) (hu : ∀ j, ‖u j‖ = 1) :
    vectorDiscrepancy A ≤ ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u j‖ := by
  unfold vectorDiscrepancy
  exact iInf_le
    (fun v : {v : Fin n → EuclideanSpace ℝ (Fin n) // ∀ j, ‖v j‖ = 1} =>
      ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • v.1 j‖)
    (⟨u, hu⟩ : {v : Fin n → EuclideanSpace ℝ (Fin n) // ∀ j, ‖v j‖ = 1})

theorem le_vectorDiscrepancy (A : Matrix (Fin m) (Fin n) ℝ) (r : ENNReal)
    (h : ∀ (u : Fin n → EuclideanSpace ℝ (Fin n)), (∀ j, ‖u j‖ = 1) →
      r ≤ ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u j‖) : r ≤ vectorDiscrepancy A :=
  le_iInf (fun u => h u.1 u.2)

theorem vectorDiscrepancy_le_of_coloring (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin n → EuclideanSpace ℝ (Fin n)) (hu : ∀ j, ‖u j‖ = 1)
    (hrows : ∀ i, ‖∑ j, A i j • u j‖ ≤ 1) : vectorDiscrepancy A ≤ 1 := by
  apply (iInf_le _ ⟨u, hu⟩).trans
  exact (ENNReal.ofReal_le_ofReal ((pi_norm_le_iff_of_nonneg (by norm_num)).2 hrows)).trans_eq
    (by simp)

theorem vectorDiscrepancy_le_discrepancy (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) : vectorDiscrepancy A ≤ discrepancy A := by
  obtain ⟨x, hx⟩ := discrepancy_attained A
  let k : Fin n := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
  let u : Fin n → EuclideanSpace ℝ (Fin n) := fun j => EuclideanSpace.single k (signValue (x j))
  have hu : ∀ j, ‖u j‖ = 1 := by
    intro j
    simp [u, Real.norm_eq_abs]
  have hsum (i : Fin m) : (∑ j, A i j • u j) =
      EuclideanSpace.single k (∑ j, A i j * signValue (x j)) := by
    ext l
    by_cases h : l = k <;> simp [u, h]
  have hnorm : ‖fun i : Fin m => ∑ j, A i j • u j‖ =
      ‖A.mulVec (fun j => signValue (x j))‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro i
      simp only [hsum, PiLp.norm_single]
      exact norm_le_pi_norm (A.mulVec (fun j => signValue (x j))) i
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro i
      change ‖∑ j, A i j * signValue (x j)‖ ≤ _
      have hi := norm_le_pi_norm (fun i : Fin m => ∑ j, A i j • u j) i
      simpa only [hsum, PiLp.norm_single] using hi
  calc
    _ ≤ ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u j‖ := vectorDiscrepancy_le_coloring A u hu
    _ = discrepancy A := by rw [hnorm, hx]

/-- **The vector discrepancy is attained.** Let $A$ be a real $m \times n$ matrix with $n \ge 1$.
Then there are unit vectors $u_1, \dots, u_n$ in the Euclidean space $\mathbb{R}^n$ such that
the vector discrepancy of $A$ equals $\max_{1 \le i \le m} \lVert \sum_{j=1}^{n} A_{ij} u_j \rVert$
(taken to be $0$ when $m = 0$), where $\lVert \cdot \rVert$ is the Euclidean norm. -/
theorem vectorDiscrepancy_attained (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ u : Fin n → EuclideanSpace ℝ (Fin n), (∀ j, ‖u j‖ = 1) ∧
      vectorDiscrepancy A = ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u j‖ := by
  let s : Set (Fin n → EuclideanSpace ℝ (Fin n)) := {u | ∀ j, ‖u j‖ = 1}
  have hs : IsCompact s := by
    simpa [s, Metric.mem_sphere, dist_zero_right] using
      (isCompact_pi_infinite (fun _ : Fin n =>
        isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  have hne : s.Nonempty := by
    refine ⟨fun _ => EuclideanSpace.single (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩ : Fin n)
      (1 : ℝ), ?_⟩
    simp [s]
  let f : (Fin n → EuclideanSpace ℝ (Fin n)) → ENNReal :=
    fun u => ENNReal.ofReal ‖fun i : Fin m => ∑ j, A i j • u j‖
  have hf : Continuous f := by
    unfold f
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  obtain ⟨u, hu, hmin⟩ := hs.exists_isMinOn hne hf.continuousOn
  refine ⟨u, hu, ?_⟩
  dsimp only [f] at hmin
  apply le_antisymm (vectorDiscrepancy_le_coloring A u hu)
  exact le_vectorDiscrepancy A _ (fun v hv => hmin hv)

end

end MatrixDiscrepancy

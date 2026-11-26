/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KamanoLandenPolyBernoulli

/-!
# Kamano's generalized multiple polylogarithm sum formula

This module proves the sum formula for Kamano's generalized multiple polylogarithms,
`generalizedMultiplePolylog_sum_formula`: for Landen data `D`, weights `β γ δ`, a real
number `μ` and `k ≥ 1`, the weighted sum over all compositions of `k` equals the depth-one
polylogarithm with combined weights.

The proof works with the reversed recursion `LandenData.polylogRev`: compositions of
`k + 1` split by their first part into those starting with `1` and those starting with at
least `2`, giving the recurrence for the sum, which matches the singleton recurrence by
induction; the statement for `generalizedMultiplePolylog` follows via the reverse
bijection on compositions.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 1,
Identity (7).
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

namespace generalizedMultiplePolylog_sum_formula

/-- Prepend the part `1` to a composition. -/
private def consOneComp {k : ℕ} (c : Composition k) : Composition (k + 1) where
  blocks := 1 :: c.blocks
  blocks_pos hi := by
    rcases List.mem_cons.mp hi with rfl | hi
    · decide
    · exact c.blocks_pos hi
  blocks_sum := by
    simp [c.blocks_sum, Nat.add_comm]
/-- Blocks of `consOneComp`. -/
@[simp] private theorem consOneComp_blocks {k : ℕ} (c : Composition k) :
    (consOneComp c).blocks = 1 :: c.blocks :=
  rfl
/-- A composition of a positive number has nonempty blocks. -/
private theorem blocks_ne_nil_of_pos {n : ℕ} (c : Composition n) (hn : 0 < n) :
    c.blocks ≠ [] := by
  intro he
  have hs := c.blocks_sum
  rw [he] at hs
  simp at hs
  omega
/-- The first part of a composition of a positive number is at least one. -/
private theorem headI_ge_one {n : ℕ} (c : Composition n) (hn : 0 < n) :
    1 ≤ c.blocks.headI := by
  cases hc : c.blocks with
  | nil =>
    have hs := c.blocks_sum
    rw [hc] at hs
    simp at hs
    omega
  | cons b t =>
    have hb : b ∈ c.blocks := by
      rw [hc]
      exact List.mem_cons_self
    have h1 := c.one_le_blocks hb
    simpa using h1
/-- Increase the first part of a composition by one. -/
private def incHeadComp {k : ℕ} (c : Composition k) : Composition (k + 1) where
  blocks := (c.blocks.headI + 1) :: c.blocks.tail
  blocks_pos hi := by
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · exact c.blocks_pos (List.mem_of_mem_tail hi)
  blocks_sum := by
    have h : c.blocks.headI + c.blocks.tail.sum = c.blocks.sum := by
      cases c.blocks with
      | nil => simp
      | cons b t => simp
    have hs := c.blocks_sum
    simp only [List.sum_cons]
    omega
/-- Blocks of `incHeadComp`. -/
@[simp] private theorem incHeadComp_blocks {k : ℕ} (c : Composition k) :
    (incHeadComp c).blocks = (c.blocks.headI + 1) :: c.blocks.tail :=
  rfl
/-- Length of `consOneComp`. -/
@[simp] private theorem consOneComp_length {k : ℕ} (c : Composition k) :
    (consOneComp c).length = c.length + 1 :=
  rfl
/-- Length of `incHeadComp` for positive `k`. -/
private theorem incHeadComp_length {k : ℕ} (c : Composition k) (hk : 0 < k) :
    (incHeadComp c).length = c.length := by
  have hne := blocks_ne_nil_of_pos c hk
  have h : (incHeadComp c).blocks.length = c.blocks.length := by
    rw [incHeadComp_blocks]
    cases hc : c.blocks with
    | nil => exact (hne hc).elim
    | cons b t => simp
  exact h
/-- Drop the first part `1` of a composition. -/
private def tailComp {k : ℕ} (d : Composition (k + 1)) (h : d.blocks.headI = 1) :
    Composition k where
  blocks := d.blocks.tail
  blocks_pos hi := d.blocks_pos (List.mem_of_mem_tail hi)
  blocks_sum := by
    have hsum : d.blocks.headI + d.blocks.tail.sum = d.blocks.sum := by
      cases d.blocks with
      | nil => simp
      | cons b t => simp
    have hs := d.blocks_sum
    omega
/-- Decrease the first part of a composition by one. -/
private def decHeadComp {k : ℕ} (d : Composition (k + 1)) (h : d.blocks.headI ≠ 1) :
    Composition k where
  blocks := (d.blocks.headI - 1) :: d.blocks.tail
  blocks_pos hi := by
    rcases List.mem_cons.mp hi with rfl | hi
    · have hg := headI_ge_one d (Nat.succ_pos k)
      omega
    · exact d.blocks_pos (List.mem_of_mem_tail hi)
  blocks_sum := by
    have hsum : d.blocks.headI + d.blocks.tail.sum = d.blocks.sum := by
      cases d.blocks with
      | nil => simp
      | cons b t => simp
    have hs := d.blocks_sum
    have hg := headI_ge_one d (Nat.succ_pos k)
    simp only [List.sum_cons]
    omega
/-- Rebuilding blocks from head and tail. -/
private theorem headI_tail_eq {n : ℕ} (c : Composition n) (hn : 0 < n) :
    c.blocks.headI :: c.blocks.tail = c.blocks := by
  cases hc : c.blocks with
  | nil => exact (blocks_ne_nil_of_pos c hn hc).elim
  | cons b t => simp
/-- Blocks of `tailComp`. -/
@[simp] private theorem tailComp_blocks {k : ℕ} (d : Composition (k + 1))
    (h : d.blocks.headI = 1) : (tailComp d h).blocks = d.blocks.tail :=
  rfl
/-- Blocks of `decHeadComp`. -/
@[simp] private theorem decHeadComp_blocks {k : ℕ} (d : Composition (k + 1))
    (h : d.blocks.headI ≠ 1) :
    (decHeadComp d h).blocks = (d.blocks.headI - 1) :: d.blocks.tail :=
  rfl
/-- Head of `consOneComp` is one. -/
private theorem consOneComp_headI {k : ℕ} (c : Composition k) :
    (consOneComp c).blocks.headI = 1 := by
  simp [consOneComp_blocks]
/-- Tail after `consOneComp` recovers the original. -/
private theorem tailComp_consOneComp {k : ℕ} (c : Composition k)
    (h : (consOneComp c).blocks.headI = 1) : tailComp (consOneComp c) h = c := by
  ext1
  simp [consOneComp_blocks]
/-- Head of `incHeadComp`. -/
private theorem incHeadComp_headI {k : ℕ} (c : Composition k) :
    (incHeadComp c).blocks.headI = c.blocks.headI + 1 := by
  simp [incHeadComp_blocks]
/-- Head of `incHeadComp` is never one for positive `k`. -/
private theorem incHeadComp_headI_ne_one {k : ℕ} (c : Composition k) (hk : 0 < k) :
    (incHeadComp c).blocks.headI ≠ 1 := by
  rw [incHeadComp_headI]
  have hg := headI_ge_one c hk
  omega
/-- Decrement after `incHeadComp` recovers the original. -/
private theorem decHeadComp_incHeadComp {k : ℕ} (c : Composition k) (hk : 0 < k)
    (h : (incHeadComp c).blocks.headI ≠ 1) : decHeadComp (incHeadComp c) h = c := by
  ext1
  simp only [decHeadComp_blocks, incHeadComp_blocks]
  have hhead : ((c.blocks.headI + 1) :: c.blocks.tail).headI = c.blocks.headI + 1 := by
    simp
  have htail : ((c.blocks.headI + 1) :: c.blocks.tail).tail = c.blocks.tail := by
    simp
  rw [hhead, htail]
  have hsub : c.blocks.headI + 1 - 1 = c.blocks.headI := by
    omega
  rw [hsub]
  exact headI_tail_eq c hk
/-- Prepending after dropping recovers the original. -/
private theorem consOneComp_tailComp {k : ℕ} (d : Composition (k + 1))
    (h : d.blocks.headI = 1) : consOneComp (tailComp d h) = d := by
  ext1
  simp only [consOneComp_blocks, tailComp_blocks]
  have heq := headI_tail_eq d (Nat.succ_pos k)
  rw [h] at heq
  exact heq
/-- Incrementing after decrementing recovers the original. -/
private theorem incHeadComp_decHeadComp {k : ℕ} (d : Composition (k + 1))
    (h : d.blocks.headI ≠ 1) : incHeadComp (decHeadComp d h) = d := by
  ext1
  simp only [incHeadComp_blocks, decHeadComp_blocks]
  have hhead : ((d.blocks.headI - 1) :: d.blocks.tail).headI = d.blocks.headI - 1 := by
    simp
  have htail : ((d.blocks.headI - 1) :: d.blocks.tail).tail = d.blocks.tail := by
    simp
  rw [hhead, htail]
  have hg := headI_ge_one d (Nat.succ_pos k)
  have hadd : d.blocks.headI - 1 + 1 = d.blocks.headI := by
    omega
  rw [hadd]
  exact headI_tail_eq d (Nat.succ_pos k)
/-- Splitting compositions of `k + 1` by their first part. -/
private def headSplitEquiv {k : ℕ} (hk : 0 < k) :
    Composition k ⊕ Composition k ≃ Composition (k + 1) where
  toFun
    | .inl c => incHeadComp c
    | .inr c => consOneComp c
  invFun d := if h : d.blocks.headI = 1 then .inr (tailComp d h) else .inl (decHeadComp d h)
  left_inv
    | .inl c => by
      have hf := incHeadComp_headI_ne_one c hk
      simp only [hf, dite_false]
      congr 1
      exact decHeadComp_incHeadComp c hk _
    | .inr c => by
      have ht := consOneComp_headI c
      simp only [ht, dite_true, tailComp_consOneComp]
  right_inv d := by
    by_cases h : d.blocks.headI = 1
    · simp only [h, dite_true]
      exact consOneComp_tailComp d h
    · simp only [h, dite_false]
      exact incHeadComp_decHeadComp d h
/-- Polylogarithm on `consOneComp`. -/
private theorem polylogRev_consOneComp (D : LandenData) (β γ : Fin D.s → ℝ) {k : ℕ}
    (c : Composition k) (hk : 0 < k) :
    D.polylogRev β γ (consOneComp c).blocks =
      integralDivX (D.formSeries γ * D.polylogRev β γ c.blocks) := by
  have hne := blocks_ne_nil_of_pos c hk
  cases hc : c.blocks with
  | nil => exact (hne hc).elim
  | cons r rs =>
    rw [consOneComp_blocks, hc]
    simp [LandenData.polylogRev]
/-- Polylogarithm on `incHeadComp`. -/
private theorem polylogRev_incHeadComp (D : LandenData) (β γ : Fin D.s → ℝ) {k : ℕ}
    (c : Composition k) (hk : 0 < k) :
    D.polylogRev β γ (incHeadComp c).blocks =
      integralDivX (D.formSeries β * D.polylogRev β γ c.blocks) := by
  have hne := blocks_ne_nil_of_pos c hk
  cases hc : c.blocks with
  | nil => exact (hne hc).elim
  | cons b t =>
    have hb : b ∈ c.blocks := by
      rw [hc]
      exact List.mem_cons_self
    have hbpos := c.blocks_pos hb
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hbpos)
    have hblocks : (incHeadComp c).blocks = (a + 2) :: t := by
      simp [incHeadComp_blocks, hc]
    rw [hblocks]
    simp [LandenData.polylogRev]
/-- `integralDivX` preserves addition. -/
private theorem integralDivX_add (h1 h2 : ℝ⟦X⟧) :
    integralDivX (h1 + h2) = integralDivX h1 + integralDivX h2 := by
  ext n
  simp [integralDivX, map_add, add_div]
/-- `integralDivX` preserves zero. -/
private theorem integralDivX_zero : integralDivX (0 : ℝ⟦X⟧) = 0 := by
  ext n
  simp [integralDivX]
/-- `integralDivX` commutes with scalar multiplication. -/
private theorem integralDivX_smul (r : ℝ) (h : ℝ⟦X⟧) :
    integralDivX (r • h) = r • integralDivX h := by
  ext n
  simp [integralDivX]
  ring
/-- `integralDivX` commutes with finite sums. -/
private theorem integralDivX_sum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ⟦X⟧) : integralDivX (∑ i ∈ s, F i) = ∑ i ∈ s, integralDivX (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [integralDivX_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, integralDivX_add, ih]
/-- `formSeries` is linear in the weights. -/
private theorem formSeries_add_smul (D : LandenData) (β γ : Fin D.s → ℝ) (μ : ℝ) :
    D.formSeries (β + μ • γ) = D.formSeries β + μ • D.formSeries γ := by
  simp only [LandenData.formSeries, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← smul_eq_C_mul]
/-- Every composition of one is the singleton. -/
private theorem comp_one_eq_single (c : Composition 1) :
    c = Composition.single 1 zero_lt_one := by
  rw [Composition.eq_single_iff_length]
  have hle := c.length_le
  have hpos := c.length_pos_of_pos zero_lt_one
  omega
/-- The sum over compositions of one is the singleton term. -/
private theorem sum_comp_one (D : LandenData) (β γ : Fin D.s → ℝ) (μ : ℝ) :
    ∑ c : Composition 1, μ ^ (c.length - 1) • D.polylogRev β γ c.blocks =
      D.polylogRev β γ [1] := by
  have : Subsingleton (Composition 1) :=
    ⟨fun c1 c2 => (comp_one_eq_single c1).trans (comp_one_eq_single c2).symm⟩
  rw [Fintype.sum_subsingleton _ (Composition.single 1 zero_lt_one)]
  simp [Composition.single_blocks, Composition.single_length]
/-- Singleton recurrence for `polylogRev`. -/
private theorem polylogRev_singleton_succ (D : LandenData) (β' δ : Fin D.s → ℝ) {k : ℕ}
    (hk : 0 < k) :
    D.polylogRev β' δ [k + 1] =
      integralDivX (D.formSeries β' * D.polylogRev β' δ [k]) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hk)
  have heq : a + 1 + 1 = a + 2 := by ring
  rw [heq]
  simp [LandenData.polylogRev]
/-- Power for `incHeadComp`. -/
private theorem pow_incHeadComp (μ : ℝ) {k : ℕ} (c : Composition k) (hk : 0 < k) :
    μ ^ ((incHeadComp c).length - 1) = μ ^ (c.length - 1) := by
  rw [incHeadComp_length c hk]
/-- Power for `consOneComp`. -/
private theorem pow_consOneComp (μ : ℝ) {k : ℕ} (c : Composition k) (hk : 0 < k) :
    μ ^ ((consOneComp c).length - 1) = μ * μ ^ (c.length - 1) := by
  rw [consOneComp_length]
  have hlen := c.length_pos_of_pos hk
  have heq : c.length + 1 - 1 = c.length := by omega
  rw [heq]
  have hlen_eq : c.length = (c.length - 1) + 1 := (Nat.sub_add_cancel hlen).symm
  nth_rewrite 1 [hlen_eq]
  rw [pow_succ']
/-- The sum over `k + 1` in terms of the sum over `k`. -/
private theorem sum_succ_aux (D : LandenData) (β γ : Fin D.s → ℝ) (μ : ℝ) {k : ℕ}
    (hk : 0 < k) :
    ∑ d : Composition (k + 1), μ ^ (d.length - 1) • D.polylogRev β γ d.blocks =
      integralDivX (D.formSeries (β + μ • γ) *
        ∑ c : Composition k, μ ^ (c.length - 1) • D.polylogRev β γ c.blocks) := by
  rw [← Equiv.sum_comp (headSplitEquiv hk)]
  rw [Fintype.sum_sum_type]
  have hinl : ∀ c : Composition k, (headSplitEquiv hk) (.inl c) = incHeadComp c :=
    fun c => rfl
  have hinr : ∀ c : Composition k, (headSplitEquiv hk) (.inr c) = consOneComp c :=
    fun c => rfl
  simp_rw [hinl, hinr]
  have hinc : ∀ c : Composition k,
      μ ^ ((incHeadComp c).length - 1) • D.polylogRev β γ (incHeadComp c).blocks =
        μ ^ (c.length - 1) •
          integralDivX (D.formSeries β * D.polylogRev β γ c.blocks) := by
    intro c
    rw [pow_incHeadComp μ c hk, polylogRev_incHeadComp D β γ c hk]
  have hcon : ∀ c : Composition k,
      μ ^ ((consOneComp c).length - 1) • D.polylogRev β γ (consOneComp c).blocks =
        μ • (μ ^ (c.length - 1) •
          integralDivX (D.formSeries γ * D.polylogRev β γ c.blocks)) := by
    intro c
    rw [pow_consOneComp μ c hk, polylogRev_consOneComp D β γ c hk, mul_smul]
  simp_rw [hinc, hcon]
  have hβ : ∀ c : Composition k,
      μ ^ (c.length - 1) •
          integralDivX (D.formSeries β * D.polylogRev β γ c.blocks) =
        integralDivX (D.formSeries β *
          (μ ^ (c.length - 1) • D.polylogRev β γ c.blocks)) := by
    intro c
    rw [← integralDivX_smul, ← mul_smul_comm]
  have hγ : ∀ c : Composition k,
      μ ^ (c.length - 1) •
          integralDivX (D.formSeries γ * D.polylogRev β γ c.blocks) =
        integralDivX (D.formSeries γ *
          (μ ^ (c.length - 1) • D.polylogRev β γ c.blocks)) := by
    intro c
    rw [← integralDivX_smul, ← mul_smul_comm]
  simp_rw [hβ, hγ]
  rw [← integralDivX_sum, ← Finset.smul_sum, ← integralDivX_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [formSeries_add_smul, add_mul, smul_mul_assoc, integralDivX_add, integralDivX_smul]
/-- The `polylogRev` sum formula. -/
private theorem sum_eq_polylogRev_singleton (D : LandenData) (β γ δ : Fin D.s → ℝ)
    (μ : ℝ) (k : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) • D.polylogRev β γ c.blocks =
      D.polylogRev (β + μ • γ) δ [k] := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [sum_comp_one]
    simp [LandenData.polylogRev]
  | succ k hk1 ih =>
    rw [sum_succ_aux D β γ μ hk1, polylogRev_singleton_succ D (β + μ • γ) δ hk1, ih]
/-- Reversing preserves length. -/
private theorem reverse_length {k : ℕ} (c : Composition k) :
    c.reverse.length = c.length := by
  have h : c.reverse.blocks.length = c.blocks.length := by
    simp [Composition.reverse_blocks, List.length_reverse]
  exact h
/-- The reverse involution as an equivalence. -/
private def reverseEquiv (k : ℕ) : Composition k ≃ Composition k where
  toFun c := c.reverse
  invFun c := c.reverse
  left_inv c := Composition.reverse_reverse c
  right_inv c := Composition.reverse_reverse c
end generalizedMultiplePolylog_sum_formula

/-- **Sum formula.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data, let
$\beta, \gamma, \delta \in \mathbb{R}^s$, let $\mu$ be a real number and let $k \ge 1$ be an
integer. Then
$\sum_{\mathbf{k}} \mu^{d(\mathbf{k}) - 1} \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); z) =
\mathrm{Li}_{(k)}(g; (\beta + \mu \gamma, \delta); z)$, where the sum runs over all compositions
$\mathbf{k} = (k_1, \dots, k_r)$ of $k$ (sequences of positive integers with
$k_1 + \dots + k_r = k$) and $d(\mathbf{k}) = r$ is the depth of $\mathbf{k}$.

The paper takes $\mu$ an indeterminate; both sides are polynomials in $\mu$, so this
is equivalent.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 1,
Identity (7). -/
public theorem generalizedMultiplePolylog_sum_formula (D : LandenData)
    (β γ δ : Fin D.s → ℝ) (μ : ℝ) (k : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) • generalizedMultiplePolylog D β γ c.blocks =
      generalizedMultiplePolylog D (β + μ • γ) δ [k] := by
  have hGMP : ∀ c : Composition k,
      generalizedMultiplePolylog D β γ c.blocks =
        D.polylogRev β γ c.blocks.reverse := fun c => rfl
  simp_rw [hGMP]
  have hterm : ∀ c : Composition k,
      μ ^ (c.length - 1) • D.polylogRev β γ c.blocks.reverse =
        μ ^ (c.reverse.length - 1) • D.polylogRev β γ c.reverse.blocks := by
    intro c
    rw [generalizedMultiplePolylog_sum_formula.reverse_length,
      Composition.reverse_blocks]
  simp_rw [hterm]
  have hsum : (∑ c : Composition k,
        μ ^ (c.reverse.length - 1) • D.polylogRev β γ c.reverse.blocks) =
      ∑ d : Composition k, μ ^ (d.length - 1) • D.polylogRev β γ d.blocks :=
    Equiv.sum_comp (generalizedMultiplePolylog_sum_formula.reverseEquiv k)
      (fun d : Composition k => μ ^ (d.length - 1) • D.polylogRev β γ d.blocks)
  rw [hsum]
  rw [generalizedMultiplePolylog_sum_formula.sum_eq_polylogRev_singleton D β γ δ μ k hk]
  have hRHS : generalizedMultiplePolylog D (β + μ • γ) δ [k] =
      D.polylogRev (β + μ • γ) δ [k] := by
    simp [generalizedMultiplePolylog]
  rw [hRHS]

end

end MetaMathlibExt

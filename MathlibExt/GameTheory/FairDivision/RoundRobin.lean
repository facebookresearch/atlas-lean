/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.FairDivision.Indivisible

/-!
# Round-robin allocation of indivisible goods

A bijection `order` lists the agents in picking order; a bijection `pick` lists the goods
in the order in which they were taken. The goods still available at a turn are exactly
its suffix in `pick`. Maximising over this suffix imposes no tie-breaking rule.

For the EF1 comparison, discard the rival's first pick. Each remaining pick has a
preceding round, in which the evaluating agent chose while that rival good was still
available. These preceding rounds are distinct, even if the last round is incomplete.

## Reference

I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah and J. Wang,
*The Unreasonable Fairness of Maximum Nash Welfare*, ACM Transactions on Economics
and Computation 7(3), 2019. See §1.3 and the draft argument at the start of §3
(pages A:4 and A:7 of the authors' manuscript).
-/

@[expose] public section

namespace MathlibExt.GameTheory.FairDivision.Indivisible

variable {ι γ : Type*} {n m : ℕ} [NeZero n]

/-- Given a fixed order of `n ≥ 1` agents and a chronological enumeration of all goods,
assign the good taken at zero-based turn `k` to the agent at position `k % n` in that order. -/
def roundRobinAllocation (order : Fin n ≃ ι) (pick : Fin m ≃ γ) (g : γ) : ι :=
  order (Fin.ofNat n (pick.symm g).val)

/-- Fix an order of `n ≥ 1` agents. A chronological bijection `pick` from turns to goods is a
round-robin draft if, at each zero-based turn `t`, the agent at position `t % n` in that order
weakly prefers `pick t` to every good in the suffix starting at `t`. This suffix consists of
exactly the remaining goods, so any maximiser may be chosen and all goods are taken. -/
def IsRoundRobinDraft (order : Fin n ≃ ι) (v : ι → γ → ℝ) (pick : Fin m ≃ γ) : Prop :=
  ∀ t u : Fin m, t ≤ u → v (order (Fin.ofNat n t.val)) (pick u) ≤
    v (order (Fin.ofNat n t.val)) (pick t)

/-- For any fixed cyclic ordering of a nonempty finite set of agents, any finite set of
indivisible goods (possibly empty), and any real single-good values, there exists a complete
round-robin draft: at each turn the scheduled agent takes a highest-valued remaining good,
with any maximiser permitted. The draft makes exactly one pick per good. -/
theorem exists_roundRobinDraft [Fintype γ] (order : Fin n ≃ ι) (v : ι → γ → ℝ) :
    ∃ pick : Fin (Fintype.card γ) ≃ γ, IsRoundRobinDraft order v pick := by
  classical
  let m := Fintype.card γ
  let score (t : Fin m) := v (order (Fin.ofNat n t.val))
  -- Grow a greedy prefix by swapping a best remaining good into its next slot.
  have hprefix (k : ℕ) (hk : k ≤ m) : ∃ p : Fin m ≃ γ,
      ∀ t u : Fin m, t.val < k → t ≤ u → score t (p u) ≤ score t (p t) := by
    induction k with
    | zero => exact ⟨(Fintype.equivFin γ).symm, by simp⟩
    | succ k ih =>
      obtain ⟨p, hp⟩ := ih (by omega)
      let a : Fin m := ⟨k, by omega⟩
      let s := Finset.univ.filter (a ≤ ·)
      have hs (u : Fin m) : u ∈ s ↔ a ≤ u := by simp [s]
      obtain ⟨b, hb, hmax⟩ := s.exists_max_image (fun u => score a (p u))
        ⟨a, (hs a).2 le_rfl⟩
      have hab := (hs b).1 hb
      have hswap {t u : Fin m} (ht : t ≤ a) (hu : t ≤ u) : t ≤ Equiv.swap a b u := by
        rw [Equiv.swap_apply_def]
        split_ifs
        exacts [ht.trans hab, ht, hu]
      refine ⟨(Equiv.swap a b).trans p, ?_⟩
      intro t u ht htu
      change score t (p (Equiv.swap a b u)) ≤ score t (p (Equiv.swap a b t))
      by_cases h : t = a
      · subst t
        rw [Equiv.swap_apply_left]
        exact hmax _ ((hs _).2 (hswap le_rfl htu))
      · have hta : t < a := lt_of_le_of_ne (show t.val ≤ k by omega) h
        rw [Equiv.swap_apply_of_ne_of_ne h (hta.trans_le hab).ne]
        exact hp _ _ hta (hswap hta.le htu)
  obtain ⟨p, hp⟩ := hprefix m le_rfl
  exact ⟨p, fun t u h => hp t u t.isLt h⟩

private theorem mem_roundRobinBundle [Fintype γ] [DecidableEq ι]
    (order : Fin n ≃ ι) (pick : Fin m ≃ γ) (g : γ) (j : Fin n) :
    g ∈ bundle (roundRobinAllocation order pick) (order j) ↔
      (pick.symm g).val % n = j.val := by
  simp [bundle, roundRobinAllocation, Fin.ext_iff, Fin.ofNat]

-- A rival turn other than the first lies in round `q+1`. Subtracting the fixed
-- distance `n + j - i` reaches slot `i` of round `q`, without truncation.
omit [NeZero n] in
private theorem precedingRound {k : ℕ} (i j : Fin n) (hj : k % n = j.val) (hne : k ≠ j.val) :
    n + j.val - i.val ≤ k ∧ (k - (n + j.val - i.val)) % n = i.val := by
  have he := Nat.mod_add_div k n
  rw [hj] at he
  cases hq : k / n with
  | zero => simp [hq] at he; exact (hne he.symm).elim
  | succ q =>
    rw [hq, Nat.mul_succ] at he
    have hi := i.isLt
    refine ⟨by omega, ?_⟩
    have h : k - (n + j.val - i.val) = i.val + n * q := by omega
    simp [h, Nat.mod_eq_of_lt hi]

/-- With a nonempty finite set of agents in any fixed cyclic order and finitely many
indivisible goods, suppose each agent values a bundle by the sum of its nonnegative
single-good values. Every complete draft in which each turn takes a maximiser among all
remaining goods, however ties are broken, produces an allocation envy-free up to one good:
for each pair of agents `i, j` with `j`'s bundle nonempty, one can remove a good from it
so that `i` values the remainder no more than `i`'s own bundle. -/
theorem IsRoundRobinDraft.isEF1 [Fintype γ] [DecidableEq γ] [DecidableEq ι]
    {order : Fin n ≃ ι} {v : ι → γ → ℝ} {pick : Fin m ≃ γ}
    (h : IsRoundRobinDraft order v pick) (hv : ∀ i g, 0 ≤ v i g) :
    IsEF1 v (roundRobinAllocation order pick) := by
  intro a b hne
  obtain ⟨i, rfl⟩ := order.surjective a
  obtain ⟨j, rfl⟩ := order.surjective b
  obtain ⟨g, hg⟩ := hne
  have hj : j.val < m := calc
    j.val = (pick.symm g).val % n := ((mem_roundRobinBundle order pick g j).1 hg).symm
    _ ≤ (pick.symm g).val := Nat.mod_le _ _
    _ < m := (pick.symm g).isLt
  let first : Fin m := ⟨j.val, hj⟩
  refine ⟨pick first, (mem_roundRobinBundle ..).2 (by simp [first, Nat.mod_eq_of_lt j.isLt]), ?_⟩
  let d := n + j.val - i.val
  let prev (g : γ) : Fin m := ⟨(pick.symm g).val - d, (Nat.sub_le ..).trans_lt (pick.symm g).isLt⟩
  let s := (bundle (roundRobinAllocation order pick) (order j)).erase (pick first)
  have pair {x : γ} (hx : x ∈ s) : d ≤ (pick.symm x).val ∧ (prev x).val % n = i.val := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
    apply precedingRound i j ((mem_roundRobinBundle ..).1 hmem)
    intro he
    exact hne (pick.symm_apply_eq.mp (Fin.ext he : pick.symm x = first))
  change ∑ x ∈ s, v (order i) x ≤ ∑ y ∈ bundle _ (order i), v (order i) y
  apply Finset.sum_le_sum_of_injOn (fun x => pick (prev x))
  · intro x hx y hy he
    have he' := congrArg Fin.val (pick.injective he)
    have hx' := (pair hx).1
    have hy' := (pair hy).1
    apply pick.symm.injective
    apply Fin.ext
    change (pick.symm x).val - d = (pick.symm y).val - d at he'
    omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_roundRobinBundle order pick _ i).2 (by simpa using (pair hx).2)
  · intro x hx
    have ht : Fin.ofNat n (prev x).val = i := Fin.ext (pair hx).2
    simpa only [ht, Equiv.apply_symm_apply] using h (prev x) (pick.symm x) (Nat.sub_le ..)
  · intro y _ _
    exact hv _ y

end MathlibExt.GameTheory.FairDivision.Indivisible

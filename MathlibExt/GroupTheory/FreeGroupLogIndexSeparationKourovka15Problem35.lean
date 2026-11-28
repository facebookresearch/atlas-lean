/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Logarithmic-index separation in free groups

The theorem `logIndexSeparation_refuted` gives short nontrivial words that act
trivially on every coset space of bounded size. A balanced tree of commutators combines
powers of one generator, one for each possible order of its permutation on the cosets.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.35 (O. V.
Bogopolski). UnsolvedMath record UM-00701123 (`KOU-15.35`), dataset ulamai/UnsolvedMath v1.8.0.

Ranks `r ≥ 2` only: for `r = 1` the answer is yes (the least non-divisor of `n` is `O(log n)`) and
for `r = 0` it is vacuous. The target is stated for some rank `r ≥ 2`, so its refutation says that
no rank `r ≥ 2` admits such a `C`. Word length is `FreeGroup.norm` (reduced word length); the
subgroup must have finite index, since `Subgroup.index` is `0` for infinite index.
-/

/-- **Logarithmic-index separation in free groups (Kourovka 15.35).** The statement, posed by
O. V. Bogopolski, that for some integer $r \ge 2$ there is a real number $C$ such that every
element $w$ of the free group $F_r$ of rank $r$ whose reduced word length $n$ satisfies $n > 1$
lies outside some subgroup of $F_r$ of finite index at most $C \log n$, where $\log$ is the
natural logarithm. -/
def logIndexSeparation : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧ ∃ C : ℝ, ∀ w : FreeGroup (Fin r), 1 < w.norm →
    ∃ H : Subgroup (FreeGroup (Fin r)), H.FiniteIndex ∧ w ∉ H ∧
      (H.index : ℝ) ≤ C * Real.log w.norm

open FreeGroup
open scoped commutatorElement

variable {α : Type*} [DecidableEq α]

-- The two boundary letters suffice to check that no cancellation occurs at a join.
private def Ends (w : FreeGroup α) (p q : α × Bool) : Prop :=
  w.toWord.head? = some p ∧ w.toWord.getLast? = some q

private theorem ends_mul {u v : FreeGroup α} {p q s t : α × Bool}
    (hu : Ends u p q) (hv : Ends v s t) (h : q.1 = s.1 → q.2 = s.2) :
    Ends (u * v) p t := by
  have hr : IsReduced (u.toWord ++ v.toWord) := by
    apply List.isChain_append.mpr
    refine ⟨isReduced_toWord, isReduced_toWord, ?_⟩
    simpa [hu.2, hv.1] using h
  have h₁ : u.toWord ≠ [] := fun he => by simpa [he] using hu.1
  have h₂ : v.toWord ≠ [] := fun he => by simpa [he] using hv.1
  simpa [Ends, toWord_mul, hr.reduce_eq, List.head?_append_of_ne_nil _ h₁,
    List.getLast?_append_of_ne_nil _ h₂] using And.intro hu.1 hv.2

private theorem ends_inv {w : FreeGroup α} {a b : α} {s t : Bool}
    (hw : Ends w (a, s) (b, t)) : Ends w⁻¹ (b, !t) (a, !s) := by
  simp [Ends, toWord_inv, invRev, hw.1, hw.2]

private theorem ends_of (a : α) : Ends (of a) (a, true) (a, true) := by
  simp [Ends]

private def joinWords {G : Type*} [Group G] (a b u v : G) : G :=
  MulAut.conj a ⁅u, MulAut.conj b v⁆

-- At depth d the leaves carry the powers indexed by the interval (i, i + 2^d].
private def law {G : Type*} [Group G] (a b : G) : ℕ → ℕ → G
  | 0, i => MulAut.conj a (b ^ (i + 1))
  | d + 1, i => joinWords a b (law a b d i) (law a b d (i + 2 ^ d))

-- Conjugating by the two distinct letters keeps the commutator reduced at every join.
private theorem ends_law {a b : α} (hab : a ≠ b) (d i : ℕ) :
    Ends (law (of a) (of b) d i) (a, true) (a, false) := by
  induction d generalizing i with
  | zero =>
    have hp : Ends (of b ^ (i + 1)) (b, true) (b, true) := by
      simp [Ends, toWord_of_pow, List.head?_replicate, List.getLast?_replicate]
    exact ends_mul (ends_mul (ends_of a) hp (by simp [hab]))
      (ends_inv (ends_of a)) (by simp [hab.symm])
  | succ d ih =>
    have hu := ih i
    have hv := ih (i + 2 ^ d)
    have hz := ends_mul (ends_mul (ends_of b) hv (by simp [hab.symm]))
      (ends_inv (ends_of b)) (by simp [hab])
    have huz := ends_mul hu hz (by simp [hab])
    have huzu := ends_mul huz (ends_inv hu) (by simp [hab.symm])
    have hc := ends_mul huzu (ends_inv hz) (by simp [hab])
    exact ends_mul (ends_mul (ends_of a) hc (by simp)) (ends_inv (ends_of a))
      (by simp [hab.symm])

private theorem one_lt_norm_law {a b : α} (hab : a ≠ b) (d i : ℕ) :
    1 < (law (of a) (of b) d i).norm := by
  obtain ⟨h₁, h₂⟩ := ends_law hab d i
  unfold FreeGroup.norm
  generalize (law (of a) (of b) d i).toWord = l at *
  cases l with
  | nil => simp at h₁
  | cons p l =>
    cases l with
    | nil => simp_all
    | cons => simp

private theorem norm_conj_le (a : α) (w : FreeGroup α) :
    (MulAut.conj (of a) w).norm ≤ w.norm + 2 := by
  have h := norm_mul_le (of a * w) (of a)⁻¹
  have h' := norm_mul_le (of a) w
  simp only [norm_inv_eq, norm_of] at h h'
  rw [MulAut.conj_apply]
  omega

private theorem norm_joinWords_le (a b : α) (u v : FreeGroup α) :
    (joinWords (of a) (of b) u v).norm ≤ 2 * u.norm + 2 * v.norm + 6 := by
  let z := MulAut.conj (of b) v
  have hz : z.norm ≤ v.norm + 2 := norm_conj_le _ _
  have h₁ := norm_mul_le u z
  have h₂ := norm_mul_le (u * z) u⁻¹
  have h₃ := norm_mul_le (u * z * u⁻¹) z⁻¹
  have h₄ := norm_conj_le a (u * z * u⁻¹ * z⁻¹)
  simp only [norm_inv_eq] at h₂ h₃
  change (MulAut.conj (of a) (u * z * u⁻¹ * z⁻¹)).norm ≤ _
  omega

private theorem norm_law_le (a b : α) (d i : ℕ) :
    (law (of a) (of b) d i).norm + 2 ≤ 4 ^ d * (i + 2 ^ d + 4) := by
  induction d generalizing i with
  | zero =>
    simpa [law, norm_of_pow] using Nat.add_le_add_right (norm_conj_le a (of b ^ (i + 1))) 2
  | succ d ih =>
    have h₁ := ih i
    have h₂ := ih (i + 2 ^ d)
    have h₃ := norm_joinWords_le a b (law (of a) (of b) d i)
      (law (of a) (of b) d (i + 2 ^ d))
    rw [law, pow_succ, pow_succ]
    nlinarith only [h₁, h₂, h₃, Nat.zero_le (4 ^ d * 2 ^ d)]

-- A leaf killed by a homomorphism kills every commutator above it.
private theorem map_law_eq_one {G K : Type*} [Group G] [Group K] (f : G →* K) (a b : G)
    (d i j : ℕ) (hlo : i < j) (hhi : j ≤ i + 2 ^ d) (h : f b ^ j = 1) :
    f (law a b d i) = 1 := by
  induction d generalizing i with
  | zero =>
    simp only [pow_zero] at hhi
    have : j = i + 1 := by omega
    simp [law, MulAut.conj_apply, ← this, h]
  | succ d ih =>
    rw [pow_succ] at hhi
    by_cases hj : j ≤ i + 2 ^ d
    · simp [law, joinWords, map_commutatorElement, MulAut.conj_apply, ih i hlo hj]
    · simp [law, joinWords, map_commutatorElement, MulAut.conj_apply,
        ih (i + 2 ^ d) (by omega) (by omega)]

-- Small cycle lengths divide (k²)!. There are at most k² longer cycles, each of length
-- at most k⁴. This puts all possible permutation orders within reach of a shallow tree.
private theorem orderOf_le {X : Type*} [Fintype X] (g : Equiv.Perm X)
    {k : ℕ} (hk : 0 < k) (hX : Fintype.card X ≤ k ^ 4) :
    orderOf g ≤ 2 ^ (8 * k ^ 3) := by
  classical
  let large := g.cycleType.filter (k ^ 2 < ·)
  have hlarge {m : ℕ} : m ∈ large ↔ m ∈ g.cycleType ∧ k ^ 2 < m := Multiset.mem_filter
  have hsum := g.sum_cycleType_le.trans hX
  have hsum' : large.sum ≤ k ^ 4 := by
    obtain ⟨rest, he⟩ := Multiset.le_iff_exists_add.mp (Multiset.filter_le (k ^ 2 < ·) g.cycleType)
    change g.cycleType = large + rest at he
    rw [he, Multiset.sum_add] at hsum
    omega
  have hcard : large.card ≤ k ^ 2 := by
    have h := Multiset.card_nsmul_le_sum (s := large) (a := k ^ 2)
      (fun m hm => (hlarge.mp hm).2.le)
    simp only [nsmul_eq_mul] at h
    apply Nat.le_of_mul_le_mul_right (c := k ^ 2) _ (by positivity)
    calc
      large.card * k ^ 2 ≤ k ^ 4 := h.trans hsum'
      _ = k ^ 2 * k ^ 2 := by ring
  have hdvd : orderOf g ∣ (k ^ 2).factorial * large.prod := by
    rw [← g.lcm_cycleType, Multiset.lcm_dvd]
    intro m hm
    by_cases h : m ≤ k ^ 2
    · exact dvd_mul_of_dvd_left (Nat.dvd_factorial (g.one_lt_of_mem_cycleType hm).le h) _
    · exact dvd_mul_of_dvd_right (Multiset.dvd_prod (hlarge.mpr ⟨hm, by omega⟩)) _
  have hpos : 0 < large.prod := Multiset.prod_pos (fun m hm => by
    have := (hlarge.mp hm).2
    omega)
  have hpow : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk (by decide)
  calc
    orderOf g ≤ (k ^ 2).factorial * large.prod := Nat.le_of_dvd (by positivity) hdvd
    _ ≤ (k ^ 4) ^ (k ^ 2) * (k ^ 4) ^ (k ^ 2) := by
      apply Nat.mul_le_mul
      · exact (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hpow _)
      · exact (large.prod_le_pow_card _ (fun m hm =>
          (Multiset.le_sum_of_mem (hlarge.mp hm).1).trans hsum)).trans
            (Nat.pow_le_pow_right (by positivity) hcard)
    _ = k ^ (8 * k ^ 2) := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ (2 ^ k) ^ (8 * k ^ 2) := Nat.pow_le_pow_left k.lt_two_pow_self.le _
    _ = 2 ^ (8 * k ^ 3) := by rw [← pow_mul]; ring_nf

private theorem log_norm_law_le {a b : α} (hab : a ≠ b) (d : ℕ) :
    Real.log (law (of a) (of b) d 0).norm ≤ 3 * d + 3 := by
  have hbase : 2 ^ d + 4 ≤ 2 ^ (d + 3) := by
    rw [pow_add]
    have := Nat.one_le_two_pow (n := d)
    omega
  have hlen : (law (of a) (of b) d 0).norm ≤ 2 ^ (3 * d + 3) := calc
    _ ≤ 4 ^ d * (2 ^ d + 4) := by
      have h := norm_law_le a b d 0
      rw [zero_add] at h
      omega
    _ ≤ 4 ^ d * 2 ^ (d + 3) := Nat.mul_le_mul_left _ hbase
    _ = 2 ^ (3 * d + 3) := by rw [show 4 = 2 ^ 2 by decide, ← pow_mul, ← pow_add]; ring_nf
  have hnorm := one_lt_norm_law hab d 0
  calc
    _ ≤ Real.log ((2 : ℝ) ^ (3 * d + 3)) :=
      Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hnorm)) (by exact_mod_cast hlen)
    _ = (3 * d + 3 : ℕ) * Real.log 2 := Real.log_pow _ _
    _ ≤ _ := by
      have h : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      push_cast
      nlinarith [mul_nonneg (by positivity : 0 ≤ (d : ℝ)) (sub_nonneg.mpr h)]

/--
**Bogopolski's logarithmic-index separation fails in free groups of rank at least 2.** For every
integer $r \ge 2$ and every real number $C$, there is an element $w$ of the free group $F_r$ of
rank $r$ whose reduced word length $n$ satisfies $n > 1$ and such that every subgroup of finite
index in $F_r$ that does not contain $w$ has index greater than $C \log n$, where $\log$ is the
natural logarithm. That is, the logarithmic-index separation property of Kourovka Problem 15.35
holds for no rank $r \ge 2$.

Bou-Rabee and McReynolds (Theorem 1.4) prove that for every rank $m > 1$ the maximal divisibility
function of $F_m$ on words of length at most $n$ is not $O(\log n)$, which rules out every $C$;
the Kourovka Archive answers 15.35 "No, it is not true".

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.35 (O. V. Bogopolski); resolution:
K. Bou-Rabee and D. B. McReynolds, Asymptotic growth and least common multiples in groups, Bull.
London Math. Soc. 43 (2011), 1059-1068, arXiv:0907.3681, Theorem 1.4 (for m > 1, max D_{F_m}(n) is
not bounded by O(log n)), https://arxiv.org/abs/0907.3681.
-/
public theorem logIndexSeparation_refuted : ¬ logIndexSeparation := by
  rintro ⟨r, hr, C, hC⟩
  -- Up to index k⁴, the logarithm of the law length is at most 27 k³.
  obtain ⟨k, hk⟩ := exists_nat_gt (27 * max C 1)
  have hC₁ : 1 ≤ max C 1 := le_max_right _ _
  have hk' : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  let d := 8 * k ^ 3
  let w := law (of a) (of b) d 0
  have hw : 1 < w.norm := one_lt_norm_law hab _ _
  obtain ⟨H, hH, hout, hindex⟩ := hC w hw
  have hlog : Real.log w.norm ≤ 27 * (k : ℝ) ^ 3 := by
    have hbound := log_norm_law_le hab d
    dsimp [d] at hbound
    push_cast at hbound
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk'
    have hk₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk₁ 3
    change Real.log (law (of a) (of b) (8 * k ^ 3) 0).norm ≤ _
    linarith
  have hind : H.index ≤ k ^ 4 := by
    have hnonneg : 0 ≤ Real.log w.norm := Real.log_nonneg (by exact_mod_cast hw.le)
    have := calc
      (H.index : ℝ) ≤ C * Real.log w.norm := hindex
      _ ≤ max C 1 * (27 * (k : ℝ) ^ 3) :=
        mul_le_mul (le_max_left ..) hlog hnonneg (by linarith)
      _ ≤ (k : ℝ) ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hk.le) (by positivity : 0 ≤ (k : ℝ) ^ 3)]
    exact_mod_cast this
  classical
  let := H.fintypeQuotientOfFiniteIndex
  let f := MulAction.toPermHom (FreeGroup (Fin r)) (FreeGroup (Fin r) ⧸ H)
  have hcard : Fintype.card (FreeGroup (Fin r) ⧸ H) ≤ k ^ 4 := by
    simpa [Subgroup.index_eq_card, Nat.card_eq_fintype_card] using hind
  have horder := orderOf_le (f (of b)) hk' hcard
  apply hout
  apply H.normalCore_le
  rw [Subgroup.normalCore_eq_ker]
  exact map_law_eq_one f (of a) (of b) d 0 _ (orderOf_pos _) (by simpa [d] using horder)
    (pow_orderOf_eq_one _)

end MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.GameTheory.NimPassIndicator
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Bitwise
import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtFoldlXor

/-! # Grundy numbers of Nim with a restricted pass

For strictly positive pile thresholds, the Grundy number of every legal position is the
nim-sum of its pile sizes and pass bit if and only if every threshold is even. Here a
pass-on position is legal only if at least one pile meets its threshold. The positivity
hypothesis matters: a zero threshold would keep the pass available regardless of the other
thresholds, so an odd threshold could no longer force the pass to be lost.

## References

* Ryohei Miyadera, Hikaru Manabe and Aditi Singh,
  *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*,
  INTEGERS 25 (2025), Article G3, pp. 1–29, Definitions 15–17 and 20–21, Theorem 7,
  Lemma 10 and Corollary 2. The mex argument here specializes the height-cut argument
  to a single pass bit; the converse uses a move across an odd threshold.
* The proof uses `exists_of_lt_foldl_xor` and `foldl_xor_update` from
  `MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtFoldlXor`, and
  `nimPassIndicator_sections_hasNSProperty_iff` from `MathlibExt.GameTheory.NimPassIndicator`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Grundy number of a chocolate bar with a height function.** Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$. The $(s + 1)$-dimensional chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$ has, at each $u = (u_1, \dots, u_s)$ with $u_t \le x_t$ for
all $t$, a column of height $\min(F(u), y) + 1$. A move either lowers one coordinate $x_i$ to some
$a < x_i$, which clamps the height to $\min(F(x'), y)$ for the new position $x'$, or lowers the
height $y$ to some $v < y$. The Grundy number of $\mathrm{CB}(F, x_1, \dots, x_s, y)$ is the mex
(least natural number not attained) of the Grundy numbers of the positions reachable in one
move. It is defined for all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$; the bars themselves are
the positions with $y \le F(x)$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 15, 16 and 17 (and Definition 13 with second function `0`). -/
public noncomputable def heightChocolateBarGrundy {s : ℕ} (F : (Fin s → ℕ) → ℕ)
    (x : Fin s → ℕ) (y : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
      (min (F (Function.update x i u)) y) ≠ m) ∧
    ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m}
termination_by (∑ t, x t) + y
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    have := min_le_right (F (Function.update x i u)) y
    omega
  · omega

/-- **Mex recursion for chocolate bars with a height function.** Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$, and write $G(x, y)$ for the Grundy number of the chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$. For all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$,
$G(x, y)$ is the least natural number $m$ such that $m \ne G(x', \min(F(x'), y))$ for every $x'$
obtained from $x$ by lowering one coordinate $x_i$ to some $u < x_i$, and $m \ne G(x, v)$ for
every $v < y$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 17. -/
public theorem heightChocolateBarGrundy_eq {s : ℕ} (F : (Fin s → ℕ) → ℕ) (x : Fin s → ℕ)
    (y : ℕ) :
    heightChocolateBarGrundy F x y =
      sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
          (min (F (Function.update x i u)) y) ≠ m) ∧
        ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m} := by
  rw [heightChocolateBarGrundy]

local notation "pileXor" x:max => (List.foldl (· ^^^ ·) 0 (List.ofFn x))

private theorem xor_one_div_two (u : ℕ) : (u ^^^ 1) / 2 = u / 2 := by
  simpa using (Nat.xor_div_two (a := u) (b := 1))

private theorem nimPassGrundy_eq_xor_of_even {s : ℕ} {m : Fin s → ℕ}
    (hm : ∀ i, 0 < m i) (heven : ∀ i, Even (m i)) (x : Fin s → ℕ) (p : ℕ)
    (hp : p ≤ nimPassIndicator m x) :
    heightChocolateBarGrundy (nimPassIndicator m) x p = pileXor x ^^^ p := by
  let F := nimPassIndicator m
  change p ≤ F x at hp
  have hp_le := hp.trans (nimPassIndicator_le_one m x)
  have hcut (i : Fin s) (u : ℕ) (hu : u < x i) :
      heightChocolateBarGrundy F (Function.update x i u) (min (F (Function.update x i u)) p) =
        pileXor (Function.update x i u) ^^^ min (F (Function.update x i u)) p :=
    nimPassGrundy_eq_xor_of_even hm heven _ _ (min_le_left ..)
  have hpass (v : ℕ) (hv : v < p) : heightChocolateBarGrundy F x v = pileXor x ^^^ v :=
    nimPassGrundy_eq_xor_of_even hm heven x v (hv.le.trans hp)
  have hupdate (i : Fin s) (u : ℕ) :
      pileXor (Function.update x i u) = pileXor x ^^^ (x i ^^^ u) := by
    simpa only [Nat.xor_xor_cancel_left] using foldl_xor_update x i (x i ^^^ u)
  have hpair (i : Fin s) {u v : ℕ} (h : u / 2 = v / 2) :
      F (Function.update x i u) = F (Function.update x i v) := by
    have hns := (nimPassIndicator_sections_hasNSProperty_iff hm).mpr heven x i
    have he := hns.min_div_two_pow_eq (z' := u) (z := v) (k := 1) (by decide) (by simpa using h) 1
    simpa only [Nat.sub_self, pow_zero, Nat.div_one,
      min_eq_left (nimPassIndicator_le_one m (Function.update x i u)),
      min_eq_left (nimPassIndicator_le_one m (Function.update x i v))] using he
  rw [heightChocolateBarGrundy_eq]
  let missing : Set ℕ := {c | (∀ i u, u < x i →
      heightChocolateBarGrundy F (Function.update x i u) (min (F (Function.update x i u)) p) ≠ c) ∧
    ∀ v, v < p → heightChocolateBarGrundy F x v ≠ c}
  change sInf missing = pileXor x ^^^ p
  have hmissing : pileXor x ^^^ p ∈ missing := by
    refine ⟨?_, fun v hv h ↦ hv.ne (by simpa only [hpass v hv, Nat.xor_right_inj] using h)⟩
    intro i u hu h
    rw [hcut i u hu, hupdate] at h
    by_cases hkeep : p ≤ F (Function.update x i u)
    · rw [min_eq_right hkeep, Nat.xor_left_inj] at h
      have hz := Nat.xor_right_injective (h.trans (Nat.xor_zero _).symm)
      exact hu.ne (Nat.xor_eq_zero_iff.mp hz).symm
    · have hp1 : p = 1 := by omega
      have hu0 : F (Function.update x i u) = 0 := by omega
      rw [hp1, hu0, Nat.zero_min, Nat.xor_zero, Nat.xor_right_inj] at h
      have hu_eq : u = x i ^^^ 1 := by
        simpa only [Nat.xor_xor_cancel_left] using congrArg (fun n ↦ x i ^^^ n) h
      rw [hu_eq, hpair i (xor_one_div_two _), Function.update_eq_self] at hu0
      omega
  refine le_antisymm (Nat.sInf_le hmissing) ?_
  by_contra! hlt
  have hmex := Nat.sInf_mem (s := missing) ⟨_, hmissing⟩
  rcases exists_of_lt_foldl_xor (f := fun i _ ↦ x i) (fun i ↦ hasNSProperty_const (x i))
      (fun _ ↦ le_rfl) hlt with ⟨i, u, hu, he⟩ | ⟨v, hv, he⟩
  · by_cases hkeep : p ≤ F (Function.update x i u)
    · exact hmex.1 i u hu (by rw [hcut i u hu, min_eq_right hkeep, ← he])
    · have hp1 : p = 1 := by omega
      have hu0 : F (Function.update x i u) = 0 := by omega
      let v := u ^^^ 1
      have hvdiv : v / 2 = u / 2 := xor_one_div_two u
      have hv0 : F (Function.update x i v) = 0 := (hpair i hvdiv).trans hu0
      have hdiv : u / 2 < x i / 2 := by
        refine lt_of_le_of_ne (Nat.div_le_div_right hu.le) (fun heq ↦ ?_)
        rw [hpair i heq, Function.update_eq_self] at hu0
        omega
      have hv : v < x i := by omega
      apply hmex.1 i v hv
      rw [hcut i v hv, hv0, Nat.zero_min, Nat.xor_zero, he, hp1]
      simp only [hupdate, v, Nat.xor_assoc]
  · exact hmex.2 v hv (by simpa only [min_self, hpass v hv] using he.symm)
termination_by (∑ t, x t) + p
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simpa using hu.le
      · simp [Function.update_of_ne hj]
    exact Nat.add_lt_add_of_lt_of_le hlt (min_le_right ..)
  · exact Nat.add_lt_add_left hv _

/-- **Nim with a restricted pass.** Let $s \in \mathbb{N}$ and $m \in \mathbb{N}^s$ with $m_i > 0$
for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be the pass indicator of $m$:
$F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise. Write $\oplus$ for nim-sum.
Then the following are equivalent: (a) for all $x \in \mathbb{N}^s$ and $p \in \mathbb{N}$ with
$p \le F(x)$, the Grundy number of the chocolate bar $\mathrm{CB}(F, x_0, \dots, x_{s-1}, p)$ is
$x_0 \oplus \cdots \oplus x_{s-1} \oplus p$; (b) $m_i$ is even for every $i < s$.

The bar is Nim on $s$ piles with a one-time pass usable only while $F(x) = 1$: removing stones
from a pile, reaching $x'$, replaces $p$ by $\min(F(x'), p)$, and the pass lowers $p$ from $1$
to $0$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Corollary 2 (`integers-2025-G3-cor-2`). -/
public theorem nimPassGrundy_eq_xor_iff {s : ℕ} {m : Fin s → ℕ} (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) p, p ≤ nimPassIndicator m x →
        heightChocolateBarGrundy (nimPassIndicator m) x p =
          (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ p) ↔
      ∀ i, Even (m i) := by
  constructor
  · intro h i
    by_contra hi
    have hodd := Nat.not_even_iff_odd.mp hi
    let x := Function.update (fun _ : Fin s ↦ 0) i (m i)
    let u := x i ^^^ 1
    let F := nimPassIndicator m
    have hx : x i = m i := by simp [x]
    have hu : u < x i := by
      rw [show u = x i ^^^ 1 from rfl, hx, Nat.xor_one_of_odd hodd]
      have := hm i
      omega
    have hp : 1 ≤ F x :=
      (nimPassIndicator_eq_one_iff.mpr ⟨i, hx.ge⟩).ge
    have hcut : F (Function.update x i u) = 0 := by
      apply nimPassIndicator_eq_zero_iff.mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self, hx] using hu
      · simpa only [x, Function.update_of_ne hj] using hm j
    have hsame : heightChocolateBarGrundy F (Function.update x i u)
        (min (F (Function.update x i u)) 1) = heightChocolateBarGrundy F x 1 := by
      rw [hcut, Nat.zero_min, h _ _ (Nat.zero_le _), h x 1 hp, Nat.xor_zero]
      exact foldl_xor_update x i 1
    -- The finite set of followers omits its mex.
    classical
    let moves := (Finset.univ.biUnion fun j : Fin s ↦ (Finset.range (x j)).image fun v ↦
      heightChocolateBarGrundy F (Function.update x j v) (min (F (Function.update x j v)) 1)) ∪
      (Finset.range 1).image (heightChocolateBarGrundy F x)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset moves
    have hgaps : {n | (∀ j v, v < x j → heightChocolateBarGrundy F (Function.update x j v)
        (min (F (Function.update x j v)) 1) ≠ n) ∧
        ∀ v, v < 1 → heightChocolateBarGrundy F x v ≠ n}.Nonempty := by
      refine ⟨c, ?_, ?_⟩
      · intro j v hv hEq
        exact hc (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, hEq⟩⟩))
      · intro v hv hEq
        exact hc (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, hEq⟩))
    conv_rhs at hsame => rw [heightChocolateBarGrundy_eq]
    exact (Nat.sInf_mem hgaps).1 i u hu hsame
  · intro heven x p hp
    exact nimPassGrundy_eq_xor_of_even hm heven x p hp

end

end MetaMathlibExt

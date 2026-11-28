/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Basic
public import MathlibExt.NumberTheory.Digits.ZeckendorfProperBlockCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Pairwise

/-!
# Decomposing proper blocks of nested periodic Zeckendorf collections

Let `L` and `L'` be digit lists of length at least two, each with nonzero first digit, such
that the periodic Zeckendorf collection for integers of `L` is a proper subset of that of `L'`.
A nonzero proper `L*`-block on `[i, b]` is a sum of disjoint proper `L'*`-blocks ending at or before
`b`, including an interval ending at `b`. The proof reflects a finite maximal `L`-block, rather
than decomposing the infinite maximal `L*`-block: the strict decrease at `b` becomes a strict
decrease at the reflected index `0`.

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
  pp. 1–45, Definitions 10, 11, and 17 and Lemma 9, §3.3.1.
  <https://math.colgate.edu/~integers/z25/z25.pdf>
* S. Chang, *The weak converse of Zeckendorf’s theorem*, Research in Number Theory 7 (2021),
  Article 48, Theorem 7 (the integer collection construction cited in Chang's Theorem 4).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The maximal $L$-block $\theta^{m+1}$.** Let $L = (e_1, \dots, e_N)$ be a list of natural
numbers and $m \in \mathbb N$, with indices of coefficient functions starting at $0$. The maximal
$L$-block $\theta^{m+1}$ is the finitely supported coefficient function whose entry at each index
$i < m$ is $e_j$, where $j - 1 = (m - 1 - i) \bmod N$, and whose entries at the indices $i \ge m$
are $0$ (every entry is $0$ when $L$ is empty).

In the paper's one-based indexing, $\theta^n = \mathrm{rev}_{n-1}(\beta^*)$, where $\beta^*$ is
the coefficient function with $\beta^*_k = e_j$ for $k \equiv j \pmod N$ and
$\mathrm{rev}_{n-1}(\beta^*)$ lists the first $n - 1$ entries of $\beta^*$ in reverse order,
followed by zeros.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public noncomputable def periodicTheta (L : List ℕ) (m : ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ Finset.range m, Finsupp.single i (L.getD ((m - 1 - i) % L.length) 0)

/-- **The maximal block $\theta^4$ in the Fibonacci case.** For $L = (1, 0)$, the maximal $L$-block
$\theta^4$ is $(1, 0, 1)$: its entries at indices $0$, $1$, $2$ are $1$, $0$, $1$, and all its
entries from index $3$ on are $0$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public theorem periodicTheta_one_zero_three :
    periodicTheta [1, 0] 3 = Finsupp.single 0 1 + Finsupp.single 2 1 := by
  simp [periodicTheta, Finset.sum_range_succ]

/-- **L-blocks.** Let $L$ be a list of natural numbers, and for each $m$ let $\theta^{m+1}$ be the
maximal $L$-block, which vanishes from index $m$ on (indices are zero-based). A finitely supported
coefficient function $\zeta$ is an $L$-block with support interval $[s, m - 1]$ if $1 \le m$,
$s < m$, and either $s = 0$ and $\zeta = \theta^{m+1}$, or $\zeta_i = \theta^{m+1}_i$ for every
$i > s$, $\zeta_s < \theta^{m+1}_s$ and $\zeta_i = 0$ for every $i < s$.

In the paper's indexing this is a block at index $n - 1$ with $n = m + 1 \ge 2$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Definition 10 (arXiv:2308.12872v1, Section 2.2). -/
public def IsLBlock (L : List ℕ) (ζ : ℕ →₀ ℕ) (lo m : ℕ) : Prop :=
  1 ≤ m ∧ lo < m ∧
    ((lo = 0 ∧ ζ = periodicTheta L m) ∨
      (ζ.filter (lo < ·) = (periodicTheta L m).filter (lo < ·) ∧ ζ lo < periodicTheta L m lo ∧
        ζ.filter (· < lo) = 0))

/-- **Periodic Zeckendorf collection.** For a list $L$ of natural numbers, the periodic Zeckendorf
collection determined by $L$ is the set of finitely supported coefficient functions $\mu$ that
can be written as a sum $\mu = \zeta_1 + \dots + \zeta_r$ of finitely many $L$-blocks
$\zeta_1, \dots, \zeta_r$ (possibly none, which gives $\mu = 0$) whose support intervals are
pairwise disjoint.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Theorem 4 and the definition following it (arXiv:2308.12872v1, Section 2.2). -/
public def periodicZeckendorfCollection (L : List ℕ) : Set (ℕ →₀ ℕ) :=
  {μ | ∃ blocks : List ((ℕ →₀ ℕ) × ℕ × ℕ), (∀ b ∈ blocks, IsLBlock L b.1 b.2.1 b.2.2) ∧
    blocks.Pairwise (fun a b => a.2.2 ≤ b.2.1 ∨ b.2.2 ≤ a.2.1) ∧ μ = (blocks.map Prod.fst).sum}

end

private abbrev IntegerBlock := (ℕ →₀ ℕ) × ℕ × ℕ

private theorem periodicTheta_apply (L : List ℕ) (m j : ℕ) :
    periodicTheta L m j = if j < m then L.getD ((m - 1 - j) % L.length) 0 else 0 := by
  classical
  simp [periodicTheta, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_range]

private theorem periodicTheta_reflect (L : List ℕ) {b u j : ℕ} (hu : u ≤ b + 1) (hj : j < u) :
    periodicTheta L u j = maxLStarBlock L (b + 1 - u) (b - j) := by
  rw [periodicTheta_apply, ite_eq_left hj, maxLStarBlock_of_le (by omega),
    show b - j - (b + 1 - u) = u - 1 - j by omega]

private theorem IsLBlock.digit_eq {L : List ℕ} {δ : ℕ →₀ ℕ} {lo u j : ℕ}
    (h : IsLBlock L δ lo u) (hj : lo < j) : δ j = periodicTheta L u j := by
  rcases h.2.2 with ⟨_, rfl⟩ | ⟨hfilter, _, _⟩
  · rfl
  · simpa only [Finsupp.filter_apply, ite_eq_left hj] using DFunLike.congr_fun hfilter j

private theorem IsLBlock.digit_zero {L : List ℕ} {δ : ℕ →₀ ℕ} {lo u j : ℕ}
    (h : IsLBlock L δ lo u) (hj : j ∉ Set.Ico lo u) : δ j = 0 := by
  by_cases hjlo : j < lo
  · rcases h.2.2 with ⟨rfl, _⟩ | ⟨_, _, hfilter⟩
    · omega
    · simpa only [Finsupp.filter_apply, ite_eq_left hjlo, Finsupp.zero_apply] using
        DFunLike.congr_fun hfilter j
  · have hju : u ≤ j := le_of_not_gt fun hlt => hj ⟨le_of_not_gt hjlo, hlt⟩
    rw [h.digit_eq (h.2.1.trans_le hju), periodicTheta_apply, ite_eq_right (not_lt.mpr hju)]

private theorem IsLBlock.first_digit_le {L : List ℕ} {δ : ℕ →₀ ℕ} {lo u : ℕ}
    (h : IsLBlock L δ lo u) : δ lo ≤ periodicTheta L u lo := by
  rcases h.2.2 with ⟨_, rfl⟩ | ⟨_, hlt, _⟩
  · exact le_rfl
  · exact hlt.le

private theorem IsLBlock.first_digit_lt {L : List ℕ} {δ : ℕ →₀ ℕ} {lo u : ℕ}
    (h : IsLBlock L δ lo u) (hlo : 0 < lo) : δ lo < periodicTheta L u lo := by
  rcases h.2.2 with ⟨rfl, _⟩ | ⟨_, hlt, _⟩
  · omega
  · exact hlt

private theorem exists_finset_integerBlocks {L : List ℕ} {μ : ℕ →₀ ℕ}
    (hμ : μ ∈ periodicZeckendorfCollection L) :
    ∃ S : Finset IntegerBlock,
      (∀ t ∈ S, IsLBlock L t.1 t.2.1 t.2.2) ∧
      (S : Set IntegerBlock).PairwiseDisjoint (fun t => Set.Ico t.2.1 t.2.2) ∧
      ∀ j, μ j = ∑ t ∈ S, t.1 j := by
  classical
  obtain ⟨blocks, hblock, hpair, hsum⟩ := hμ
  have hnodup : blocks.Nodup := hpair.imp_of_mem (fun {a b} ha _ hsep heq => by
    subst b
    exact (not_le_of_gt (hblock a ha).2.1) (hsep.elim id id))
  let : Std.Symm (fun a b : IntegerBlock => a.2.2 ≤ b.2.1 ∨ b.2.2 ≤ a.2.1) :=
    ⟨fun _ _ h => h.symm⟩
  refine ⟨blocks.toFinset, fun t ht => hblock t (List.mem_toFinset.mp ht), ?_, ?_⟩
  · intro a ha b hb hab
    have hs := hpair.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    exact Set.disjoint_left.mpr fun j hj hj' => hs.elim
      (fun h => hj.2.not_ge (h.trans hj'.1)) (fun h => hj'.2.not_ge (h.trans hj.1))
  · intro j
    rw [hsum, ← List.sum_toFinset Prod.fst hnodup, Finsupp.finsetSum_apply]

-- The list-length, leading digit of L, nonzero-block, and strictness conditions are kept
-- as in Lemma 9. The finite argument only needs inclusion and the nonzero leading digit of L'.
set_option linter.unusedVariables false in
/-- **Decomposing $L^*$-blocks into $\tilde L^*$-blocks.** Let $L$ and $\tilde L$ be lists of
natural numbers of length at least $2$ with nonzero first entries whose periodic Zeckendorf
collections satisfy $E \subsetneq \tilde E$. If $\zeta$ is a nonzero proper $L^*$-block with
support interval $[i, b]$, then $\zeta$ is a sum of disjoint proper $\tilde L^*$-blocks whose
support intervals all lie in $[0, b]$, one of which has support interval $[a, b]$ for some $a$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 9 (`integers-2025-A25-lem-9`; arXiv:2308.12872v1, Section 3.3). -/
public theorem exists_lStarBlockSum_of_properLStarBlock (L L' : List ℕ)
    (hL : 2 ≤ L.length) (he : L.getD 0 0 ≠ 0) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0)
    (hsub : periodicZeckendorfCollection L ⊂ periodicZeckendorfCollection L') {ζ : ℕ → ℕ}
    {i b : ℕ} (hζ : IsProperLStarBlock L ζ i b) (hζ0 : ζ ≠ 0) :
    ∃ I, IsLStarBlockSum L' I ζ ∧ (∀ p ∈ I, p.2 ≤ b) ∧ ∃ a, (a, b) ∈ I := by
  classical
  obtain ⟨hib, hprefix, hend, hsupport⟩ := isProperLStarBlock_iff.mp hζ
  let m := b - i + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmb : m ≤ b + 1 := by dsimp [m]; omega
  have hstart : b + 1 - m = i := by dsimp [m]; omega
  have htheta (j : ℕ) (hj : j < m) : periodicTheta L m j = maxLStarBlock L i (b - j) := by
    simpa only [hstart] using periodicTheta_reflect L hmb hj
  have hlast : ζ b < periodicTheta L m 0 := by
    simpa only [htheta 0 hm, Nat.sub_zero] using hend
  have hmem : periodicTheta L m ∈ periodicZeckendorfCollection L := by
    refine ⟨[(periodicTheta L m, 0, m)], ?_, by simp, by simp⟩
    intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨hm, hm, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨S, hS, hdisj, hsum⟩ := exists_finset_integerBlocks (hsub.subset hmem)
  have hdigit (t : IntegerBlock) (ht : t ∈ S) {j : ℕ} (hj : j ∈ Set.Ico t.2.1 t.2.2) :
      periodicTheta L m j = t.1 j := by
    rw [hsum]
    exact Finset.sum_eq_single_of_mem t ht fun u hu hut =>
      (hS u hu).digit_zero fun hju => Set.disjoint_left.mp (hdisj hu ht hut) hju hj
  have hcover {j : ℕ} (hj : 0 < periodicTheta L m j) :
      ∃ t ∈ S, j ∈ Set.Ico t.2.1 t.2.2 := by
    by_contra! h
    rw [hsum, Finset.sum_eq_zero fun t ht => (hS t ht).digit_zero (h t ht)] at hj
    exact (lt_irrefl 0) hj
  -- Blocks starting at or above m need not be retained (they can be zero singleton blocks).
  -- Any block starting below m also ends below m, since a longer block has a nonzero top digit.
  have hbound (t : IntegerBlock) (ht : t ∈ S) (hlo : t.2.1 < m) : t.2.2 ≤ m := by
    by_contra! hu
    have hlt : t.2.1 < t.2.2 - 1 := by omega
    have htop : periodicTheta L m (t.2.2 - 1) = L'.getD 0 0 := by
      rw [hdigit t ht ⟨hlt.le, by omega⟩, (hS t ht).digit_eq hlt, periodicTheta_apply,
        ite_eq_left (by omega), Nat.sub_self, Nat.zero_mod]
    rw [periodicTheta_apply, ite_eq_right (by omega)] at htop
    exact he' htop.symm
  let reflect (t : IntegerBlock) := (b + 1 - t.2.2, b - t.2.1)
  let I := reflect '' {t ∈ (S : Set IntegerBlock) | t.2.1 < m}
  have hreflect (t : IntegerBlock) (ht : t ∈ S) (hlo : t.2.1 < m) {x : ℕ} :
      x ∈ Set.Icc (reflect t).1 (reflect t).2 ↔ x ≤ b ∧ b - x ∈ Set.Ico t.2.1 t.2.2 := by
    have ht' := hbound t ht hlo
    simp only [reflect, Set.mem_Icc, Set.mem_Ico]
    omega
  obtain ⟨last, hlastS, hlastlo, hlastu⟩ := hcover ((Nat.zero_le (ζ b)).trans_lt hlast)
  have hlastlo' : last.2.1 = 0 := Nat.eq_zero_of_le_zero hlastlo
  have hlastI : reflect last ∈ I := ⟨last, ⟨hlastS, by omega⟩, rfl⟩
  refine ⟨I, isLStarBlockSum_iff.mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨t, ⟨ht, hlo⟩, rfl⟩ _ ⟨u, ⟨hu, hu₀⟩, rfl⟩ hne
    exact Set.disjoint_left.mpr fun _ hx hy =>
      Set.disjoint_left.mp (hdisj ht hu (ne_of_apply_ne reflect hne))
        ((hreflect t ht hlo).mp hx).2 ((hreflect u hu hu₀).mp hy).2
  · rintro _ ⟨t, ⟨ht, hlo⟩, rfl⟩
    have htu := hbound t ht hlo
    have hlt := (hS t ht).2.1
    change b + 1 - t.2.2 ≤ b - t.2.1 ∧ _ ∧ _
    refine ⟨by omega, ?_, ?_⟩
    · intro x hx
      change b + 1 - t.2.2 ≤ x ∧ x < b - t.2.1 at hx
      have hj : b - x ∈ Set.Ico t.2.1 t.2.2 :=
        ((hreflect t ht hlo).mp ⟨hx.1, hx.2.le⟩).2
      have hxi : x ∈ Set.Ico i b := ⟨by omega, by omega⟩
      have heq : b - (b - x) = x := by omega
      have hθ := periodicTheta_reflect L' (b := b) (by omega) hj.2
      rw [heq] at hθ
      calc
        ζ x = maxLStarBlock L i x := hprefix hxi
        _ = periodicTheta L m (b - x) := by
          rw [htheta (b - x) (by omega), heq]
        _ = t.1 (b - x) := hdigit t ht hj
        _ = periodicTheta L' t.2.2 (b - x) := (hS t ht).digit_eq (by omega)
        _ = maxLStarBlock L' (reflect t).1 x := hθ
    · have hθ := periodicTheta_reflect L' (b := b) (by omega) hlt
      change ζ (b - t.2.1) < maxLStarBlock L' (b + 1 - t.2.2) (b - t.2.1)
      rw [← hθ]
      have hd := hdigit t ht (j := t.2.1) ⟨le_rfl, hlt⟩
      by_cases hzero : t.2.1 = 0
      · have hle := (hS t ht).first_digit_le
        rw [hzero] at hd hle
        simpa only [hzero, Nat.sub_zero] using (hlast.trans_eq hd).trans_le hle
      · have hpos : 0 < t.2.1 := Nat.pos_of_ne_zero hzero
        have hx : b - t.2.1 ∈ Set.Ico i b := ⟨by omega, by omega⟩
        rw [hprefix hx, ← htheta t.2.1 hlo, hd]
        exact (hS t ht).first_digit_lt hpos
  · intro x hx
    obtain ⟨hix, hxb⟩ := hsupport hx
    rcases eq_or_lt_of_le hxb with rfl | hxb
    · exact Set.mem_iUnion.mpr ⟨reflect last, Set.mem_iUnion.mpr ⟨hlastI,
        (hreflect last hlastS (by omega)).mpr ⟨le_rfl, by simpa using And.intro hlastlo hlastu⟩⟩⟩
    · have hj : 0 < periodicTheta L m (b - x) := by
        rw [htheta (b - x) (by omega), show b - (b - x) = x by omega, ← hprefix ⟨hix, hxb⟩]
        exact Nat.pos_of_ne_zero hx
      obtain ⟨t, ht, hj⟩ := hcover hj
      have hlo : t.2.1 < m := by have := hj.1; omega
      exact Set.mem_iUnion.mpr ⟨reflect t, Set.mem_iUnion.mpr ⟨⟨t, ⟨ht, hlo⟩, rfl⟩,
        (hreflect t ht hlo).mpr ⟨hxb.le, hj⟩⟩⟩
  · rintro _ ⟨t, _, rfl⟩
    exact Nat.sub_le ..
  · exact ⟨(reflect last).1, by simpa [reflect, hlastlo'] using hlastI⟩

end MetaMathlibExt

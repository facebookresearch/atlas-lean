/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Card
public import MathlibExt.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose]
public section

/-- **Number of excedances.** For a permutation $\sigma$ of $\{0, 1, \dots, n-1\}$, an excedance
of $\sigma$ is a point $i$ with $\sigma(i) > i$, and the excedance count $e(\sigma)$ is the number
of excedances of $\sigma$.

Source: Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 130-132; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def excedanceCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i < σ i)).card

/-- **Permutations with all cycles of length at most $r$.** A permutation $\sigma$ of
$\{0, 1, \dots, n-1\}$ is an $r$-minus-associated cycle permutation when every cycle of $\sigma$,
fixed points counted as cycles of length one, has length at most $r$: every fixed point of
$\sigma$ forces $1 \le r$, and every cycle of $\sigma$ of length at least $2$ has length at most
$r$. For $n = 0$ the empty permutation qualifies for every $r$.

Source: Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 257-259;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRMinusAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → 1 ≤ r) ∧ ∀ m ∈ σ.cycleType.toFinset, m ≤ r

/-- **Permutations with all cycles longer than $r$.** A permutation $\sigma$ of
$\{0, 1, \dots, n-1\}$ is an $r$-associated cycle permutation when every cycle of $\sigma$, fixed
points counted as cycles of length one, has length greater than $r$: every fixed point of $\sigma$
forces $r < 1$, and every cycle of $\sigma$ of length at least $2$ has length greater than $r$.
For $n = 0$ the empty permutation qualifies for every $r$.

Source: Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 653-657;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → r < 1) ∧ ∀ m ∈ σ.cycleType.toFinset, r < m

instance (r n : ℕ) : DecidablePred (IsRMinusAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRMinusAssociatedCyclePerm; infer_instance

instance (r n : ℕ) : DecidablePred (IsRAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRAssociatedCyclePerm; infer_instance

/-- **$r$-minus-associated Stirling Eulerian numbers.** For natural numbers $r$, $n$ and
$m$, the $r$-minus-associated Stirling Eulerian number is the number of permutations $\sigma$ of
$\{0, \dots, n-1\}$ all of whose cycles, fixed points counted as cycles of length $1$, have
length at most $r$, and that have exactly $m$ excedances, that is, exactly $m$ indices $i$ with
$\sigma(i) > i$.

Source: Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 257-259; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rMinusAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRMinusAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- **$r$-associated Stirling Eulerian numbers.** For natural numbers $r$, $n$ and $m$, the
$r$-associated Stirling Eulerian number $A^{r}_{n,m}$ is the number of permutations $\sigma$ of
$\{0, \dots, n-1\}$ all of whose cycles, fixed points counted as cycles of length $1$, have
length greater than $r$, and that have exactly $m$ excedances, that is, exactly $m$ indices $i$
with $\sigma(i) > i$.

Source: Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 653-657; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- **Circular Eulerian numbers.** For natural numbers $n$ and $m$, the circular Eulerian number
$C_{n,m}$ is the number of permutations $\sigma$ of $\{0, 1, \dots, n-1\}$ such that $n \ge 1$,
all points lie in a single cycle of $\sigma$ (for any two points $i$ and $j$ there is an integer
$k$ with $\sigma^k(i) = j$), and $\sigma$ has exactly $m$ excedances, that is, exactly $m$ points
$i$ with $\sigma(i) > i$. In particular $C_{0,m} = 0$ for every $m$, and the identity permutation
of a single point counts as circular.

For $n \ge 2$ the permutations with a single cycle through all points are exactly the $n$-cycles.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 5 and 6 (excedance distribution `C_n(x)` over
circular permutations, `C_{1,0} = 1`). -/
def circularEulerian (n m : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (0 < n ∧ ∀ i j : Fin n, σ.SameCycle i j) ∧
      excedanceCount n σ = m)).card

/-- **Small circular Eulerian numbers.** Writing $C_{n,m}$ for the circular Eulerian number, we have
$C_{0,0} = 0$, $C_{1,0} = 1$, $C_{3,1} = 1$ and $C_{3,2} = 1$.

Of the two cyclic permutations of $\{1, 2, 3\}$, $1 \mapsto 3 \mapsto 2 \mapsto 1$ has one
excedance and $1 \mapsto 2 \mapsto 3 \mapsto 1$ has two.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 5. -/
theorem circularEulerian_small :
    circularEulerian 0 0 = 0 ∧ circularEulerian 1 0 = 1 ∧ circularEulerian 3 1 = 1 ∧
      circularEulerian 3 2 = 1 := by
  decide

/-- **Circular permutations are the full cycles.** Let $n \ge 2$ and let $\sigma$ be a
permutation of $\{0, \dots, n-1\}$. Any two points $i$ and $j$ lie in the same cycle of
$\sigma$ (that is, $j = \sigma^k(i)$ for some integer $k$) if and only if $\sigma$ is a cycle,
meaning that it moves some point and any two points it moves lie in the same cycle, and
$\sigma$ moves every point.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 5 and 6 (circular permutations). -/
theorem sameCycle_all_iff_isCycle_support_eq_univ {n : ℕ} (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    (∀ i j : Fin n, σ.SameCycle i j) ↔ σ.IsCycle ∧ σ.support = Finset.univ := by
  constructor
  · intro hall
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra h
      push Not at h
      have h1 : σ = 1 := Equiv.ext h
      have h01 := hall ⟨0, by omega⟩ ⟨1, by omega⟩
      rw [h1, Equiv.Perm.sameCycle_one] at h01
      exact absurd (congrArg Fin.val h01) (by simp)
    refine ⟨⟨x, hx, fun y _ => hall x y⟩, ?_⟩
    ext y
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    exact fun hy => hx (((hall x y).apply_eq_self_iff).mpr hy)
  · rintro ⟨hc, hs⟩ i j
    have hmov : ∀ z, σ z ≠ z := fun z => Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ z)
    exact hc.sameCycle (hmov i) (hmov j)

/-- **Permutations with all cycles of length $r$.** A permutation $\sigma$ of
$\{0, 1, \dots, n-1\}$ is an $r$-cycle permutation when every cycle of $\sigma$, fixed points
counted as cycles of length one, has exactly $r$ elements: for every point $i$, exactly $r$
points $j$ satisfy $\sigma^k(i) = j$ for some integer $k$. For $n = 0$ the condition holds for
every $r$.

These are the paper's $(r)$-cycle permutations, the set $S_n^r$ of Corollary 25.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20-23 and Corollaries 24-26. -/
def IsRCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card = r

instance (r n : ℕ) : DecidablePred (IsRCyclePerm r n) :=
  fun σ => by unfold IsRCyclePerm; infer_instance

/-- **Cycle-type characterization of $r$-cycle permutations.** A permutation $\sigma$ of
$\{0, 1, \dots, n-1\}$ has all its cycles, fixed points counted as cycles of length one, of length
exactly $r$ if and only if every fixed point of $\sigma$ forces $r = 1$ and every cycle of $\sigma$
of length at least $2$ has length exactly $r$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20-23 (cycle lengths of `(r)`-cycle permutations). -/
theorem isRCyclePerm_iff {r n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsRCyclePerm r n σ ↔ (∀ i, σ i = i → r = 1) ∧ ∀ k ∈ σ.cycleType, k = r := by
  have key : ∀ i, σ i ≠ i →
      Finset.univ.filter (σ.SameCycle i) = (σ.cycleOf i).support := by
    intro i hi
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨fun h => ⟨h, Equiv.Perm.mem_support.mpr hi⟩, fun h => h.1⟩
  have fixed : ∀ i, σ i = i → Finset.univ.filter (σ.SameCycle i) = {i} := by
    intro i hi
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact (h.eq_of_left hi).symm
    · rintro rfl
      exact Equiv.Perm.SameCycle.refl σ j
  constructor
  · intro h
    refine ⟨fun i hi => by rw [← h i, fixed i hi, Finset.card_singleton], fun k hk => ?_⟩
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have hc' : c ∈ σ.cycleFactorsFinset := Finset.mem_val.mp hc
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc').1.nonempty_support
    have hca : c = σ.cycleOf a := Equiv.Perm.cycle_is_cycleOf ha hc'
    have hσa : σ a ≠ a :=
      Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc' ha)
    simp only [Function.comp_apply]
    rw [hca, ← key a hσa, h a]
  · rintro ⟨h1, h2⟩ i
    by_cases hi : σ i = i
    · rw [fixed i hi, Finset.card_singleton, h1 i hi]
    · rw [key i hi]
      apply h2
      rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
      exact ⟨σ.cycleOf i, Finset.mem_val.mpr
        (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hi)), rfl⟩

/-- **$r$-cycle Stirling Eulerian numbers.** For natural numbers $r$, $n$ and $m$, the number
$A^{(r)}_{n,m}$ is the number of permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose
cycles, fixed points counted as cycles of length $1$, have length exactly $r$, and that have
exactly $m$ excedances, that is, exactly $m$ indices $i$ with $\sigma(i) > i$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorems 20 and 21. -/
def rCycleStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRCyclePerm r n)).filter (fun σ => excedanceCount n σ = m)).card

/-- **Small $r$-cycle Stirling Eulerian numbers.** Write $A^{(r)}_{n,m}$ for the number of
permutations $\sigma$ of $\{0, \dots, n-1\}$ all of whose cycles, fixed points counted as
cycles of length $1$, have length exactly $r$, and that have exactly $m$ excedances (indices $i$
with $\sigma(i) > i$). Then $A^{(2)}_{0,0} = 1$ (the empty permutation), $A^{(2)}_{2,1} = 1$
(the transposition), $A^{(2)}_{3,1} = 0$, and $A^{(3)}_{3,1} = A^{(3)}_{3,2} = 1$ (the two
$3$-cycles).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 20 and Corollary 25. -/
theorem rCycleStirlingEulerian_small :
    rCycleStirlingEulerian 2 0 0 = 1 ∧ rCycleStirlingEulerian 2 2 1 = 1 ∧
      rCycleStirlingEulerian 2 3 1 = 0 ∧ rCycleStirlingEulerian 3 3 1 = 1 ∧
      rCycleStirlingEulerian 3 3 2 = 1 := by
  decide

/-- **Excedance and cycle generating function of a permutation family.** Let $R$ be a
commutative $\mathbb{Q}$-algebra, let $x, q \in R$, and for each $n$ let $P_n$ be a set of
permutations of $\{0, 1, \dots, n-1\}$. The excedance and cycle exponential generating function
of the family $(P_n)$ is the formal power series in $u$ over $R$

$$\sum_{n \ge 0} \frac{1}{n!} \Big(\sum_{\sigma \in P_n} x^{e(\sigma)} q^{c(\sigma)}\Big) u^n,$$

where $e(\sigma)$ is the number of excedances of $\sigma$ (points $i$ with $\sigma(i) > i$) and
$c(\sigma)$ its number of cycles, fixed points counted as cycles of length one.

With $q = 1$ this is the paper's $P(x, u)$, and for general $q$ its $q$-analogue $P(q, x, u)$.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6 and Corollary 43 (the series `C(x,u)` and
`A_k(x,u)`), Corollary 24 (the weight `x^{e(π)} q^{c(π)}`). -/
noncomputable def permExcedanceCycleEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (P : ∀ n, Equiv.Perm (Fin n) → Prop) [∀ n, DecidablePred (P n)] (x q : R) :
    PowerSeries R :=
  PowerSeries.mk fun n => ((n.factorial : ℚ)⁻¹) •
    ∑ σ ∈ Finset.univ.filter (P n), x ^ excedanceCount n σ * q ^ cycleQuotientCount σ

/-- **Coefficients of the excedance and cycle generating function.** Let $R$ be a commutative
$\mathbb{Q}$-algebra, let $x, q \in R$, and for each $n$ let $P_n$ be a set of permutations of
$\{0, 1, \dots, n-1\}$. For every $n \ge 0$, the coefficient of $u^n$ in the excedance and cycle
exponential generating function of the family $(P_n)$ is
$\frac{1}{n!} \sum_{\sigma \in P_n} x^{e(\sigma)} q^{c(\sigma)}$, where $e(\sigma)$ is the number
of excedances of $\sigma$ and $c(\sigma)$ its number of cycles, fixed points counted as cycles of
length one.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6. -/
theorem coeff_permExcedanceCycleEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (P : ∀ n, Equiv.Perm (Fin n) → Prop) [∀ n, DecidablePred (P n)] (x q : R) (n : ℕ) :
    PowerSeries.coeff n (permExcedanceCycleEGF P x q) = ((n.factorial : ℚ)⁻¹) •
      ∑ σ ∈ Finset.univ.filter (P n), x ^ excedanceCount n σ * q ^ cycleQuotientCount σ := by
  simp [permExcedanceCycleEGF]

/-- **Constant coefficient of the generating function of all permutations.** Let $R$ be a
commutative $\mathbb{Q}$-algebra and let $x, q \in R$. In the excedance and cycle exponential
generating function of the family of all permutations, the coefficient of $u^0$ is $1$.

The only permutation of the empty set has no excedance and no cycle.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6. -/
theorem coeff_zero_permExcedanceCycleEGF_true {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) :
    PowerSeries.coeff 0 (permExcedanceCycleEGF (fun _ _ => True) x q) = 1 := by
  rw [coeff_permExcedanceCycleEGF]
  have he : excedanceCount 0 (1 : Equiv.Perm (Fin 0)) = 0 := by decide
  have hc : cycleQuotientCount (1 : Equiv.Perm (Fin 0)) = 0 := by
    rw [cycleQuotientCount_eq]; simp
  simp [Finset.univ_unique, he, hc]

end
end MetaMathlibExt

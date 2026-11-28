/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Order.Int.LeastGreatest
public import MathlibExt.NumberTheory.BinomidIndex

/-!
# The monoid of lex-minimal extensions

We use zero-based indexing for the binomid indices of Caalim and Tanaka. The gcd of the
maximizing prefix lengths divides every length attaining the same average in a lex-minimal
extension. For a nonempty prefix, this gcd is the least positive eventual period. We also show
that the atoms of an atom-generated submonoid of natural-valued functions form its unique basis.

For a lex-minimal extension of a prefix of length $m \ge 1$ and a capacity $c \ge 1$, the $c$-th
partial sum is the optimal unbounded knapsack value, attained at total weight $c$, with the
first $m$ partial sums as values and their lengths as weights.

## References

* Jonathan Caalim and Yu-ichi Tanaka, *Generalized Binomial Coefficients and the Monoid of
  Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113, pp. 1–14.
  The knapsack result is Proposition 2 (pp. 4–5), which uses Proposition 1 for the tight split.
* Jonathan Caalim and Yu-ichi Tanaka, *Lexicographically Minimal Extension of a Finite Binomid
  Index*, INTEGERS 24 (2024), Article A53, pp. 1–13, Lemma 1 (p. 5): the partial-sum criterion
  and recurrence behind Proposition 1 of the later paper.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The first average is the first entry.** For every sequence $\eta = (e_1, e_2, \dots)$ of
nonnegative integers, the initial average $A_{1,0}(\eta)$ of its first entry equals $e_1$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 2. -/
public theorem binomidAverage_one (η : ℕ → ℕ) : binomidAverage η 1 = η 0 := by
  simp [binomidAverage]

/-- **Indices of maximal average.** For a sequence $\eta = (e_1, e_2, \dots)$ of nonnegative
integers and $m \ge 0$, let $A_i = (e_1 + \dots + e_i)/i$ be the average of the first $i$
entries of $\eta$. The set of maximal-average indices of $\eta$ up to $m$ is the set of all $i$
with $1 \le i \le m$ such that $A_j \le A_i$ for every $j$ with $1 \le j \le m$; for
$m \ge 1$ these are the $i$ with $1 \le i \le m$ and $A_i = A_{\max}$, where
$A_{\max} = \max \{A_i \mid 1 \le i \le m\}$, and for $m = 0$ the set is empty.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 3 (the set `{i ≤ m | A_max = A_i}`). -/
public noncomputable def maxAverageIndices (η : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  open scoped Classical in
  (Finset.Icc 1 m).filter fun i =>
    ∀ j ∈ Finset.Icc 1 m, binomidAverage η j ≤ binomidAverage η i

/-- **Maximal-average indices for $m = 1$.** Let $\eta = (e_1, e_2, \dots)$ be a sequence of
nonnegative integers and $A_i = (e_1 + \dots + e_i)/i$. For $m = 1$, the set of indices
$1 \le i \le m$ at which $A_i$ is maximal among $A_1, \dots, A_m$ is $\{1\}$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 3. -/
public theorem maxAverageIndices_one (η : ℕ → ℕ) : maxAverageIndices η 1 = {1} := by
  simp [maxAverageIndices]

namespace IsLexMinimalExtensionOf

private abbrev prefixSum (η : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, η k

private theorem prefixSum_superadditive {η : ℕ → ℕ} (hη : IsBinomidIndex η) (a b : ℕ) :
    prefixSum η a + prefixSum η b ≤ prefixSum η (a + b) := by
  have h := hη b (a + b) (by omega)
  rw [Nat.add_sub_cancel] at h
  simpa only [prefixSum, Finset.sum_range_add_sum_Ico η (Nat.le_add_right a b)] using
    Nat.add_le_add_left h (prefixSum η a)

/-- Beyond the given prefix a partial sum must be tight at some proper split.
Otherwise lowering just that partial sum preserves superadditivity and gives a smaller extension. -/
private theorem exists_tight_split {η : ℕ → ℕ} {m r : ℕ}
    (hη : IsLexMinimalExtensionOf η m) (hm : 0 < m) (hr : m < r) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = r ∧ prefixSum η a + prefixSum η b = prefixSum η r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hm.trans hr).ne'
  have hsuper := prefixSum_superadditive hη.1
  by_contra hsplit
  have hstrict (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 1) :
      prefixSum η a + prefixSum η b < prefixSum η (n + 1) := by
    exact lt_of_le_of_ne (hab ▸ hsuper a b) fun he => hsplit ⟨a, b, ha, hb, hab, he⟩
  let T (k : ℕ) := if k = n + 1 then prefixSum η k - 1 else prefixSum η k
  have hT0 : T 0 = 0 := by simp [T, prefixSum]
  have hle (k : ℕ) : T k ≤ prefixSum η k := by
    by_cases hk : k = n + 1 <;> simp [T, hk]
  have hT (a b : ℕ) : T a + T b ≤ T (a + b) := by
    by_cases hab : a + b = n + 1
    · obtain rfl | ha := Nat.eq_zero_or_pos a
      · simp [hT0]
      obtain rfl | hb := Nat.eq_zero_or_pos b
      · simp [hT0]
      apply (add_le_add (hle a) (hle b)).trans
      simpa [T, hab] using Nat.le_pred_of_lt (hstrict a b ha hb hab)
    · exact (add_le_add (hle a) (hle b)).trans (by simpa [T, hab] using hsuper a b)
  have hmono : Monotone T :=
    monotone_nat_of_le_succ fun k => (Nat.le_add_right _ _).trans (hT k 1)
  let γ (k : ℕ) := T (k + 1) - T k
  have hsum (k : ℕ) : prefixSum γ k = T k := by
    simpa [prefixSum, γ, hT0] using Finset.sum_range_tsub hmono k
  have hγ : IsBinomidIndex γ := by
    intro k r hkr
    have h := hT (r - k) k
    simp only [Nat.sub_add_cancel hkr, ← hsum] at h
    exact Nat.le_of_add_le_add_left
      (h.trans_eq (Finset.sum_range_add_sum_Ico γ (Nat.sub_le r k)).symm)
  have hearly (k : ℕ) (hk : k < n) : γ k = η k := by
    simp [γ, T, hk.ne, show k ≠ n + 1 by omega, prefixSum, Finset.sum_range_succ]
  have hdrop : γ n < η n := by
    have h := hstrict n 1 (by omega) (by decide) rfl
    simp only [prefixSum, Finset.sum_range_succ] at h
    simp [γ, T, prefixSum, Finset.sum_range_succ]
    omega
  rcases hη.2 γ hγ (fun k hk => hearly k (by omega)) with heq | ⟨j, hj, hlt⟩
  · exact (congrFun heq n).not_gt hdrop
  · rcases lt_trichotomy j n with h | rfl | h
    · exact (hearly j h).not_gt hlt
    · exact (not_lt_of_gt hdrop) hlt
    · exact (hj n h).not_gt hdrop

/-- **Partial sums of a lex-minimal extension solve a knapsack problem.** Let $m \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, and write
$S_i = e_1 + \dots + e_i$. Then for every $c \ge 1$ there are nonnegative integers
$n_1, \dots, n_m$ with $\sum_{i=1}^m n_i i = c$ and $S_c = \sum_{i=1}^m n_i S_i$ that solve the
unbounded knapsack problem with values $S_i$, weights $i$ and capacity $c$: all nonnegative
integers $n'_1, \dots, n'_m$ with $\sum_{i=1}^m n'_i i \le c$ satisfy
$\sum_{i=1}^m n'_i S_i \le \sum_{i=1}^m n_i S_i$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 2 (`integers-2026-A113-prop-2`). -/
public theorem exists_knapsack {η : ℕ → ℕ} {m : ℕ}
    (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) {c : ℕ} (hc : 1 ≤ c) :
    ∃ n : ℕ → ℕ, ∑ i ∈ Finset.Icc 1 m, n i * i = c ∧
      ∑ l ∈ Finset.range c, η l
        = ∑ i ∈ Finset.Icc 1 m, n i * ∑ l ∈ Finset.range i, η l ∧
      ∀ n' : ℕ → ℕ, ∑ i ∈ Finset.Icc 1 m, n' i * i ≤ c →
        ∑ i ∈ Finset.Icc 1 m, n' i * ∑ l ∈ Finset.range i, η l
          ≤ ∑ i ∈ Finset.Icc 1 m, n i * ∑ l ∈ Finset.range i, η l := by
  have hexact (d : ℕ) (hd : 1 ≤ d) : ∃ n : ℕ → ℕ, ∑ i ∈ Finset.Icc 1 m, n i * i = d ∧
      prefixSum η d = ∑ i ∈ Finset.Icc 1 m, n i * prefixSum η i := by
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      by_cases hdm : d ≤ m
      · have hdmem : d ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hd, hdm⟩
        refine ⟨fun i => if i = d then 1 else 0, ?_, ?_⟩ <;>
          simp [ite_mul, hdmem]
      · obtain ⟨a, b, ha, hb, rfl, hs⟩ := hη.exists_tight_split hm (lt_of_not_ge hdm)
        obtain ⟨n₁, hw₁, hv₁⟩ := ih a (Nat.lt_add_of_pos_right hb) ha
        obtain ⟨n₂, hw₂, hv₂⟩ := ih b (Nat.lt_add_of_pos_left ha) hb
        refine ⟨fun i => n₁ i + n₂ i, ?_, ?_⟩
        · simp only [add_mul, Finset.sum_add_distrib, hw₁, hw₂]
        · simpa only [add_mul, Finset.sum_add_distrib, ← hv₁, ← hv₂] using hs.symm
  obtain ⟨n, hw, hv⟩ := hexact c hc
  refine ⟨n, hw, hv, fun n' hn' => ?_⟩
  rw [← hv]
  -- In the dual order, the prefix sums are subadditive, including the empty sum.
  have hsum (s : Finset ℕ) (w : ℕ → ℕ) :
      ∑ i ∈ s, prefixSum η (w i) ≤ prefixSum η (∑ i ∈ s, w i) :=
    Finset.le_sum_of_subadditive (N := ℕᵒᵈ) (prefixSum η) (by exact le_rfl)
      (prefixSum_superadditive hη.isBinomidIndex) s w
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 m, prefixSum η (n' i * i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using
        hsum (Finset.range (n' i)) (fun _ => i)
    _ ≤ prefixSum η (∑ i ∈ Finset.Icc 1 m, n' i * i) := hsum _ _
    _ ≤ prefixSum η c := Finset.sum_le_sum_of_subset (Finset.range_mono hn')

private theorem prefixSum_bound_and_dvd {η : ℕ → ℕ} {m j : ℕ}
    (hη : IsLexMinimalExtensionOf η m) (hj : j ∈ maxAverageIndices η m) {k : ℕ} (hk : 0 < k) :
    (prefixSum η k : ℚ) ≤ binomidAverage η j * k ∧
      ((prefixSum η k : ℚ) = binomidAverage η j * k → (maxAverageIndices η m).gcd id ∣ k) := by
  classical
  simp only [maxAverageIndices, Finset.mem_filter] at hj
  obtain ⟨hjmem, hbest⟩ := hj
  let A := binomidAverage η j
  let g := (maxAverageIndices η m).gcd id
  change (prefixSum η k : ℚ) ≤ A * k ∧ ((prefixSum η k : ℚ) = A * k → g ∣ k)
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hkm : k ≤ m
    · have hmem := Finset.mem_Icc.mpr ⟨hk, hkm⟩
      have hk' : (0 : ℚ) < k := by exact_mod_cast hk
      refine ⟨(div_le_iff₀ hk').mp (hbest k hmem), fun ht => ?_⟩
      have hAk : binomidAverage η k = A := (div_eq_iff hk'.ne').mpr ht
      apply Finset.gcd_dvd (f := id) (b := k)
      simp only [maxAverageIndices, Finset.mem_filter]
      exact ⟨hmem, fun l hl => (hbest l hl).trans_eq hAk.symm⟩
    · obtain ⟨hjpos, hjle⟩ := Finset.mem_Icc.mp hjmem
      obtain ⟨a, b, ha, hb, rfl, hs⟩ :=
        hη.exists_tight_split (hjpos.trans hjle) (lt_of_not_ge hkm)
      obtain ⟨ha_le, ha_dvd⟩ := ih a (by omega) ha
      obtain ⟨hb_le, hb_dvd⟩ := ih b (by omega) hb
      have hs' : (prefixSum η (a + b) : ℚ) = prefixSum η a + prefixSum η b := by
        exact_mod_cast hs.symm
      rw [hs', Nat.cast_add, mul_add]
      refine ⟨add_le_add ha_le hb_le, fun ht => ?_⟩
      obtain ⟨ha_eq, hb_eq⟩ := (add_eq_add_iff_eq_and_eq ha_le hb_le).mp ht
      exact dvd_add (ha_dvd ha_eq) (hb_dvd hb_eq)

end IsLexMinimalExtensionOf

/-- **Every index with maximal average is a multiple of the gcd of those up to $m$.** Let
$m \ge 0$, let $\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries,
with averages $A_i = (e_1 + \dots + e_i)/i$, let $J$ be the set of indices $1 \le j \le m$ with
$A_j = \max \{A_{j'} \mid 1 \le j' \le m\}$, and let $g = \gcd J$. Then $g$ divides every
$i \ge 1$ such that $A_i = A_j$ for some $j \in J$.

Since every element of $J$ is such an index, $g$ is also the greatest common divisor of all
$i \ge 1$ with $A_i = A_j$ for some $j \in J$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 2 (`integers-2026-A113-lem-2`). -/
public theorem IsLexMinimalExtensionOf.gcd_maxAverageIndices_dvd {η : ℕ → ℕ}
    {m : ℕ} (hη : IsLexMinimalExtensionOf η m) {i : ℕ} (hi : 1 ≤ i)
    (hmax : ∃ j ∈ maxAverageIndices η m, binomidAverage η i = binomidAverage η j) :
    (maxAverageIndices η m).gcd id ∣ i := by
  obtain ⟨j, hj, heq⟩ := hmax
  have hi' : (0 : ℚ) < i := by exact_mod_cast (show 0 < i from hi)
  exact (hη.prefixSum_bound_and_dvd hj hi).2 ((div_eq_iff hi'.ne').mp heq)

namespace IsLexMinimalExtensionOf

/-- A nonnegative subadditive deficit vanishing on all large multiples of `g` eventually
attains the minimum of each residue class everywhere in that class. -/
private theorem eventually_periodic_deficit {d : ℕ → ℤ} {g L : ℕ} (hg : 0 < g)
    (hnonneg : ∀ n, 0 ≤ d n) (hadd : ∀ i j, d (i + j) ≤ d i + d j)
    (hzero : ∀ n ≥ L, g ∣ n → d n = 0) :
    ∃ N, ∀ n ≥ N, d (n + g) = d n := by
  classical
  have hmin (r : Fin g) : ∃ a : ℕ, a % g = r ∧ ∀ n, n % g = r → d a ≤ d n := by
    let P (z : ℤ) := ∃ n : ℕ, n % g = r ∧ d n = z
    obtain ⟨_, ⟨a, ha, rfl⟩, hleast⟩ := Int.exists_least_of_bdd (P := P)
      ⟨0, by rintro _ ⟨n, _, rfl⟩; exact hnonneg n⟩
      ⟨d r, r, Nat.mod_eq_of_lt r.isLt, rfl⟩
    exact ⟨a, ha, fun n hn => hleast _ ⟨n, hn, rfl⟩⟩
  choose a ha hmin using hmin
  let M := Finset.univ.sup a
  have hstable (r : Fin g) (n : ℕ) (hn : M + L ≤ n) (hr : n % g = r) : d n = d (a r) := by
    have hle : a r ≤ M := Finset.le_sup (Finset.mem_univ r)
    have hmod : a r ≡ n [MOD g] := (ha r).trans hr.symm
    have hz := hzero (n - a r) (by omega) ((Nat.modEq_iff_dvd' (by omega)).mp hmod)
    have hs := hadd (a r) (n - a r)
    rw [Nat.add_sub_of_le (by omega : a r ≤ n), hz, add_zero] at hs
    exact hs.antisymm (hmin r n hr)
  refine ⟨M + L, fun n hn => ?_⟩
  let r : Fin g := ⟨n % g, Nat.mod_lt _ hg⟩
  exact (hstable r _ (by omega) (Nat.add_mod_right n g)).trans (hstable r n hn rfl).symm

/-- If the zeros on the tail are exactly the multiples of `g`, a period of the first
differences must preserve these zeros. Along a progression of step `q` the drift is constant,
and after `g` steps the progression returns to a zero. -/
private theorem dvd_of_periodic_differences {d : ℕ → ℤ} {g L N q : ℕ} (hg : 0 < g)
    (hzeros : ∀ n ≥ L, d n = 0 ↔ g ∣ n)
    (hperiod : ∀ n ≥ N, d (n + q + 1) - d (n + q) = d (n + 1) - d n) : g ∣ q := by
  let b := (N + L) * g
  have hb : N + L ≤ b := Nat.le_mul_of_pos_right _ hg
  have hgb : g ∣ b := dvd_mul_left ..
  have hbase := (hzeros b (by omega)).2 hgb
  have hstep (n : ℕ) (hn : b ≤ n) : d (n + q) - d n = d (b + q) := by
    induction n, hn using Nat.le_induction with
    | base => simp [hbase]
    | succ n hn ih =>
      have h := hperiod n (by omega)
      rw [Nat.succ_add]
      change d (n + q + 1) - d (n + 1) = d (b + q)
      omega
  have hsteps (t : ℕ) : d (b + t * q) = t * d (b + q) := by
    induction t with
    | zero => simpa using hbase
    | succ t ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, Nat.cast_succ, add_mul, one_mul]
      have := hstep (b + t * q) (by omega)
      omega
  have hz := (hzeros (b + g * q) (by omega)).2 (dvd_add hgb (dvd_mul_right ..))
  rw [hsteps] at hz
  have hnext := (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hg.ne')
  exact (Nat.dvd_add_right hgb).mp ((hzeros _ (by omega : L ≤ b + q)).mp hnext)

end IsLexMinimalExtensionOf

/-- **Minimal period of a lex-minimal extension.** Let $m \ge 1$ and let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of $(e_1, \dots, e_m)$. For
$1 \le i \le m$ let $A_i = (e_1 + \dots + e_i)/i$, and let $A_{\max}$ be the largest of
$A_1, \dots, A_m$. Let $g$ be the greatest common divisor of the indices $1 \le i \le m$ with
$A_i = A_{\max}$. Then $g$ is the minimal eventual period of $\eta$: $g \ge 1$,
$e_{i+g} = e_i$ for all sufficiently large $i$, and every $q \ge 1$ with $e_{i+q} = e_i$ for
all sufficiently large $i$ satisfies $g \le q$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Theorem 1 (`integers-2026-A113-thm-1`). -/
public theorem IsLexMinimalExtensionOf.isLeast_period_gcd_maxAverageIndices
    {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) :
    IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i}
      ((maxAverageIndices η m).gcd id) := by
  classical
  let J := maxAverageIndices η m
  let g := J.gcd id
  obtain ⟨j, hj, hbest⟩ := (Finset.Icc 1 m).exists_max_image (binomidAverage η)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩
  have hjJ : j ∈ J := by
    simpa only [J, maxAverageIndices, Finset.mem_filter] using And.intro hj hbest
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjQ : (0 : ℚ) < j := by exact_mod_cast hjpos
  have hg : 0 < g := Nat.pos_of_ne_zero fun h =>
    hjpos.ne' (Finset.gcd_eq_zero_iff.mp h j hjJ)
  -- Scale the difference between the maximal average and each prefix average to an integer.
  let d (n : ℕ) : ℤ := (prefixSum η j : ℤ) * n - (prefixSum η n : ℤ) * j
  have hnonneg (n : ℕ) : 0 ≤ d n := by
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · simp [d, prefixSum]
    have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
    have havg : binomidAverage η n ≤ binomidAverage η j :=
      (div_le_iff₀ hnQ).mpr (hη.prefixSum_bound_and_dvd hjJ hn).1
    apply sub_nonneg.mpr
    exact_mod_cast (div_le_div_iff₀ hnQ hjQ).mp havg
  have heq (n : ℕ) (hn : 0 < n) : d n = 0 ↔ binomidAverage η n = binomidAverage η j := by
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [binomidAverage, binomidAverage, div_eq_div_iff hnQ hjQ.ne']
    change _ - _ = (0 : ℤ) ↔ _
    rw [sub_eq_zero, eq_comm]
    norm_cast
  have hadd (a b : ℕ) : d (a + b) ≤ d a + d b := by
    have hs : (prefixSum η a : ℤ) + prefixSum η b ≤ (prefixSum η (a + b) : ℤ) := by
      exact_mod_cast prefixSum_superadditive hη.1 a b
    simp only [d, Nat.cast_add, mul_add]
    linarith [mul_le_mul_of_nonneg_right hs (Int.natCast_nonneg j)]
  -- All sufficiently large multiples of the gcd are sums of maximizing lengths.
  obtain ⟨L, hL⟩ := Nat.exists_mem_closure_of_ge (J : Set ℕ)
  have hdiv : Nat.setGcd (J : Set ℕ) ∣ g :=
    Finset.dvd_gcd fun _ hn => Nat.setGcd_dvd_of_mem hn
  have hclosure {n : ℕ} (hn : n ∈ AddSubmonoid.closure (J : Set ℕ)) : d n = 0 := by
    induction hn using AddSubmonoid.closure_induction with
    | zero => simp [d, prefixSum]
    | mem n hn =>
      change n ∈ J at hn
      simp only [J, maxAverageIndices, Finset.mem_filter] at hn
      obtain ⟨hnmem, hnmax⟩ := hn
      exact (heq n (Finset.mem_Icc.mp hnmem).1).mpr ((hbest n hnmem).antisymm (hnmax j hj))
    | add a b _ _ ha hb =>
      have h := hadd a b
      rw [ha, hb, zero_add] at h
      exact h.antisymm (hnonneg _)
  have hzeros (n : ℕ) (hn : L + 1 ≤ n) : d n = 0 ↔ g ∣ n := by
    refine ⟨fun hz => hη.gcd_maxAverageIndices_dvd (by omega) ⟨j, hjJ, (heq n (by omega)).mp hz⟩,
      fun hd => hclosure (hL n (by omega) (hdiv.trans hd))⟩
  have hdiff (n : ℕ) : d (n + 1) - d n = prefixSum η j - (η n : ℤ) * j := by
    simp only [d, prefixSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨N, hN⟩ := eventually_periodic_deficit hg hnonneg hadd (fun n hn => (hzeros n hn).mpr)
  refine ⟨⟨hg, N, fun n hn => ?_⟩, ?_⟩
  · have h := hdiff (n + g)
    rw [Nat.add_right_comm n g 1, hN (n + 1) (by omega), hN n hn, hdiff] at h
    have hmul := sub_right_injective h
    exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hjpos.ne' : (j : ℤ) ≠ 0) hmul.symm
  · rintro q ⟨hq, T, hT⟩
    apply Nat.le_of_dvd hq
    apply dvd_of_periodic_differences hg hzeros (N := T)
    intro n hn
    rw [hdiff, hdiff, hT n hn]

/-- **Basis of a submonoid.** Let $M$ and $B$ be subsets of an additive commutative monoid.
Then $B$ is a basis of $M$ when $M$ is the submonoid $\langle B \rangle$ generated by $B$ and
no element of $B$ is a nonnegative integer combination of elements of $B$ in which its own
coefficient is $0$: for all pairwise distinct $\beta_1, \dots, \beta_n \in B$, all nonnegative
integers $c_1, \dots, c_n$ and every $j$, if $\beta_j = \sum_{i=1}^n c_i \beta_i$ then
$c_j \ge 1$.

The elements $\beta_i$ are required to be distinct: the paper's wording allows repeated
entries, under which $\beta = (b, b)$ and $b = 0 \cdot b + 1 \cdot b$ would rule out every
nonempty $B$; its uniqueness proof uses distinct entries.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (definition of a basis). -/
public def IsAddMonoidBasis {α : Type*} [AddCommMonoid α] (M B : Set α) : Prop :=
  (AddSubmonoid.closure B : Set α) = M ∧
    ∀ (n : ℕ) (β : Fin n → α), Function.Injective β → (∀ i, β i ∈ B) →
      ∀ (c : Fin n → ℕ) (j : Fin n), β j = ∑ i, c i • β i → 1 ≤ c j

/-- **A monoid basis does not contain zero.** Let $\alpha$ be an additive commutative monoid and
let $M$ and $B$ be subsets of $\alpha$. If $B$ is a basis of $M$, then $0 \notin B$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4. -/
public theorem IsAddMonoidBasis.zero_notMem {α : Type*} [AddCommMonoid α] {M B : Set α}
    (h : IsAddMonoidBasis M B) : (0 : α) ∉ B := by
  intro h0
  have := h.2 1 (fun _ => 0) (fun a b _ => Subsingleton.elim a b) (fun _ => h0)
    (fun _ => 0) 0 (by simp)
  simp at this

/-- **The empty set is a basis of the zero submonoid.** In every additive commutative monoid,
the empty set is a basis of the subset $\{0\}$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4. -/
public theorem isAddMonoidBasis_empty {α : Type*} [AddCommMonoid α] :
    IsAddMonoidBasis ({0} : Set α) ∅ :=
  ⟨by simp, fun _ _ _ hβ _ j _ => absurd (hβ j) (Set.notMem_empty _)⟩

/-- A combination of a subset of a basis can equal a basis element only in that subset. -/
private theorem IsAddMonoidBasis.mem_of_mem_closure {α : Type*} [AddCommMonoid α]
    {M B S : Set α} (hB : IsAddMonoidBasis M B) (hSB : S ⊆ B) {x : α} (hx : x ∈ B)
    (hgen : x ∈ AddSubmonoid.closure S) : x ∈ S := by
  classical
  obtain ⟨c, t, ht, hsupp, hsum⟩ := AddSubmonoid.mem_closure_iff_exists_finset_subset.mp hgen
  by_contra hxS
  have hxt : x ∉ t := fun h => hxS (ht h)
  have hc : c x = 0 := Function.support_subset_iff'.mp hsupp x hxt
  -- Include x in the indexed family, with coefficient zero.
  let u := insert x t
  let e := u.equivFin
  let j := e ⟨x, Finset.mem_insert_self x t⟩
  have hu : ↑u ⊆ B := by
    simpa [u] using Set.insert_subset hx (ht.trans hSB)
  have hpos := hB.2 u.card (fun i => (e.symm i : α))
    (Subtype.val_injective.comp e.symm.injective) (fun i => hu (e.symm i).property)
    (fun i => c (e.symm i)) j (by
      rw [e.symm.sum_comp (fun a : u => c a • (a : α)),
        Finset.sum_coe_sort u (fun a => c a • a)]
      simpa [u, j, hc, hxt] using hsum.symm)
  simp [j, hc] at hpos

/-- **Atoms are the unique basis of an atom-generated submonoid.** Let $\iota$ be a type and
let $M$ be a submonoid of $\mathbb{N}^\iota$ under componentwise addition. Let $A$ be the set
of atoms of $M$: the elements $a \in M$ with $a \ne 0$ such that $y = 0$ or $z = 0$ whenever
$a = y + z$ with $y, z \in M$. If every element of $M$ is a finite sum of elements of $A$, then
a set $B \subseteq \mathbb{N}^\iota$ is a basis of $M$ if and only if $B = A$; that is, $A$ is
the unique basis of $M$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 4 (`integers-2026-A113-prop-4`). -/
public theorem isAddMonoidBasis_iff_eq_atoms {ι : Type*} (M : AddSubmonoid (ι → ℕ))
    (hM : ∀ x ∈ M, x ∈ AddSubmonoid.closure
      {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0})
    (B : Set (ι → ℕ)) :
    IsAddMonoidBasis (M : Set (ι → ℕ)) B ↔
      B = {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0} := by
  classical
  let A : Set (ι → ℕ) :=
    {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0}
  change IsAddMonoidBasis (M : Set (ι → ℕ)) B ↔ B = A
  have hAM : A ⊆ M := fun _ ha => ha.1
  -- An atom in the closure of a subset of M must already belong to that subset.
  have atom_mem {S : Set (ι → ℕ)} (hS : S ⊆ M) {x} (hx : x ∈ AddSubmonoid.closure S) :
      x ∈ A → x ∈ S := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => exact fun _ => hx
    | zero => exact fun ha => (ha.2.1 rfl).elim
    | add y z hy hz ihy ihz =>
      intro ha
      obtain rfl | rfl := ha.2.2 y (AddSubmonoid.closure_le.mpr hS hy) z
        (AddSubmonoid.closure_le.mpr hS hz) rfl
      · simp only [zero_add] at ha ⊢
        exact ihz ha
      · simp only [add_zero] at ha ⊢
        exact ihy ha
  constructor
  · intro hB
    have hclosure : AddSubmonoid.closure B = M := SetLike.coe_injective hB.1
    have hBM : B ⊆ M := hclosure ▸ AddSubmonoid.subset_closure
    have hAB : A ⊆ B := fun x hx => atom_mem hBM (hclosure ▸ hAM hx) hx
    exact Set.Subset.antisymm (fun x hx => hB.mem_of_mem_closure hAB hx (hM x (hBM hx))) hAB
  · rintro rfl
    refine ⟨Set.Subset.antisymm (AddSubmonoid.closure_le.mpr hAM) (fun x => hM x), ?_⟩
    intro n β hinj hβ c j heq
    by_contra! hj
    have hc : c j = 0 := by omega
    let S := A \ {β j}
    have hgen : β j ∈ AddSubmonoid.closure S := by
      rw [heq]
      apply AddSubmonoid.sum_mem
      intro i _
      by_cases hij : i = j
      · simp [hij, hc]
      · exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure
          (show β i ∈ S from ⟨hβ i, fun h => hij (hinj h)⟩)) _
    exact (atom_mem (S := S) (fun _ h => hAM h.1) hgen (hβ j)).2 rfl

/-- **Atomic binomid index.** A sequence $\eta$ of nonnegative integers is a nonzero atomic
binomid index (an element of the paper's set $\mathrm{Atom}$) when $\eta$ is a nonzero binomid
index that is not the sum of two nonzero binomid indices: whenever $\eta = \eta_1 + \eta_2$
termwise with $\eta_1$ and $\eta_2$ binomid indices, $\eta_1 = 0$ or $\eta_2 = 0$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (definition of atomic). -/
public def IsAtomicBinomidIndex (η : ℕ → ℕ) : Prop :=
  IsBinomidIndex η ∧ η ≠ 0 ∧
    ∀ η₁ η₂ : ℕ → ℕ, IsBinomidIndex η₁ → IsBinomidIndex η₂ → η = η₁ + η₂ →
      η₁ = 0 ∨ η₂ = 0

/-- **The constant sequence $1$ is atomic.** The constant sequence $(1, 1, 1, \dots)$ is a
nonzero atomic binomid index: it is a nonzero binomid index that is not the sum of two nonzero
binomid indices.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (example of `(E_m)^∞` with `m = 1`). -/
public theorem isAtomicBinomidIndex_one : IsAtomicBinomidIndex fun _ => 1 := by
  have key : ∀ γ : ℕ → ℕ, IsBinomidIndex γ → ∀ i, γ 0 ≤ γ i := fun γ hγ i => by
    simpa using hγ 1 (i + 1) (by omega)
  refine ⟨isBinomidIndex_const 1, fun h => by simpa using congrFun h 0, ?_⟩
  intro η₁ η₂ h₁ h₂ h
  have hs : ∀ i, η₁ i + η₂ i = 1 := fun i => by simpa [eq_comm] using congrFun h i
  rcases Nat.eq_zero_or_pos (η₁ 0) with h0 | h0
  · left
    funext i
    have := key η₂ h₂ i
    have := hs 0
    have := hs i
    change η₁ i = 0
    omega
  · right
    funext i
    have := key η₁ h₁ i
    have := hs 0
    have := hs i
    change η₂ i = 0
    omega

private theorem IsLexMinimalExtensionOf.left_of_add {η₁ η₂ : ℕ → ℕ} {k : ℕ}
    (h : IsLexMinimalExtensionOf (η₁ + η₂) k) (h₁ : IsBinomidIndex η₁)
    (h₂ : IsBinomidIndex η₂) : IsLexMinimalExtensionOf η₁ k := by
  refine ⟨h₁, fun γ hγ hprefix => ?_⟩
  have hsum : IsBinomidIndex (γ + η₂) := by
    intro m n hmn
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using
      add_le_add (hγ m n hmn) (h₂ m n hmn)
  rcases h.2 (γ + η₂) hsum (fun i hi => congrArg (· + η₂ i) (hprefix i hi)) with
    heq | ⟨j, hj, hlt⟩
  · exact Or.inl (funext fun i => Nat.add_right_cancel (congrFun heq i))
  · exact Or.inr ⟨j, fun i hi => Nat.add_right_cancel (hj i hi), Nat.lt_of_add_lt_add_right hlt⟩

/-- **Summands of a lex-minimal extension are lex-minimal.** Let $\eta_1$ and $\eta_2$ be
infinite binomid indices and let $k \ge 0$. If the termwise sum $\eta_1 + \eta_2$ is the
lex-minimal extension of its first $k$ entries, then $\eta_1$ is the lex-minimal extension of
its first $k$ entries and $\eta_2$ is the lex-minimal extension of its first $k$ entries.

Since every lex-minimal extension is the lex-minimal extension of its first $k$ entries for some
$k$, this contains the first claim of the source: if $\eta_1 + \eta_2$ is a lex-minimal
extension, then so are $\eta_1$ and $\eta_2$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 3 (`integers-2026-A113-prop-3`). -/
public theorem IsLexMinimalExtensionOf.of_add {η₁ η₂ : ℕ → ℕ} {k : ℕ}
    (h : IsLexMinimalExtensionOf (η₁ + η₂) k) (h₁ : IsBinomidIndex η₁)
    (h₂ : IsBinomidIndex η₂) :
    IsLexMinimalExtensionOf η₁ k ∧ IsLexMinimalExtensionOf η₂ k :=
  ⟨h.left_of_add h₁ h₂, left_of_add (add_comm η₁ η₂ ▸ h) h₂ h₁⟩

end

end MetaMathlibExt

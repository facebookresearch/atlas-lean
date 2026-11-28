/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Quasi-shuffle product for Bradley–Zhao q-multiple zeta values

For two lists of positive integers whose first entry, when present, is at least $2$,
the product of their Bradley–Zhao q-multiple zeta values is the sum over the
quasi-shuffle with letter product $z_a \diamond z_b = z_{a+b} + z_{a+b-1}$.

At a finite cutoff, raising the cutoff by one adds exactly the summands with the
new largest index. In the product, that index can occur on either side alone or on
both sides. The last case uses the two-term letter product. For an admissible list,
terms beyond the cutoff vanish in any fixed degree once the cutoff exceeds that degree.

## References

* Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
  pp. 1–41, Definitions 1, 9 and 10, and Proposition 5.
  <https://math.colgate.edu/~integers/y6/y6.pdf>
* David M. Bradley, *Multiple q-zeta values*, Journal of Algebra 283 (2005),
  pp. 752–798, Section 2 (q-stuffle multiplication).
* Jianqiang Zhao, *Multiple q-zeta functions and multiple q-polylogarithms*,
  The Ramanujan Journal 14 (2007), pp. 189–221 (Bradley–Zhao model).
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Partial sums of general qMZVs.** Let $(k_1, Q_1), \dots, (k_r, Q_r)$ be pairs of natural
numbers $k_j$ and polynomials $Q_j \in \mathbb{Q}[X]$, and let $M$ be a natural number. The
partial sum is the formal power series in $q$ over $\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{Q_j(q^{m_j})}{(1 - q^{m_j})^{k_j}},$$
where the sum runs over integers $m_1, \dots, m_r$ and $1/(1 - q^m)$ is the inverse in
$\mathbb{Q}[[q]]$. For $r = 0$ it equals $1$ for every $M$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn), defining sum truncated at
`m₁ < M`. -/
public noncomputable def qMZVPartial : List (ℕ × Polynomial ℚ) → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | (k, Q) :: kQ, M => ∑ m ∈ Finset.Ioo 0 M,
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m

/-- **General q-multiple zeta values.** For natural numbers $k_1, \dots, k_r$ and polynomials
$Q_1, \dots, Q_r \in \mathbb{Q}[X]$, the general qMZV $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$
is the formal power series in $q$ over $\mathbb{Q}$ whose coefficient of $q^N$, for every $N$, is
the coefficient of $q^N$ in the finite sum
$\sum_{N \ge m_1 > m_2 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$
over integers $m_1, \dots, m_r$, and $\zeta_q(\varnothing; \varnothing) = 1$.

When $Q_1(0) = 0$ (the paper's condition $Q_1 \in X \mathbb{Q}[X]$), the summands with
$m_1 > N$ have $q$-adic order greater than $N$, so this is the series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$; for other data
the value is a junk value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn). -/
public noncomputable def qMZV : List (ℕ × Polynomial ℚ) → ℚ⟦X⟧
  | [] => 1
  | (k, Q) :: kQ => PowerSeries.mk fun N => coeff N (∑ m ∈ Finset.Ioo 0 (N + 1),
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m)

/-- **Bradley–Zhao q-multiple zeta values.** For an index $k = (k_1, \dots, k_r)$ of natural
numbers, the Bradley–Zhao q-multiple zeta value is the general qMZV
$\zeta_q^{BZ}(k) = \zeta_q(k_1, \dots, k_r; X^{k_1 - 1}, \dots, X^{k_r - 1})$, a formal power
series in $q$ over $\mathbb{Q}$, where $k_j - 1$ is truncated at $0$. For an admissible index
($k_1 \ge 2$ and all $k_i \ge 1$) it equals

$$\zeta_q^{BZ}(k) = \sum_{m_1 > \dots > m_r > 0} \prod_{j=1}^{r}
\frac{q^{m_j (k_j - 1)}}{(1 - q^{m_j})^{k_j}};$$

for other indices the value has no intended meaning.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public noncomputable def bzQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  qMZV (k.map fun k => (k, Polynomial.X ^ (k - 1)))

/-- **Quasi-shuffle product.** Fix an alphabet and a product of letters $a \diamond b$, a formal
sum of letters given as a finite list (possibly empty, possibly with repetitions). The
quasi-shuffle product $u \ast v$ of two words $u$ and $v$ is the formal sum of words, recorded as
a list, defined recursively by $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty word
$\mathbf{1}$ and by
$a u \ast b v = a (u \ast b v) + b (a u \ast v) + (a \diamond b)(u \ast v)$
for letters $a$, $b$ and words $u$, $v$. Here a letter, or a formal sum of letters, written in
front of a formal sum of words is prepended to each of its words, and the terms are listed in
the order of the formula.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, quasi-shuffle products of Section 2 (the induced quasi-shuffle
products on `M`, `𝔎`, `𝔥¹`). -/
public def quasiShuffle {α : Type*} (d : α → α → List α) : List α → List α → List (List α)
  | [], v => [v]
  | a :: u, [] => [a :: u]
  | a :: u, b :: v =>
      (quasiShuffle d u (b :: v)).map (a :: ·) ++ (quasiShuffle d (a :: u) v).map (b :: ·) ++
        (d a b).flatMap fun c => (quasiShuffle d u v).map (c :: ·)
termination_by u v => u.length + v.length

open Finset

local notation "T" => (fun (w : List ℕ) (M : ℕ) =>
  qMZVPartial (List.map (fun k => (k, Polynomial.X ^ (k - 1))) w) M)

local notation "W" => (fun (a m : ℕ) =>
  ((X : ℚ⟦X⟧) ^ m) ^ (a - 1) * ((1 - X ^ m)⁻¹) ^ a)

local notation "shuffleBZ" => (quasiShuffle fun (a b : ℕ) => [a + b, a + b - 1])

-- The difference between successive cutoffs is the term with largest index `m`.
private lemma partial_succ {m : ℕ} (hm : 0 < m) (a : ℕ) (u : List ℕ) :
    T (a :: u) (m + 1) = T (a :: u) m + W a m * T u m := by
  simp only [List.map_cons, qMZVPartial, map_pow, Polynomial.aeval_X,
    ← Ico_add_one_left_eq_Ioo, zero_add]
  exact sum_Ico_succ_top (a := 1) (b := m) hm (fun i => W a i * T u i)

private lemma sum_partial_succ {m : ℕ} (hm : 0 < m) (a : ℕ) (l : List (List ℕ)) :
    (l.map fun w => T (a :: w) (m + 1)).sum =
      (l.map fun w => T (a :: w) m).sum + W a m * (l.map fun w => T w m).sum := by
  simp only [partial_succ hm, List.sum_map_add, List.sum_map_mul_left]

-- A tie at the largest index contributes two letters rather than one.
private lemma weight_mul {m a b : ℕ} (hm : 0 < m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    W a m * W b m = W (a + b) m + W (a + b - 1) m := by
  let x := (X : ℚ⟦X⟧) ^ m
  let y := (1 - x)⁻¹
  have hy' : y - x * y = 1 := by
    have h := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ m) (by simp [hm.ne'])
    rw [sub_mul, one_mul] at h
    exact h
  have hy : y = x * y + 1 := (sub_eq_iff_eq_add.mp hy').trans (add_comm _ _)
  change (x ^ (a - 1) * y ^ a) * (x ^ (b - 1) * y ^ b) = _
  have h₀ : a - 1 + (b - 1) = a + b - 1 - 1 := by omega
  have h₁ : a + b - 1 - 1 + 1 = a + b - 1 := by omega
  have h₂ : a + b - 1 + 1 = a + b := by omega
  rw [mul_mul_mul_comm, ← pow_add, ← pow_add, h₀]
  calc
    _ = x ^ (a + b - 1 - 1) * y ^ (a + b - 1) * y := by rw [mul_assoc, ← pow_succ, h₂]
    _ = x ^ (a + b - 1 - 1) * y ^ (a + b - 1) * (x * y + 1) := congrArg (_ * ·) hy
    _ = (x ^ (a + b - 1 - 1) * x) * (y ^ (a + b - 1) * y) +
        x ^ (a + b - 1 - 1) * y ^ (a + b - 1) := by ring
    _ = _ := by rw [← pow_succ, ← pow_succ, h₁, h₂]

-- At the finite level even tails whose head is 1 can enter the induction.
private lemma partial_mul (M : ℕ) (u v : List ℕ) (hu : ∀ k ∈ u, 1 ≤ k)
    (hv : ∀ k ∈ v, 1 ≤ k) :
    T u (M + 1) * T v (M + 1) = ((shuffleBZ u v).map (T · (M + 1))).sum := by
  induction M generalizing u v with
  | zero =>
    have hempty : Ioo 0 1 = ∅ := by decide
    cases u <;> cases v <;> simp [quasiShuffle, qMZVPartial, hempty, Function.comp_def]
  | succ M ih =>
    rcases u with _ | ⟨a, u⟩
    · simp [quasiShuffle, qMZVPartial]
    rcases v with _ | ⟨b, v⟩
    · simp [quasiShuffle, qMZVPartial]
    have ha := hu a List.mem_cons_self
    have hb := hv b List.mem_cons_self
    have hu' (k : ℕ) (hk : k ∈ u) : 1 ≤ k := hu k (List.mem_cons_of_mem _ hk)
    have hv' (k : ℕ) (hk : k ∈ v) : 1 ≤ k := hv k (List.mem_cons_of_mem _ hk)
    have hm : 0 < M + 1 := Nat.succ_pos _
    rw [partial_succ hm a u, partial_succ hm b v]
    calc
      _ = T (a :: u) (M + 1) * T (b :: v) (M + 1) +
          W a (M + 1) * (T u (M + 1) * T (b :: v) (M + 1)) +
          W b (M + 1) * (T (a :: u) (M + 1) * T v (M + 1)) +
          (W (a + b) (M + 1) + W (a + b - 1) (M + 1)) * (T u (M + 1) * T v (M + 1)) := by
        rw [← weight_mul hm ha hb]
        ring
      _ = _ := by
        rw [ih (a :: u) (b :: v) hu hv, ih u (b :: v) hu' hv,
          ih (a :: u) v hu hv', ih u v hu' hv']
        simp only [quasiShuffle.eq_3, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.map_append, List.sum_append, List.map_map, Function.comp_def, sum_partial_succ hm]
        ring

private lemma head_ge_two_of_mem_shuffleBZ {u v w : List ℕ}
    (hu : ∀ k ∈ u.head?, 2 ≤ k) (hv : ∀ k ∈ v.head?, 2 ≤ k) (hw : w ∈ shuffleBZ u v) :
    ∀ k ∈ w.head?, 2 ≤ k := by
  rcases u with _ | ⟨a, u⟩
  · simpa [quasiShuffle] using (fun h : w = v => h ▸ hv) (by simpa [quasiShuffle] using hw)
  rcases v with _ | ⟨b, v⟩
  · exact (fun h : w = a :: u => h ▸ hu) (by simpa [quasiShuffle] using hw)
  have ha : 2 ≤ a := hu a (by simp)
  have hb : 2 ≤ b := hv b (by simp)
  simp only [quasiShuffle.eq_3, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_map] at hw
  rcases hw with (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) | (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩)
  · exact hu
  · exact hv
  · simpa using (show 2 ≤ a + b by omega)
  · simpa using (show 2 ≤ a + b - 1 by omega)

/-- **Bradley–Zhao coefficients at a finite cutoff.** If the first entry of `w`, when present,
 is at least $2$, the coefficient of $q^N$ in its Bradley–Zhao qMZV equals the same coefficient
 in the partial sum with all indices strictly below any bound `M` greater than `N`.
 Here the letter of weight $k$ uses numerator $X^{k-1}$, with truncated subtraction. -/
public theorem coeff_bzQMZV_eq_coeff_partial (w : List ℕ) (h : ∀ k ∈ w.head?, 2 ≤ k)
    {N M : ℕ} (hNM : N < M) :
    coeff N (bzQMZV w) =
      coeff N (qMZVPartial (w.map fun k => (k, Polynomial.X ^ (k - 1))) M) := by
  cases w with
  | nil => rfl
  | cons a u =>
    have ha : 2 ≤ a := h a (by simp)
    have hstart : coeff N (bzQMZV (a :: u)) = coeff N (T (a :: u) (N + 1)) := by
      simp only [bzQMZV, List.map_cons, qMZV, qMZVPartial, coeff_mk]
    rw [hstart]
    have hle : N + 1 ≤ M := hNM
    clear hNM
    induction M, hle using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have hm' : m ≤ m * (a - 1) := Nat.le_mul_of_pos_right _ (by omega)
      have hz : coeff N (W a m * T u m) = 0 := by
        dsimp only
        rw [← pow_mul, mul_assoc, coeff_X_pow_mul', ite_eq_right (by omega)]
      calc
        _ = coeff N (T (a :: u) m) := ih
        _ = coeff N (T (a :: u) (m + 1)) := by
          rw [partial_succ (m := m) (by omega) a u, map_add, hz, add_zero]

/-- **Quasi-shuffle relations for Bradley–Zhao qMZVs.** Identify an index $(k_1, \dots, k_r)$
with the word $z_{k_1} \cdots z_{k_r}$, and let $u$ and $v$ be admissible indices: finite,
possibly empty, sequences of positive integers whose first entry, if any, is at least $2$. Let
$u \ast_{BZ} v$ be the quasi-shuffle product of $u$ and $v$ with letter product
$z_a \diamond z_b = z_{a+b} + z_{a+b-1}$, a formal sum of indices. Then
$\zeta_q^{BZ}(u)\,\zeta_q^{BZ}(v) = \zeta_q^{BZ}(u \ast_{BZ} v)$, where the Bradley–Zhao qMZV
$\zeta_q^{BZ}$ is extended linearly to formal sums of indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 5 (`integers-2024-A6-prop-5`). -/
public theorem bzQMZV_mul_eq_sum_quasiShuffle (u v : List ℕ)
    (hu : ∀ k ∈ u, 1 ≤ k) (hu₁ : ∀ k₁ ∈ u.head?, 2 ≤ k₁)
    (hv : ∀ k ∈ v, 1 ≤ k) (hv₁ : ∀ k₁ ∈ v.head?, 2 ≤ k₁) :
    bzQMZV u * bzQMZV v =
      ((quasiShuffle (fun a b => [a + b, a + b - 1]) u v).map bzQMZV).sum := by
  ext N
  have hprod : coeff N (bzQMZV u * bzQMZV v) = coeff N (T u (N + 1) * T v (N + 1)) := by
    rw [coeff_mul, coeff_mul]
    refine sum_congr rfl ?_
    rintro ⟨i, j⟩ hij
    have hij' := mem_antidiagonal.mp hij
    rw [coeff_bzQMZV_eq_coeff_partial u hu₁ (by omega : i < N + 1),
      coeff_bzQMZV_eq_coeff_partial v hv₁ (by omega : j < N + 1)]
  rw [hprod, partial_mul N u v hu hv]
  simp only [map_list_sum, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact (coeff_bzQMZV_eq_coeff_partial w (head_ge_two_of_mem_shuffleBZ hu₁ hv₁ hw)
    (Nat.lt_succ_self N)).symm

end

end MetaMathlibExt

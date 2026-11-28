/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.GameTheory.EuclidGameCalkinWilf
public import MathlibExt.GameTheory.SmithRemoteness
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Golden-ratio bounds on optimal Euclid play

For a Calkin–Wilf vertex $m/n$ in row $k$ with $m>n$, if $(m,n)$ is a next-player win
and its Smith remoteness equals $k$, then $\varphi<m/n<\varphi+1$. The row index is
an upper bound for the length of play, since every move ascends at least one row.

The proof uses the golden cone of P-positions. At an N-position, optimal play can
move to a P-position. A move that skips more than one row would give remoteness
strictly less than $k$, so the first move must subtract just one copy of the smaller
entry. Applying the cone bound to that follower gives the upper inequality.

## References

* Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
  of the Game Euclid*, The Fibonacci Quarterly 62 (1) (2024), pp. 15–28,
  Section 2 (the P-position cone) and Proposition 6.3 (p. 24).
* A. J. Cole and A. J. T. Davie, *A game based on the Euclidean algorithm and a winning
  strategy for it*, The Mathematical Gazette 53 (386) (1969), pp. 354–357.
* T. Lengyel, *A Nim-type game and continued fractions*, The Fibonacci Quarterly
  41 (4) (2003), pp. 310–320 (the golden cone argument).
* S. Hofmann, G. Schuster, and J. Steuding, *Euclid, Calkin & Wilf—playing with rationals*,
  Elemente der Mathematik 63 (3) (2008), pp. 109–117 (moves along Calkin–Wilf branches).
* C. A. B. Smith, *Graphs and composite games*, Journal of Combinatorial Theory 1 (1)
  (1966), pp. 51–81 (remoteness).
-/

namespace MetaMathlibExt

open SpragueGrundy
open scoped goldenRatio

private theorem even_smithRemoteness_iff (G : ImpartialGame) (p : G.Pos) :
    Even (smithRemoteness G p) ↔ IsP G p := by
  induction p using (wfRel G).induction with
  | h p ih =>
    let V := (G.moves p).image (smithRemoteness G)
    have mem_even (q : G.Pos) (hq : q ∈ G.moves p) (hP : IsP G q) :
        smithRemoteness G q ∈ V.filter Even :=
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hq, (ih q hq).2 hP⟩
    rw [smithRemoteness_eq, isP_iff]
    change Even (if he : (V.filter Even).Nonempty then 1 + (V.filter Even).min' he
      else if hv : V.Nonempty then 1 + V.max' hv else 0) ↔ _
    split_ifs with he hv
    · have hEven := (Finset.mem_filter.mp (Finset.min'_mem _ he)).2
      obtain ⟨r, hr⟩ : ∃ r, r ∈ V.filter Even := he
      obtain ⟨hqMem, hrEven⟩ := Finset.mem_filter.mp hr
      obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hqMem
      refine iff_of_false ?_ (fun hall => hall q hq ((ih q hq).1 (hEq ▸ hrEven)))
      rw [add_comm 1, Nat.even_add_one]
      exact not_not_intro hEven
    · have hOdd : ¬Even (V.max' hv) := fun h =>
        he ⟨_, Finset.mem_filter.mpr ⟨Finset.max'_mem _ hv, h⟩⟩
      refine iff_of_true ?_ (fun q hq hP => he ⟨_, mem_even q hq hP⟩)
      rw [add_comm 1]
      exact Nat.even_add_one.2 hOdd
    · exact iff_of_true (by decide) fun q hq =>
        (hv ⟨_, Finset.mem_image_of_mem (smithRemoteness G) hq⟩).elim

private def goldenCone (a b : ℕ) : Prop :=
  (a : ℝ) < φ * b ∧ (b : ℝ) < φ * a

private theorem cone_iff_ratio {a b : ℕ} (hb : 0 < b) :
    goldenCone a b ↔ φ - 1 < (a : ℝ) / b ∧ (a : ℝ) / b < φ := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hφ : φ * (φ - 1) = 1 := by nlinarith only [Real.goldenRatio_sq]
  have hmul : φ * ((φ - 1) * (b : ℝ)) = b := by rw [← mul_assoc, hφ, one_mul]
  have hlt : (b : ℝ) < φ * a ↔ (φ - 1) * b < a := calc
    (b : ℝ) < φ * a ↔ φ * ((φ - 1) * b) < φ * a := by rw [hmul]
    _ ↔ _ := mul_lt_mul_iff_of_pos_left Real.goldenRatio_pos
  rw [goldenCone, lt_div_iff₀ hb', div_lt_iff₀ hb', hlt, and_comm]

-- Subtracting a positive integer from a ratio in this open interval of width one leaves it.
private theorem not_cone_sub {a b j : ℕ} (hb : 0 < b) (hj : 0 < j) (h : j * b < a)
    (hp : goldenCone a b) : ¬goldenCone (a - j * b) b := by
  intro hq
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have hj' : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hleft := ((cone_iff_ratio hb).1 hq).1
  rw [Nat.cast_sub h.le, Nat.cast_mul, sub_div, mul_div_cancel_right₀ _ hb'] at hleft
  linarith [((cone_iff_ratio hb).1 hp).2]

-- The floor is the shift into the cone. Irrationality excludes its lower endpoint.
private theorem exists_cone_sub {a b : ℕ} (hb : 0 < b) (h : φ * b ≤ (a : ℝ)) :
    ∃ j : ℕ, 0 < j ∧ j * b < a ∧ goldenCone (a - j * b) b := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hratio := (le_div_iff₀ hb').2 h
  let j := ⌊(a : ℝ) / b - (φ - 1)⌋₊
  have hfloor : 1 ≤ (a : ℝ) / b - (φ - 1) := by linarith
  have hj : 0 < j := (Nat.one_le_floor_iff _).2 hfloor
  have hlo : φ - 1 ≤ (a : ℝ) / b - (j : ℝ) := by
    have hle := Nat.floor_le (zero_le_one.trans hfloor)
    linarith
  have hhi : (a : ℝ) / b - (j : ℝ) < φ := by
    have hlt := Nat.lt_floor_add_one ((a : ℝ) / b - (φ - 1))
    linarith
  have hreal : (j : ℝ) * b < a := (lt_div_iff₀ hb').1 (by linarith [Real.one_lt_goldenRatio])
  have hlegal : j * b < a := by exact_mod_cast hreal
  refine ⟨j, hj, hlegal, (cone_iff_ratio hb).2 ?_⟩
  rw [Nat.cast_sub hlegal.le, Nat.cast_mul, sub_div, mul_div_cancel_right₀ _ hb'.ne']
  have hirr : Irrational (φ - 1) := by
    rw [← neg_sub, Real.one_sub_goldenConj]
    exact Real.goldenConj_irrational.neg
  have hne : φ - 1 ≠ (a : ℝ) / b - j := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using
      hirr.ne_rat ((a : ℚ) / b - j)
  exact ⟨lt_of_le_of_ne hlo hne, hhi⟩

private theorem isP_iff_cone (p : ℕ × ℕ) :
    0 < p.1 → 0 < p.2 → (IsP euclidGame p ↔ goldenCone p.1 p.2) := by
  induction p using (wfRel euclidGame).induction with
  | h p ih =>
    obtain ⟨a, b⟩ := p
    intro ha hb
    refine (isP_iff euclidGame (a, b)).trans ?_
    constructor
    · intro hall
      constructor
      · by_contra! h
        obtain ⟨j, hj, hlt, hcone⟩ := exists_cone_sub hb h
        have hq : (a - j * b, b) ∈ euclidGame.moves (a, b) :=
          mem_euclidGame_moves_iff.2 (Or.inl ⟨hb, j, hj, hlt, rfl⟩)
        exact hall _ hq ((ih _ hq (Nat.sub_pos_of_lt hlt) hb).2 hcone)
      · by_contra! h
        obtain ⟨j, hj, hlt, hcone⟩ := exists_cone_sub ha h
        have hq : (a, b - j * a) ∈ euclidGame.moves (a, b) :=
          mem_euclidGame_moves_iff.2 (Or.inr ⟨ha, j, hj, hlt, rfl⟩)
        exact hall _ hq ((ih _ hq ha (Nat.sub_pos_of_lt hlt)).2 ⟨hcone.2, hcone.1⟩)
    · intro hc q hq hp
      rcases mem_euclidGame_moves_iff.1 hq with ⟨_, j, hj, hlt, rfl⟩ | ⟨_, j, hj, hlt, rfl⟩
      · exact not_cone_sub hb hj hlt hc ((ih _ hq (Nat.sub_pos_of_lt hlt) hb).1 hp)
      · have hcone := (ih _ hq ha (Nat.sub_pos_of_lt hlt)).1 hp
        exact not_cone_sub ha hj hlt ⟨hc.2, hc.1⟩ ⟨hcone.2, hcone.1⟩

private theorem remoteness_le_row {k : ℕ} {p : ℕ × ℕ} (hp : p ∈ calkinWilfRow k) :
    smithRemoteness euclidGame p ≤ k := by
  induction k using Nat.strong_induction_on generalizing p with
  | ind k ih =>
    obtain ⟨a, b⟩ := p
    have hbound (q : ℕ × ℕ) (hq : q ∈ euclidGame.moves (a, b)) :
        smithRemoteness euclidGame q < k := by
      rcases mem_euclidGame_moves_iff.1 hq with ⟨_, j, hj, hlt, rfl⟩ | ⟨_, j, hj, hlt, rfl⟩
      · obtain ⟨hjk, hmem⟩ := (calkinWilfRow_sub_mul hp j).1 hlt
        exact (ih (k - j) (by omega) hmem).trans_lt (by omega)
      · obtain ⟨hjk, hmem⟩ := (calkinWilfRow_sub_mul hp j).2 hlt
        exact (ih (k - j) (by omega) hmem).trans_lt (by omega)
    refine (smithRemoteness_eq euclidGame (a, b)).le.trans ?_
    split_ifs with he hv
    · have hmem := (Finset.mem_filter.mp (Finset.min'_mem _ he)).1
      obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hmem
      rw [← hEq]
      have := hbound q hq
      omega
    · obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp (Finset.max'_mem _ hv)
      rw [← hEq]
      have := hbound q hq
      omega
    · exact Nat.zero_le _

/-- **Golden-ratio bounds for N-positions of maximal remoteness above 1.** Let $\varphi$ be the
golden ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf
tree, $n < m$, the position $(m, n)$ of Euclid is not a P-position, and its Smith remoteness in
Euclid equals $k$, then $\varphi < m/n < \varphi + 1$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.3. -/
public theorem golden_bounds_of_max_remoteness_N (k m n : ℕ) (hk : (m, n) ∈ calkinWilfRow k)
    (hmn : n < m) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    Real.goldenRatio < (m : ℝ) / n ∧ (m : ℝ) / n < Real.goldenRatio + 1 := by
  have hnP : ¬IsP euclidGame (m, n) := fun h => by
    have ht := (euclidPPosition_eq_true_iff m n).2 h
    rw [hN] at ht
    exact Bool.false_ne_true ht
  have hreply : ¬∀ q ∈ euclidGame.moves (m, n), ¬IsP euclidGame q :=
    mt (isP_iff euclidGame (m, n)).2 hnP
  push Not at hreply
  obtain ⟨q, hq, hP⟩ := hreply
  obtain ⟨hn, j, hj, hmul, rfl⟩ := (mem_euclidGame_moves_iff.1 hq).resolve_right (by
    rintro ⟨_, j, hj, hlt, _⟩
    exact (not_lt_of_ge (hmn.le.trans (Nat.le_mul_of_pos_left m hj))) hlt)
  have ⟨hjle, hrow⟩ := (calkinWilfRow_sub_mul hk j).1 hmul
  have heven := (even_smithRemoteness_iff _ _).2 hP
  have hv : smithRemoteness euclidGame (m - j * n, n) ∈
      ((euclidGame.moves (m, n)).image (smithRemoteness euclidGame)).filter Even :=
    Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hq, heven⟩
  have hle : k ≤ 1 + smithRemoteness euclidGame (m - j * n, n) := by
    rw [← hr, smithRemoteness_eq euclidGame (m, n), dite_eq_left ⟨_, hv⟩]
    exact Nat.add_le_add_left (Finset.min'_le _ _ hv) 1
  have h₁ : j = 1 := by
    have := remoteness_le_row hrow
    omega
  have hqcone := ((isP_iff_cone (m - j * n, n) (Nat.sub_pos_of_lt hmul) hn).1 hP).1
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmn' : (n : ℝ) < m := by exact_mod_cast hmn
  have hnocone : ¬goldenCone m n := mt (isP_iff_cone (m, n) (hn.trans hmn) hn).2 hnP
  have hlow : φ * (n : ℝ) < m := by
    refine lt_of_le_of_ne (le_of_not_gt fun h => hnocone ⟨h, ?_⟩) ?_
    · have hφm := mul_lt_mul_of_pos_right Real.one_lt_goldenRatio
        (show (0 : ℝ) < m from hn'.trans hmn')
      linarith
    · exact (Real.goldenRatio_irrational.mul_natCast hn.ne').ne_nat m
  refine ⟨(lt_div_iff₀ hn').2 hlow, (div_lt_iff₀ hn').2 ?_⟩
  rw [Nat.cast_sub hmul.le, h₁, one_mul] at hqcone
  linarith only [hqcone]

end MetaMathlibExt

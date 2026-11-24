/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Closure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Non-negative lines in weighted rank-three matroids

In a simple rank-three matroid of non-negative total weight, the non-negative points
are connected by non-negative lines.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted

/-- **Simple matroid.** A matroid $M$ on elements of $\{0, \dots, n-1\}$ is simple when the set
$\{e, f\}$ is independent in $M$ for all $e, f \in \{0, \dots, n-1\}$, so that every set of at most
two of these elements is independent (no loops, no parallel pairs). -/
def IsSimpleMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop := ∀ e f, M.Indep {e, f}

/-- **Line of a matroid.** A set $L$ of points is a line of a matroid $M$ on elements of
$\{0, \dots, n-1\}$ when $L$ is a flat of $M$ of rank $2$. -/
def IsLine {n : ℕ} (M : Matroid (Fin n)) (L : Set (Fin n)) : Prop := M.IsFlat L ∧ M.eRk L = 2

open Classical in
/-- **Weight of a set of points.** Given real weights $a_0, \dots, a_{n-1}$ on the points
$0, \dots, n-1$, the weight of a set $S$ of points is $\sum_{i \in S} a_i$. -/
noncomputable def weight {n : ℕ} (a : Fin n → ℝ) (S : Set (Fin n)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ∈ S), a i

open Classical in
/-- **Graph of non-negative lines.** Let $M$ be a matroid on elements of $\{0, \dots, n-1\}$ and
let $a_0, \dots, a_{n-1}$ be real weights, the weight of a set of points being the sum of the
weights of its points. The graph of non-negative lines has as vertices the points $i$ with
$a_i \ge 0$, and two distinct vertices are adjacent when some line of $M$ (a flat of rank $2$)
contains both and has non-negative weight. -/
def nonnegGraph {n : ℕ} (M : Matroid (Fin n)) (a : Fin n → ℝ) :
    SimpleGraph {i : Fin n // 0 ≤ a i} :=
  SimpleGraph.fromRel fun i j =>
    ∃ L, IsLine M L ∧ 0 ≤ weight a L ∧ (i : Fin n) ∈ L ∧ (j : Fin n) ∈ L

/-- **Connectivity question for weighted rank-3 matroids.** This is the statement that for every
$n$, every simple matroid $M$ of rank $3$ on the ground set $\{0, \dots, n-1\}$ (every set of at
most two points is independent) and all real weights $a_0, \dots, a_{n-1}$ with
$a_0 + \dots + a_{n-1} \ge 0$, the graph on the points $i$ with $a_i \ge 0$, in which two distinct
points are adjacent when some line of $M$ (a flat of rank $2$) contains both and has non-negative
weight, the weight of a set being the sum of the weights of its points, is connected. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)) (a : Fin n → ℝ), IsSimpleMatroid M → M.eRank = 3 →
    M.E = Set.univ →
    0 ≤ ∑ i, a i → (nonnegGraph M a).Connected

open scoped BigOperators

private abbrev Line {n : ℕ} (M : Matroid (Fin n)) := {L : Set (Fin n) // IsLine M L}

private theorem existsUnique_line {n : ℕ} {M : Matroid (Fin n)} (hs : IsSimpleMatroid M)
    {i j : Fin n} (hij : i ≠ j) : ∃! L : Line M, i ∈ L.val ∧ j ∈ L.val := by
  have hInd := hs i j
  have hRank : M.eRk {i, j} = 2 := hInd.eRk_eq_encard.trans (Set.encard_pair hij)
  have hsub := M.subset_closure _ hInd.subset_ground
  refine ⟨⟨M.closure {i, j}, M.isFlat_closure _, (M.eRk_closure_eq _).trans hRank⟩,
    ⟨hsub (by simp), hsub (by simp)⟩, ?_⟩
  intro L ⟨hi, hj⟩
  have hpair : {i, j} ⊆ L.val := Set.insert_subset hi (Set.singleton_subset_iff.mpr hj)
  have hle : M.eRk L.val ≤ M.eRk {i, j} := by rw [L.property.2, hRank]
  have hb := hInd.isBasis_of_eRk_ge (Set.toFinite _) hpair hle L.property.1.subset_ground
  exact Subtype.ext (hb.closure_eq_closure.trans L.property.1.closure).symm

private noncomputable instance lineFintype {n : ℕ} (M : Matroid (Fin n)) :
    Fintype (Line M) := Fintype.ofFinite _

/-- Every pair from disjoint supports contributes on its unique line. -/
private theorem sum_line_weight_mul {n : ℕ} {M : Matroid (Fin n)} (hs : IsSimpleMatroid M)
    (f g : Fin n → ℝ) (hfg : ∀ i, f i * g i = 0) :
    ∑ L : Line M, weight f L.val * weight g L.val = (∑ i, f i) * ∑ j, g j := by
  classical
  simp only [weight, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, ← ite_and]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hij : i = j
  · subst j
    simp [hfg]
  · obtain ⟨L, hL, huniq⟩ := existsUnique_line hs hij
    have hmem (K : Line M) : i ∈ K.val ∧ j ∈ K.val ↔ K = L :=
      ⟨fun h ↦ huniq K h, fun h ↦ h ▸ hL⟩
    simp [hmem]

private theorem reachable_of_line {n : ℕ} {M : Matroid (Fin n)} {a : Fin n → ℝ}
    {x y : {i : Fin n // 0 ≤ a i}} {L : Line M}
    (hx : x.val ∈ L.val) (hy : y.val ∈ L.val) (hL : 0 ≤ weight a L.val) :
    (nonnegGraph M a).Reachable x y := by
  by_cases h : x = y
  · subst y
    exact SimpleGraph.Reachable.refl _
  apply SimpleGraph.Adj.reachable
  exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨L.val, L.property, hL, hx, hy⟩⟩

/-- If a component omits a vertex, it contains a point of strictly positive weight. -/
private theorem exists_pos_of_not_reachable {n : ℕ} {M : Matroid (Fin n)}
    {a : Fin n → ℝ} (hs : IsSimpleMatroid M) (ht : 0 ≤ ∑ i, a i)
    {x y : {i : Fin n // 0 ≤ a i}} (hxy : ¬ (nonnegGraph M a).Reachable x y) :
    ∃ z, (nonnegGraph M a).Reachable x z ∧ 0 < a z.val := by
  classical
  by_contra! h
  have hx0 : a x.val = 0 := le_antisymm (h x (SimpleGraph.Reachable.refl _)) x.property
  let δ : Fin n → ℝ := fun i ↦ if i = x.val then 1 else 0
  have hδ (i : Fin n) : δ i * a i = 0 := by
    simp only [δ, ite_mul, one_mul, zero_mul]
    split_ifs with hi
    · simpa [hi] using hx0
    · rfl
  have hδL (L : Line M) : weight δ L.val = if x.val ∈ L.val then 1 else 0 := by
    simp [weight, δ, Finset.sum_ite_eq']
  have htotal : (∑ L : Line M, weight δ L.val * weight a L.val) = ∑ i, a i := by
    rw [sum_line_weight_mul hs δ a hδ]
    simp [δ]
  have hnonpos (L : Line M) : weight δ L.val * weight a L.val ≤ 0 := by
    rw [hδL]
    split_ifs with hxL
    · rw [one_mul]
      by_contra! hpos
      apply hpos.not_ge
      exact Finset.sum_nonpos fun z hz ↦
        by
          by_contra! hzpos
          exact (h ⟨z, hzpos.le⟩
            (reachable_of_line hxL (Finset.mem_filter.mp hz).2 hpos.le)).not_gt hzpos
    · simp
  have hne : x.val ≠ y.val := fun he ↦ hxy (Subtype.ext he ▸ SimpleGraph.Reachable.refl _)
  obtain ⟨L, ⟨hxL, hyL⟩, _⟩ := existsUnique_line hs hne
  have hneg : weight δ L.val * weight a L.val < 0 := by
    rw [hδL, ite_eq_left hxL, one_mul]
    exact lt_of_not_ge fun hw ↦ hxy (reachable_of_line hxL hyL hw)
  have hsum := Finset.sum_lt_sum (g := fun _ ↦ (0 : ℝ))
    (fun K _ ↦ hnonpos K) ⟨L, Finset.mem_univ _, hneg⟩
  simp [htotal, not_lt.mpr ht] at hsum

private theorem weight_nonneg {n : ℕ} {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i) (S : Set (Fin n)) :
    0 ≤ weight f S := Finset.sum_nonneg fun i _ ↦ hf i

/-- Two positive parts share a line whose negative mass is at most their combined mass. -/
private theorem exists_line_of_parts {n : ℕ} {M : Matroid (Fin n)} (hs : IsSimpleMatroid M)
    (p q d : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hd : ∀ i, 0 ≤ d i)
    (hpq : ∀ i, p i * q i = 0) (hpd : ∀ i, p i * d i = 0) (hqd : ∀ i, q i * d i = 0)
    (hP : 0 < ∑ i, p i) (hQ : 0 < ∑ i, q i)
    (ht : (∑ i, d i) ≤ (∑ i, p i) + ∑ i, q i) :
    ∃ L : Line M, 0 < weight p L.val ∧ 0 < weight q L.val ∧
      weight d L.val ≤ weight p L.val + weight q L.val := by
  classical
  let P := ∑ i, p i
  let Q := ∑ i, q i
  let D := ∑ i, d i
  let pL (L : Line M) := weight p L.val
  let qL (L : Line M) := weight q L.val
  let dL (L : Line M) := weight d L.val
  have hpL (L : Line M) : 0 ≤ pL L := weight_nonneg hp L.val
  have hqL (L : Line M) : 0 ≤ qL L := weight_nonneg hq L.val
  have hdL (L : Line M) : 0 ≤ dL L := weight_nonneg hd L.val
  have hpq' : ∑ L, pL L * qL L = P * Q := sum_line_weight_mul hs p q hpq
  have hpd' : ∑ L, pL L * dL L = P * D := sum_line_weight_mul hs p d hpd
  have hqd' : ∑ L, qL L * dL L = Q * D := sum_line_weight_mul hs q d hqd
  change 0 < P at hP
  change 0 < Q at hQ
  change D ≤ P + Q at ht
  by_contra! h
  change ∀ L, 0 < pL L → 0 < qL L → pL L + qL L < dL L at h
  -- On a line meeting both parts, compare the negative mass with their combined mass.
  have hstrict (L : Line M) (hlp : 0 < pL L) (hlq : 0 < qL L) :
      (P + Q)^2 * (pL L * qL L) < (Q^2 * pL L + P^2 * qL L) * dL L := by
    have hsq := sq_nonneg (Q * pL L - P * qL L)
    calc
      _ ≤ (Q^2 * pL L + P^2 * qL L) * (pL L + qL L) := by nlinarith only [hsq]
      _ < _ := mul_lt_mul_of_pos_left (h L hlp hlq) (by positivity)
  have hnonneg (L : Line M) :
      (P + Q)^2 * (pL L * qL L) ≤ (Q^2 * pL L + P^2 * qL L) * dL L := by
    rcases (hpL L).eq_or_lt with hzero | hlp
    · rw [← hzero, zero_mul, mul_zero, mul_zero, zero_add]
      exact mul_nonneg (mul_nonneg (sq_nonneg P) (hqL L)) (hdL L)
    rcases (hqL L).eq_or_lt with hzero | hlq
    · simp only [← hzero, mul_zero, add_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg Q) (hpL L)) (hdL L)
    exact (hstrict L hlp hlq).le
  have hsum_pos : 0 < ∑ L, pL L * qL L := by rw [hpq']; exact mul_pos hP hQ
  obtain ⟨L, _, hL⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun K _ ↦ mul_nonneg (hpL K) (hqL K)).mp hsum_pos
  have hsum := Finset.sum_lt_sum (fun K _ ↦ hnonneg K)
    ⟨L, Finset.mem_univ _, hstrict L (pos_of_mul_pos_left hL (hqL L))
      (pos_of_mul_pos_right hL (hpL L))⟩
  simp only [add_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
    mul_assoc, hpq', hpd', hqd'] at hsum
  have hbound := mul_le_mul_of_nonneg_left ht (show 0 ≤ P * Q * (P + Q) by positivity)
  apply (not_lt_of_ge hbound)
  convert hsum using 1 <;> ring

/--
**Non-negative points of a weighted rank-3 matroid are connected by non-negative lines.** Let $n$
be a natural number, let $M$ be a simple matroid of rank $3$ on the ground set $\{0, \dots, n-1\}$
(every set of at most two points is independent) and let $a_0, \dots, a_{n-1}$ be real weights
with $a_0 + \dots + a_{n-1} \ge 0$. Then the graph on the points $i$ with $a_i \ge 0$, in which two
distinct points are adjacent when some line of $M$ (a flat of rank $2$) contains both and has
non-negative weight, the weight of a set being the sum of the weights of its points, is
connected.

Resolved true: for a matroid of rank $r$, a generic weight and a threshold $t \le \min\{0, w\}$,
where $w$ is the total weight, the proper flats of weight greater than $t$ form an
$(r - 3)$-connected poset (Adiprasito–Björner, Theorem 2.1, settling the Mikhalkin–Ziegler
conjecture); for $r = 3$, a small generic perturbation with $t$ slightly below $0$ gives the
connectivity of the non-negative points through non-negative lines. Shellability in the omitted
rank-$r$ part is open (their Open Problem 3.2).

Source: K. A. Adiprasito, A. Björner, Filtered geometric lattices and
Lefschetz section theorems over the tropical semiring, arXiv:1401.7301,
https://arxiv.org/abs/1401.7301. Moved from
`OpenConjectures/Combinatorics/WeightedMatroidNonnegativeLinesConnected`.
-/
theorem conjecture_holds : conjecture := by
  classical
  intro n M a hs hr _ ht
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
    obtain ⟨B, hB⟩ := M.exists_isBase
    have hcard := hB.encard_eq_eRank.trans hr
    obtain ⟨i, _⟩ := Set.one_le_encard_iff_nonempty.mp (show 1 ≤ B.encard by rw [hcard]; decide)
    exact ⟨i, Finset.mem_univ _⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ?_⟩
  · intro x y
    by_contra hxy
    let G := nonnegGraph M a
    let C (i : Fin n) := ∃ hi : 0 ≤ a i, G.Reachable x ⟨i, hi⟩
    let p (i : Fin n) := if C i then max (a i) 0 else 0
    let q (i : Fin n) := if C i then 0 else max (a i) 0
    let d (i : Fin n) := max (-a i) 0
    have hp (i : Fin n) : 0 ≤ p i := by unfold p; split_ifs <;> positivity
    have hq (i : Fin n) : 0 ≤ q i := by unfold q; split_ifs <;> positivity
    have hd (i : Fin n) : 0 ≤ d i := le_max_right _ _
    have hpq i : p i * q i = 0 := by by_cases h : C i <;> simp [p, q, h]
    have hmax (i : Fin n) : max (a i) 0 * d i = 0 := by
      rcases le_total (a i) 0 with hi | hi
      · simp [max_eq_right hi]
      · simp [d, max_eq_right (neg_nonpos.mpr hi)]
    have hpd i : p i * d i = 0 := by simp [p, ite_mul, hmax]
    have hqd i : q i * d i = 0 := by simp [q, ite_mul, hmax]
    have ha (i : Fin n) : a i = p i + q i - d i := by
      have hs' : max (a i) 0 - max (-a i) 0 = a i := by
        rcases le_total (a i) 0 with hi | hi
        · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
        · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      unfold p q d
      split_ifs <;> simp only [add_zero, zero_add] <;> exact hs'.symm
    obtain ⟨u, hxu, hu⟩ := exists_pos_of_not_reachable hs ht hxy
    obtain ⟨v, hyv, hv⟩ := exists_pos_of_not_reachable hs ht (fun hyx ↦ hxy hyx.symm)
    have hCu : C u.val := ⟨u.property, hxu⟩
    have hCv : ¬ C v.val := by
      rintro ⟨_, hxv⟩
      exact hxy (hxv.trans hyv.symm)
    have hP : 0 < ∑ i, p i :=
      Finset.sum_pos' (fun i _ ↦ hp i) ⟨u.val, Finset.mem_univ _, by simpa [p, hCu]⟩
    have hQ : 0 < ∑ i, q i :=
      Finset.sum_pos' (fun i _ ↦ hq i) ⟨v.val, Finset.mem_univ _, by simpa [q, hCv]⟩
    have htotal : (∑ i, d i) ≤ (∑ i, p i) + ∑ i, q i := by
      simp only [ha, Finset.sum_sub_distrib, Finset.sum_add_distrib] at ht
      exact sub_nonneg.mp ht
    obtain ⟨L, hpL, hqL, hL⟩ := exists_line_of_parts hs p q d hp hq hd hpq hpd hqd hP hQ htotal
    have hw : 0 ≤ weight a L.val := by
      unfold weight at *
      simp only [ha, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      exact sub_nonneg.mpr hL
    obtain ⟨i, hi, hip⟩ := (Finset.sum_pos_iff_of_nonneg fun i _ ↦ hp i).mp hpL
    obtain ⟨j, hj, hjq⟩ := (Finset.sum_pos_iff_of_nonneg fun j _ ↦ hq j).mp hqL
    have hCi : C i := by by_contra h; simp [p, h] at hip
    have hCj : ¬ C j := by intro h; simp [q, h] at hjq
    have hjpos : 0 < a j := by simpa [q, hCj] using hjq
    obtain ⟨_, hxi⟩ := hCi
    exact hCj ⟨hjpos.le, hxi.trans (reachable_of_line
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hw)⟩
  · by_contra! h
    have hneg : ∀ i, a i < 0 := fun i ↦ lt_of_not_ge fun hi ↦ h.false ⟨i, hi⟩
    exact (Finset.sum_neg (fun i _ ↦ hneg i) hn).not_ge ht

end MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted

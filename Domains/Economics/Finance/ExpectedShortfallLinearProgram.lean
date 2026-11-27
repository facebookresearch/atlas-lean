/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.ExpectedShortfall
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Linarith

/-!
# Finite-scenario expected shortfall as a linear program

With nonnegative weights summing to one and `0 ≤ α < 1`, each decision's scalar threshold
problem has a minimum. Neither the threshold nor the affine losses have a sign constraint.
Across decisions, equality of the sets of lower bounds expresses equality of the infima even
for unbounded-below problems. In contrast to the threshold minimum, an outer optimum need not exist.

## Reference

R. T. Rockafellar and S. Uryasev, *Optimization of conditional value-at-risk*, Journal of Risk
2(3) (2000), 21–41. Theorems 1–2, (5) and (10), relate the threshold and joint minimizations
under the paper's distribution assumptions. Equation (9) uses equal sample weights; the linear
epigraph formulation follows (17). The results here for arbitrary normalized finite weights,
confidence zero, unbounded outer values and slack at zero weight are deductions.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ExpectedShortfall

open Set

variable {Ω : Type*} [Fintype Ω]

/-- The linear objective of the finite-scenario lift at threshold `z` and excess vector `u`:
`z + (∑ s, p s * u s) / (1 - α)`. Its risk interpretation uses nonnegative weights summing
to one and `0 ≤ α < 1`; the expression itself is defined for all real coefficients. -/
noncomputable def liftCost (p : Ω → ℝ) (α z : ℝ) (u : Ω → ℝ) : ℝ :=
  z + (∑ s, p s * u s) / (1 - α)

/-- The scalar Rockafellar–Uryasev objective for finite signed losses `Y` at a real threshold
`z`: evaluate the lift at `u s = max (Y s - z) 0`. With nonnegative weights summing to one and
`0 ≤ α < 1`, its minimum is `expectedShortfall p α Y`. -/
noncomputable def thresholdCost (p : Ω → ℝ) (α : ℝ) (Y : Ω → ℝ) (z : ℝ) : ℝ :=
  liftCost p α z (fun s => max (Y s - z) 0)

private theorem mean_le_thresholdCost {p : Ω → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp1 : ∑ s, p s = 1) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) (Y : Ω → ℝ) (z : ℝ) :
    ∑ s, p s * Y s ≤ thresholdCost p α Y z := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    mul_le_mul_of_nonneg_left (le_max_left (Y s - z) 0) (hp s)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul] at h
  have hnonneg : 0 ≤ ∑ s, p s * max (Y s - z) 0 :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (le_max_right _ _)
  have hscale : (∑ s, p s * max (Y s - z) 0) ≤ (∑ s, p s * max (Y s - z) 0) / (1 - α) :=
    (le_div_iff₀ (sub_pos.mpr hα')).2 (mul_le_of_le_one_right hnonneg (by linarith))
  unfold thresholdCost liftCost
  linarith

/-- For signed losses on a finite scenario space with nonnegative weights summing to one and
`0 ≤ α < 1`, expected shortfall is the **least attained value** of the scalar threshold cost.
At zero any threshold below all losses realizes the mean; at positive confidence the lower
quantile realizes the minimum. No outer decision or integrability hypothesis is needed. -/
theorem isLeast_range_thresholdCost {p : Ω → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) (Y : Ω → ℝ) :
    IsLeast (range (thresholdCost p α Y)) (expectedShortfall p α Y) := by
  have lb := mean_le_thresholdCost hp hp1 hα hα' Y
  have hlow : ∀ z, expectedShortfall p α Y ≤ thresholdCost p α Y z :=
    ciInf_le (f := thresholdCost p α Y) ⟨_, forall_mem_range.mpr lb⟩
  refine ⟨?_, forall_mem_range.mpr hlow⟩
  rcases hα.eq_or_lt with rfl | hpos
  · obtain ⟨z, hz⟩ := (finite_range Y).bddBelow
    have hmean : thresholdCost p 0 Y z = ∑ s, p s * Y s := by
      have hpos : ∀ s, 0 ≤ Y s - z := fun s => sub_nonneg.mpr (hz (mem_range_self s))
      simp only [thresholdCost, liftCost, max_eq_left (hpos _), sub_zero, div_one, mul_sub,
        Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
      abel
    refine ⟨z, le_antisymm ?_ (hlow z)⟩
    rw [hmean]
    exact le_ciInf lb
  · exact ⟨_, (expectedShortfall_eq_valueAtRisk_add hp hp1 hpos hα' Y).symm⟩

/-- The feasible triples `(x,z,u)` over a decision set `S` and signed scenario losses `L x`:
`x ∈ S`, `u s ≥ 0` and `u s ≥ L x s - z` for **every** scenario, regardless of weight. The
threshold and decisions have no additional sign constraints. -/
def feasibleLift {E : Type*} (S : Set E) (L : E → Ω → ℝ) : Set (E × ℝ × (Ω → ℝ)) :=
  {q | q.1 ∈ S ∧ ∀ s, 0 ≤ q.2.2 s ∧ L q.1 s - q.2.1 ≤ q.2.2 s}

private theorem liftCost_eq_iff {p Y u : Ω → ℝ} {α z : ℝ} (hp : ∀ s, 0 ≤ p s) (hα' : α < 1)
    (hu : ∀ s, max (Y s - z) 0 ≤ u s) :
    liftCost p α z u = thresholdCost p α Y z ↔ ∀ s, 0 < p s → u s = max (Y s - z) 0 := by
  have hterms := Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun s _ => mul_le_mul_of_nonneg_left (hu s) (hp s))
  constructor
  · intro heq s hs
    have hdiv : (∑ i, p i * max (Y i - z) 0) / (1 - α) = (∑ i, p i * u i) / (1 - α) :=
      add_left_cancel heq.symm
    have hsum := (div_left_inj₀ (sub_ne_zero.mpr hα'.ne')).mp hdiv
    exact (mul_left_cancel₀ hs.ne' (hterms.mp hsum s (Finset.mem_univ s))).symm
  · intro h
    apply congrArg (fun t : ℝ => z + t / (1 - α))
    apply Finset.sum_congr rfl
    intro s _
    rcases (hp s).eq_or_lt with hs | hs
    · simp [← hs]
    · rw [h s hs]

/-- **Finite-scenario CVaR minimization as a linear program.** On the nonempty polyhedron
`S = {x | A x ≤ b}`, take signed affine losses `L x = C x + d`, nonnegative finite scenario
weights `p` summing to one, and `0 ≤ α < 1`. At each decision, the scalar threshold cost attains
its minimum at some real threshold and that value is expected shortfall. The feasible triples
`(x,z,u)` retain `x ∈ S` and satisfy `u ≥ 0`, `u ≥ L x - z` coordinatewise. Their linear costs
`z + (∑ s, p s * u s) / (1 - α)` and the attainable expected shortfalls have the same real lower
bounds, hence the same infimum including `−∞`. A decision
is a feasible global minimizer exactly when it has an optimal lift. More precisely, a feasible
triple is optimal exactly when its decision minimizes risk, its threshold attains the scalar
minimum, and its positive-weight excesses equal the positive parts. Thus zero-weight excesses
can be chosen independently anywhere above their feasibility bounds. No boundedness or outer
attainment assumption is made. -/
theorem expectedShortfall_linearProgram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hS : ∃ x, A.mulVec x ≤ b) (C : Matrix Ω (Fin n) ℝ) (d : Ω → ℝ)
    {p : Ω → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) :
    let S := {x | A.mulVec x ≤ b}
    let L := fun x => C.mulVec x + d
    let P := feasibleLift S L
    let risk := fun x => expectedShortfall p α (L x)
    let cost := fun q : (Fin n → ℝ) × ℝ × (Ω → ℝ) => liftCost p α q.2.1 q.2.2
    (∀ x, IsLeast (range (thresholdCost p α (L x))) (risk x)) ∧
      P.Nonempty ∧ lowerBounds (risk '' S) = lowerBounds (cost '' P) ∧
      (∀ x, (x ∈ S ∧ IsMinOn risk S x) ↔ ∃ z u, (x, z, u) ∈ P ∧ IsMinOn cost P (x, z, u)) ∧
      (∀ q ∈ P, IsMinOn cost P q ↔ IsMinOn risk S q.1 ∧ thresholdCost p α (L q.1) q.2.1 = risk q.1 ∧
        ∀ s, 0 < p s → q.2.2 s = max (L q.1 s - q.2.1) 0) := by
  intro S L P risk cost
  have least x := isLeast_range_thresholdCost hp hp1 hα hα' (L x)
  have realize x (hx : x ∈ S) : ∃ z u, (x, z, u) ∈ P ∧ cost (x, z, u) = risk x := by
    obtain ⟨z, hz⟩ := (least x).1
    exact ⟨z, fun s => max (L x s - z) 0, ⟨hx, fun s => ⟨le_max_right _ _, le_max_left _ _⟩⟩, hz⟩
  have sandwich q (hq : q ∈ P) : risk q.1 ≤ thresholdCost p α (L q.1) q.2.1 ∧
      thresholdCost p α (L q.1) q.2.1 ≤ cost q := by
    refine ⟨(least q.1).2 (mem_range_self q.2.1), add_le_add_right ?_ _⟩
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hα'.le)
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (max_le (hq.2 s).2 (hq.2 s).1) (hp s)
  have bound q (hq : q ∈ P) := (sandwich q hq).1.trans (sandwich q hq).2
  have optimal q (hq : q ∈ P) : IsMinOn cost P q ↔ IsMinOn risk S q.1 ∧ cost q = risk q.1 := by
    constructor
    · intro h
      have comp y (hy : y ∈ S) : cost q ≤ risk y := by
        obtain ⟨z, u, hmem, heq⟩ := realize y hy
        exact (isMinOn_iff.mp h (y, z, u) hmem).trans_eq heq
      exact ⟨isMinOn_iff.mpr (fun y hy => (bound q hq).trans (comp y hy)),
        le_antisymm (comp q.1 hq.1) (bound q hq)⟩
    · rintro ⟨h, heq⟩
      exact isMinOn_iff.mpr fun r hr =>
        heq.le.trans ((isMinOn_iff.mp h r.1 hr.1).trans (bound r hr))
  obtain ⟨x₀, hx₀⟩ := hS
  obtain ⟨z₀, u₀, hmem, -⟩ := realize x₀ hx₀
  refine ⟨least, ⟨(x₀, z₀, u₀), hmem⟩, ?_, ?_, ?_⟩
  · ext a
    constructor
    · rintro h _ ⟨q, hq, rfl⟩
      exact (h ⟨q.1, hq.1, rfl⟩).trans (bound q hq)
    · rintro h _ ⟨x, hx, rfl⟩
      obtain ⟨z, u, hq, heq⟩ := realize x hx
      exact h ⟨(x, z, u), hq, heq⟩
  · intro x
    constructor
    · rintro ⟨hx, h⟩
      obtain ⟨z, u, hq, heq⟩ := realize x hx
      exact ⟨z, u, hq, (optimal _ hq).2 ⟨h, heq⟩⟩
    · rintro ⟨z, u, hq, h⟩
      exact ⟨hq.1, ((optimal _ hq).1 h).1⟩
  · intro q hq
    rw [optimal q hq, and_congr_right_iff]
    intro _
    have htight := liftCost_eq_iff hp hα' (fun s => max_le (hq.2 s).2 (hq.2 s).1)
    constructor
    · intro heq
      have hs := sandwich q hq
      have ht := le_antisymm (hs.2.trans heq.le) hs.1
      exact ⟨ht, htight.mp (heq.trans ht.symm)⟩
    · rintro ⟨hz, hu⟩
      exact (htight.mpr hu).trans hz

end MathlibExt.Probability.Finance.ExpectedShortfall

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Uniqueness of measures on `ℝᵈ`

Two finite measures on `Fin d → ℝ` are equal as soon as they agree on a
generating π-system. This file proves the two forms of that principle that
the book needs for measures on `ℝᵈ`: agreement on all left-closed quadrants
`Iic a`, and agreement on all half-open rectangles `(a, b]`. It also records
a moment criterion: finite measures supported in a fixed compact set are
determined by all mixed moments.

## Source

This formalizes the uniqueness half of the target "Theorem (characterizing
probability measures on R^d)" (Lecture 3, section "Characterizing probability
measures on R^d") of `v1/Atlas/TheoryOfProbability/targets.yaml`: "Given `F`,
there is a unique measure whose values on finite rectangles are determined by
taking differences of `F` applied to vertices, provided that `F` is
non-decreasing, right continuous, and assigns a non-negative value to each
rectangle." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean`
(`exists_unique_borelMeasure_of_rectangleFunction`).

Only the uniqueness half is ported here: the v1 existence half
(`caratheodory_extension_rectangleFunction`) is left unproved in v1 and is
not claimed here. The uniqueness half is proved in v1 in full (the `huniq`
argument of `exists_unique_borelMeasure_of_rectangleFunction`, plus
`ProbabilityMeasure.ext_of_Iic`).

## Relation to Mathlib

Mathlib's `MeasureTheory.Measure.ext_of_Iic` determines a finite measure on a
*linearly ordered* space by its values on `Iic a`. The space `Fin d → ℝ`
with the product order is not linearly ordered for `d ≥ 2`, so that lemma
does not apply here; `MeasureTheory.Measure.ext_of_Iic_pi` is the
multivariate form. Mathlib has no rectangle-value uniqueness statement:
the inclusion-exclusion sum `rectangleValue` over the vertices of a
rectangle is defined here.

The statements are generalized from v1 in two respects: the quadrant
theorem is stated for finite measures, not just probability measures, and
the rectangle argument is factored through a private lemma that takes
finiteness on the spanning boxes as a hypothesis. The finite-measure
rectangle theorem and the `F`-version discharge that hypothesis in
different ways. The `F`-version itself needs no finiteness hypothesis
(as in v1): it covers Lebesgue measure, given by `F (x) = x` in
dimension `1`, which is not finite.

## Main results

* `MeasureTheory.Measure.ext_of_Iic_pi`: two finite measures on
  `Fin d → ℝ` agreeing on every quadrant `Iic a` are equal.
* `MeasureTheory.Measure.eq_of_forall_Ioc_eq`: two finite measures on
  `Fin d → ℝ` agreeing on every half-open rectangle `(a, b]` are equal.
* `MeasureTheory.Measure.eq_of_forall_rectangleValue_eq`: if two
  measures on `Fin d → ℝ` both assign every rectangle `(a, b]` the mass
  `ENNReal.ofReal (rectangleValue F a b)`, then they are equal.
* `MeasureTheory.Measure.eq_of_forall_integral_monomial_eq`: two finite
  measures with no mass outside a compact `E ⊆ Fin d → ℝ` and with equal
  mixed moments of every order are equal.
* `MeasureTheory.rectangleValue`: the inclusion-exclusion sum of `F`
  over the vertices of a rectangle.

The moment criterion is a local derivation from Stone-Weierstrass
approximation and Mathlib's bounded-continuous extensionality for finite
measures; it is not part of the v1 rectangle port described above.
-/

@[expose] public section

open MeasureTheory Set MeasurableSpace
open scoped ENNReal

namespace MeasureTheory

/-- **Vertex of a rectangle.** Let $d$ be a natural number, let $a, b \in \mathbb{R}^d$, and let
$S$ be a finite set of coordinate indices in $\{0, \dots, d-1\}$. The vertex of the rectangle
$(a, b]$ selected by $S$ is the point $v \in \mathbb{R}^d$ with $v_i = a_i$ for $i \in S$ and
$v_i = b_i$ for $i \notin S$.

As $S$ ranges over all $2^d$ subsets of indices, these points are the vertices used in
inclusion-exclusion sums over the rectangle. -/
def rectangleVertex {d : ℕ} (a b : Fin d → ℝ) (S : Finset (Fin d)) : Fin d → ℝ :=
  fun i => if i ∈ S then a i else b i

/-- **Rectangle value of a function.** For $F : \mathbb{R}^d \to \mathbb{R}$ and arbitrary
$a, b \in \mathbb{R}^d$, the rectangle value of $F$ at $a, b$ is
$$\Delta_{a,b} F = \sum_{S \subseteq \{1, \dots, d\}} (-1)^{|S|} F(v_S),$$
where $v_S \in \mathbb{R}^d$ is the vertex with $(v_S)_i = a_i$ for $i \in S$ and $(v_S)_i = b_i$
for $i \notin S$.

Write $(a, b] = \prod_{i=1}^d (a_i, b_i]$. When $a_i \le b_i$ for every $i$ and $F$ is a
distribution function on $\mathbb{R}^d$, this signed inclusion–exclusion sum equals the mass
$\mu((a, b])$ of the associated measure $\mu$. -/
def rectangleValue {d : ℕ} (F : (Fin d → ℝ) → ℝ) (a b : Fin d → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, (-1 : ℝ) ^ S.card * F (rectangleVertex a b S)

/-- The family of left-infinite intervals `{Iic n : n ∈ ℕ}` is a countable
spanning collection of `ℝ`: their union covers all of `ℝ`. -/
private lemma isCountablySpanning_range_Iic :
    IsCountablySpanning (range (Iic : ℝ → Set ℝ)) :=
  ⟨fun n => Iic (n : ℝ), fun n => mem_range.mpr ⟨n, rfl⟩, by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩

/-- The Borel σ-algebra on `ℝ` is generated by the left-infinite intervals
`Iic x` for `x ∈ ℝ`. -/
private lemma generateFrom_range_Iic :
    generateFrom (range (Iic : ℝ → Set ℝ)) = (inferInstance : MeasurableSpace ℝ) :=
  (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm

/-- **Lower orthants form a π-system.** For $a \in \mathbb{R}^d$ let
$L_a = \prod_{i=1}^d (-\infty, a_i]$. If two such boxes $L_a$ and $L_b$ intersect, then their
intersection is $L_c$ for some $c \in \mathbb{R}^d$. -/
lemma isPiSystem_piIic (d : ℕ) :
    IsPiSystem (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ))) :=
  IsPiSystem.pi fun _ => isPiSystem_Iic

/-- **Lower orthants generate the product σ-algebra on $\mathbb{R}^d$.** The product σ-algebra on
$\mathbb{R}^d$, built from the Borel σ-algebra on each coordinate, is generated by the boxes
$\prod_{i=1}^d (-\infty, a_i]$ for $a \in \mathbb{R}^d$. -/
lemma generateFrom_piIic (d : ℕ) :
    generateFrom (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ))) =
      MeasurableSpace.pi :=
  generateFrom_eq_pi (fun _ => generateFrom_range_Iic)
    (fun _ => isCountablySpanning_range_Iic)

/-- **Quadrant uniqueness for measures on $\mathbb{R}^d$.** Let $\mu$ and $\nu$ be finite measures
on $\mathbb{R}^d$. If $\mu(\{x : x \le a\}) = \nu(\{x : x \le a\})$ for every $a \in \mathbb{R}^d$,
where $x \le a$ means $x_i \le a_i$ for every $i$, then $\mu = \nu$.

This is the multivariate analogue of a CDF determining a probability measure. -/
theorem Measure.ext_of_Iic_pi (d : ℕ)
    (μ ν : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : Fin d → ℝ, μ (Iic a) = ν (Iic a)) :
    μ = ν := by
  apply Measure.ext_of_generateFrom_of_iUnion
    (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ)))
    (fun n : ℕ => Iic (fun _ : Fin d => (n : ℝ)))
  · exact (generateFrom_piIic d).symm
  · exact isPiSystem_piIic d
  · ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true, Pi.le_def]
    refine ⟨⌈∑ i, |x i|⌉₊, fun i => ?_⟩
    calc x i ≤ |x i| := le_abs_self _
      _ ≤ ∑ j, |x j| :=
        Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
      _ ≤ (⌈∑ j, |x j|⌉₊ : ℝ) := Nat.le_ceil _
  · intro n
    refine ⟨fun _ => Iic (n : ℝ), fun i _ => ⟨n, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Pi.le_def]
  · intro n
    exact measure_ne_top μ _
  · intro s hs
    obtain ⟨f, hf, rfl⟩ := hs
    choose a ha using fun i => hf i (Set.mem_univ i)
    have hpi : univ.pi f = Iic a := by
      ext x
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Pi.le_def]
      exact forall_congr' fun i => by rw [← ha i]; simp [Set.mem_Iic]
    rw [hpi]
    exact h a

/-- **Nonempty bounded half-open intervals.** The family of all intervals
$(l, u] \subseteq \mathbb{R}$ with real endpoints $l < u$. It is used as a generating π-system for
the Borel σ-algebra on $\mathbb{R}$. -/
def C_Ioc_pi : Set (Set ℝ) := { S | ∃ l u, l < u ∧ Ioc l u = S }

/-- **Nonempty bounded half-open intervals form a π-system.** If two intervals $(l, u]$ and
$(l', u']$ in $\mathbb{R}$ with $l < u$ and $l' < u'$ intersect, then their intersection is again
an interval $(l'', u'']$ with $l'' < u''$. -/
lemma isPiSystem_C_Ioc_pi : IsPiSystem C_Ioc_pi := by
  have h := isPiSystem_Ioc_mem (univ : Set ℝ) univ
  show IsPiSystem { S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S }
  simpa only [mem_univ, true_and] using h

/-- **Half-open intervals generate the Borel σ-algebra on $\mathbb{R}$.** The Borel σ-algebra on
$\mathbb{R}$ is the σ-algebra generated by the nonempty bounded half-open intervals $(l, u]$
with $l < u$. -/
lemma generateFrom_C_Ioc_pi :
    generateFrom C_Ioc_pi = (inferInstance : MeasurableSpace ℝ) := by
  rw [show (inferInstance : MeasurableSpace ℝ) = borel ℝ from BorelSpace.measurable_eq]
  exact (borel_eq_generateFrom_Ioc ℝ).symm

/-- **Half-open intervals countably span $\mathbb{R}$.** There is a sequence of nonempty bounded
half-open intervals $(l, u]$ with $l < u$ whose union is $\mathbb{R}$; for example, the intervals
$(-n - 1, n + 1]$ for $n \in \mathbb{N}$. -/
lemma isCountablySpanning_C_Ioc_pi : IsCountablySpanning C_Ioc_pi := by
  refine ⟨fun n => Ioc (-(n : ℝ) - 1) (n + 1), ?_, ?_⟩
  · intro n
    exact ⟨-(n : ℝ) - 1, n + 1, by linarith, rfl⟩
  · ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- Core rectangle-uniqueness argument, with the finiteness of the first
measure on the spanning boxes as an explicit hypothesis. The two public
theorems below discharge it in different ways: from global finiteness,
and from the rectangle formula for a distribution function. -/
private theorem eq_of_forall_Ioc_eq_of_forall_ne_top (d : ℕ)
    (μ₁ μ₂ : Measure (Fin d → ℝ))
    (hfin : ∀ n : ℕ,
      μ₁ (univ.pi fun _ : Fin d => Ioc (-(n : ℝ) - 1) ((n : ℝ) + 1)) ≠ ∞)
    (h : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) = μ₂ (univ.pi fun i => Ioc (a i) (b i))) :
    μ₁ = μ₂ := by
  apply Measure.ext_of_generateFrom_of_iUnion
    (univ.pi '' univ.pi (fun _ : Fin d => C_Ioc_pi))
    (fun n : ℕ => univ.pi (fun _ : Fin d => Ioc (-(n : ℝ) - 1) ((n : ℝ) + 1)))
  · exact (generateFrom_eq_pi
      (fun _ => generateFrom_C_Ioc_pi) (fun _ => isCountablySpanning_C_Ioc_pi)).symm
  · exact IsPiSystem.pi fun _ => isPiSystem_C_Ioc_pi
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hd : d = 0
    · subst hd
      exact ⟨0, fun i _ => Fin.elim0 i⟩
    · have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
      have hex : ∃ n : ℕ, ∀ i : Fin d, |x i| < (n : ℝ) := by
        obtain ⟨n, hn⟩ := exists_nat_gt
          (Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|))
        exact ⟨n, fun i => lt_of_le_of_lt
          (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)) hn⟩
      obtain ⟨n, hn⟩ := hex
      refine ⟨n, fun i _ => ?_⟩
      exact ⟨by linarith [neg_abs_le (x i), hn i], by linarith [le_abs_self (x i), hn i]⟩
  · intro n
    exact ⟨fun _ => Ioc (-(n : ℝ) - 1) (n + 1),
      fun i _ => ⟨-(n : ℝ) - 1, n + 1, by linarith, rfl⟩, rfl⟩
  · intro n
    exact hfin n
  · intro s hs
    obtain ⟨f, hf, rfl⟩ := hs
    choose a b hab hfab using fun i => hf i (mem_univ i)
    have heq : univ.pi f = univ.pi (fun i => Ioc (a i) (b i)) := by
      congr 1
      funext i
      exact (hfab i).symm
    rw [heq, h a b (fun i => le_of_lt (hab i))]

/-- **Rectangle uniqueness for measures on $\mathbb{R}^d$.** Let $\mu_1$ and $\mu_2$ be finite
measures on $\mathbb{R}^d$. If $\mu_1((a, b]) = \mu_2((a, b])$ for all $a, b \in \mathbb{R}^d$ with
$a_i \le b_i$ for every $i$, where $(a, b] = \prod_{i=1}^d (a_i, b_i]$, then $\mu_1 = \mu_2$.

The finiteness hypothesis is essential: for $d \ge 1$, counting measure and twice counting measure
agree on every rectangle (both give $\infty$ on every nonempty rectangle and $0$ on every empty
one) but are distinct. -/
theorem Measure.eq_of_forall_Ioc_eq (d : ℕ)
    (μ₁ μ₂ : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) = μ₂ (univ.pi fun i => Ioc (a i) (b i))) :
    μ₁ = μ₂ :=
  eq_of_forall_Ioc_eq_of_forall_ne_top d μ₁ μ₂ (fun _ => measure_ne_top μ₁ _) h

/-- **Uniqueness from rectangle values.** Let $F : \mathbb{R}^d \to \mathbb{R}$, and let $\mu_1$
and $\mu_2$ be measures on $\mathbb{R}^d$. Suppose that for all $a, b \in \mathbb{R}^d$ with
$a_i \le b_i$ for every $i$, both $\mu_1$ and $\mu_2$ assign the rectangle
$(a, b] = \prod_{i=1}^d (a_i, b_i]$ the mass $\max(\Delta_{a,b} F, 0)$, where $\Delta_{a,b} F$
is the rectangle value of $F$ at $a, b$. Then $\mu_1 = \mu_2$.

This is the uniqueness half of the characterization of measures on $\mathbb{R}^d$ by a
distribution function. No finiteness hypothesis is needed: the rectangle formula itself forces
the measures to be finite on every rectangle $(a, b]$. -/
theorem Measure.eq_of_forall_rectangleValue_eq {d : ℕ}
    (F : (Fin d → ℝ) → ℝ)
    {μ₁ μ₂ : Measure (Fin d → ℝ)}
    (h₁ : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) = ENNReal.ofReal (rectangleValue F a b))
    (h₂ : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₂ (univ.pi fun i => Ioc (a i) (b i)) = ENNReal.ofReal (rectangleValue F a b)) :
    μ₁ = μ₂ := by
  refine eq_of_forall_Ioc_eq_of_forall_ne_top d μ₁ μ₂ (fun n => ?_) (fun a b hab => ?_)
  · rw [show univ.pi (fun _ : Fin d => Ioc (-(n : ℝ) - 1) ((n : ℝ) + 1)) =
        univ.pi (fun i => Ioc ((fun _ => -(n : ℝ) - 1) i) ((fun _ => (n : ℝ) + 1) i)) from rfl,
      h₁ _ _ (fun _ => by linarith)]
    exact ENNReal.ofReal_ne_top
  · rw [h₁ a b hab, h₂ a b hab]

/-- **Moment determinacy on a compact subset of `ℝ^d`.** Let `E ⊆ ℝ^d` be compact and let `μ`, `ν`
be finite Borel measures on `ℝ^d` that put no mass outside `E`. If all their mixed moments agree,
`∫ ∏ i, x i ^ β i ∂μ = ∫ ∏ i, x i ^ β i ∂ν` for every multi-index `β : Fin d → ℕ`, then
`μ = ν`. (The `β = 0` moment is the total mass.) -/
theorem Measure.eq_of_forall_integral_monomial_eq {d : ℕ} {E : Set (Fin d → ℝ)}
    (hE : IsCompact E) (μ ν : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0)
    (h : ∀ β : Fin d → ℕ, ∫ x, ∏ i, x i ^ β i ∂μ = ∫ x, ∏ i, x i ^ β i ∂ν) :
    μ = ν := by
  have hEμ : ∀ᵐ x ∂μ, x ∈ E := mem_ae_iff.mpr hμ
  have hEν : ∀ᵐ x ∂ν, x ∈ E := mem_ae_iff.mpr hν
  have hmon_cont : ∀ β : Fin d → ℕ, Continuous (fun x : Fin d → ℝ => ∏ i, x i ^ β i) :=
    fun β => by continuity
  have hmon_intμ : ∀ β : Fin d → ℕ, Integrable (fun x : Fin d → ℝ => ∏ i, x i ^ β i) μ := by
    intro β
    have hc := hmon_cont β
    have hmeas : AEStronglyMeasurable (fun x : Fin d → ℝ => ∏ i, x i ^ β i) μ :=
      hc.aestronglyMeasurable
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hE hc.continuousOn
    refine Integrable.of_bound hmeas C ?_
    filter_upwards [hEμ] with x hx
    exact hC x hx
  have hmon_intν : ∀ β : Fin d → ℕ, Integrable (fun x : Fin d → ℝ => ∏ i, x i ^ β i) ν := by
    intro β
    have hc := hmon_cont β
    have hmeas : AEStronglyMeasurable (fun x : Fin d → ℝ => ∏ i, x i ^ β i) ν :=
      hc.aestronglyMeasurable
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hE hc.continuousOn
    refine Integrable.of_bound hmeas C ?_
    filter_upwards [hEν] with x hx
    exact hC x hx
  have hpoly : ∀ p : MvPolynomial (Fin d) ℝ,
      ∫ x, MvPolynomial.eval x p ∂μ = ∫ x, MvPolynomial.eval x p ∂ν := by
    intro p
    have hfun : (fun x : Fin d → ℝ => MvPolynomial.eval x p)
        = (fun x => ∑ m ∈ p.support, p.coeff m * ∏ i, x i ^ m i) := by
      funext x
      exact MvPolynomial.eval_eq' x p
    rw [hfun]
    have hint1 : ∀ m ∈ p.support,
        Integrable (fun x : Fin d → ℝ => p.coeff m * ∏ i, x i ^ m i) μ := by
      intro m hm
      exact Integrable.const_mul (hmon_intμ ⇑m) (p.coeff m)
    have hint2 : ∀ m ∈ p.support,
        Integrable (fun x : Fin d → ℝ => p.coeff m * ∏ i, x i ^ m i) ν := by
      intro m hm
      exact Integrable.const_mul (hmon_intν ⇑m) (p.coeff m)
    rw [integral_finsetSum p.support hint1, integral_finsetSum p.support hint2]
    apply Finset.sum_congr rfl
    intro m hm
    rw [integral_const_mul, integral_const_mul]
    congr 1
    exact h ⇑m
  have hcont_intμ : ∀ g : ContinuousMap (Fin d → ℝ) ℝ, Integrable ⇑g μ := by
    intro g
    have hc : Continuous ⇑g := g.continuous
    have hmeas : AEStronglyMeasurable ⇑g μ := hc.aestronglyMeasurable
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hE hc.continuousOn
    refine Integrable.of_bound hmeas C ?_
    filter_upwards [hEμ] with x hx
    exact hC x hx
  have hcont_intν : ∀ g : ContinuousMap (Fin d → ℝ) ℝ, Integrable ⇑g ν := by
    intro g
    have hc : Continuous ⇑g := g.continuous
    have hmeas : AEStronglyMeasurable ⇑g ν := hc.aestronglyMeasurable
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hE hc.continuousOn
    refine Integrable.of_bound hmeas C ?_
    filter_upwards [hEν] with x hx
    exact hC x hx
  let A : Subalgebra ℝ (ContinuousMap (Fin d → ℝ) ℝ) :=
    { carrier := {f | ∃ p : MvPolynomial (Fin d) ℝ, ∀ x, f x = MvPolynomial.eval x p}
      zero_mem' := ⟨0, by intro x; simp⟩
      one_mem' := ⟨1, by intro x; simp⟩
      add_mem' := by
        intro f g hf hg
        obtain ⟨p, hp⟩ := hf
        obtain ⟨q, hq⟩ := hg
        exact ⟨p + q, by intro x; simp [hp x, hq x, MvPolynomial.eval_add]⟩
      mul_mem' := by
        intro f g hf hg
        obtain ⟨p, hp⟩ := hf
        obtain ⟨q, hq⟩ := hg
        exact ⟨p * q, by intro x; simp [hp x, hq x, MvPolynomial.eval_mul]⟩
      algebraMap_mem' := by
        intro r
        exact ⟨MvPolynomial.C r, by intro x; simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    let p : MvPolynomial (Fin d) ℝ := MvPolynomial.X i
    let g : ContinuousMap (Fin d → ℝ) ℝ :=
      ⟨fun x => MvPolynomial.eval x p, MvPolynomial.continuous_eval p⟩
    have hgA : g ∈ A := ⟨p, fun x => rfl⟩
    have himg : (fun f : ContinuousMap (Fin d → ℝ) ℝ => (f : (Fin d → ℝ) → ℝ)) g ∈
        (fun f : ContinuousMap (Fin d → ℝ) ℝ => (f : (Fin d → ℝ) → ℝ)) ''
          (A : Set (ContinuousMap (Fin d → ℝ) ℝ)) := by
      exact ⟨g, hgA, rfl⟩
    refine ⟨_, himg, ?_⟩
    change g x ≠ g y
    have hx : g x = x i := MvPolynomial.eval_X i
    have hy : g y = y i := MvPolynomial.eval_X i
    rw [hx, hy]
    exact hi
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfμ : Integrable ⇑f μ := BoundedContinuousFunction.integrable μ f
  have hfν : Integrable ⇑f ν := BoundedContinuousFunction.integrable ν f
  have hKnonneg : 0 ≤ μ.real Set.univ + ν.real Set.univ := by
    have h1 : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    have h2 : 0 ≤ ν.real Set.univ := ENNReal.toReal_nonneg
    linarith
  apply eq_of_forall_dist_le
  intro ε hε
  set K := μ.real Set.univ + ν.real Set.univ with hKdef
  have hKnonneg' : 0 ≤ K := hKnonneg
  have hK1pos : 0 < K + 1 := by linarith
  set δ := ε / (K + 1) with hδdef
  have hδpos : 0 < δ := div_pos hε hK1pos
  let fc : ContinuousMap (Fin d → ℝ) ℝ := f.toContinuousMap
  obtain ⟨g, hgA, happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hsep fc hE hδpos
  obtain ⟨p, hp⟩ := hgA
  have hg_eq : (∫ x, g x ∂μ) = (∫ x, g x ∂ν) := by
    have h1 : (∫ x, g x ∂μ) = (∫ x, MvPolynomial.eval x p ∂μ) := by
      simp only [hp]
    have h2 : (∫ x, g x ∂ν) = (∫ x, MvPolynomial.eval x p ∂ν) := by
      simp only [hp]
    rw [h1, h2]
    exact hpoly p
  have hgμ : Integrable ⇑g μ := hcont_intμ g
  have hgν : Integrable ⇑g ν := hcont_intν g
  have hboundμ : ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖ ≤ δ * μ.real Set.univ := by
    have heq : (∫ x, (f x - g x) ∂μ) = (∫ x, f x ∂μ) - (∫ x, g x ∂μ) :=
      integral_sub hfμ hgμ
    have hle : ‖∫ x, (f x - g x) ∂μ‖ ≤ δ * μ.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [hEμ] with x hx
      have happ := happrox x hx
      have hfc : fc x = f x := rfl
      rw [hfc] at happ
      rw [norm_sub_rev]
      exact le_of_lt happ
    rw [heq] at hle
    exact hle
  have hboundν : ‖(∫ x, f x ∂ν) - (∫ x, g x ∂ν)‖ ≤ δ * ν.real Set.univ := by
    have heq : (∫ x, (f x - g x) ∂ν) = (∫ x, f x ∂ν) - (∫ x, g x ∂ν) :=
      integral_sub hfν hgν
    have hle : ‖∫ x, (f x - g x) ∂ν‖ ≤ δ * ν.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [hEν] with x hx
      have happ := happrox x hx
      have hfc : fc x = f x := rfl
      rw [hfc] at happ
      rw [norm_sub_rev]
      exact le_of_lt happ
    rw [heq] at hle
    exact hle
  have htri : ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ δ * K := by
    have hring : (∫ x, f x ∂μ) - (∫ x, f x ∂ν)
        = ((∫ x, f x ∂μ) - (∫ x, g x ∂μ)) + ((∫ x, g x ∂μ) - (∫ x, g x ∂ν))
          + ((∫ x, g x ∂ν) - (∫ x, f x ∂ν)) := by ring
    have hmid : (∫ x, g x ∂μ) - (∫ x, g x ∂ν) = 0 := by rw [hg_eq, sub_self]
    have hnorm : ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖
        ≤ ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖ + ‖(∫ x, g x ∂μ) - (∫ x, g x ∂ν)‖
          + ‖(∫ x, g x ∂ν) - (∫ x, f x ∂ν)‖ := by
      rw [hring]
      calc ‖_ + _ + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
          gcongr
          exact norm_add_le _ _
    rw [hmid] at hnorm
    simp only [norm_zero, add_zero] at hnorm
    have hrev : ‖(∫ x, g x ∂ν) - (∫ x, f x ∂ν)‖ = ‖(∫ x, f x ∂ν) - (∫ x, g x ∂ν)‖ :=
      norm_sub_rev _ _
    rw [hrev] at hnorm
    calc ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖
        ≤ ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖ + ‖(∫ x, f x ∂ν) - (∫ x, g x ∂ν)‖ := hnorm
      _ ≤ δ * μ.real Set.univ + δ * ν.real Set.univ := add_le_add hboundμ hboundν
      _ = δ * K := by rw [hKdef]; ring
  have hδK : δ * K ≤ ε := by
    have h1 : K / (K + 1) ≤ 1 := by
      rw [div_le_one hK1pos]
      linarith
    calc δ * K = ε * (K / (K + 1)) := by rw [hδdef]; ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hε)
      _ = ε := mul_one ε
  rw [dist_eq_norm]
  calc ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ δ * K := htri
    _ ≤ ε := hδK


end MeasureTheory

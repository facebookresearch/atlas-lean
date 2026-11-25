/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Domains.Biology.PopulationGenetics.Linkage
public import Domains.Biology.PopulationGenetics.Selection
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Multiplicative haploid selection preserves linkage equilibrium

For two alleles at each of two loci, suppose the haplotype frequencies are in
linkage equilibrium, `x (i, j) = p i * q j`, and haplotype fitnesses are
multiplicative across loci, `w (i, j) = a i * b j`. Then one generation of
haploid selection followed by random mating with any recombination fraction
is again a product: the factors are the single-locus selected frequencies
`select p a` and `select q b`. In particular, the resulting linkage
disequilibrium is zero.

This is the haploid product-fitness statement. A diploid two-locus product
law would require a diploid two-locus recursion and is not stated here.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, Section VIII.2.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Classical.TwoLocusSelection

/-- **Multiplicative haploid selection preserves linkage equilibrium** (core identity, two
alleles at each of two loci). A haplotype is `g : Bool × Bool` (`g.1` the allele at the first
locus, `g.2` the allele at the second). The haplotype frequencies are in linkage equilibrium,
`x g = p g.1 * q g.2`, and the haplotype fitnesses are multiplicative across loci,
`w g = a g.1 * b g.2`. `y` is the result of one round of haploid selection,
`y g = x g * w g / ∑ h, x h * w h`. One round of random mating with recombination fraction `r`,
`(1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2)))`, then gives the product of the two
single-locus selected frequencies `p i * a i / ∑ j, p j * a j` and
`q i * b i / ∑ j, q j * b j`, so the population stays in linkage equilibrium.

The identity holds for every real `r` and needs no nonzero mean-fitness hypothesis: when a
single-locus mean fitness vanishes, both sides are `0` (`x / 0 = 0`). The biological domain is
`0 ≤ r ≤ 1/2`, `p` and `q` on the simplex and positive fitnesses. -/
theorem recombine_select_eq_mul (r : ℝ) (x w y : Bool × Bool → ℝ) (p q a b : Bool → ℝ)
    (hx : ∀ g, x g = p g.1 * q g.2) (hw : ∀ g, w g = a g.1 * b g.2)
    (hy : ∀ g, y g = x g * w g / ∑ h, x h * w h) (g : Bool × Bool) :
    (1 - r) * y g + r * ((∑ l, y (g.1, l)) * (∑ k, y (k, g.2))) =
      p g.1 * a g.1 / (∑ i, p i * a i) * (q g.2 * b g.2 / ∑ j, q j * b j) := by
  have hW : (∑ h, x h * w h) = (∑ i, p i * a i) * (∑ j, q j * b j) := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hx (i, j), hw (i, j)]
    ring
  have hY : y g = (p g.1 * a g.1) * (q g.2 * b g.2) / (∑ h, x h * w h) := by
    rw [hy g, hx g, hw g]
    ring
  have hM1 : (∑ l, y (g.1, l)) =
      (p g.1 * a g.1) * (∑ j, q j * b j) / (∑ h, x h * w h) := by
    have hpt : ∀ l, y (g.1, l) =
        (p g.1 * a g.1) * (q l * b l) / (∑ h, x h * w h) := by
      intro l
      rw [hy _, hx _, hw _]
      ring
    simp_rw [hpt]
    rw [← Finset.sum_div, ← Finset.mul_sum]
  have hM2 : (∑ k, y (k, g.2)) =
      (∑ i, p i * a i) * (q g.2 * b g.2) / (∑ h, x h * w h) := by
    have hpt : ∀ k, y (k, g.2) =
        (p k * a k) * (q g.2 * b g.2) / (∑ h, x h * w h) := by
      intro k
      rw [hy _, hx _, hw _]
      ring
    simp_rw [hpt]
    rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [hY, hM1, hM2, hW]
  by_cases hA : (∑ i, p i * a i) = 0
  · rw [hA]
    simp
  · by_cases hB : (∑ j, q j * b j) = 0
    · rw [hB]
      simp
    · have hW0 : (∑ i, p i * a i) * (∑ j, q j * b j) ≠ 0 :=
        mul_ne_zero hA hB
      field_simp
      ring

/-- Multiplicative haploid selection followed by recombination preserves a
product haplotype-frequency vector, stated with Atlas's `Selection.select`
and `Linkage.recombine`. It holds for all real `r`, `p`, `q`, `a`, `b`: when a single-locus mean
fitness vanishes, both sides are `0` (division by zero gives zero). -/
theorem recombine_select_of_mul {r : ℝ} {x w : Bool × Bool → ℝ}
    {p q a b : Bool → ℝ} (hx : ∀ g, x g = p g.1 * q g.2)
    (hw : ∀ g, w g = a g.1 * b g.2) (g : Bool × Bool) :
    MathlibExt.Biology.PopulationGenetics.Linkage.recombine r
        (MathlibExt.Biology.PopulationGenetics.Selection.select x w) g =
      MathlibExt.Biology.PopulationGenetics.Selection.select p a g.1 *
        MathlibExt.Biology.PopulationGenetics.Selection.select q b g.2 :=
  recombine_select_eq_mul r x w
    (MathlibExt.Biology.PopulationGenetics.Selection.select x w)
    p q a b hx hw (fun _ => rfl) g

/-- If the haplotype frequencies are in linkage equilibrium (`x g = p g.1 * q g.2`) and the
fitnesses are multiplicative across loci (`w g = a g.1 * b g.2`), then for every `r` the haplotype
frequencies after selection and recombination have zero linkage disequilibrium. Here `p`, `q`,
`a`, `b` are arbitrary real vectors: when a single-locus mean fitness vanishes, so does the
haplotype mean fitness, and division by zero makes the selected and then the recombined
frequencies `0`, not a haplotype distribution. The biological domain is `0 ≤ r ≤ 1/2`, `p` and
`q` on the simplex and positive fitnesses. -/
theorem linkageDiseq_recombine_select_of_mul {r : ℝ}
    {x w : Bool × Bool → ℝ} {p q a b : Bool → ℝ}
    (hx : ∀ g, x g = p g.1 * q g.2) (hw : ∀ g, w g = a g.1 * b g.2) :
    MathlibExt.Biology.PopulationGenetics.Linkage.linkageDiseq
        (MathlibExt.Biology.PopulationGenetics.Linkage.recombine r
          (MathlibExt.Biology.PopulationGenetics.Selection.select x w)) = 0 := by
  unfold MathlibExt.Biology.PopulationGenetics.Linkage.linkageDiseq
  rw [recombine_select_of_mul hx hw (true, true),
    recombine_select_of_mul hx hw (false, false),
    recombine_select_of_mul hx hw (true, false),
    recombine_select_of_mul hx hw (false, true)]
  ring

open Linkage Selection

private theorem select_mul_select (x w : Bool × Bool → ℝ) (g h : Bool × Bool) :
    select x w g * select x w h = x g * x h * (w g * w h) / meanFitness x w ^ 2 := by
  rw [select, select, ← mul_div_mul_comm, pow_two]
  congr 1
  ring

/-- **Haploid selection and the crossproduct ratio.** A haplotype is a pair of alleles, in
order `AB`, `Ab`, `aB`, `ab` for `(true, true)`, `(true, false)`, `(false, true)`, `(false, false)`.
For simplex frequencies `x` and positive fitnesses `w`, selection without recombination gives
`x' = select x w`. This gives the update for linkage disequilibrium and, when `x_Ab * x_aB > 0`,
multiplies the crossproduct ratio by `w_AB * w_ab / (w_Ab * w_aB)`.

At initial linkage equilibrium, both frequency crossproducts equal `p (1 - p) q (1 - q)`,
where `p`, `q` are the frequencies of `A`, `B`. Equilibrium is preserved exactly when the fitness
crossproducts agree or at least one locus is monomorphic. If both are polymorphic, the sign of
the new disequilibrium is that of `w_AB * w_ab - w_Ab * w_aB`.

In the parametrization `w = ((1 + s) * (1 + t) * (1 + E), 1 + s, 1 + t, 1)`, the ratio
multiplier is `1 + E`. If fitness is additive (`w_AB = 1 + s + t`), then
`E = -(s * t) / ((1 + s) * (1 + t))`, and `s * t > 0` yields negative disequilibrium from
equilibrium at polymorphic loci. See Felsenstein, *Theoretical Evolutionary Genetics*,
Section VIII.2, equations (VIII-3)–(VIII-9), pp. 360–361. -/
theorem haploid_selection_crossproduct_ratio {x w : Bool × Bool → ℝ}
    (hx : ∀ g, 0 ≤ x g) (hsum : ∑ g, x g = 1) (hw : ∀ g, 0 < w g) :
    let x' := select x w
    let W := meanFitness x w
    let u := w (true, true) * w (false, false)
    let v := w (true, false) * w (false, true)
    let p := alleleFreqFst x true
    let q := alleleFreqSnd x true
    let c := p * (1 - p) * q * (1 - q)
    linkageDiseq x' =
      (x (true, true) * x (false, false) * u - x (true, false) * x (false, true) * v) / W ^ 2 ∧
    (0 < x (true, false) * x (false, true) →
      0 < x' (true, false) * x' (false, true) ∧
      x' (true, true) * x' (false, false) / (x' (true, false) * x' (false, true)) =
        x (true, true) * x (false, false) / (x (true, false) * x (false, true)) * (u / v)) ∧
    (linkageDiseq x = 0 →
      x (true, true) * x (false, false) = c ∧ x (true, false) * x (false, true) = c ∧
      linkageDiseq x' = c * (u - v) / W ^ 2 ∧
      (linkageDiseq x' = 0 ↔ u = v ∨ p = 0 ∨ p = 1 ∨ q = 0 ∨ q = 1) ∧
      (0 < p → p < 1 → 0 < q → q < 1 →
        (0 < linkageDiseq x' ↔ v < u) ∧ (linkageDiseq x' < 0 ↔ u < v))) ∧
    (∀ s t E : ℝ, w (true, true) = (1 + s) * (1 + t) * (1 + E) →
      w (true, false) = 1 + s → w (false, true) = 1 + t → w (false, false) = 1 →
      u / v = 1 + E ∧
      (w (true, true) = 1 + s + t → E = -(s * t) / ((1 + s) * (1 + t)) ∧
        (0 < s * t → linkageDiseq x = 0 → 0 < p → p < 1 → 0 < q → q < 1 →
          linkageDiseq x' < 0))) := by
  dsimp only
  let p := alleleFreqFst x true
  let q := alleleFreqSnd x true
  let c := p * (1 - p) * q * (1 - q)
  let u := w (true, true) * w (false, false)
  let v := w (true, false) * w (false, true)
  have hW := meanFitness_pos hx hsum hw
  have hW2 := pow_pos hW 2
  have hD : linkageDiseq (select x w) =
      (x (true, true) * x (false, false) * u - x (true, false) * x (false, true) * v) /
        meanFitness x w ^ 2 := by
    simp only [linkageDiseq, select_mul_select, ← sub_div, u, v]
  have hEq (heq : linkageDiseq x = 0) :
      x (true, true) * x (false, false) = c ∧ x (true, false) * x (false, true) = c ∧
      linkageDiseq (select x w) = c * (u - v) / meanFitness x w ^ 2 := by
    have hp : p = x (true, true) + x (true, false) := by
      simp [p, alleleFreqFst, add_comm]
    have hq : q = x (true, true) + x (false, true) := by
      simp [q, alleleFreqSnd, add_comm]
    have hAB : x (true, true) = p * q := by
      rw [hp, hq]
      rw [sum_four] at hsum
      unfold linkageDiseq at heq
      linear_combination heq - x (true, true) * hsum
    have hAb : x (true, false) = p * (1 - q) := by
      linear_combination -hAB - hp
    have haB : x (false, true) = (1 - p) * q := by
      linear_combination -hAB - hq
    have hr : x (true, false) * x (false, true) = c := by
      rw [hAb, haB]
      dsimp only [c]
      ring
    have hc : x (true, true) * x (false, false) = c := (sub_eq_zero.mp heq).trans hr
    exact ⟨hc, hr, by rw [hD, hc, hr, mul_sub]⟩
  have hSign (heq : linkageDiseq x = 0) (hc : 0 < c) :
      (0 < linkageDiseq (select x w) ↔ v < u) ∧ (linkageDiseq (select x w) < 0 ↔ u < v) := by
    rw [(hEq heq).2.2]
    constructor
    · rw [lt_div_iff₀ hW2, zero_mul, mul_pos_iff_of_pos_left hc, sub_pos]
    · rw [div_lt_iff₀ hW2, zero_mul, ← mul_zero c, mul_lt_mul_iff_right₀ hc, sub_neg]
  have hcPos (hp₀ : 0 < p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1) : 0 < c :=
    mul_pos (mul_pos (mul_pos hp₀ (sub_pos.mpr hp₁)) hq₀) (sub_pos.mpr hq₁)
  refine ⟨hD, ?_, ?_, ?_⟩
  · intro hden
    have h₂ := pos_of_mul_pos_left hden (hx (false, true))
    have h₃ := pos_of_mul_pos_right hden (hx (true, false))
    refine ⟨mul_pos (div_pos (mul_pos h₂ (hw _)) hW) (div_pos (mul_pos h₃ (hw _)) hW), ?_⟩
    rw [select_mul_select, select_mul_select, div_div_div_cancel_right₀ hW2.ne', mul_div_mul_comm]
  · intro heq
    obtain ⟨hc, hr, hD'⟩ := hEq heq
    refine ⟨hc, hr, hD', ?_, fun hp₀ hp₁ hq₀ hq₁ => hSign heq (hcPos hp₀ hp₁ hq₀ hq₁)⟩
    rw [hD']
    simp only [c, u, v, p, q, div_eq_zero_iff, hW2.ne', or_false, mul_eq_zero, sub_eq_zero]
    simp only [or_assoc, or_left_comm, or_comm, eq_comm (a := (1 : ℝ))]
  · intro s t E hab hAb haB hab'
    have hst : 0 < (1 + s) * (1 + t) := by
      rw [← hAb, ← haB]
      exact mul_pos (hw _) (hw _)
    refine ⟨?_, ?_⟩
    · rw [hab, hAb, haB, hab', mul_one]
      exact (div_eq_iff hst.ne').2 (mul_comm _ _)
    · intro hadd
      have hdiff : u - v = -(s * t) := by
        dsimp only [u, v]
        rw [hadd, hAb, haB, hab']
        ring
      refine ⟨(eq_div_iff hst.ne').2 ?_, ?_⟩
      · linear_combination hab.symm.trans hadd
      · intro hprod heq hp₀ hp₁ hq₀ hq₁
        exact (hSign heq (hcPos hp₀ hp₁ hq₀ hq₁)).2.mpr (sub_neg.mp (hdiff ▸ neg_neg_of_pos hprod))

end MathlibExt.Biology.PopulationGenetics.Classical.TwoLocusSelection

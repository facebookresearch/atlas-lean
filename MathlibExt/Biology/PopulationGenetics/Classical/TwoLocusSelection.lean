/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.Biology.PopulationGenetics.Linkage
public import MathlibExt.Biology.PopulationGenetics.Selection
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
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
and `Linkage.recombine`. -/
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

/-- Under the same hypotheses, the haplotype frequencies after selection and
recombination have zero linkage disequilibrium. -/
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

end MathlibExt.Biology.PopulationGenetics.Classical.TwoLocusSelection

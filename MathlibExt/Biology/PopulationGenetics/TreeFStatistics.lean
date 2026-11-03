/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics

/-!
# Outgroup f3 and admixed branches

Two uses of f-statistics in the drift model of `FStatistics`.

## Outgroup f3 (Raghavan et al. 2014)

With binary loadings (in particular on a tree), `f3 O A B` is the total drift length of the
edges shared by the paths `O–A` and `O–B` (`f3_eq_sum_inter_symmDiff`). If `O` is an outgroup,
i.e. its root-to-`O` lineage shares no edge with the lineages of `A` and `B`, this is the drift
on the path from the outgroup to the root plus the drift shared by `A` and `B` from the root to
their common ancestor (`f3_outgroup`), as stated by Raghavan et al. (2014, Methods). The first
term does not depend on `A`, `B`, so for a fixed `A` the outgroup `f3` ranks candidate
populations `B` by the drift they share with `A` (`f3_outgroup_le_iff`).

## Admixed branches (MixMapper, Lipson et al. 2013)

MixMapper fits a population `Mx` as a mixture of two populations that split from points `A`
and `B` of an unadmixed scaffold tree, then drifted (edges `a` and `b`), mixed in proportions
`α : 1 - α`, and drifted again (edge `c`). For a reference population `X` that does not use
`a`, `b`, `c`,

  `f2 Mx X = α f2 A X + (1 - α) f2 B X - α (1 - α) f2 A B + (α² ℓ_a + (1 - α)² ℓ_b + ℓ_c)`

(`f2_admixedBranch`). The three terminal drift lengths enter only through the combination
`α² ℓ_a + (1 - α)² ℓ_b + ℓ_c` (`mixedDrift`, the paper's "MixedDrift"), which is why they are not
separately identifiable. Given the split points, two references `X₁`, `X₂` with different
contrasts `f2 A Xᵢ - f2 B Xᵢ` determine `α` (`alpha_eq_of_f2`) and then the mixed drift
(`mixedDrift_eq`). This identifiability statement, for split points given as populations of the
model, is our formulation; the paper's criterion for the split positions (two scaffold
populations branching from different points between the split points) is not formalized here.

## References

* M. Raghavan, P. Skoglund, K. E. Graf, et al., *Upper Palaeolithic Siberian genome reveals dual
  ancestry of Native Americans*, Nature 505 (2014), 87–91.
* M. Lipson, P.-R. Loh, A. Levin, D. Reich, N. Patterson, B. Berger, *Efficient moment-based
  inference of admixture parameters and sources of gene flow*, Mol. Biol. Evol. 30 (2013),
  1788–1802.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped symmDiff

namespace MathlibExt.Biology.PopulationGenetics.TreeFStatistics

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
  (M : DriftModel μ E P)

/-! ### Outgroup f3 -/

/-- With binary loadings, `f3 O A B` is the total drift length of the edges shared by the paths
`O–A` and `O–B` (on a tree, the path from `O` to the `A–B` path). -/
theorem f3_eq_sum_inter_symmDiff [DecidableEq E] (hM : M.HasBinaryLoadings) (O A B : P) :
    f3 μ M.freq O A B =
      ∑ e ∈ (M.lineage O ∆ M.lineage A) ∩ (M.lineage O ∆ M.lineage B), M.len e := by
  rw [M.f3_freq, ← Finset.univ_inter ((M.lineage O ∆ M.lineage A) ∩ _), ← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases hM O e with hO | hO <;> rcases hM A e with hA | hA <;> rcases hM B e with hB | hB <;>
    simp [DriftModel.lineage, Finset.mem_symmDiff, hO, hA, hB]

/-- Outgroup `f3` (Raghavan et al. 2014): with binary loadings, if the lineage of `O` shares no
edge with the lineages of `A` and `B`, then `f3 O A B` is the drift from the outgroup to the root
plus the drift shared by `A` and `B`. -/
theorem f3_outgroup [DecidableEq E] (hM : M.HasBinaryLoadings) {O A B : P}
    (hA : Disjoint (M.lineage O) (M.lineage A)) (hB : Disjoint (M.lineage O) (M.lineage B)) :
    f3 μ M.freq O A B = ∑ e ∈ M.lineage O, M.len e + ∑ e ∈ M.lineage A ∩ M.lineage B, M.len e := by
  rw [M.f3_freq, ← Finset.univ_inter (M.lineage O), ← Finset.univ_inter (M.lineage A ∩ _),
    ← Finset.sum_ite_mem, ← Finset.sum_ite_mem, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hOA : e ∈ M.lineage O → e ∉ M.lineage A := fun h => Finset.disjoint_left.mp hA h
  have hOB : e ∈ M.lineage O → e ∉ M.lineage B := fun h => Finset.disjoint_left.mp hB h
  rcases hM O e with hO | hO <;> rcases hM A e with hA' | hA' <;>
    rcases hM B e with hB' | hB' <;>
    simp_all [DriftModel.lineage]

/-- For a fixed outgroup `O` and population `A`, the outgroup `f3` ranks candidates `B` by the
drift they share with `A`. -/
theorem f3_outgroup_le_iff [DecidableEq E] (hM : M.HasBinaryLoadings) {O A B B' : P}
    (hA : Disjoint (M.lineage O) (M.lineage A)) (hB : Disjoint (M.lineage O) (M.lineage B))
    (hB' : Disjoint (M.lineage O) (M.lineage B')) :
    f3 μ M.freq O A B ≤ f3 μ M.freq O A B' ↔
      ∑ e ∈ M.lineage A ∩ M.lineage B, M.len e ≤ ∑ e ∈ M.lineage A ∩ M.lineage B', M.len e := by
  rw [f3_outgroup M hM hA hB, f3_outgroup M hM hA hB', add_le_add_iff_left]

/-! ### Admixed branches -/

/-- MixMapper's mixed drift `α² ℓ_a + (1 - α)² ℓ_b + ℓ_c`: the only combination of the terminal
drift lengths that enters the `f2` statistics of an admixed population. -/
def mixedDrift (α la lb lc : ℝ) : ℝ := α ^ 2 * la + (1 - α) ^ 2 * lb + lc

/-- The admixed-branch identity (Lipson et al. 2013): if `Mx` is an `α : 1 - α` mixture of the
endpoints of the edges `a` (below `A`) and `b` (below `B`), followed by drift on `c`, and `A`,
`B`, `X` do not use `a`, `b`, `c`, then
`f2 Mx X = α f2 A X + (1 - α) f2 B X - α (1 - α) f2 A B + mixedDrift α ℓ_a ℓ_b ℓ_c`. -/
theorem f2_admixedBranch [DecidableEq E] {Mx A B X : P} {a b c : E} {α : ℝ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hw : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hX : ∀ e ∈ ({a, b, c} : Finset E), M.weight X e = 0) :
    f2 μ M.freq Mx X = α * f2 μ M.freq A X + (1 - α) * f2 μ M.freq B X -
      α * (1 - α) * f2 μ M.freq A B + mixedDrift α (M.len a) (M.len b) (M.len c) := by
  have key : ∀ e, (M.weight Mx e - M.weight X e) ^ 2 * M.len e =
      α * ((M.weight A e - M.weight X e) ^ 2 * M.len e) +
        (1 - α) * ((M.weight B e - M.weight X e) ^ 2 * M.len e) -
        α * (1 - α) * ((M.weight A e - M.weight B e) ^ 2 * M.len e) +
        ((Pi.single a (α ^ 2 * M.len a) : E → ℝ) e +
          (Pi.single b ((1 - α) ^ 2 * M.len b) : E → ℝ) e + (Pi.single c (M.len c) : E → ℝ) e) := by
    intro e
    rw [hw]
    by_cases hea : e = a
    · subst hea
      simp [hA e (by simp), hB e (by simp), hX e (by simp), hab, hac]
    by_cases heb : e = b
    · subst heb
      simp [hA e (by simp), hB e (by simp), hX e (by simp), Ne.symm hab, hbc]
    by_cases hec : e = c
    · subst hec
      simp [hA e (by simp), hB e (by simp), hX e (by simp), Ne.symm hac, Ne.symm hbc]
    · simp [hea, heb, hec]
      ring
  rw [M.f2_freq, M.f2_freq, M.f2_freq, M.f2_freq, Finset.sum_congr rfl fun e _ => key e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_pi_single', Finset.mem_univ, ite_true, mixedDrift]

/-- Identifiability of the mixture proportion (our formulation): with the split points `A`, `B`
given, two references `X₁`, `X₂` satisfying the hypotheses of `f2_admixedBranch` and with
different contrasts `f2 A Xᵢ - f2 B Xᵢ` determine `α` from `f2` statistics. -/
theorem alpha_eq_of_f2 [DecidableEq E] {Mx A B X₁ X₂ : P} {a b c : E} {α : ℝ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hw : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hX₁ : ∀ e ∈ ({a, b, c} : Finset E), M.weight X₁ e = 0)
    (hX₂ : ∀ e ∈ ({a, b, c} : Finset E), M.weight X₂ e = 0)
    (hD : f2 μ M.freq A X₁ - f2 μ M.freq B X₁ ≠ f2 μ M.freq A X₂ - f2 μ M.freq B X₂) :
    α = (f2 μ M.freq Mx X₁ - f2 μ M.freq Mx X₂ - (f2 μ M.freq B X₁ - f2 μ M.freq B X₂)) /
      (f2 μ M.freq A X₁ - f2 μ M.freq B X₁ - (f2 μ M.freq A X₂ - f2 μ M.freq B X₂)) := by
  have h₁ := f2_admixedBranch M hab hac hbc hw hA hB hX₁
  have h₂ := f2_admixedBranch M hab hac hbc hw hA hB hX₂
  rw [eq_div_iff (sub_ne_zero.mpr hD), h₁, h₂]
  ring

/-- Given `α`, the mixed drift is determined by the `f2` statistics of one reference `X`. -/
theorem mixedDrift_eq [DecidableEq E] {Mx A B X : P} {a b c : E} {α : ℝ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hw : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hX : ∀ e ∈ ({a, b, c} : Finset E), M.weight X e = 0) :
    mixedDrift α (M.len a) (M.len b) (M.len c) = f2 μ M.freq Mx X - α * f2 μ M.freq A X -
      (1 - α) * f2 μ M.freq B X + α * (1 - α) * f2 μ M.freq A B := by
  rw [f2_admixedBranch M hab hac hbc hw hA hB hX]
  ring

end MathlibExt.Biology.PopulationGenetics.TreeFStatistics

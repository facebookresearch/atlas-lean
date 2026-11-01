/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.CodonOmega
import Mathlib.Tactic.NormNum

/-!
# Tests for the Goldman–Yang model and `dN / dS = ω`

A toy genetic code on all 64 codons in which the amino acid is the first nucleotide: changes
at the first position are nonsynonymous, at the other two synonymous. With uniform codon
frequencies both substitution rates are positive, so `dN / dS = ω` holds non-vacuously; the
Goldman–Yang matrix is a reversible rate matrix; and a degenerate code with a single amino acid
shows the junk value `dN = 0` when `ρ_N(1) = 0`.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.Phylogenetics.CodonOmega

open MathlibExt.Biology.Phylogenetics.CodonModel

/-- The toy code: the amino acid of a codon is its first nucleotide. -/
def firstBase (c : Codon) : Fin 4 := c 0

/-- Uniform codon frequencies. -/
noncomputable def uniform : Codon → ℝ := fun _ => 1 / 64

lemma uniform_pos (c : Codon) : 0 < uniform c := by norm_num [uniform]

lemma single_syn : IsSingleChange ![0, 0, 0] ![0, 0, 1] := by decide

lemma single_nonsyn : IsSingleChange ![0, 0, 0] ![1, 0, 0] := by decide

/-- Both rates are positive in the toy model, for every `κ > 0`. -/
lemma rates_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < synRate uniform id firstBase κ 1 ∧ 0 < nonsynRate uniform id firstBase κ 1 :=
  ⟨synRate_pos_of_mem id firstBase (fun c => (uniform_pos c).le) hκ (i := ![0, 0, 0])
      (j := ![0, 0, 1]) (by decide) rfl single_syn (uniform_pos _) (uniform_pos _),
    nonsynRate_pos_of_mem id firstBase (fun c => (uniform_pos c).le) hκ (i := ![0, 0, 0])
      (j := ![1, 0, 0]) (by decide) single_nonsyn (uniform_pos _) (uniform_pos _)⟩

/-- **`dN / dS = ω`** in the toy model, for every `κ > 0` and every `ω`. -/
example {κ : ℝ} (hκ : 0 < κ) (ω : ℝ) :
    dN uniform id firstBase κ ω / dS uniform id firstBase κ ω = ω :=
  dN_div_dS uniform id firstBase κ ω (rates_pos hκ).1 (rates_pos hκ).2

/-- Three sites per codon in the toy model. -/
example {κ : ℝ} (hκ : 0 < κ) :
    synSites uniform id firstBase κ + nonsynSites uniform id firstBase κ = 3 :=
  synSites_add_nonsynSites uniform id firstBase κ (add_pos (rates_pos hκ).1 (rates_pos hκ).2).ne'

/-- The Goldman–Yang matrix of the toy model is a reversible rate matrix. -/
example : ProbabilityTheory.IsRateMatrix (gyRate uniform id firstBase 2 0.5) ∧
    ProbabilityTheory.IsDetailedBalance uniform (gyRate uniform id firstBase 2 0.5) :=
  ⟨isRateMatrix_gyRate id firstBase (fun c => (uniform_pos c).le) (by norm_num) (by norm_num),
    isDetailedBalance_gyRate uniform id firstBase 2 0.5⟩

/-- A transition at the third position (`A → G`) is weighted by `κ`, a nonsynonymous
transversion at the first (`A → C`) by `ω`. -/
example (κ ω : ℝ) : gyExchange id firstBase κ ω ![0, 0, 0] ![0, 0, 2] = κ ∧
    gyExchange id firstBase κ ω ![0, 0, 0] ![1, 0, 0] = ω := by
  have h1 : IsSingleChange ![0, 0, 0] ![0, 0, 2] := by decide
  have h2 : IsTransitionChange ![0, 0, 0] ![0, 0, 2] := by decide
  have h3 : ¬ IsTransitionChange ![0, 0, 0] ![1, 0, 0] := by decide
  refine ⟨?_, ?_⟩
  · simp [gyExchange, firstBase, h1, h2]
  · simp [gyExchange, firstBase, single_nonsyn, h3]

/-- Junk value: with a single amino acid there are no nonsynonymous changes, `ρ_N = 0`, and
`dN = 0 / 0 = 0`. -/
example (κ ω : ℝ) : dN uniform id (fun _ => (0 : Fin 1)) κ ω = 0 := by
  simp [dN, nonsynRate]

end MathlibExtTest.Biology.Phylogenetics.CodonOmega

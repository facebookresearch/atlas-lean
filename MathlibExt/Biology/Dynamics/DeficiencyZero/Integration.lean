/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.DeficiencyZero.API
public import MathlibExt.Biology.Dynamics.DeficiencyZero.Existence
import MathlibExt.Biology.Dynamics.DeficiencyZero.RankIdentities

/-!
# The deficiency-zero theorem, weakly reversible case

This file connects the three parts of the deficiency-zero development:

* `MathlibExt.Biology.Dynamics.DeficiencyZero.API` defines the complexes, linkage classes,
  `deficiency` `δ = n - ℓ - s` and `IsWeaklyReversible` of a reaction network;
* `MathlibExt.Biology.Dynamics.DeficiencyZero.RankIdentities` proves
  `n - ℓ - s = dim (ker Y ∩ Δ)`, where `Δ = im ∂ = span {e_{prod r} - e_{src r}}` lives in
  the space of functions on the complexes and `Y` sends `e_y` to the composition `y`;
* `MathlibExt.Biology.Dynamics.DeficiencyZero.Existence` proves existence of a positive
  complex-balanced equilibrium from weak reversibility and the elementary form of
  `ker Y ∩ im ∂ = 0`: every weighting `α` of the reactions with
  `∑ α r (prod r - src r) = 0` has `∑ α r (η (prod r) - η (src r)) = 0` for every `η`.

## Main results

* `deficiency_eq_zero_iff`: `N.deficiency = 0` is equivalent to the elementary form of
  `ker Y ∩ im ∂ = 0` used in `Existence`.
* `exists_pos_isComplexBalanced`: a weakly reversible network of deficiency zero has, for any
  positive rate constants, a positive complex-balanced equilibrium (Horn 1972; Feinberg 1972).
* `existsUnique_equilibrium`: under the same hypotheses each positive stoichiometric
  compatibility class contains exactly one equilibrium (the deficiency-zero theorem, weakly
  reversible case).

The non-weakly-reversible half of the deficiency-zero theorem remains recorded in
`WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`.

## References

* F. Horn, "Necessary and sufficient conditions for complex balancing in chemical kinetics",
  Arch. Rational Mech. Anal. 49 (1972) 172–186.
* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42 (1987)
  2229–2268.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), §6.4.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The source of reaction `r` as a complex. -/
private def srcCx (r : ρ) : N.complexes := ⟨N.src r, src_mem_complexes r⟩

/-- The product of reaction `r` as a complex. -/
private def prodCx (r : ρ) : N.complexes := ⟨N.prod r, prod_mem_complexes r⟩

private lemma linkageGraph_adj_iff (c c' : N.complexes) :
    N.linkageGraph.Adj c c' ↔
      c ≠ c' ∧ ∃ r, (N.srcCx r = c ∧ N.prodCx r = c') ∨ (N.srcCx r = c' ∧ N.prodCx r = c) := by
  rw [linkageGraph_adj]
  simp only [Reacts, srcCx, prodCx, Subtype.ext_iff, ← exists_or]

/-- `δ = 0` is `ker Y ∩ Δ = ⊥` for the complexes of `N`, by the rank identity of
`RankIdentities`. -/
private lemma ker_inf_eq_bot_iff [Finite ρ] [Fintype N.complexes] [DecidableEq N.complexes] :
    N.deficiency = 0 ↔
      LinearMap.ker (Matrix.of fun i (c : N.complexes) => ((c : S → ℕ) i : ℝ)).mulVecLin ⊓
          Submodule.span ℝ (Set.range fun r =>
            (Pi.single (N.prodCx r) 1 - Pi.single (N.srcCx r) 1 : N.complexes → ℝ)) = ⊥ := by
  rw [← N.card_sub_card_sub_finrank_eq_zero_iff Subtype.val N.srcCx N.prodCx (fun _ => rfl)
    (fun _ => rfl) N.linkageGraph N.linkageGraph_adj_iff, deficiency, numLinkageClasses,
    Nat.card_eq_fintype_card]

/-- The vector `∑ α r (e_{prod r} - e_{src r})` in `Δ`. -/
private lemma mulVec_sum_single [Fintype ρ] [Fintype N.complexes] [DecidableEq N.complexes]
    (α : ρ → ℝ) :
    (Matrix.of fun i (c : N.complexes) => ((c : S → ℕ) i : ℝ)).mulVecLin
        (∑ r, α r • (Pi.single (N.prodCx r) 1 - Pi.single (N.srcCx r) 1)) =
      ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, map_sub]
  funext i
  simp [srcCx, prodCx]

private lemma sum_mul_sum_single [Fintype ρ] [Fintype N.complexes] [DecidableEq N.complexes]
    (α : ρ → ℝ) (η : (S → ℕ) → ℝ) :
    ∑ c : N.complexes, η c *
        (∑ r, α r • (Pi.single (N.prodCx r) 1 - Pi.single (N.srcCx r) 1 : N.complexes → ℝ)) c =
      ∑ r, α r * (η (N.prod r) - η (N.src r)) := by
  simp only [Finset.sum_apply, Finset.mul_sum, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, srcCx, prodCx, mul_comm]

/-- **Deficiency zero in linear form.** A network with finitely many reactions has deficiency
`δ = n - ℓ - s = 0` exactly when `ker Y ∩ im ∂ = 0`, written elementarily: every weighting
`α` of the reactions with zero net stoichiometric change `∑ α r (prod r - src r) = 0` has zero
net change `∑ α r (η (prod r) - η (src r)) = 0` against every function `η` on complexes. The
right-hand side is the hypothesis `hδ` of
`exists_pos_isComplexBalanced_of_deficiency_zero`; the equivalence is the rank identity
`dim im ∂ = n - ℓ` (`card_sub_card_sub_finrank_eq_zero_iff`).

Source: Feinberg (2019), Theorem 6.4.7. -/
theorem deficiency_eq_zero_iff [Fintype ρ] :
    N.deficiency = 0 ↔
      ∀ α : ρ → ℝ, ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) = 0 →
        ∀ η : (S → ℕ) → ℝ, ∑ r, α r * (η (N.prod r) - η (N.src r)) = 0 := by
  classical
  have := Fintype.ofFinite N.complexes
  rw [N.ker_inf_eq_bot_iff]
  constructor
  · intro hbot α hα η
    have hv : (∑ r, α r • (Pi.single (N.prodCx r) 1 - Pi.single (N.srcCx r) 1 :
        N.complexes → ℝ)) = 0 := by
      have hmem := Submodule.mem_inf.2
        ⟨LinearMap.mem_ker.2 ((N.mulVec_sum_single α).trans hα),
          Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ (α r)
            (Submodule.subset_span (Set.mem_range_self r))⟩
      rwa [hbot, Submodule.mem_bot] at hmem
    rw [← N.sum_mul_sum_single α η, hv]
    simp
  · intro h
    rw [eq_bot_iff]
    rintro v ⟨hvY, hvΔ⟩
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hvΔ
    rw [Submodule.mem_bot]
    funext c
    let η : (S → ℕ) → ℝ := fun y => if y = (c : S → ℕ) then 1 else 0
    have hα := (N.sum_mul_sum_single α η).trans
      (h α ((N.mulVec_sum_single α).symm.trans (LinearMap.mem_ker.1 hvY)) η)
    simp only [η] at hα
    rw [Fintype.sum_eq_single c fun c' hc' => by
      rw [ite_eq_right fun h => hc' (Subtype.ext h), zero_mul]] at hα
    simpa using hα

/-- **Horn–Feinberg: complex balancing for every choice of rate constants.** A weakly
reversible mass-action network of deficiency zero has, for any positive rate constants, a
positive complex-balanced equilibrium. Together with
`existsUnique_equilibrium_of_isComplexBalanced` this gives `existsUnique_equilibrium`.

Source: Horn (1972); Feinberg (1972); Feinberg (1987). -/
theorem exists_pos_isComplexBalanced [Fintype S] [Fintype ρ] (hδ : N.deficiency = 0)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ N.IsComplexBalanced k c :=
  N.exists_pos_isComplexBalanced_of_deficiency_zero (N.deficiency_eq_zero_iff.1 hδ) hwr hk

/-- **Deficiency-zero theorem, weakly reversible case.** A weakly reversible mass-action
network of deficiency zero has, for any positive rate constants, exactly one equilibrium in
each positive stoichiometric compatibility class.

Source: Horn (1972); Horn & Jackson (1972); Feinberg (1987). -/
theorem existsUnique_equilibrium [Fintype S] [Fintype ρ] (hδ : N.deficiency = 0)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    ∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0 :=
  N.existsUnique_equilibrium_of_deficiency_zero (N.deficiency_eq_zero_iff.1 hδ) hwr hk hx₀

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced

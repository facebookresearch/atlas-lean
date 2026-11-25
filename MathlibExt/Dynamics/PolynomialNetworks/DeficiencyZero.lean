/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
import MathlibExt.Combinatorics.EndpointMapMultigraph.OrientedIncidence

/-!
# The deficiency-zero theorem for networks without weak reversibility

`ReactionNetwork.not_exists_positive_equilibrium` rules out positive mass-action equilibria
in deficiency-zero networks that are not weakly reversible.
-/

@[expose] public section

open Finset Matrix
open EndpointMapMultigraph (orientedIncidence underlyingGraph)

namespace MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork

variable {S ρ : Type*} (N : ReactionNetwork S ρ)

private def srcComplex (r : ρ) : N.complexes := ⟨N.src r, Or.inl ⟨r, rfl⟩⟩

private def prodComplex (r : ρ) : N.complexes := ⟨N.prod r, Or.inr ⟨r, rfl⟩⟩

-- Loops contribute neither to adjacency nor to the vector field.
private theorem underlyingGraph_eq :
    underlyingGraph (fun r : {r // N.src r ≠ N.prod r} => N.prodComplex r)
      (fun r => N.srcComplex r) = N.linkageGraph := by
  ext c d
  rw [EndpointMapMultigraph.underlyingGraph_adj]
  simp only [linkageGraph, SimpleGraph.fromRel_adj, Reacts, ← exists_or]
  refine and_congr_right fun hcd => ⟨?_, ?_⟩
  · rintro ⟨⟨r, _⟩, ⟨hc, hd⟩ | ⟨hd, hc⟩⟩
    · exact ⟨r, Or.inr ⟨congrArg Subtype.val hd, congrArg Subtype.val hc⟩⟩
    · exact ⟨r, Or.inl ⟨congrArg Subtype.val hc, congrArg Subtype.val hd⟩⟩
  · have hval : c.val ≠ d.val := fun h => hcd (Subtype.ext h)
    rintro ⟨r, ⟨hc, hd⟩ | ⟨hd, hc⟩⟩
    · exact ⟨⟨r, by simpa [hc, hd] using hval⟩, Or.inr ⟨Subtype.ext hd, Subtype.ext hc⟩⟩
    · exact ⟨⟨r, by simpa [hc, hd] using hval.symm⟩, Or.inl ⟨Subtype.ext hc, Subtype.ext hd⟩⟩

/-- **Deficiency-zero theorem, non-weakly-reversible case.** A mass-action network of
deficiency zero that is not weakly reversible has no positive equilibrium for any positive
rate constants.

Source: Feinberg (1987). -/
theorem not_exists_positive_equilibrium [Fintype S] [Fintype ρ]
    (hδ : N.deficiency = 0) (hwr : ¬ N.IsWeaklyReversible)
    {k : ρ → ℝ} (hk : ∀ r, 0 < k r) :
    ¬ ∃ x : S → ℝ, (∀ s, 0 < x s) ∧ N.massActionField k x = 0 := by
  classical
  rintro ⟨x, hx, heq⟩
  let Q := {r // N.src r ≠ N.prod r}
  let : Fintype Q := inferInstanceAs (Fintype {r // N.src r ≠ N.prod r})
  let := Fintype.ofFinite N.complexes
  let B := orientedIncidence (fun r : Q => N.prodComplex r) (fun r => N.srcComplex r)
  let Y : Matrix S N.complexes ℝ := Matrix.of fun s c => (c.val s : ℝ)
  have hcol (s : S) (r : Q) : (Y * B) s r = (N.prod r s : ℝ) - N.src r s := by
    change (Y s ᵥ* B) r = _
    rw [EndpointMapMultigraph.vecMul_orientedIncidence_apply]
    rfl
  have hspan : Submodule.span ℝ (Set.range (Y * B).col) = N.stoichiometricSubspace := by
    unfold stoichiometricSubspace
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨r, rfl⟩
      exact Submodule.subset_span ⟨r.val, (funext fun s => hcol s r).symm⟩
    · rintro _ ⟨r, rfl⟩
      by_cases hr : N.src r = N.prod r
      · change (fun s => (N.prod r s : ℝ) - N.src r s) ∈ _
        have hzero : (fun s => (N.prod r s : ℝ) - N.src r s) = 0 := by
          ext s
          simp [hr]
        rw [hzero]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨r, hr⟩, funext fun s => hcol s ⟨r, hr⟩⟩
  -- Deficiency zero gives the same rank before and after applying the composition map.
  have hrank := EndpointMapMultigraph.rank_orientedIncidence_add_card_connectedComponent
    (fun r : Q => N.prodComplex r) (fun r => N.srcComplex r)
    (fun r h => r.property (congrArg Subtype.val h.symm))
  change B.rank + _ = _ at hrank
  rw [N.underlyingGraph_eq] at hrank
  have hYB : (Y * B).rank = B.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, hspan]
    rw [deficiency, numLinkageClasses, Nat.card_eq_fintype_card] at hδ
    omega
  have hker : LinearMap.ker B.mulVecLin = LinearMap.ker (Y * B).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Matrix.mulVecLin_mul]
      exact B.mulVecLin.ker_le_ker_comp Y.mulVecLin
    · have hB := B.mulVecLin.finrank_range_add_finrank_ker
      have hY := (Y * B).mulVecLin.finrank_range_add_finrank_ker
      change B.rank + _ = _ at hB
      change (Y * B).rank + _ = _ at hY
      omega
  let w (r : ρ) : ℝ := k r * ∏ s, x s ^ N.src r s
  let v : Q → ℝ := fun r => w r
  have hw (r : ρ) : 0 < w r := mul_pos (hk r) (prod_pos fun s _ => pow_pos (hx s) _)
  have hYv : (Y * B).mulVecLin v = 0 := by
    funext s
    change (∑ r : Q, (Y * B) s r * v r) = 0
    simp only [hcol, v]
    change (∑ r : {r // N.src r ≠ N.prod r}, ((N.prod r s : ℝ) - N.src r s) * w r) = 0
    rw [← subtype_univ,
      sum_subtype_eq_sum_filter (fun r : ρ => ((N.prod r s : ℝ) - N.src r s) * w r)]
    calc
      ∑ r ∈ univ.filter (fun r => N.src r ≠ N.prod r),
          ((N.prod r s : ℝ) - N.src r s) * w r =
          ∑ r, ((N.prod r s : ℝ) - N.src r s) * w r := by
        apply sum_subset (filter_subset _ _)
        intro r _ h
        have hr : N.src r = N.prod r := by simpa using h
        simp [hr]
      _ = 0 := by
        simpa only [massActionField, Pi.zero_apply, w, mul_comm] using congrFun heq s
  have hBv : B *ᵥ v = 0 := by
    change v ∈ LinearMap.ker B.mulVecLin
    rwa [hker, LinearMap.mem_ker]
  -- The indicator of the complexes reachable from the product detects any entering edge.
  apply hwr
  intro r
  by_contra hreturn
  have hr : N.src r ≠ N.prod r := fun h => hreturn (h ▸ .refl)
  let reaches := Relation.ReflTransGen N.Reacts (N.prod r)
  let η : N.complexes → ℝ := fun c => if reaches c.val then 1 else 0
  have hdiff (q : Q) : (η ᵥ* B) q =
      (if reaches (N.prod q) then 1 else 0) - (if reaches (N.src q) then 1 else 0) :=
    EndpointMapMultigraph.vecMul_orientedIncidence_apply _ _ η q
  have hnonneg (q : Q) : 0 ≤ (η ᵥ* B) q := by
    rw [hdiff]
    by_cases h : reaches (N.src q)
    · have h' : reaches (N.prod q) := h.tail ⟨q, rfl, rfl⟩
      simp [h, h']
    · simp [h]
      split <;> simp
  have hpos : 0 < (η ᵥ* B) (⟨r, hr⟩ : Q) := by
    have hprod : reaches (N.prod r) := .refl
    simp [hdiff, show ¬ reaches (N.src r) from hreturn, hprod]
  have hsum : 0 < (η ᵥ* B) ⬝ᵥ v :=
    sum_pos' (fun q _ => mul_nonneg (hnonneg q) (hw q).le)
      ⟨⟨r, hr⟩, mem_univ _, mul_pos hpos (hw r)⟩
  rw [← dotProduct_mulVec, hBv, dotProduct_zero] at hsum
  exact lt_irrefl _ hsum

end MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork

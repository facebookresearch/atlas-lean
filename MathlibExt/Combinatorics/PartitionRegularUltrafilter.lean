/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Partition regular families and ultrafilters

A family has a monochromatic member in every finite coloring exactly when some ultrafilter
consists of sets containing members of the family.
-/

open Filter

namespace MetaMathlibExt

/-- **Partition regular families and ultrafilters.** Let $\mathcal{F}$ be a family of subsets of a
set $S$. Every finite coloring of $S$ has a monochromatic member of $\mathcal{F}$ (that is,
$\mathcal{F}$ is weakly partition regular) if and only if there is an ultrafilter $U$ on $S$ such
that every $A \in U$ contains some member of $\mathcal{F}$ ($U$ is a PR-witness of $\mathcal{F}$).

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.1 (`integers-2025-A105-prop-3-1`), quoting
Hindman and Strauss, Theorem 5.7. -/
public theorem weaklyPartitionRegular_iff_exists_ultrafilter {S : Type*}
    (𝓕 : Set (Set S)) :
    (∀ (r : ℕ) (c : S → Fin r), ∃ F ∈ 𝓕, ∃ k : Fin r, ∀ x ∈ F, c x = k) ↔
      ∃ U : Ultrafilter S, ∀ A ∈ U, ∃ F ∈ 𝓕, F ⊆ A := by
  classical
  constructor
  · intro h
    -- The complements of sets containing no family member have the finite intersection property.
    let dual : Set (Set S) := {B | ¬ ∃ F ∈ 𝓕, F ⊆ Bᶜ}
    have hfinite (T : Finset (Set S)) (hT : (T : Set (Set S)) ⊆ dual) :
        (⋂₀ (T : Set (Set S))).Nonempty := by
      by_contra hempty
      -- Color each point by a set of T that misses it.
      have hmiss (x : S) : ∃ B : T, x ∉ (B : Set S) := by
        by_contra! hall
        exact hempty ⟨x, fun B hB => hall ⟨B, hB⟩⟩
      choose c hc using hmiss
      obtain ⟨F, hF, k, hk⟩ := h T.card (fun x => T.equivFin (c x))
      let B := T.equivFin.symm k
      apply hT B.property
      refine ⟨F, hF, fun x hx => ?_⟩
      have heq : c x = B := T.equivFin.eq_symm_apply.mpr (hk x hx)
      exact heq ▸ hc x
    obtain ⟨U, hU⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty dual hfinite
    refine ⟨U, fun A hA => ?_⟩
    by_contra hbad
    exact compl_notMem hA (hU (show Aᶜ ∈ dual by simpa [dual] using hbad))
  · rintro ⟨U, hU⟩ r c
    obtain ⟨k, hk⟩ : ∃ k, ∀ᶠ x in U, c x = k :=
      Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall fun x => ⟨c x, rfl⟩)
    obtain ⟨F, hF, hsub⟩ := hU {x | c x = k} hk
    exact ⟨F, hF, k, fun _ hx => hsub hx⟩

end MetaMathlibExt

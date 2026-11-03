/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Monotone.Basic
import Section_1_Introduction.A_EvolutionAlgebra
import Section_2_Preliminaries.A_Preliminaries

/-!
# Lemma 3.1 and Theorem 3.2: the greatest idempotent subspace

Paper Lemma `einfty_is_idempotent`: for a finite-dimensional evolution algebra,
`𝓔^(∞)` (the stabilized value of the derived series) is the greatest
idempotent subspace — it satisfies `(𝓔^(∞))² = 𝓔^(∞)`, and every subspace
`V` with `V² = V` sits inside it.

We define `𝓔^(∞)` as the infimum of the derived series
(`derivedSeriesInf`) and prove it is the stable value: in finite dimensions
the decreasing chain `𝓔⁽ᵏ⁾` must stabilize (`derivedSeries_stabilizes`),
since finranks strictly drop at every strict step.

(Definitions `IsIdempotentSubmodule` and `derivedSeriesInf` live in
`Preliminaries`.)

## Main results

* `EvolutionAlgebras.derivedSeries_stabilizes`: the derived series of a
  finite-dimensional algebra stabilizes after one step somewhere.
* `EvolutionAlgebras.derivedSeriesInf_eq_of_stabilizes`: the infimum
  equals any stable term.
* `EvolutionAlgebras.einfty_is_idempotent`: `𝓔^(∞)` is the greatest idempotent
  subspace.
* `EvolutionAlgebras.solvable_iff_no_idempotent_subspace`: paper Theorem
  `solvableiff` — solvable iff no nonzero idempotent subspace.
* `EvolutionAlgebras.solvable_iff_derivedSeriesInf_eq_bot`: paper Theorem
  `solvableiff`, conditions (1) ↔ (2) — solvable iff `𝓔^(∞) = ⊥`.
-/

namespace EvolutionAlgebras

universe u v

/- Hypotheses are organized so that every structure is provided exactly once:
`Field` supplies the scalar side (`CommSemiring`, `DivisionRing`), while
`NonUnitalNonAssocRing` — which extends both `AddCommGroup` and
`NonUnitalNonAssocSemiring` — supplies the additive side. This keeps
`Module K E` and `FiniteDimensional K E` unambiguous, and lets
`square` apply directly.
The general lemmas below take `Module K E` directly; Theorem 3.2 lives in
its own section where the module structure comes solely from
`NonUnitalNonAssocAlgebra K E`. -/
section GeneralLemmas
variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-- **Section 2.** The derived series is antitone (Section 2: `𝓔⁽ⁱ⁺¹⁾ ⊆ 𝓔⁽ⁱ⁾`). The starting
point for the stabilization argument below. -/
theorem derivedSeries_antitone : Antitone (derivedSeries K E) :=
  antitone_nat_of_succ_le (derivedSeries_succ_le K E)

/-- In finite dimensions the derived series stabilizes after one step
somewhere: some term is fixed by squaring (Section 2: the chain stabilizes at
some `l`). Ranks strictly drop at every strict step, so the rank sequence —
a decreasing sequence of naturals — stabilizes, and equal rank plus `≤`
gives equality of the subspaces. The stable index is used to identify
`𝓔^(∞)` and to show it is nontrivial when the algebra is not solvable. -/
theorem derivedSeries_stabilizes [FiniteDimensional K E] :
    ∃ l, derivedSeries K E (l + 1) = derivedSeries K E l := by
  classical
  have hanti := derivedSeries_antitone K E
  have hganti : Antitone (fun k => Module.finrank K (derivedSeries K E k)) := by
    intro m n hmn
    exact Submodule.finrank_mono (hanti hmn)
  have hstab : ∃ N, ∀ k, N ≤ k →
      Module.finrank K (derivedSeries K E k) =
        Module.finrank K (derivedSeries K E N) := by
    have hne : ∃ n, n ∈ Set.range
        (fun k => Module.finrank K (derivedSeries K E k)) := ⟨_, 0, rfl⟩
    obtain ⟨N, hN⟩ := Nat.find_spec hne
    refine ⟨N, fun k hNk => le_antisymm (hganti hNk) ?_⟩
    have hNeq : Module.finrank K (derivedSeries K E N) = Nat.find hne := hN
    rw [hNeq]
    exact Nat.find_min' hne (Set.mem_range_self k)
  obtain ⟨N, hN⟩ := hstab
  exact ⟨N, Submodule.eq_of_le_of_finrank_eq
    (derivedSeries_succ_le K E N) (hN (N + 1) (Nat.le_succ N))⟩

/-- **Helper.** The infimum equals any stable term: if `𝓔⁽ˡ⁺¹⁾ = 𝓔⁽ˡ⁾` then
`𝓔^(∞) = 𝓔⁽ˡ⁾` (no finite-dimensionality needed). This identifies the Lean
definition `derivedSeriesInf` with the paper's stabilized value `𝓔^(∞)`,
and is used for both the greatest-idempotent-subspace lemma and the
corollary. -/
theorem derivedSeriesInf_eq_of_stabilizes {l : ℕ}
    (hl : derivedSeries K E (l + 1) = derivedSeries K E l) :
    derivedSeriesInf K E = derivedSeries K E l := by
  have hanti := derivedSeries_antitone K E
  have hstable : ∀ k, l ≤ k → derivedSeries K E k = derivedSeries K E l := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hle ih =>
      calc derivedSeries K E (k + 1)
          = square K E (derivedSeries K E k) := derivedSeries_succ K E k
        _ = square K E (derivedSeries K E l) := by rw [ih]
        _ = derivedSeries K E (l + 1) := (derivedSeries_succ K E l).symm
        _ = derivedSeries K E l := hl
  apply le_antisymm
  · exact iInf_le _ l
  · unfold derivedSeriesInf
    apply le_iInf
    intro k
    obtain h | h := le_total k l
    · exact hanti h
    · rw [hstable k h]

end GeneralLemmas

section MainResults
variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E]

/-- **Paper Lemma 3.1.** Paper Lemma `einftyisidempotent`: for a finite-dimensional
evolution algebra, `𝓔^(∞)` is the greatest idempotent subspace. The engine
behind the solvable characterization; it also supplies the witness subspace
for the corollary. (The proof uses only the general lemmas above, but the
statement matches the paper.) -/
theorem einfty_is_idempotent [NonUnitalNonAssocAlgebra K E]
    [EvolutionAlgebra K E] [FiniteDimensional K E] :
    square K E (derivedSeriesInf K E) = derivedSeriesInf K E ∧
      ∀ V : Submodule K E, square K E V = V → V ≤ derivedSeriesInf K E := by
  have hmax : ∀ V : Submodule K E,
      square K E V = V → V ≤ derivedSeriesInf K E := by
    intro V hV
    unfold derivedSeriesInf
    apply le_iInf
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero K E]
      exact le_top
    | succ k ih =>
      calc V = square K E V := hV.symm
        _ ≤ square K E (derivedSeries K E k) := square_mono K E ih
        _ = derivedSeries K E (k + 1) := (derivedSeries_succ K E k).symm
  obtain ⟨l, hl⟩ := derivedSeries_stabilizes K E
  have hinf : derivedSeriesInf K E = derivedSeries K E l :=
    derivedSeriesInf_eq_of_stabilizes K E hl
  refine ⟨?_, hmax⟩
  rw [hinf, ← derivedSeries_succ K E l]
  exact hl

/-- **Paper Theorem 3.2.** Paper Theorem `solvableiff`: a finite-dimensional algebra is solvable if
and only if every idempotent subspace is `⊥` (i.e. there is no nontrivial,
nonzero, idempotent subspace). Both directions go through the lemma above:
`𝓔^(∞)` is idempotent, and every idempotent subspace sits inside it. -/
theorem solvable_iff_no_idempotent_subspace [NonUnitalNonAssocAlgebra K E]
    [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔
      ∀ V : Submodule K E, IsIdempotentSubmodule K E V → V = ⊥ := by
  constructor
  · -- Solvable implies every idempotent subspace is `⊥`.
    intro hsol
    obtain ⟨k, hk⟩ := hsol.solvable
    intro V hV
    have hle : V ≤ derivedSeriesInf K E :=
      (einfty_is_idempotent K E).2 V hV
    have hinf : derivedSeriesInf K E ≤ derivedSeries K E k := iInf_le _ k
    rw [hk] at hinf
    exact le_antisymm (le_trans hle hinf) bot_le
  · -- No nontrivial idempotent subspace implies solvable: `𝓔^(∞)` itself
    -- is idempotent, hence `⊥`, and it equals a stable term.
    intro h
    have hidem := (einfty_is_idempotent K E).1
    have hInfBot : derivedSeriesInf K E = ⊥ := h _ hidem
    obtain ⟨l, hl⟩ := derivedSeries_stabilizes K E
    have hinf : derivedSeriesInf K E = derivedSeries K E l :=
      derivedSeriesInf_eq_of_stabilizes K E hl
    have hbot : derivedSeries K E l = ⊥ := by
      rw [← hinf]
      exact hInfBot
    exact IsSolvable.mk K E hbot

/-- Conditions (1) ↔ (2) of paper Theorem `solvableiff`:
solvability is equivalent to `𝓔^(∞) = ⊥`. The definitional half of the
three-way equivalence (the `(1) ↔ (3)` half is `solvable_iff_no_idempotent_subspace`
above). -/
theorem solvable_iff_derivedSeriesInf_eq_bot [NonUnitalNonAssocAlgebra K E]
    [EvolutionAlgebra K E] [FiniteDimensional K E] :
    IsSolvable K E ↔ derivedSeriesInf K E = ⊥ := by
  constructor
  · intro hsol
    obtain ⟨k, hk⟩ := hsol.solvable
    have hle : derivedSeriesInf K E ≤ derivedSeries K E k := iInf_le _ k
    rw [hk] at hle
    exact le_antisymm hle bot_le
  · intro hbot
    obtain ⟨l, hl⟩ := derivedSeries_stabilizes K E
    have hinf : derivedSeriesInf K E = derivedSeries K E l :=
      derivedSeriesInf_eq_of_stabilizes K E hl
    have hterm : derivedSeries K E l = ⊥ := by
      rw [← hinf]
      exact hbot
    exact IsSolvable.mk K E hterm

end MainResults

end EvolutionAlgebras

/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length

/-!
# Length framework for the Koszul/Hilbert–Samuel step (sub-plan M4c-i)

Thin verified wrappers bundling Mathlib's `Module.length` API into the exact
application shapes step M4c-ii (Hilbert–Samuel) needs. No Hilbert theory is
developed here: every lemma below is a direct transport of a Mathlib fact
(`Module.length_eq_add_of_exact`, `Module.length_eq_rank` /
`Module.length_eq_finrank`, `Module.length_ne_top_iff`, the `IsFiniteLength`
API) into submodule/quotient/finrank/`ℕ`-valued form.

## Sections

* (§1) SES additivity in submodule shape: `length_add_of_submodule`,
  the two-step tower `length_add_of_le`, the simple-quotient step
  `length_add_of_simple_quot`, the `ℕ`-coerced `length_nat_add_of_submodule`,
  and the monotonicity wrappers `length_submodule_le` / `length_quot_le`.
* (§2) Finite-length API: `isFiniteLength_iff_length_ne_top`, the
  Noetherian+Artinian constructors, and stability under submodules and
  quotients (`isFiniteLength_submodule`, `isFiniteLength_quotient`).
* (§3) Field bridge (length ↔ dimension): `length_eq_coe_finrank`,
  `length_eq_coe_rank`, `length_ne_top_of_finite`,
  `finrank_eq_untop₀_length`.
* (§4) `ℕ`-valued finite length `finLength` for the Hilbert–Samuel
  computation: `coe_finLength`, `finLength_add_of_submodule`,
  `finLength_tower`, `finLength_add_of_simple_quot`,
  `finLength_eq_finrank`, `finLength_zero_of_subsingleton`.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/Length.lean`: `Module.length`, `Module.length_eq_add_of_exact`,
  `Module.length_le_of_injective/surjective`, `Module.length_eq_rank`,
  `Module.length_eq_finrank`, `Module.length_ne_top_iff`,
  `Module.length_ne_top`, `Module.length_eq_one`, `Module.length_eq_zero`,
  `LinearEquiv.length_eq`.
* `RingTheory/FiniteLength.lean`: `IsFiniteLength`,
  `isFiniteLength_iff_isNoetherian_isArtinian`,
  `IsFiniteLength.of_injective/of_surjective`.
* `Algebra/Exact/Basic.lean`: `LinearMap.exact_subtype_mkQ`.
* `Algebra/Order/WithTop/Untop0.lean`: `WithTop.untop₀` API
  (`untop₀_add`, `untop₀_coe`, `coe_untop₀_of_ne_top`, `untop₀_one`,
  `untop₀_zero`).
* `Algebra/Module/Submodule/Map.lean`: `Submodule.comapSubtypeEquivOfLe`.

Project (read-only):
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): the graded ring whose
  Hilbert–Samuel theory M4c-ii builds on this framework).

## Status

All declarations below are unconditional (direct Mathlib transports).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LengthFramework

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-! ## §1. SES additivity in submodule shape -/

/-- Length is additive over a submodule and its quotient: the submodule-shaped
specialization of `Module.length_eq_add_of_exact` to
`0 → N → M → M ⧸ N → 0`.
-/
theorem length_add_of_submodule (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.subtype_injective N)
    (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)

/-- Two-step tower additivity: for `N ≤ P`, the length of `P` is the length of
`N` plus the length of the relative quotient. This is the single rung M4c-ii
iterates along the `I`-adic filtration.
-/
theorem length_add_of_le (N P : Submodule R M) (h : N ≤ P) :
    Module.length R P =
      Module.length R N + Module.length R (↥P ⧸ N.comap P.subtype) := by
  have h1 := length_add_of_submodule (N.comap P.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).length_eq] at h1
  exact h1

/-- Extension by a simple module adds one: the composition-factor step.
-/
theorem length_add_of_simple_quot (N : Submodule R M)
    [IsSimpleModule R (M ⧸ N)] :
    Module.length R M = Module.length R N + 1 := by
  have h1 : Module.length R (M ⧸ N) = 1 := Module.length_eq_one R (M ⧸ N)
  rw [length_add_of_submodule N, h1]

/-- `ℕ`-coerced additivity: if both sides are known naturals, so is the total.
-/
theorem length_nat_add_of_submodule (N : Submodule R M) (n p : ℕ)
    (hn : Module.length R N = n) (hp : Module.length R (M ⧸ N) = p) :
    Module.length R M = ↑(n + p) := by
  rw [length_add_of_submodule N, hn, hp, Nat.cast_add]

/-- Length is monotone in submodules.
-/
theorem length_submodule_le (N : Submodule R M) :
    Module.length R N ≤ Module.length R M :=
  Module.length_le_of_injective N.subtype (Submodule.subtype_injective N)

/-- Length drops under quotients.
-/
theorem length_quot_le (N : Submodule R M) :
    Module.length R (M ⧸ N) ≤ Module.length R M :=
  Module.length_le_of_surjective N.mkQ (Submodule.mkQ_surjective N)

/-! ## §2. Finite-length API -/

/-- Finite length unfolds to length `≠ ⊤` (symmetric form of
`Module.length_ne_top_iff`).
-/
theorem isFiniteLength_iff_length_ne_top :
    IsFiniteLength R M ↔ Module.length R M ≠ ⊤ :=
  Module.length_ne_top_iff.symm

/-- Noetherian + Artinian implies finite length.
-/
theorem isFiniteLength_of_isNoetherian_isArtinian [IsNoetherian R M]
    [IsArtinian R M] : IsFiniteLength R M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- Finite length passes to submodules.
-/
theorem isFiniteLength_submodule (hM : IsFiniteLength R M) (N : Submodule R M) :
    IsFiniteLength R N :=
  hM.of_injective (Submodule.subtype_injective N)

/-- Finite length passes to quotients.
-/
theorem isFiniteLength_quotient (hM : IsFiniteLength R M) (N : Submodule R M) :
    IsFiniteLength R (M ⧸ N) :=
  hM.of_surjective (Submodule.mkQ_surjective N)

/-! ## §3. Field bridge (length ↔ dimension) -/

/-- Over a division ring, length is the finrank (explicit-coercion form of
`Module.length_eq_finrank`).
-/
theorem length_eq_coe_finrank (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] :
    Module.length K V = ↑(Module.finrank K V) :=
  Module.length_eq_finrank K V

/-- Over a division ring, length is the rank (explicit form of
`Module.length_eq_rank`).
-/
theorem length_eq_coe_rank (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] : Module.length K V = (Module.rank K V).toENat :=
  Module.length_eq_rank K V

/-- A finite-dimensional vector space has length `≠ ⊤`.
-/
theorem length_ne_top_of_finite (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] : Module.length K V ≠ ⊤ := by
  rw [length_eq_coe_finrank]
  exact WithTop.ne_top_iff_exists.mpr ⟨_, rfl⟩

/-- Finrank recovered from length via `untop₀`.
-/
theorem finrank_eq_untop₀_length (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] :
    Module.finrank K V = (Module.length K V).untop₀ := by
  rw [length_eq_coe_finrank]
  exact (WithTop.untop₀_coe _).symm

/-! ## §4. `ℕ`-valued finite length -/

/-- The `ℕ`-valued finite length: `untop₀` of `Module.length`. On modules of
finite length this is the true length (`coe_finLength`); on infinite-length
modules it is junk (`0`), so every consumer below takes an `IsFiniteLength`
hypothesis.
-/
noncomputable def finLength (R : Type*) (M : Type*) [Ring R] [AddCommGroup M]
    [Module R M] : ℕ :=
  (Module.length R M).untop₀

/-- On finite-length modules, `finLength` coerces back to `Module.length`.
-/
theorem coe_finLength (hM : IsFiniteLength R M) :
    ↑(finLength R M) = Module.length R M :=
  WithTop.coe_untop₀_of_ne_top (Module.length_ne_top_iff.mpr hM)

/-- `ℕ`-valued SES additivity over a submodule and its quotient.
-/
theorem finLength_add_of_submodule (hM : IsFiniteLength R M)
    (N : Submodule R M) :
    finLength R M = finLength R N + finLength R (M ⧸ N) := by
  have hN : Module.length R N ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_injective (Submodule.subtype_injective N))
  have hQ : Module.length R (M ⧸ N) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_surjective (Submodule.mkQ_surjective N))
  have hadd := WithTop.untop₀_add hN hQ
  unfold finLength
  rw [length_add_of_submodule N]
  exact hadd

/-- `ℕ`-valued two-step tower additivity.
-/
theorem finLength_tower (N P : Submodule R M) (h : N ≤ P)
    (hP : IsFiniteLength R P) :
    finLength R P =
      finLength R N + finLength R (↥P ⧸ N.comap P.subtype) := by
  have h1 := finLength_add_of_submodule hP (N.comap P.subtype)
  rw [show finLength R ↥(N.comap P.subtype) = finLength R N from ?_] at h1
  · exact h1
  · unfold finLength
    rw [(Submodule.comapSubtypeEquivOfLe h).length_eq]

/-- `ℕ`-valued extension by a simple module adds one.
-/
theorem finLength_add_of_simple_quot (N : Submodule R M)
    [IsSimpleModule R (M ⧸ N)] (hM : IsFiniteLength R M) :
    finLength R M = finLength R N + 1 := by
  have h1 : finLength R (M ⧸ N) = 1 := by
    unfold finLength
    rw [Module.length_eq_one]
    exact WithTop.untop₀_one
  rw [finLength_add_of_submodule hM N, h1]

/-- `ℕ`-valued length of a finite-dimensional vector space is the finrank.
-/
theorem finLength_eq_finrank (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] : finLength K V = Module.finrank K V := by
  unfold finLength
  rw [length_eq_coe_finrank]
  exact WithTop.untop₀_coe _

/-- `ℕ`-valued length of a subsingleton module is zero.
-/
theorem finLength_zero_of_subsingleton [Subsingleton M] : finLength R M = 0 := by
  unfold finLength
  rw [Module.length_eq_zero]
  exact WithTop.untop₀_zero

#print axioms length_add_of_submodule
#print axioms finLength_add_of_submodule
#print axioms finLength_eq_finrank

end LengthFramework
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

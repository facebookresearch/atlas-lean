/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ResidualWiring
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceStep
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.TriangularRegularity
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Per-rung regularity inputs for `hres2`
This file proves the per-rung `IsSMulRegular` inputs that the
`hres2` wiring (`BridgeToFixedPoint.ResidualWiring`) consumes, in the exact
binder shape of its `hreg` `∀`-form
(`ResidualWiring.lean`, quotient by `Ideal.ofList` of the taken prefix list):

* (§1, unconditional) `hreg_rung0`: rung `j.val = 0` for every `(n, c)`,
  via (t1) (`Triangular.mkSystem_isSMulRegular`) transported across
  `R ⧸ ⊥` (`isSMulRegular_quot_bot_of_regular`).
* (§2, conditional-exact on `[hprime0, hndvd1, hdich]`) `hreg_rung1`:
  rung `j.val = 1` from the t2a/t2b dichotomy at the `mkSystem`
  instantiation (`isSMulRegular_mkSystem_mod_of_not_dvd`,
  `Triangular.mkSystem_isSMulRegular_mod_of_dvd`), repackaged from the
  `Ideal.ofList`-prefix quotient via `ofList_take_eq_span_image`.
* (§3) `hreg_of_hreg_ge1` + `hres2_of_hreg_ge1_of_noEmbedded_minAvoid` +
  `fixedPoint_of_idempotent_of_rung1plus`: the `hreg` `∀`-form narrowed to
  rungs `1 ≤ j.val`, wired into the `ResidualWiring` consumers
  (`hres2_of_rungRegular_of_noEmbedded_minAvoid`,
  `fixedPoint_of_idempotent_of_rungRegular`).
* (§4, false with witness) `hreg_forall_false`: the full `hreg` `∀`-form
  over all `(n, c)` is refuted at `n = 2`, `j = 1` by `badConsts`
  (`F₀ = X₀²`, `F₁ = X₀X₁`): `G₀ = x₀(x₀−z)`, `G₁ = x₁(x₀−z)`, so
  `x₀·G₁ = x₁·G₀ ∈ (G₀)` while `x₀ ∉ (G₀)` (else `1 ∈ (x₀−z)`,
  contradicted by evaluation at the origin). The witness needs the
  off-diagonal constant `c 0 1 1 = 1`, so it is not an evolution-algebra
  family (whose `Fₖ` are diagonal `∑ᵢ c i i k xᵢ²`); a diagonal-`c`
  narrowing of the rung-`≥ 1` inputs is the scoped follow-up. Rungs `≥ 2`
  stay residual regardless (the (t3) obstruction in `TriangularRegularity`).

Status: `hreg_rung0` unconditional; `hreg_rung1_of_dichotomy`
conditional-exact on `[hprime0, hndvd1, hdich]`; the full `hreg` `∀`-form
false (witness `badConsts` at `n = 2`).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint.ResidualWiring`, `Hres2`, `hres2_of_rungRegular_of_noEmbedded_minAvoid`,
  `fixedPoint_of_idempotent_of_rungRegular` (consumed §3 targets).
* `BridgeToFixedPoint.FixedPointFromBezout`, `bridgeSystem`, `bridgeForms`,
  `shiftConsts`, `shiftEquiv`, `statementIndex`, `mkQuadForm`.
* `Regularity.Avoid.TriangularRegularity`, `mkSystem_isSMulRegular` (t1),
  `mkSystem_isSMulRegular_mod_of_dvd` (t2b carried back).
* `Regularity.Avoid.AvoidanceApply`, `isSMulRegular_quot_bot_of_regular`,
  `isSMulRegular_mkSystem_mod_of_not_dvd` (t2a carried back),
  `ofList_take_eq_span_image`, `hsucc_of_step_outputs`.
* `Regularity.Avoid.AvoidanceStep`, `quot_mk_smul`.
* `Dimension.RegularSequenceDimDrop`, `span_smul_top`.
* `Regularity.Avoid.RegularityBridge`, `SuccessiveSMulRegular`.

Mathlib:

* `Ideal.ofList_nil`, `Ideal.ofList_singleton`
  (`Mathlib/RingTheory/Regular/RegularSequence.lean`).
* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/Algebra/GroupWithZero/Action/Regular.lean`).
* `MvPolynomial.X_ne_zero`
  (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
* `MvPolynomial.rename_X` (`Mathlib/Algebra/MvPolynomial/Rename.lean`);
  `MvPolynomial.eval_X` (`Mathlib/Algebra/MvPolynomial/Eval.lean`).
* `Fin.sum_univ_two` (`Mathlib/Algebra/BigOperators/Fin.lean`).
* `Ideal.Quotient.eq_zero_iff_mem`
  (`Mathlib/RingTheory/Ideal/Quotient/Defs.lean`);
  `Ideal.mem_span_singleton`, `Ideal.subset_span`
  (`Mathlib/RingTheory/Ideal/Span.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungRegular

open scoped BigOperators

/-! ## §1 Rung 0, unconditional (t1 transport) -/

/-- Rung 0 of the `hres2` `hreg` `∀`-form, unconditional: for `j.val = 0`
the prefix quotient is `R ⧸ ⊥`, so (t1) regularity on the domain
transports via `isSMulRegular_quot_bot_of_regular`. Exact
`ResidualWiring.lean` binder shape. -/
theorem hreg_rung0 (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have hbot : ((⊥ : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K)) : Submodule _ _) =
        ((⊥ : Ideal _) : Submodule _ _) := by
    rw [← Ideal.span_empty]
    exact RegularSequenceDimDrop.span_smul_top _
  rw [hj, List.take_zero, Ideal.ofList_nil, hbot]
  exact AvoidanceApply.isSMulRegular_quot_bot_of_regular (statementIndex n) K _
    (Triangular.mkSystem_isSMulRegular (statementIndex n) K
      (bridgeForms n K c hn) j)

/-! ## §2 Rung 1 from the t2a/t2b dichotomy -/

/-- Rung 1 of the `hres2` `hreg` `∀`-form, conditional-exact on
`[hprime0, hndvd1, hdich]`: for `j.val = 1` the prefix quotient is
`R ⧸ span{G ⟨0, _⟩}` (via `ofList_take_eq_span_image`), so the carried-back
t2a/t2b dichotomy at the `mkSystem` instantiation applies. The `X j ≠ 0`
conjunct of the t2a branch is closed by `X_ne_zero`, leaving the
non-divisibility half as `hdich`'s left disjunct. -/
theorem hreg_rung1_of_dichotomy (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1)
    (hprime0 : Prime (MvPolynomial.X
      (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ : Fin (statementIndex n + 1)) :
      MvPolynomial (Fin (statementIndex n + 1)) K))
    (hndvd1 : ¬ (MvPolynomial.X
      (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ : Fin (statementIndex n + 1)) :
      MvPolynomial (Fin (statementIndex n + 1)) K) ∣ MvPolynomial.X j)
    (hdich : (¬ (MvPolynomial.X
          (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ : Fin (statementIndex n + 1)) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
          MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ * L0 ∧
        MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
          Fin (statementIndex n + 1)) * bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn
            ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0)) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have htake :=
    AvoidanceApply.ofList_take_eq_span_image (bridgeSystem n K c hn) j
  rw [hj] at htake ⊢
  have himage : Set.image (bridgeSystem n K c hn)
      {k : Fin (statementIndex n + 1) | k.val < 1} =
      {(bridgeSystem n K c hn) ⟨0, Nat.zero_lt_succ (statementIndex n)⟩} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk0 : k.val = 0 := by omega
      have ek : k = ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ := Fin.ext hk0
      rw [ek]
    · intro hy
      refine ⟨⟨0, Nat.zero_lt_succ (statementIndex n)⟩, ?_, hy.symm⟩
      show ((⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
        Fin (statementIndex n + 1)).val) < 1
      have hv0 : ((⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
        Fin (statementIndex n + 1)).val) = 0 := rfl
      omega
  rw [htake, himage, RegularSequenceDimDrop.span_smul_top]
  rcases hdich with hndvd0 | ⟨L0, hF0, hM⟩
  · exact AvoidanceApply.isSMulRegular_mkSystem_mod_of_not_dvd (statementIndex n)
      K (bridgeForms n K c hn) _ j hprime0 hndvd0 (by simp) hndvd1
  · exact Triangular.mkSystem_isSMulRegular_mod_of_dvd (statementIndex n) K
      (bridgeForms n K c hn) _ j L0 hF0 hM hprime0 hndvd1

/-! ## §3 Narrowed wiring into the `ResidualWiring` consumers -/

/-- The full `hreg` `∀`-form from rung-`≥ 1` data: rung 0 is `hreg_rung0`. -/
theorem hreg_of_hreg_ge1 (K : Type*) [Field K]
    (hreg1 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), 1 ≤ j.val → IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  intro n hn c j
  by_cases hj : j.val = 0
  · exact hreg_rung0 K n hn c j hj
  · exact hreg1 n hn c j (by omega)

/-- `hres2` from rung-`≥ 1` regularity + unmixedness + minimal avoidance:
the `ResidualWiring` wiring lemma with rung 0 discharged by `hreg_rung0`.

bookkeeping: one dead antecedent (`hmin`, explained below); `hreg1`
(the `∀(n, c, j ≥ 1)` form) is live — `RungRegular.hreg_forall_false`
(below) refutes only the unsided `∀(n, c, j)` form at `n = 2`,
`j = 1` (the derivation needs the `j = 0` case).
`hmin` (the `∀c` minimal-avoidance form is false:
`ResidualWiring.not_forall_secFormAvoidsMinimal_bridgeForms`,
`ResidualWiring.lean`, via `c = 0`). -/
theorem hres2_of_hreg_ge1_of_noEmbedded_minAvoid (K : Type*) [Field K]
    (hreg1 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), 1 ≤ j.val → IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.ConeNoEmbedded (statementIndex n) K (bridgeForms n K c hn))
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
        (bridgeForms n K c hn)) :
    ResidualWiring.Hres2 K :=
  ResidualWiring.hres2_of_rungRegular_of_noEmbedded_minAvoid K
    (hreg_of_hreg_ge1 K hreg1) hunmixed hmin

/-- End-to-end fixed point from rung-`≥ 1` regularity + unmixedness +
minimal avoidance, via the `ResidualWiring` end-to-end wiring.

bookkeeping: one dead antecedent (`hmin`, explained below); `hreg1`
(the `∀(n, c, j ≥ 1)` form) is live — `RungRegular.hreg_forall_false`
(below) refutes only the unsided `∀(n, c, j)` form at `n = 2`,
`j = 1` (the derivation needs the `j = 0` case).
`hmin` (the `∀c` minimal-avoidance form is false:
`ResidualWiring.not_forall_secFormAvoidsMinimal_bridgeForms`,
`ResidualWiring.lean`, via `c = 0`). -/
theorem fixedPoint_of_idempotent_of_rung1plus (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hreg1 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), 1 ≤ j.val → IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.ConeNoEmbedded (statementIndex n) K (bridgeForms n K c hn))
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
        (bridgeForms n K c hn)) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x :=
  ResidualWiring.fixedPoint_of_idempotent_of_rungRegular K E V hfin hV hN hneV
    htower hcomm (hreg_of_hreg_ge1 K hreg1) hunmixed hmin

/-! ## §4 The full `hreg` `∀`-form is false (witness at `n = 2`)

`badConsts` has `F₀ = X₀²`, `F₁ = X₀X₁`, hence `G₀ = x₀(x₀−z)` and
`G₁ = x₁(x₀−z)`: `x₀·G₁ = x₁·G₀ ∈ (G₀)` while `x₀ ∉ (G₀)`, so `G₁` is a
zerodivisor mod `(G₀)` and rung-1 regularity fails. The witness needs the
off-diagonal `c 0 1 1 = 1`, hence is not an evolution-algebra family. -/

/-- Refutation witness: `F₀ = X₀²` (`c 0 0 0 = 1`), `F₁ = X₀X₁`
(`c 0 1 1 = 1`), all else `0`. Off-diagonal, hence not evolution-algebra. -/
def badConsts (K : Type*) [Field K] : Fin 2 → Fin 2 → Fin 2 → K :=
  fun a b d =>
    (if a.val = 0 ∧ b.val = 0 ∧ d.val = 0 then 1 else 0) +
    (if a.val = 0 ∧ b.val = 1 ∧ d.val = 1 then 1 else 0)

/-- Rung-0 equation index at `n = 2` (abbrev so rewrites match). -/
abbrev badI0 : Fin (statementIndex 2 + 1) := ⟨0, by decide⟩

/-- Rung-1 equation index at `n = 2` (abbrev so rewrites match). -/
abbrev badI1 : Fin (statementIndex 2 + 1) := ⟨1, by decide⟩

/-- The `x₀` variable in `MvPolynomial (Fin (statementIndex 2 + 2)) K`. -/
noncomputable abbrev badX0 (K : Type*) [Field K] :
    MvPolynomial (Fin (statementIndex 2 + 2)) K :=
  MvPolynomial.X (Fin.castSucc badI0)

/-- The `x₁` variable in `MvPolynomial (Fin (statementIndex 2 + 2)) K`. -/
noncomputable abbrev badX1 (K : Type*) [Field K] :
    MvPolynomial (Fin (statementIndex 2 + 2)) K :=
  MvPolynomial.X (Fin.castSucc badI1)

/-- The `z` variable in `MvPolynomial (Fin (statementIndex 2 + 2)) K`. -/
noncomputable abbrev badZ (K : Type*) [Field K] :
    MvPolynomial (Fin (statementIndex 2 + 2)) K :=
  MvPolynomial.X (Fin.last (statementIndex 2 + 1))

/-- The shift equivalence fixes `0 : Fin 2` (stated at `Fin 2` so rewrites
match syntactically after the `show`-defeq crossing). -/
theorem shiftEquiv_two_zero (hn2 : 0 < 2) :
    shiftEquiv 2 hn2 (0 : Fin 2) = (0 : Fin 2) := Fin.ext rfl

/-- The shift equivalence fixes `1 : Fin 2`. -/
theorem shiftEquiv_two_one (hn2 : 0 < 2) :
    shiftEquiv 2 hn2 (1 : Fin 2) = (1 : Fin 2) := Fin.ext rfl

/-- At the witness, `F₀ = X₀²`: only the `(0, 0)` summand survives. The
`change` crosses the `Fin (statementIndex 2 + 1)`/`Fin 2` defeq gap so that
`Fin.sum_univ_two` applies syntactically. -/
theorem bridgeForms_two_zero (K : Type*) [Field K] (hn2 : 0 < 2) :
    bridgeForms 2 K (badConsts K) hn2 badI0 =
      MvPolynomial.X badI0 * MvPolynomial.X badI0 := by
  change (∑ i : Fin 2, ∑ j : Fin 2, MvPolynomial.C
      (badConsts K (shiftEquiv 2 hn2 i) (shiftEquiv 2 hn2 j)
        (shiftEquiv 2 hn2 (0 : Fin 2))) *
        (MvPolynomial.X i * MvPolynomial.X j)) =
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (0 : Fin 2)
  have c000 : badConsts K (shiftEquiv 2 hn2 (0 : Fin 2))
      (shiftEquiv 2 hn2 (0 : Fin 2)) (shiftEquiv 2 hn2 (0 : Fin 2)) = 1 := by
    rw [shiftEquiv_two_zero]
    simp [badConsts]
  have c010 : badConsts K (shiftEquiv 2 hn2 (0 : Fin 2))
      (shiftEquiv 2 hn2 (1 : Fin 2)) (shiftEquiv 2 hn2 (0 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  have c100 : badConsts K (shiftEquiv 2 hn2 (1 : Fin 2))
      (shiftEquiv 2 hn2 (0 : Fin 2)) (shiftEquiv 2 hn2 (0 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  have c110 : badConsts K (shiftEquiv 2 hn2 (1 : Fin 2))
      (shiftEquiv 2 hn2 (1 : Fin 2)) (shiftEquiv 2 hn2 (0 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  simp only [Fin.sum_univ_two]
  rw [c000, c010, c100, c110]
  simp only [map_one, one_mul, map_zero, zero_mul, add_zero]
  rfl

/-- At the witness, `F₁ = X₀X₁`: only the `(0, 1)` summand survives. -/
theorem bridgeForms_two_one (K : Type*) [Field K] (hn2 : 0 < 2) :
    bridgeForms 2 K (badConsts K) hn2 badI1 =
      MvPolynomial.X badI0 * MvPolynomial.X badI1 := by
  change (∑ i : Fin 2, ∑ j : Fin 2, MvPolynomial.C
      (badConsts K (shiftEquiv 2 hn2 i) (shiftEquiv 2 hn2 j)
        (shiftEquiv 2 hn2 (1 : Fin 2))) *
        (MvPolynomial.X i * MvPolynomial.X j)) =
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
  have c001 : badConsts K (shiftEquiv 2 hn2 (0 : Fin 2))
      (shiftEquiv 2 hn2 (0 : Fin 2)) (shiftEquiv 2 hn2 (1 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  have c011 : badConsts K (shiftEquiv 2 hn2 (0 : Fin 2))
      (shiftEquiv 2 hn2 (1 : Fin 2)) (shiftEquiv 2 hn2 (1 : Fin 2)) = 1 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  have c101 : badConsts K (shiftEquiv 2 hn2 (1 : Fin 2))
      (shiftEquiv 2 hn2 (0 : Fin 2)) (shiftEquiv 2 hn2 (1 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_zero, shiftEquiv_two_one]
    simp [badConsts]
  have c111 : badConsts K (shiftEquiv 2 hn2 (1 : Fin 2))
      (shiftEquiv 2 hn2 (1 : Fin 2)) (shiftEquiv 2 hn2 (1 : Fin 2)) = 0 := by
    rw [shiftEquiv_two_one]
    simp [badConsts]
  simp only [Fin.sum_univ_two]
  rw [c001, c011, c101, c111]
  simp only [map_one, one_mul, map_zero, zero_mul, add_zero, zero_add]
  rfl

/-- At the witness, `G₀ = x₀(x₀−z)`. -/
theorem bridgeSystem_two_zero (K : Type*) [Field K] (hn2 : 0 < 2) :
    (bridgeSystem 2 K (badConsts K) hn2) badI0 =
      badX0 K * (badX0 K - badZ K) := by
  have hF := bridgeForms_two_zero K hn2
  simp only [bridgeSystem, mkSystem, badX0, badZ]
  rw [hF, map_mul]
  simp only [MvPolynomial.rename_X]
  ring

/-- At the witness, `G₁ = x₁(x₀−z)`. -/
theorem bridgeSystem_two_one (K : Type*) [Field K] (hn2 : 0 < 2) :
    (bridgeSystem 2 K (badConsts K) hn2) badI1 =
      badX1 K * (badX0 K - badZ K) := by
  have hF := bridgeForms_two_one K hn2
  simp only [bridgeSystem, mkSystem, badX0, badX1, badZ]
  rw [hF, map_mul]
  simp only [MvPolynomial.rename_X]
  ring

/-- The zerodivisor relation: `G₁·x₀ = x₁·G₀`. -/
theorem bridgeSystem_two_ring (K : Type*) [Field K] (hn2 : 0 < 2) :
    (bridgeSystem 2 K (badConsts K) hn2) badI1 * badX0 K =
      badX1 K * (bridgeSystem 2 K (badConsts K) hn2) badI0 := by
  rw [bridgeSystem_two_zero K hn2, bridgeSystem_two_one K hn2]
  ring

/-- Rung-1 regularity fails at the witness: `G₁` is a zerodivisor mod
`(G₀)`, so the bridge family is not successively regular. -/
theorem not_successive_bridgeSystem_two (K : Type*) [Field K] (hn2 : 0 < 2) :
    ¬ RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 2 K (badConsts K) hn2) := by
  intro hsucc
  have hG0 := bridgeSystem_two_zero K hn2
  have hG1 := bridgeSystem_two_one K hn2
  have hring := bridgeSystem_two_ring K hn2
  have hreg := hsucc badI1
  have h1val : badI1.val = 1 := rfl
  rw [h1val] at hreg
  have himage : Set.image (bridgeSystem 2 K (badConsts K) hn2)
      {k : Fin (statementIndex 2 + 1) | k.val < 1} =
      {(bridgeSystem 2 K (badConsts K) hn2) badI0} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk0 : k.val = 0 := by omega
      have ek : k = badI0 := Fin.ext hk0
      rw [ek]
    · intro hy
      refine ⟨badI0, ?_, hy.symm⟩
      show badI0.val < 1
      have hv0 : badI0.val = 0 := rfl
      omega
  rw [himage, RegularSequenceDimDrop.span_smul_top] at hreg
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg
  have hsmul : (bridgeSystem 2 K (badConsts K) hn2) badI1 •
      Ideal.Quotient.mk
        (Ideal.span {(bridgeSystem 2 K (badConsts K) hn2) badI0})
        (badX0 K) = 0 := by
    rw [← quot_mk_smul, smul_eq_mul, hring]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  have hne : Ideal.Quotient.mk
      (Ideal.span {(bridgeSystem 2 K (badConsts K) hn2) badI0})
      (badX0 K) ≠ 0 := by
    intro hcon
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hcon
    obtain ⟨Q, hQ⟩ := hcon
    have hx0 : badX0 K ≠ 0 := by simp [badX0]
    have hmul : badX0 K * 1 = badX0 K * ((badX0 K - badZ K) * Q) := by
      conv_lhs => rw [hQ, hG0]
      ring
    have hcancel : (1 : MvPolynomial (Fin (statementIndex 2 + 2)) K) =
        (badX0 K - badZ K) * Q :=
      mul_left_cancel₀ hx0 hmul
    have heval := congrArg
      (MvPolynomial.eval (0 : Fin (statementIndex 2 + 2) → K)) hcancel
    simp only [badX0, badZ, map_one, map_mul, map_sub, MvPolynomial.eval_X,
      Pi.zero_apply, sub_zero, zero_mul] at heval
    exact one_ne_zero heval
  exact hne (hreg _ hsmul)

/-- The full `hreg` `∀`-form over all `(n, c)` is false: refuted at
`n = 2`, `j = 1` by `badConsts`, via the contrapositive of
`hsucc_of_step_outputs`. Rung-`≥ 1` inputs must therefore carry hypotheses
on `c` (or a family narrowing); rung 0 above is the unconditional part. -/
theorem hreg_forall_false (K : Type*) [Field K] :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  intro hall
  exact not_successive_bridgeSystem_two K (by decide)
    (AvoidanceApply.hsucc_of_step_outputs _ (hall 2 (by decide) (badConsts K)))

#print axioms hreg_rung0
#print axioms hreg_rung1_of_dichotomy
#print axioms hres2_of_hreg_ge1_of_noEmbedded_minAvoid
#print axioms fixedPoint_of_idempotent_of_rung1plus
#print axioms hreg_forall_false

end RungRegular
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

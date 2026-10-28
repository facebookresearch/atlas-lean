/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.SesClosure

/-!
# Sup-tower closure: the H5 `htower` hypothesis is uninhabitable
Target: discharge `htower` of `hChiReduceAtAss_of_towers`
(`SesClosure.lean`:757) — per `Q ∈ Ass`, a dimension pin plus
the selection-colon tower `∀ J' ≠ ⊤, ∃ y, SupSelectData J' y ∧
SupColonStabFor J' y` over `R_Q`.

## Verdicts (see grades per declaration)

* The tower as stated is **false** (formal refutation): at
  `J' = 𝔪`, `SupSelectData` forces `y ∈ 𝔪`, but then
  `(𝔪 : y) = ⊤ ≠ 𝔪`, so `SupColonStabFor 𝔪 y` fails at every rank
  (`supColonStabFor_maximalIdeal_false`). Hence the tower is
  uninhabitable over any local ring (`supSelectColon_tower_false`).
* Stronger: over any adically-stabilized proper ideal (`𝔪 ^ k ≤ J'`,
  the dim-zero case), no `y ∈ 𝔪` satisfies the colon condition
  (`supColonStabFor_of_adicStab_forces_top`): past stabilization the
  colon equation reads `(J' : y) = J'`, hence `(J' : y ^ k) = J'`,
  but `y ^ k ∈ J'` then puts `1 ∈ J'`.
* Consequence for H6: `htower` forces `Ass = ∅`
  (`htower_forces_assEmpty`); on any quotient with nonempty `Ass`
  the hypothesis can never be discharged, so `hChiReduceAtAss_of_towers`
  cannot fire there. The per-`Q` form is `htower_atAss_false`.
* Reshape (SPEC, priced not attempted): `SupTowerPosDim` restricts the
  tower to positive-dimensional quotients (`¬ KrullDimLE 0`), where
  superficial elements exist classically. Price: superficial/order-one
  existence via prime avoidance on the project's `associatedGraded`
  (~300–500 lines: Mathlib v4.34.0 has zero superficial-element API —
  grep `superficial` over Mathlib returns only a prose comment in
  `Topology/Semicontinuity/Defs.lean` — and zero `associatedGraded`
  API, so homogeneous avoidance + lifting is all new) plus
  colon-from-superficial transfer (~100 lines). Note the masters
  (`sup_tower_nonvanishing`, `hChiReduceAtAss_of_towers`) additionally
  need exact-dimension pins (`dim = e`, not `≤ e`): at a dim-zero `J`
  with `e ≥ 1` the nonvanishing conclusion itself is false
  (`χ` eventually constant), so the induction must case-split on
  `KrullDimLE 0` — rework scoped ~100–150 lines, not attempted.

## Residual register

open (exact): `SupTowerPosDim` + master rework above. The proved
`supSopSelect` still supplies the selection half; only the colon half
is uninhabitable at dim-zero ideals. Closed this lane: [tower-as-stated
refutation], [dim-zero generalization], [`htower` forces `Ass = ∅`].

## References

Project (read-only): `SuperficialReduction.lean` (`SupSelectData`:165,
`supSopSelect`:380), `SesClosure.lean` (`SupColonStabFor`:290,
`hChiReduceAtAss_of_towers`:757), `AssociatedGradedRing.lean`
(`associatedGraded`:548, project-local).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
`Ideal/Colon.lean` (`Submodule.mem_colon_singleton`),
`Ideal/Operations.lean` (`Ideal.mul_le_left`, `Ideal.mul_le_right`,
`Ideal.pow_mem_pow`, `Ideal.eq_top_iff_one`),
`LocalRing/MaximalIdeal/Basic.lean` (`IsLocalRing.maximalIdeal.isMaximal`),
`Ideal/AssociatedPrime/Basic.lean` (`IsAssociatedPrime.isPrime`),
`Localization/AtPrime/Basic.lean` (`Localization.AtPrime.isLocalRing`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace TowerClosure

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SesClosure

/-! ## §1. Adic-power monotonicity helpers -/

/-- Positive powers of the maximal ideal lie inside it.
Follows from `𝔪 ^ (d+1) = 𝔪 ^ d * 𝔪 ≤ 𝔪`.
-/
theorem supMaximal_pow_le_self {R : Type*} [CommRing R] [IsLocalRing R]
    (k : ℕ) (hk : 1 ≤ k) :
    IsLocalRing.maximalIdeal R ^ k ≤ IsLocalRing.maximalIdeal R := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = d + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  exact Ideal.mul_le_right

#print axioms supMaximal_pow_le_self

/-- Adic powers decrease along `+`: `𝔪 ^ (k + d) ≤ 𝔪 ^ k`.
-/
theorem supMaximal_pow_add_le {R : Type*} [CommRing R] [IsLocalRing R]
    (k d : ℕ) :
    IsLocalRing.maximalIdeal R ^ (k + d)
      ≤ IsLocalRing.maximalIdeal R ^ k := by
  rw [pow_add]
  exact Ideal.mul_le_left

#print axioms supMaximal_pow_add_le

/-! ## §2. The tower is false at `𝔪` -/

/-- For `y ∈ 𝔪`, the colon `(𝔪 : y)` is everything: every `x` has
`x * y ∈ 𝔪`.
-/
theorem supColon_maximal_eq_top {R : Type*} [CommRing R] [IsLocalRing R]
    (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R : Submodule R R).colon {y}) = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact (IsLocalRing.maximalIdeal R).mul_mem_left x hym

#print axioms supColon_maximal_eq_top

/-- Falsity at `𝔪`: no `y ∈ 𝔪` satisfies `SupColonStabFor 𝔪 y`.
Both adic terms collapse (`𝔪 ^ (n+i) ⊔ 𝔪 = 𝔪`), so the colon equation
reads `(𝔪 : y) = 𝔪`, but the left side is `⊤`
(`supColon_maximal_eq_top`) while `𝔪 ≠ ⊤`.

Status: false (formal refutation of the `J' = 𝔪` tower instance). -/
theorem supColonStabFor_maximalIdeal_false {R : Type*} [CommRing R]
    [IsLocalRing R] (y : R)
    (hym : y ∈ IsLocalRing.maximalIdeal R) :
    ¬ SupColonStabFor (R := R) (IsLocalRing.maximalIdeal R) y := by
  intro hcol
  obtain ⟨c, hc⟩ := hcol
  have h := hc c le_rfl
  have hpow2 : IsLocalRing.maximalIdeal R ^ (c + 2)
      ≤ IsLocalRing.maximalIdeal R :=
    supMaximal_pow_le_self (c + 2) (by omega)
  have hpow1 : IsLocalRing.maximalIdeal R ^ (c + 1)
      ≤ IsLocalRing.maximalIdeal R :=
    supMaximal_pow_le_self (c + 1) (by omega)
  rw [sup_eq_right.mpr hpow2, sup_eq_right.mpr hpow1,
    supColon_maximal_eq_top y hym] at h
  have h1 : (1 : R) ∈ (IsLocalRing.maximalIdeal R : Submodule R R) := by
    rw [← h]
    exact Submodule.mem_top
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)

#print axioms supColonStabFor_maximalIdeal_false

/-- Falsity of the tower: `SupSelectData` at `𝔪` forces `y ∈ 𝔪`,
which contradicts `supColonStabFor_maximalIdeal_false`. No
Noetherian hypothesis is needed — the obstruction is purely the
colon equation at `𝔪`.

Status: false (formal refutation). -/
theorem supSelectColon_tower_false {R : Type*} [CommRing R]
    [IsLocalRing R] :
    ¬ ∀ J' : Ideal R, J' ≠ ⊤ →
      ∃ y : R, SupSelectData (R := R) J' y ∧
        SupColonStabFor (R := R) J' y := by
  intro htower
  have hmax : IsLocalRing.maximalIdeal R ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨y, hsop, hcol⟩ := htower _ hmax
  exact supColonStabFor_maximalIdeal_false y hsop.1 hcol

#print axioms supSelectColon_tower_false

/-! ## §3. Stronger: all adically-stabilized (dim-zero) ideals -/

/-- Colon stabilization over an adically-stabilized ideal forces the
ideal to be everything. Past stabilization the colon equation reads
`(J' : y) = J'`; by induction `(J' : y ^ t) = J'` for all `t`; but
`y ^ k ∈ 𝔪 ^ k ≤ J'` puts `1 ∈ (J' : y ^ k) = J'`. In particular no
`y ∈ 𝔪` satisfies the colon condition over any proper dim-zero `J'`.
-/
theorem supColonStabFor_of_adicStab_forces_top {R : Type*} [CommRing R]
    [IsLocalRing R] (J' : Ideal R) (y : R) (k : ℕ)
    (hstab : IsLocalRing.maximalIdeal R ^ k ≤ J')
    (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hcol : SupColonStabFor (R := R) J' y) : J' = ⊤ := by
  obtain ⟨c, hc⟩ := hcol
  set N : ℕ := max c k
  have hcN : c ≤ N := le_max_left c k
  have hkN : k ≤ N + 1 :=
    le_trans (le_max_right c k) (Nat.le_succ _)
  have hpow1 : IsLocalRing.maximalIdeal R ^ (N + 1) ≤ J' := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, N + 1 = k + d := ⟨N + 1 - k, by omega⟩
    rw [hd]
    exact le_trans (supMaximal_pow_add_le k d) hstab
  have hpow2 : IsLocalRing.maximalIdeal R ^ (N + 2) ≤ J' := by
    have hstep : IsLocalRing.maximalIdeal R ^ (N + 2)
        ≤ IsLocalRing.maximalIdeal R ^ (N + 1) := by
      have e : N + 2 = (N + 1) + 1 := by omega
      rw [e, pow_succ]
      exact Ideal.mul_le_left
    exact le_trans hstep hpow1
  have heq2 : IsLocalRing.maximalIdeal R ^ (N + 2) ⊔ J' = J' :=
    sup_eq_right.mpr hpow2
  have heq1 : IsLocalRing.maximalIdeal R ^ (N + 1) ⊔ J' = J' :=
    sup_eq_right.mpr hpow1
  have hcolonJ : ((J' : Submodule R R).colon {y})
      = (J' : Submodule R R) := by
    have h := hc N hcN
    rwa [heq2, heq1] at h
  have hpowColon : ∀ t : ℕ,
      ((J' : Submodule R R).colon {y ^ t})
        = (J' : Submodule R R) := by
    intro t
    induction t with
    | zero =>
      simp only [pow_zero]
      ext x
      simp [Submodule.mem_colon_singleton, smul_eq_mul]
    | succ t ih =>
      ext x
      have e : x • y ^ (t + 1) = (x • y ^ t) • y := by
        simp only [pow_succ, smul_eq_mul, mul_assoc]
      rw [Submodule.mem_colon_singleton, e,
        ← Submodule.mem_colon_singleton, hcolonJ,
        ← Submodule.mem_colon_singleton, ih]
  have hyk : y ^ k ∈ (J' : Submodule R R) :=
    hstab (Ideal.pow_mem_pow hym k)
  have h1 : (1 : R) ∈ (J' : Submodule R R) := by
    have hmem : (1 : R) ∈ ((J' : Submodule R R).colon {y ^ k}) := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul, one_mul]
      exact hyk
    rwa [hpowColon k] at hmem
  exact (Ideal.eq_top_iff_one _).mpr h1

#print axioms supColonStabFor_of_adicStab_forces_top

/-- The tower is uninhabitable over every prime localization: direct
instantiation of `supSelectColon_tower_false` at `R_Q` (a local ring
by `Localization.AtPrime.isLocalRing`).
-/
theorem supSelectColon_tower_false_atPrime (m : ℕ) (K : Type*)
    [Field K] (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    ¬ ∀ J' : Ideal (Localization.AtPrime Q), J' ≠ ⊤ →
      ∃ y : Localization.AtPrime Q,
        SupSelectData (R := Localization.AtPrime Q) J' y ∧
          SupColonStabFor (R := Localization.AtPrime Q) J' y :=
  supSelectColon_tower_false

#print axioms supSelectColon_tower_false_atPrime

/-! ## §4. Consequence: `htower` forces `Ass = ∅` -/

/-- The per-`Q` form: `htower` at any `Q ∈ Ass` is contradictory, since
its tower component is refuted by
`supSelectColon_tower_false_atPrime`.
-/
theorem htower_atAss_false (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [hQp : Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        (∀ J' : Ideal (Localization.AtPrime Q), J' ≠ ⊤ →
          ∃ y : Localization.AtPrime Q,
            SupSelectData (R := Localization.AtPrime Q) J' y ∧
              SupColonStabFor (R := Localization.AtPrime Q) J' y)) :
    False := by
  obtain ⟨dimN, hpin, htow⟩ := htower Q hQ
  exact supSelectColon_tower_false_atPrime m K Q htow

#print axioms htower_atAss_false

/-- The H5 verdict: the `htower` hypothesis of
`hChiReduceAtAss_of_towers` (SupSesClose:757) forces
`Ass(R ⧸ J) = ∅`. On any quotient with nonempty `Ass` it can never be
discharged, so the H3-pin conclusion cannot fire there; the tower must
be reshaped to positive-dimensional ideals (`SupTowerPosDim`).
-/
theorem htower_forces_assEmpty (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (htower : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∃ dimN : ℕ,
        ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        (∀ J' : Ideal (Localization.AtPrime Q), J' ≠ ⊤ →
          ∃ y : Localization.AtPrime Q,
            SupSelectData (R := Localization.AtPrime Q) J' y ∧
              SupColonStabFor (R := Localization.AtPrime Q) J' y)) :
    associatedPrimes (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K ⧸ J) = ∅ := by
  by_contra hne
  obtain ⟨Q, hQ⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hQprime : Q.IsPrime := IsAssociatedPrime.isPrime hQ
  exact htower_atAss_false m K J Q (hQp := hQprime) hQ htower

#print axioms htower_forces_assEmpty

/-! ## §5. Reshaped SPEC (scoped, not attempted) -/

/-- SPEC (residual, reshaped): the positive-dimension selection-colon
tower — the same conjunction as `htower` but quantified only over
ideals with `¬ KrullDimLE 0`, where superficial elements exist
classically. The `J' = 𝔪` and dim-zero counterexamples (§2–§3) do not
apply. Price: superficial/order-one existence via prime avoidance on
the project's `associatedGraded` (~300–500 lines, all new: Mathlib
v4.34.0 has zero superficial-element and zero `associatedGraded` API)
plus colon-from-superficial transfer (~100 lines); the masters
additionally need exact-dimension pins (rework ~100–150 lines).

Status: open (exact reshaped residual). -/
def SupTowerPosDim {R : Type*} [CommRing R] [IsLocalRing R] : Prop :=
  ∀ J' : Ideal R, J' ≠ ⊤ → ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    ∃ y : R, SupSelectData (R := R) J' y ∧
      SupColonStabFor (R := R) J' y

#print axioms SupTowerPosDim

end TowerClosure
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

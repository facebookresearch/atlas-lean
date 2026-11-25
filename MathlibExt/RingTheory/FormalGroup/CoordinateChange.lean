/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FormalGroup_PointTransport.lean`,
`Theorems/Thm_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one.lean`
and
`P2M/Sol/S_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

universe u

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- Substitution of a power series into the `i`-th variable. -/
noncomputable def LawHom.substX (i : Fin 2) (φ : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) φ

/-- A homomorphism of one-dimensional formal group laws given by a power
series with zero constant coefficient intertwining the two laws. -/
structure LawHom (F G : FormalGroup R) where
  /-- The underlying power series. -/
  series : PowerSeries R
  /-- The series has zero constant coefficient. -/
  constantCoeff_series : PowerSeries.constantCoeff series = 0
  /-- The series intertwines the two formal group laws. -/
  comm : PowerSeries.subst F.toPowerSeries series =
    MvPowerSeries.subst ![LawHom.substX 0 series, LawHom.substX 1 series] G.toPowerSeries

/-- An isomorphism of one-dimensional formal group laws: a law homomorphism
whose linear coefficient is a unit. -/
structure LawIso (F G : FormalGroup R) extends LawHom F G where
  /-- The linear coefficient is a unit. -/
  isUnit_coeff_one : IsUnit (PowerSeries.coeff 1 series)

end FormalGroup

namespace FormalGroup

namespace TransportAux

open MvPowerSeries

variable {R : Type u} [CommRing R]

private theorem coeff_single_one_mul_eq_zero {τ : Type} [DecidableEq τ] (i : τ) (g h :
    MvPowerSeries τ R)
    (hg : MvPowerSeries.constantCoeff g = 0) (hh : MvPowerSeries.constantCoeff h = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (g * h) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = 1 := by
    rw [← map_add, hp, Finsupp.degree_single]
  rcases Nat.eq_zero_or_pos (Finsupp.degree p.1) with h1 | h1
  · rw [(Finsupp.degree_eq_zero_iff _).mp h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg,
      zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh,
        mul_zero]

private def FlatTwo {τ : Type} (g : MvPowerSeries τ R) : Prop :=
  MvPowerSeries.constantCoeff g = 0 ∧ ∀ i : τ, MvPowerSeries.coeff (Finsupp.single i 1) g = 0

private theorem FlatTwo.mul_right {τ : Type} [DecidableEq τ] {g : MvPowerSeries τ R} (hg : FlatTwo
    g) (h : MvPowerSeries τ R) :
    FlatTwo (g * h) := by
  classical
  refine ⟨by rw [map_mul, hg.1, zero_mul], fun i => ?_⟩
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = 1 := by
    rw [← map_add, hp, Finsupp.degree_single]
  rcases Nat.eq_zero_or_pos (Finsupp.degree p.1) with h1 | h1
  · rw [(Finsupp.degree_eq_zero_iff _).mp h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      hg.1, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    have hp1 : p.1 = Finsupp.single i 1 := by
      have := hp; rw [(Finsupp.degree_eq_zero_iff _).mp h2, _root_.add_zero] at this; exact this
    rw [hp1, hg.2 i, zero_mul]

private theorem FlatTwo.mul_left {τ : Type} [DecidableEq τ] {h : MvPowerSeries τ R} (hh : FlatTwo
    h) (g : MvPowerSeries τ R) :
    FlatTwo (g * h) := by
  rw [mul_comm]; exact hh.mul_right g

private theorem flatTwo_mul {τ : Type} [DecidableEq τ] (g h : MvPowerSeries τ R)
    (hg : MvPowerSeries.constantCoeff g = 0) (hh : MvPowerSeries.constantCoeff h = 0) : FlatTwo (g
        * h) :=
  ⟨by rw [map_mul, hg, zero_mul], fun i => coeff_single_one_mul_eq_zero i g h hg hh⟩

private theorem flatTwo_pow {τ : Type} [DecidableEq τ] (g : MvPowerSeries τ R) (hg :
    MvPowerSeries.constantCoeff g = 0)
    (n : ℕ) (hn : 2 ≤ n) : FlatTwo (g ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [pow_add, pow_two]
  exact (flatTwo_mul g g hg hg).mul_left _

private theorem coeff_single_one_subst_powerSeries {τ : Type} [DecidableEq τ] (i : τ) (A :
    MvPowerSeries τ R)
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff (Finsupp.single i 1) A := by
  classical
  have hsA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero hA
  rw [PowerSeries.coeff_subst hsA, finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, MvPowerSeries.coeff_one, ite_eq_right (Finsupp.single_ne_zero.mpr one_ne_zero),
          smul_zero]
    · rw [(flatTwo_pow A hA d (by omega)).2 i, smul_zero]

private theorem coeff_single_one_subst_fin_two {τ : Type} [DecidableEq τ] (i : τ) (a : Fin 2 →
    MvPowerSeries τ R)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst a f) =
      MvPowerSeries.coeff (Finsupp.single 0 1) f * MvPowerSeries.coeff (Finsupp.single i 1) (a 0) +
      MvPowerSeries.coeff (Finsupp.single 1 1) f * MvPowerSeries.coeff (Finsupp.single i 1) (a 1)
          := by
  classical
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => a s ^ e) = a 0 ^ d 0 * a 1 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun s => pow_zero (a s)), Fin.prod_univ_two]
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    simp [Finsupp.single_eq_single_iff]
  rw [MvPowerSeries.coeff_subst hsa,
    finsum_eq_sum_of_support_subset _ (s := {Finsupp.single 0 1, Finsupp.single 1 1}) ?_,
    Finset.sum_pair hne, hprod, hprod]
  · simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from
      Fin.zero_ne_one),
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from Fin.zero_ne_one.symm), pow_one, pow_zero,
          mul_one, one_mul,
      smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hnot
    push Not at hnot
    apply hd
    rw [hprod]

    have key : MvPowerSeries.coeff (Finsupp.single i 1) (a 0 ^ d 0 * a 1 ^ d 1) = 0 := by
      rcases Nat.lt_or_ge (d 0) 2 with h0 | h0
      · rcases Nat.lt_or_ge (d 1) 2 with h1 | h1
        ·
          have hd01 : ¬ (d 0 = 1 ∧ d 1 = 0) := by
            rintro ⟨e0, e1⟩; apply hnot.1; ext s; fin_cases s <;> simp [e0, e1]
          have hd10 : ¬ (d 0 = 0 ∧ d 1 = 1) := by
            rintro ⟨e0, e1⟩; apply hnot.2; ext s; fin_cases s <;> simp [e0, e1]
          rcases Nat.eq_zero_or_pos (d 0) with e0 | e0 <;> rcases Nat.eq_zero_or_pos (d 1) with e1
              | e1
          · rw [e0, e1, pow_zero, pow_zero, one_mul, MvPowerSeries.coeff_one,
              ite_eq_right (Finsupp.single_ne_zero.mpr one_ne_zero)]
          · exact absurd ⟨e0, by omega⟩ hd10
          · exact absurd ⟨by omega, e1⟩ hd01
          · have : d 0 = 1 := by omega
            have : d 1 = 1 := by omega
            rw [‹d 0 = 1›, ‹d 1 = 1›, pow_one, pow_one]
            exact coeff_single_one_mul_eq_zero i _ _ (ha 0) (ha 1)
        · exact ((flatTwo_pow (a 1) (ha 1) (d 1) h1).mul_left _).2 i
      · exact ((flatTwo_pow (a 0) (ha 0) (d 0) h0).mul_right _).2 i
    rw [key, smul_zero]

section Construction

variable (F : FormalGroup R) (u : PowerSeries R)
  (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u))

private noncomputable abbrev inv : PowerSeries R := PowerSeries.substInvOfIsUnit u hu1

private theorem constantCoeff_inv : PowerSeries.constantCoeff (inv u hu1) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

include hu0 in
private theorem subst_inv_left : PowerSeries.subst u (inv u hu1) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left u hu0 hu1

include hu0 in
private theorem subst_inv_right : PowerSeries.subst (inv u hu1) u = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right u hu0 hu1

private theorem constantCoeff_substX (s : Fin 2) (φ : PowerSeries R) (hφ :
    PowerSeries.constantCoeff φ = 0) :
    MvPowerSeries.constantCoeff (LawHom.substX s φ) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ hφ

private theorem hasSubst_substX (φ : PowerSeries R) (hφ : PowerSeries.constantCoeff φ = 0) :
    MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => constantCoeff_substX s φ hφ)

private theorem vec_eq (φ : PowerSeries R) :
    (![LawHom.substX 0 φ, LawHom.substX 1 φ] : Fin 2 → MvPowerSeries (Fin 2) R) = fun s =>
        LawHom.substX s φ := by
  funext s; fin_cases s <;> rfl

private noncomputable def inner : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (fun s : Fin 2 => LawHom.substX s (inv u hu1)) F.toPowerSeries

private noncomputable def series : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (inner F u hu1) u

private theorem constantCoeff_inner : MvPowerSeries.constantCoeff (inner F u hu1) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_substX _ (constantCoeff_inv u hu1))
    (fun s => constantCoeff_substX s _ (constantCoeff_inv u hu1)) F.zero_constantCoeff

include hu0 in
private theorem constantCoeff_series : MvPowerSeries.constantCoeff (series F u hu1) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_inner F u hu1) u hu0


private theorem subst_inner {τ : Type} (b : Fin 2 → MvPowerSeries τ R) (hb : ∀ s,
    MvPowerSeries.constantCoeff (b s) = 0) :
    MvPowerSeries.subst b (inner F u hu1) =
      MvPowerSeries.subst (fun s : Fin 2 => PowerSeries.subst (b s) (inv u hu1)) F.toPowerSeries :=
          by
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  unfold inner
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_substX _ (constantCoeff_inv u hu1)) hsb]
  congr 1
  funext s
  rw [show LawHom.substX s (inv u hu1) = PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin
      2) R) (inv u hu1)
      from rfl, PowerSeries.subst_def (MvPowerSeries.X s : MvPowerSeries (Fin 2) R),
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X s).const hsb,
        MvPowerSeries.subst_X hsb s,
    ← PowerSeries.subst_def]

private theorem subst_series {τ : Type} (b : Fin 2 → MvPowerSeries τ R) (hb : ∀ s,
    MvPowerSeries.constantCoeff (b s) = 0) :
    MvPowerSeries.subst b (series F u hu1) =
      PowerSeries.subst (MvPowerSeries.subst (fun s : Fin 2 => PowerSeries.subst (b s) (inv u hu1))
          F.toPowerSeries) u := by
  have hsb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  unfold series
  rw [PowerSeries.subst_def (inner F u hu1) u,
    MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_inner F u hu1)).const hsb,
    ← PowerSeries.subst_def, subst_inner F u hu1 b hb]

include hu0 in
private theorem subst_subst_inv {τ : Type} (B : MvPowerSeries τ R) (hB :
    MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst (PowerSeries.subst B u) (inv u hu1) = B := by
  have hsB : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hu0) hsB,
    subst_inv_left u hu0 hu1, PowerSeries.subst_X hsB]

include hu0 in
private theorem subst_inv_subst {τ : Type} (B : MvPowerSeries τ R) (hB :
    MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst (PowerSeries.subst B (inv u hu1)) u = B := by
  have hsB : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero'
      (constantCoeff_inv u hu1)) hsB,
    subst_inv_right u hu0 hu1, PowerSeries.subst_X hsB]

private theorem subst_subst_pair {τ τ' : Type} (c : τ → MvPowerSeries τ' R) (hc :
    MvPowerSeries.HasSubst c)
    (g₁ g₂ : MvPowerSeries τ R) (hg₁ : MvPowerSeries.constantCoeff g₁ = 0) (hg₂ :
        MvPowerSeries.constantCoeff g₂ = 0) :
    MvPowerSeries.subst c (MvPowerSeries.subst ![g₁, g₂] F.toPowerSeries) =
      MvPowerSeries.subst ![MvPowerSeries.subst c g₁, MvPowerSeries.subst c g₂] F.toPowerSeries :=
          by
  have hg : MvPowerSeries.HasSubst (![g₁, g₂] : Fin 2 → MvPowerSeries τ R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> assumption)
  rw [MvPowerSeries.subst_comp_subst_apply hg hc]
  congr 1
  funext s; fin_cases s <;> rfl

include hu0 in
set_option maxHeartbeats 1600000 in
private theorem series_assoc :
    MvPowerSeries.subst ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
        MvPowerSeries.X 1]
        (series F u hu1), MvPowerSeries.X 2] (series F u hu1) =
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]
        (series F u hu1)] (series F u hu1) := by

  set c : Fin 3 → MvPowerSeries (Fin 3) R :=
    fun s => PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 3) R) (inv u hu1) with hc
  have hc0 : ∀ s, MvPowerSeries.constantCoeff (c s) = 0 :=
    fun s => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _
        (constantCoeff_inv u hu1)
  have hsc : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hc0
  have hS0 := constantCoeff_series F u hu0 hu1
  have hX0 : ∀ s : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries (Fin 3) R)
      = 0 :=
    fun s => MvPowerSeries.constantCoeff_X s

  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 1]
          (series F u hu1)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> exact hX0 _))
      (fun s => by fin_cases s <;> exact hX0 _) hS0
  have h12 : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]
          (series F u hu1)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> exact hX0 _))
      (fun s => by fin_cases s <;> exact hX0 _) hS0

  have hFcc : ∀ i j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.subst ![c i, c j]
      F.toPowerSeries) = 0 :=
    fun i j => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> exact hc0 _))
      (fun s => by fin_cases s <;> exact hc0 _) F.zero_constantCoeff

  have hin : ∀ i j : Fin 3, MvPowerSeries.subst ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X j]
      (series F u hu1) = PowerSeries.subst (MvPowerSeries.subst ![c i, c j] F.toPowerSeries) u := by
    intro i j
    rw [subst_series F u hu1 _ (fun s => by fin_cases s <;> exact hX0 _)]
    congr 2
    funext s; fin_cases s <;> rfl

  have hL : MvPowerSeries.subst ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3)
      R), MvPowerSeries.X 1]
        (series F u hu1), MvPowerSeries.X 2] (series F u hu1) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst ![c 0, c 1] F.toPowerSeries, c
          2] F.toPowerSeries) u := by
    rw [subst_series F u hu1 _ (fun s => by fin_cases s; exact h01; exact hX0 _)]
    congr 2
    funext s; fin_cases s
    · show PowerSeries.subst (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
        MvPowerSeries.X 1]
          (series F u hu1)) (inv u hu1)
        = MvPowerSeries.subst ![c 0, c 1] F.toPowerSeries
      rw [hin 0 1, subst_subst_inv u hu0 hu1 _ (hFcc 0 1)]
    · rfl
  have hR : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]
        (series F u hu1)] (series F u hu1) =
      PowerSeries.subst (MvPowerSeries.subst ![c 0, MvPowerSeries.subst ![c 1, c 2]
          F.toPowerSeries] F.toPowerSeries) u := by
    rw [subst_series F u hu1 _ (fun s => by fin_cases s; exact hX0 _; exact h12)]
    congr 2
    funext s; fin_cases s
    · rfl
    · show PowerSeries.subst (MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
        MvPowerSeries.X 2]
          (series F u hu1)) (inv u hu1)
        = MvPowerSeries.subst ![c 1, c 2] F.toPowerSeries
      rw [hin 1 2, subst_subst_inv u hu0 hu1 _ (hFcc 1 2)]

  have hcc01 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![MvPowerSeries.X (R := R) (0 : Fin 3), MvPowerSeries.X (R := R) (1 : Fin 3)]
      F.toPowerSeries) = 0 := by
    refine MvPowerSeries.constantCoeff_subst_eq_zero MvPowerSeries.HasSubst.X_X ?_
      F.zero_constantCoeff
    intro s
    fin_cases s <;> exact hX0 _
  have hcc12 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![MvPowerSeries.X (R := R) (1 : Fin 3), MvPowerSeries.X (R := R) (2 : Fin 3)]
      F.toPowerSeries) = 0 := by
    refine MvPowerSeries.constantCoeff_subst_eq_zero MvPowerSeries.HasSubst.X_X ?_
      F.zero_constantCoeff
    intro s
    fin_cases s <;> exact hX0 _
  have hA := congrArg (MvPowerSeries.subst c) F.assoc
  rw [subst_subst_pair F c hsc _ _ hcc01 (hX0 2),
    subst_subst_pair F c hsc _ _ (hX0 0) hcc12,
    subst_subst_pair F c hsc _ _ (hX0 0) (hX0 1),
    subst_subst_pair F c hsc _ _ (hX0 1) (hX0 2)] at hA
  simp only [MvPowerSeries.subst_X hsc] at hA
  rw [hL, hR, hA]

private theorem coeff_single_one_substX (i s : Fin 2) (φ : PowerSeries R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (LawHom.substX s φ) = if i = s then PowerSeries.coeff
        1 φ else 0 := by
  classical
  unfold LawHom.substX
  rw [PowerSeries.coeff_subst_single]
  by_cases h : i = s
  · subst h
    simp [Finsupp.single_eq_same]
  · have h1 : (Finsupp.single i 1 : Fin 2 →₀ ℕ) s = 0 := by simp [h]
    rw [h1, ite_eq_right, ite_eq_right h]
    rw [Finsupp.single_zero]
    exact Finsupp.single_ne_zero.mpr one_ne_zero

private theorem coeff_single_one_inner (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (inner F u hu1) = PowerSeries.coeff 1 (inv u hu1) := by
  classical
  unfold inner
  rw [coeff_single_one_subst_fin_two i _ (fun s => constantCoeff_substX s _ (constantCoeff_inv u
      hu1)),
    F.lin_coeff_X, F.lin_coeff_Y, one_mul, one_mul, coeff_single_one_substX,
        coeff_single_one_substX]
  fin_cases i <;> simp

private theorem coeff_single_one_series (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (series F u hu1) = 1 := by
  classical
  unfold series
  rw [coeff_single_one_subst_powerSeries i _ (constantCoeff_inner F u hu1), coeff_single_one_inner,
    PowerSeries.coeff_one_substInvOfIsUnit]
  exact hu1.mul_val_inv

include hu0 in
private theorem comm_series :
    PowerSeries.subst F.toPowerSeries u =
      MvPowerSeries.subst ![LawHom.substX 0 u, LawHom.substX 1 u] (series F u hu1) := by
  have hb : ∀ s, MvPowerSeries.constantCoeff ((![LawHom.substX 0 u, LawHom.substX 1 u] : Fin 2 → _)
      s) = 0 :=
    fun s => by fin_cases s <;> exact constantCoeff_substX _ u hu0
  rw [subst_series F u hu1 _ hb]
  have hfam : (fun s : Fin 2 => PowerSeries.subst ((![LawHom.substX 0 u, LawHom.substX 1 u] : Fin 2
      → _) s) (inv u hu1)) =
      (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext s
    fin_cases s
    · show PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) u)
        (inv u hu1) = _
      exact subst_subst_inv u hu0 hu1 _ (MvPowerSeries.constantCoeff_X 0)
    · show PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) u)
        (inv u hu1) = _
      exact subst_subst_inv u hu0 hu1 _ (MvPowerSeries.constantCoeff_X 1)
  rw [hfam, ← MvPowerSeries.map_algebraMap_eq_subst_X, Algebra.algebraMap_self,
      MvPowerSeries.map_id]
  rfl

private theorem series_comm [F.IsComm] :
    series F u hu1 = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (series F u hu1)
        := by
  have hX0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries (Fin 2) R)
      = 0 :=
    fun s => MvPowerSeries.constantCoeff_X s
  have hb : ∀ s, MvPowerSeries.constantCoeff ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 →
      MvPowerSeries (Fin 2) R) s)
      = 0 := fun s => by fin_cases s <;> exact hX0 _
  rw [subst_series F u hu1 _ hb]
  have hfam : (fun s : Fin 2 => PowerSeries.subst
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s) (inv u hu1)) =
      ![LawHom.substX 1 (inv u hu1), LawHom.substX 0 (inv u hu1)] := by
    funext s; fin_cases s <;> rfl
  have hin : inner F u hu1 =
      MvPowerSeries.subst ![LawHom.substX 1 (inv u hu1), LawHom.substX 0 (inv u hu1)]
          F.toPowerSeries := by
    unfold inner
    conv_lhs => rw [‹F.IsComm›.comm]
    rw [subst_subst_pair F _ (hasSubst_substX _ (constantCoeff_inv u hu1)) _ _ (hX0 1) (hX0 0),
      MvPowerSeries.subst_X (hasSubst_substX _ (constantCoeff_inv u hu1)),
      MvPowerSeries.subst_X (hasSubst_substX _ (constantCoeff_inv u hu1))]
  rw [hfam, ← hin]
  rfl

include hu0 in
private noncomputable def law : FormalGroup R where
  toPowerSeries := series F u hu1
  zero_constantCoeff := constantCoeff_series F u hu0 hu1
  lin_coeff_X := coeff_single_one_series F u hu1 0
  lin_coeff_Y := coeff_single_one_series F u hu1 1
  assoc := series_assoc F u hu0 hu1

include hu0 in
private noncomputable def iso : LawIso F (law F u hu0 hu1) where
  series := u
  constantCoeff_series := hu0
  comm := comm_series F u hu0 hu1
  isUnit_coeff_one := hu1

private theorem isComm_law [F.IsComm] : (law F u hu0 hu1).IsComm :=
  ⟨series_comm F u hu1⟩

end Construction

end TransportAux

end FormalGroup


theorem FormalGroup.TransportAux.target_eq_of_series_eq
    {R : Type u} [CommRing R] {F G G' : FormalGroup R} (ψ : FormalGroup.LawIso F G) (θ :
        FormalGroup.LawHom F G')
    (h : θ.series = ψ.series) : G' = G := by
  have hP0 : PowerSeries.constantCoeff ψ.series = 0 := ψ.constantCoeff_series
  have hu : IsUnit (PowerSeries.coeff 1 ψ.series) := ψ.isUnit_coeff_one
  set χ := PowerSeries.substInvOfIsUnit ψ.series hu with hχ
  have hQ0 : PowerSeries.constantCoeff χ = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hright : PowerSeries.subst χ ψ.series = PowerSeries.X :=
      PowerSeries.subst_substInvOfIsUnit_right ψ.series hP0 hu
  have hsQ : PowerSeries.HasSubst χ := PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  have hvec : ∀ φ : PowerSeries R,
      (![LawHom.substX 0 φ, LawHom.substX 1 φ] : Fin 2 → MvPowerSeries (Fin 2) R) = fun s =>
          LawHom.substX s φ := by
    intro φ; funext s; fin_cases s <;> rfl
  have hcX : ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      ∀ s : Fin 2, MvPowerSeries.constantCoeff (LawHom.substX s φ) = 0 :=
    fun φ hφ s => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ hφ
  have hXP : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s ψ.series) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hP0)
  have hXQ : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s χ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hQ0)
  have hXs : ∀ s : Fin 2, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X s :
      MvPowerSeries (Fin 2) R)) :=
    fun s => (PowerSeries.HasSubst.X s).const

  have key : ∀ s : Fin 2,
      MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t χ) (LawHom.substX s ψ.series) =
          MvPowerSeries.X s := by
    intro s
    rw [show LawHom.substX s ψ.series =
          PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) ψ.series from rfl,
      PowerSeries.subst_def (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) ψ.series,
      MvPowerSeries.subst_comp_subst_apply (hXs s) hXQ, MvPowerSeries.subst_X hXQ s,
      show LawHom.substX s χ = PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) χ
          from rfl,
      ← PowerSeries.subst_def, ← PowerSeries.subst_comp_subst_apply hsQ (PowerSeries.HasSubst.X s),
          hright,
      PowerSeries.subst_X (PowerSeries.HasSubst.X s)]

  have ev : ∀ H : FormalGroup R,
      MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t χ)
        (MvPowerSeries.subst ![LawHom.substX 0 ψ.series, LawHom.substX 1 ψ.series] H.toPowerSeries)
            =
      H.toPowerSeries := by
    intro H
    rw [hvec, MvPowerSeries.subst_comp_subst_apply hXP hXQ]
    simp only [key]
    rw [← MvPowerSeries.map_algebraMap_eq_subst_X, Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl
  have e1 := ψ.comm
  have e2 := θ.comm
  rw [h, e1] at e2

  have := congrArg (MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t χ)) e2
  rw [ev G, ev G'] at this
  exact FormalGroup.ext this.symm

theorem FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one
    {R : Type u} [CommRing R] (F : FormalGroup R) (u : PowerSeries R)
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u)) :
    ∃ F' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F', ψ.series = u) ∧ (F.IsComm → F'.IsComm) ∧
      ∀ F'' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F'', ψ.series = u) → F'' = F' :=
  ⟨FormalGroup.TransportAux.law F u hu0 hu1, ⟨FormalGroup.TransportAux.iso F u hu0 hu1, rfl⟩,
    fun _ => FormalGroup.TransportAux.isComm_law F u hu0 hu1,
    fun _ h => h.elim fun ψ hψ => FormalGroup.TransportAux.target_eq_of_series_eq
        (FormalGroup.TransportAux.iso F u hu0 hu1) ψ.toLawHom hψ⟩

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Gibbs

/-!
# Partition functions of finite systems and their pressure

The partition function of a finite system, its products, and the pressure of independent copies.

## i. Overview

For a finite state space with energy `E`, `Z(β) = ∑_s e^{-βE(s)}`; the partition function of a
product system with additive energy is the product of the partition functions. For `n` independent
copies, `log Z_n` is subadditive and `log Z_n / n → log Z`, so `pressure β E = log Z(β)`. For the
Ising model on a finite graph this gives `pressure β (hamiltonian G h) = log (isingZ G β h)`.

Note: this is the pressure of independent copies of one finite system, not the thermodynamic limit
of the lattice model; boundary-condition independence of lattice box pressures is in
`PressureSurfaceVolume`.

## ii. Key results

- `StatMech.Ising.Z` : the partition function of a finite system
- `StatMech.Ising.Z_prod` : partition functions of products
- `StatMech.Ising.pressure` : the pressure of independent copies
- `StatMech.Ising.ising_pressure_eq` : the Ising pressure is `log Z`

## iii. Table of contents

- A. Partition functions
- B. Independent copies
- C. The pressure

## iv. References

- D. Ruelle, *Statistical Mechanics: Rigorous Results*, Benjamin (1969)
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 3
-/

@[expose] public section

open scoped BigOperators
open Finset Filter Topology

namespace StatMech

namespace Ising

/-! ## A. Partition functions -/

/-- The partition function `Z(β) = ∑_s e^{-βE(s)}` of a finite system. -/
noncomputable def Z {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) : ℝ :=
  ∑ s : Ω, Real.exp (-β * E s)

lemma Z_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) : 0 < Z β E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma Z_prod {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (β : ℝ)
    (E₁ : Ω₁ → ℝ) (E₂ : Ω₂ → ℝ) :
    Z β (fun p : Ω₁ × Ω₂ => E₁ p.1 + E₂ p.2) = Z β E₁ * Z β E₂ := by
  unfold Z
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Real.exp_add]
  ring_nf

/-! ## B. Independent copies -/

/-- The partition function of `n` independent copies of the system. -/
noncomputable def Zpow {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) : ℝ :=
  Z β (fun c : Fin n → Ω => ∑ i, E (c i))

lemma Zpow_eq {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    Zpow β E n = (Z β E) ^ n := by
  unfold Zpow Z
  have key : (∑ a, Real.exp (-β * E a)) ^ n
      = ∑ p : Fin n → Ω, ∏ i, Real.exp (-β * E (p i)) :=
    Fintype.sum_pow (fun a => Real.exp (-β * E a)) n
  rw [key]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Real.exp_sum]

lemma Zpow_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    0 < Zpow β E n :=
  Z_pos β _

/-- The sequence `log Z_n` for `n` independent copies. -/
noncomputable def logZSeq {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) : ℝ :=
  Real.log (Zpow β E n)

lemma logZSeq_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    logZSeq β E n = n * Real.log (Z β E) := by
  unfold logZSeq
  rw [Zpow_eq, Real.log_pow]

lemma logZSeq_subadditive {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    Subadditive (logZSeq β E) := by
  intro m n
  rw [logZSeq_eq, logZSeq_eq, logZSeq_eq]
  have hcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  rw [hcast]
  apply le_of_eq
  ring

lemma logZSeq_bddBelow {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    BddBelow (Set.range fun n => logZSeq β E n / n) := by
  refine ⟨min 0 (Real.log (Z β E)), ?_⟩
  rintro x ⟨n, rfl⟩
  simp only
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [logZSeq, Zpow, Nat.cast_zero, div_zero]
    exact min_le_left _ _
  · rw [logZSeq_eq, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]
    exact min_le_right _ _

/-! ## C. The pressure -/

/-- The pressure: the limit of `log Z_n / n` for independent copies, obtained from subadditivity. -/
noncomputable def pressure {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) : ℝ :=
  (logZSeq_subadditive β E).lim

lemma pressure_exists {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    Tendsto (fun n => logZSeq β E n / n) atTop (𝓝 (pressure β E)) :=
  (logZSeq_subadditive β E).tendsto_lim (logZSeq_bddBelow β E)

lemma pressure_eq_logZ {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    pressure β E = Real.log (Z β E) := by
  have hlim : Tendsto (fun n => logZSeq β E n / n) atTop (𝓝 (Real.log (Z β E))) := by
    have hc : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (Z β E) / n) atTop
        (𝓝 (Real.log (Z β E))) := by
      refine (tendsto_const_nhds (x := Real.log (Z β E))).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]
    refine hc.congr fun n => ?_
    rw [logZSeq_eq]
  exact tendsto_nhds_unique (pressure_exists β E) hlim

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

lemma isingZ_eq_Z (β h : ℝ) : isingZ G β h = Z β (hamiltonian G h) := rfl

lemma ising_pressure_exists (β h : ℝ) :
    Tendsto (fun n => logZSeq β (hamiltonian G h) n / n) atTop
      (𝓝 (pressure β (hamiltonian G h))) :=
  pressure_exists β (hamiltonian G h)

lemma ising_pressure_eq (β h : ℝ) :
    pressure β (hamiltonian G h) = Real.log (isingZ G β h) := by
  rw [pressure_eq_logZ, isingZ_eq_Z]

end Ising

end StatMech

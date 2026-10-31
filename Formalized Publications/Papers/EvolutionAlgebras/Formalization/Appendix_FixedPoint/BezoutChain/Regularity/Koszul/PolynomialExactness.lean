/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# Koszul exactness over `κ[X]` (A4(iii), file 5 of 6)

Tower induction for the Koszul chain complex of the variables
`X₀, …, X_{d-1}` over `S = MvPolynomial (Fin d) κ`: the file-4 shared
cone-step (`koszulStep_augmented_exact`, used read-only) climbs the tower of
quotients `S ⧸ span{X₀..X_{n-1}}`, with var-regularity per rung from an
eval-kill retraction into the polynomial domain. Pure matrix chase via
file 4 (no `δ`/LES).

* (§1) The rung ideals `towerIdeal n = span{X i : i < n}` and one-step growth.
* (§2) The eval-kill map `killEval n` (first `n` variables to 0) and its
  kernel, both directions.
* (§3) The rung scalar `rungScalar n` and var-regularity `tower_var_regular`.
* (§4) The rung quotient map `towerMap n` with the file-4 presentation inputs.
* (§5) The base case: higher exterior powers of the empty module vanish.
* (§6) The tower (`towerMod` / `towerPhi` / `towerAug`), the step, and the
  master `koszul_poly_augmented_exact` in the exact file-4 triple shape that
  file 6 (`GradedLift`) consumes.

Design note: the sketch suggested `MvPolynomial.finSuccEquiv_X_zero`
for the quotient tower; the eval-kill retraction here has the same force
(quotient by peeling variables) while avoiding `DoubleQuot` iteration and
`Fin`-subtraction casts. The output shape is exactly as sketched.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/MvPolynomial/Basic.lean`: `induction_on`, `X_ne_zero`,
  `NoZeroDivisors` instance.
* `Algebra/MvPolynomial/Eval.lean`: `eval₂Hom`, `eval₂Hom_C`, `eval₂Hom_X'`.
* `LinearAlgebra/ExteriorAlgebra/Basic.lean`: `ιMulti_succ_apply`,
  `ιMulti_span_fixedDegree`.
* `LinearAlgebra/ExteriorPower/Basic.lean`: `zeroEquiv`.
* `LinearAlgebra/Quotient/Basic.lean`: `mkQ`, `mkQ_surjective`, `mapQ`,
  `mapQ_mkQ`.
* `LinearAlgebra/Span/Defs.lean`: `mem_sup`, `span_le`, `span_induction`.
* `LinearAlgebra/Prod.lean`: `LinearMap.fst` / `snd`.
* `RingTheory/Ideal/Span.lean`: `span_insert`, `span_le`, `span_mono`,
  `span_empty`, `mem_span_singleton'`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `eq_zero_iff_mem`.

Project (read-only): `Regularity/Koszul/AugmentedConeStep.lean` (file 4 of 6:
`contractExactAt`, `contractAugExactZero`, `koszulStepAug`,
`koszulStep_augmented_exact`).

## Status

All unconditional.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace PolynomialExactness

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep

variable (κ : Type*) [Field κ] (d : ℕ)

/-! ## §1. Rung ideals -/

/-- Variables with index `< n`: the kill set at rung `n`. -/
def killSet (n : ℕ) : Set (Fin d) := {i | i.val < n}

/-- The kill set grows by the rung variable. -/
theorem killSet_succ (n : ℕ) (h : n < d) :
    killSet d (n + 1) = insert (⟨n, h⟩ : Fin d) (killSet d n) := by
  ext i
  change i.val < n + 1 ↔ (i = (⟨n, h⟩ : Fin d) ∨ i.val < n)
  constructor
  · intro hi
    by_cases heq : i.val = n
    · exact Or.inl (Fin.ext_iff.mpr heq)
    · exact Or.inr (by omega)
  · rintro (rfl | hi)
    · exact Nat.lt_succ_self n
    · omega

/-- The rung ideal: span of the killed variables. -/
noncomputable def towerIdeal (n : ℕ) : Ideal (MvPolynomial (Fin d) κ) :=
  Ideal.span (MvPolynomial.X '' killSet d n)

/-- One-step growth of the rung ideal. -/
theorem towerIdeal_succ (n : ℕ) (h : n < d) :
    towerIdeal κ d (n + 1)
      = Ideal.span {MvPolynomial.X (⟨n, h⟩ : Fin d)} ⊔ towerIdeal κ d n := by
  rw [towerIdeal, killSet_succ d n h, Set.image_insert_eq, Ideal.span_insert,
    ← towerIdeal]

/-- Monotonicity of the rung ideals. -/
theorem towerIdeal_mono (n : ℕ) : towerIdeal κ d n ≤ towerIdeal κ d (n + 1) := by
  rw [towerIdeal, towerIdeal]
  apply Ideal.span_mono
  intro g hg
  obtain ⟨i, hi, rfl⟩ := hg
  refine ⟨i, ?_, rfl⟩
  have hi' : i.val < n := hi
  have hgoal : i.val < n + 1 := by omega
  exact hgoal

/-- The base rung ideal is trivial. -/
theorem towerIdeal_zero : towerIdeal κ d 0 = ⊥ := by
  rw [towerIdeal]
  have hkill : killSet d 0 = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun i hi => Nat.not_lt_zero _ hi)
  rw [hkill, Set.image_empty, Ideal.span_empty]

/-! ## §2. The eval-kill map and its kernel -/

/-- Evaluation killing the first `n` variables. -/
noncomputable def killEval (n : ℕ) :
    MvPolynomial (Fin d) κ →+* MvPolynomial (Fin d) κ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    fun i => if i.val < n then 0 else MvPolynomial.X i

/-- `killEval` kills `X i` for `i < n` and fixes it otherwise. -/
@[simp]
theorem killEval_X (n : ℕ) (i : Fin d) :
    killEval κ d n (MvPolynomial.X i)
      = if i.val < n then 0 else MvPolynomial.X i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- `killEval` fixes constants. -/
theorem killEval_C (n : ℕ) (a : κ) :
    killEval κ d n (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [killEval, MvPolynomial.eval₂Hom_C]

/-- The rung variable survives its own rung's evaluation. -/
theorem killEval_rung (n : ℕ) (h : n < d) :
    killEval κ d n (MvPolynomial.X (⟨n, h⟩ : Fin d))
      = MvPolynomial.X (⟨n, h⟩ : Fin d) := by
  rw [killEval_X]
  have hneg : ¬ (⟨n, h⟩ : Fin d).val < n := Nat.lt_irrefl n
  rw [ite_eq_right hneg]

/-- Easy direction: the evaluation kills the rung ideal. -/
theorem killEval_eq_zero_of_mem (n : ℕ) (f : MvPolynomial (Fin d) κ)
    (h : f ∈ towerIdeal κ d n) : killEval κ d n f = 0 := by
  refine Submodule.span_induction (p := fun x _ => killEval κ d n x = 0) ?_ ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i.val < n := hi
    rw [killEval_X, ite_eq_left hi']
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- Hard direction, difference form: `f - E f` lies in the rung ideal. -/
theorem killEval_sub_mem (n : ℕ) (f : MvPolynomial (Fin d) κ) :
    f - killEval κ d n f ∈ towerIdeal κ d n := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      rw [killEval_C, sub_self]
      exact Submodule.zero_mem _
  | add p q ihp ihq =>
      have hmap : killEval κ d n (p + q)
        = killEval κ d n p + killEval κ d n q := map_add _ _ _
      rw [hmap, add_sub_add_comm]
      exact add_mem ihp ihq
  | mul_X p i ihp =>
      have hmap : killEval κ d n (p * MvPolynomial.X i)
        = killEval κ d n p * killEval κ d n (MvPolynomial.X i) :=
        map_mul _ _ _
      rw [hmap, killEval_X]
      by_cases hi : i.val < n
      · rw [ite_eq_left hi, mul_zero, sub_zero]
        have hmem : MvPolynomial.X i ∈ towerIdeal κ d n :=
          Submodule.subset_span ⟨i, hi, rfl⟩
        rw [← smul_eq_mul]
        exact Submodule.smul_mem _ _ hmem
      · rw [ite_eq_right hi, ← sub_mul, mul_comm, ← smul_eq_mul]
        exact Submodule.smul_mem _ _ ihp

/-- Hard direction: the kernel of the evaluation is the rung ideal. -/
theorem mem_towerIdeal_of_killEval_eq_zero (n : ℕ) (f : MvPolynomial (Fin d) κ)
    (h : killEval κ d n f = 0) : f ∈ towerIdeal κ d n := by
  have hsub := killEval_sub_mem κ d n f
  rw [h, sub_zero] at hsub
  exact hsub

/-! ## §3. The rung scalar and var-regularity -/

/-- The rung scalar: the `n`-th variable (zero past the last rung). -/
noncomputable def rungScalar (n : ℕ) : MvPolynomial (Fin d) κ :=
  if h : n < d then MvPolynomial.X (⟨n, h⟩ : Fin d) else 0

/-- The rung variable. -/
noncomputable def rungVar (n : ℕ) (h : n < d) : MvPolynomial (Fin d) κ :=
  MvPolynomial.X (⟨n, h⟩ : Fin d)

/-- The rung scalar at a valid rung is the rung variable. -/
theorem rungScalar_eq (n : ℕ) (h : n < d) :
    rungScalar κ d n = rungVar κ d n h :=
  dite_eq_left h

/-- Scalar action on a rung quotient, on representatives. -/
theorem quot_smul_mkQ (J : Ideal (MvPolynomial (Fin d) κ))
    (x f : MvPolynomial (Fin d) κ) :
    x • (Submodule.mkQ (J : Submodule _ _)) f
      = (Submodule.mkQ (J : Submodule _ _)) (x * f) := by
  rw [← map_smul, smul_eq_mul]

/-- Vanishing on a rung quotient means ideal membership. -/
theorem mkQ_eq_zero_iff (J : Ideal (MvPolynomial (Fin d) κ))
    (f : MvPolynomial (Fin d) κ) :
    (Submodule.mkQ (J : Submodule _ _)) f = 0 ↔ f ∈ J := by
  change (Ideal.Quotient.mk J) f = 0 ↔ f ∈ J
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Var-regularity per rung: the rung variable is regular on its quotient,
by the eval-kill section into the polynomial domain. -/
theorem tower_var_regular (n : ℕ) (h : n < d)
    (q : MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n)
    (hq : rungVar κ d n h • q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
    (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)) q
  rw [quot_smul_mkQ] at hq
  have hmem : rungVar κ d n h * f ∈ towerIdeal κ d n :=
    (mkQ_eq_zero_iff κ d _ _).mp hq
  have hE : killEval κ d n (rungVar κ d n h * f) = 0 :=
    killEval_eq_zero_of_mem κ d n _ hmem
  have hrung : killEval κ d n (rungVar κ d n h) = rungVar κ d n h :=
    killEval_rung κ d n h
  rw [map_mul, hrung] at hE
  have hX : rungVar κ d n h ≠ (0 : MvPolynomial (Fin d) κ) :=
    MvPolynomial.X_ne_zero _
  have hEf : killEval κ d n f = 0 := (mul_eq_zero.mp hE).resolve_left hX
  have hfJ : f ∈ towerIdeal κ d n :=
    mem_towerIdeal_of_killEval_eq_zero κ d n f hEf
  exact (mkQ_eq_zero_iff κ d _ _).mpr hfJ

/-- Var-regularity in rung-scalar form (the file-4 `hreg` input). -/
theorem tower_hreg (n : ℕ) (h : n < d)
    (q : MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n)
    (hq : rungScalar κ d n • q = 0) : q = 0 := by
  rw [rungScalar_eq κ d n h] at hq
  exact tower_var_regular κ d n h q hq

/-! ## §4. The rung quotient map -/

/-- Each tower ideal is contained in the next: the side condition for
`towerMap`. -/
theorem towerMap_le (n : ℕ) :
    (towerIdeal κ d n : Submodule _ _)
      ≤ Submodule.comap LinearMap.id
        (towerIdeal κ d (n + 1) : Submodule _ _) := by
  simpa using towerIdeal_mono κ d n

/-- The rung quotient map. -/
noncomputable def towerMap (n : ℕ) (_ : n < d) :
    (MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n)
      →ₗ[MvPolynomial (Fin d) κ]
      (MvPolynomial (Fin d) κ ⧸ towerIdeal κ d (n + 1)) :=
  Submodule.mapQ (p := (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
    (q := (towerIdeal κ d (n + 1) : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
    (f := (LinearMap.id : MvPolynomial (Fin d) κ
      →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ))
    (h := towerMap_le κ d n)

/-- `towerMap` acts as the identity on representatives. -/
theorem towerMap_mkQ (n : ℕ) (h : n < d) (f : MvPolynomial (Fin d) κ) :
    towerMap κ d n h ((Submodule.mkQ _) f) = (Submodule.mkQ _) f := by
  have hcomp := Submodule.mapQ_mkQ (p := (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
    (q := (towerIdeal κ d (n + 1) : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
    (f := (LinearMap.id : MvPolynomial (Fin d) κ
      →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ))
    (h := towerMap_le κ d n)
  have happ := congrArg (fun L : MvPolynomial (Fin d) κ
    →ₗ[MvPolynomial (Fin d) κ]
      (MvPolynomial (Fin d) κ ⧸ towerIdeal κ d (n + 1)) =>
    L f) hcomp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply] at happ
  exact happ

/-- The file-4 `hsurjπ` input. -/
theorem tower_hsurjπ (n : ℕ) (h : n < d) :
    Function.Surjective (towerMap κ d n h) := by
  intro y
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
    (towerIdeal κ d (n + 1) : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)) y
  exact ⟨(Submodule.mkQ _) f, towerMap_mkQ κ d n h f⟩

/-- The file-4 `hxQ` input. -/
theorem tower_hxQ (n : ℕ) (h : n < d)
    (q : MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n) :
    towerMap κ d n h (rungScalar κ d n • q) = 0 := by
  rw [rungScalar_eq κ d n h]
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [quot_smul_mkQ κ d, towerMap_mkQ κ d n h, mkQ_eq_zero_iff κ d]
  have hX : MvPolynomial.X (⟨n, h⟩ : Fin d) ∈ towerIdeal κ d (n + 1) :=
    Submodule.subset_span ⟨⟨n, h⟩, Nat.lt_succ_self n, rfl⟩
  rw [mul_comm, ← smul_eq_mul]
  exact Submodule.smul_mem _ _ hX

/-- The file-4 `hkerπ` input. -/
theorem tower_hkerπ (n : ℕ) (h : n < d)
    (q : MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n)
    (hq : towerMap κ d n h q = 0) :
    ∃ t, rungScalar κ d n • t = q := by
  rw [rungScalar_eq κ d n h]
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
    (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)) q
  rw [towerMap_mkQ κ d n h] at hq
  have hmem : f ∈ towerIdeal κ d (n + 1) := (mkQ_eq_zero_iff κ d _ _).mp hq
  rw [towerIdeal_succ κ d n h] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  rw [mul_comm] at hc
  have hc' : rungVar κ d n h * c = a := hc
  have hb0 : (Submodule.mkQ (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ))) b = 0 :=
    (mkQ_eq_zero_iff κ d _ _).mpr hb
  refine ⟨(Submodule.mkQ _) c, ?_⟩
  rw [quot_smul_mkQ κ d]
  have hcongr : (Submodule.mkQ (towerIdeal κ d n : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ))) f
    = (Submodule.mkQ _) (rungVar κ d n h * c) := by
    rw [← hab, map_add, hb0, add_zero, ← hc']
  exact hcongr.symm

/-! ## §5. The base case -/

/-- Higher exterior powers of the empty module vanish. -/
theorem exterior_succ_eq (j : ℕ)
    (a b : ↥(⋀[MvPolynomial (Fin d) κ]^(j + 1)
      (Fin 0 → MvPolynomial (Fin d) κ))) : a = b := by
  have hspan : Submodule.span (MvPolynomial (Fin d) κ)
      (Set.range (ExteriorAlgebra.ιMulti (MvPolynomial (Fin d) κ) (j + 1) :
        (Fin (j + 1) → (Fin 0 → MvPolynomial (Fin d) κ)) → _))
      = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    have hv0 : v 0 = 0 := funext fun i => (Nat.not_lt_zero _ i.2).elim
    have hmem : ExteriorAlgebra.ιMulti (MvPolynomial (Fin d) κ) j.succ v
        ∈ (⊥ : Submodule (MvPolynomial (Fin d) κ)
          (ExteriorAlgebra (MvPolynomial (Fin d) κ)
            (Fin 0 → MvPolynomial (Fin d) κ))) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, hv0, map_zero, zero_mul]
      exact Submodule.zero_mem _
    exact hmem
  have hbot : (⋀[MvPolynomial (Fin d) κ]^(j + 1)
      (Fin 0 → MvPolynomial (Fin d) κ)) = ⊥ := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact hspan
  apply Subtype.ext
  have hval : ∀ x : ExteriorAlgebra (MvPolynomial (Fin d) κ)
      (Fin 0 → MvPolynomial (Fin d) κ),
      x ∈ ⋀[MvPolynomial (Fin d) κ]^(j + 1)
        (Fin 0 → MvPolynomial (Fin d) κ) → x = 0 := by
    intro x hx
    rw [hbot] at hx
    exact (Submodule.mem_bot _).mp hx
  rw [hval _ a.2, hval _ b.2]

/-- Base augmentation: degree 0 is the scalars, mapped to the base quotient. -/
noncomputable def baseAug :
    ↥(⋀[MvPolynomial (Fin d) κ]^0 (Fin 0 → MvPolynomial (Fin d) κ))
      →ₗ[MvPolynomial (Fin d) κ]
      (MvPolynomial (Fin d) κ ⧸ towerIdeal κ d 0) :=
  (Submodule.mkQ _).comp (exteriorPower.zeroEquiv _ _).toLinearMap

/-- The base augmentation is injective: the rung-`0` tower ideal is trivial
(`towerIdeal_zero`), so `mkQ` after `zeroEquiv` kills only `0`. -/
theorem baseAug_injective
    (b : ↥(⋀[MvPolynomial (Fin d) κ]^0 (Fin 0 → MvPolynomial (Fin d) κ)))
    (hb : baseAug κ d b = 0) : b = 0 := by
  have hmem : (exteriorPower.zeroEquiv _ _ b) ∈ towerIdeal κ d 0 := by
    have h0 : (Submodule.mkQ (towerIdeal κ d 0 : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
        ((exteriorPower.zeroEquiv _ _ b)) = 0 := hb
    exact (mkQ_eq_zero_iff κ d _ _).mp h0
  rw [towerIdeal_zero κ d, Submodule.mem_bot] at hmem
  have h0 : (exteriorPower.zeroEquiv (MvPolynomial (Fin d) κ)
      (Fin 0 → MvPolynomial (Fin d) κ)) b
    = (exteriorPower.zeroEquiv (MvPolynomial (Fin d) κ)
      (Fin 0 → MvPolynomial (Fin d) κ)) 0 := by rw [hmem, map_zero]
  exact (exteriorPower.zeroEquiv (MvPolynomial (Fin d) κ)
    (Fin 0 → MvPolynomial (Fin d) κ)).injective h0

/-- Exactness at the tower base: over `Fin 0` every positive exterior power
vanishes, so every cycle is a boundary. -/
theorem base_exact (j : ℕ) :
    contractExactAt (0 : (Fin 0 → MvPolynomial (Fin d) κ)
      →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ) j := by
  intro z _
  have h0 : z = 0 := exterior_succ_eq κ d j z 0
  exact ⟨0, by rw [map_zero]; exact h0.symm⟩

/-- Augmented exactness at the tower base: the kernel of `baseAug` is the
image of the differential, via `baseAug_injective`. -/
theorem base_aug : contractAugExactZero
    (0 : (Fin 0 → MvPolynomial (Fin d) κ)
      →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ)
    (baseAug κ d) := by
  refine ⟨?_, ?_⟩
  · intro a
    have ha0 : a = 0 := exterior_succ_eq κ d 0 a 0
    rw [ha0, map_zero, map_zero]
  · intro b hb
    have hb0 : b = 0 := baseAug_injective κ d b hb
    exact ⟨0, by rw [map_zero]; exact hb0.symm⟩

/-- The base augmentation is surjective, since `Submodule.mkQ` is. -/
theorem base_surj : Function.Surjective (baseAug κ d) := by
  intro y
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
    (towerIdeal κ d 0 : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)) y
  obtain ⟨b, hb⟩ := (exteriorPower.zeroEquiv (MvPolynomial (Fin d) κ)
    (Fin 0 → MvPolynomial (Fin d) κ)).surjective f
  refine ⟨b, ?_⟩
  have hcomp : baseAug κ d b
      = (Submodule.mkQ (towerIdeal κ d 0 : Submodule (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)))
        ((exteriorPower.zeroEquiv (MvPolynomial (Fin d) κ)
          (Fin 0 → MvPolynomial (Fin d) κ)) b) := rfl
  rw [hcomp, hb]

/-! ## §6. The tower and the master theorem -/

/-- The Koszul module tower: products growing by one factor per rung. -/
abbrev towerMod : ℕ → Type _
  | 0 => Fin 0 → MvPolynomial (Fin d) κ
  | n + 1 => towerMod n × MvPolynomial (Fin d) κ

/-- Pointwise additive group structure on each tower module (`Pi` at
rung `0`, product above). -/
noncomputable instance towerModAddCommGroup :
    ∀ n : ℕ, AddCommGroup (towerMod κ d n)
  | 0 => Pi.addCommGroup
  | n + 1 => @Prod.instAddCommGroup _ _ (towerModAddCommGroup n) _

/-- Pointwise module structure on each tower module (`Pi` at rung `0`,
product above). -/
noncomputable instance towerModModule :
    ∀ n : ℕ, Module (MvPolynomial (Fin d) κ) (towerMod κ d n)
  | 0 => Pi.Function.module (Fin 0) (MvPolynomial (Fin d) κ)
      (MvPolynomial (Fin d) κ)
  | n + 1 =>
      @Prod.instModule _ _ _ _ _ _ (towerModModule n) _

/-- The Koszul differential functional tower. -/
noncomputable def towerPhi :
    ∀ n : ℕ, (towerMod κ d n)
      →ₗ[MvPolynomial (Fin d) κ] MvPolynomial (Fin d) κ
  | 0 => 0
  | n + 1 => (towerPhi n).comp
      (LinearMap.fst (MvPolynomial (Fin d) κ) (towerMod κ d n)
        (MvPolynomial (Fin d) κ))
      + rungScalar κ d n • (LinearMap.snd (MvPolynomial (Fin d) κ)
        (towerMod κ d n) (MvPolynomial (Fin d) κ))

/-- The rung functional splits as required by the file-4 step. -/
theorem towerPhi_succ (n : ℕ) (p : towerMod κ d (n + 1)) :
    towerPhi κ d (n + 1) p
      = towerPhi κ d n p.1 + rungScalar κ d n * p.2 := by
  simp only [towerPhi, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The augmentation tower, via the file-4 step augmentation. -/
noncomputable def towerAug : ∀ (n : ℕ) (_ : n ≤ d),
    ↥(⋀[MvPolynomial (Fin d) κ]^0 (towerMod κ d n))
      →ₗ[MvPolynomial (Fin d) κ]
      (MvPolynomial (Fin d) κ ⧸ towerIdeal κ d n)
  | 0, _ => baseAug κ d
  | n + 1, h => koszulStepAug (towerAug n (by omega)) (towerMap κ d n (by omega))

/-- The rung package: exactness plus augmentation plus surjectivity. -/
def towerPackage (n : ℕ) (h : n ≤ d) : Prop :=
  (∀ j, contractExactAt (towerPhi κ d n) j)
    ∧ contractAugExactZero (towerPhi κ d n) (towerAug κ d n h)
    ∧ Function.Surjective (towerAug κ d n h)

/-- The tower package holds at rung `0`: exactness, augmented exactness,
and surjectivity from the base lemmas. -/
theorem tower_base : towerPackage κ d 0 (Nat.zero_le d) := by
  change (∀ j, contractExactAt (towerPhi κ d 0) j) ∧ _ ∧ _
  exact ⟨base_exact κ d, base_aug κ d, base_surj κ d⟩

/-- The tower package propagates across one rung, via the master
short-exact-sequence step. -/
theorem tower_step (n : ℕ) (h : n + 1 ≤ d)
    (ih : towerPackage κ d n (Nat.le_of_succ_le h)) :
    towerPackage κ d (n + 1) h := by
  obtain ⟨hexact, haug, hsurj⟩ := ih
  have hlt : n < d := by omega
  have hreg : ∀ q : MvPolynomial (Fin d) κ
      ⧸ towerIdeal κ d n,
      rungScalar κ d n • q = 0 → q = 0 :=
    fun q hq => tower_hreg κ d n hlt q hq
  have hmaster := koszulStep_augmented_exact
    (φ := towerPhi κ d (n + 1)) (φ' := towerPhi κ d n) (x := rungScalar κ d n)
    (phi_split := fun p => towerPhi_succ κ d n p)
    (ε' := towerAug κ d n (Nat.le_of_succ_le h)) (π := towerMap κ d n hlt)
    hexact haug hsurj hreg
    (tower_hxQ κ d n hlt) (tower_hkerπ κ d n hlt) (tower_hsurjπ κ d n hlt)
  exact hmaster

/-- The tower package holds at every rung `n ≤ d`, by induction from
`tower_base` via `tower_step`. -/
theorem tower_package_all (n : ℕ) (h : n ≤ d) : towerPackage κ d n h := by
  revert h
  induction n with
  | zero =>
      intro h
      exact tower_base κ d
  | succ n ih =>
      intro h
      exact tower_step κ d n h (ih (Nat.le_of_succ_le h))

/-- The top kill set is everything. -/
theorem killSet_top : killSet d d = Set.univ := by
  ext i
  change i.val < d ↔ True
  exact ⟨fun _ => trivial, fun _ => i.2⟩

/-- The top rung ideal is the full variable span. -/
theorem towerIdeal_top :
    towerIdeal κ d d = Ideal.span (Set.range MvPolynomial.X) := by
  rw [towerIdeal, killSet_top d, Set.image_univ]

/-- Master: augmented Koszul exactness over `κ[X]`, in the exact shape file 6
(`GradedLift`) consumes. -/
theorem koszul_poly_augmented_exact :
    (∀ j, contractExactAt (towerPhi κ d d) j)
      ∧ contractAugExactZero (towerPhi κ d d) (towerAug κ d d (le_refl d))
      ∧ Function.Surjective (towerAug κ d d (le_refl d)) :=
  tower_package_all κ d d (le_refl d)

#print axioms koszul_poly_augmented_exact
#print axioms tower_var_regular

end PolynomialExactness
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

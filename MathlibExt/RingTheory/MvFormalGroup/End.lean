/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`Definitions/Def_MvFormalGroup_BasicV2.lean`,
`Definitions/Def_MvFormalGroup_EndRingV2.lean`,
`P2M/Sol/S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.lean`,
`P2M/Sol/S_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric.lean`, and
`P2M/Sol/S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq.lean`
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

public import MathlibExt.RingTheory.MvFormalGroup.Hom

/-!
# Endomorphisms of multivariate formal group laws

The endomorphisms `MvFormalGroup.End F` of a formal group law form a monoid under composition, and
a semiring when `F` is commutative, in which the natural number `n` is the `n`-series. The linear
part of an endomorphism is a ring homomorphism to matrices (`MvFormalGroup.linearPartHom`).
-/

@[expose] public section

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

/-- Endomorphisms of a formal group law. -/
def End (F : MvFormalGroup g R) := Hom F F

namespace End

variable (F : MvFormalGroup g R)

instance instMonoid : Monoid (End F) where
  mul φ ψ := Hom.comp φ ψ
  one := Hom.id F
  mul_assoc φ ψ χ := by
    apply Hom.ext
    funext i
    change subst (Hom.toPowerSeries χ) (subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i))
      = subst (fun j => subst (Hom.toPowerSeries χ) (Hom.toPowerSeries ψ j))
        (Hom.toPowerSeries φ i)
    rw [subst_comp_subst_apply (Hom.hasSubst_toPowerSeries ψ)
      (Hom.hasSubst_toPowerSeries χ)]
  one_mul φ := by
    apply Hom.ext
    funext i
    change subst (Hom.toPowerSeries φ) (X i) = Hom.toPowerSeries φ i
    exact subst_X (Hom.hasSubst_toPowerSeries φ) i
  mul_one φ := by
    apply Hom.ext
    funext i
    change subst (fun j => (X j : MvPowerSeries (Fin g) R)) (Hom.toPowerSeries φ i)
      = Hom.toPowerSeries φ i
    exact congrFun subst_self (Hom.toPowerSeries φ i)

@[simp]
theorem toPowerSeries_one :
    Hom.toPowerSeries (1 : End F) = fun i => (X i : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_mul (φ ψ : End F) :
    Hom.toPowerSeries (φ * ψ)
      = fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i) := rfl

instance instAddCommMonoid [IsComm F] : AddCommMonoid (End F) :=
  inferInstanceAs (AddCommMonoid (Hom F F))

instance instSemiring [IsComm F] : Semiring (End F) :=
  { End.instAddCommMonoid F, End.instMonoid F with
    left_distrib := fun a b c => by
      apply Hom.ext
      funext i
      change subst (fun j => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          (F.toPowerSeries j)) (Hom.toPowerSeries a i)
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
          (F.toPowerSeries i)
      have hbc : HasSubst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero b) (Hom.constantCoeff_eq_zero c)
      have hXl : HasSubst (fun l : Fin g =>
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hXr : HasSubst (fun l : Fin g =>
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have haLR : HasSubst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j)) :=
        hasSubst_elim
          (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j))
          fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j)
      rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries hbc, Hom.subst_eq a i,
        subst_comp_subst_apply haLR hbc]
      have hbfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inl l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries b := by
        funext l
        change subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inl l)) = Hom.toPowerSeries b l
        rw [subst_X hbc]
        rfl
      have hcfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inr l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries c := by
        funext l
        change subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inr l)) = Hom.toPowerSeries c l
        rw [subst_X hbc]
        rfl
      have hfam : (fun s => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j) := by
        funext s
        rcases s with j | j
        · change subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXl hbc, hbfam]
        · change subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXr hbc, hcfam]
      rw [hfam]
    right_distrib := fun a b c => by
      apply Hom.ext
      funext i
      change subst (Hom.toPowerSeries c)
          (subst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b))
            (F.toPowerSeries i))
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j))
          (F.toPowerSeries i)
      have hab : HasSubst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero a) (Hom.constantCoeff_eq_zero b)
      rw [subst_comp_subst_apply hab (Hom.hasSubst_toPowerSeries c)]
      have hfam : (fun s => subst (Hom.toPowerSeries c)
          ((Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [hfam]
    zero_mul := fun a => by
      apply Hom.ext
      funext i
      change subst (Hom.toPowerSeries a) (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom (Hom.hasSubst_toPowerSeries a), map_zero]
    mul_zero := fun a => by
      apply Hom.ext
      funext i
      change subst (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          (Hom.toPowerSeries a i) = 0
      exact subst_zero_of_constantCoeff_eq_zero (Hom.constantCoeff_eq_zero a i) }

@[simp]
theorem toPowerSeries_natCast [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((n : End F)) = F.nthSeries n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, nthSeries_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ]
    funext i
    change subst (Sum.elim (Hom.toPowerSeries ((n : End F)))
        (Hom.toPowerSeries (1 : End F))) (F.toPowerSeries i)
      = F.nthSeries (n + 1) i
    rw [ih, nthSeries_succ]
    rfl

@[simp]
theorem toPowerSeries_zero [IsComm F] :
    Hom.toPowerSeries (0 : End F) = fun _ => (0 : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_add [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ + ψ)
      = fun i => subst (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ))
        (F.toPowerSeries i) := rfl

end End

/-- The linear part of an endomorphism, as a ring homomorphism to matrices. -/
def linearPartHom (F : MvFormalGroup g R) [IsComm F] :
    End F →+* Matrix (Fin g) (Fin g) R where
  toFun φ := linearPart (Hom.toPowerSeries φ)
  map_one' := by
    change linearPart (fun i => (X i : MvPowerSeries (Fin g) R)) = 1
    exact linearPart_X
  map_mul' φ ψ := by
    change linearPart (fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i)) = _
    exact linearPart_subst (Hom.constantCoeff_eq_zero ψ) (Hom.toPowerSeries φ)
  map_zero' := by
    change linearPart (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) = 0
    exact linearPart_zero
  map_add' φ ψ := by
    change linearPart (fun i => subst
        (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ)) (F.toPowerSeries i)) = _
    exact linearPart_subst_elim F (Hom.constantCoeff_eq_zero φ)
      (Hom.constantCoeff_eq_zero ψ)

@[simp]
theorem linearPartHom_apply (F : MvFormalGroup g R) [IsComm F] (φ : End F) :
    linearPartHom F φ = linearPart (Hom.toPowerSeries φ) := rfl

@[simp]
theorem linearPartHom_natCast (F : MvFormalGroup g R) [IsComm F] (n : ℕ) :
    linearPartHom F ((n : End F)) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [linearPartHom_apply, End.toPowerSeries_natCast, linearPart_nthSeries]

end MvFormalGroup

end

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Basic
public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Amplification
public import Batteries.Data.Vector.Lemmas
import Mathlib.Tactic

/-!
# A sharp binary Freivalds example

For the one-by-one inputs `A = B = [1]` and `C = [0]`, the actual trial
accepts precisely the zero seed. This supplies the boundary example for the
one-half error bound in MIT 6.046J Spring 2015 Lecture 6, printed page 2.
All matrices and arithmetic here are over `ZMod 2` by intentional GF(2) specialization (see
`Freivalds.Basic`); the lecture itself only takes the seed vector binary over a general
coefficient domain.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open scoped ENNReal

@[expose] public section

namespace Cslib.Algorithms.Lean.Matrix

/-- **The sharp Freivalds example has a wrong product.** Let $A = B = (1)$ and $C = (0)$ be
$1 \times 1$ matrices over $\mathbb{Z}/2\mathbb{Z}$. Then $AB \neq C$. -/
theorem freivalds_one_wrong :
    freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2))) *
      freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2))) ≠
      freivaldsMatrix
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) := by
  intro equal
  have first := congrFun (congrFun equal 0) 0
  simp [freivaldsMatrix, _root_.Matrix.mul_apply, _root_.Vector.get_replicate] at first

/-- **The sharp Freivalds example accepts exactly the zero seed.** Let $A = B = (1)$ and
$C = (0)$ be $1 \times 1$ matrices over $\mathbb{Z}/2\mathbb{Z}$. For every seed
$r \in (\mathbb{Z}/2\mathbb{Z})^1$, the Freivalds trial on $A$, $B$, $C$ with seed $r$, which
compares $A(Br)$ with $Cr$, accepts if and only if the single entry $r_0$ of $r$ is $0$. -/
theorem freivaldsTrial_one_accept_iff (r : Fin 1 → ZMod 2) :
    (freivaldsTrial
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true ↔
        r 0 = 0 := by
  rw [freivaldsTrial_accept_iff]
  constructor
  · intro equal
    have first := congrFun equal 0
    simpa [freivaldsMatrix, _root_.Matrix.mulVec_apply_eq_sum,
      _root_.Vector.get_replicate] using first
  · intro zero
    funext i
    have index : i = 0 := Subsingleton.elim i 0
    subst i
    simp [freivaldsMatrix, _root_.Matrix.mulVec_apply_eq_sum, zero]

/-- **The sharp Freivalds example has exactly one accepted seed.** Let $A = B = (1)$ and
$C = (0)$ be $1 \times 1$ matrices over $\mathbb{Z}/2\mathbb{Z}$. Exactly one seed
$r \in (\mathbb{Z}/2\mathbb{Z})^1$ is accepted by the Freivalds trial on $A$, $B$, $C$. -/
theorem freivaldsTrial_one_acceptanceCard :
    Fintype.card {r : Fin 1 → ZMod 2 //
      (freivaldsTrial
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true} =
      1 := by
  classical
  let _ : Unique {r : Fin 1 → ZMod 2 //
      (freivaldsTrial
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
        (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) r).ret = true} := {
    default := ⟨fun _ => 0, (freivaldsTrial_one_accept_iff (fun _ => 0)).mpr rfl⟩
    uniq := by
      intro r
      apply Subtype.ext
      funext i
      have index : i = 0 := Subsingleton.elim i 0
      subst i
      exact (freivaldsTrial_one_accept_iff r.val).mp r.property
  }
  exact Fintype.card_unique

/-- **The sharp Freivalds example is accepted with probability one half.** Let $A = B = (1)$
and $C = (0)$ be $1 \times 1$ matrices over $\mathbb{Z}/2\mathbb{Z}$. When the seed is drawn
uniformly from $(\mathbb{Z}/2\mathbb{Z})^1$, the Freivalds trial on $A$, $B$, $C$ accepts with
probability exactly $1/2$.

Since $AB \neq C$, this shows that the bound $1/2$ on the probability that one trial accepts a
wrong product cannot be improved. -/
theorem freivaldsTrialLaw_one_sharp :
    freivaldsTrialLaw
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) true =
        (1 : ℝ≥0∞) / 2 := by
  rw [freivaldsTrialLaw_acceptance, freivaldsTrial_one_acceptanceCard]
  simp

/-- **Exact acceptance probability of repeated trials on the sharp Freivalds example.** Let
$A = B = (1)$ and $C = (0)$ be $1 \times 1$ matrices over $\mathbb{Z}/2\mathbb{Z}$, and let $k$
be a natural number. Run $k$ Freivalds trials on $A$, $B$, $C$ with seeds drawn independently and
uniformly from $(\mathbb{Z}/2\mathbb{Z})^1$, accepting exactly when every trial accepts. Then the
run accepts with probability exactly $2^{-k}$.

Since $AB \neq C$, the bound $2^{-k}$ on the probability that $k$ trials accept a wrong product
cannot be improved. -/
theorem freivaldsRepeatLaw_one_sharp (k : Nat) :
    freivaldsRepeatLaw k
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (1 : ZMod 2)))
      (_root_.Vector.replicate 1 (_root_.Vector.replicate 1 (0 : ZMod 2))) true =
        ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [freivaldsRepeatLaw_acceptance_power, freivaldsTrialLaw_one_sharp]
  simp [div_eq_mul_inv, ENNReal.inv_pow]

end Cslib.Algorithms.Lean.Matrix

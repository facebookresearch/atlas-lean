/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-parameter groups in `GL_n (ℂ)`

A **one-parameter group** in `GL_n (ℂ)` is a differentiable homomorphism
`φ : ℝ → GL_n (ℂ)` from the additive group `ℝ`. This file proves that every
such group is the exponential of a fixed matrix: there is a unique matrix `A`
with `φ t = exp (t • A)` for all `t`, and conversely every exponential curve
of this form is a one-parameter group.

For a subgroup `G ≤ GL_n (ℂ)`, `IsOneParameterGroupIn G φ` additionally requires
`φ t ∈ G` for every real `t`. The canonical lift `IsOneParameterGroup.toGL`
turns a matrix-valued one-parameter group into a `GL_n (ℂ)`-valued curve.

The proof differentiates the homomorphism law to get the linear ODE
`φ'(s) = A * φ(s)` with `A = φ'(0)`, and concludes by Grönwall uniqueness:
`φ - exp (· • A)` satisfies the same homogeneous ODE with initial value `0`.

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` (targets
`SimpleGroups.IsOneParameterGroup` and `SimpleGroups.one_param_subgroup_form`
in `v1/Atlas/AlgebraNotes/targets.yaml` / `report.json`). The subgroup-relative
definition is represented by `IsOneParameterGroupIn`.
-/

@[expose] public section

namespace OneParameterGroup

/-- **One-parameter group of complex matrices.** For $m \in \mathbb{N}$, a map
$\varphi \colon \mathbb{R} \to M_m(\mathbb{C})$ into the complex $m \times m$ matrices is a
one-parameter group when $\varphi(0)$ is the identity matrix $I$,
$\varphi(s + t) = \varphi(s)\,\varphi(t)$ for all real $s$ and $t$, and $\varphi$ is
differentiable.

Such a map takes values in $\mathrm{GL}_m(\mathbb{C})$, since $\varphi(t)\,\varphi(-t) = I$. -/
structure IsOneParameterGroup (m : ℕ) (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) : Prop where
  /-- `φ 0 = 1`: the identity maps to the identity matrix. -/
  map_zero : φ 0 = 1
  /-- `φ (s + t) = φ s * φ t`: the homomorphism law. -/
  map_add : ∀ s t : ℝ, φ (s + t) = φ s * φ t
  /-- `φ` is differentiable (for the entrywise topology on matrices). -/
  differentiable : Differentiable ℝ φ

/-- **One-parameter group in a subgroup of the general linear group.** Let $m \in \mathbb{N}$
and let $G$ be a subgroup of $\mathrm{GL}_m(\mathbb{C})$. A map
$\varphi \colon \mathbb{R} \to \mathrm{GL}_m(\mathbb{C})$ is a one-parameter group in $G$ when
the matrix-valued map $t \mapsto \varphi(t)$ is a one-parameter group and $\varphi(t) \in G$ for
every real $t$. -/
structure IsOneParameterGroupIn {m : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℂ))
    (φ : ℝ → Matrix.GeneralLinearGroup (Fin m) ℂ) : Prop
    extends IsOneParameterGroup m (fun t => (φ t : Matrix (Fin m) (Fin m) ℂ)) where
  /-- Every value of the curve lies in `G`. -/
  mem : ∀ t : ℝ, φ t ∈ G

/-- **The lift of a one-parameter group to the general linear group.** Let $m \in \mathbb{N}$ and
let $\varphi \colon \mathbb{R} \to M_m(\mathbb{C})$ be a one-parameter group of complex
$m \times m$ matrices. For every real $t$ the matrix $\varphi(t)$ is invertible with inverse
$\varphi(-t)$; this gives the element of $\mathrm{GL}_m(\mathbb{C})$ with matrix $\varphi(t)$
and inverse $\varphi(-t)$. -/
def IsOneParameterGroup.toGL {m : ℕ} {φ : ℝ → Matrix (Fin m) (Fin m) ℂ}
    (hφ : IsOneParameterGroup m φ) (t : ℝ) : Matrix.GeneralLinearGroup (Fin m) ℂ where
  val := φ t
  inv := φ (-t)
  val_inv := by rw [← hφ.map_add, add_neg_cancel, hφ.map_zero]
  inv_val := by rw [← hφ.map_add, neg_add_cancel, hφ.map_zero]

/-- **Underlying matrix of the lift of a one-parameter group.** Let $m \in \mathbb{N}$ and let
$\varphi \colon \mathbb{R} \to M_m(\mathbb{C})$ be a one-parameter group of complex $m \times m$
matrices. For every real $t$, the element of $\mathrm{GL}_m(\mathbb{C})$ assigned to $t$ by the
lift of $\varphi$ has underlying matrix $\varphi(t)$. -/
@[simp] theorem IsOneParameterGroup.coe_toGL {m : ℕ}
    {φ : ℝ → Matrix (Fin m) (Fin m) ℂ} (hφ : IsOneParameterGroup m φ) (t : ℝ) :
    (hφ.toGL t : Matrix (Fin m) (Fin m) ℂ) = φ t := rfl

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The derivative of the exponential curve `t ↦ exp (t • B)`. -/
private theorem hasDerivAt_exp_ofReal_smul {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((↑u : ℂ) • B))
      (NormedSpace.exp ((↑s : ℂ) • B) * B) s := by
  have ist : IsScalarTower ℝ ℂ (Matrix (Fin m) (Fin m) ℂ) := inferInstance
  have h2 := @HasDerivAt.scomp ℝ _ (Matrix (Fin m) (Fin m) ℂ) _ _ s ℂ _ _ _ ist _ _ _ _
    (hasDerivAt_exp_smul_const B (↑s : ℂ)) Complex.ofRealCLM.hasDerivAt
  convert h2 using 1 <;> first
    | rfl
    | (funext u; simp; rfl)

/-- **One-parameter groups of matrices are exponentials.** Let $m \in \mathbb{N}$. If
$\varphi \colon \mathbb{R} \to M_m(\mathbb{C})$ is a one-parameter group of complex $m \times m$
matrices, then there is a unique matrix $A \in M_m(\mathbb{C})$ such that
$\varphi(t) = \exp(tA)$ for every real $t$. -/
theorem one_param_subgroup_form (m : ℕ)
    (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) (hφ : IsOneParameterGroup m φ) :
    ∃! A : Matrix (Fin m) (Fin m) ℂ,
      ∀ t : ℝ, φ t = NormedSpace.exp ((↑t : ℂ) • A) := by
  set A := deriv φ 0
  have hφ_ode : ∀ s : ℝ, deriv φ s = A * φ s := by
    intro s
    have h : (fun u => φ (u + s)) = (fun u => φ u * φ s) := funext (fun u => hφ.map_add u s)
    calc deriv φ s = deriv φ (0 + s) := by ring_nf
      _ = deriv (fun u => φ (u + s)) 0 := (deriv_comp_add_const φ s 0).symm
      _ = deriv (fun u => φ u * φ s) 0 := by rw [h]
      _ = deriv φ 0 * φ s := (hφ.differentiable.differentiableAt.hasDerivAt.mul_const (φ s)).deriv
  set g : ℝ → Matrix (Fin m) (Fin m) ℂ := fun s => φ s - NormedSpace.exp ((↑s : ℂ) • A)
  have hg_diff : Differentiable ℝ g :=
    hφ.differentiable.sub (fun s => (hasDerivAt_exp_ofReal_smul A s).differentiableAt)
  have hg_zero : g 0 = 0 := by simp [g, hφ.map_zero, NormedSpace.exp_zero]
  have hg_ode : ∀ s : ℝ, deriv g s = A * g s := by
    intro s
    have hd := (hφ.differentiable s).hasDerivAt.sub (hasDerivAt_exp_ofReal_smul A s)
    have heq : deriv g s = deriv φ s - NormedSpace.exp ((↑s : ℂ) • A) * A := hd.deriv
    rw [heq, hφ_ode s, ((Commute.refl A).smul_left (↑s : ℂ)).exp_left.eq, mul_sub]
  have hg_eq_zero : ∀ t : ℝ, g t = 0 := by
    intro t
    by_cases ht : 0 ≤ t
    ·
      exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f' := fun x => deriv g x)
        hg_diff.continuous.continuousOn
        (fun x _ => (hg_diff x).hasDerivAt.hasDerivWithinAt)
        hg_zero
        (fun x _ => by rw [hg_ode x]; exact norm_mul_le A (g x))
        t ⟨ht, le_refl t⟩
    ·
      have ht' : t < 0 := not_le.mp ht
      have hh_diff : Differentiable ℝ (fun s => g (-s)) := hg_diff.comp differentiable_neg
      have hmem : -t ∈ Set.Icc 0 (-t) := ⟨by linarith, le_refl _⟩
      have h_eq := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
          (f' := fun x => deriv (fun s => g (-s)) x)
        hh_diff.continuous.continuousOn
        (fun x _ => (hh_diff x).hasDerivAt.hasDerivWithinAt)
        (show (fun s => g (-s)) 0 = 0 by simp [hg_zero])
        (fun x _ => by
          have hcomp : ∀ x : ℝ, deriv (fun s => g (-s)) x = -deriv g (-x) :=
            fun x => deriv_comp_neg g x
          rw [hcomp x, norm_neg, hg_ode (-x)]
          exact norm_mul_le A (g (-x)))
        (-t) hmem
      simpa using h_eq
  refine ⟨A, ?_, ?_⟩
  ·
    intro t; exact sub_eq_zero.mp (hg_eq_zero t)
  ·
    intro B hB
    have heq : (fun s : ℝ => φ s) = (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) :=
      funext hB
    have hB_deriv : deriv (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) 0 = B := by
      have h0 : NormedSpace.exp ((↑(0 : ℝ) : ℂ) • B) * B = B := by simp
      exact (hasDerivAt_exp_ofReal_smul B 0).deriv.trans h0
    calc B = deriv (fun s : ℝ => NormedSpace.exp ((↑s : ℂ) • B)) 0 := hB_deriv.symm
      _ = deriv (fun s : ℝ => φ s) 0 := by rw [← heq]
      _ = A := rfl

/-- **Exponential curves are one-parameter groups.** For every $m \in \mathbb{N}$ and every
complex $m \times m$ matrix $A$, the map $t \mapsto \exp(tA)$ from $\mathbb{R}$ to the complex
$m \times m$ matrices is a one-parameter group. -/
theorem isOneParameterGroup_exp_smul (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) :
    IsOneParameterGroup m (fun t => NormedSpace.exp ((↑t : ℂ) • A)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro s t
    have hcast : (↑(s + t) : ℂ) • A = (↑s : ℂ) • A + (↑t : ℂ) • A := by
      push_cast
      rw [add_smul]
    rw [hcast]
    exact NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left (↑s : ℂ)).smul_right (↑t : ℂ))
  · exact fun s => (hasDerivAt_exp_ofReal_smul A s).differentiableAt

end OneParamSubgroupTheorem

end OneParameterGroup

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.QuadraticForm.Round
public import MathlibExt.LinearAlgebra.QuadraticForm.PfisterSuccessor
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Roundness of diagonal quasi-Pfister forms

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). Roundness means that, for every nonzero c, c is
represented by qₐ if and only if cqₐ is isometric to qₐ. Every qₐ is round over an arbitrary
field. These diagonal forms are quasi-Pfister forms, including the zero-fold square form.
They coincide with quadratic Pfister forms when the characteristic is not two and are
totally singular in characteristic two.

## References

* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic
Forms*, Corollary 10.3 for quasi-Pfister forms in arbitrary characteristic; Corollary 9.9
for quadratic Pfister forms in characteristic different from two.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace QuadraticForm

variable (F : Type u) [Field F]

private def pfisterOneVector (n : ℕ) : Finset (Fin n) → F :=
  fun s => if s = ∅ then 1 else 0

private theorem pfister_oneVector
    {n : ℕ} (a : Fin n → Fˣ) :
    pfister F a (pfisterOneVector F n) = 1 := by
  classical
  rw [pfister_apply]
  simp [pfisterOneVector]

private theorem pfisterZero_isRound (a : Fin 0 → Fˣ) :
    (pfister F a).IsRound := by
  intro d hd
  constructor
  · rintro ⟨x, hx⟩
    let r : F := x ∅
    have hQr : pfister F a x = r * r := by
      rw [pfister_apply, Fintype.sum_unique]
      have hdefault : (default : Finset (Fin 0)) = ∅ :=
        Subsingleton.elim _ _
      rw [hdefault, pfisterWeight_empty]
      simp [r]
    have hr : r ≠ 0 := by
      intro hr
      apply hd
      rw [← hx, hQr, hr, zero_mul]
    have hrd : r * r = d := by
      rw [← hx, hQr]
    let eLin : (Finset (Fin 0) → F) ≃ₗ[F] (Finset (Fin 0) → F) :=
      LinearEquiv.piCongrRight (fun _ => LinearEquiv.smulOfNeZero F F r hr)
    refine ⟨{ toLinearEquiv := eLin, map_app' := ?_ }⟩
    intro z
    change pfister F a (eLin z) = d * pfister F a z
    rw [pfister_apply, pfister_apply,
      Fintype.sum_unique, Fintype.sum_unique]
    have hdefault : (default : Finset (Fin 0)) = ∅ :=
      Subsingleton.elim _ _
    rw [hdefault, pfisterWeight_empty]
    simp only [one_mul]
    have heval : eLin z ∅ = LinearEquiv.smulOfNeZero F F r hr (z ∅) := rfl
    rw [heval, LinearEquiv.smulOfNeZero_apply, smul_eq_mul, ← hrd]
    ring
  · rintro ⟨e⟩
    refine ⟨e (pfisterOneVector F 0), ?_⟩
    rw [e.map_app]
    change d * pfister F a (pfisterOneVector F 0) = d
    rw [pfister_oneVector]
    ring

/-- **Every diagonal quasi-Pfister form is round.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ₋₁ ∈ Fˣ. For s ⊆ Fin n put wₐ(s) = ∏ᵢ∈s (−aᵢ), and let
qₐ(x) = ∑ₛ wₐ(s)xₛ² on F^(Finset(Fin n)). For every c ≠ 0, there exists x with qₐ(x) = c if
and only if cqₐ is isometric to qₐ. This is Corollary 10.3 for quasi-Pfister forms over
arbitrary fields, and agrees with Corollary 9.9 for quadratic Pfister forms when 2 ≠ 0.
-/
theorem pfister_isRound {n : ℕ} (a : Fin n → Fˣ) :
    (pfister F a).IsRound := by
  induction n with
  | zero =>
      exact pfisterZero_isRound F a
  | succ n ih =>
      let lower : Fin n → Fˣ := fun i => a i.castSucc
      let c : F := a (Fin.last n)
      have hlower : (pfister F lower).IsRound := ih lower
      have hc : c ≠ 0 := Units.ne_zero (a (Fin.last n))
      have hprod :
          ((pfister F lower).prod ((-c) • pfister F lower)).IsRound :=
        hlower.prod_neg_smul c hc
      exact hprod.map_isometryEquiv (pfisterSuccEquiv F a).symm

end QuadraticForm

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FrickeGamma0
public import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

/-!
# The Fricke involution on cusp forms for `Γ₀(N)`

`MathlibExt.NumberTheory.ModularForms.FrickeGamma0` defines the Fricke matrix
`ModularForm.frickeGL N = W_N = !![0, -1; N, 0]` and the Fricke operator on
`ModularForm (Gamma0 N) k`. This file adds:

* `ModularForm.frickeGL_mul_mapGL_mul_inv`: for `γ = !![a, b; c, d] ∈ Γ₀(N)`, `W_N γ W_N⁻¹`
  is the image of an element of `Γ₀(N)` with entries `!![d, -c/N; -N b, a]`, making
  `ModularForm.exists_frickeGL_mul_eq` explicit;
* `ModularForm.toConjAct_frickeGL_inv_smul`: `W_N⁻¹ Γ₀(N) W_N = Γ₀(N)` in `GL(2, ℝ)`;
* `UpperHalfPlane.coe_frickeGL_smul`: `W_N • z = -1/(Nz)`;
* `CuspForm.fricke N k`: the Fricke operator `f ↦ f ∣[k] W_N` as a `ℂ`-linear map on
  `CuspForm (Gamma0 N) k`, from Mathlib's `CuspForm.translate` and `CuspForm.mcast`, with
  `CuspForm.fricke_apply_two`, `(f ∣[2] W_N)(z) = N⁻¹ z⁻² f(W_N • z)`, and
  `CuspForm.fricke_fricke_two`, `f ∣[2] W_N ∣[2] W_N = f`, from
  `ModularForm.slash_frickeGL_slash_frickeGL`;
* `ModularForm.fricke_involution_weight_two`, the three items of the statement that `W_N`
  normalises `Γ₀(N)` and acts on `S₂(Γ₀(N))` as an involution.

## References

* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University
  Press (1997), Chapter II, §2.4, pp. 18–19 of the author's online text
  (https://johncremona.github.io/book/fulltext/chapter2.pdf): the weight-two action
  `(f|M)(z) = (ad - bc)/(cz + d)² f((az + b)/(cz + d))`, and the Fricke involution `W_N` of
  `S₂(Γ₀(N))`, from `z ↦ -1/Nz`, with matrix `!![0, -1; N, 0]`.
* J. Coates, *The work of Gross and Zagier on Heegner points and the derivatives of
  `L`-series*, Séminaire Bourbaki, exp. 635 (1984/85), Astérisque 133–134 (1986), 57–72,
  p. 65, for the notation `w_N(z) = -1/(Nz)` and `f|₂w_N`. In the proof of Theorem 5 there,
  `f|₂w_N = f` is the eigenvalue `+1` of `w_N` on the primitive form `f` attached to an
  elliptic curve `E` whose `L(E, s)` has a simple zero at `s = 1`; it is not the involution
  `f ∣[2] W_N ∣[2] W_N = f` of every weight-two cusp form.
-/

@[expose] public section

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup ModularForm
open scoped MatrixGroups ModularForm Pointwise

namespace ModularForm

variable (N : ℕ) [NeZero N]

/-- **The Fricke matrix normalises `Γ₀(N)`, explicitly.** For `γ = !![a, b; c, d] ∈ Γ₀(N)`
there is `γ' ∈ Γ₀(N)` with `W_N γ W_N⁻¹ = γ'` in `GL(2, ℝ)` and `γ' = !![d, -c/N; -N b, a]`;
`W_N = ModularForm.frickeGL N`. -/
theorem frickeGL_mul_mapGL_mul_inv {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ γ' ∈ Gamma0 N,
      frickeGL N * SpecialLinearGroup.mapGL ℝ γ * (frickeGL N)⁻¹ =
        SpecialLinearGroup.mapGL ℝ γ' ∧
      ((SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(γ 1 1 : ℝ), -(γ 1 0 : ℝ) / N; -N * (γ 0 1 : ℝ), (γ 0 0 : ℝ)] := by
  obtain ⟨γ', hγ', heq⟩ := exists_frickeGL_mul_eq N hγ
  refine ⟨γ', hγ', by rw [heq, mul_inv_cancel_right], ?_⟩
  have hN : (N : ℝ) ≠ 0 := NeZero.ne _
  have hm := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ)) heq
  simp only [Units.val_mul, val_frickeGL, SpecialLinearGroup.mapGL_coe_matrix,
    SpecialLinearGroup.map_apply_coe] at hm
  have e00 : -(γ 1 0 : ℝ) = (γ' 0 1 : ℝ) * N := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 0
  have e01 : (γ 1 1 : ℝ) = γ' 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 1
  have e10 : (N : ℝ) * γ 0 0 = (γ' 1 1 : ℝ) * N := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 0
  have e11 : (N : ℝ) * γ 0 1 = -(γ' 1 0 : ℝ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 1
  have h00 : (γ' 0 0 : ℝ) = γ 1 1 := e01.symm
  have h01 : (γ' 0 1 : ℝ) = -(γ 1 0 : ℝ) / N := by
    field_simp
    linarith
  have h10 : (γ' 1 0 : ℝ) = -N * γ 0 1 := by linarith
  have h11 : (γ' 1 1 : ℝ) = γ 0 0 := (mul_left_cancel₀ hN (e10.trans (mul_comm _ _))).symm
  rw [SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

private lemma frickeGL_sq_comm (g : GL (Fin 2) ℝ) :
    frickeGL N * frickeGL N * g = g * (frickeGL N * frickeGL N) := by
  rw [frickeGL_mul_frickeGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.natCast_apply, mul_comm]

/-- **The Fricke matrix normalises `Γ₀(N)`.** As subgroups of `GL(2, ℝ)`,
`W_N⁻¹ Γ₀(N) W_N = Γ₀(N)`: the group for which Mathlib's `CuspForm.translate` makes
`f ∣[k] W_N` a cusp form. -/
theorem toConjAct_frickeGL_inv_smul :
    ConjAct.toConjAct (frickeGL N)⁻¹ • (Gamma0 N).map (SpecialLinearGroup.mapGL ℝ) =
      (Gamma0 N).map (SpecialLinearGroup.mapGL ℝ) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · rintro ⟨γ, hγ, hx⟩
    obtain ⟨γ', hγ', h1, -⟩ := frickeGL_mul_mapGL_mul_inv N hγ
    refine ⟨γ', hγ', ?_⟩
    have hx' : x = (frickeGL N)⁻¹ * SpecialLinearGroup.mapGL ℝ γ * frickeGL N := by
      rw [hx]; group
    have hc := frickeGL_sq_comm N (SpecialLinearGroup.mapGL ℝ γ)
    rw [hx', ← h1]
    symm
    calc (frickeGL N)⁻¹ * SpecialLinearGroup.mapGL ℝ γ * frickeGL N
        = (frickeGL N)⁻¹ * (SpecialLinearGroup.mapGL ℝ γ * (frickeGL N * frickeGL N)) *
            (frickeGL N)⁻¹ := by group
      _ = (frickeGL N)⁻¹ * (frickeGL N * frickeGL N * SpecialLinearGroup.mapGL ℝ γ) *
            (frickeGL N)⁻¹ := by rw [hc]
      _ = frickeGL N * SpecialLinearGroup.mapGL ℝ γ * (frickeGL N)⁻¹ := by group
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨γ', hγ', h1, -⟩ := frickeGL_mul_mapGL_mul_inv N hγ
    exact ⟨γ', hγ', h1.symm⟩

end ModularForm

namespace UpperHalfPlane

variable (N : ℕ) [NeZero N]

/-- The Fricke matrix `W_N = ModularForm.frickeGL N` acts on the upper half-plane by
`z ↦ -1/(Nz)`. -/
theorem coe_frickeGL_smul (z : ℍ) : ((frickeGL N • z : ℍ) : ℂ) = -1 / (N * z) := by
  have hdet : 0 < ((frickeGL N).det : ℝ) := by
    rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [coe_smul_of_det_pos hdet]
  simp [num, denom]

end UpperHalfPlane

namespace CuspForm

variable (N : ℕ) [NeZero N]

/-- The **Fricke operator on cusp forms** for `Γ₀(N)`: `f ↦ f ∣[k] W_N`, with
`W_N = ModularForm.frickeGL N`, as a `ℂ`-linear map from `CuspForm (Gamma0 N) k` to itself
(the cusp-form counterpart of `ModularForm.fricke`). -/
noncomputable def fricke (k : ℤ) : CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N) k where
  toFun f := CuspForm.mcast rfl (CuspForm.translate f (frickeGL N))
    (toConjAct_frickeGL_inv_smul N).symm
  map_add' f g := by
    ext τ
    change ((⇑f + ⇑g) ∣[k] frickeGL N) τ = (⇑f ∣[k] frickeGL N) τ + (⇑g ∣[k] frickeGL N) τ
    rw [SlashAction.add_slash]
    rfl
  map_smul' c f := by
    ext τ
    have hpos : 0 < ((frickeGL N).det : ℝ) := by
      rw [det_frickeGL]
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hσ : UpperHalfPlane.σ (frickeGL N) = .refl ℝ ℂ := by
      simp only [UpperHalfPlane.σ, hpos, ↓reduceIte]
    change ((c • ⇑f) ∣[k] frickeGL N) τ = c * (⇑f ∣[k] frickeGL N) τ
    rw [smul_slash, hσ]
    rfl

/-- **`f ↦ f ∣[k] W_N` maps `CuspForm (Gamma0 N) k` to itself:** `CuspForm.fricke N k f` is a
cusp form of weight `k` for `Γ₀(N)` with underlying function `f ∣[k] W_N`. -/
theorem coe_fricke (k : ℤ) (f : CuspForm (Gamma0 N) k) :
    ⇑(fricke N k f) = ⇑f ∣[k] frickeGL N :=
  rfl

/-- The formula for the Fricke involution in weight `2`:
`(f ∣[2] W_N)(z) = N⁻¹ z⁻² f(W_N • z)`, where `W_N • z = -1/(Nz)`
(`UpperHalfPlane.coe_frickeGL_smul`). -/
theorem fricke_apply_two (f : CuspForm (Gamma0 N) 2) (z : ℍ) :
    fricke N 2 f z = (N : ℂ)⁻¹ * (z : ℂ) ^ (-2 : ℤ) * f (frickeGL N • z) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [coe_fricke, slash_apply]
  simp only [σ, det_frickeGL, denom, val_frickeGL]
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp [hNpos]
  field_simp

/-- **The Fricke map is an involution in weight `2`:** `f ∣[2] W_N ∣[2] W_N = f` on
`S₂(Γ₀(N))`, the case `k = 2` of `ModularForm.slash_frickeGL_slash_frickeGL`. -/
theorem fricke_fricke_two (f : CuspForm (Gamma0 N) 2) : fricke N 2 (fricke N 2 f) = f := by
  ext z
  rw [coe_fricke, coe_fricke, slash_frickeGL_slash_frickeGL]
  simp

end CuspForm

namespace ModularForm

variable (N : ℕ) [NeZero N]

/-- **The Fricke matrix normalises `Γ₀(N)` and acts on weight-two cusp forms as an
involution.** For `N ≥ 1` and `W_N = ModularForm.frickeGL N = !![0, -1; N, 0]`:

1. for `γ = !![a, b; c, d] ∈ Γ₀(N)`, `W_N γ W_N⁻¹` is the image in `GL(2, ℝ)` of an element of
   `Γ₀(N)` with entries `!![d, -c/N; -N b, a]`;
2. for `f ∈ S₂(Γ₀(N))`, `f ∣[2] W_N` is again in `S₂(Γ₀(N))`, and
   `(f ∣[2] W_N)(z) = N⁻¹ z⁻² f(W_N • z)` with `W_N • z = -1/(Nz)`;
3. `f ∣[2] W_N ∣[2] W_N = f`.

Here `S₂(Γ₀(N))` is Mathlib's `CuspForm` for the image of `Γ₀(N)` in `GL(2, ℝ)` and `∣[2]` is
Mathlib's weight-two slash action. -/
theorem fricke_involution_weight_two :
    (∀ γ ∈ Gamma0 N, ∃ γ' ∈ Gamma0 N,
      frickeGL N * SpecialLinearGroup.mapGL ℝ γ * (frickeGL N)⁻¹ =
        SpecialLinearGroup.mapGL ℝ γ' ∧
      ((SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(γ 1 1 : ℝ), -(γ 1 0 : ℝ) / N; -N * (γ 0 1 : ℝ), (γ 0 0 : ℝ)]) ∧
    (∀ f : CuspForm (Gamma0 N) 2,
      ∃ g : CuspForm (Gamma0 N) 2, ⇑g = ⇑f ∣[(2 : ℤ)] frickeGL N ∧
        ∀ z : ℍ, g z = (N : ℂ)⁻¹ * (z : ℂ) ^ (-2 : ℤ) * f (frickeGL N • z) ∧
          ((frickeGL N • z : ℍ) : ℂ) = -1 / (N * z)) ∧
    (∀ f : CuspForm (Gamma0 N) 2,
      (⇑f ∣[(2 : ℤ)] frickeGL N) ∣[(2 : ℤ)] frickeGL N = ⇑f) := by
  refine ⟨fun γ hγ => frickeGL_mul_mapGL_mul_inv N hγ,
    fun f => ⟨CuspForm.fricke N 2 f, CuspForm.coe_fricke N 2 f,
      fun z => ⟨CuspForm.fricke_apply_two N f z, coe_frickeGL_smul N z⟩⟩, fun f => ?_⟩
  rw [slash_frickeGL_slash_frickeGL]
  simp

end ModularForm

end

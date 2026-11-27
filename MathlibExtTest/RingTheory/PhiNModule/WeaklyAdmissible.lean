/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.WeaklyAdmissible
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Tests for weakly admissible filtered `(φ, N)`-modules

Over `K₀ = K = ℚ_[p] = W(𝔽_p)[1/p]`, whose absolute Frobenius is the identity, with the `p`-adic
valuation `Padic.addValuation` (so `v(p) = 1`): the one-dimensional filtered `φ`-module
`ℚ_[p](n)` with `φ = p ^ n` and the filtration jumping at `n` has `t_H = t_N = n` and is weakly
admissible, while the same `φ` with the filtration jumping at `n + 1` is not. The results of
Fontaine–Ouyang, Proposition 8.41, are applied to the zero morphism `ℚ_[p](0) → ℚ_[p](1)` and to
the identity of `ℚ_[p](0)`.
-/

open Module TensorProduct FilteredPhiNModule

namespace MathlibExtTest.RingTheory.PhiNModule.WeaklyAdmissible

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuation is invariant under the absolute Frobenius `RingHom.id ℚ_[p]`. -/
theorem padic_hv (x : ℚ_[p]) : Padic.addValuation (RingHom.id ℚ_[p] x) = Padic.addValuation x :=
  rfl

/-- The prime `p` is nonzero in `ℚ_[p]`. -/
theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The filtered `φ`-module on `ℚ_[p]` with `φ = p ^ n • id`, `N = 0`, and the filtration of
`ℚ_[p] ⊗ ℚ_[p]` with a single jump at `m`. -/
noncomputable def line (n : ℕ) (m : ℤ) :
    FilteredPhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) ℚ_[p] ℚ_[p] where
  toPhiNModule := PhiNModule.ofPhi
    (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] ((p : ℚ_[p]) ^ n) (pow_ne_zero n p_ne_zero))
  fil := DecreasingFiltration.single m

theorem finrank_line_K : finrank ℚ_[p] (ℚ_[p] ⊗[ℚ_[p]] ℚ_[p]) = 1 := by
  rw [Module.finrank_baseChange, finrank_self]

/-- The Hodge number of `line n m` is `m`. -/
theorem hodgeNumber_line (n : ℕ) (m : ℤ) : (line (p := p) n m).hodgeNumber = m := by
  rw [hodgeNumber, line, DecreasingFiltration.hodgeNumber_single, finrank_line_K, Nat.cast_one,
    mul_one]

/-- The Newton number of `line n m` is `n`, as `v(p) = 1`. -/
theorem newtonNumber_line (n : ℕ) (m : ℤ) :
    (line (p := p) n m).newtonNumber Padic.addValuation = n := by
  have h := PhiNModule.coe_newtonNumber _ padic_hv (line (p := p) n m).toPhiNModule
    (Basis.singleton (Fin 1) ℚ_[p])
  have hdet : (Basis.singleton (Fin 1) ℚ_[p]).det
      ((line (p := p) n m).φ ∘ Basis.singleton (Fin 1) ℚ_[p]) = (p : ℚ_[p]) ^ n := by
    rw [Basis.det_apply, Matrix.det_unique]
    simp [line, Basis.toMatrix_apply]
  rw [hdet, AddValuation.map_pow, Padic.addValuation.apply p_ne_zero, Padic.valuation_p] at h
  have h' : n • ((1 : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_nsmul, nsmul_one]
  exact_mod_cast h.trans h'

/-- `ℚ_[p](n)`, with the filtration jumping at `n`, is weakly admissible. -/
theorem isWeaklyAdmissible_line (n : ℕ) :
    (line (p := p) n n).IsWeaklyAdmissible Padic.addValuation := by
  rw [isWeaklyAdmissible_iff_of_finrank_eq_one _ padic_hv (finrank_self ℚ_[p]),
    hodgeNumber_line, newtonNumber_line]

/-- With the filtration jumping at `n + 1` instead, `t_H = n + 1 ≠ n = t_N`. -/
example (n : ℕ) : ¬ (line (p := p) n (n + 1)).IsWeaklyAdmissible Padic.addValuation := by
  intro h
  have := h.hodgeNumber_eq_newtonNumber
  rw [hodgeNumber_line, newtonNumber_line] at this
  omega

/-- The equivalent condition on quotients (Fontaine–Ouyang, Remark 8.40). -/
example (n : ℕ) (D' : Submodule ℚ_[p] ℚ_[p]) (h : (line (p := p) n n).IsStable D') :
    ((line n n).quotient D' h).newtonNumber Padic.addValuation ≤
      ((line n n).quotient D' h).hodgeNumber :=
  ((isWeaklyAdmissible_iff_quotient _ padic_hv).mp (isWeaklyAdmissible_line n)).2 D' h

/-- The zero morphism `ℚ_[p](0) → ℚ_[p](1)`. -/
noncomputable def zeroHom : (line (p := p) 0 0).Hom (line 1 1) where
  toLinearMap := 0
  map_φ _ := by simp
  map_N _ := by simp
  map_fil_le _ := by simp

/-- The identity morphism of `ℚ_[p](0)`. -/
noncomputable def idHom : (line (p := p) 0 0).Hom (line 0 0) where
  toLinearMap := LinearMap.id
  map_φ _ := rfl
  map_N _ := rfl
  map_fil_le _ := by simp

example : ((line (p := p) 0 0).restrict (LinearMap.ker (zeroHom (p := p)).toLinearMap)
    zeroHom.isStable_ker).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.ker padic_hv (isWeaklyAdmissible_line 0) (isWeaklyAdmissible_line 1) zeroHom

example : ((line (p := p) 1 1).quotient (LinearMap.range (zeroHom (p := p)).toLinearMap)
    zeroHom.isStable_range).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.coker padic_hv (isWeaklyAdmissible_line 0) (isWeaklyAdmissible_line 1)
    zeroHom

example : ((line (p := p) 0 0).restrict (LinearMap.range (idHom (p := p)).toLinearMap)
    idHom.isStable_range).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.range padic_hv (isWeaklyAdmissible_line 0) (isWeaklyAdmissible_line 0) idHom

/-- Strictness of the identity of `ℚ_[p](0)` for the filtrations. -/
example (i : ℤ) : ((line (p := p) 0 0).fil.Fil i).map ((idHom (p := p)).toLinearMap.baseChange
      ℚ_[p]) = LinearMap.range ((idHom (p := p)).toLinearMap.baseChange ℚ_[p]) ⊓
      (line (p := p) 0 0).fil.Fil i :=
  IsWeaklyAdmissible.map_fil_eq_range_inf_fil padic_hv (isWeaklyAdmissible_line 0)
    (isWeaklyAdmissible_line 0) idHom i

end MathlibExtTest.RingTheory.PhiNModule.WeaklyAdmissible

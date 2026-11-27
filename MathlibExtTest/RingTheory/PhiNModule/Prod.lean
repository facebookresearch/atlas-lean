/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.Prod
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Tests for direct sums of filtered `(φ, N)`-modules

Over `K₀ = K = ℚ_[p] = W(𝔽_p)[1/p]`, whose absolute Frobenius is the identity, with the `p`-adic
valuation `Padic.addValuation` (so `v(p) = 1`): the direct sum `ℚ_[p](n) ⊕ ℚ_[p](m)` of the
weakly admissible one-dimensional filtered `φ`-modules `ℚ_[p](n)` (with `φ = p ^ n` and the
filtration jumping at `n`) has `t_H = t_N = n + m` and is weakly admissible, and so is a direct
sum of three of them; the direct sum of `ℚ_[p]` with `φ = 1` and the filtration jumping at `1`
and of `ℚ_[p](1)` has `t_H = 2 ≠ 1 = t_N`. The results of Fontaine–Ouyang, Proposition 8.41, are
applied to the inclusions and the projections of `ℚ_[p](n) ⊕ ℚ_[p](m)`.
-/

open Module TensorProduct FilteredPhiNModule

namespace MathlibExtTest.RingTheory.PhiNModule.Prod

/-- The product filtration of `ℚ × ℚ²` with jumps at `a` and `b` has Hodge number `a + 2 b`. -/
example (a b : ℤ) : ((DecreasingFiltration.single a : DecreasingFiltration ℚ ℚ).prod
    (DecreasingFiltration.single b : DecreasingFiltration ℚ (Fin 2 → ℚ))).hodgeNumber =
      a + 2 * b := by
  rw [DecreasingFiltration.hodgeNumber_prod, DecreasingFiltration.hodgeNumber_single,
    DecreasingFiltration.hodgeNumber_single, finrank_self, Module.finrank_fin_fun]
  push_cast
  ring

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

/-- The base change `ℚ_[p] ⊗ ℚ_[p]` of `ℚ_[p]` is one-dimensional. -/
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

/-- `φ` acts componentwise on a direct sum of two lines. -/
example (n m : ℕ) (x y : ℚ_[p]) : ((line (p := p) n n).prod (line m m)).φ (x, y) =
    ((p : ℚ_[p]) ^ n * x, (p : ℚ_[p]) ^ m * y) := by
  simp [line]

/-- The Hodge number of `line n m ⊕ line n' m'` is `m + m'`. -/
theorem hodgeNumber_prod_line (n n' : ℕ) (m m' : ℤ) :
    ((line (p := p) n m).prod (line n' m')).hodgeNumber = m + m' := by
  rw [hodgeNumber_prod, hodgeNumber_line, hodgeNumber_line]

/-- The Newton number of `line n m ⊕ line n' m'` is `n + n'`. -/
theorem newtonNumber_prod_line (n n' : ℕ) (m m' : ℤ) :
    ((line (p := p) n m).prod (line n' m')).newtonNumber Padic.addValuation = n + n' := by
  rw [newtonNumber_prod _ _ padic_hv, newtonNumber_line, newtonNumber_line]

/-- `ℚ_[p](n) ⊕ ℚ_[p](m)` is weakly admissible. -/
theorem isWeaklyAdmissible_prod_line (n m : ℕ) :
    ((line (p := p) n n).prod (line m m)).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.prod padic_hv (isWeaklyAdmissible_line n) (isWeaklyAdmissible_line m)

/-- `(ℚ_[p](n) ⊕ ℚ_[p](m)) ⊕ ℚ_[p](k)` is weakly admissible. -/
example (n m k : ℕ) :
    (((line (p := p) n n).prod (line m m)).prod (line k k)).IsWeaklyAdmissible
      Padic.addValuation :=
  (isWeaklyAdmissible_prod_line n m).prod padic_hv (isWeaklyAdmissible_line k)

/-- `line 0 1 ⊕ line 1 1` has `t_H = 2 ≠ 1 = t_N`, so it is not weakly admissible. -/
example : ¬ ((line (p := p) 0 1).prod (line 1 1)).IsWeaklyAdmissible Padic.addValuation := by
  intro h
  have := h.hodgeNumber_eq_newtonNumber
  rw [hodgeNumber_prod_line, newtonNumber_prod_line] at this
  omega

/-- The kernel of the first projection of `ℚ_[p](n) ⊕ ℚ_[p](m)` is weakly admissible
(Fontaine–Ouyang, Proposition 8.41 (1)). -/
example (n m : ℕ) : (((line (p := p) n n).prod (line m m)).restrict
    (LinearMap.ker (fst (line (p := p) n n) (line m m)).toLinearMap)
    (fst _ _).isStable_ker).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.ker padic_hv (isWeaklyAdmissible_prod_line n m) (isWeaklyAdmissible_line n)
    (fst _ _)

/-- The cokernel of the first inclusion of `ℚ_[p](n) ⊕ ℚ_[p](m)` is weakly admissible
(Fontaine–Ouyang, Proposition 8.41 (2)). -/
example (n m : ℕ) : (((line (p := p) n n).prod (line m m)).quotient
    (LinearMap.range (inl (line (p := p) n n) (line m m)).toLinearMap)
    (inl _ _).isStable_range).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.coker padic_hv (isWeaklyAdmissible_line n) (isWeaklyAdmissible_prod_line n m)
    (inl _ _)

/-- The image of the second inclusion of `ℚ_[p](n) ⊕ ℚ_[p](m)` is weakly admissible. -/
example (n m : ℕ) : (((line (p := p) n n).prod (line m m)).restrict
    (LinearMap.range (inr (line (p := p) n n) (line m m)).toLinearMap)
    (inr _ _).isStable_range).IsWeaklyAdmissible Padic.addValuation :=
  IsWeaklyAdmissible.range padic_hv (isWeaklyAdmissible_line m) (isWeaklyAdmissible_prod_line n m)
    (inr _ _)

/-- The second projection of `ℚ_[p](n) ⊕ ℚ_[p](m)` is strict for the filtrations
(Fontaine–Ouyang, Proposition 8.41 (3)). -/
example (n m : ℕ) (i : ℤ) :
    ((((line (p := p) n n).prod (line m m))).fil.Fil i).map
        ((snd (line (p := p) n n) (line m m)).toLinearMap.baseChange ℚ_[p]) =
      LinearMap.range ((snd (line (p := p) n n) (line m m)).toLinearMap.baseChange ℚ_[p]) ⊓
        (line (p := p) m m).fil.Fil i :=
  IsWeaklyAdmissible.map_fil_eq_range_inf_fil padic_hv (isWeaklyAdmissible_prod_line n m)
    (isWeaklyAdmissible_line m) (snd _ _) i

end MathlibExtTest.RingTheory.PhiNModule.Prod

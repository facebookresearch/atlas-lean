/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.TateDeterminant
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

universe u

/-- Consumer with the original binders (the local and adically complete hypotheses are not
needed by the proof). -/
example {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (n : ℕ) (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    (RingHom.ker π).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} ∧
      (RingHom.ker π).annihilator.map π =
        Ideal.span {(g.map MvPowerSeries.constantCoeff).det} :=
  MvPowerSeries.annihilator_ker_eq_span_det n g f hf π hπ

/-- Higher-universe consumer. -/
example {𝒪 : Type (u + 1)} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    (n : ℕ) (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    (RingHom.ker π).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} :=
  (MvPowerSeries.annihilator_ker_eq_span_det n g f hf π hπ).1

/-- Consumer with the original binders. -/
example {k : Type u} [Field k] {n : ℕ} (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J :=
  MvPowerSeries.quotient_mk_det_mem_of_ne_bot g f hf

/-- Consumer with the original binders. -/
example {k : Type u} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k)) (f : Fin n → MvPowerSeries (Fin n) k)
    (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    ∃ l : (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) →ₗ[k] k,
      Function.Bijective
        ((LinearMap.mul k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))).compr₂ l) :=
  MvPowerSeries.exists_bijective_compr₂_mul_of_finite g f hf

/-- Higher-universe consumer. -/
example {k : Type (u + 1)} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k)) (f : Fin n → MvPowerSeries (Fin n) k)
    (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 :=
  (MvPowerSeries.quotient_mk_det_mem_of_ne_bot g f hf).1

/-- Boundary: finiteness matters. For `n = 1`, `g = 0` and `f = 0`, the relation `f = g • X`
holds, but `k⟦X⟧ ⧸ (f) = k⟦X⟧` is infinite-dimensional and the class of `det g` is zero. -/
example : (∀ i, (0 : Fin 1 → MvPowerSeries (Fin 1) ℚ) i =
      ∑ j, (0 : Matrix (Fin 1) (Fin 1) (MvPowerSeries (Fin 1) ℚ)) i j * MvPowerSeries.X j) ∧
    Ideal.Quotient.mk (Ideal.span (Set.range (0 : Fin 1 → MvPowerSeries (Fin 1) ℚ)))
      (0 : Matrix (Fin 1) (Fin 1) (MvPowerSeries (Fin 1) ℚ)).det = 0 := by
  simp

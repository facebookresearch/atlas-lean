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
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Basis.VectorSpace

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

/-- The relation `f = g • X` may also be given in `Matrix.mulVec` form. -/
example {k : Type u} [Field k] {n : ℕ} (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : f = g.mulVec MvPowerSeries.X)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 :=
  (MvPowerSeries.quotient_mk_det_mem_of_ne_bot g f fun i => congrFun hf i).1

section Concrete

/-! A concrete instance: `n = 1`, `f = X²` and `g = X`, so that `k⟦X⟧ ⧸ (f)` has basis `1, X`. -/

open MvPowerSeries

private theorem span_range_vecCons_vecEmpty {R : Type*} [CommRing R] (a : R) :
    Ideal.span (Set.range ![a]) = Ideal.span {a} := by
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]

private noncomputable abbrev fSq (k : Type u) [Field k] : Fin 1 → MvPowerSeries (Fin 1) k :=
  ![X 0 ^ 2]

private noncomputable abbrev gX (k : Type u) [Field k] :
    Matrix (Fin 1) (Fin 1) (MvPowerSeries (Fin 1) k) :=
  !![X 0]

private theorem hfSq (k : Type u) [Field k] : ∀ i, fSq k i = ∑ j, gX k i j * X j := by
  intro i; fin_cases i; simp [pow_two]

private theorem mem_span_fSq (k : Type u) [Field k] (q : MvPowerSeries (Fin 1) k) :
    q - C (coeff 0 q) - C (coeff (Finsupp.single 0 1) q) * X 0 ∈
      Ideal.span (Set.range (fSq k)) := by
  rw [span_range_vecCons_vecEmpty, Ideal.mem_span_singleton]
  refine X_pow_dvd_iff.mpr fun m hm => ?_
  have hm' : m = Finsupp.single 0 (m 0) := Finsupp.ext fun i => by fin_cases i; simp
  rcases (by omega : m 0 = 0 ∨ m 0 = 1) with h | h <;> rw [hm', h] <;>
    simp [coeff_C, coeff_C_mul, coeff_X]

private instance finite_fSq (k : Type u) [Field k] :
    Module.Finite k (MvPowerSeries (Fin 1) k ⧸ Ideal.span (Set.range (fSq k))) := by
  classical
  let f := (Ideal.Quotient.mkₐ k (Ideal.span (Set.range (fSq k)))).toLinearMap
  refine Module.finite_def.mpr ⟨{1, Ideal.Quotient.mk _ (X 0)}, eq_top_iff.mpr fun t _ => ?_⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hmem : C (coeff 0 q) + C (coeff (Finsupp.single 0 1) q) * X 0 ∈
      Submodule.span k {(1 : MvPowerSeries (Fin 1) k), X 0} :=
    Submodule.mem_span_pair.mpr ⟨coeff 0 q, coeff (Finsupp.single 0 1) q, by
      rw [smul_eq_C_mul, smul_eq_C_mul, mul_one]⟩
  have hmap := Submodule.mem_map_of_mem (f := f) hmem
  rw [Submodule.map_span, Set.image_pair] at hmap
  have hq : f (C (coeff 0 q) + C (coeff (Finsupp.single 0 1) q) * X 0) =
      Ideal.Quotient.mk (Ideal.span (Set.range (fSq k))) q := by
    refine (Ideal.Quotient.eq.mpr ?_).symm
    simpa [sub_sub] using mem_span_fSq k q
  rw [hq] at hmap
  simpa [f] using hmap

private theorem fSq_le_ker (k : Type u) [Field k] :
    ∀ a ∈ Ideal.span (Set.range (fSq k)), constantCoeff a = 0 := fun a ha => by
  rw [span_range_vecCons_vecEmpty, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  simp

private noncomputable def constantCoeffAlg (k : Type u) [Field k] :
    MvPowerSeries (Fin 1) k →ₐ[k] k :=
  { (constantCoeff : MvPowerSeries (Fin 1) k →+* k) with
    commutes' := fun r => by simp [← c_eq_algebraMap] }

/-- The augmentation `k⟦X⟧ ⧸ (X²) → k` induced by the constant coefficient. -/
private noncomputable def πSq (k : Type u) [Field k] :
    (MvPowerSeries (Fin 1) k ⧸ Ideal.span (Set.range (fSq k))) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (constantCoeffAlg k) (fSq_le_ker k)

private theorem hπSq (k : Type u) [Field k] :
    ((πSq k : _ →ₐ[k] k) : _ →+* k).comp (Ideal.Quotient.mk (Ideal.span (Set.range (fSq k)))) =
      constantCoeff :=
  RingHom.ext fun _ => rfl

/-- In the concrete instance, the annihilator of the augmentation ideal is generated by `X`. -/
example (k : Type u) [Field k] : (RingHom.ker (πSq k)).annihilator =
    Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range (fSq k))) (X 0)} := by
  have h := (annihilator_ker_eq_span_det 1 (gX k) (fSq k) (hfSq k) (πSq k) (hπSq k)).1
  rwa [Matrix.det_fin_one_of] at h

/-- In the concrete instance, the image of that annihilator under the augmentation is zero,
since `det g(0) = 0`. -/
example (k : Type u) [Field k] : (RingHom.ker (πSq k)).annihilator.map (πSq k) = ⊥ := by
  rw [(annihilator_ker_eq_span_det 1 (gX k) (fSq k) (hfSq k) (πSq k) (hπSq k)).2,
    Matrix.det_fin_one, Matrix.map_apply]
  simp [gX]

/-- In the concrete instance, the class of `X` is nonzero and lies in every nonzero ideal. -/
example (k : Type u) [Field k] :
    Ideal.Quotient.mk (Ideal.span (Set.range (fSq k))) (X 0) ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin 1) k ⧸ Ideal.span (Set.range (fSq k))), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range (fSq k))) (X 0) ∈ J := by
  have h := quotient_mk_det_mem_of_ne_bot (gX k) (fSq k) (hfSq k)
  rwa [Matrix.det_fin_one_of] at h

/-- In the concrete instance, some linear form makes the multiplication pairing perfect. -/
example (k : Type u) [Field k] :
    ∃ l : (MvPowerSeries (Fin 1) k ⧸ Ideal.span (Set.range (fSq k))) →ₗ[k] k,
      Function.Bijective
        ((LinearMap.mul k (MvPowerSeries (Fin 1) k ⧸ Ideal.span (Set.range (fSq k)))).compr₂ l) :=
  exists_bijective_compr₂_mul_of_finite (gX k) (fSq k) (hfSq k)

end Concrete

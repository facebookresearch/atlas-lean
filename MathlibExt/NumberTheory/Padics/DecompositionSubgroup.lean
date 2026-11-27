/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_CompletionBridge.lean`,
`Theorems/Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_
closure_range_localGaloisToGlobal.lean`,
`P2M/Sol/S_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_
range_localGaloisToGlobal.lean`,
`Theorems/Thm_ValuationSubring_valuation_map_eq_of_mem_
decompositionSubgroup.lean`
and
`P2M/Sol/S_ValuationSubring_valuation_map_eq_of_mem_
decompositionSubgroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Topology.Algebra.Group.Subgroup

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

open scoped NNReal Pointwise

/-- A chosen embedding of the algebraic closure of `ℚ` into the algebraic
closure of `ℚ_[p]`, obtained from the universal property of algebraic
closures. -/
noncomputable def padicEmbedding (p : ℕ) [Fact p.Prime] :
    AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p :=
  IsAlgClosed.lift

/-- The valuation subring of the algebraic closure of `ℚ_[p]` consisting of
the elements of norm at most one. -/
noncomputable def padicIntegers (p : ℕ) [Fact p.Prime] :
    ValuationSubring (PadicAlgCl p) :=
  (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).valuationSubring

/-- The `p`-adic place of the algebraic closure of `ℚ`: the valuation
subring pulled back along `padicEmbedding p`. -/
noncomputable def padicPlace (p : ℕ) [Fact p.Prime] :
    ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers p).comap (padicEmbedding p).toRingHom

theorem mem_padicPlace_iff (p : ℕ) [Fact p.Prime]
    {x : AlgebraicClosure ℚ} :
    x ∈ padicPlace p ↔ ‖padicEmbedding p x‖₊ ≤ 1 :=
  Iff.rfl

section Galois

variable (p : ℕ) [Fact p.Prime]

noncomputable local instance instAlgebraQbarPadic :
    Algebra (AlgebraicClosure ℚ) (PadicAlgCl p) :=
  (padicEmbedding p).toRingHom.toAlgebra

local instance instTowerQbarPadic :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

local instance instTowerQqPadic : IsScalarTower ℚ ℚ_[p] (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- The restriction map from the Galois group of the algebraic closure of
`ℚ_[p]` to the Galois group of the algebraic closure of `ℚ`, obtained by
restricting automorphisms along `padicEmbedding p`. -/
noncomputable def localGaloisToGlobal (p : ℕ) [Fact p.Prime] :
    (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl p)
    (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

theorem padicEmbedding_localGaloisToGlobal
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : AlgebraicClosure ℚ) :
    padicEmbedding p (localGaloisToGlobal p τ x) =
      τ (padicEmbedding p x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ)
    (AlgebraicClosure ℚ) x

private theorem nnnorm_padicAlgCl_algEquiv
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : PadicAlgCl p) : ‖τ y‖₊ = ‖y‖₊ := by
  ext
  exact (spectralNorm_eq_of_equiv τ y).symm

theorem localGaloisToGlobal_mem_decompositionSubgroup
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    localGaloisToGlobal p τ ∈ (padicPlace p).decompositionSubgroup ℚ := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (localGaloisToGlobal p τ)⁻¹ =
      localGaloisToGlobal p τ⁻¹ := (map_inv _ τ).symm
  rw [AlgEquiv.smul_def, hinv]
  rw [mem_padicPlace_iff, mem_padicPlace_iff,
    padicEmbedding_localGaloisToGlobal, nnnorm_padicAlgCl_algEquiv]

end Galois

section ValuationInvariance

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem apply_mem_iff_of_mem_decompositionSubgroup
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

private theorem apply_mem_nonunits_iff_of_mem_decompositionSubgroup
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) :
    σ x ∈ A.nonunits ↔ x ∈ A.nonunits := by
  have h1 : σ x = 0 ↔ x = 0 := by
    constructor
    · intro h; exact σ.injective (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  rw [ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, h1,
    apply_mem_iff_of_mem_decompositionSubgroup hσ]

private theorem valuation_lt_of_lt_of_mem_decompositionSubgroup
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {a b : L}
    (h : A.valuation a < A.valuation b) :
    A.valuation (σ a) < A.valuation (σ b) := by
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact (not_lt_of_ge zero_le) h
  have hb' : σ b ≠ 0 := fun h0 => hb (σ.injective (by rw [h0, map_zero]))
  have hvb : 0 < A.valuation b := lt_of_le_of_lt zero_le h
  have hvb' : 0 < A.valuation (σ b) :=
    lt_of_le_of_ne zero_le (Ne.symm ((Valuation.ne_zero_iff _).mpr hb'))
  have hab : a / b ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ hvb]
    exact h
  have hab' : σ a / σ b ∈ A.nonunits := by
    rw [← map_div₀,
      apply_mem_nonunits_iff_of_mem_decompositionSubgroup hσ]
    exact hab
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ hvb']
    at hab'
  exact hab'

private theorem exists_pow_apply_eq [Algebra.IsAlgebraic K L]
    (σ : L ≃ₐ[K] L) (z : L) :
    ∃ N : ℕ, 0 < N ∧ (σ ^ N) z = z := by
  classical
  have hz : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hp0 : minpoly K z ≠ 0 := minpoly.ne_zero hz
  have hmem : ∀ n : ℕ, (σ ^ n) z ∈ (minpoly K z).rootSet L := by
    intro n
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    rw [Polynomial.aeval_algHom_apply (σ ^ n) z (minpoly K z),
      minpoly.aeval, map_zero]
  let f : ℕ → (minpoly K z).rootSet L := fun n => ⟨(σ ^ n) z, hmem n⟩
  obtain ⟨m, n, hmn, hfmn⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hval : (σ ^ m) z = (σ ^ n) z := congrArg Subtype.val hfmn
  have key : ∀ m n : ℕ, m < n → (σ ^ m) z = (σ ^ n) z →
      ∃ N : ℕ, 0 < N ∧ (σ ^ N) z = z := by
    intro m n hlt heq
    refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    apply (σ ^ m).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact heq.symm
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact key m n hlt hval
  · exact key n m hlt hval.symm

private theorem not_valuation_apply_lt_of_mem_decompositionSubgroup
    [Algebra.IsAlgebraic K L] {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) (z : L) :
    ¬ A.valuation (σ z) < A.valuation z := by
  intro h
  have step : ∀ k : ℕ,
      A.valuation ((σ ^ (k + 1)) z) < A.valuation ((σ ^ k) z) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have := valuation_lt_of_lt_of_mem_decompositionSubgroup hσ ih
      rwa [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ',
        ← pow_succ'] at this
  have chain : ∀ k : ℕ, A.valuation ((σ ^ (k + 1)) z) < A.valuation z := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => exact lt_trans (step (k + 1)) ih
  obtain ⟨N, hN, hfix⟩ := exists_pow_apply_eq σ z
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have := chain k
  rw [hfix] at this
  exact lt_irrefl _ this

private theorem valuation_apply_eq_of_mem_decompositionSubgroup
    [Algebra.IsAlgebraic K L] {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) (z : L) :
    A.valuation (σ z) = A.valuation z := by
  rcases lt_trichotomy (A.valuation (σ z)) (A.valuation z) with h | h | h
  · exact absurd h (not_valuation_apply_lt_of_mem_decompositionSubgroup
      hσ z)
  · exact h
  · exfalso
    have hσ' : σ⁻¹ ∈ A.decompositionSubgroup K :=
      (A.decompositionSubgroup K).inv_mem hσ
    apply not_valuation_apply_lt_of_mem_decompositionSubgroup hσ' (σ z)
    have e : σ⁻¹ (σ z) = z := by
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [e]
    exact h

/-- An automorphism in the decomposition subgroup of a valuation subring of an algebraic
extension preserves the valuation of that subring. -/
theorem ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup
    [Algebra.IsAlgebraic K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (z : L) :
    A.valuation (σ z) = A.valuation z :=
  valuation_apply_eq_of_mem_decompositionSubgroup hσ z

end ValuationInvariance

section MainProof

open Polynomial

private theorem nnnorm_padicEmbedding_map_eq_of_mem_decompositionSubgroup
    (p : ℕ) [Fact p.Prime]
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ (padicPlace p).decompositionSubgroup ℚ)
    (x : AlgebraicClosure ℚ) :
    ‖padicEmbedding p (σ x)‖₊ = ‖padicEmbedding p x‖₊ := by
  let v : Valuation (AlgebraicClosure ℚ) ℝ≥0 :=
    (Valued.v : Valuation (PadicAlgCl p) ℝ≥0).comap
      (padicEmbedding p).toRingHom
  have hA : v.valuationSubring = padicPlace p := by
    ext y
    rfl
  have heq : v.IsEquiv (padicPlace p).valuation := by
    rw [← hA]
    exact v.isEquiv_valuation_valuationSubring
  have h1 := valuation_apply_eq_of_mem_decompositionSubgroup
    (A := padicPlace p) hσ x
  apply le_antisymm
  · exact (heq (σ x) x).mpr (le_of_eq h1)
  · exact (heq x (σ x)).mpr (le_of_eq h1.symm)

private theorem aeval_minpoly_map_eq_zero_of_isometry {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra ℚ K]
    (ι : K →ₐ[ℚ] PadicAlgCl p) (σ : K ≃ₐ[ℚ] K)
    (hiso : ∀ x, ‖ι (σ x)‖ = ‖ι x‖) (a : K) :
    aeval (ι (σ a)) (minpoly ℚ_[p] (ι a)) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (minpoly ℚ_[p] (ι a)).natDegree < n :=
    ⟨_, Nat.lt_succ_self _⟩
  let ev : (Fin n → ℚ_[p]) → PadicAlgCl p → PadicAlgCl p :=
    fun c y => ∑ i, algebraMap ℚ_[p] (PadicAlgCl p) (c i) * y ^ (i : ℕ)
  have hev_cont : ∀ y, Continuous (fun c => ev c y) := by
    intro y
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((continuous_algebraMap ℚ_[p] (PadicAlgCl p)).comp
      (continuous_apply i)).mul continuous_const
  have hratK : ∀ (c : Fin n → ℚ) (b : K),
      ev (Pi.map (fun _ => ((↑) : ℚ → ℚ_[p])) c) (ι b) =
        ι (∑ i, (c i : K) * b ^ (i : ℕ)) := by
    intro c b
    simp only [ev, Pi.map_apply, map_sum, map_mul, map_pow, map_ratCast]
  have hσsum : ∀ c : Fin n → ℚ,
      σ (∑ i, (c i : K) * a ^ (i : ℕ)) =
        ∑ i, (c i : K) * (σ a) ^ (i : ℕ) := by
    intro c
    simp only [map_sum, map_mul, map_pow, map_ratCast]
  have hrat : ∀ c : Fin n → ℚ,
      ‖ev (Pi.map (fun _ => ((↑) : ℚ → ℚ_[p])) c) (ι (σ a))‖
        = ‖ev (Pi.map (fun _ => ((↑) : ℚ → ℚ_[p])) c) (ι a)‖ := by
    intro c
    rw [hratK, hratK, ← hσsum, hiso]
  have hdense : DenseRange (Pi.map (fun (_ : Fin n) => ((↑) : ℚ → ℚ_[p]))) :=
    DenseRange.piMap (fun _ => Padic.denseRange_ratCast p)
  have hall : ∀ c : Fin n → ℚ_[p],
      ‖ev c (ι (σ a))‖ = ‖ev c (ι a)‖ := fun c =>
    hdense.induction_on (p := fun c => ‖ev c (ι (σ a))‖ = ‖ev c (ι a)‖) c
      (isClosed_eq (hev_cont _).norm (hev_cont _).norm) hrat
  have hgev : ∀ y : PadicAlgCl p, aeval y (minpoly ℚ_[p] (ι a))
      = ev (fun i => (minpoly ℚ_[p] (ι a)).coeff (i : ℕ)) y := by
    intro y
    rw [aeval_eq_sum_range' hn, Finset.sum_range]
    simp only [ev, Algebra.smul_def]
  have h0 : ‖ev (fun i => (minpoly ℚ_[p] (ι a)).coeff (i : ℕ)) (ι a)‖
      = 0 := by
    rw [← hgev, minpoly.aeval, norm_zero]
  have h1 : ‖ev (fun i => (minpoly ℚ_[p] (ι a)).coeff (i : ℕ)) (ι (σ a))‖
      = 0 := by
    rw [hall, h0]
  rw [hgev]
  exact norm_eq_zero.mp h1

private theorem exists_mem_range_localGaloisToGlobal_apply_eq
    (p : ℕ) [Fact p.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (a : AlgebraicClosure ℚ)
    (hroot : aeval (padicEmbedding p (σ a))
      (minpoly ℚ_[p] (padicEmbedding p a)) = 0) :
    ∃ τ ∈ MonoidHom.range (localGaloisToGlobal p), τ a = σ a := by
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (K := ℚ_[p])
    (L := PadicAlgCl p) (Algebra.IsAlgebraic.isAlgebraic
      (padicEmbedding p a)) hroot
  refine ⟨localGaloisToGlobal p g, ⟨g, rfl⟩, ?_⟩
  have hinj : Function.Injective (padicEmbedding p) :=
    (padicEmbedding p).toRingHom.injective
  apply hinj
  rw [padicEmbedding_localGaloisToGlobal, hg]

private theorem mem_topologicalClosure_of_forall_exists_apply_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L] [PerfectField K]
    (S : Subgroup (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L)
    (h : ∀ a : L, ∃ τ ∈ S, τ a = σ a) :
    σ ∈ S.topologicalClosure := by
  change σ ∈ _root_.closure (S : Set (L ≃ₐ[K] L))
  rw [mem_closure_iff]
  intro U hU hσU
  have hV : IsOpen ((fun g => σ * g) ⁻¹' U) :=
    hU.preimage (continuous_const_mul σ)
  have h1V : (1 : L ≃ₐ[K] L) ∈ (fun g => σ * g) ⁻¹' U := by
    simpa using hσU
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K L _).mp
    (hV.mem_nhds h1V)
  haveI : FiniteDimensional K E := hfin
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  obtain ⟨τ, hτS, hτa⟩ := h (α : L)
  have hEeq : IntermediateField.adjoin K {(α : L)} = E := by
    rw [← IntermediateField.lift_adjoin_simple K E α, hα,
      IntermediateField.lift_top]
  have hfix : σ⁻¹ * τ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff, ← hEeq]
    change ∀ x ∈ IntermediateField.adjoin K {(α : L)}, (σ⁻¹ * τ) • x = x
    rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h2 : τ • (α : L) = σ • (α : L) := hτa
    rw [mul_smul, h2, inv_smul_smul]
  exact ⟨τ, by simpa using hE hfix, hτS⟩

/-- The decomposition group at the `p`-adic place of the algebraic closure
of `ℚ` is contained in the closure of the image of the local Galois group
under restriction to the algebraic closure of `ℚ`. -/
theorem ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
    (p : ℕ) [Fact p.Prime] :
    ((padicPlace p).decompositionSubgroup ℚ
        : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      ≤ (MonoidHom.range (localGaloisToGlobal p)).topologicalClosure := by
  intro σ hσ
  refine mem_topologicalClosure_of_forall_exists_apply_eq _ σ (fun a => ?_)
  refine exists_mem_range_localGaloisToGlobal_apply_eq p σ a ?_
  refine aeval_minpoly_map_eq_zero_of_isometry (padicEmbedding p) σ
    (fun x => ?_) a
  rw [← coe_nnnorm, ← coe_nnnorm,
    nnnorm_padicEmbedding_map_eq_of_mem_decompositionSubgroup p hσ x]

end MainProof

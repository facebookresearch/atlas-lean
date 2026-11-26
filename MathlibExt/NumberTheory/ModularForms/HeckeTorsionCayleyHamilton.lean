/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_GaloisRep_FrobeniusPowerDense.lean` (`FrobeniusPowerDense`);
`Definitions/Def_HeckeGalois_EichlerShimura.lean` (`HeckeAlg`, `heckeGen`,
`heckeTorsion` and its two lemmas, `FrobeniusQuadratic`);
`Theorems/Thm_Representation_cayleyHamilton_of_frobeniusPowerDense.lean` and
`P2M/Sol/S_Representation_cayleyHamilton_of_frobeniusPowerDense.lean` (the
propagation argument in `HeckeTorsionDensity`);
`Theorems/Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense.lean`
and
`P2M/Sol/S_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense.lean`
(the torsion representation and the main theorem).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RepresentationTheory.Basic
public import MathlibExt.AlgebraicGeometry.EllipticCurve.FrobeniusTrace
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

/-- **Conjugated Frobenius powers modulo a subgroup.** For every `σ` there are a prime `ℓ ∉ S`,
a valuation subring `A` of `AlgebraicClosure ℚ` lying over `ℓ`, an element `τ` that is
Frobenius at `ℓ` for `A`, an element `g` and an exponent `n` with `g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H`,
that is, `σ` lies in the coset `H * (g * τ ^ n * g⁻¹)`. For `H` the kernel of a
representation `ρ`, this says that every image `ρ σ` is the image of a conjugated Frobenius
power. Despite the name, this is not topological density: no closure is taken. -/
def FrobeniusPowerDense (S : Finset ℕ)
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : Prop :=
  ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H

namespace ModularCurve

/-- The Hecke algebra: polynomials over `ℤ` indexed by the primes. -/
noncomputable abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ

/-- The Hecke generator at a prime `ℓ`. -/
noncomputable def heckeGen (ℓ : Nat.Primes) : HeckeAlg := MvPolynomial.X ℓ

variable {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

/-- **Hecke torsion.** The submodule of the elements `x : J` with `t • x = 0` for every
`t ∈ 𝔪`. -/
noncomputable abbrev heckeTorsion (𝔪 : Ideal HeckeAlg) : Submodule HeckeAlg J :=
  Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg)

theorem mem_heckeTorsion_iff (𝔪 : Ideal HeckeAlg) (x : J) :
    x ∈ heckeTorsion J 𝔪 ↔ ∀ t ∈ 𝔪, t • x = 0 := by
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t.1 t.2⟩

theorem smul_mem_heckeTorsion {𝔪 : Ideal HeckeAlg} (g : G) {x : J}
    (hx : x ∈ heckeTorsion J 𝔪) : g • x ∈ heckeTorsion J 𝔪 := by
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  intro t
  rw [← smul_comm g (t : HeckeAlg) x, hx t, smul_zero]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

/-- **Quadratic Frobenius relation.** For every prime `ℓ` not dividing `N * p`, every valuation
subring `A` of `L` lying over `ℓ`, every `σ : L ≃ₐ[K] L` that is Frobenius at `ℓ` for `A`, and
every `x : J` with `p ^ n • x = 0` for some `n`, the relation
`σ • σ • x - heckeGen ℓ • (σ • x) + ℓ • x = 0` holds: each such Frobenius element satisfies
`σ² - T_ℓ σ + ℓ = 0` on the `p`-power torsion of `J`. -/
def FrobeniusQuadratic : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) →
          σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x = 0

end ModularCurve

namespace HeckeTorsionDensity

open Matrix

private theorem sq_eq_trace_smul_sub_det_smul_one {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · have h := M.aeval_self_charpoly
    rw [Matrix.charpoly_fin_two] at h
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
    exact sub_eq_zero.mp (by rw [← h]; abel)

private theorem pow_add_two_eq_trace_smul_sub_det_smul {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one, Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

private theorem trace_pow_add_two {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

private theorem sq_eq_of_quadRel {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * a = M.trace • a - M.det • (1 : B) :=
  sub_eq_zero.mp (by rw [← h]; abel)

private theorem mul_compl_eq_det_smul_one {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * (M.trace • (1 : B) - a) = M.det • (1 : B) := by
  rw [mul_sub, mul_smul_comm, mul_one, sq_eq_of_quadRel h]
  abel

private theorem compl_mul_eq_det_smul_one {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (M.trace • (1 : B) - a) * a = M.det • (1 : B) := by
  rw [sub_mul, smul_mul_assoc, one_mul, sq_eq_of_quadRel h]
  abel

private theorem commute_complRoot {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    Commute a (M.trace • (1 : B) - a) := by
  unfold Commute SemiconjBy
  rw [mul_compl_eq_det_smul_one h, compl_mul_eq_det_smul_one h]

private theorem pow_add_compl_pow_eq_trace_pow_smul_one {k : Type*} [CommRing k]
    {B : Type*} [Ring B] [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (m : ℕ) :
    a ^ m + (M.trace • (1 : B) - a) ^ m = (M ^ m).trace • (1 : B) := by
  set b : B := M.trace • (1 : B) - a with hb
  have hsum : a + b = M.trace • (1 : B) := by rw [hb]; abel
  have hcomm : Commute a b := commute_complRoot h
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      simp only [pow_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, two_smul]
    | 1 =>
      simp only [pow_one, hsum]
    | (m + 2) =>
      have hc1 : b * a ^ (m + 1) = a ^ (m + 1) * b := (hcomm.symm.pow_right (m + 1)).eq
      have hc2 : b * a ^ m = a ^ m * b := (hcomm.symm.pow_right m).eq
      have hrec : a ^ (m + 2) + b ^ (m + 2)
          = (a + b) * (a ^ (m + 1) + b ^ (m + 1)) - (a * b) * (a ^ m + b ^ m) := by
        have e1 : (a + b) * (a ^ (m + 1) + b ^ (m + 1))
            = a ^ (m + 2) + a * b ^ (m + 1) + (a ^ (m + 1) * b + b ^ (m + 2)) := by
          rw [add_mul, mul_add, mul_add, ← pow_succ', ← pow_succ', hc1]
        have e2 : (a * b) * (a ^ m + b ^ m)
            = a ^ (m + 1) * b + a * b ^ (m + 1) := by
          rw [mul_add, mul_assoc a b (a ^ m), hc2, ← mul_assoc, ← pow_succ',
            mul_assoc a b (b ^ m), ← pow_succ']
        rw [e1, e2]
        abel
      rw [hrec, ih (m + 1) (by omega), ih m (by omega), hsum,
        mul_compl_eq_det_smul_one h, smul_mul_smul_comm, smul_mul_smul_comm, mul_one,
        ← sub_smul, ← trace_pow_add_two]

private theorem quadRel_pow {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (n : ℕ) :
    a ^ n * a ^ n - (M ^ n).trace • a ^ n + (M ^ n).det • (1 : B) = 0 := by
  set b : B := M.trace • (1 : B) - a with hb
  have hcomm : Commute a b := commute_complRoot h
  have hsum : (M ^ n).trace • (1 : B) = a ^ n + b ^ n :=
    (pow_add_compl_pow_eq_trace_pow_smul_one h n).symm
  have hprod : (M ^ n).det • (1 : B) = a ^ n * b ^ n := by
    rw [← hcomm.mul_pow, hb, mul_compl_eq_det_smul_one h, smul_pow, one_pow,
      Matrix.det_pow]
  have hsmul : (M ^ n).trace • a ^ n = ((M ^ n).trace • (1 : B)) * a ^ n := by
    rw [smul_mul_assoc, one_mul]
  rw [hsmul, hsum, hprod, add_mul, (hcomm.pow_pow n n).eq]
  abel

private theorem quadRel_conj {k : Type*} [CommRing k] {B : Type*} [Ring B]
    [Algebra k B] {a u v : B} (huv : u * v = 1) (hvu : v * u = 1)
    {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B) = 0 := by
  have key : (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B)
      = u * (a * a - M.trace • a + M.det • (1 : B)) * v := by
    have e1 : (u * a * v) * (u * a * v) = u * (a * a) * v := by
      calc (u * a * v) * (u * a * v) = u * a * (v * u) * a * v := by
            simp only [mul_assoc]
        _ = u * (a * a) * v := by rw [hvu, mul_one, mul_assoc u a a]
    have e2 : M.trace • (u * a * v) = u * (M.trace • a) * v := by
      rw [mul_smul_comm, smul_mul_assoc]
    have e3 : M.det • (1 : B) = u * (M.det • (1 : B)) * v := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, huv]
    rw [mul_add, add_mul, mul_sub, sub_mul, ← e1, ← e2, ← e3]
  rw [key, h, mul_zero, zero_mul]

private theorem cayleyHamilton_of_frobeniusPowerDense {k : Type*} [CommRing k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 := by
  obtain ⟨ℓ, A, τ, g, n, hℓ, hS, hA, hτ, hmem⟩ := hdense σ
  rw [← div_eq_mul_inv] at hmem
  have keyρ : ρ σ = ρ g * (ρ τ) ^ n * ρ g⁻¹ := by
    rw [← ρ.div_mem_ker_iff.mp (Subgroup.mem_inf.mp hmem).1, map_mul, map_mul, map_pow]
  have keyρV : ρV σ = ρV g * (ρV τ) ^ n * ρV g⁻¹ := by
    rw [← ρV.div_mem_ker_iff.mp (Subgroup.mem_inf.mp hmem).2, map_mul, map_mul, map_pow]
  have htr : (ρ σ).trace = ((ρ τ) ^ n).trace := by
    rw [keyρ]
    exact Matrix.trace_units_conj (ρ.toHomUnits g) _
  have hdet : (ρ σ).det = ((ρ τ) ^ n).det := by
    rw [keyρ]
    exact Matrix.det_units_conj (ρ.toHomUnits g) _
  have hpow : (ρV τ) ^ n * (ρV τ) ^ n - ((ρ τ) ^ n).trace • (ρV τ) ^ n
      + ((ρ τ) ^ n).det • (1 : Module.End k V) = 0 :=
    quadRel_pow (hCH ℓ hℓ hS A hA τ hτ) n
  rw [htr, hdet, keyρV]
  exact quadRel_conj (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one]) hpow

end HeckeTorsionDensity

namespace ModularCurve

open HeckeTorsionDensity

private theorem smul_eq_zero_of_mem_heckeTorsion {J : Type*} [AddCommGroup J]
    [Module HeckeAlg J] {𝔪 : Ideal HeckeAlg} {x : J} (hx : x ∈ heckeTorsion J 𝔪)
    {t : HeckeAlg} (ht : t ∈ 𝔪) : t • x = 0 :=
  (mem_heckeTorsion_iff (J := J) 𝔪 x).mp hx t ht

private theorem smul_congr_of_mem_heckeTorsion {J : Type*} [AddCommGroup J]
    [Module HeckeAlg J] {𝔪 : Ideal HeckeAlg} {x : J} (hx : x ∈ heckeTorsion J 𝔪)
    {t t' : HeckeAlg} (h : Ideal.Quotient.mk 𝔪 t = Ideal.Quotient.mk 𝔪 t') :
    t • x = t' • x := by
  have hmem : t - t' ∈ 𝔪 := Ideal.Quotient.eq.mp h
  have hz := smul_eq_zero_of_mem_heckeTorsion hx hmem
  rw [sub_smul, sub_eq_zero] at hz
  exact hz

private noncomputable def heckeTorsionRep {G : Type*} [Group G] {J : Type*} [AddCommGroup J]
    [Module HeckeAlg J] [DistribMulAction G J] [SMulCommClass G HeckeAlg J]
    (𝔪 : Ideal HeckeAlg) :
    Representation (HeckeAlg ⧸ 𝔪) G (heckeTorsion J 𝔪 : Type _) where
  toFun σ :=
    { toFun := fun x => ⟨σ • (x : J), smul_mem_heckeTorsion J σ x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add σ (x : J) (y : J))
      map_smul' := fun q x => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine Subtype.ext ?_
        have hxq : ((Ideal.Quotient.mk 𝔪 t • x : heckeTorsion J 𝔪) : J)
            = t • (x : J) := by
          rw [Submodule.torsionBySet.mk_smul]
          rfl
        have hyq : ((Ideal.Quotient.mk 𝔪 t •
            (⟨σ • (x : J), smul_mem_heckeTorsion J σ x.2⟩ : heckeTorsion J 𝔪) :
              heckeTorsion J 𝔪) : J) = t • (σ • (x : J)) := by
          rw [Submodule.torsionBySet.mk_smul]
          rfl
        change σ • ((Ideal.Quotient.mk 𝔪 t • x : heckeTorsion J 𝔪) : J) = _
        rw [hxq]
        refine Eq.trans (smul_comm σ t (x : J)) ?_
        exact hyq.symm }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_smul G (x : J))
  map_mul' σ τ := LinearMap.ext fun x => Subtype.ext (mul_smul σ τ (x : J))

private theorem coe_heckeTorsionRep_quadRel_apply {G : Type*} [Group G]
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    [SMulCommClass G HeckeAlg J] {𝔪 : Ideal HeckeAlg}
    (ρ : G → Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (σ : G) (x : heckeTorsion J 𝔪) {t d : HeckeAlg}
    (ht : Ideal.Quotient.mk 𝔪 t = (ρ σ).trace)
    (hd : Ideal.Quotient.mk 𝔪 d = (ρ σ).det) :
    (((heckeTorsionRep (J := J) (𝔪) σ * heckeTorsionRep (J := J) (𝔪) σ
        - (ρ σ).trace • heckeTorsionRep (J := J) (𝔪) σ
        + (ρ σ).det • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪))) x
      : heckeTorsion J 𝔪) : J)
      = σ • σ • (x : J) - t • (σ • (x : J)) + d • (x : J) := by
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    mul_apply_eq_comp, one_apply_eq_self]
  rw [Submodule.coe_add, AddSubgroupClass.coe_sub]
  have hterm1 : ((heckeTorsionRep (J := J) (𝔪) σ
      (heckeTorsionRep (J := J) (𝔪) σ x) : heckeTorsion J 𝔪) : J)
      = σ • σ • (x : J) := rfl
  have hterm2 : (((ρ σ).trace • (heckeTorsionRep (J := J) (𝔪) σ x) :
      heckeTorsion J 𝔪) : J) = t • (σ • (x : J)) := by
    rw [← ht, Submodule.torsionBySet.mk_smul, SetLike.val_smul]
    rfl
  have hterm3 : (((ρ σ).det • x : heckeTorsion J 𝔪) : J) = d • (x : J) := by
    rw [← hd, Submodule.torsionBySet.mk_smul, SetLike.val_smul]
  rw [hterm1, hterm2, hterm3]

private theorem heckeTorsionRep_quadRel_iff {G : Type*} [Group G]
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    [SMulCommClass G HeckeAlg J] {𝔪 : Ideal HeckeAlg}
    (ρ : G → Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) (σ : G) :
    (heckeTorsionRep (J := J) (𝔪) σ * heckeTorsionRep (J := J) (𝔪) σ
        - (ρ σ).trace • heckeTorsionRep (J := J) (𝔪) σ
        + (ρ σ).det • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪)) = 0)
      ↔ (∀ x : J, x ∈ heckeTorsion J 𝔪 →
          ∀ t d : HeckeAlg, Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
            Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
            σ • σ • x - t • (σ • x) + d • x = 0) := by
  constructor
  · intro hEnd x hx t d ht hd
    have happ := LinearMap.congr_fun hEnd (⟨x, hx⟩ : heckeTorsion J 𝔪)
    rw [LinearMap.zero_apply, ← ZeroMemClass.coe_eq_zero,
      coe_heckeTorsionRep_quadRel_apply ρ σ _ ht hd] at happ
    exact happ
  · intro hCH
    refine LinearMap.ext fun x => ?_
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((ρ σ).trace)
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective ((ρ σ).det)
    rw [LinearMap.zero_apply, ← ZeroMemClass.coe_eq_zero,
      coe_heckeTorsionRep_quadRel_apply ρ σ _ ht hd]
    exact hCH (x : J) x.2 t d ht hd

private theorem fixingSubgroup_heckeTorsion_eq_ker {G : Type*} [Group G]
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    [SMulCommClass G HeckeAlg J] {𝔪 : Ideal HeckeAlg} :
    fixingSubgroup G (heckeTorsion J 𝔪 : Set J) = (heckeTorsionRep (J := J) (𝔪)).ker := by
  ext σ
  rw [mem_fixingSubgroup_iff, MonoidHom.mem_ker]
  constructor
  · intro h
    refine LinearMap.ext fun x => Subtype.ext ?_
    change σ • (x : J) = (x : J)
    exact h (x : J) x.2
  · intro h y hy
    have := congrArg Subtype.val
      (LinearMap.congr_fun h (⟨y, hy⟩ : heckeTorsion J 𝔪))
    exact this

/-- **Cayley–Hamilton on Hecke torsion.** Let `J` be a `HeckeAlg`-module with a commuting
action of `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`, and let `ρ` be a homomorphism from
that group to the `2 × 2` matrices over `HeckeAlg ⧸ 𝔪`. Assume:

* `p ∈ 𝔪`;
* `FrobeniusQuadratic N p J`, over `ℚ` and in `AlgebraicClosure ℚ`;
* no prime `ℓ ∉ S` divides `N * p`;
* for every prime `ℓ ∉ S`, every valuation subring `A` of `AlgebraicClosure ℚ` lying over
  `ℓ`, and every `σ` that is Frobenius at `ℓ` for `A`, the trace and determinant of `ρ σ`
  are the images of `heckeGen ℓ` and `ℓ` in `HeckeAlg ⧸ 𝔪`;
* `FrobeniusPowerDense S` modulo the intersection of the kernel of `ρ` with the subgroup
  fixing the `𝔪`-torsion of `J`.

Then for every `σ`, every `x` in the `𝔪`-torsion of `J`, and all `t d : HeckeAlg` whose
images in `HeckeAlg ⧸ 𝔪` are the trace and determinant of `ρ σ`, we have
`σ • σ • x - t • (σ • x) + d • x = 0`. -/
public theorem cayleyHamilton_forall_of_frobeniusQuadratic_of_dense {J : Type*}
    [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J),
      x ∈ heckeTorsion J 𝔪 →
      ∀ (t d : HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 := by
  have hCHfrobEnd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          heckeTorsionRep (J := J) (𝔪) τ * heckeTorsionRep (J := J) (𝔪) τ
            - (ρ τ).trace • heckeTorsionRep (J := J) (𝔪) τ
            + (ρ τ).det • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪)) = 0 := by
    intro ℓ hℓ hSℓ A hA τ hτ
    refine (heckeTorsionRep_quadRel_iff (⇑ρ) τ).mpr ?_
    intro x hx t d ht hd
    have hp0 : ((p : HeckeAlg)) • x = 0 := smul_eq_zero_of_mem_heckeTorsion hx hp
    have hex : ∃ n : ℕ, p ^ n • x = 0 := by
      refine ⟨1, ?_⟩
      rw [pow_one, ← Nat.cast_smul_eq_nsmul HeckeAlg p x]
      exact hp0
    have hkey := hES ℓ hℓ (hS ℓ hℓ hSℓ) A hA τ hτ x hex
    have hσx : τ • x ∈ heckeTorsion J 𝔪 := smul_mem_heckeTorsion J τ hx
    have h1 : t • (τ • x) = heckeGen ⟨ℓ, hℓ⟩ • (τ • x) :=
      smul_congr_of_mem_heckeTorsion hσx (by rw [ht, (hatt ℓ hℓ hSℓ A hA τ hτ).1])
    have h2 : d • x = ((ℓ : HeckeAlg)) • x :=
      smul_congr_of_mem_heckeTorsion hx (by rw [hd, (hatt ℓ hℓ hSℓ A hA τ hτ).2])
    have h3 : ((ℓ : HeckeAlg)) • x = ℓ • x := Nat.cast_smul_eq_nsmul HeckeAlg ℓ x
    rw [h1, h2, h3]
    exact hkey
  have hdense' : FrobeniusPowerDense S
      (ρ.ker ⊓ (heckeTorsionRep (J := J) (𝔪)).ker) := by
    rw [← fixingSubgroup_heckeTorsion_eq_ker]
    exact hdense
  intro σ
  have hEnd := HeckeTorsionDensity.cayleyHamilton_of_frobeniusPowerDense
    (heckeTorsionRep (J := J) (𝔪)) ρ hCHfrobEnd hdense' σ
  exact (heckeTorsionRep_quadRel_iff (⇑ρ) σ).mp hEnd

end ModularCurve

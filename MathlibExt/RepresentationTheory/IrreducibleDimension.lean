/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Dimension of an irreducible representation divides the group order

For a finite group `G` and an irreducible representation `ρ` of `G` over an
algebraically closed field of characteristic zero, the dimension of `ρ`
divides `|G|`. This is the classical Frobenius theorem on irreducible
degrees, proved by the character-theoretic argument: the operator
`∑ g, χ(g⁻¹) • ρ g` is a scalar (by Schur's lemma, since the character is
a class function), its trace is `|G|`, and it is also `dim ρ` times a
rational number `|G| / dim ρ`; integrality of traces of the powers of that
operator forces `|G| / dim ρ` to be an integer.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (target
`CharacterTheory.irred_dim_dvd_card` in
`v1/Atlas/AlgebraNotes/targets.yaml` / `report.json`).
-/

@[expose] public section

namespace CharacterTheory

universe u

/-- A rational number `r` is an integer as soon as `d * r ^ n` is an integer
for every `n`, where `d` is a fixed nonzero integer: the denominator of `r`
divides `d` to every power, so it must be `1`. -/
private theorem rat_int_of_pow_int
    (r : ℚ) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ n : ℕ, ∃ m : ℤ, (d : ℚ) * r ^ n = ↑m) :
    ∃ z : ℤ, r = ↑z := by
  suffices r.den = 1 from ⟨r.num, ((Rat.den_eq_one_iff r).mp this).symm⟩

  have hden_dvd : ∀ n : ℕ, (r.den : ℤ) ^ n ∣ d := by
    intro n
    obtain ⟨m, hm⟩ := h n
    have hr : r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    have key : d * r.num ^ n = m * (r.den : ℤ) ^ n := by
      have hcast : (d : ℚ) * (r.num : ℚ) ^ n = (m : ℚ) * (r.den : ℚ) ^ n := by
        rw [hr] at hm; rw [div_pow] at hm; field_simp at hm ⊢; linarith
      exact_mod_cast hcast
    have hcop : IsCoprime (r.num : ℤ) (r.den : ℤ) := by
      have hred := r.reduced.isCoprime
      rcases Int.natAbs_eq r.num with hpos | hneg
      · rw [hpos]; exact hred
      · rw [hneg]; exact IsCoprime.neg_left hred
    have hcop_pow : IsCoprime (r.num ^ n : ℤ) ((r.den : ℤ) ^ n) := hcop.pow
    have hdvd_prod : (r.den : ℤ) ^ n ∣ d * r.num ^ n := ⟨m, by linarith⟩
    rw [mul_comm] at hdvd_prod
    exact hcop_pow.symm.dvd_of_dvd_mul_left hdvd_prod

  by_contra hden_ne_one
  have hbpos : 1 < r.den := by have := r.den_pos; omega
  have hle : ∀ n : ℕ, r.den ^ n ≤ d.natAbs := by
    intro n
    have h1 : (↑(r.den ^ n) : ℤ) ∣ d := by push_cast; exact hden_dvd n
    have h2 : (↑(r.den ^ n) : ℤ) ≤ |d| :=
      Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs (↑(r.den ^ n)) d).mpr h1)
    rw [Int.abs_eq_natAbs] at h2
    exact_mod_cast h2
  have hgrow : d.natAbs < r.den ^ (d.natAbs + 1) := by
    have h1 : d.natAbs < 2 ^ d.natAbs := Nat.lt_two_pow_self
    have h2 : 2 ^ d.natAbs ≤ r.den ^ d.natAbs := Nat.pow_le_pow_left hbpos _
    have h3 : r.den ^ d.natAbs ≤ r.den ^ (d.natAbs + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    linarith
  linarith [hle (d.natAbs + 1)]

/-- The operator attached to a function `f` on `G`: `∑ g, f g • ρ g`. When
`f` is a class function, this operator commutes with every `ρ h`, so by
Schur's lemma it is a scalar for an irreducible `ρ`. -/
private noncomputable def repOfFun {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k) : V →ₗ[k] V :=
  ∑ g : G, f g • ρ g

/-- `repOfFun ρ f` is the image of the group-algebra element with coefficients
`f` under the algebra homomorphism attached to `ρ`. -/
private theorem repOfFun_eq_asAlgebraHom
    {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k) :
    repOfFun ρ f = ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm f)) := by
  simp only [repOfFun, Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
  rw [Finsupp.sum_fintype _ _ (by intro g; simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]

/-- If `f` is a class function, `repOfFun ρ f` commutes with `ρ h` for every
`h`, by reindexing the sum by conjugation by `h`. -/
private theorem repOfFun_comm_of_classFunction
    {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (h : G) :
    (repOfFun ρ f) ∘ₗ (ρ h) = (ρ h) ∘ₗ (repOfFun ρ f) := by
  ext v
  simp only [repOfFun, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  have mul_apply : ∀ (a b : G) (w : V), (ρ a) ((ρ b) w) = (ρ (a * b)) w := fun a b w => by
    rw [← LinearMap.comp_apply]
    exact congr_fun (congr_arg DFunLike.coe (ρ.map_mul a b).symm) w
  simp_rw [mul_apply]
  rw [← Fintype.sum_equiv ((Equiv.mulLeft h).trans (Equiv.mulRight h⁻¹)) _ _ (fun x => ?_)]
  show f x • (ρ (h * x)) v = f (h * x * h⁻¹) • (ρ (h * x * h⁻¹ * h)) v
  rw [hf x h, show h * x * h⁻¹ * h = h * x from by group]

/-- For an irreducible representation over an algebraically closed field,
`repOfFun ρ f` is a scalar whenever `f` is a class function: it is an
intertwining operator, and Schur's lemma says every intertwining operator
of an irreducible representation is a scalar. -/
private theorem irred_rep_class_fun_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (f : G → k) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    ∃ c : k, repOfFun ρ f = c • LinearMap.id := by
  have hbij := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) (k := k)
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := repOfFun ρ f
      isIntertwining' := repOfFun_comm_of_classFunction ρ f hf }
  obtain ⟨c, hc⟩ := hbij.2 T
  exact ⟨c, by
    have h1 : T.toLinearMap = repOfFun ρ f := rfl
    rw [← h1, ← hc]; ext v; simp [Algebra.algebraMap_eq_smul_one]⟩

/-- Taking `f g = χ(g⁻¹)`: the operator `repOfFun ρ f` is a scalar `c`,
and comparing traces with character orthogonality gives
`c * dim ρ = |G|`. -/
private theorem rep_conj_char_eq_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ c : k, repOfFun ρ (fun g => ρ.character g⁻¹) = c • LinearMap.id ∧
      c * (Module.finrank k V : k) = (Nat.card G : k) := by

  have hcf : ∀ g h : G, ρ.character (h * g * h⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g h
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group]
    exact Representation.char_conj ρ g⁻¹ h

  obtain ⟨c, heq⟩ := irred_rep_class_fun_scalar ρ (fun g => ρ.character g⁻¹) hcf
  refine ⟨c, heq, ?_⟩

  have htrace := congr_arg (LinearMap.trace k V) heq
  rw [LinearMap.map_smul_of_tower, LinearMap.trace_id, smul_eq_mul] at htrace
  simp only [repOfFun, map_sum, LinearMap.map_smul_of_tower, smul_eq_mul] at htrace

  have key : ∑ g : G, ρ.character g * ρ.character g⁻¹ = c * ↑(Module.finrank k V) := by
    rw [← htrace]
    simp only [Representation.character]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [inv_inv])

  have hortho : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k) := by
    have h := Representation.char_orthonormal ρ ρ
    simp only [show Nonempty (ρ.Equiv ρ) from ⟨Representation.Equiv.refl ρ⟩, ite_true] at h
    have hne : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
    exact mul_left_cancel₀ (inv_ne_zero hne) (h.trans (inv_mul_cancel₀ hne).symm)
  exact key.symm.trans hortho

/-- Coefficients of powers of a group-algebra element with integral
coefficients stay integral: the coefficient of a product is a sum of
products of coefficients. -/
private lemma monoidAlgebra_pow_isIntegral_general
    {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    (φ : MonoidAlgebra k G) (hφ : ∀ g : G, IsIntegral ℤ (φ.coeff g))
    (n : ℕ) : ∀ g : G, IsIntegral ℤ ((φ ^ n).coeff g) := by
  induction n with
  | zero =>
    intro g
    simp only [pow_zero]
    by_cases hg : g = 1
    · subst hg; simp [MonoidAlgebra.one_def]; exact isIntegral_one
    · simp [MonoidAlgebra.one_def, hg]; exact isIntegral_zero
  | succ m ih =>
    intro g
    rw [pow_succ]
    classical
    have hmul : (φ ^ m * φ).coeff g =
        ∑ p ∈ (Finset.univ (α := G × G)).filter (fun p => p.1 * p.2 = g),
          (φ ^ m).coeff p.1 * φ.coeff p.2 := by
      apply MonoidAlgebra.coeff_mul_antidiag
      simp
    rw [hmul]
    apply IsIntegral.sum
    intro p _
    exact (ih p.1).mul (hφ p.2)

/-- The `Nat.card` form of the dimension-divides-order theorem. The scalar
`c` from `rep_conj_char_eq_scalar` equals `|G| / dim ρ` in `k`, and its
powers have integral trace, so `|G| / dim ρ` is an integer. -/
private theorem mainTheorem_dim_dvd_card_charZero
    {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [NeZero (Nat.card G : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Nat.card G := by
  set d := Module.finrank k V

  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 := Representation.IsIrreducible.finrank_intertwiningMap_self ρ
    have hzero : Module.finrank k (V →ₗ[k] V) = 0 := by
      rw [Module.finrank_linearMap]; simp [show Module.finrank k V = 0 from h0]
    have hss : Subsingleton (V →ₗ[k] V) := Module.finrank_zero_iff.mp hzero
    have h2 : Module.finrank k (ρ.IntertwiningMap ρ) = 0 := Module.finrank_zero_iff.mpr
      ((Representation.IntertwiningMap.toLinearMap_injective ρ ρ).subsingleton)
    linarith
  have hdk_ne : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  have : Invertible (Nat.card G : k) := invertibleOfNonzero (NeZero.ne _)

  obtain ⟨c, hcf, hcd⟩ := rep_conj_char_eq_scalar ρ

  set r : ℚ := (Nat.card G : ℚ) / (d : ℚ)
  have hd_rat_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd_ne
  have hc_eq : c = algebraMap ℚ k r := by
    have h1 : c = (Nat.card G : k) * (d : k)⁻¹ := by
      rw [← hcd, mul_assoc, mul_inv_cancel₀ hdk_ne, mul_one]
    rw [h1]; simp [r, map_div₀]; ring

  have hf_int : ∀ g : G, IsIntegral ℤ (ρ.character g⁻¹) := fun g =>
    Representation.isIntegral_character ρ g⁻¹

  have hρf : repOfFun ρ (fun g => ρ.character g⁻¹) = (algebraMap ℚ k r) • LinearMap.id := by
    rw [hcf, hc_eq]

  have h_pow_int : ∀ n : ℕ, ∃ m : ℤ, (d : ℚ) * r ^ n = ↑m := by
    intro n
    set φ : MonoidAlgebra k G :=
      MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun g => ρ.character g⁻¹))
    have hbase : ∀ g : G, IsIntegral ℤ (φ.coeff g) := by
      intro g; simp [φ, Finsupp.equivFunOnFinite]; exact hf_int g

    have hpow : (repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n =
        ((algebraMap ℚ k r) ^ n) • (LinearMap.id : V →ₗ[k] V) := by
      rw [hρf]; change ((algebraMap ℚ k r) • (1 : Module.End k V)) ^ n = _
      rw [smul_pow, one_pow]; rfl

    have htrace_eq : LinearMap.trace k V ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n) =
        (d : k) * (algebraMap ℚ k r) ^ n := by
      rw [hpow, LinearMap.map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

    have htrace_sum : LinearMap.trace k V ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n) =
        ∑ g : G, (φ ^ n).coeff g * LinearMap.trace k V (ρ g) := by
      rw [repOfFun_eq_asAlgebraHom, ← map_pow]
      simp only [Representation.asAlgebraHom, MonoidAlgebra.lift_apply]
      rw [Finsupp.sum_fintype _ _ (by intro g; simp), map_sum]
      congr 1; ext g; rw [LinearMap.map_smul, smul_eq_mul]

    have htrace_int : IsIntegral ℤ (LinearMap.trace k V
        ((repOfFun ρ (fun g => ρ.character g⁻¹)) ^ n)) := by
      rw [htrace_sum]; apply IsIntegral.sum; intro g _
      exact (monoidAlgebra_pow_isIntegral_general φ hbase n g).mul (Representation.isIntegral_character ρ g)

    rw [htrace_eq] at htrace_int
    have hrat : (d : k) * (algebraMap ℚ k r) ^ n = algebraMap ℚ k ((d : ℚ) * r ^ n) := by
      push_cast; ring
    rw [hrat] at htrace_int
    have hq_int : IsIntegral ℤ ((d : ℚ) * r ^ n) :=
      isIntegral_algebraMap_iff.mp htrace_int
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq_int
    exact ⟨z, by exact_mod_cast hz.symm⟩

  have hr_int : ∃ z : ℤ, r = ↑z :=
    rat_int_of_pow_int r (d : ℤ) (by exact_mod_cast hd_ne) h_pow_int

  obtain ⟨z, hz⟩ := hr_int
  have hr_pos : (0 : ℚ) < r := by
    apply div_pos
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.pos_of_ne_zero hd_ne
  have hz_pos : 0 < z := by
    have : (0 : ℚ) < (z : ℚ) := hz ▸ hr_pos; exact_mod_cast this
  have key : d * z.toNat = Nat.card G := by
    have h1 : (d : ℚ) * r = (Nat.card G : ℚ) := mul_div_cancel₀ _ hd_rat_ne
    rw [hz] at h1
    have h2 : (d : ℤ) * z = (Nat.card G : ℤ) := by exact_mod_cast h1
    zify; rw [Int.toNat_of_nonneg hz_pos.le]; exact_mod_cast h2
  exact ⟨z.toNat, key.symm⟩

/-- **Dimension of an irreducible representation divides the group order.**
If `ρ` is an irreducible representation of a finite group `G` over an
algebraically closed field `k` of characteristic zero, then
`dim_k ρ ∣ |G|`. In particular, over `ℂ`, every irreducible degree divides
the order of the group. -/
theorem irred_dim_dvd_card
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Fintype.card G := by
  letI : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'⟩
  rw [← Nat.card_eq_fintype_card]
  exact mainTheorem_dim_dvd_card_charZero ρ

end CharacterTheory

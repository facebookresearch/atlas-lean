/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ThickBhSets
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Affine equivalences between Bose sets

`zModAffinelyEquivalent_boseSet` gives three sufficient conditions for two generalized Bose
sets to differ by an affine change of exponents.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Membership in a Bose set.** Let $F$ be a finite field with $q$ elements, let $K$ be a field
extension of $F$, let $\theta \in K$, and let $h$ and $b$ be natural numbers. A residue
$a \in \mathbb{Z}/(q^h - 1)\mathbb{Z}$ lies in the Bose set $\mathrm{Bose}_h(q, b)$ built from
$F$, $K$ and $\theta$ if and only if $\theta^a = \theta^b + v$ for some $v \in F$, where
$\theta^a$ means $\theta$ raised to the least nonnegative representative of $a$ (or to $|a|$
when $h = 0$, since then $\mathbb{Z}/(q^h - 1)\mathbb{Z} = \mathbb{Z}$).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 1. -/
public theorem mem_boseSet {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ h - 1)) :
    a ∈ boseSet F h θ b ↔ ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v :=
  Iff.rfl

namespace zModAffinelyEquivalent_boseSet

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

local notation "baseSpace" => LinearMap.range (Algebra.linearMap F K)

private theorem frobenius_mem_iff [Finite F] [Finite K] {p : ℕ} [ExpChar F p] [ExpChar K p]
    (i : ℕ) (x : K) : x ^ p ^ i ∈ baseSpace ↔ x ∈ baseSpace := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv F p i).surjective v
    refine ⟨w, (iterateFrobeniusEquiv K p i).injective ?_⟩
    simpa only [iterateFrobeniusEquiv_def, Algebra.linearMap_apply, map_pow] using hv
  · rintro ⟨v, rfl⟩
    exact ⟨v ^ p ^ i, map_pow (algebraMap F K) _ _⟩

variable [Fintype F] {θ : K} {h b e : ℕ}

local notation "M" => Fintype.card F ^ h - 1
local notation "Q" => M / (Fintype.card F - 1)

private theorem mem_iff_sub_mem (a : ZMod M) :
    a ∈ boseSet F h θ b ↔ θ ^ a.val - θ ^ b ∈ baseSpace := by
  rw [mem_boseSet]
  change (∃ v : F, _) ↔ ∃ v : F, algebraMap F K v = _
  exact exists_congr fun v => by rw [eq_sub_iff_add_eq, add_comm, eq_comm]

private theorem natCast_mem (hord : orderOf θ = M) (n k : ℕ) :
    (n : ZMod M) ∈ boseSet F h θ k ↔ θ ^ n - θ ^ k ∈ baseSpace := by
  rw [mem_iff_sub_mem, ZMod.val_natCast, ← hord, pow_mod_orderOf]

/-- After centering exponents at `k`, each multiple of `Q` in `k` contributes a nonzero
base-field scalar to the membership test. -/
private theorem centered_mem [Finite K] [NeZero M] (hK : Module.finrank F K = h)
    (hord : orderOf θ = M) (hθ₀ : θ ≠ 0) (t : ZMod M) (k : ℕ) :
    t + k ∈ boseSet F h θ k ↔ θ ^ (k % Q) * (θ ^ t.val - 1) ∈ baseSpace := by
  have hnorm : algebraMap F K (Algebra.norm F θ) = θ ^ Q := by
    rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := F) (V := K),
      hK, Nat.card_eq_fintype_card]
  have hpow : θ ^ k = (Algebra.norm F θ ^ (k / Q)) • θ ^ (k % Q) := by
    rw [Algebra.smul_def, map_pow, hnorm, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have hcast : t + k = ((t.val + k : ℕ) : ZMod M) := by simp
  rw [hcast, natCast_mem hord, pow_add, mul_comm, ← mul_sub_one, hpow, smul_mul_assoc,
    Submodule.smul_mem_iff _ (pow_ne_zero _ (Algebra.norm_ne_zero_iff.mpr hθ₀))]

private theorem affine_of_congr [Finite K] [NeZero M] (hK : Module.finrank F K = h)
    (hord : orderOf θ = M) (hθ₀ : θ ≠ 0) (hbe : b ≡ e [MOD Q]) :
    ZModAffinelyEquivalent (boseSet F h θ b) (boseSet F h θ e) := by
  have hmem (t : ZMod M) : t + b ∈ boseSet F h θ b ↔ t + e ∈ boseSet F h θ e := by
    rw [centered_mem hK hord hθ₀, centered_mem hK hord hθ₀, hbe]
  refine ⟨1, e - b, isUnit_one, ?_⟩
  simp only [one_mul]
  ext a
  constructor
  · intro ha
    exact ⟨a - e + b, (hmem _).mpr (by simpa using ha), by abel_nf⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (hmem (x - b)).mp (by simpa using hx)

private theorem affine_of_frobenius [Finite K] [NeZero M] (hh : 0 < h)
    (hord : orderOf θ = M) {i : ℕ} (hi : b ≡ ringChar F ^ i * e [MOD M]) :
    ZModAffinelyEquivalent (boseSet F h θ b) (boseSet F h θ e) := by
  let p := ringChar F
  obtain ⟨n, hp, hq⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_injective_algebraMap' F p
  have hdvd : p ∣ Fintype.card F ^ h := by
    rw [hq, ← pow_mul]
    exact dvd_pow_self _ (Nat.mul_ne_zero n.ne_zero hh.ne')
  have hcop : p.Coprime M := Nat.Coprime.of_dvd_left hdvd
    ((Nat.coprime_self_sub_right (Nat.one_le_pow _ _ Fintype.card_pos)).mpr
      (Nat.coprime_one_right _))
  obtain ⟨d, hd⟩ := (ZMod.isUnit_iff_coprime _ _).mpr (hcop.pow_left i)
  have hbpow : θ ^ b = (θ ^ e) ^ p ^ i := by
    rw [← pow_mul, mul_comm e, ← pow_mod_orderOf θ b, hord, hi, ← hord, pow_mod_orderOf]
  have hmem (a : ZMod M) : (d : ZMod M) * a ∈ boseSet F h θ b ↔ a ∈ boseSet F h θ e := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    rw [hd, ← Nat.cast_mul, natCast_mem hord, natCast_mem hord, mul_comm, pow_mul, hbpow,
      ← sub_pow_expChar_pow, frobenius_mem_iff]
  refine ⟨↑d⁻¹, 0, d⁻¹.isUnit, ?_⟩
  simp only [add_zero]
  ext a
  constructor
  · intro ha
    exact ⟨d * a, (hmem a).mpr ha, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact (hmem _).mp (by simpa)

end zModAffinelyEquivalent_boseSet

open zModAffinelyEquivalent_boseSet in
/-- **Affine equivalences between Bose sets.** Let $F$ be a finite field with $q$ elements and
characteristic $p$, let $h \ge 2$, let $K$ be a field extension of $F$ of degree $h$, and let
$\theta \in K$ have order $|K| - 1$, that is, generate $K^\times$. Let $b$ and $e$ be natural
numbers such that the minimal polynomials of $\theta^b$ and $\theta^e$ over $F$ both have
degree $h$. Suppose that (i) $b \equiv e \pmod{(q^h - 1)/(q - 1)}$, or
(ii) $\theta^b - \theta^e \in F$, or (iii) $b \equiv p^i e \pmod{q^h - 1}$ for some natural
number $i$. Then the Bose sets $\mathrm{Bose}_h(q, b)$ and $\mathrm{Bose}_h(q, e)$ built from
$F$, $K$ and $\theta$ are affinely equivalent.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 4 (items (i)–(iii)) (`jis-2024-24.1.2-thm-4`). -/
public theorem zModAffinelyEquivalent_boseSet {F K : Type*} [Field F] [Fintype F]
    [Field K] [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h)
    {θ : K} (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (he : (minpoly F (θ ^ e)).natDegree = h)
    (hbe : b ≡ e [MOD (Fintype.card F ^ h - 1) / (Fintype.card F - 1)] ∨
      θ ^ b - θ ^ e ∈ Set.range (algebraMap F K) ∨
      ∃ i : ℕ, b ≡ ringChar F ^ i * e [MOD Fintype.card F ^ h - 1]) :
    ZModAffinelyEquivalent (boseSet F h θ b) (boseSet F h θ e) := by
  have hcard : Fintype.card K = Fintype.card F ^ h := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  have hord := hθ.trans (congrArg (· - 1) hcard)
  have hpos : 0 < Fintype.card F ^ h - 1 := by
    rw [← hcard]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  have : NeZero (Fintype.card F ^ h - 1) := ⟨hpos.ne'⟩
  rcases hbe with hmod | hdiff | ⟨i, hi⟩
  · have hθ₀ : θ ≠ 0 := by
      rintro rfl
      simp [← hord] at hpos
    exact affine_of_congr hK hord hθ₀ hmod
  · have heq : boseSet F h θ b = boseSet F h θ e := by
      ext a
      rw [mem_iff_sub_mem, mem_iff_sub_mem]
      have hv : θ ^ b - θ ^ e ∈ LinearMap.range (Algebra.linearMap F K) := hdiff
      rw [← sub_add_sub_cancel (θ ^ a.val) (θ ^ b) (θ ^ e), Submodule.add_mem_iff_left _ hv]
    rw [heq]
    exact zModAffinelyEquivalent_refl _
  · exact affine_of_frobenius (by omega) hord hi

end

end MetaMathlibExt

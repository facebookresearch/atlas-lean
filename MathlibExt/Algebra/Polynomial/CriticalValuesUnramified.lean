/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Unramified

/-!
# A polynomial map is unramified away from its critical values

Let `k` be an algebraically closed field and `p ∈ k[z]` a polynomial with `p' ≠ 0`. On the
affine line, `p` is the morphism `Spec k[z] → Spec k[w]` given by `w ↦ p(z)`, that is, the ring
map `Polynomial.compRingHom p : k[w] → k[z]`, `q ↦ q ∘ p`. Let
`S = {p(r) : r ∈ k, p'(r) = 0}` be the finite set of its finite critical values and
`s = ∏_{c ∈ S} (w - c)`. The restriction of `p` over `𝔸¹ ∖ S` is the ring map
`k[w]_s → k[z]_{s ∘ p}`, and this file shows that it is formally unramified: its module of
Kähler differentials vanishes. As `p⁻¹(∞) = {∞}` for the extension of `p` to `ℙ¹`, this is
the restriction of `p : ℙ¹ → ℙ¹` over `ℙ¹ ∖ ({∞} ∪ S)`; that identification and the fibre over
`∞` are not formalized here.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof
of Lemma 3.5, pp. 262–263: "S₁ ∪ {∞} is the set of critical values of p₁", where
`S₁ = p₁({r : p₁'(r) = 0})`, and Köck writes `Crit(t) = t(supp(Ω¹_{X/ℙ¹}))` in the proof of
Lemma 3.4. The result here is the inclusion `Crit(p) ⊆ S ∪ {∞}`.

## Main results

* `Polynomial.formallyUnramified_awayMap_compRingHom`: the restriction of `p` over the
  complement of its finite critical values is formally unramified, for `p' ≠ 0`.
* `Polynomial.formallyUnramified_awayMap_compRingHom_of_natDegree_pos`: the same for a
  nonconstant `p` in characteristic zero.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {k : Type*} [Field k] [DecidableEq k]

/-- **A polynomial map is unramified away from its critical values.** Let `k` be an
algebraically closed field and `p ∈ k[X]` a polynomial whose derivative `p'` is nonzero. Let
`S = {p(r) : r ∈ k, p'(r) = 0}` and `s = ∏_{c ∈ S} (X - c)`. Then the ring map
`k[X]_s → k[X]_{s ∘ p}` induced by `q ↦ q ∘ p` (`Localization.awayMap (compRingHom p) s`),
the morphism `z ↦ p(z)` of the affine line restricted over `𝔸¹ ∖ S`, is formally
unramified.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof
of Lemma 3.5, pp. 262–263 ("S₁ ∪ {∞} is the set of critical values of p₁"), in the direction
that `p` is unramified over the complement. Köck assumes characteristic zero and `p`
nonconstant; this statement needs only `p' ≠ 0`
(`formallyUnramified_awayMap_compRingHom_of_natDegree_pos` has Köck's hypotheses). The
point `∞` of `ℙ¹` and its fibre `p⁻¹(∞) = {∞}` are not formalized here. -/
theorem formallyUnramified_awayMap_compRingHom [IsAlgClosed k] (p : k[X])
    (hp : derivative p ≠ 0) :
    (Localization.awayMap (compRingHom p)
      (∏ c ∈ (derivative p).roots.toFinset.image (fun r => p.eval r),
        (X - C c))).FormallyUnramified := by
  set s : k[X] := ∏ c ∈ (derivative p).roots.toFinset.image (fun r => p.eval r), (X - C c)
    with hs
  set f := compRingHom p
  let R := Localization.Away s
  let S := Localization.Away (f s)
  let _ : Algebra R S := (Localization.awayMap f s).toAlgebra
  let φ : k[X] →+* S := algebraMap k[X] S
  have hφf : ∀ q : k[X], φ (f q) = algebraMap R S (algebraMap k[X] R q) := fun q => by
    change _ = Localization.awayMap f s (algebraMap k[X] R q)
    simp only [Localization.awayMap, IsLocalization.Away.map]
    exact (IsLocalization.map_eq _ q).symm
  let D := KaehlerDifferential.D R S
  have hmul : ∀ q₁ q₂ : k[X], D (φ q₁) = φ (derivative q₁) • D (φ X) →
      D (φ q₂) = φ (derivative q₂) • D (φ X) →
      D (φ (q₁ * q₂)) = φ (derivative (q₁ * q₂)) • D (φ X) := by
    intro q₁ q₂ h₁ h₂
    rw [map_mul, Derivation.leibniz, h₁, h₂, derivative_mul, map_add, map_mul, map_mul, add_smul,
      smul_smul, smul_smul, mul_comm (φ q₂), add_comm]
  have hP : ∀ q : k[X], D (φ q) = φ (derivative q) • D (φ X) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      have : φ (C a) = algebraMap R S (algebraMap k[X] R (C a)) := by
        rw [← hφf]
        simp [f]
      rw [this, Derivation.map_algebraMap, derivative_C, map_zero, zero_smul]
    | add q₁ q₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, derivative_add, map_add, add_smul]
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc]
      refine hmul _ _ h ?_
      rw [derivative_X, map_one, one_smul]
  have hunit : IsUnit (φ (derivative p)) := by
    have hsplit := IsAlgClosed.splits (derivative p)
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.mp hsplit), map_mul,
      map_multiset_prod]
    refine IsUnit.mul ?_ ?_
    · exact (isUnit_C.mpr (leadingCoeff_ne_zero.mpr hp).isUnit).map φ
    · refine IsUnit.multisetProd_iff.mpr fun u hu => ?_
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp (Multiset.map_map _ _ _ ▸ hu)
      have hdvd : X - C r ∣ f s := by
        rw [dvd_iff_isRoot]
        simp only [f, coe_compRingHom_apply, IsRoot, eval_comp, hs, eval_prod, eval_sub, eval_X,
          eval_C]
        apply Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr hr))
        exact sub_self _
      change IsUnit (φ (X - C r))
      exact isUnit_of_dvd_unit (_root_.map_dvd φ hdvd) (IsLocalization.Away.algebraMap_isUnit (f s))
  have hz : D (φ X) = 0 := by
    have h0 : D (φ (f X)) = 0 := by rw [hφf, Derivation.map_algebraMap]
    have hfX : f X = p := by simp [f]
    rw [hfX, hP] at h0
    exact hunit.smul_left_cancel.mp (h0.trans (smul_zero _).symm)
  have hall : ∀ x : S, D x = 0 := by
    intro x
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f s)) x
    have ha : D (φ a) = 0 := by rw [hP, hz, smul_zero]
    have hb : D (φ b) = 0 := by rw [hP, hz, smul_zero]
    have h1 := congrArg D (IsLocalization.mk'_spec S a b)
    rw [Derivation.leibniz, hb, smul_zero, zero_add] at h1
    have hbu : IsUnit (φ (b : k[X])) := IsLocalization.map_units S b
    exact hbu.smul_left_cancel.mp ((h1.trans ha).trans (smul_zero _).symm)
  change Algebra.FormallyUnramified R S
  refine ⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩
  have hω : ω ∈ Submodule.span S (Set.range D) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact hall y
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul a x _ hx => rw [hx, smul_zero]

/-- **A nonconstant polynomial map is unramified away from its critical values, in
characteristic zero.** Let `k` be an algebraically closed field of characteristic zero and
`p ∈ k[X]` nonconstant. With `S = {p(r) : r ∈ k, p'(r) = 0}` and `s = ∏_{c ∈ S} (X - c)`, the
ring map `k[X]_s → k[X]_{s ∘ p}` induced by `q ↦ q ∘ p` is formally unramified.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof
of Lemma 3.5, pp. 262–263, in the direction that `p` is unramified over the complement of
`S ∪ {∞}`. -/
theorem formallyUnramified_awayMap_compRingHom_of_natDegree_pos [IsAlgClosed k] [CharZero k]
    (p : k[X]) (hp : 0 < p.natDegree) :
    (Localization.awayMap (compRingHom p)
      (∏ c ∈ (derivative p).roots.toFinset.image (fun r => p.eval r),
        (X - C c))).FormallyUnramified :=
  formallyUnramified_awayMap_compRingHom p fun h =>
    hp.ne' (derivative_eq_zero.mp h)

end Polynomial

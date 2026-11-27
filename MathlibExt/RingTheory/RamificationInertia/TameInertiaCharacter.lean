/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean`
and
`P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.RingTheory.IntegralDomain

/-!
# The tame character of an inertia group

Let a group `G` act on a commutative ring `B`, let `𝔓` be a maximal ideal of `B` with finite
residue field, and let `ϖ ∈ 𝔓` generate `𝔓` modulo `𝔓 ^ 2` with `c * ϖ ∈ 𝔓 ^ 2` only for
`c ∈ 𝔓`. The coefficient `t` in `σ • ϖ ≡ ϖ * t` modulo `𝔓 ^ 2` is then a unit modulo `𝔓` for
every `σ` in the inertia group of `𝔓`, and it is multiplicative in `σ`.

## Main results

* `Ideal.exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer`: there is a
  homomorphism `θ` from the inertia group of `𝔓` to `(B ⧸ 𝔓)ˣ` such that `θ σ` is the residue
  class of `t` exactly when `σ • ϖ ≡ ϖ * t` modulo `𝔓 ^ 2`, `θ σ = 1` exactly when `σ` acts
  trivially modulo `𝔓 ^ 2` on all of `B`, and the range of `θ` is cyclic.
-/

@[expose] public section

namespace Ideal

section TameInertiaCharacter

variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]

private theorem smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have hzz : σ • z = (σ • z - z) + z := by ring
  rw [hzz]; exact 𝔓.add_mem h hz

private theorem smul_mem_sq_of_mem_inertia (𝔓 : Ideal B) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    σ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B σ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz'
    exact smul_mem_of_mem_inertia 𝔓 hσ hz'
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

private theorem pow_sub_pow_mem_sq (𝔓 : Ideal B) {a b : B} (hab : a - b ∈ 𝔓)
    {N : ℕ} (hN : (N : B) ∈ 𝔓) :
    a ^ N - b ^ N ∈ 𝔓 ^ 2 := by
  set m := a - b with hm
  have ha : a = b + m := by rw [hm]; ring
  rw [ha, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases Nat.lt_or_ge (N - k) 2 with hlt | hge
  · have hk1 : N - k = 1 := by omega
    have hkN : k = N - 1 := by omega
    have hch : (N.choose k : B) = N := by
      rw [hkN, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
    rw [hk1, pow_one, hch, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hab) hN
  · have hmem : m ^ (N - k) ∈ 𝔓 ^ 2 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rw [hj, pow_add]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hab 2)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

private theorem smul_sub_mem_sq_of_mem_inertia (𝔓 : Ideal B) [𝔓.IsMaximal]
    [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hϖ : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    {σ : G} (hσ : σ ∈ 𝔓.inertia G) (hσϖ : σ • ϖ - ϖ ∈ 𝔓 ^ 2) (x : B) :
    σ • x - x ∈ 𝔓 ^ 2 := by
  classical
  let : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  let : Fintype (B ⧸ 𝔓) := Fintype.ofFinite _
  set N := Fintype.card (B ⧸ 𝔓) with hNdef
  have hN : (N : B) ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hNdef]
    exact Nat.cast_card_eq_zero (B ⧸ 𝔓)
  have hF : x ^ N - x ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hNdef,
      FiniteField.pow_card, sub_self]
  obtain ⟨y, hy⟩ := hϖ (x - x ^ N) (by rw [← neg_sub]; exact 𝔓.neg_mem hF)
  set e := x - x ^ N - ϖ * y with he
  have hx : x = x ^ N + ϖ * y + e := by rw [he]; ring
  have h1 : σ • (x ^ N) - x ^ N ∈ 𝔓 ^ 2 := by
    rw [smul_pow']
    exact pow_sub_pow_mem_sq 𝔓 (hσ x) hN
  have h2 : σ • (ϖ * y) - ϖ * y ∈ 𝔓 ^ 2 := by
    have hdecomp : σ • (ϖ * y) - ϖ * y
        = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
      rw [smul_mul']; ring
    rw [hdecomp]
    refine (𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hσϖ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hϖP (hσ y)
  have h3 : σ • e - e ∈ 𝔓 ^ 2 :=
    (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) hy
  have hdecomp : σ • x - x = (σ • (x ^ N) - x ^ N)
      + (σ • (ϖ * y) - ϖ * y) + (σ • e - e) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_add]; ring
  rw [hdecomp]
  exact (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem h1 h2) h3

variable (𝔓 : Ideal B) [𝔓.IsMaximal] {ϖ : B}

omit [𝔓.IsMaximal] in
private theorem exists_tameCoeff (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) : ∃ t : B, σ • ϖ - ϖ * t ∈ 𝔓 ^ 2 :=
  hgen (σ • ϖ) (smul_mem_of_mem_inertia 𝔓 hσ hϖP)

private noncomputable def tameCoeff (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) : B :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose

omit [𝔓.IsMaximal] in
private theorem tameCoeff_spec (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) :
    σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 :=
  (exists_tameCoeff 𝔓 hϖP hgen hσ).choose_spec

omit [𝔓.IsMaximal] in
private theorem tameCoeff_unique
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {z t t' : B}
    (ht : z - ϖ * t ∈ 𝔓 ^ 2) (ht' : z - ϖ * t' ∈ 𝔓 ^ 2) : t - t' ∈ 𝔓 := by
  apply hreg
  have hdecomp : (t - t') * ϖ = (z - ϖ * t') - (z - ϖ * t) := by ring
  rw [hdecomp]
  exact (𝔓 ^ 2).sub_mem ht' ht

private theorem tameCoeff_not_mem (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) {σ : G}
    (hσ : σ ∈ 𝔓.inertia G) : tameCoeff 𝔓 hϖP hgen hσ ∉ 𝔓 := by
  intro ht
  have h1 : σ • ϖ ∈ 𝔓 ^ 2 := by
    have h := tameCoeff_spec 𝔓 hϖP hgen hσ
    have h2 : ϖ * tameCoeff 𝔓 hϖP hgen hσ ∈ 𝔓 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hϖP ht
    have hdecomp : σ • ϖ = (σ • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen hσ)
        + ϖ * tameCoeff 𝔓 hϖP hgen hσ := by ring
    rw [hdecomp]; exact (𝔓 ^ 2).add_mem h h2
  have h2 : ϖ ∈ 𝔓 ^ 2 := by
    have h := smul_mem_sq_of_mem_inertia 𝔓 (Subgroup.inv_mem _ hσ) h1
    rwa [inv_smul_smul] at h
  have h3 : (1 : B) ∈ 𝔓 := hreg 1 (by rwa [one_mul])
  have hprime : 𝔓.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  exact hprime.one_notMem h3

private noncomputable def tameCharFun (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) :
    (B ⧸ 𝔓)ˣ :=
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  Units.mk0 (Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2))
    (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
        exact tameCoeff_not_mem 𝔓 hϖP hgen hreg σ.2)

private theorem val_tameCharFun (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) (σ : 𝔓.inertia G) :
    ((tameCharFun 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓)
      = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

private noncomputable def tameChar (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    (𝔓.inertia G) →* (B ⧸ 𝔓)ˣ where
  toFun := tameCharFun 𝔓 hϖP hgen hreg
  map_one' := by
    apply Units.ext
    rw [val_tameCharFun, Units.val_one, ← map_one (Ideal.Quotient.mk 𝔓),
      Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    simp
  map_mul' := by
    intro σ τ
    apply Units.ext
    rw [Units.val_mul, val_tameCharFun, val_tameCharFun, val_tameCharFun,
      ← map_mul, Ideal.Quotient.eq]
    refine tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen _) ?_
    set tσ := tameCoeff 𝔓 hϖP hgen σ.2
    set tτ := tameCoeff 𝔓 hϖP hgen τ.2
    have hτ := tameCoeff_spec 𝔓 hϖP hgen τ.2
    have hσ' := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have e1 : ((σ * τ : 𝔓.inertia G) : G) • ϖ
        = (σ : G) • ((τ : G) • ϖ) := mul_smul _ _ _
    have e2 : (σ : G) • ((τ : G) • ϖ)
        = (σ : G) • ((τ : G) • ϖ - ϖ * tτ) + ((σ : G) • ϖ) * ((σ : G) • tτ) := by
      rw [← smul_mul', ← smul_add]; congr 1; ring
    have hA : (σ : G) • ((τ : G) • ϖ - ϖ * tτ) ∈ 𝔓 ^ 2 :=
      smul_mem_sq_of_mem_inertia 𝔓 σ.2 hτ
    have e3 : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = ((σ : G) • ϖ - ϖ * tσ) * ((σ : G) • tτ)
          + ϖ * (tσ * ((σ : G) • tτ - tτ)) := by ring
    have hB : ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ) ∈ 𝔓 ^ 2 := by
      rw [e3]
      refine (𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ hσ') ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖP (Ideal.mul_mem_left _ _ (σ.2 tτ))
    rw [e1, e2]
    have hdecomp : (σ : G) • ((τ : G) • ϖ - ϖ * tτ)
        + ((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)
        = (σ : G) • ((τ : G) • ϖ - ϖ * tτ)
          + (((σ : G) • ϖ) * ((σ : G) • tτ) - ϖ * (tσ * tτ)) := by ring
    rw [hdecomp]
    exact (𝔓 ^ 2).add_mem hA hB

variable (hϖP : ϖ ∈ 𝔓) (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
  (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓)

private theorem tameChar_apply (σ : 𝔓.inertia G) :
    ((tameChar 𝔓 hϖP hgen hreg σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓)
      = Ideal.Quotient.mk 𝔓 (tameCoeff 𝔓 hϖP hgen σ.2) := rfl

private theorem tameChar_eq_one_iff (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1 ↔ (σ : G) • ϖ - ϖ ∈ 𝔓 ^ 2 := by
  rw [← Units.val_eq_one, tameChar_apply, ← map_one (Ideal.Quotient.mk 𝔓),
    Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have hdecomp : (σ : G) • ϖ - ϖ
        = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2)
          + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - 1) := by ring
    rw [hdecomp]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2)
      (by rwa [mul_one])

private theorem tameChar_eq_one_iff_forall [Finite (B ⧸ 𝔓)]
    (σ : 𝔓.inertia G) :
    tameChar 𝔓 hϖP hgen hreg σ = 1
      ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2 := by
  rw [tameChar_eq_one_iff]
  exact ⟨fun h x => smul_sub_mem_sq_of_mem_inertia 𝔓 hϖP hgen σ.2 h x,
    fun h => h ϖ⟩

private theorem isCyclic_range_tameChar [Finite (B ⧸ 𝔓)] :
    IsCyclic (tameChar (G := G) 𝔓 hϖP hgen hreg).range := by
  let : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (B ⧸ 𝔓)).comp (tameChar (G := G) 𝔓 hϖP hgen hreg).range.subtype)
    (Units.val_injective.comp Subtype.val_injective)

/-- **Tame character of the inertia group at a maximal ideal.** Let a group $G$ act on a
commutative ring $B$ by ring automorphisms, let $\mathfrak{P}$ be a maximal ideal of $B$ whose
residue field $B/\mathfrak{P}$ is finite, and let $\varpi \in \mathfrak{P}$ satisfy two
conditions: every $x \in \mathfrak{P}$ satisfies $x \equiv \varpi y \pmod{\mathfrak{P}^2}$ for
some $y \in B$, and $c \varpi \in \mathfrak{P}^2$ implies $c \in \mathfrak{P}$ for every
$c \in B$. Let $I$ be the inertia group of $\mathfrak{P}$, the subgroup of the $\sigma \in G$
with $\sigma(x) - x \in \mathfrak{P}$ for every $x \in B$. Then there is a group homomorphism
$\theta \colon I \to (B/\mathfrak{P})^\times$ with the following properties.
- Coefficient characterization: for $\sigma \in I$ and $t \in B$, $\theta(\sigma)$ is the
  residue class of $t$ if and only if $\sigma(\varpi) \equiv \varpi t \pmod{\mathfrak{P}^2}$.
- Kernel: $\theta(\sigma) = 1$ if and only if $\sigma(x) \equiv x \pmod{\mathfrak{P}^2}$ for
  every $x \in B$, not only for $x = \varpi$.
- The image of $\theta$ is cyclic. -/
public theorem exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer
    (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B),
        ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
          (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧
        IsCyclic θ.range := by
  refine ⟨tameChar (G := G) 𝔓 hϖP hgen hreg, fun σ t => ?_,
    fun σ => tameChar_eq_one_iff_forall 𝔓 hϖP hgen hreg σ,
    isCyclic_range_tameChar 𝔓 hϖP hgen hreg⟩
  rw [tameChar_apply, Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have hdecomp : (σ : G) • ϖ - ϖ * t
        = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2)
          + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - t) := by ring
    rw [hdecomp]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) h

end TameInertiaCharacter

end Ideal

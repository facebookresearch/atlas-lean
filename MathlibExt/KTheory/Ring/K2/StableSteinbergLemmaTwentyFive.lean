/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleWeylBorelTransport
public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleTwoCell
public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleRootTransport

/-! # Pointwise core of Steinberg Lemma 25

For `[Field F]`, `hm : m + 1 < n`, `s = weyl m (m + 1) 1`, a finite-Weyl
element `w`, and `b ∈ finiteBorelSubgroup n`, prove the pointwise core of
Steinberg Lemma 25 (Steinberg, *Lectures on Chevalley Groups*, Yale 1967,
pp. 39--40, Lemmas 24--26): under positivity of the two adjacent permutation
images, `w * b * s = b₁ * (w * s) * b₂` for Borel `b₁, b₂`; without a sign
hypothesis, the alternative of such a `B * (w * s) * B` factorization or a
`B * w * B` factorization. This follows the fully checked plan of read-only
scouts `46032`, `67856`, and `55531`.

Positive proof: split `b = u * h` by `finiteBorel_exists_upper_mul_torus`,
split `u = xpart * rest` by `upperUnipotent_exists_simple_mul_complement`,
place `w * xpart * w⁻¹` in the Borel via `finiteWeyl_simpleRoot_mem_borel`
(positivity), transport `rest` across `s` by the public inverse-complement
lemma `weyl_inv_conj_complement_mem_upper`, transport `h` across `s` via
`weyl_conj_finiteTorus_mem` at unit `-1` (so `s⁻¹ * h * s` is a torus
conjugate by `weyl(-1)`), then close the pure group reassociation.

General proof: split on positivity. In the negative branch put
`w₀ = w * s⁻¹` as a bounded subgroup element; its adjacent images are the
swapped images of `w` (via `finiteWeylPerm.map_mul/map_inv`,
`finiteWeylPerm_weyl`, and swap identities), hence positive, and
`w = w₀ * s`. Classify `s * b * s` only via public `simpleTwoCellSubgroup`
membership and `mem_simpleTwoCellSubgroup`. In its Borel branch identify the
`w₀` cell with the `w * s` cell using public `simpleWeyl_sq_mem_borel`; in
its `B * s * B` branch apply the positive theorem to `w₀` and identify
`w₀ * s = w`. Branch order and all Borel witnesses stay explicit.

Hypotheses are always `hm : m + 1 < n`. Conjugation orientation is always
conjugator on the left. Characteristic-two/`F₂` safe: only group identities,
`weyl_neg_eq_inv`, torus membership, and permutation swaps are used; no
`(-1 ≠ 1)` or `(2 ≠ 0)` assumption occurs.

Nonclaims: no full Bruhat existence, no quotient injectivity, no target
kernel containment, no universal central extension, no Matsumoto theorem, no
reflected-Weyl-cell cancellation, and no commutation of an arbitrary Borel
factor through a Weyl element are used or claimed.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Positive pointwise Lemma-25 factorization: for `hm : m + 1 < n`,
a finite-Weyl element `w` with positivity of its induced permutation on the
adjacent indices `m, m + 1`, and `b ∈ finiteBorelSubgroup n`, with
`s = weyl m (m + 1) 1`, exhibit Borel `b₁, b₂` with
`w * b * s = b₁ * (w * s) * b₂`.
Purpose: positive core of Steinberg Lemma 25, consumer API for the weak
Bruhat route. Hypotheses: `hm`, positivity of the two adjacent images under
`finiteWeylPerm n w`. Orientation: `w * b * s` on the left,
`b₁ * (w * s) * b₂` on the right. Characteristic-two safe.
Nonclaim: no sign-free alternative, Bruhat, quotient, or Matsumoto claim. -/
public theorem lemmaTwentyFive_positive {n m : ℕ} (hm : m + 1 < n)
    (w : ↥(finiteWeylSubgroup (R := F) n))
    (hpos : ((finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩).val <
      ((finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩).val)
    {b : StableSteinberg F} (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    ∃ b₁ ∈ finiteBorelSubgroup (F := F) n,
      ∃ b₂ ∈ finiteBorelSubgroup (F := F) n,
        (↑w : StableSteinberg F) * b *
          weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) =
          b₁ * ((↑w : StableSteinberg F) *
            weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)) * b₂ := by
  set s : StableSteinberg F :=
    weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hUle : upperUnipotentSubgroup (R := F) n ≤ finiteBorelSubgroup (F := F) n :=
    upperUnipotentSubgroup_le_finiteBorelSubgroup n
  have hTle : finiteTorusSubgroup (R := F) n ≤ finiteBorelSubgroup (F := F) n :=
    finiteTorusSubgroup_le_finiteBorelSubgroup n
  obtain ⟨u, hu, h, hh, rfl⟩ := finiteBorel_exists_upper_mul_torus hb
  obtain ⟨xpart, hxpart, rest, hrest, rfl⟩ :=
    upperUnipotent_exists_simple_mul_complement hm hu
  have hBx : (↑w : StableSteinberg F) * xpart * (↑w)⁻¹ ∈
      finiteBorelSubgroup (F := F) n :=
    finiteWeyl_simpleRoot_mem_borel hm w hpos hxpart
  have hrestU : s⁻¹ * rest * s ∈ upperUnipotentSubgroup (R := F) n :=
    weyl_inv_conj_complement_mem_upper hm hrest
  have hw_inv : weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (-1 : Fˣ) =
      s⁻¹ :=
    weyl_neg_eq_inv _ _ _ _
  have htorus : weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (-1 : Fˣ) * h *
      (weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (-1 : Fˣ))⁻¹ ∈
      finiteTorusSubgroup (R := F) n :=
    weyl_conj_finiteTorus_mem hm_n hm _ _ hh
  have hinv : (weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (-1 : Fˣ))⁻¹ =
      s := by
    rw [hw_inv, inv_inv]
  have hhT : s⁻¹ * h * s ∈ finiteTorusSubgroup (R := F) n := by
    rw [← hw_inv, ← hinv]
    exact htorus
  have hrestB : s⁻¹ * rest * s ∈ finiteBorelSubgroup (F := F) n := hUle hrestU
  have hhB : s⁻¹ * h * s ∈ finiteBorelSubgroup (F := F) n := hTle hhT
  have hB2 : (s⁻¹ * rest * s) * (s⁻¹ * h * s) ∈ finiteBorelSubgroup (F := F) n :=
    Subgroup.mul_mem _ hrestB hhB
  have hfinal : (↑w : StableSteinberg F) * ((xpart * rest) * h) * s =
      ((↑w : StableSteinberg F) * xpart * (↑w)⁻¹) * ((↑w : StableSteinberg F) * s) *
        ((s⁻¹ * rest * s) * (s⁻¹ * h * s)) := by
    group
  exact ⟨_, hBx, _, hB2, hfinal⟩

/-- Sign-free pointwise Lemma-25 alternative: for `hm : m + 1 < n`, a
finite-Weyl element `w`, and `b ∈ finiteBorelSubgroup n`, with
`s = weyl m (m + 1) 1`, either `w * b * s = b₁ * (w * s) * b₂` for Borel
`b₁, b₂`, or `w * b * s = c₁ * w * c₂` for Borel `c₁, c₂`.
Purpose: full pointwise core of Steinberg Lemma 25 without a sign
hypothesis, consumer API for the weak Bruhat route. The negative branch
writes `w = w₀ * s` with positive `w₀ = w * s⁻¹` and classifies `s * b * s`
in the public two-cell subgroup. Characteristic-two safe.
Nonclaim: no Bruhat existence, quotient injectivity, target kernel
containment, universal central extension, or Matsumoto claim. -/
public theorem lemmaTwentyFive_alternative {n m : ℕ} (hm : m + 1 < n)
    (w : ↥(finiteWeylSubgroup (R := F) n))
    {b : StableSteinberg F} (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    (∃ b₁ ∈ finiteBorelSubgroup (F := F) n, ∃ b₂ ∈ finiteBorelSubgroup (F := F) n,
      (↑w : StableSteinberg F) * b *
        weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) =
        b₁ * ((↑w : StableSteinberg F) *
          weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)) * b₂) ∨
    (∃ c₁ ∈ finiteBorelSubgroup (F := F) n, ∃ c₂ ∈ finiteBorelSubgroup (F := F) n,
      (↑w : StableSteinberg F) * b *
        weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) =
        c₁ * (↑w : StableSteinberg F) * c₂) := by
  by_cases hpos : ((finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩).val <
    ((finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩).val
  · exact Or.inl (lemmaTwentyFive_positive hm w hpos hb)
  · set s : StableSteinberg F :=
      weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)
    have hm_n : m < n := Nat.lt_of_succ_lt hm
    set sW : ↥(finiteWeylSubgroup (R := F) n) :=
      ⟨weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ),
        weyl_mem_finiteWeylSubgroup (R := F) hm_n hm
          (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)⟩ with hsW_def
    set w₀ : ↥(finiteWeylSubgroup (R := F) n) := w * sW⁻¹ with hw₀_def
    have hsW_coe : (sW : StableSteinberg F) = s := rfl
    have hw0_coe : (w₀ : StableSteinberg F) =
        (↑w : StableSteinberg F) * (sW : StableSteinberg F)⁻¹ := rfl
    have hw : (↑w : StableSteinberg F) = (w₀ : StableSteinberg F) * s := by
      rw [hw0_coe, hsW_coe]
      group
    have hswap : finiteWeylPerm (F := F) n sW =
        Equiv.swap (⟨m, hm_n⟩ : Fin n) (⟨m + 1, hm⟩ : Fin n) := by
      rw [hsW_def]
      exact finiteWeylPerm_weyl hm_n hm (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)
    have hperm0 : finiteWeylPerm (F := F) n w₀ =
        finiteWeylPerm (F := F) n w * (finiteWeylPerm (F := F) n sW)⁻¹ := by
      simp only [hw₀_def, map_mul, map_inv]
    have himg_m : (finiteWeylPerm (F := F) n w₀) ⟨m, Nat.lt_of_succ_lt hm⟩ =
        (finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩ := by
      rw [hperm0, Equiv.Perm.mul_apply]
      congr 1
      change ((finiteWeylPerm (F := F) n sW).symm) ⟨m, Nat.lt_of_succ_lt hm⟩ = ⟨m + 1, hm⟩
      rw [hswap, Equiv.symm_swap]
      exact Equiv.swap_apply_left _ _
    have himg_m1 : (finiteWeylPerm (F := F) n w₀) ⟨m + 1, hm⟩ =
        (finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩ := by
      rw [hperm0, Equiv.Perm.mul_apply]
      congr 1
      change ((finiteWeylPerm (F := F) n sW).symm) ⟨m + 1, hm⟩ = ⟨m, Nat.lt_of_succ_lt hm⟩
      rw [hswap, Equiv.symm_swap]
      exact Equiv.swap_apply_right _ _
    have hne : ((finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩).val ≠
        ((finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩).val := by
      intro hcon
      have hfin : (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin n) ≠ ⟨m + 1, hm⟩ := by
        intro h
        have hval := congrArg Fin.val h
        exact (Nat.ne_of_lt (Nat.lt_succ_self m)) hval
      apply hfin
      apply (finiteWeylPerm (F := F) n w).injective
      exact Fin.val_injective hcon
    have hneg : ((finiteWeylPerm (F := F) n w) ⟨m + 1, hm⟩).val <
        ((finiteWeylPerm (F := F) n w) ⟨m, Nat.lt_of_succ_lt hm⟩).val :=
      lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hne)
    have hpos0 : ((finiteWeylPerm (F := F) n w₀) ⟨m, Nat.lt_of_succ_lt hm⟩).val <
        ((finiteWeylPerm (F := F) n w₀) ⟨m + 1, hm⟩).val := by
      rw [himg_m, himg_m1]
      exact hneg
    have hs_mem : s ∈ simpleTwoCellSubgroup (F := F) n m hm :=
      weyl_mem_simpleTwoCell hm
    have hb_mem : b ∈ simpleTwoCellSubgroup (F := F) n m hm :=
      finiteBorelSubgroup_le_simpleTwoCell hm hb
    have hmem : s * b * s ∈ simpleTwoCellSubgroup (F := F) n m hm :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs_mem hb_mem) hs_mem
    rw [mem_simpleTwoCellSubgroup hm] at hmem
    rcases hmem with hBmem | ⟨b₁, hb1, b₂, hb2, heq⟩
    · have hsq : s * s ∈ finiteBorelSubgroup (F := F) n :=
        simpleWeyl_sq_mem_borel hm
      refine Or.inl ⟨1, Subgroup.one_mem _, _, Subgroup.mul_mem _
        (Subgroup.inv_mem _ hsq) hBmem, ?_⟩
      rw [hw]
      group
    · have heq' : s * b * s = b₁ * s * b₂ := heq
      obtain ⟨c₁, hc1, c₂, hc2, hceq⟩ := lemmaTwentyFive_positive hm w₀ hpos0 hb1
      have hceq' : (w₀ : StableSteinberg F) * b₁ * s =
          c₁ * ((w₀ : StableSteinberg F) * s) * c₂ := hceq
      have hw0s : (w₀ : StableSteinberg F) * s = (↑w : StableSteinberg F) := hw.symm
      have e1 : ((w₀ : StableSteinberg F) * s) * b * s =
          ((w₀ : StableSteinberg F) * b₁ * s) * b₂ := by
        rw [show ((w₀ : StableSteinberg F) * s) * b * s =
            (w₀ : StableSteinberg F) * (s * b * s) from by group, heq']
        group
      rw [← hw, hceq', hw0s] at e1
      refine Or.inr ⟨c₁, hc1, _, Subgroup.mul_mem _ hc2 hb2, ?_⟩
      rw [e1]
      group

end StableSteinberg

end AlgebraicKTheory

end

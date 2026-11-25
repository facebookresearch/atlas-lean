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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergSimpleRootComplement

/-! # Simple-Weyl inverse complement and square-in-Borel

For `[Field F]` and `hm : m + 1 < n`, with `s = weyl m (m + 1) 1`,
prove the two small prerequisites for the forthcoming Steinberg-Lemma-25
packet: the inverse conjugate `s⁻¹ * c * s` of a simple-root-complement
element stays upper-unipotent, and `s * s` lies in the finite Borel.

Proof route (per read-only scout `19746`): reuse the accepted forward
transport `weyl_conj_complement_mem_upper` for `s * c * s⁻¹`; write
`t = torus m (m + 1) (-1) = s⁻¹ * s⁻¹` via `torus` and `weyl_neg_eq_inv`,
so `t` lies in the finite torus and normalizes the upper subgroup by
`finiteTorusSubgroup_le_normalizer_upperUnipotent`; then
`t * (s * c * s⁻¹) * t⁻¹ = s⁻¹ * c * s` by pure group identities.
This is the strictly shorter rearrangement (direct `t * y * t⁻¹`
orientation, no extra inverse-membership step). Likewise
`s * s = (torus m (m + 1) (-1))⁻¹` lies in the finite torus, hence in the
finite Borel. Characteristic-two/F2 safe: only group identities,
`weyl_neg_eq_inv`, and torus membership are used; no `(-1 ≠ 1)` or
`(2 ≠ 0)` assumption occurs.

Orientation is always conjugator on the left (`t * y * t⁻¹`).

Nonclaims: no full Steinberg Lemma 25, no `B w B s B` containment, no
double-coset assembly, no quotient injectivity, no Matsumoto theorem, no
target kernel containment, no universal central extension, no later Bruhat
result, and no arbitrary Borel-through-Weyl normalization are used or
claimed.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Inverse simple-Weyl conjugate of the complement stays upper: for
`hm : m + 1 < n`, `c ∈ simpleRootComplementSubgroup n m`, and
`s = weyl m (m + 1) 1`, `s⁻¹ * c * s ∈ upperUnipotentSubgroup n`.
Purpose: structural inverse-transport prerequisite for Lemma 25, avoiding a
duplicate four-case root proof. Reuses the forward
`weyl_conj_complement_mem_upper` plus one torus normalization.
Orientation: `s⁻¹ * c * s`. Characteristic-two safe.
Nonclaim: no Lemma 25 containment, Bruhat, quotient, or Matsumoto claim. -/
public theorem weyl_inv_conj_complement_mem_upper {n m : ℕ} (hm : m + 1 < n)
    {c : StableSteinberg F} (hc : c ∈ simpleRootComplementSubgroup (F := F) n m) :
    (weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ))⁻¹ * c *
      weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) ∈
      upperUnipotentSubgroup (R := F) n := by
  have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hy : weyl (R := F) m (m + 1) hmm (1 : Fˣ) * c *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ ∈
      upperUnipotentSubgroup (R := F) n :=
    weyl_conj_complement_mem_upper hm hc
  have hw_inv : weyl (R := F) m (m + 1) hmm (-1 : Fˣ) =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ :=
    weyl_neg_eq_inv _ _ _ _
  have hTmem : torus (R := F) m (m + 1) hmm (-1 : Fˣ) ∈
      finiteTorusSubgroup (R := F) n :=
    torus_mem_finiteTorusSubgroup hm_n hm hmm _
  have hTnorm : torus (R := F) m (m + 1) hmm (-1 : Fˣ) ∈
      Subgroup.normalizer (upperUnipotentSubgroup (R := F) n) :=
    finiteTorusSubgroup_le_normalizer_upperUnipotent n hTmem
  have hconj : torus (R := F) m (m + 1) hmm (-1 : Fˣ) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * c *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
      (torus (R := F) m (m + 1) hmm (-1 : Fˣ))⁻¹ ∈
      upperUnipotentSubgroup (R := F) n :=
    (Subgroup.mem_normalizer_iff.mp hTnorm _).mp hy
  have hTeq : torus (R := F) m (m + 1) hmm (-1 : Fˣ) =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ := by
    change weyl (R := F) m (m + 1) hmm (-1 : Fˣ) *
      weyl (R := F) m (m + 1) hmm (-1 : Fˣ) = _
    rw [hw_inv]
  have heq : torus (R := F) m (m + 1) hmm (-1 : Fˣ) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * c *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
      (torus (R := F) m (m + 1) hmm (-1 : Fˣ))⁻¹ =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ * c *
        weyl (R := F) m (m + 1) hmm (1 : Fˣ) := by
    rw [hTeq]
    group
  rw [heq] at hconj
  exact hconj

/-- Square of the simple Weyl element lies in the finite Borel: for
`hm : m + 1 < n` and `s = weyl m (m + 1) 1`, `s * s ∈ finiteBorelSubgroup n`.
Purpose: tiny public `s² ∈ B` wrapper for Lemma-25 torus normalization.
Since `torus(-1) = s⁻¹ * s⁻¹`, `s * s = torus(-1)⁻¹` lies in the finite
torus, hence in the Borel. Characteristic-two safe.
Orientation: none beyond the product order `s * s`.
Nonclaim: no Lemma 25, Bruhat, quotient, or Matsumoto claim. -/
public theorem simpleWeyl_sq_mem_borel {n m : ℕ} (hm : m + 1 < n) :
    weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) *
      weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) ∈
      finiteBorelSubgroup (F := F) n := by
  have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hTle : finiteTorusSubgroup (R := F) n ≤
      finiteBorelSubgroup (F := F) n :=
    finiteTorusSubgroup_le_finiteBorelSubgroup n
  have hw1 : weyl (R := F) m (m + 1) hmm (-1 : Fˣ) =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ :=
    weyl_neg_eq_inv _ _ _ _
  have hTmem : torus (R := F) m (m + 1) hmm (-1 : Fˣ) ∈
      finiteTorusSubgroup (R := F) n :=
    torus_mem_finiteTorusSubgroup hm_n hm hmm _
  have hTeq : torus (R := F) m (m + 1) hmm (-1 : Fˣ) =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ := by
    change weyl (R := F) m (m + 1) hmm (-1 : Fˣ) *
      weyl (R := F) m (m + 1) hmm (-1 : Fˣ) = _
    rw [hw1]
  have hsq : weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
      weyl (R := F) m (m + 1) hmm (1 : Fˣ) =
      (torus (R := F) m (m + 1) hmm (-1 : Fˣ))⁻¹ := by
    rw [hTeq, mul_inv_rev, inv_inv]
  rw [hsq]
  exact hTle (Subgroup.inv_mem _ hTmem)

end StableSteinberg

end AlgebraicKTheory

end

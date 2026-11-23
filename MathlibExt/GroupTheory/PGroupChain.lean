/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Composition series of finite `p`-groups

Source: `v1/Atlas/AlgebraNotes/targets.yaml` (Lecture 34, Subsection: Main Theorem
of Algebra, Proposition: every `p`-group is solvable, with a chain of subgroups
`G = G₀ ⊃ G₁ ⊃ ⋯ ⊃ Gₙ = {1}` such that `Gᵢ₊₁` is normal in `Gᵢ` and
`Gᵢ / Gᵢ₊₁ ≅ ℤ / p`). This target has no Lean code in `v1` (it appears only in
`targets.yaml`); the formalization here is new.

The main result is `IsPGroup.exists_chain_zmod_p_quotients`: a finite `p`-group
of order `p ^ n` has such a chain, of length `n + 1`. The quotient condition is
stated in the equivalent form given by the first isomorphism theorem: there is
a surjective homomorphism `Gᵢ →* Multiplicative (ZMod p)` whose kernel is
exactly `Gᵢ₊₁`, viewed as a subgroup of `Gᵢ`. (Stating the quotient
`Gᵢ ⧸ Gᵢ₊₁ ≃* Multiplicative (ZMod p)` directly would require the normality of
`Gᵢ₊₁` in `Gᵢ` as an instance in the statement itself; the homomorphism form
avoids that.)

The solvability claim (`IsPGroup.isSolvable`) is the one-line corollary of
Mathlib's `IsPGroup.isNilpotent` and `Group.IsNilpotent.to_isSolvable`; the
chain is the new content.
-/

@[expose] public section

namespace IsPGroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- One step in the construction of a composition series of a finite `p`-group:
unless `H = ⊥`, we choose a subgroup of index `p` in `H`, normal in `H`. This
uses Mathlib's existence of normal subgroups of every divisor index in a finite
nilpotent group. -/
private theorem exists_step (hG : IsPGroup p G) (H : Subgroup G) :
    ∃ H' : Subgroup G,
      (H = ⊥ → H' = ⊥) ∧
        (H ≠ ⊥ → H' ≤ H ∧ (H'.subgroupOf H).Normal ∧
          (H'.subgroupOf H).index = p ∧ Nat.card ↥H' = Nat.card ↥H / p) := by
  by_cases hH : H = ⊥
  · exact ⟨⊥, fun _ => rfl, fun h => (h hH).elim⟩
  · have : Group.IsNilpotent G := hG.isNilpotent
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hG.to_subgroup H)
    have hmpos : 0 < m := by
      rcases m with _ | m
      · exfalso
        apply hH
        apply Subgroup.eq_bot_of_card_eq
        simp [hm]
      · exact Nat.succ_pos _
    have hdvd : p ∣ Nat.card ↥H := by
      rw [hm]
      exact dvd_pow_self p (by omega : m ≠ 0)
    obtain ⟨K, hKindex, hKnormal⟩ :=
      Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := ↥H) (k := p) hdvd
    have hmul := Subgroup.index_mul_card K
    rw [hKindex] at hmul
    have hcardK : Nat.card ↥K = Nat.card ↥H / p := by
      rw [← hmul, Nat.mul_div_cancel_left]
      exact (Fact.out : p.Prime).pos
    refine ⟨K.map H.subtype, fun h => (hH h).elim, fun _ => ?_⟩
    have hker : (H.subtype).ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot]
      exact Subtype.coe_injective
    have hsub : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self (by rw [hker]; exact bot_le)
    refine ⟨Subgroup.map_subtype_le K, ?_, ?_, ?_⟩
    · rw [hsub]; exact hKnormal
    · rw [hsub]; exact hKindex
    · calc Nat.card ↥(K.map H.subtype)
          = Nat.card ↥K := Nat.card_congr
            (Subgroup.equivMapOfInjective K H.subtype Subtype.coe_injective).symm.toEquiv
        _ = Nat.card ↥H / p := hcardK

/-- The descending chain of subgroups of a finite `p`-group obtained by repeatedly
taking a subgroup of index `p`. -/
private noncomputable def pChain (hG : IsPGroup p G) : ℕ → Subgroup G
  | 0 => ⊤
  | (i + 1) => Classical.choose (exists_step hG (pChain hG i))

private theorem pChain_zero (hG : IsPGroup p G) : pChain hG 0 = ⊤ := rfl

private theorem pChain_succ (hG : IsPGroup p G) (i : ℕ) :
    pChain hG (i + 1) = Classical.choose (exists_step hG (pChain hG i)) := rfl

private theorem pChain_spec (hG : IsPGroup p G) (i : ℕ) :
    (pChain hG i = ⊥ → pChain hG (i + 1) = ⊥) ∧
      (pChain hG i ≠ ⊥ → pChain hG (i + 1) ≤ pChain hG i ∧
        ((pChain hG (i + 1)).subgroupOf (pChain hG i)).Normal ∧
        ((pChain hG (i + 1)).subgroupOf (pChain hG i)).index = p ∧
        Nat.card ↥(pChain hG (i + 1)) = Nat.card ↥(pChain hG i) / p) := by
  rw [pChain_succ]
  exact Classical.choose_spec (exists_step hG (pChain hG i))

private theorem pChain_card (hG : IsPGroup p G) {n : ℕ} (hn : Nat.card G = p ^ n)
    (i : ℕ) (hi : i ≤ n) : Nat.card ↥(pChain hG i) = p ^ (n - i) := by
  induction i with
  | zero =>
    rw [pChain_zero]
    have htop : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [htop, hn, Nat.sub_zero]
  | succ i ih =>
    have hi' : i ≤ n := by omega
    have hlt : i < n := by omega
    have hne : pChain hG i ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥(pChain hG i) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
      have hcard := ih hi'
      rw [h1] at hcard
      have hgt : 1 < p ^ (n - i) :=
        one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega : n - i ≠ 0)
      omega
    obtain ⟨_, _, _, hcard⟩ := (pChain_spec hG i).2 hne
    have hih := ih hi'
    rw [hcard, hih]
    have hsub : n - i = (n - (i + 1)) + 1 := by omega
    rw [hsub, pow_succ', Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]

/-- **Composition series of finite p-groups.** Let $p$ be a prime and let $G$ be a finite
$p$-group of order $p^n$. Then there are subgroups
$G = H_0 \supseteq H_1 \supseteq \cdots \supseteq H_n = \{1\}$ such that for each $i < n$,
$H_{i+1}$ is a normal subgroup of $H_i$ and there is a surjective homomorphism
$H_i \to \mathbb{Z}/p\mathbb{Z}$ with kernel $H_{i+1}$. By the first isomorphism theorem,
$H_i / H_{i+1} \cong \mathbb{Z}/p\mathbb{Z}$ for each $i < n$. -/
theorem exists_chain_zmod_p_quotients (hG : IsPGroup p G) {n : ℕ}
    (hn : Nat.card G = p ^ n) :
    ∃ H : Fin (n + 1) → Subgroup G,
      H 0 = ⊤ ∧
        H (Fin.last n) = ⊥ ∧
        ∀ i : Fin n,
          H i.succ ≤ H i.castSucc ∧
            ((H i.succ).subgroupOf (H i.castSucc)).Normal ∧
            ∃ φ : ↥(H i.castSucc) →* Multiplicative (ZMod p),
              Function.Surjective φ ∧ φ.ker = (H i.succ).subgroupOf (H i.castSucc) := by
  refine ⟨fun i => pChain hG i.val, ?_, ?_, ?_⟩
  · rfl
  · show pChain hG (Fin.last n).val = ⊥
    rw [Fin.val_last]
    apply Subgroup.eq_bot_of_card_eq
    have hcard := pChain_card hG hn n le_rfl
    rw [Nat.sub_self, pow_zero] at hcard
    exact hcard
  · intro i
    have hlt : i.val < n := i.isLt
    have hne : pChain hG i.val ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥(pChain hG i.val) = 1 := (Subgroup.eq_bot_iff_card _).mp hbot
      have hcard := pChain_card hG hn i.val (by omega)
      rw [h1] at hcard
      have hgt : 1 < p ^ (n - i.val) :=
        one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega : n - i.val ≠ 0)
      omega
    obtain ⟨hle, hnorm, hindex, _⟩ := (pChain_spec hG i.val).2 hne
    refine ⟨?_, ?_, ?_⟩
    · show pChain hG (i.val + 1) ≤ pChain hG i.val
      exact hle
    · show ((pChain hG (i.val + 1)).subgroupOf (pChain hG i.val)).Normal
      exact hnorm
    · have := hnorm
      show ∃ φ : ↥(pChain hG i.val) →* Multiplicative (ZMod p),
        Function.Surjective φ ∧
          φ.ker = (pChain hG (i.val + 1)).subgroupOf (pChain hG i.val)
      have hqcard : Nat.card (↥(pChain hG i.val) ⧸
          ((pChain hG (i.val + 1)).subgroupOf (pChain hG i.val))) = p := by
        rw [← Subgroup.index_eq_card, hindex]
      have hcyc : IsCyclic (↥(pChain hG i.val) ⧸
          ((pChain hG (i.val + 1)).subgroupOf (pChain hG i.val))) :=
        isCyclic_of_prime_card hqcard
      have e : (↥(pChain hG i.val) ⧸
          ((pChain hG (i.val + 1)).subgroupOf (pChain hG i.val))) ≃*
            Multiplicative (ZMod p) := by
        have h := (zmodCyclicMulEquiv hcyc).symm
        rw [hqcard] at h
        exact h
      refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
      · rw [MonoidHom.coe_comp]
        exact e.surjective.comp (QuotientGroup.mk'_surjective _)
      · rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' _)
          e.toMonoidHom e.injective, QuotientGroup.ker_mk']

/-- **Finite p-groups are solvable.** For every prime $p$, every finite $p$-group is
solvable. -/
theorem isSolvable (hG : IsPGroup p G) : Group.IsSolvable G := by
  have : Group.IsNilpotent G := hG.isNilpotent
  infer_instance

end IsPGroup

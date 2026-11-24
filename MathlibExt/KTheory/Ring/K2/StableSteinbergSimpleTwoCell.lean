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
public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations
public import MathlibExt.KTheory.Ring.K2.StableSteinbergEqualIndexZero
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylTorus
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteTorusNormalizer

/-! # Simple two-cell subgroup (Steinberg Lemma 24)

For a field `F`, rank `n`, and `m + 1 < n`, the set `B ∪ B w B` with
`w = weyl m (m + 1) _ 1` and `B = finiteBorelSubgroup n` is a subgroup of
`StableSteinberg F`, packaged as `simpleTwoCellSubgroup` with an exact
membership iff.

Proof route (no Bruhat existence, quotients, or circularity): the negative
simple root lies in `B w B` (`x_ji_neg_inv_mul_x_ij` plus
`weyl(u) = torus(u) * w`); `w * w ∈ B` via `torus(-1)`; every
simple-root-subgroup element is a single `x m (m+1) a`; conjugation by `w`
sends `B` into the two-cell set (simple factor via `weyl_conj_x_ij` at unit
`1`, complement via `weyl_conj_complement_mem_upper`, torus via
`weyl_conj_finiteTorus_mem`); two Weyl cells multiply via `B * (w * B * w) * B`;
inversion uses `w⁻¹ = (w * w)⁻¹ * w`. Conjugation orientation is always
`w * y * w⁻¹`.

Hypotheses are always `m + 1 < n`. Nonclaims: no Lemma 25 double-coset step,
Bruhat existence, quotient, target kernel inclusion, quotient faithfulness, or
Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {F : Type u} [Field F]

/-- Two-cell carrier `B ∪ B w B` for `w = weyl m (m+1) _ 1` and
`B = finiteBorelSubgroup n`. Purpose: carrier of Steinberg Lemma 24.
Public because the subgroup packaging below must reference it.
Nonclaim: not yet a subgroup; closure needs `m + 1 < n`. -/
public def twoCellSet (n m : ℕ) : Set (StableSteinberg F) :=
  { g | g ∈ finiteBorelSubgroup (F := F) n ∨
    ∃ b₁ ∈ finiteBorelSubgroup (F := F) n,
      ∃ b₂ ∈ finiteBorelSubgroup (F := F) n,
        g = b₁ * weyl (R := F) m (m + 1)
          (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * b₂ }

/-- Conjugation distributes over products: reassociation plus `w⁻¹ * w = 1`.
Orientation: `w * (x * y) * w⁻¹`. -/
private theorem conj_split (w x y : StableSteinberg F) :
    (w * x * w⁻¹) * (w * y * w⁻¹) = w * (x * y) * w⁻¹ := by
  have h : w⁻¹ * (w * (y * w⁻¹)) = y * w⁻¹ := by
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  calc (w * x * w⁻¹) * (w * y * w⁻¹)
      = w * (x * (w⁻¹ * (w * (y * w⁻¹)))) := by simp only [mul_assoc]
    _ = w * (x * (y * w⁻¹)) := by rw [h]
    _ = w * (x * y) * w⁻¹ := by simp only [mul_assoc]

/-- Conjugation distributes over inverses. Orientation: `w * x⁻¹ * w⁻¹`. -/
private theorem conj_inv (w x : StableSteinberg F) :
    w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by
  simp only [mul_inv_rev, mul_assoc, inv_inv]

/-- Left stability of the two-cell set under `B`. -/
private theorem twoCell_mul_leftBorel {n m : ℕ} {s b : StableSteinberg F}
    (hs : s ∈ twoCellSet n m) (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    b * s ∈ twoCellSet n m := by
  unfold twoCellSet at hs ⊢
  rcases hs with hbS | ⟨b₁, hb1, b₂, hb2, rfl⟩
  · exact Or.inl (Subgroup.mul_mem _ hb hbS)
  · refine Or.inr ⟨b * b₁, Subgroup.mul_mem _ hb hb1, b₂, hb2, ?_⟩
    simp only [mul_assoc]

/-- Right stability of the two-cell set under `B`. -/
private theorem twoCell_mul_rightBorel {n m : ℕ} {s b : StableSteinberg F}
    (hs : s ∈ twoCellSet n m) (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    s * b ∈ twoCellSet n m := by
  unfold twoCellSet at hs ⊢
  rcases hs with hbS | ⟨b₁, hb1, b₂, hb2, rfl⟩
  · exact Or.inl (Subgroup.mul_mem _ hbS hb)
  · refine Or.inr ⟨b₁, hb1, b₂ * b, Subgroup.mul_mem _ hb2 hb, ?_⟩
    simp only [mul_assoc]

/-- Negative simple root lies in the two-cell set. For `t = 0` this is `x_zero`;
for `t ≠ 0`, put `u = Units.mk0 (-(t⁻¹)) _` so `t = -(↑u⁻¹)`, then
`x_ji_neg_inv_mul_x_ij` gives `x_ji(t) = x_ij(-↑u) * weyl(u) * x_ij(↑u)⁻¹`
and `weyl(u) = torus(u) * w` puts all outer factors in `B`.
Characteristic-two and `F₂` safe. -/
private theorem negSimpleRoot_mem_twoCell {n m : ℕ} (hm : m + 1 < n) (t : F) :
    x (R := F) (m + 1) m (Nat.ne_of_lt (Nat.lt_succ_self m)).symm t ∈
      twoCellSet n m := by
  have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hUle : upperUnipotentSubgroup (R := F) n ≤
      finiteBorelSubgroup (F := F) n :=
    upperUnipotentSubgroup_le_finiteBorelSubgroup n
  have hTle : finiteTorusSubgroup (R := F) n ≤
      finiteBorelSubgroup (F := F) n :=
    finiteTorusSubgroup_le_finiteBorelSubgroup n
  by_cases ht : t = 0
  · subst ht
    have h1 : x (R := F) (m + 1) m hmm.symm (0 : F) = 1 := x_zero _ _ _
    rw [h1]
    exact Or.inl (Subgroup.one_mem _)
  · have htinv : -(t⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht)
    let u : Fˣ := Units.mk0 (-(t⁻¹)) htinv
    have hcoe : (↑u : F) = -(t⁻¹) := Units.val_mk0 htinv
    have hu_inv : ((u⁻¹ : Fˣ) : F) = -t := by
      rw [Units.val_inv_eq_inv_val, hcoe, inv_neg, inv_inv]
    have ht_eq : t = -(↑u⁻¹ : F) := by rw [hu_inv, neg_neg]
    have hbase := x_ji_neg_inv_mul_x_ij (R := F) m (m + 1) hmm u
    rw [← ht_eq] at hbase
    have hsol : x (R := F) (m + 1) m hmm.symm t =
        x (R := F) m (m + 1) hmm (-(↑u : F)) *
          weyl (R := F) m (m + 1) hmm u *
          (x (R := F) m (m + 1) hmm (↑u : F))⁻¹ := by
      rw [← hbase, mul_inv_cancel_right]
    have hw1 : weyl (R := F) m (m + 1) hmm (-1 : Fˣ) =
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ :=
      weyl_neg_eq_inv _ _ _ _
    have hwu : weyl (R := F) m (m + 1) hmm u =
        torus (R := F) m (m + 1) hmm u *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ) := by
      have hdecomp : torus (R := F) m (m + 1) hmm u *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ) =
          weyl (R := F) m (m + 1) hmm u := by
        change weyl (R := F) m (m + 1) hmm u *
          weyl (R := F) m (m + 1) hmm (-1 : Fˣ) *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ) = _
        rw [hw1, inv_mul_cancel_right]
      exact hdecomp.symm
    have hB1 : x (R := F) m (m + 1) hmm (-(↑u : F)) *
        torus (R := F) m (m + 1) hmm u ∈
        finiteBorelSubgroup (F := F) n :=
      Subgroup.mul_mem _
        (hUle (x_mem_upperUnipotentSubgroup hmm (Nat.lt_succ_self m) hm_n hm _))
        (hTle (torus_mem_finiteTorusSubgroup hm_n hm hmm _))
    have hB2 : (x (R := F) m (m + 1) hmm (↑u : F))⁻¹ ∈
        finiteBorelSubgroup (F := F) n :=
      Subgroup.inv_mem _
        (hUle (x_mem_upperUnipotentSubgroup hmm (Nat.lt_succ_self m) hm_n hm _))
    rw [hsol, hwu]
    refine Or.inr ⟨_, hB1, _, hB2, ?_⟩
    simp only [mul_assoc]

/-- `w * w ∈ B`: `torus(-1) = weyl(-1) * weyl(-1) = w⁻¹ * w⁻¹`, hence
`w * w = torus(-1)⁻¹` lies in the finite torus, hence in `B`. -/
private theorem weyl_sq_mem_borel {n m : ℕ} (hm : m + 1 < n) :
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

/-- Conjugation by `w` sends `B` into the two-cell set. Factor `b = u * h`,
then `u = xpart * rest`: the simple factor becomes a negative simple root
(`weyl_conj_x_ij` at unit `1`) in the two-cell set, the complement lands in
upper, and `h` lands in the finite torus; left/right `B`-stability reassembles.
Orientation: `w * b * w⁻¹`. -/
private theorem weyl_conj_borel_mem_twoCell {n m : ℕ} (hm : m + 1 < n)
    {b : StableSteinberg F} (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * b *
      (weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m))
        (1 : Fˣ))⁻¹ ∈
      twoCellSet n m := by
  have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  have hm_n : m < n := Nat.lt_of_succ_lt hm
  have hUle : upperUnipotentSubgroup (R := F) n ≤
      finiteBorelSubgroup (F := F) n :=
    upperUnipotentSubgroup_le_finiteBorelSubgroup n
  have hTle : finiteTorusSubgroup (R := F) n ≤
      finiteBorelSubgroup (F := F) n :=
    finiteTorusSubgroup_le_finiteBorelSubgroup n
  obtain ⟨u, hu, h, hh, rfl⟩ := finiteBorel_exists_upper_mul_torus hb
  obtain ⟨xpart, hxpart, rest, hrest, rfl⟩ :=
    upperUnipotent_exists_simple_mul_complement hm hu
  obtain ⟨a, rfl⟩ := simpleRootSubgroup_exists_eq_x m hxpart
  have hconj := weyl_conj_x_ij (R := F) m (m + 1) hmm (1 : Fˣ) a
  have hneg : weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
      x (R := F) m (m + 1) hmm a *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ ∈ twoCellSet n m := by
    rw [hconj]
    exact negSimpleRoot_mem_twoCell hm _
  have hrestB : weyl (R := F) m (m + 1) hmm (1 : Fˣ) * rest *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ ∈
      finiteBorelSubgroup (F := F) n :=
    hUle (weyl_conj_complement_mem_upper hm hrest)
  have hhB : weyl (R := F) m (m + 1) hmm (1 : Fˣ) * h *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ ∈
      finiteBorelSubgroup (F := F) n :=
    hTle (weyl_conj_finiteTorus_mem hm_n hm hmm (1 : Fˣ) hh)
  have hsplit : weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
      ((x (R := F) m (m + 1) hmm a * rest) * h) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
        x (R := F) m (m + 1) hmm a *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * rest *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * h *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) := by
    rw [conj_split, conj_split]
  rw [hsplit]
  exact twoCell_mul_rightBorel (twoCell_mul_rightBorel hneg hrestB) hhB

/-- Two-sided variant: `w * b * w ∈` the two-cell set, via `w * b * w⁻¹` and
`w * b * w = (w * b * w⁻¹) * (w * w)` with `w * w ∈ B`. -/
private theorem weyl_mul_borel_mul_weyl_mem_twoCell {n m : ℕ} (hm : m + 1 < n)
    {b : StableSteinberg F} (hb : b ∈ finiteBorelSubgroup (F := F) n) :
    weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * b *
      weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) ∈
      twoCellSet n m := by
  have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
  have hsq := weyl_sq_mem_borel (F := F) (n := n) (m := m) hm
  have hconj := weyl_conj_borel_mem_twoCell (F := F) (n := n) (m := m) hm hb
  have hconv : weyl (R := F) m (m + 1) hmm (1 : Fˣ) * b *
      weyl (R := F) m (m + 1) hmm (1 : Fˣ) =
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * b *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
      (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
        weyl (R := F) m (m + 1) hmm (1 : Fˣ)) := by
    have hcancel : (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ *
        (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ)) =
        weyl (R := F) m (m + 1) hmm (1 : Fˣ) := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    calc weyl (R := F) m (m + 1) hmm (1 : Fˣ) * b *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ)
        = (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * b) *
          ((weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ *
            (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
              weyl (R := F) m (m + 1) hmm (1 : Fˣ))) := by
          rw [hcancel]
      _ = (weyl (R := F) m (m + 1) hmm (1 : Fˣ) * b *
          (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹) *
          (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
            weyl (R := F) m (m + 1) hmm (1 : Fˣ)) := by
          exact (mul_assoc _ _ _).symm
  rw [hconv]
  exact twoCell_mul_rightBorel hconj hsq

/-- Multiplication closure of the two-cell set. `B` and mixed products are
direct; two Weyl cells reduce to `B * (w * B * w) * B` via the two-sided
conjugation helper. Uses only set-level helpers, not subgroup closure.
Public because the subgroup packaging below must reference it. -/
public theorem twoCell_mul {n m : ℕ} (hm : m + 1 < n)
    {x y : StableSteinberg F} (hx : x ∈ twoCellSet n m)
    (hy : y ∈ twoCellSet n m) : x * y ∈ twoCellSet n m := by
  unfold twoCellSet at hx hy ⊢
  rcases hx with hbX | ⟨a₁, ha1, a₂, ha2, rfl⟩
  · rcases hy with hbY | ⟨c₁, hc1, c₂, hc2, rfl⟩
    · exact Or.inl (Subgroup.mul_mem _ hbX hbY)
    · refine Or.inr ⟨x * c₁, Subgroup.mul_mem _ hbX hc1, c₂, hc2, ?_⟩
      simp only [mul_assoc]
  · rcases hy with hbY | ⟨c₁, hc1, c₂, hc2, rfl⟩
    · refine Or.inr ⟨a₁, ha1, a₂ * y, Subgroup.mul_mem _ ha2 hbY, ?_⟩
      simp only [mul_assoc]
    · have hmem := weyl_mul_borel_mul_weyl_mem_twoCell hm
        (Subgroup.mul_mem _ ha2 hc1)
      unfold twoCellSet at hmem
      have hmid : (a₁ * weyl (R := F) m (m + 1)
          (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * a₂) *
          (c₁ * weyl (R := F) m (m + 1)
            (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * c₂) =
          a₁ * (weyl (R := F) m (m + 1)
            (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * (a₂ * c₁) *
            weyl (R := F) m (m + 1)
              (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ)) * c₂ := by
        simp only [mul_assoc]
      rcases hmem with hbM | ⟨d₁, hd1, d₂, hd2, hdeq⟩
      · rw [hmid]
        exact Or.inl (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hbM) hc2)
      · refine Or.inr ⟨a₁ * d₁, Subgroup.mul_mem _ ha1 hd1, d₂ * c₂,
          Subgroup.mul_mem _ hd2 hc2, ?_⟩
        rw [hmid, hdeq]
        simp only [mul_assoc]

/-- Inverse closure of the two-cell set. `B` is direct; the inverse of a Weyl
cell uses `w⁻¹ = (w * w)⁻¹ * w`, so it is again a Weyl cell.
Public because the subgroup packaging below must reference it. -/
public theorem twoCell_inv {n m : ℕ} (hm : m + 1 < n)
    {x : StableSteinberg F} (hx : x ∈ twoCellSet n m) :
    x⁻¹ ∈ twoCellSet n m := by
  unfold twoCellSet at hx ⊢
  rcases hx with hbX | ⟨b₁, hb1, b₂, hb2, rfl⟩
  · exact Or.inl (Subgroup.inv_mem _ hbX)
  · have hmm : m ≠ m + 1 := Nat.ne_of_lt (Nat.lt_succ_self m)
    have hWinv : (weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ =
        ((weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹ *
          weyl (R := F) m (m + 1) hmm (1 : Fˣ)) := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hsq := weyl_sq_mem_borel (F := F) (n := n) (m := m) hm
    refine Or.inr ⟨b₂⁻¹ * (weyl (R := F) m (m + 1) hmm (1 : Fˣ) *
        weyl (R := F) m (m + 1) hmm (1 : Fˣ))⁻¹,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) (Subgroup.inv_mem _ hsq),
      b₁⁻¹, Subgroup.inv_mem _ hb1, ?_⟩
    rw [mul_inv_rev, mul_inv_rev, hWinv]
    simp only [← mul_assoc]

/-- The simple two-cell subgroup `B ∪ B w B` (Steinberg Lemma 24).
Hypothesis `hm : m + 1 < n`. Orientation: Weyl cell `b₁ * w * b₂`.
Nonclaim: no Lemma 25 step, Bruhat, quotient, or Matsumoto claim. -/
public def simpleTwoCellSubgroup (n m : ℕ) (hm : m + 1 < n) :
    Subgroup (StableSteinberg F) where
  carrier := twoCellSet n m
  mul_mem' := fun hx hy => twoCell_mul hm hx hy
  one_mem' := Or.inl (Subgroup.one_mem _)
  inv_mem' := fun hx => twoCell_inv hm hx

/-- Exact membership iff for the two-cell subgroup: `g` lies in it iff `g ∈ B`
or `g = b₁ * w * b₂` with `b₁, b₂ ∈ B`. -/
public theorem mem_simpleTwoCellSubgroup {n m : ℕ} (hm : m + 1 < n)
    {g : StableSteinberg F} :
    g ∈ simpleTwoCellSubgroup (F := F) n m hm ↔
      g ∈ finiteBorelSubgroup (F := F) n ∨
        ∃ b₁ ∈ finiteBorelSubgroup (F := F) n,
          ∃ b₂ ∈ finiteBorelSubgroup (F := F) n,
            g = b₁ * weyl (R := F) m (m + 1)
              (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) * b₂ :=
  Iff.rfl

/-- The finite Borel lies in the two-cell subgroup. Consumer API for Lemma 25. -/
public theorem finiteBorelSubgroup_le_simpleTwoCell {n m : ℕ} (hm : m + 1 < n) :
    finiteBorelSubgroup (F := F) n ≤ simpleTwoCellSubgroup (F := F) n m hm :=
  fun _ hb => Or.inl hb

/-- The simple Weyl generator lies in the two-cell subgroup (`1 * w * 1`).
Consumer API for Lemma 25. -/
public theorem weyl_mem_simpleTwoCell {n m : ℕ} (hm : m + 1 < n) :
    weyl (R := F) m (m + 1) (Nat.ne_of_lt (Nat.lt_succ_self m)) (1 : Fˣ) ∈
      simpleTwoCellSubgroup (F := F) n m hm :=
  Or.inr ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩

end StableSteinberg

end AlgebraicKTheory

end

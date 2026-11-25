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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteTorusBoundaryReduction

/-! # Finite-torus boundary-word normal form

For `[Field F]`, every `t ∈ finiteTorusSubgroup n` factors head-left as
`t = c * boundaryTorusWord L` with `c ∈ torusCocycleSubgroup` and
`L : List (Fin n × Fˣ)`.

Hypotheses: only `[Field F]` and the membership hypothesis `ht` are used. No
kernel hypothesis, length measure, product-one condition, or rank bound appears.

Orientation is head-left throughout: every cocycle defect stands to the left of
the boundary word, matching `torus_finitePair_eq_cocycle_mul_boundaryPair` and
`torus_mul_eq_torusCocycleAt_mul`. Cocycle factors are moved left past torus
letters and words by centrality (`torusCocycleSubgroup_le_center`).

Structural invariant: the proof is structural `Subgroup.closure_induction` on
`ht`, not a kernel argument or length induction. The `1` case uses `[]`;
multiplication concatenates words and commutes the right defect left; the
inverse case reverses the word, inverts coefficients, and accumulates explicit
left defects. The generator case applies the accepted finite-pair reduction and
rewrites the inverse boundary letter through the same-index cocycle identity at
`(u, u⁻¹)` closed by `torus_one`.

Low-rank behavior: for `n = 0` there are no `Fin n` letters and for `n = 1`
there is no distinct-index generator, so the closure is trivially generated and
the statement holds uniformly with no rank hypothesis.

Nonclaims: no canonicity or minimality of the word `L`, no product-one claim on
its coefficients, no membership of `boundaryTorusWord L` in the finite torus
subgroup, and no kernel (`ker toStableE`) or landing consequence.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u
variable {F : Type u} [Field F]

/-- Appending boundary-word lists multiplies the boundary words. -/
private theorem boundaryTorusWord_append {n : ℕ} (L₁ L₂ : List (Fin n × Fˣ)) :
    boundaryTorusWord (F := F) (L₁ ++ L₂) =
      boundaryTorusWord (F := F) L₁ * boundaryTorusWord (F := F) L₂ := by
  simp [boundaryTorusWord, List.map_append, List.prod_append]

/-- Inverse of one boundary letter is a left cocycle defect times the
inverse-coefficient letter. Uses the same-index pair identity
`torus_mul_eq_torusCocycleAt_mul` at `(w, w⁻¹)` closed by `torus_one`, keeping
the defect left via centrality. -/
private theorem boundaryLetter_inv {n : ℕ} (k : Fin n) (w : Fˣ) :
    ∃ d ∈ torusCocycleSubgroup (F := F),
      (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ =
        d * boundaryTorusWord (F := F) [(k, w⁻¹)] := by
  have hpair := torus_mul_eq_torusCocycleAt_mul (F := F)
    (n := n) (i := k.val) (Nat.ne_of_lt k.isLt) w w⁻¹
  have hCmem := torusCocycleAt_mem_torusCocycleSubgroup (F := F)
    k.val n (Nat.ne_of_lt k.isLt) w w⁻¹
  rw [mul_inv_cancel, torus_one (R := F) k.val n (Nat.ne_of_lt k.isLt),
    mul_one] at hpair
  have hCcenter : torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹ ∈
      Subgroup.center (StableSteinberg F) :=
    torusCocycleSubgroup_le_center (F := F) hCmem
  have hT : torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ =
      (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ *
        torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹ := by
    calc torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹
        = 1 * torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ := (one_mul _).symm
      _ = ((torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ *
            torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w) *
          torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ := by
          rw [inv_mul_cancel]
      _ = (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ *
          (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
            torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹) :=
          mul_assoc _ _ _
      _ = (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ *
          torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹ := by
          rw [hpair]
  have hinv : (torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w)⁻¹ =
      torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ *
        (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹ := by
    have h := congrArg
      (· * (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹) hT
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    exact h.symm
  have hCinv : (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹ ∈
      torusCocycleSubgroup (F := F) :=
    (torusCocycleSubgroup (F := F)).inv_mem hCmem
  have hCinvCenter :
      (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹ ∈
        Subgroup.center (StableSteinberg F) :=
    (Subgroup.center (StableSteinberg F)).inv_mem hCcenter
  have hswap : torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ *
        (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹ =
      (torusCocycleAt (F := F) k.val n (Nat.ne_of_lt k.isLt) w w⁻¹)⁻¹ *
        torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ :=
    Subgroup.mem_center_iff.mp hCinvCenter _
  have hword : boundaryTorusWord (F := F) [(k, w⁻¹)] =
      torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w⁻¹ := by
    simp [boundaryTorusWord]
  refine ⟨_, hCinv, ?_⟩
  rw [hword, hinv, hswap]

/-- Inverse of a boundary word is a left cocycle defect times the reversed
inverse-coefficient word. Induction on the word; the letter case is
`boundaryLetter_inv`, defects move left by centrality. -/
private theorem boundaryTorusWord_inv {n : ℕ} (L : List (Fin n × Fˣ)) :
    ∃ d ∈ torusCocycleSubgroup (F := F),
      (boundaryTorusWord (F := F) L)⁻¹ =
        d * boundaryTorusWord (F := F)
          (L.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) := by
  induction L with
  | nil =>
    refine ⟨1, (torusCocycleSubgroup (F := F)).one_mem, ?_⟩
    simp [boundaryTorusWord]
  | cons p L' ih =>
    obtain ⟨k, w⟩ := p
    obtain ⟨d', hd'mem, hd'eq⟩ := ih
    obtain ⟨e, hemem, heeq⟩ := boundaryLetter_inv (F := F) k w
    have hecenter : e ∈ Subgroup.center (StableSteinberg F) :=
      torusCocycleSubgroup_le_center (F := F) hemem
    have hcomm : boundaryTorusWord (F := F)
          (L'.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) * e =
        e * boundaryTorusWord (F := F)
          (L'.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) :=
      Subgroup.mem_center_iff.mp hecenter _
    have hword_cons : boundaryTorusWord (F := F) ((k, w) :: L') =
        torus (R := F) k.val n (Nat.ne_of_lt k.isLt) w *
          boundaryTorusWord (F := F) L' := by
      simp [boundaryTorusWord]
    have hrev : (((k, w) :: L').reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) =
        (L'.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) ++ [(k, w⁻¹)] := by
      simp
    refine ⟨d' * e,
      (torusCocycleSubgroup (F := F)).mul_mem hd'mem hemem, ?_⟩
    rw [hword_cons, mul_inv_rev, hd'eq, heeq, hrev, boundaryTorusWord_append,
      mul_assoc d' _ _, ← mul_assoc _ e _, hcomm, mul_assoc e _ _,
      mul_assoc d' e _]

/-- Every finite-torus element is a left cocycle defect times a boundary word.

Hypotheses: only `[Field F]` and `ht : t ∈ finiteTorusSubgroup n`. The proof is
structural `Subgroup.closure_induction`: `1` maps to `[]`, products concatenate
words, inverses reverse/invert words, and generators use the accepted
finite-pair reduction with the inverse letter rewritten by the same-index
cocycle identity. Orientation is head-left; defects commute left by centrality.

Nonclaims: the word is not canonical or minimal, no product-one condition on
coefficients is claimed, and no kernel consequence is drawn. -/
public theorem finiteTorus_eq_cocycle_mul_boundaryTorusWord
    {n : ℕ} {t : StableSteinberg F}
    (ht : t ∈ StableSteinberg.finiteTorusSubgroup (R := F) n) :
    ∃ c ∈ StableSteinberg.torusCocycleSubgroup (F := F),
      ∃ L : List (Fin n × Fˣ),
        t = c * StableSteinberg.boundaryTorusWord (F := F) L := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, u, rfl, hi, hj⟩ := hx
    obtain ⟨c₀, hc₀mem, hc₀eq⟩ :=
      torus_finitePair_eq_cocycle_mul_boundaryPair (F := F) hi hj hij u
    obtain ⟨e, hemem, heeq⟩ := boundaryLetter_inv (⟨j, hj⟩ : Fin n) u
    have hecenter : e ∈ Subgroup.center (StableSteinberg F) :=
      torusCocycleSubgroup_le_center (F := F) hemem
    have hcomm : torus (R := F) (⟨i, hi⟩ : Fin n).val n
          (Nat.ne_of_lt (⟨i, hi⟩ : Fin n).isLt) u * e =
        e * torus (R := F) (⟨i, hi⟩ : Fin n).val n
          (Nat.ne_of_lt (⟨i, hi⟩ : Fin n).isLt) u :=
      Subgroup.mem_center_iff.mp hecenter _
    have hc₀eq' : torus (R := F) i j hij u =
        c₀ * (torus (R := F) (⟨i, hi⟩ : Fin n).val n
          (Nat.ne_of_lt (⟨i, hi⟩ : Fin n).isLt) u *
          (torus (R := F) (⟨j, hj⟩ : Fin n).val n
            (Nat.ne_of_lt (⟨j, hj⟩ : Fin n).isLt) u)⁻¹) := hc₀eq
    have hword : boundaryTorusWord (F := F) [(⟨i, hi⟩, u), (⟨j, hj⟩, u⁻¹)] =
        torus (R := F) (⟨i, hi⟩ : Fin n).val n
          (Nat.ne_of_lt (⟨i, hi⟩ : Fin n).isLt) u *
          boundaryTorusWord (F := F) [(⟨j, hj⟩, u⁻¹)] := by
      simp [boundaryTorusWord]
    refine ⟨c₀ * e,
      (torusCocycleSubgroup (F := F)).mul_mem hc₀mem hemem,
      [(⟨i, hi⟩, u), (⟨j, hj⟩, u⁻¹)], ?_⟩
    rw [hc₀eq', heeq, hword, ← mul_assoc _ e _, hcomm, mul_assoc e _ _,
      mul_assoc c₀ e _]
  | one =>
    refine ⟨1, (torusCocycleSubgroup (F := F)).one_mem, [], ?_⟩
    simp [boundaryTorusWord]
  | mul x y _ _ ihx ihy =>
    obtain ⟨c₁, hc₁mem, L₁, h₁⟩ := ihx
    obtain ⟨c₂, hc₂mem, L₂, h₂⟩ := ihy
    have hc₂center : c₂ ∈ Subgroup.center (StableSteinberg F) :=
      torusCocycleSubgroup_le_center (F := F) hc₂mem
    have hcomm : boundaryTorusWord (F := F) L₁ * c₂ =
        c₂ * boundaryTorusWord (F := F) L₁ :=
      Subgroup.mem_center_iff.mp hc₂center _
    refine ⟨c₁ * c₂,
      (torusCocycleSubgroup (F := F)).mul_mem hc₁mem hc₂mem, L₁ ++ L₂, ?_⟩
    rw [h₁, h₂, boundaryTorusWord_append, mul_assoc c₁ _ _,
      ← mul_assoc _ c₂ _, hcomm, mul_assoc c₂ _ _, mul_assoc c₁ c₂ _]
  | inv x _ ih =>
    obtain ⟨c, hcmem, L, hL⟩ := ih
    obtain ⟨d, hdmem, hdeq⟩ := boundaryTorusWord_inv (F := F) L
    have hcInvCenter : c⁻¹ ∈ Subgroup.center (StableSteinberg F) :=
      (Subgroup.center (StableSteinberg F)).inv_mem
        (torusCocycleSubgroup_le_center (F := F) hcmem)
    have hswap : boundaryTorusWord (F := F)
          (L.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) * c⁻¹ =
        c⁻¹ * boundaryTorusWord (F := F)
          (L.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)) :=
      Subgroup.mem_center_iff.mp hcInvCenter _
    have hdCenter : d ∈ Subgroup.center (StableSteinberg F) :=
      torusCocycleSubgroup_le_center (F := F) hdmem
    have hswap2 : c⁻¹ * d = d * c⁻¹ :=
      Subgroup.mem_center_iff.mp hdCenter _
    refine ⟨c⁻¹ * d,
      (torusCocycleSubgroup (F := F)).mul_mem
        ((torusCocycleSubgroup (F := F)).inv_mem hcmem) hdmem,
      (L.reverse.map fun p : Fin n × Fˣ => (p.1, p.2⁻¹)), ?_⟩
    rw [hL, mul_inv_rev, hdeq, mul_assoc d _ c⁻¹, hswap, ← mul_assoc d c⁻¹ _,
      ← hswap2]

end StableSteinberg

end AlgebraicKTheory

end

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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzTrace
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatBoundaryTorusIdentities

/-! # Bounded torus transport through a weighted Weyl word

For `n : ℕ` and `[Field F]`, a single torus generator `Tₐ(r)` travels right
past a coefficient-carrying Weyl word `weightedWeylProd wc` at the cost of a
left central cocycle defect: `Tₐ(r) * weightedWeylProd wc =
c * (weightedWeylProd wc * T_{a'}(r'))` with `c ∈ torusCocycleSubgroup` and
`T_{a'}(r') ∈ finiteTorusSubgroup n`.

Orientation is head-left throughout, matching `weightedWeylProd` and
`List.prod`: the head entry is the leftmost factor, the atomic step rewrites
`Tₐ(r) * W_b(u)` with the head Weyl factor on the left, and the list induction
is head-first, preserving the exact `c * (weightedWeylProd wc * T')`
parentheses. Hypotheses are `[Field F]` only: the field is needed for the
same-pair collapse `weyl_samePair_mul_eq_cocycle_mul_torus`, while the labels
contribute only `Fin n` endpoints.

Both the transported label `a'` and the transported coefficient `r'` are
existential: each atomic step takes `a' = conjLabel b a` with a coefficient
supplied by two applications of `exists_weylOfSwapLabel_mul_eq_rightHurwitz`
followed by the same-pair collapse, and the list recursion threads those
existentials through the tail. Finite-rank preservation holds because every
transported torus sits at `Fin n` endpoints, hence in `finiteTorusSubgroup n`
via `torus_mem_finiteTorusSubgroup`.

Nonclaims: no fixed transported label or coefficient is asserted, no defect
triviality (`c = 1` is false in general), no deletion, strict descent, or
termination, no torus normal form, no kernel generation, no TWT, and no
Matsumoto theorem.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- Head-left product of a paired cons cell: the head Weyl factor is leftmost. -/
private theorem weightedWeylProd_cons_aux {n : ℕ} (b : SwapLabel n) (u : Fˣ)
    (tl : List (SwapLabel n × Fˣ)) :
    weightedWeylProd ((b, u) :: tl) =
      weylOfSwapLabel b u * weightedWeylProd tl := by
  simp only [weightedWeylProd, List.map_cons, List.prod_cons]

/-- Atomic torus step past one weighted Weyl factor, with no endpoint analysis.

Unfold `Tₐ(r) = Wₐ(r) * Wₐ(-1)`, transport each Weyl factor right past `W_b(u)`
by `exists_weylOfSwapLabel_mul_eq_rightHurwitz` (first with `-1`, then with
`r`) so both landed factors share the label `conjLabel b a`, collapse that
same-label pair by `weyl_samePair_mul_eq_cocycle_mul_torus`, and move only the
cocycle defect left past `W_b(u)` by centrality. The transported coefficient
`(-q₁) * q₂⁻¹` is existential, and the new torus lies in
`finiteTorusSubgroup n` by its `Fin n` endpoints. -/
private theorem atomic_torus_through_weyl {n : ℕ} (a b : SwapLabel n)
    (r u : Fˣ) :
    ∃ (c : StableSteinberg F) (a' : SwapLabel n) (r' : Fˣ),
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
          (fun h => a.property (Fin.ext h)) r * weylOfSwapLabel b u =
        c * (weylOfSwapLabel b u *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
  obtain ⟨q₁, hq₁⟩ := exists_weylOfSwapLabel_mul_eq_rightHurwitz a b r u
  obtain ⟨q₂, hq₂⟩ := exists_weylOfSwapLabel_mul_eq_rightHurwitz a b (-1) u
  obtain ⟨c₀, hc₀, hpair⟩ :=
    StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus (F := F)
      (conjLabel b a).val.1.val (conjLabel b a).val.2.val
      (fun h => (conjLabel b a).property (Fin.ext h)) q₁ q₂
  have hTor : StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
        (fun h => a.property (Fin.ext h)) r =
        weylOfSwapLabel a r * weylOfSwapLabel a (-1) := rfl
  have hpairW : weylOfSwapLabel (conjLabel b a) q₁ *
        weylOfSwapLabel (conjLabel b a) q₂ =
        c₀ * StableSteinberg.torus (R := F) (conjLabel b a).val.1.val
          (conjLabel b a).val.2.val
          (fun h => (conjLabel b a).property (Fin.ext h)) ((-q₁) * q₂⁻¹) :=
    hpair
  have hTmem : StableSteinberg.torus (R := F) (conjLabel b a).val.1.val
        (conjLabel b a).val.2.val
        (fun h => (conjLabel b a).property (Fin.ext h)) ((-q₁) * q₂⁻¹) ∈
      StableSteinberg.finiteTorusSubgroup (R := F) n :=
    StableSteinberg.torus_mem_finiteTorusSubgroup
      (conjLabel b a).val.1.isLt (conjLabel b a).val.2.isLt _ _
  have hcen : c₀ ∈ Subgroup.center (StableSteinberg F) :=
    StableSteinberg.torusCocycleSubgroup_le_center (F := F) hc₀
  have hcomm : weylOfSwapLabel b u * c₀ = c₀ * weylOfSwapLabel b u :=
    Subgroup.mem_center_iff.mp hcen _
  refine ⟨c₀, conjLabel b a, (-q₁) * q₂⁻¹, hc₀, hTmem, ?_⟩
  rw [hTor, mul_assoc, hq₂, ← mul_assoc, hq₁, mul_assoc, hpairW,
    ← mul_assoc, hcomm, mul_assoc]

/-- Cons combination: atomic head step plus tail recursion, defects in order.

From `Tₐ(r) * W_b(u) = c₀ * (W_b(u) * T_mid)` and
`T_mid * weightedWeylProd tl = c₁ * (weightedWeylProd tl * T')`, reassociate
head-left, move the recursive defect `c₁` left past the head Weyl factor by
centrality, and combine defects as `c₀ * c₁`, preserving the exact head-left
`c * (weightedWeylProd ((b, u) :: tl) * T')` parentheses. -/
private theorem cons_torus_through {n : ℕ} (b : SwapLabel n) (u : Fˣ)
    (tl : List (SwapLabel n × Fˣ)) (a : SwapLabel n) (r : Fˣ)
    (c₀ : StableSteinberg F) (a_mid : SwapLabel n) (r_mid : Fˣ)
    (hc₀ : c₀ ∈ StableSteinberg.torusCocycleSubgroup (F := F))
    (h₀ : StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
        (fun h => a.property (Fin.ext h)) r * weylOfSwapLabel b u =
      c₀ * (weylOfSwapLabel b u *
        StableSteinberg.torus (R := F) a_mid.val.1.val a_mid.val.2.val
          (fun h => a_mid.property (Fin.ext h)) r_mid))
    (c₁ : StableSteinberg F) (a' : SwapLabel n) (r' : Fˣ)
    (hc₁ : c₁ ∈ StableSteinberg.torusCocycleSubgroup (F := F))
    (hmem' : StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
        (fun h => a'.property (Fin.ext h)) r' ∈
      StableSteinberg.finiteTorusSubgroup (R := F) n)
    (h₁ : StableSteinberg.torus (R := F) a_mid.val.1.val a_mid.val.2.val
        (fun h => a_mid.property (Fin.ext h)) r_mid * weightedWeylProd tl =
      c₁ * (weightedWeylProd tl *
        StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r')) :
    ∃ (c : StableSteinberg F) (a'' : SwapLabel n) (r'' : Fˣ),
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) a''.val.1.val a''.val.2.val
          (fun h => a''.property (Fin.ext h)) r'' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
          (fun h => a.property (Fin.ext h)) r *
          weightedWeylProd ((b, u) :: tl) =
        c * (weightedWeylProd ((b, u) :: tl) *
          StableSteinberg.torus (R := F) a''.val.1.val a''.val.2.val
            (fun h => a''.property (Fin.ext h)) r'') := by
  have hWcons : weightedWeylProd ((b, u) :: tl) =
      weylOfSwapLabel b u * weightedWeylProd tl :=
    weightedWeylProd_cons_aux b u tl
  have hcen₁ : c₁ ∈ Subgroup.center (StableSteinberg F) :=
    StableSteinberg.torusCocycleSubgroup_le_center (F := F) hc₁
  have hcomm₁ : weylOfSwapLabel b u * c₁ = c₁ * weylOfSwapLabel b u :=
    Subgroup.mem_center_iff.mp hcen₁ _
  have hc : c₀ * c₁ ∈ StableSteinberg.torusCocycleSubgroup (F := F) :=
    Subgroup.mul_mem _ hc₀ hc₁
  refine ⟨c₀ * c₁, a', r', hc, hmem', ?_⟩
  rw [hWcons]
  calc StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
          (fun h => a.property (Fin.ext h)) r *
          (weylOfSwapLabel b u * weightedWeylProd tl)
      _ = (StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
            (fun h => a.property (Fin.ext h)) r * weylOfSwapLabel b u) *
          weightedWeylProd tl := by
        rw [← mul_assoc]
      _ = (c₀ * (weylOfSwapLabel b u *
            StableSteinberg.torus (R := F) a_mid.val.1.val a_mid.val.2.val
              (fun h => a_mid.property (Fin.ext h)) r_mid)) *
          weightedWeylProd tl := by
        rw [h₀]
      _ = c₀ * ((weylOfSwapLabel b u *
            StableSteinberg.torus (R := F) a_mid.val.1.val a_mid.val.2.val
              (fun h => a_mid.property (Fin.ext h)) r_mid) *
          weightedWeylProd tl) := by
        rw [mul_assoc]
      _ = c₀ * (weylOfSwapLabel b u *
          (StableSteinberg.torus (R := F) a_mid.val.1.val a_mid.val.2.val
              (fun h => a_mid.property (Fin.ext h)) r_mid *
            weightedWeylProd tl)) := by
        rw [mul_assoc (weylOfSwapLabel b u) _ _]
      _ = c₀ * (weylOfSwapLabel b u *
          (c₁ * (weightedWeylProd tl *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r'))) := by
        rw [h₁]
      _ = c₀ * ((weylOfSwapLabel b u * c₁) *
          (weightedWeylProd tl *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r')) := by
        rw [← mul_assoc (weylOfSwapLabel b u) _ _]
      _ = c₀ * ((c₁ * weylOfSwapLabel b u) *
          (weightedWeylProd tl *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r')) := by
        rw [hcomm₁]
      _ = c₀ * (c₁ * (weylOfSwapLabel b u *
          (weightedWeylProd tl *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r'))) := by
        rw [mul_assoc c₁ _ _]
      _ = c₀ * (c₁ * ((weylOfSwapLabel b u * weightedWeylProd tl) *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r')) := by
        rw [← mul_assoc (weylOfSwapLabel b u) _ _]
      _ = (c₀ * c₁) * ((weylOfSwapLabel b u * weightedWeylProd tl) *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
        rw [← mul_assoc]

/-- Bounded torus transport through a weighted Weyl word.

Purpose: move one torus generator right past a head-left
`weightedWeylProd wc` word, exhibiting a left central cocycle defect and a
transported torus generator. Orientation is head-left throughout, matching
`weightedWeylProd`: the empty word fixes `(c, a', r') = (1, a, r)`, and the
cons case threads the private atomic head step through the tail recursion,
moving the recursive defect past the head Weyl factor by centrality and
combining defects in order as `c₀ * c₁`. Hypotheses: `[Field F]` only.
The transported label and coefficient are existential, and the transported
torus stays in `finiteTorusSubgroup n` by its `Fin n` endpoints.

Nonclaims: no fixed transported label or coefficient, no defect triviality,
no deletion, strict descent, or termination, no torus normal form, no kernel
generation, no TWT, and no Matsumoto theorem. -/
public theorem exists_torus_through_weightedWeylProd {n : ℕ}
    (a : SwapLabel n) (r : Fˣ) (wc : List (SwapLabel n × Fˣ)) :
    ∃ (c : StableSteinberg F) (a' : SwapLabel n) (r' : Fˣ),
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      StableSteinberg.torus (R := F) a.val.1.val a.val.2.val
          (fun h => a.property (Fin.ext h)) r * weightedWeylProd wc =
        c * (weightedWeylProd wc *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
  induction wc generalizing a r with
  | nil =>
    refine ⟨1, a, r, Subgroup.one_mem _, ?_, ?_⟩
    · exact StableSteinberg.torus_mem_finiteTorusSubgroup
        a.val.1.isLt a.val.2.isLt _ r
    · simp only [weightedWeylProd, List.map_nil, List.prod_nil, mul_one,
        one_mul]
  | cons head tail ih =>
    obtain ⟨b, u⟩ := head
    obtain ⟨c₀, a_mid, r_mid, hc₀, _, h₀⟩ :=
      atomic_torus_through_weyl a b r u
    obtain ⟨c₁, a', r', hc₁, hmem', h₁⟩ := ih a_mid r_mid
    exact cons_torus_through b u tail a r c₀ a_mid r_mid hc₀ h₀
      c₁ a' r' hc₁ hmem' h₁

end AlgebraicKTheory

end

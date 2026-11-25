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

/-! # Terminal equal-denotation weighted Weyl deletion

For `n : ℕ` and `[Field F]`, a coefficient-carrying word `wc` over
`pre ++ [t₁, t₂] ++ suf` whose terminal pair has equal swap denotations
deletes to a word over `pre ++ suf` with the exact two-letter length drop, at
the cost of a left cocycle defect and a finite-torus residual kept at the
deletion site. Orientation is head-left throughout, matching
`weightedWeylProd`.

The coefficients `u v` are read existentially from the actual paired word by
a sound split, never invented from the label-only hypothesis. Equal swap
denotations give exactly the ordered-equal or reversed-endpoint case (proved
privately): the ordered case rewrites `W(t₁, u) * W(t₂, v)` by the existing
public `StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus` with residual
`r = (-u) * v⁻¹`, while the reversed case first rewrites the second Weyl
factor into `t₁` orientation by `StableSteinberg.weyl_swap` and then applies
the same-pair theorem with residual `r = (-u) * (-(v⁻¹))⁻¹`. The cocycle
defect moves past `weightedWeylProd wcPre` to the far left by centrality
(`torusCocycleSubgroup_le_center`); the torus residual stays at the deletion
site and never travels through `wcSuf`.

Nonclaims: no vanishing defect (`c = 1` is false in general) or vanishing
torus, no torus transport or ordered normal form, no termination or global
induction, no kernel generation, no TWT, and no Matsumoto result.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- Equal swap denotations give exactly the ordered-equal or reversed-endpoint
case. Evaluating both denotations at `t₁.val.1` forces the first endpoint of
`t₂` to agree with one endpoint of `t₁`; the remaining endpoint is then
forced, since a third alternative would fix `t₁.val.1` against `t₁.property`. -/
private theorem swapDenote_eq_cases {n : ℕ} (t₁ t₂ : SwapLabel n)
    (heq : swapDenote t₁ = swapDenote t₂) :
    (t₁.val.1 = t₂.val.1 ∧ t₁.val.2 = t₂.val.2) ∨
      (t₁.val.1 = t₂.val.2 ∧ t₁.val.2 = t₂.val.1) := by
  have e : swapDenote t₁ t₁.val.1 = swapDenote t₂ t₁.val.1 := by rw [heq]
  have eL : swapDenote t₁ t₁.val.1 = t₁.val.2 := by
    unfold swapDenote
    exact Equiv.swap_apply_left _ _
  have h1 : swapDenote t₂ t₁.val.1 = t₁.val.2 := e.symm.trans eL
  unfold swapDenote at h1
  by_cases hb1 : t₁.val.1 = t₂.val.1
  · left
    refine ⟨hb1, ?_⟩
    rw [hb1, Equiv.swap_apply_left] at h1
    exact h1.symm
  · by_cases hb2 : t₁.val.1 = t₂.val.2
    · right
      refine ⟨hb2, ?_⟩
      rw [hb2, Equiv.swap_apply_right] at h1
      exact h1.symm
    · exfalso
      rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at h1
      exact t₁.property h1

/-- A paired word over `pre ++ [t₁, t₂] ++ suf` splits around the terminal
pair, with both coefficients read existentially from the actual word. -/
private theorem split_paired_delete {n : ℕ} {pre suf : List (SwapLabel n)}
    {t₁ t₂ : SwapLabel n} {wc : List (SwapLabel n × Fˣ)}
    (h : wc.map Prod.fst = pre ++ [t₁, t₂] ++ suf) :
    ∃ wcPre u v wcSuf,
      wc = wcPre ++ ([(t₁, u), (t₂, v)] ++ wcSuf) ∧
        wcPre.map Prod.fst = pre ∧ wcSuf.map Prod.fst = suf := by
  rw [List.append_assoc] at h
  obtain ⟨wcPre, wcRest, rfl, hPre, hRest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨wcPair, wcSuf, rfl, hPair, hSuf⟩ := List.map_eq_append_iff.mp hRest
  obtain ⟨p₁, rest₁, rfl, hp₁, ht₁⟩ := List.map_eq_cons_iff.mp hPair
  obtain ⟨p₂, rest₂, rfl, hp₂, ht₂⟩ := List.map_eq_cons_iff.mp ht₁
  have hnil : rest₂ = [] := List.map_eq_nil_iff.mp ht₂
  subst hnil
  obtain ⟨l₁, u⟩ := p₁
  obtain ⟨l₂, v⟩ := p₂
  have hl₁ : l₁ = t₁ := hp₁
  have hl₂ : l₂ = t₂ := hp₂
  subst hl₁
  subst hl₂
  exact ⟨wcPre, u, v, wcSuf, rfl, hPre, hSuf⟩

/-- Weyl words at propositionally equal indices agree; the inequality proofs
are identified by proof irrelevance. -/
private theorem weyl_label_congr {x x' y y' : ℕ} {hx : x ≠ y} {hx' : x' ≠ y'}
    (w : Fˣ) (h1 : x = x') (h2 : y = y') :
    StableSteinberg.weyl x y hx w = StableSteinberg.weyl x' y' hx' w := by
  subst h1
  subst h2
  rfl

/-- Appending paired words multiplies head-left products. -/
private theorem weightedWeylProd_append_aux {n : ℕ}
    (l₁ l₂ : List (SwapLabel n × Fˣ)) :
    weightedWeylProd (l₁ ++ l₂) =
      weightedWeylProd l₁ * weightedWeylProd l₂ := by
  unfold weightedWeylProd
  rw [List.map_append, List.prod_append]

/-- Head-left product of an explicit coefficient pair. -/
private theorem weightedWeylProd_pair_aux {n : ℕ} (t₁ t₂ : SwapLabel n)
    (u v : Fˣ) :
    weightedWeylProd [(t₁, u), (t₂, v)] =
      weylOfSwapLabel t₁ u * weylOfSwapLabel t₂ v := by
  unfold weightedWeylProd
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]

/-- Assemble the deletion packet from a same-pair product identity: the cocycle
defect moves past the prefix product to the far left by centrality, while the
torus residual stays at the deletion site. The shortened label projection and
the exact two-letter length drop follow from the sound split. -/
private theorem pack_terminal_delete {n : ℕ} {pre suf : List (SwapLabel n)}
    {t₁ t₂ : SwapLabel n} {wc wcPre wcSuf : List (SwapLabel n × Fˣ)}
    {u v : Fˣ} {c : StableSteinberg F} {r : Fˣ}
    (hsplit : wc = wcPre ++ ([(t₁, u), (t₂, v)] ++ wcSuf))
    (hPre : wcPre.map Prod.fst = pre) (hSuf : wcSuf.map Prod.fst = suf)
    (hc : c ∈ StableSteinberg.torusCocycleSubgroup (F := F))
    (hT : StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
      (fun h => t₁.property (Fin.ext h)) r ∈
      StableSteinberg.finiteTorusSubgroup (R := F) n)
    (hW1W2 : weylOfSwapLabel t₁ u * weylOfSwapLabel t₂ v =
      c * StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
        (fun h => t₁.property (Fin.ext h)) r) :
    ∃ (wcPre' wcSuf' : List (SwapLabel n × Fˣ)) (u' v' : Fˣ)
      (c' : StableSteinberg F) (r' : Fˣ),
      wc = wcPre' ++ ([(t₁, u'), (t₂, v')] ++ wcSuf') ∧
      wcPre'.map Prod.fst = pre ∧
      wcSuf'.map Prod.fst = suf ∧
      c' ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) r' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      weightedWeylProd wc =
        c' * (weightedWeylProd wcPre' *
          (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
            (fun h => t₁.property (Fin.ext h)) r' * weightedWeylProd wcSuf')) ∧
      (wcPre' ++ wcSuf').map Prod.fst = pre ++ suf ∧
      wc.length = (wcPre' ++ wcSuf').length + 2 := by
  refine ⟨wcPre, wcSuf, u, v, c, r, hsplit, hPre, hSuf, hc, hT, ?_, ?_, ?_⟩
  · have e1 : weightedWeylProd wc = weightedWeylProd wcPre *
        (weightedWeylProd [(t₁, u), (t₂, v)] * weightedWeylProd wcSuf) := by
      rw [hsplit, weightedWeylProd_append_aux, weightedWeylProd_append_aux]
    have hcen : c ∈ Subgroup.center (StableSteinberg F) :=
      StableSteinberg.torusCocycleSubgroup_le_center (F := F) hc
    have hcomm : weightedWeylProd wcPre * c = c * weightedWeylProd wcPre :=
      Subgroup.mem_center_iff.mp hcen _
    rw [e1, weightedWeylProd_pair_aux, hW1W2]
    calc weightedWeylProd wcPre *
            ((c * StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
              (fun h => t₁.property (Fin.ext h)) r) * weightedWeylProd wcSuf)
        _ = weightedWeylProd wcPre *
            (c * (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
              (fun h => t₁.property (Fin.ext h)) r * weightedWeylProd wcSuf)) := by
          rw [mul_assoc]
        _ = (weightedWeylProd wcPre * c) *
            (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
              (fun h => t₁.property (Fin.ext h)) r * weightedWeylProd wcSuf) := by
          rw [mul_assoc]
        _ = (c * weightedWeylProd wcPre) *
            (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
              (fun h => t₁.property (Fin.ext h)) r * weightedWeylProd wcSuf) := by
          rw [hcomm]
        _ = c * (weightedWeylProd wcPre *
            (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
              (fun h => t₁.property (Fin.ext h)) r * weightedWeylProd wcSuf)) := by
          rw [mul_assoc]
  · rw [List.map_append, hPre, hSuf]
  · rw [hsplit]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Terminal equal-denotation weighted Weyl deletion.

Purpose: delete an adjacent equal-denotation terminal pair from a
coefficient-carrying Weyl word, keeping head-left orientation throughout
(matching `weightedWeylProd`). Hypotheses: `[Field F]` only, a paired word
`wc` projecting to `pre ++ [t₁, t₂] ++ suf`, and equal swap denotations
`swapDenote t₁ = swapDenote t₂`. The coefficients `u v` are read
existentially from the actual word by a sound split. Equal denotations give
exactly two cases: ordered-equal labels use
`StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus` with residual
`r = (-u) * v⁻¹`, while reversed-endpoint labels first rewrite the second
Weyl factor into `t₁` orientation by `StableSteinberg.weyl_swap` and then use
the same-pair theorem with residual `r = (-u) * (-(v⁻¹))⁻¹`. The cocycle
defect `c` moves past the prefix product to the far left by centrality; the
torus residual stays at the deletion site and lands in
`finiteTorusSubgroup n`. The shortened word projects to `pre ++ suf` with
the exact two-letter length drop.

Nonclaims: no vanishing defect (`c = 1` is false in general) or vanishing
torus, no torus transport through the suffix or ordered normal form, no
termination or global induction, no kernel generation, no TWT, and no
Matsumoto result. -/
public theorem exists_weighted_hurwitz_terminal_delete
    {n : ℕ}
    (pre suf : List (SwapLabel n)) (t₁ t₂ : SwapLabel n)
    (wc : List (SwapLabel n × Fˣ))
    (hlabels : wc.map Prod.fst = pre ++ [t₁, t₂] ++ suf)
    (heq : swapDenote t₁ = swapDenote t₂) :
    ∃ (wcPre wcSuf : List (SwapLabel n × Fˣ)) (u v : Fˣ)
      (c : StableSteinberg F) (r : Fˣ),
      wc = wcPre ++ ([(t₁, u), (t₂, v)] ++ wcSuf) ∧
      wcPre.map Prod.fst = pre ∧
      wcSuf.map Prod.fst = suf ∧
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) r ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      weightedWeylProd wc =
        c * (weightedWeylProd wcPre *
          (StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
            (fun h => t₁.property (Fin.ext h)) r * weightedWeylProd wcSuf)) ∧
      (wcPre ++ wcSuf).map Prod.fst = pre ++ suf ∧
      wc.length = (wcPre ++ wcSuf).length + 2 := by
  obtain ⟨wcPre, u, v, wcSuf, hsplit, hPre, hSuf⟩ :=
    split_paired_delete hlabels
  obtain hcase := swapDenote_eq_cases t₁ t₂ heq
  cases hcase with
  | inl hord =>
    obtain ⟨h1, h2⟩ := hord
    have hW2 : weylOfSwapLabel t₂ v =
        StableSteinberg.weyl t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) v :=
      weyl_label_congr v (congrArg Fin.val h1.symm) (congrArg Fin.val h2.symm)
    obtain ⟨c, hc, hpair⟩ :=
      StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus (F := F)
        t₁.val.1.val t₁.val.2.val (fun h => t₁.property (Fin.ext h)) u v
    have hW1W2 : weylOfSwapLabel t₁ u * weylOfSwapLabel t₂ v =
        c * StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) ((-u) * v⁻¹) := by
      have hW1 : weylOfSwapLabel t₁ u =
          StableSteinberg.weyl t₁.val.1.val t₁.val.2.val
            (fun h => t₁.property (Fin.ext h)) u := rfl
      rw [hW1, hW2]
      exact hpair
    have hT : StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) ((-u) * v⁻¹) ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n :=
      StableSteinberg.torus_mem_finiteTorusSubgroup
        t₁.val.1.isLt t₁.val.2.isLt _ ((-u) * v⁻¹)
    exact pack_terminal_delete hsplit hPre hSuf hc hT hW1W2
  | inr hrev =>
    obtain ⟨h1, h2⟩ := hrev
    have hW2 : weylOfSwapLabel t₂ v =
        StableSteinberg.weyl t₁.val.2.val t₁.val.1.val
          (fun h => t₁.property ((Fin.ext h).symm)) v :=
      weyl_label_congr v (congrArg Fin.val h2.symm) (congrArg Fin.val h1.symm)
    have hswap := StableSteinberg.weyl_swap t₁.val.2.val t₁.val.1.val
      (fun h => t₁.property ((Fin.ext h).symm)) v
    have hW2' : weylOfSwapLabel t₂ v =
        StableSteinberg.weyl t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) (-(v⁻¹)) := by
      rw [hW2, hswap]
    obtain ⟨c, hc, hpair⟩ :=
      StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus (F := F)
        t₁.val.1.val t₁.val.2.val (fun h => t₁.property (Fin.ext h)) u (-(v⁻¹))
    have hW1W2 : weylOfSwapLabel t₁ u * weylOfSwapLabel t₂ v =
        c * StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) ((-u) * (-(v⁻¹))⁻¹) := by
      have hW1 : weylOfSwapLabel t₁ u =
          StableSteinberg.weyl t₁.val.1.val t₁.val.2.val
            (fun h => t₁.property (Fin.ext h)) u := rfl
      rw [hW1, hW2']
      exact hpair
    have hT : StableSteinberg.torus (R := F) t₁.val.1.val t₁.val.2.val
          (fun h => t₁.property (Fin.ext h)) ((-u) * (-(v⁻¹))⁻¹) ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n :=
      StableSteinberg.torus_mem_finiteTorusSubgroup
        t₁.val.1.isLt t₁.val.2.isLt _ ((-u) * (-(v⁻¹))⁻¹)
    exact pack_terminal_delete hsplit hPre hSuf hc hT hW1W2

end AlgebraicKTheory

end

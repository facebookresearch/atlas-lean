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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzDeleteTransport

/-! # Global weighted Hurwitz strict decrease

For `n : ℕ` and `[Field F]`, a coefficient-carrying Weyl word `wc` whose
label projection is nonempty with permutation product one admits a one-step
global strict decrease: a shorter paired word `wcShort` with product-one
projection and exact two-letter length drop, a cocycle defect `c`, and a
transported torus residual in `finiteTorusSubgroup n`, with
`weightedWeylProd wc = c * (weightedWeylProd wcShort * T')` head-left
throughout.

The proof composes the three predecessor packets in canonical temporal order.
The pure shortening theorem exposes a reachable adjacent equal-denotation pair
with deleted product one and exact length drop; the trace packet lifts that
reach to the coefficient-carrying word with the identical product; terminal
deletion through the suffix removes the lifted pair and transports the at-site
residual right, accumulating only the central cocycle defect. The returned
`wordProd` follows by rewriting with the shortened projection, the paired-word
length equation follows from `List.length_map` with the pure length equation
and the shortened projection, and the weighted products compose by
transitivity. No cocycle centrality or algebraic rearrangement is needed here.

Nonclaims: this is the one-step global strict decrease, not the normal-form
induction; `pre`, `suf`, the trace, and any auxiliary `wcMid` stay
existential and are not exposed. No normal-form theorem, kernel generation,
`List.ofFn` bridge, TWT, inverse identities, naturality, or Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- One-step global weighted Hurwitz strict decrease.

Purpose: from a coefficient-carrying Weyl word whose label projection is
nonempty with permutation product one, produce a shorter paired word with
product-one projection and exact two-letter length drop, keeping head-left
orientation throughout (matching `weightedWeylProd`). Hypotheses: `[Field F]`
only, a paired word `wc`, nonemptiness of the label projection itself, and
product one of that projection. The shortened word, the cocycle defect in
`torusCocycleSubgroup`, and the transported torus residual in
`finiteTorusSubgroup n` are existential. The defect order is the canonical
temporal order inherited from the deletion-transport packet.

Nonclaims: one step only, not the normal-form induction; no exposed `pre`,
`suf`, trace, or auxiliary midpoint word; no kernel generation, `List.ofFn`
bridge, TWT, inverse identities, naturality, or Matsumoto claim. -/
public theorem exists_weighted_hurwitz_global_strict_decrease
    {n : ℕ} (wc : List (SwapLabel n × Fˣ))
    (hne : wc.map Prod.fst ≠ [])
    (hprod : wordProd (wc.map Prod.fst) = 1) :
    ∃ (wcShort : List (SwapLabel n × Fˣ)) (c : StableSteinberg F)
      (a' : SwapLabel n) (r' : Fˣ),
      wordProd (wcShort.map Prod.fst) = 1 ∧
      wc.length = wcShort.length + 2 ∧
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      weightedWeylProd wc =
        c * (weightedWeylProd wcShort *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
  obtain ⟨pre, t₁, t₂, suf, hReach, heq, hprodDel, hlenPure⟩ :=
    exists_hurwitz_adjacent_equal (wc.map Prod.fst) hne hprod
  obtain ⟨wcMid, hMidLabels, hMidProd⟩ :=
    exists_weighted_hurwitz_trace hReach wc rfl
  obtain ⟨wcShort, c, a', r', hShortLabels, _hlenDel, hc, hmem, hprodMid⟩ :=
    exists_weighted_hurwitz_terminal_delete_through_suffix pre suf t₁ t₂ wcMid
      hMidLabels heq
  have hword : wordProd (wcShort.map Prod.fst) = 1 := by
    rw [hShortLabels]
    exact hprodDel
  have hlen : wc.length = wcShort.length + 2 := by
    have hmap : (wc.map Prod.fst).length = wc.length := by simp
    have hmapS : (wcShort.map Prod.fst).length = wcShort.length := by simp
    have hShortLen : (wcShort.map Prod.fst).length = (pre ++ suf).length := by
      rw [hShortLabels]
    omega
  exact ⟨wcShort, c, a', r', hword, hlen, hc, hmem, hMidProd.trans hprodMid⟩

end AlgebraicKTheory

end

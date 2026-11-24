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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzDelete
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylTorusTransport

/-! # Terminal weighted deletion transported through its suffix

For `n : ℕ` and `[Field F]`, a coefficient-carrying word `wc` over
`pre ++ [t₁, t₂] ++ suf` whose terminal pair has equal swap denotations
deletes to a word over `pre ++ suf` with the exact two-letter length drop,
while the at-site torus residual travels right through the suffix word.
Orientation is head-left throughout, matching `weightedWeylProd`.

The proof composes the two predecessor packets in canonical temporal order.
Terminal deletion gives `weightedWeylProd wc = c_d * (P_pre * (T * P_suf))`
with `c_d` in the cocycle subgroup and `T` the at-site torus residual at
`t₁`; bounded transport gives `T * P_suf = c_t * (P_suf * T')` with `c_t`
central and `T'` the transported torus generator. Only the central defect
`c_t` moves left across the prefix product (by
`torusCocycleSubgroup_le_center`); no Weyl or torus factor is commuted.
Defects combine in canonical temporal order as `c_d * c_t`, and the shortened
product folds to `weightedWeylProd (wcPre ++ wcSuf) = P_pre * P_suf`. The
shortened word, its projection, and the exact length drop are reused from the
deletion packet; the finite-torus membership of `T'` is preserved from the
transport packet.

Nonclaims: no `wordProd`/permutation-kernel hypothesis or conclusion, no
global Hurwitz reach, no well-founded induction or termination, no arbitrary
finite-torus normal form, no kernel generation, no TWT, and no Matsumoto
theorem.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- Appending paired words multiplies head-left products. -/
private theorem weightedWeylProd_append_aux {n : ℕ}
    (l₁ l₂ : List (SwapLabel n × Fˣ)) :
    weightedWeylProd (l₁ ++ l₂) =
      weightedWeylProd l₁ * weightedWeylProd l₂ := by
  unfold weightedWeylProd
  rw [List.map_append, List.prod_append]

/-- Terminal equal-denotation weighted deletion with the residual transported
through the suffix.

Purpose: delete an adjacent equal-denotation terminal pair from a
coefficient-carrying Weyl word and move the resulting at-site torus residual
right past the suffix word, keeping head-left orientation throughout
(matching `weightedWeylProd`). Hypotheses: `[Field F]` only, a paired word
`wc` projecting to `pre ++ [t₁, t₂] ++ suf`, and equal swap denotations
`swapDenote t₁ = swapDenote t₂`. The shortened word is `wcPre ++ wcSuf`,
reused from the deletion packet together with its `pre ++ suf` projection
and the exact two-letter length drop. The transported label `a'` and
coefficient `r'` are existential, and the transported torus stays in
`finiteTorusSubgroup n`. Defects combine in canonical temporal order
`c_d * c_t`: the deletion defect first, the transport defect second, with
only the central `c_t` commuted left across the prefix product.

Nonclaims: no `wordProd`/permutation-kernel hypothesis or conclusion, no
global Hurwitz reach, no well-founded induction or termination, no arbitrary
finite-torus normal form, no kernel generation, no TWT, and no Matsumoto
theorem. -/
public theorem exists_weighted_hurwitz_terminal_delete_through_suffix
    {n : ℕ}
    (pre suf : List (SwapLabel n)) (t₁ t₂ : SwapLabel n)
    (wc : List (SwapLabel n × Fˣ))
    (hlabels : wc.map Prod.fst = pre ++ [t₁, t₂] ++ suf)
    (heq : swapDenote t₁ = swapDenote t₂) :
    ∃ (wcShort : List (SwapLabel n × Fˣ)) (c : StableSteinberg F)
      (a' : SwapLabel n) (r' : Fˣ),
      wcShort.map Prod.fst = pre ++ suf ∧
      wc.length = wcShort.length + 2 ∧
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r' ∈
        StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      weightedWeylProd wc =
        c * (weightedWeylProd wcShort *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r') := by
  obtain ⟨wcPre, wcSuf, _u, _v, c_d, r, _hsplit, _hPre, _hSuf, hc_d, _hT,
    hprod, hshort, hlen⟩ :=
    exists_weighted_hurwitz_terminal_delete pre suf t₁ t₂ wc hlabels heq
  obtain ⟨c_t, a', r', hc_t, hmem', htrans⟩ :=
    exists_torus_through_weightedWeylProd t₁ r wcSuf
  have hcen_t : c_t ∈ Subgroup.center (StableSteinberg F) :=
    StableSteinberg.torusCocycleSubgroup_le_center (F := F) hc_t
  have hcomm_t : weightedWeylProd wcPre * c_t = c_t * weightedWeylProd wcPre :=
    Subgroup.mem_center_iff.mp hcen_t _
  have hc : c_d * c_t ∈ StableSteinberg.torusCocycleSubgroup (F := F) :=
    Subgroup.mul_mem _ hc_d hc_t
  have e1 : weightedWeylProd wc =
      c_d * (weightedWeylProd wcPre *
        (c_t * (weightedWeylProd wcSuf *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r'))) := by
    rw [hprod, htrans]
  have e2 : weightedWeylProd wcPre *
        (c_t * (weightedWeylProd wcSuf *
          StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
            (fun h => a'.property (Fin.ext h)) r')) =
      c_t * ((weightedWeylProd wcPre * weightedWeylProd wcSuf) *
        StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
          (fun h => a'.property (Fin.ext h)) r') := by
    calc weightedWeylProd wcPre *
            (c_t * (weightedWeylProd wcSuf *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r'))
        _ = (weightedWeylProd wcPre * c_t) *
            (weightedWeylProd wcSuf *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r') := by
          rw [mul_assoc]
        _ = (c_t * weightedWeylProd wcPre) *
            (weightedWeylProd wcSuf *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r') := by
          rw [hcomm_t]
        _ = c_t * (weightedWeylProd wcPre *
            (weightedWeylProd wcSuf *
              StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
                (fun h => a'.property (Fin.ext h)) r')) := by
          rw [mul_assoc]
        _ = c_t * ((weightedWeylProd wcPre * weightedWeylProd wcSuf) *
            StableSteinberg.torus (R := F) a'.val.1.val a'.val.2.val
              (fun h => a'.property (Fin.ext h)) r') := by
          rw [← mul_assoc (weightedWeylProd wcPre) (weightedWeylProd wcSuf) _]
  have hfold : weightedWeylProd (wcPre ++ wcSuf) =
      weightedWeylProd wcPre * weightedWeylProd wcSuf :=
    weightedWeylProd_append_aux wcPre wcSuf
  refine ⟨wcPre ++ wcSuf, c_d * c_t, a', r', hshort, hlen, hc, hmem', ?_⟩
  rw [e1, e2, ← mul_assoc c_d c_t _, hfold]

end AlgebraicKTheory

end

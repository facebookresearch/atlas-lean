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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzLift

/-! # Coefficient-bearing transport along a Hurwitz trace

For `n : ℕ` and `[Ring R]`, `weightedWeylProd wc` is the head-left ordered
product of the coefficient-carrying Weyl elements `weylOfSwapLabel` over the
paired word `wc : List (SwapLabel n × Rˣ)`, and
`exists_weighted_hurwitz_trace` transports those coefficients forward along a
`HurwitzReach` trace: from a paired word over `w` it exhibits a paired word
over `w'` with the identical product. Orientation is head-left and forward
throughout, matching `wordProd`, the accepted right move, and the atomic lift:
in each step the conjugator travels left past the victim and the conjugated
label appears on the right with the transported coefficient supplied by
`exists_weylOfSwapLabel_mul_eq_rightHurwitz`. Hypotheses are `[Ring R]` only,
with no field, commutativity, or finiteness assumption beyond the labels.

Nonclaims: no symmetric, left, or reverse closure (only the directed right
move and its reflexive-transitive closure), no terminal-pair deletion, no
torus/cocycle landing, no strict descent or termination, no finite
`List.ofFn` bridge, no kernel generation, no TWT, and no Matsumoto theorem.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {R : Type u} [Ring R]

/-- Head-left product of a coefficient-carrying Weyl word.

Purpose: product meaning of a paired label-coefficient word, with each entry
`(a, u)` denoting `weylOfSwapLabel a u`. Orientation is head-left, matching
`wordProd` and `List.prod`: the head entry is the leftmost factor.
Hypotheses: `[Ring R]` only. Nonclaims: no trace transport, deletion,
torus/cocycle, descent, `List.ofFn` bridge, kernel, TWT, or Matsumoto
content. -/
public def weightedWeylProd {n : ℕ}
    (wc : List (SwapLabel n × Rˣ)) : StableSteinberg R :=
  (wc.map fun p => weylOfSwapLabel p.1 p.2).prod

/-- Appending paired words multiplies head-left products. -/
private theorem weightedWeylProd_append {n : ℕ}
    (l₁ l₂ : List (SwapLabel n × Rˣ)) :
    weightedWeylProd (l₁ ++ l₂) =
      weightedWeylProd l₁ * weightedWeylProd l₂ := by
  unfold weightedWeylProd
  rw [List.map_append, List.prod_append]

/-- One paired right-Hurwitz step, via the atomic coefficient update. -/
private theorem weighted_pair_step {n : ℕ} (a b : SwapLabel n) (u v : Rˣ) :
    ∃ q : Rˣ, weightedWeylProd [(a, u), (b, v)] =
      weightedWeylProd [(b, v), (conjLabel b a, q)] := by
  obtain ⟨q, hq⟩ := exists_weylOfSwapLabel_mul_eq_rightHurwitz a b u v
  refine ⟨q, ?_⟩
  unfold weightedWeylProd
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  exact hq

/-- A paired word over `pre ++ [a, b] ++ suf` splits around the active pair. -/
private theorem split_paired {n : ℕ} {pre suf : List (SwapLabel n)}
    {a b : SwapLabel n} {wc : List (SwapLabel n × Rˣ)}
    (h : wc.map Prod.fst = pre ++ [a, b] ++ suf) :
    ∃ wcPre u v wcSuf,
      wc = wcPre ++ ([(a, u), (b, v)] ++ wcSuf) ∧
        wcPre.map Prod.fst = pre ∧ wcSuf.map Prod.fst = suf := by
  rw [List.append_assoc] at h
  obtain ⟨wcPre, wcRest, rfl, hPre, hRest⟩ := List.map_eq_append_iff.mp h
  obtain ⟨wcPair, wcSuf, rfl, hPair, hSuf⟩ := List.map_eq_append_iff.mp hRest
  obtain ⟨p₁, t₁, rfl, hp₁, ht₁⟩ := List.map_eq_cons_iff.mp hPair
  obtain ⟨p₂, t₂, rfl, hp₂, ht₂⟩ := List.map_eq_cons_iff.mp ht₁
  have ht₂nil : t₂ = [] := List.map_eq_nil_iff.mp ht₂
  subst ht₂nil
  obtain ⟨l₁, u⟩ := p₁
  obtain ⟨l₂, v⟩ := p₂
  have hl₁ : l₁ = a := hp₁
  have hl₂ : l₂ = b := hp₂
  subst hl₁
  subst hl₂
  exact ⟨wcPre, u, v, wcSuf, rfl, hPre, hSuf⟩

/-- One directed step transports coefficients with the product preserved. -/
private theorem step_transport {n : ℕ} {w₁ w₂ : List (SwapLabel n)}
    (h : HurwitzStep w₁ w₂) (wc : List (SwapLabel n × Rˣ))
    (hlabels : wc.map Prod.fst = w₁) :
    ∃ wc' : List (SwapLabel n × Rˣ),
      wc'.map Prod.fst = w₂ ∧
        weightedWeylProd wc = weightedWeylProd wc' := by
  cases h with
  | step pre suf a b =>
    obtain ⟨wcPre, u, v, wcSuf, hsplit, hPre, hSuf⟩ := split_paired hlabels
    obtain ⟨q, hq⟩ := weighted_pair_step a b u v
    have hmap : ([(b, v), (conjLabel b a, q)].map Prod.fst) =
      [b, conjLabel b a] := rfl
    refine ⟨wcPre ++ ([(b, v), (conjLabel b a, q)] ++ wcSuf), ?_, ?_⟩
    · simp only [List.map_append, hPre, hSuf, hmap, List.append_assoc]
    · simp only [hsplit, weightedWeylProd_append, hq]

/-- Reflexive-transitive recursion of the transport over the trace. -/
private theorem transport_reach {n : ℕ} {w w' : List (SwapLabel n)}
    (h : Relation.ReflTransGen (@HurwitzStep n) w w')
    (wc : List (SwapLabel n × Rˣ)) (hlabels : wc.map Prod.fst = w) :
    ∃ wc' : List (SwapLabel n × Rˣ),
      wc'.map Prod.fst = w' ∧
        weightedWeylProd wc = weightedWeylProd wc' := by
  induction h generalizing wc with
  | refl =>
    exact ⟨wc, hlabels, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨wcMid, hMidLabels, hMidProd⟩ := ih wc hlabels
    obtain ⟨wc', hFinLabels, hFinProd⟩ :=
      step_transport hstep wcMid hMidLabels
    exact ⟨wc', hFinLabels, hMidProd.trans hFinProd⟩

/-- Coefficients transport forward along a Hurwitz trace, product preserved.

Purpose: lift a pure forward `HurwitzReach w w'` trace to paired words: every
coefficient-carrying word over `w` reaches one over `w'` with the identical
`weightedWeylProd`. Orientation is head-left and forward: each single step
rewrites `Wₐ(u) * W_b(v)` to `W_b(v) * W_{conjLabel b a}(q)` with the exact
witness `q` from `exists_weylOfSwapLabel_mul_eq_rightHurwitz`, and the trace
recursion follows the pinned `Relation.ReflTransGen` order. Hypotheses:
`[Ring R]` only. Nonclaims: no symmetric/left/reverse closure, no
terminal-pair deletion, no torus/cocycle landing, no strict
descent/termination, no finite `List.ofFn` bridge, no kernel generation, no
TWT, and no Matsumoto theorem. -/
public theorem exists_weighted_hurwitz_trace {n : ℕ}
    {w w' : List (SwapLabel n)} (h : HurwitzReach w w')
    (wc : List (SwapLabel n × Rˣ)) (hlabels : wc.map Prod.fst = w) :
    ∃ wc' : List (SwapLabel n × Rˣ),
      wc'.map Prod.fst = w' ∧ weightedWeylProd wc = weightedWeylProd wc' :=
  transport_reach h wc hlabels

end AlgebraicKTheory

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Compositions with an odd number of parts

This module proves a roots-of-unity partial fraction identity and relates linear and circular
composition counts when the parts are unrestricted.

## Roots-of-unity partial fractions

For natural numbers `α < β`, with `ζ = e^{2πi/β}`, and a complex number `u` with
`1 - u ^ β ≠ 0`,
`u ^ α / (1 - u ^ β) = (1 / β) ∑_{k < β} ζ ^ (-k α) / (1 - ζ ^ k u)`
(`MetaMathlibExt.pow_div_one_sub_pow_eq_sum`): the partial fraction decomposition of
`u ^ α / (1 - u ^ β)` over the `β`-th roots of unity.

## Proof outline

Since `ζ` is a primitive `β`-th root of unity, `(ζ ^ k u) ^ β = u ^ β`, so no denominator
`1 - ζ ^ k u` vanishes, and the geometric sum gives
`1 / (1 - ζ ^ k u) = (∑_{j < β} (ζ ^ k u) ^ j) / (1 - u ^ β)`. After exchanging the two sums,
the coefficient of `u ^ j / (1 - u ^ β)` is `∑_{k < β} (ζ ^ (j - α)) ^ k`. It is `β` when
`j = α`, and `0` otherwise: for `j ≠ α` with `j, α < β`, `β` does not divide `j - α`, so
`ζ ^ (j - α)` is a `β`-th root of unity different from `1`.

## Implementation notes

For the first identity of Bowman's Lemma 9, split the circular cut sets according to whether
they contain the last edge. Those with that edge cut correspond to linear compositions.

`pow_div_one_sub_pow_eq_sum` keeps the full name, the statement and the docstring it had as a
wanted theorem in `WantedExt.Combinatorics.Enumerative.CompositionsOddPartsWanted`, which
imports this module.

## References

The theorem's docstring cites its source, Joshua P. Bowman's *Compositions with an Odd Number of
Parts, and Other Congruences* (Journal of Integer Sequences, 2024). The proof here is
self-contained.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The multiplicity function (indicator sequence `i(A; n)`) of a set `A ⊆ ℕ`: `1` on `A`,
`0` off `A`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 2 (`jis-2024-24.3.6-thm-3`). -/
public def setMultiplicity (A : Set ℕ) [DecidablePred (· ∈ A)] (a : ℕ) : ℕ :=
  if a ∈ A then 1 else 0

/-- `b(ℕ_[μ], m, q; n)`: the number of (linear) compositions of `n` with parts in the multiset
`ℕ_[μ]` whose number of parts is congruent to `q` modulo `m`; a composition with `k` parts is a
`k`-tuple of positive integers summing to `n`, weighted by its `∏ μ(part)` colorings. The empty
composition of `0` has `0` parts.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public def compositionCountMod (μ : ℕ → ℕ) (m q n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % m = q % m),
    ∑ c ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun c => ∀ i, 0 < c i), ∏ i, μ (c i)

/-- The size of the part of a circular composition of `n` that starts right after the removed
edge `s`. The cycle graph `C_n` has vertices `0, …, n - 1` and edges `s = {s, s + 1 mod n}`;
a circular composition is a nonempty set `S` of removed edges, and the part after edge `s`
ends at the next removed edge, so its size is the least `d ∈ [1, n]` with `(s + d) % n ∈ S`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 2 (`jis-2024-24.3.6-thm-3`). -/
public def circularPartSize (n : ℕ) (S : Finset ℕ) (s : ℕ) : ℕ :=
  (((Finset.Icc 1 n).filter fun d => (s + d) % n ∈ S).min).untopD 0

/-- `c(ℕ_[μ], m, q; n)`: the number of circular compositions of `n` (nonempty sets of removed
edges of the cycle graph `C_n`, one part per removed edge) with parts in `ℕ_[μ]` whose number
of parts is congruent to `q` modulo `m`, each weighted by its `∏ μ(part size)` colorings.
There are none for `n = 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Section 3 (`jis-2024-24.3.6-thm-3`). -/
public def circularCompositionCountMod (μ : ℕ → ℕ) (m q n : ℕ) : ℕ :=
  ∑ S ∈ (Finset.range n).powerset.filter (fun S => S.Nonempty ∧ S.card % m = q % m),
    ∏ s ∈ S, μ (circularPartSize n S s)

/-- **Roots-of-unity partial fraction identity.** Let $\alpha < \beta$ be natural numbers and
let $\zeta = e^{2 \pi i / \beta}$. For every complex number $u$ with $1 - u^\beta \ne 0$,
$$\frac{u^\alpha}{1 - u^\beta} =
\frac{1}{\beta} \sum_{k=0}^{\beta - 1} \frac{\zeta^{-k \alpha}}{1 - \zeta^k u}.$$

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 7 (`jis-2024-24.3.6-lem-7`). -/
public theorem pow_div_one_sub_pow_eq_sum (α β : ℕ) (hα : α < β)
    (u : ℂ) (hu : 1 - u ^ β ≠ 0) :
    u ^ α / (1 - u ^ β)
      = (1 / (β : ℂ)) * ∑ k ∈ Finset.range β,
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ (-((k : ℤ) * (α : ℤ)))
            / (1 - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ k * u) := by
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ))
  have hβ0 : β ≠ 0 := by omega
  have hζ : IsPrimitiveRoot ζ β := Complex.isPrimitiveRoot_exp β hβ0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hβ0
  have hβC : (β : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hβ0
  have hpow (k : ℕ) : (ζ ^ k * u) ^ β = u ^ β := by
    rw [mul_pow, ← pow_mul, mul_comm k β, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  -- No denominator vanishes: `ζ ^ k * u = 1` would give `u ^ β = 1`.
  have hden (k : ℕ) : 1 - ζ ^ k * u ≠ 0 := fun h => by
    apply hu
    rw [← hpow k, show ζ ^ k * u = 1 by linear_combination -h, one_pow, sub_self]
  -- Expand each term with the geometric sum `∑_{j < β} (ζ ^ k * u) ^ j`.
  have hterm (k : ℕ) : ζ ^ (-((k : ℤ) * (α : ℤ))) / (1 - ζ ^ k * u)
      = (∑ j ∈ Finset.range β, u ^ j * (ζ ^ ((j : ℤ) - α)) ^ k) / (1 - u ^ β) := by
    have hmul (j : ℕ) : u ^ j * (ζ ^ ((j : ℤ) - α)) ^ k
        = ζ ^ (-((k : ℤ) * (α : ℤ))) * (ζ ^ k * u) ^ j := by
      rw [mul_pow, ← pow_mul, ← zpow_natCast (ζ ^ ((j : ℤ) - α)), ← zpow_mul,
        ← zpow_natCast ζ (k * j), ← mul_assoc, ← zpow_add₀ hζ0, mul_comm]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j _ => hmul j, ← Finset.mul_sum,
      div_eq_div_iff (hden k) hu, ← hpow k, ← geom_sum_mul_neg]
    ring
  -- Orthogonality: `∑_{k < β} (ζ ^ (j - α)) ^ k` is `β` if `j = α` and `0` otherwise.
  have horth : ∀ j ∈ Finset.range β,
      ∑ k ∈ Finset.range β, (ζ ^ ((j : ℤ) - α)) ^ k = if j = α then (β : ℂ) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    split_ifs with hjα
    · subst hjα
      simp
    · have hne : ζ ^ ((j : ℤ) - α) ≠ 1 := by
        rw [Ne, hζ.zpow_eq_one_iff_dvd]
        intro hdvd
        have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
        omega
      rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hζ.pow_eq_one, one_zpow, sub_self, zero_div]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j hj => by rw [horth j hj]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range.mpr hα, ↓reduceIte]
  field_simp

private theorem card_positiveTuples (n k : ℕ) :
    ((Finset.Nat.antidiagonalTuple k n).filter (fun v => ∀ i, 0 < v i)).card =
      (Finset.univ.filter (fun c : Composition n => c.length = k)).card := by
  let toComposition (v : Fin k → ℕ)
      (hv : v ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun v => ∀ i, 0 < v i)) :
      Composition n :=
    ⟨List.ofFn v, List.forall_mem_ofFn_iff.mpr (Finset.mem_filter.mp hv).2 _, by
      rw [List.sum_ofFn]
      exact Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hv).1⟩
  refine Finset.card_bij toComposition ?_ ?_ ?_
  · intro v hv
    exact (Finset.mem_filter_univ _).mpr List.length_ofFn
  · intro v hv w hw h
    exact List.ofFn_injective (congrArg Composition.blocks h)
  · intro c hc
    have hlen : c.length = k := (Finset.mem_filter.mp hc).2
    subst k
    refine ⟨c.blocksFun, Finset.mem_filter.mpr ⟨Finset.Nat.mem_antidiagonalTuple.mpr
      c.sum_blocksFun, c.one_le_blocksFun⟩, ?_⟩
    exact Composition.ext c.ofFn_blocksFun

private theorem compositionCountMod_univ_eq_card {m q : ℕ} (hq : q < m) (n : ℕ) :
    compositionCountMod (setMultiplicity Set.univ) m q n =
      (Finset.univ.filter (fun c : Composition n => c.length % m = q)).card := by
  let lengths := (Finset.range (n + 1)).filter (fun k => k % m = q % m)
  calc
    compositionCountMod (setMultiplicity Set.univ) m q n =
        ∑ k ∈ lengths, (Finset.univ.filter (fun c : Composition n => c.length = k)).card := by
      unfold compositionCountMod
      refine Finset.sum_congr rfl fun k _ => ?_
      simpa [setMultiplicity] using card_positiveTuples n k
    _ = (Finset.univ.filter (fun c : Composition n => c.length ∈ lengths)).card :=
      Finset.sum_card_fiberwise_eq_card_filter Finset.univ lengths Composition.length
    _ = _ := by
      congr 1
      ext c
      simp [lengths, Nat.mod_eq_of_lt hq]

private def circularCutSets (m q n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun S => S.Nonempty ∧ S.card % m = q % m)

private theorem circularCompositionCountMod_univ_eq_card (m q n : ℕ) :
    circularCompositionCountMod (setMultiplicity Set.univ) m q n =
      (circularCutSets m q n).card := by
  simp [circularCompositionCountMod, circularCutSets, setMultiplicity]

-- Mathlib encodes the internal boundaries, shifted down by one, as a subset of `Fin n`.
private def compositionCuts (n : ℕ) : Composition (n + 1) ≃ Finset (Fin n) :=
  (compositionEquiv (n + 1)).trans (compositionAsSetEquiv (n + 1))

private theorem compositionCuts_length (n : ℕ) (s : Finset (Fin n)) :
    ((compositionCuts n).symm s).length = s.card + 1 := by
  let e : Fin n ↪ Fin (n + 2) := (Fin.succEmb n).trans Fin.castSuccEmb
  let c := (compositionAsSetEquiv (n + 1)).symm s
  change c.toComposition.length = _
  have hb : c.boundaries = insert 0 (insert (Fin.last (n + 1)) (s.map e)) := by
    ext i
    change i ∈ { j : Fin (n + 2) | j = 0 ∨ j = Fin.last (n + 1) ∨
      ∃ (k : Fin n) (_ : k ∈ s), (j : ℕ) = (k : ℕ) + 1 }.toFinset ↔ _
    simp only [Set.toFinset_ofPred, Finset.mem_filter_univ, Finset.mem_insert, Finset.mem_map,
      exists_prop, Fin.ext_iff]
    simp only [e, Function.Embedding.trans_apply, Fin.castSuccEmb_apply, Fin.val_castSucc,
      eq_comm (a := (i : ℕ))]
    rfl
  have notLast : Fin.last (n + 1) ∉ s.map e := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    have hv : (i : ℕ) + 1 = n + 1 := congrArg Fin.val hi
    exact (Nat.ne_of_lt i.isLt) (Nat.add_right_cancel hv)
  have notZero : (0 : Fin (n + 2)) ∉ insert (Fin.last (n + 1)) (s.map e) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · have hv : 0 = n + 1 := congrArg Fin.val h
      omega
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      have hv : (i : ℕ) + 1 = 0 := congrArg Fin.val hi
      omega
  rw [CompositionAsSet.toComposition_length, CompositionAsSet.length, hb,
    Finset.card_insert_of_notMem notZero, Finset.card_insert_of_notMem notLast,
    Finset.card_map, Nat.add_sub_cancel]

private theorem card_circularCutSets_with_last (m q n : ℕ) :
    ((circularCutSets m q (n + 1)).filter (fun S => n ∈ S)).card =
      (Finset.univ.filter (fun c : Composition (n + 1) => c.length % m = q % m)).card := by
  let e := compositionCuts n
  let toCuts : Composition (n + 1) → Finset ℕ := fun c =>
    insert n ((e c).map Fin.valEmbedding)
  have notLast (s : Finset (Fin n)) : n ∉ s.map Fin.valEmbedding := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    exact (Nat.ne_of_lt i.isLt) hi
  have hcard (c : Composition (n + 1)) : (toCuts c).card = c.length := by
    change (insert n ((e c).map Fin.valEmbedding)).card = _
    rw [Finset.card_insert_of_notMem (notLast (e c)), Finset.card_map,
      ← compositionCuts_length n (e c), e.symm_apply_apply]
  symm
  refine Finset.card_bij (fun c _ => toCuts c) ?_ ?_ ?_
  · intro c hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩,
      Finset.mem_insert_self _ _⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
      · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_lt i.isLt)
    · refine ⟨⟨n, Finset.mem_insert_self _ _⟩, ?_⟩
      rw [hcard]
      exact (Finset.mem_filter.mp hc).2
  · intro a _ b _ hab
    apply e.injective
    apply Finset.map_injective Fin.valEmbedding
    simpa only [toCuts, Finset.erase_insert (notLast _)] using
      congrArg (fun S : Finset ℕ => S.erase n) hab
  · intro S hS
    obtain ⟨hS, hn⟩ := Finset.mem_filter.mp hS
    obtain ⟨hsub, _, hmod⟩ := Finset.mem_filter.mp hS
    let s : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) ∈ S)
    have hs : s.map Fin.valEmbedding = S.erase n := by
      ext j
      simp only [Finset.mem_map, Finset.mem_erase, s, Finset.mem_filter_univ]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨Nat.ne_of_lt i.isLt, hi⟩
      · rintro ⟨hne, hj⟩
        have hlt := Finset.mem_range.mp (Finset.mem_powerset.mp hsub hj)
        exact ⟨⟨j, by omega⟩, hj, rfl⟩
    have hEq : toCuts (e.symm s) = S := by
      change insert n ((e (e.symm s)).map Fin.valEmbedding) = S
      rw [e.apply_symm_apply, hs, Finset.insert_erase hn]
    refine ⟨e.symm s, (Finset.mem_filter_univ _).mpr ?_, hEq⟩
    rw [← hcard, hEq]
    exact hmod

/-- Lemma 9: for `0 ≤ q < m` and `n ≥ 1`, `b(ℕ, m, q; n) = c(ℕ, m, q; n) - c(ℕ, m, q; n - 1)`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 9 (`jis-2024-24.3.6-lem-9`). -/
public theorem compositionCountMod_univ_eq_circular_sub {m q n : ℕ} (hq : q < m)
    (hn : 0 < n) :
    (compositionCountMod (setMultiplicity Set.univ) m q n : ℤ)
      = circularCompositionCountMod (setMultiplicity Set.univ) m q n
        - circularCompositionCountMod (setMultiplicity Set.univ) m q (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, compositionCountMod_univ_eq_card hq,
    circularCompositionCountMod_univ_eq_card]
  have hwithout : (circularCutSets m q (n + 1)).filter (fun S => n ∉ S) =
      circularCutSets m q n := by
    ext S
    simp only [circularCutSets, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsub, hp⟩, hn⟩
      refine ⟨?_, hp⟩
      intro j hj
      have hlt := Finset.mem_range.mp (hsub hj)
      have hne : j ≠ n := fun h => hn (h ▸ hj)
      exact Finset.mem_range.mpr (by omega)
    · rintro ⟨hsub, hp⟩
      refine ⟨⟨?_, hp⟩, ?_⟩
      · intro j hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hsub hj)))
      · exact fun h => Nat.lt_irrefl _ (Finset.mem_range.mp (hsub h))
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := circularCutSets m q (n + 1)) (fun S => n ∈ S)
  rw [hwithout, card_circularCutSets_with_last] at hsplit
  rw [Nat.mod_eq_of_lt hq] at hsplit
  apply eq_sub_iff_add_eq.mpr
  exact_mod_cast hsplit

end

end MetaMathlibExt

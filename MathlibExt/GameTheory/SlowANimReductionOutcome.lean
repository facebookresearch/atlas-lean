/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.GameTheory.SlowANim

/-!
# Outcomes of Slow A-Nim positions with the same reduction

In normal-play Slow `A`-Nim on `n` labelled stacks, with `A ⊆ {1, …, n}`, two positions with
equal reductions are in the same outcome class. Keeping the labels fixed lets us match each
move by its chosen set of stacks without sorting the positions. The argument also covers the
no-move cases of an empty `A` or zero stacks, in which both positions are P-positions.

## References

* Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
  Slow A-Nim*, INTEGERS 26 (2026), Article G3, pp. 1–25. Corollary 1 (Section 3.3) is the
  outcome comparison. The move correspondence uses the unplayable-token argument of
  Lemma 1 (Section 3.1).
-/

namespace MetaMathlibExt

private theorem unplayable_le_of_reachable {n : ℕ} {A : Finset ℕ} {p q : Fin n → ℕ}
    (hpq : Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p q) (i : Fin n) :
    p i - slowANimReduction A p i ≤ q i := by
  have hwf : WellFounded (fun x y : Fin n → ℕ => x ∈ slowANimMoves A y) :=
    SpragueGrundy.wfRel (slowANimGame n A)
  obtain ⟨t, hqt, ht⟩ := hwf.has_min
    {t | Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) q t} ⟨q, .refl⟩
  have hterminal : slowANimMoves A t = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun r hr => ?_
    exact ht r (hqt.tail hr) hr
  have hle : t ≤ q := by
    apply Relation.reflTransGen_le_of_le (r := (· ≥ ·)) _ _ _ hqt
    intro x y hxy j
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hxy
    by_cases hj : j ∈ S <;> simp [slowANimAfter, hj]
  let T : Set (Fin n → ℕ) := {r | Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p r ∧
    slowANimMoves A r = ∅}
  have hmem : t i ∈ (fun r => r i) '' T := ⟨t, ⟨hpq.trans hqt, hterminal⟩, rfl⟩
  have hmin : sInf ((fun r => r i) '' T) ≤ q i := (Nat.sInf_le hmem).trans (hle i)
  change p i - (p i - sInf ((fun r => r i) '' T)) ≤ q i
  omega

private theorem isP_iff_reduction {n : ℕ} (A : Finset ℕ) (p : Fin n → ℕ) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔
      SpragueGrundy.IsP (slowANimGame n A) (slowANimReduction A p) := by
  let G := slowANimGame n A
  let u (i : Fin n) := p i - slowANimReduction A p i
  let strip (q : Fin n → ℕ) (i : Fin n) := q i - u i
  have moves_strip (q : Fin n → ℕ)
      (hq : Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p q) :
      slowANimMoves A (strip q) = (slowANimMoves A q).image strip := by
    simp only [slowANimMoves, Finset.image_image]
    have hfilter : ((Finset.univ : Finset (Finset (Fin n))).filter fun S =>
        S.Nonempty ∧ S.card ∈ A ∧ ∀ i ∈ S, 1 ≤ strip q i) =
        Finset.univ.filter fun S => S.Nonempty ∧ S.card ∈ A ∧ ∀ i ∈ S, 1 ≤ q i := by
      apply Finset.filter_congr
      intro S hS
      constructor
      · rintro ⟨hne, hcard, hpos⟩
        exact ⟨hne, hcard, fun i hi => (hpos i hi).trans (Nat.sub_le _ _)⟩
      · intro hlegal
        refine ⟨hlegal.1, hlegal.2.1, fun i hi => ?_⟩
        have hmove : slowANimAfter q S ∈ slowANimMoves A q :=
          Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hlegal⟩, rfl⟩
        have hle : u i ≤ slowANimAfter q S i := unplayable_le_of_reachable (hq.tail hmove) i
        simp only [slowANimAfter, hi, ite_true] at hle
        have hpos := hlegal.2.2 i hi
        change 1 ≤ q i - u i
        omega
    rw [hfilter]
    congr 1
    funext S i
    by_cases hi : i ∈ S
    · simpa only [slowANimAfter, strip, Function.comp_apply, hi, ite_true] using
        Nat.sub_right_comm (q i) (u i) 1
    · simp [slowANimAfter, strip, hi]
  have hpreserve (q : Fin n → ℕ) :
      Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p q →
        (SpragueGrundy.IsP G q ↔ SpragueGrundy.IsP G (strip q)) := by
    induction q using (SpragueGrundy.wfRel G).induction with
    | h q ih =>
      intro hq
      rw [SpragueGrundy.isP_iff G q, SpragueGrundy.isP_iff G (strip q)]
      change (∀ r ∈ slowANimMoves A q, ¬ SpragueGrundy.IsP G r) ↔
        (∀ r ∈ slowANimMoves A (strip q), ¬ SpragueGrundy.IsP G r)
      rw [moves_strip q hq, Finset.forall_mem_image]
      exact forall_congr' fun r => forall_congr' fun hr => (ih r hr (hq.tail hr)).not
  have hstrip : strip p = slowANimReduction A p :=
    funext fun i => Nat.sub_sub_self (slowANimReduction_le A p i)
  simpa only [hstrip] using hpreserve p .refl

@[expose] public section

/-- **Positions with the same reduction have the same outcome.** Let
$A \subseteq \{1, \dots, n\}$. If two positions $p$ and $q$ of Slow$A$-Nim $\mathrm{SN}(n, A)$
have the same reduction, $r(p) = r(q)$, then $p$ is a P-position if and only if $q$ is a
P-position.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Corollary 1. -/
public theorem slowANim_isP_iff_of_reduction_eq (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (p q : Fin n → ℕ)
    (h : slowANimReduction A p = slowANimReduction A q) :
    SpragueGrundy.IsP (slowANimGame n A) p ↔ SpragueGrundy.IsP (slowANimGame n A) q := by
  by_cases hdeg : n = 0 ∨ A = ∅
  · have hempty : A = ∅ := hdeg.elim (fun hn => by simpa [hn] using hA) id
    rw [SpragueGrundy.isP_iff (slowANimGame n A) p,
      SpragueGrundy.isP_iff (slowANimGame n A) q]
    simp [hempty, slowANimGame, slowANimMoves]
  · rw [isP_iff_reduction A p, isP_iff_reduction A q, h]

end

end MetaMathlibExt

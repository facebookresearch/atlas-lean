/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSwapInjection
public import Mathlib.Combinatorics.Hall.Basic

/-!
# Orbit counting: swap injections via Hall's theorem

Swapping coordinates between `ω` and `τ` keeps the pair `(ω ∨ τ, ω ∧ τ)` fixed (`orbitKey`), and
two pairs are related by a coordinate swap iff they have the same key (`sameOrbit_iff_orbitKey`).
So a swap injection exists iff it exists orbit by orbit, and by Hall's marriage theorem
(`Fintype.all_card_le_filter_rel_iff_exists_injective`) this happens iff in every orbit the
number of pairs with first entry in `A □ B` is at most the number of pairs in `A × B`
(`PerOrbitCard`, `r2k_swapInjection_iff_perOrbitCard`). This gives an equivalent purely
combinatorial target for Reimer's inequality.

For the top orbit `PerOrbitCard A B` is the counting inequality `|A □ B| ≤ |{ω ∈ A | ω̄ ∈ B}|`
(`ω̄` the coordinatewise complement; `poc_ReimerCardForm` in `ReimerOrbitSlab`), the counting
form of Reimer's theorem. Every other orbit is a sub-cube with the remaining coordinates frozen,
and restricting `A`, `B` to it reduces that orbit to the same counting inequality for the
restricted events (argument by hand, not formalized). So `PerOrbitCardAll` has the strength of
Reimer's theorem itself. It is **not** proved here.

## Main definitions

* `orbitKey`, `sameOrbit`: the swap orbits of pairs of configurations.
* `boxOrbit A B k`, `imgOrbit A B k`: pairs with key `k` and first entry in `A □ B`, respectively
  in `A × B`.
* `PerOrbitCard A B`: `#(boxOrbit A B k) ≤ #(imgOrbit A B k)` for every key `k`;
  `PerOrbitCardAll`: for all events on all `Fin n`.

## Main results

* `r2k_swapInjection_iff_perOrbitCard`: swap injections exist iff `PerOrbitCard` holds.
* `reimer_wprob_of_perOrbitCard`: `PerOrbitCard A B → P(A □ B) ≤ P(A) P(B)`.
* `reimer_wprob_core_of_perOrbitCard`, `reimer_inequality_of_perOrbitCard`: Reimer's inequality
  **assuming** `PerOrbitCardAll`.
* `perOrbitCard_of_disjoint_support`, `perOrbitCard_of_box_empty`, `perOrbitCard_rbi`: cases
  where `PerOrbitCard` is proved.

## References

* D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000).
-/

@[expose] public section

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `q` is obtained from `p` by exchanging the two entries on some set of coordinates. -/
def sameOrbit (p q : ConfigSpace α × ConfigSpace α) : Prop :=
  ∀ a, (q.1 a = p.1 a ∧ q.2 a = p.2 a) ∨ (q.1 a = p.2 a ∧ q.2 a = p.1 a)

/-- The swap invariant `(ω ∨ τ, ω ∧ τ)` of a pair. -/
def orbitKey (p : ConfigSpace α × ConfigSpace α) : ConfigSpace α × ConfigSpace α :=
  (fun a => p.1 a || p.2 a, fun a => p.1 a && p.2 a)

omit [Fintype α] [DecidableEq α] in
/-- Two pairs are related by a coordinate swap iff they have the same orbit key. -/
theorem sameOrbit_iff_orbitKey (p q : ConfigSpace α × ConfigSpace α) :
    sameOrbit p q ↔ orbitKey p = orbitKey q := by
  constructor
  · intro h
    apply Prod.ext <;> funext a <;> rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [orbitKey, h1, h2, Bool.or_comm, Bool.and_comm]
  · intro h a
    have hor := congrFun (congrArg Prod.fst h) a
    have hand := congrFun (congrArg Prod.snd h) a
    simp only [orbitKey] at hor hand
    revert hor hand
    cases p.1 a <;> cases p.2 a <;> cases q.1 a <;> cases q.2 a <;> simp_all

omit [Fintype α] [DecidableEq α] in
/-- `swapPair` preserves the orbit key. -/
theorem orbitKey_swapPair (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : orbitKey (swapPair σ p) = orbitKey p := by
  apply Prod.ext <;> funext a <;>
    simp only [orbitKey, swapPair_fst, swapPair_snd, swapGlue_apply] <;>
    by_cases h : σ p a <;> simp [h, Bool.or_comm, Bool.and_comm]

omit [Fintype α] [DecidableEq α] in
/-- A pair in the same orbit as `p` is obtained from `p` by swapping on the coordinates where the
first entries differ. -/
theorem swapPair_eq_of_sameOrbit (p q : ConfigSpace α × ConfigSpace α) (h : sameOrbit p q) :
    q = swapPair (fun _ => fun a => decide (q.1 a ≠ p.1 a)) p := by
  apply Prod.ext
  · funext a
    simp only [swapPair_fst, swapGlue_apply]
    by_cases hpe : q.1 a = p.1 a
    · simp only [hpe, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
    · simp only [ne_eq, hpe, not_false_eq_true, decide_true, ite_true]
      rcases h a with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hpe
      · exact h1
  · funext a
    simp only [swapPair_snd, swapGlue_apply]
    by_cases hpe : q.1 a = p.1 a
    · simp only [hpe, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rcases h a with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · rw [h2, ← hpe, h1]
    · simp only [ne_eq, hpe, not_false_eq_true, decide_true, ite_true]
      rcases h a with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hpe
      · exact h2

open Classical in
/-- Pairs with orbit key `k` whose first entry lies in `A □ B`. -/
noncomputable def boxOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α × ConfigSpace α) :=
  Finset.univ.filter (fun p => p.1 ∈ disjointOccurrence A B ∧ orbitKey p = k)

open Classical in
/-- Pairs with orbit key `k` lying in `A × B`. -/
noncomputable def imgOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α × ConfigSpace α) :=
  Finset.univ.filter (fun q => q.1 ∈ A ∧ q.2 ∈ B ∧ orbitKey q = k)

/-- In every swap orbit there are at most as many pairs with first entry in `A □ B` as pairs in
`A × B`. -/
def PerOrbitCard (A B : Set (ConfigSpace α)) : Prop :=
  ∀ k : ConfigSpace α × ConfigSpace α, #(boxOrbit A B k) ≤ #(imgOrbit A B k)

/-- `PerOrbitCard` gives a swap injection, by Hall's marriage theorem. -/
theorem r2k_swapInjection_of_perOrbitCard (A B : Set (ConfigSpace α))
    (hpo : PerOrbitCard A B) : r2k_SwapInjection A B := by
  classical
  set Dom := {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} with hDom
  set r : Dom → (ConfigSpace α × ConfigSpace α) → Prop :=
    fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∧ q.2 ∈ B with hr
  have key : ∃ f : Dom → (ConfigSpace α × ConfigSpace α),
      Function.Injective f ∧ ∀ x, r x (f x) := by
    rw [← Fintype.all_card_le_filter_rel_iff_exists_injective r]
    intro Aset
    set K := Aset.image (fun p : Dom => orbitKey p.val) with hK
    have hfib : #Aset = ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp; exact Finset.mem_image_of_mem _ hp
    rw [hfib]
    have hkstep : ∀ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) ≤ #(imgOrbit A B k) := by
      intro k _
      refine le_trans ?_ (hpo k)
      apply Finset.card_le_card_of_injOn (fun p => p.val)
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        simp only [boxOrbit, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p.property, hp.2⟩
      · intro a _ b _ hab; exact Subtype.ext hab
    calc ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k))
        ≤ ∑ k ∈ K, #(imgOrbit A B k) := Finset.sum_le_sum hkstep
      _ = #(K.biUnion (fun k => imgOrbit A B k)) := by
          rw [Finset.card_biUnion]
          intro k1 _ k2 _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro q hq1 hq2
          simp only [imgOrbit, Finset.mem_filter] at hq1 hq2
          exact hne (hq1.2.2.2 ▸ hq2.2.2.2)
      _ ≤ #{b | ∃ a ∈ Aset, r a b} := by
          apply Finset.card_le_card
          intro q hq
          rw [Finset.mem_biUnion] at hq
          obtain ⟨k, hkK, hqimg⟩ := hq
          simp only [imgOrbit, Finset.mem_filter] at hqimg
          rw [hK, Finset.mem_image] at hkK
          obtain ⟨p, hpA, hpk⟩ := hkK
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ q, p, hpA, ?_, hqimg.2.1, hqimg.2.2.1⟩
          rw [sameOrbit_iff_orbitKey, hpk, ← hqimg.2.2.2]
  obtain ⟨f, hfinj, hfr⟩ := key
  set σ : ConfigSpace α × ConfigSpace α → (α → Bool) :=
    fun p => if hp : p.1 ∈ disjointOccurrence A B then
      (fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) else (fun _ => false) with hσ
  have hσbox : ∀ p (hp : p.1 ∈ disjointOccurrence A B), swapPair σ p = f ⟨p, hp⟩ := by
    intro p hp
    have hso : sameOrbit p (f ⟨p, hp⟩) := (hfr ⟨p, hp⟩).1
    have heq : swapPair (fun _ => fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) p = f ⟨p, hp⟩ :=
      (swapPair_eq_of_sameOrbit p (f ⟨p, hp⟩) hso).symm
    rw [← heq]
    simp only [swapPair, hσ, hp, ↓reduceDIte]
  refine ⟨σ, ?_, ?_⟩
  · intro p hp
    have hmem := (hfr ⟨p, hp⟩).2
    rw [hσbox p hp]
    exact ⟨hmem.1, hmem.2⟩
  · intro p hp q hq heq
    rw [Set.mem_ofPred_eq] at hp hq
    rw [hσbox p hp, hσbox q hq] at heq
    have : (⟨p, hp⟩ : Dom) = ⟨q, hq⟩ := hfinj heq
    exact Subtype.ext_iff.mp this

/-- A swap injection gives `PerOrbitCard`. -/
theorem perOrbitCard_of_swapInjection (A B : Set (ConfigSpace α))
    (hSI : r2k_SwapInjection A B) : PerOrbitCard A B := by
  classical
  obtain ⟨σ, hmem, hinj⟩ := hSI
  intro k
  apply Finset.card_le_card_of_injOn (swapPair σ)
  · intro p hp
    rw [Finset.mem_coe, boxOrbit, Finset.mem_filter] at hp
    obtain ⟨_, hpbox, hpk⟩ := hp
    have hm := hmem p hpbox
    simp only [imgOrbit, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hm.1, hm.2, by rw [orbitKey_swapPair]; exact hpk⟩
  · intro p hp q hq hpq
    rw [Finset.mem_coe, boxOrbit, Finset.mem_filter] at hp hq
    exact hinj hp.2.1 hq.2.1 hpq

/-- Swap injections exist iff `PerOrbitCard` holds. -/
theorem r2k_swapInjection_iff_perOrbitCard (A B : Set (ConfigSpace α)) :
    r2k_SwapInjection A B ↔ PerOrbitCard A B :=
  ⟨perOrbitCard_of_swapInjection A B, r2k_swapInjection_of_perOrbitCard A B⟩

/-- `PerOrbitCard A B` gives Reimer's inequality for `A`, `B` and every product probability
weight. -/
theorem reimer_wprob_of_perOrbitCard (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hpo : PerOrbitCard A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  r2k_reimer_wprob_of_swapInjection φ hφ0 hφ1 (r2k_swapInjection_of_perOrbitCard A B hpo)

/-- Events depending on disjoint coordinate sets satisfy `PerOrbitCard`. -/
theorem perOrbitCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    PerOrbitCard A B :=
  perOrbitCard_of_swapInjection A B (r2k_swapInjection_of_disjoint_support hA hB hST)

/-- If `A □ B = ∅` then `PerOrbitCard A B`. -/
theorem perOrbitCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : PerOrbitCard A B :=
  perOrbitCard_of_swapInjection A B (r2k_swapInjection_of_box_empty hbox)

/-- `PerOrbitCard rbi_A rbi_B`. -/
theorem perOrbitCard_rbi : PerOrbitCard rbi_A rbi_B :=
  perOrbitCard_of_swapInjection rbi_A rbi_B r2k_swapInjection_rbi

/-- `PerOrbitCard` for all events on all `Fin n`. Equivalent to `r2k_SwapInjectionAll`; not proved
here. -/
def PerOrbitCardAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), PerOrbitCard A B

/-- `ReimerWprobCore`, **assuming** `PerOrbitCardAll`. -/
theorem reimer_wprob_core_of_perOrbitCard (h : PerOrbitCardAll) : ReimerWprobCore :=
  r2k_reimer_wprob_core_of_swapInjection
    (fun n A B => r2k_swapInjection_of_perOrbitCard A B (h n A B))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Reimer's inequality for `bernoulliProductMeasure p`, **assuming** `PerOrbitCardAll`. -/
theorem reimer_inequality_of_perOrbitCard (h : PerOrbitCardAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (reimer_wprob_core_of_perOrbitCard h) hp A B

end StatMech

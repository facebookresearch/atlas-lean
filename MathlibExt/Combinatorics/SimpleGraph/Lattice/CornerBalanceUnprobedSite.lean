/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount

/-!
# Corner balance under removal of an unprobed site

Let `K` be a finite set of sites of `ℤ²` and `a` a boundary dart of `K`. The successor rule
`dartNext K` looks at two sites beside each dart (the site diagonally ahead and the site beside the
tail), so the boundary orbit of `a` and its corner balance (right turns minus left turns over one
period) depend on `K` only through the sites the orbit probes. Removing a site of `K` outside this
footprint leaves the orbit and its corner balance unchanged. Hence the contraction property
`BalancePreservingContraction` (every finite `K` with at least two sites has a strictly smaller
set with an orbit of the same corner balance) reduces to the saturated case
`bpc_BalanceSaturatingContraction`, where every site of `K` lies in the footprint.

Both properties are false. Under `BalancePreservingContraction`, induction on the number of sites
forces every boundary orbit of every finite nonempty set to have corner balance `-4`, the value for
a single site. The four lattice neighbours of the origin form a set with a hole; the orbit running
around the hole turns the same way at every step, so its corner balance is its (positive) period.
Every statement that takes `BalancePreservingContraction` or `bpc_BalanceSaturatingContraction` as
a hypothesis is therefore vacuous.

## Main definitions

* `StatMech.Lattice.bpc_NotProbed c e`: the successor rule at `e` does not look at the site `c`.
* `StatMech.Lattice.bpc_orbitFootprint K a`: the sites probed along the boundary orbit of `a`,
  together with the tails of its darts.
* `StatMech.Lattice.bpc_BalanceSaturatingContraction`: the contraction property restricted to
  sets contained in the footprint of the orbit.
* `StatMech.Lattice.bpc_holeRing`: the four lattice neighbours of the origin.

## Main results

* `StatMech.Lattice.bpc_cornerBalance_diff_singleton`: removing an unprobed site preserves the
  corner balance of the orbit.
* `StatMech.Lattice.bpc_contraction_of_not_saturating`: a site of `K` outside the footprint can be
  removed without changing the corner balance.
* `StatMech.Lattice.bpc_balancePreservingContraction_of_saturating`: the saturated case implies
  `BalancePreservingContraction`.
* `StatMech.Lattice.cornerBalance_eq_neg_four_of_contraction`: `BalancePreservingContraction`
  forces corner balance `-4` on every orbit.
* `StatMech.Lattice.bpc_holeRing_cornerBalance`: the orbit around the hole of `bpc_holeRing` has
  positive corner balance.
* `StatMech.Lattice.not_balancePreservingContraction`,
  `StatMech.Lattice.not_bpc_BalanceSaturatingContraction`: both contraction properties are false.
-/

@[expose] public section

open SimpleGraph Function Set

namespace StatMech

namespace Lattice

/-- The successor of `e` is the same for two sets that agree on the two sites the successor rule
probes at `e`. -/
theorem bpc_dartNext_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    dartNext K' e = dartNext K e := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K' e (h1.mpr hA), dartNext_of_front_mem K e hA]
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K' e (fun hh => hA (h1.mp hh)) (h2.mpr hB),
          dartNext_of_side_mem K e hA hB]
    · rw [dartNext_of_corner K' e (fun hh => hA (h1.mp hh)) (fun hh => hB (h2.mp hh)),
          dartNext_of_corner K e hA hB]

/-- The turn at `e` is the same for two sets that agree on the two sites the successor rule probes
at `e`. -/
theorem bpc_turnZ_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    turnZ K' e = turnZ K e := by
  classical
  unfold turnZ
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [ite_eq_left (h1.mpr hA), ite_eq_left hA]
  · rw [ite_eq_right (fun hh => hA (h1.mp hh)), ite_eq_right hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [ite_eq_left (h2.mpr hB), ite_eq_left hB]
    · rw [ite_eq_right (fun hh => hB (h2.mp hh)), ite_eq_right hB]

/-- The successor rule at the dart `e` does not look at the site `c`: `c` is neither the site
diagonally ahead of `e` nor the site beside its tail. -/
def bpc_NotProbed (c : Site 2) (e : Dart) : Prop :=
  e.head + (-rot90Fun e.dir) ≠ c ∧ e.tail + (-rot90Fun e.dir) ≠ c

/-- Removing a site not probed at `e` does not change the successor of `e`. -/
theorem bpc_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) :
    dartNext (K \ {c}) e = dartNext K e := by
  apply bpc_dartNext_agree
  · constructor
    · intro hh; exact (Set.mem_sdiff _).mp hh |>.1
    · intro hh; refine (Set.mem_sdiff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_sdiff _).mp hh |>.1
    · intro hh; refine (Set.mem_sdiff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2

/-- Removing a site not probed at `e` does not change the turn at `e`. -/
theorem bpc_turnZ_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) : turnZ (K \ {c}) e = turnZ K e := by
  apply bpc_turnZ_agree
  · constructor
    · intro hh; exact (Set.mem_sdiff _).mp hh |>.1
    · intro hh; refine (Set.mem_sdiff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_sdiff _).mp hh |>.1
    · intro hh; refine (Set.mem_sdiff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2

/-- If no dart of the orbit of `e` probes `c`, the orbit of `e` is the same for `K` and `K \ {c}`.
-/
theorem bpc_iterate_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] e)) (k : ℕ) :
    (dartNext (K \ {c}))^[k] e = (dartNext K)^[k] e := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact bpc_dartNext_diff_singleton K c ((dartNext K)^[n] e) (hnp n)

/-- A boundary dart of `K` stays a boundary dart of `K \ {c}` when `c` is not its tail. -/
theorem bpc_isBoundaryDart_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (he : IsBoundaryDart K e) (hc : c ≠ e.tail) : IsBoundaryDart (K \ {c}) e := by
  refine ⟨⟨he.1, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]; exact fun h => hc h.symm
  · intro hh; exact he.2 hh.1

/-- Removing a site never probed along the orbit preserves the periodic points of the successor map
on that orbit. -/
theorem bpc_isPeriodicPt_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (K \ {c})) n a' ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  have key : (dartNext (K \ {c}))^[n] a'.1 = (dartNext K)^[n] a.1 := by
    rw [hval]; exact bpc_iterate_dartNext_diff_singleton K c a.1 hnp n
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [key, hval] at hv
    change ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]; exact hv
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    change ((dartNextSub (K \ {c}))^[n] a').1 = a'.1
    rw [dartNextSub_iterate_val, key, hval]; exact hv

/-- Removing a site never probed along the orbit does not change the orbit period. -/
theorem bpc_dartOrbitPeriod_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    dartOrbitPeriod (K \ {c}) a' = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact bpc_isPeriodicPt_diff_singleton K c a a' hval hnp n

/-- Removing a site never probed along the orbit does not change the corner balance. -/
theorem bpc_cornerBalance_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    cornerBalance (K \ {c}) a' = cornerBalance K a := by
  classical
  unfold cornerBalance
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  set p := dartOrbitPeriod K a with hp
  have hright : rightCornerCount (K \ {c}) a'.1 p = rightCornerCount K a.1 p := by
    unfold rightCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  have hleft : leftCornerCount (K \ {c}) a'.1 p = leftCornerCount K a.1 p := by
    unfold leftCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  rw [hright, hleft]

/-- The footprint of the boundary orbit of `a`: the sites probed by the successor rule along the
orbit, together with the tails of its darts. -/
def bpc_orbitFootprint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set (Site 2) :=
  {x | ∃ i : ℕ,
    x = ((dartNext K)^[i] a.1).head + (-rot90Fun ((dartNext K)^[i] a.1).dir) ∨
    x = ((dartNext K)^[i] a.1).tail + (-rot90Fun ((dartNext K)^[i] a.1).dir) ∨
    x = ((dartNext K)^[i] a.1).tail}

theorem bpc_notProbed_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) (i : ℕ) :
    bpc_NotProbed c ((dartNext K)^[i] a.1) := by
  constructor
  · intro h; exact hc ⟨i, Or.inl h.symm⟩
  · intro h; exact hc ⟨i, Or.inr (Or.inl h.symm)⟩

theorem bpc_ne_tail_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) : c ≠ a.1.tail := by
  intro h
  apply hc
  exact ⟨0, Or.inr (Or.inr (by rw [Function.iterate_zero_apply]; exact h))⟩

/-- A site of `K` outside the footprint of the orbit of `a` can be removed, giving a strictly
smaller nonempty set with an orbit of the same corner balance. -/
theorem bpc_contraction_of_not_saturating (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hcK : c ∈ K)
    (hc : c ∉ bpc_orbitFootprint K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
  have hbd : IsBoundaryDart (K \ {c}) a.1 :=
    bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
  refine ⟨K \ {c}, hK.subset Set.sdiff_subset, ⟨a.1.tail, hbd.1⟩, ⟨a.1, hbd⟩, ?_, ?_⟩
  · have hsub : (K \ {c}) ⊂ K := by
      rw [Set.ssubset_iff_of_subset Set.sdiff_subset]
      exact ⟨c, hcK, by simp⟩
    exact Set.ncard_lt_ncard hsub hK
  · exact bpc_cornerBalance_diff_singleton K c a ⟨a.1, hbd⟩ rfl
      (bpc_notProbed_of_not_footprint K a c hc)

/-- The contraction property `BalancePreservingContraction` restricted to sets `K` contained in the
footprint of the chosen orbit. It is false: see `not_bpc_BalanceSaturatingContraction`. -/
def bpc_BalanceSaturatingContraction : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a

/-- The saturated contraction property implies `BalancePreservingContraction`: unsaturated sets
contract by removing a site outside the footprint. -/
theorem bpc_balancePreservingContraction_of_saturating
    (h : bpc_BalanceSaturatingContraction) : BalancePreservingContraction := by
  intro K hK hge a
  by_cases hsat : K ⊆ bpc_orbitFootprint K a
  · exact h K hK hge a hsat
  · rw [Set.not_subset] at hsat
    obtain ⟨c, hcK, hc⟩ := hsat
    exact bpc_contraction_of_not_saturating K hK a c hcK hc

/-- Total turn `±4` (one full revolution) for every boundary orbit of a finite nonempty star hull,
assuming `bpc_BalanceSaturatingContraction`. Vacuous: its hypothesis
`bpc_BalanceSaturatingContraction` is refuted by `not_bpc_BalanceSaturatingContraction`. -/
theorem bpc_totalTurn_eq_four_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (bpc_balancePreservingContraction_of_saturating hsat)

/-- The corner balance of the domino orbit is `-4`. -/
theorem bpc_domino_cornerBalance : cornerBalance domino dmBase = -4 := by
  rw [cornerBalance_eq_totalTurnZ]
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact domino_totalTurnZ_six

/-- Removing the site `(1, 0)` from the domino leaves the unit cell. -/
theorem bpc_domino_diff : domino \ {(![1, 0] : Site 2)} = unitCell := by
  ext v
  rw [Set.mem_sdiff, mem_domino_iff, Set.mem_singleton_iff]
  unfold unitCell
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact h
    · exact absurd h hne
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rw [h]
    intro hcon
    rw [funext_iff, Fin.forall_fin_two] at hcon
    norm_num at hcon

/-- The domino contracts to the unit cell with the same corner balance. -/
theorem bpc_domino_balanceSaturatingContraction_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
  refine ⟨unitCell, unitCell_finite, ⟨![0, 0], origin_mem_unitCell⟩, ucBase, ?_, ?_⟩
  · have h1 : unitCell.ncard = 1 := by
      unfold unitCell; exact Set.ncard_singleton _
    have h2 : domino.ncard = 2 := by
      unfold domino
      apply Set.ncard_pair
      intro hcon
      rw [funext_iff, Fin.forall_fin_two] at hcon; norm_num at hcon
    omega
  · rw [bpc_domino_cornerBalance, unitCell_cornerBalance ucBase (Or.inl rfl)]

/-- Under `BalancePreservingContraction`, every boundary orbit of every finite nonempty set has
corner balance `-4`: contract down to a single site, whose orbit has corner balance `-4`, keeping
the corner balance fixed along the way. -/
theorem cornerBalance_eq_neg_four_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : cornerBalance K a = -4 := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, rfl⟩ := Set.ncard_eq_one.mp h1
      exact singleton_cornerBalance v a
    · obtain ⟨K', hK', hne', a', hlt, hbal⟩ := hcontr K hK hge a
      rw [← hbal]; exact IH K'.ncard hlt K' hK' hne' a' rfl

/-- The four lattice neighbours `(±1, 0)`, `(0, ±1)` of the origin: a set with a one-site hole. -/
noncomputable def bpc_holeRing : Set (Site 2) := {![1, 0], ![0, 1], ![-1, 0], ![0, -1]}

theorem bpc_holeRing_finite : bpc_holeRing.Finite := by
  unfold bpc_holeRing; exact Set.toFinite _

theorem bpc_rot90Fun_mem_holeRing {x : Site 2} (hx : x ∈ bpc_holeRing) :
    rot90Fun x ∈ bpc_holeRing := by
  unfold bpc_holeRing at hx ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem bpc_zero_not_mem_holeRing : (0 : Site 2) ∉ bpc_holeRing := by
  unfold bpc_holeRing
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrFun h 0 <;> have := congrFun h 1 <;>
    simp_all

/-- A dart from a site of `bpc_holeRing` into the hole at the origin. -/
def bpc_HoleDart (e : Dart) : Prop := e.head = 0 ∧ e.tail ∈ bpc_holeRing

theorem bpc_holeDart_front {e : Dart} (he : bpc_HoleDart e) :
    e.head + (-rot90Fun e.dir) ∈ bpc_holeRing := by
  obtain ⟨hh, ht⟩ := he
  have : e.head + (-rot90Fun e.dir) = rot90Fun e.tail := by
    rw [Dart.dir_def, hh, zero_add, zero_sub, rot90Fun_neg, neg_neg]
  rw [this]; exact bpc_rot90Fun_mem_holeRing ht

theorem bpc_holeDart_turnZ {e : Dart} (he : bpc_HoleDart e) : turnZ bpc_holeRing e = 1 := by
  classical
  unfold turnZ; rw [ite_eq_left (bpc_holeDart_front he)]

theorem bpc_holeDart_dartNext {e : Dart} (he : bpc_HoleDart e) :
    bpc_HoleDart (dartNext bpc_holeRing e) := by
  refine ⟨?_, ?_⟩
  · rw [(dartNext_front_head bpc_holeRing e (bpc_holeDart_front he)).1]; exact he.1
  · rw [dartNext_of_front_mem bpc_holeRing e (bpc_holeDart_front he), mkDart_tail]
    exact bpc_holeDart_front he

theorem bpc_holeDart_iterate {e : Dart} (he : bpc_HoleDart e) (k : ℕ) :
    bpc_HoleDart ((dartNext bpc_holeRing)^[k] e) := by
  induction k with
  | zero => exact he
  | succ n ih => rw [Function.iterate_succ_apply']; exact bpc_holeDart_dartNext ih

theorem bpc_holeDart_isBoundaryDart {e : Dart} (he : bpc_HoleDart e) :
    IsBoundaryDart bpc_holeRing e :=
  ⟨he.2, by rw [he.1]; exact bpc_zero_not_mem_holeRing⟩

/-- Every orbit of darts pointing into the hole of `bpc_holeRing` turns the same way at each step,
so its corner balance equals its period. -/
theorem bpc_holeDart_cornerBalance (a : {e : Dart // IsBoundaryDart bpc_holeRing e})
    (ha : bpc_HoleDart a.1) : cornerBalance bpc_holeRing a = dartOrbitPeriod bpc_holeRing a := by
  rw [cornerBalance_eq_totalTurnZ]
  unfold totalTurnZ
  rw [Finset.sum_congr rfl (fun i _ => bpc_holeDart_turnZ (bpc_holeDart_iterate ha i))]
  simp

/-- The dart from `(1, 0)` to the origin, pointing into the hole of `bpc_holeRing`. -/
noncomputable def bpc_holeDart0 : Dart := mkDart ![1, 0] ![-1, 0] unitWt_mx

theorem bpc_holeDart0_hole : bpc_HoleDart bpc_holeDart0 :=
  ⟨by unfold bpc_holeDart0; rw [mkDart_head]; funext i; fin_cases i <;> simp, by
    unfold bpc_holeDart0; rw [mkDart_tail]; unfold bpc_holeRing; simp⟩

/-- The boundary dart `bpc_holeDart0` of `bpc_holeRing`. -/
noncomputable def bpc_holeBase : {e : Dart // IsBoundaryDart bpc_holeRing e} :=
  ⟨bpc_holeDart0, bpc_holeDart_isBoundaryDart bpc_holeDart0_hole⟩

/-- The orbit around the hole of `bpc_holeRing` has positive corner balance (it is `4`, though only
positivity is needed here). -/
theorem bpc_holeRing_cornerBalance : 0 < cornerBalance bpc_holeRing bpc_holeBase := by
  rw [bpc_holeDart_cornerBalance bpc_holeBase bpc_holeDart0_hole]
  exact_mod_cast dartOrbitPeriod_pos bpc_holeRing bpc_holeRing_finite bpc_holeBase

/-- `BalancePreservingContraction` is false: it would force corner balance `-4` on the orbit around
the hole of `bpc_holeRing`, whose corner balance is positive. -/
theorem not_balancePreservingContraction : ¬ BalancePreservingContraction := by
  intro h
  have h1 := cornerBalance_eq_neg_four_of_contraction h bpc_holeRing bpc_holeRing_finite
    ⟨![1, 0], by unfold bpc_holeRing; simp⟩ bpc_holeBase
  have h2 := bpc_holeRing_cornerBalance
  omega

/-- `bpc_BalanceSaturatingContraction` is false, since it implies `BalancePreservingContraction`. -/
theorem not_bpc_BalanceSaturatingContraction : ¬ bpc_BalanceSaturatingContraction :=
  fun h => not_balancePreservingContraction (bpc_balancePreservingContraction_of_saturating h)

end Lattice

end StatMech

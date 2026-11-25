/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Algorithms.Networking.NetworkCalculus
public import Mathlib.Probability.Process.HittingTime

/-!
# FIFO exit time of a traffic link

For cumulative arrival and departure counts on one traffic link, the
vehicle entering at time `t` has FIFO number `N0 + A t`, where `N0`
vehicles are already on the link at time `0`. Its exit time is the
hitting time of that number by the departure count, and equals the
entry time plus the network-calculus virtual delay.

## i. Overview

Time and counts are in `ℝ≥0`. The cumulative counts `A` and `D` are
counted from time `0`, so their intended origins are `A 0 = 0` and
`D 0 = 0`; the statements below assume only the hypotheses they use.
The exit-time value is `MeasureTheory.hittingAfter` for the
deterministic departure curve, the target set `Set.Ici (N0 + A t)`,
and start time `t`. Thus it is the infimum of times at or after entry
whose departure count reaches the FIFO number, or `⊤` if none does.
For right-continuous `D` the infimum is attained; on a plateau it is
the left end. Exit never precedes entry.

This is a single-link model. No origin-destination or path convention,
junction rule, interpolation between discrete steps, equilibrium, or
free-flow travel-time law is asserted. Continuous curves may be
sampled from the discrete inventory at grid times; that bridge is in
the tests. The offset curve `fun s => N0 + A s` is a
`Cslib.Algorithms.Networking.NetworkCalculus.IsCumulativeFlow` only
when `N0 = 0` (and `A` is one), so no network-calculus bound theorem
for cumulative flows is claimed for the offset curve.

For nondecreasing `D` with `D t < N0 + A t`, the exit time agrees
with the count-indexed inverse `inf {s | N0 + A t ≤ D s}`, read in
`WithTop ℝ≥0` with `⊤` for the empty set. The entry-clamped value
differs only when the unclamped infimum would precede entry.

## ii. Key results

- `FluidDynamics.Traffic.ExitTime.linkExitTime_mono`: later entry
  cannot exit earlier when arrivals are nondecreasing.
- `FluidDynamics.Traffic.ExitTime.linkExitTime_ne_top_iff`: finite
  exit exactly when the departure count reaches the FIFO number.
- `FluidDynamics.Traffic.ExitTime.linkExitTime_le_iff`: for
  nondecreasing right-continuous departures, exit by `s ≥ t` exactly
  when `N0 + A t ≤ D s`.
- `FluidDynamics.Traffic.ExitTime.apply_eq_label_of_linkExitTime_eq`:
  for continuous departures and a causal entry, the departure count
  at a finite exit time equals the FIFO number.
- `FluidDynamics.Traffic.ExitTime.linkExitTime_eq_add_delay`: exit
  time is entry time plus network-calculus virtual delay.

## iii. Table of contents

- A. Exit time and FIFO order
- B. Admission and generalized inverse
- C. Network-calculus delay

## iv. References

- J.-Y. Le Boudec and P. Thiran, *Network Calculus*, LNCS 2050,
  Springer (2001), Section 1.1 (virtual delay).
- `Cslib.Algorithms.Networking.NetworkCalculus.delay`.
- `FluidDynamics.Traffic.CumulativeInventory.cumulative_link_inventory`.
- `MeasureTheory.hittingAfter`.

## A. Exit time and FIFO order
-/

@[expose] public section

open scoped NNReal ENNReal

namespace FluidDynamics.Traffic.ExitTime

/-- Exit time of the vehicle that enters the link at time `t`, under first-in-first-out order:
the infimum of the times `≥ t` at which the cumulative departure count `D` reaches the
vehicle's number `N0 + A t`, and `⊤` if there is no such time; for right-continuous `D` this
infimum is attained and is the first such time. It is Mathlib's `MeasureTheory.hittingAfter` of the
deterministic process `D` (sample space `Unit`) into `Set.Ici (N0 + A t)` from the start time
`t`. Here `N0` is the number of vehicles on the link at time `0`, and `A`, `D` are the
cumulative arrival and departure counts from time `0`. -/
noncomputable def linkExitTime (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter (fun s (_ : Unit) => D s) (Set.Ici (N0 + A t)) t ()

/-- **FIFO: no overtaking.** If the cumulative arrival count `A` is nondecreasing, the exit
time `linkExitTime N0 A D t` is nondecreasing in the entry time `t`: a vehicle that enters later
leaves no earlier. This holds for every departure count `D` and every initial count `N0`, as an
order statement in `WithTop ℝ≥0`, so an entry with no finite exit time is followed only by
entries with none. It transports `MeasureTheory.hittingAfter_mono` (a later start time) and
`MeasureTheory.hittingAfter_anti` (a higher vehicle number). -/
theorem linkExitTime_mono (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (hA : Monotone A) :
    Monotone (linkExitTime N0 A D) := by
  intro t₁ t₂ h
  unfold linkExitTime
  have hsub : Set.Ici (N0 + A t₂) ⊆ Set.Ici (N0 + A t₁) :=
    Set.Ici_subset_Ici.mpr (add_le_add_right (hA h) N0)
  exact le_trans (MeasureTheory.hittingAfter_apply_anti _ _ _ hsub)
    (MeasureTheory.hittingAfter_apply_mono _ _ _ h)

/-- **Admission.** For a nondecreasing cumulative departure count `D`, the vehicle that enters
at time `t` has a finite exit time if and only if the departure count reaches its number
`N0 + A t` at some time. Otherwise the vehicle never leaves and its exit time is `⊤`: a missing
finite exit time is reported, not replaced by an arbitrary value. It transports
`MeasureTheory.hittingAfter_eq_top_iff`; monotonicity of `D` removes the restriction to times
after the entry. -/
lemma linkExitTime_ne_top_iff (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (hD : Monotone D) (t : ℝ≥0) :
    linkExitTime N0 A D t ≠ ⊤ ↔ ∃ s, N0 + A t ≤ D s := by
  unfold linkExitTime
  rw [ne_eq, MeasureTheory.hittingAfter_eq_top_iff]
  constructor
  · intro h
    push Not at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, Set.mem_Ici.mp hj2⟩
  · rintro ⟨s, hs⟩ hcon
    have hmax := hcon (max s t) (le_max_right s t)
    exact hmax (Set.mem_Ici.mpr (le_trans hs (hD (le_max_left s t))))

/-! ## B. Admission and generalized inverse -/

/-- **Generalized inverse at plateaus.** Let the cumulative departure count `D` be
nondecreasing and right-continuous (counts over `[0, s]`). For every time `s ≥ t`, the vehicle
that enters at `t` has left by time `s` if and only if `N0 + A t ≤ D s`. So the exit time is the
least `s ≥ t` with `N0 + A t ≤ D s`, and on a departure plateau at the vehicle number it is the
left end of the plateau. Right-continuity makes that least time attained; at a jump of a
left-continuous count the equivalence fails. -/
lemma linkExitTime_le_iff (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (hD : Monotone D)
    (hrc : ∀ s, ContinuousWithinAt D (Set.Ici s) s) {t s : ℝ≥0} (hts : t ≤ s) :
    linkExitTime N0 A D t ≤ s ↔ N0 + A t ≤ D s := by
  constructor
  · intro hle
    unfold linkExitTime at hle
    have hH : ∃ j, t ≤ j ∧ (fun s (_ : Unit) => D s) j () ∈ Set.Ici (N0 + A t) := by
      by_contra hc
      push Not at hc
      have htop : MeasureTheory.hittingAfter (fun s (_ : Unit) => D s) (Set.Ici (N0 + A t)) t () = ⊤ :=
        MeasureTheory.hittingAfter_eq_top_iff.mpr hc
      rw [htop] at hle
      exact absurd (WithTop.top_le_iff.mp hle) WithTop.coe_ne_top
    unfold MeasureTheory.hittingAfter at hle
    rw [ite_eq_left hH] at hle
    have hsInf_le : sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} ≤ s :=
      WithTop.coe_le_coe.mp hle
    by_contra hcon
    push Not at hcon
    have hlb : ∀ i ∈ {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}, s ≤ i := by
      intro i hi
      by_contra hlt
      push Not at hlt
      have hDi : D i ≤ D s := hD hlt.le
      have hcDi : N0 + A t ≤ D i := Set.mem_Ici.mp hi.2
      exact absurd (le_trans hcDi hDi) (not_le_of_gt hcon)
    have hne : {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}.Nonempty := hH
    have hge : s ≤ sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
      le_csInf hne hlb
    have heq : sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} = s :=
      le_antisymm hsInf_le hge
    have hmem : D ⁻¹' (Set.Iio (N0 + A t)) ∈ nhdsWithin s (Set.Ici s) :=
      hrc s (Iio_mem_nhds hcon)
    obtain ⟨u, Hsu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hmem
    have hlt : sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} < u := by
      rw [heq]
      exact Hsu
    have hbdd : BddBelow {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
      ⟨t, fun i hi => hi.1⟩
    rw [csInf_lt_iff hbdd hne] at hlt
    obtain ⟨i, hiH, hiu⟩ := hlt
    have hsi : s ≤ i := hlb i hiH
    have hDilt : D i < N0 + A t := hsub ⟨hsi, hiu⟩
    have hcDi : N0 + A t ≤ D i := Set.mem_Ici.mp hiH.2
    exact absurd hcDi (not_le_of_gt hDilt)
  · intro hle
    unfold linkExitTime
    exact MeasureTheory.hittingAfter_le_of_mem hts (Set.mem_Ici.mpr hle)

/-- **Exactness, `D (τ t) = N0 + A t`.** Let the cumulative departure count `D` be continuous,
and let the link storage at the entry time be nonnegative, `D t ≤ N0 + A t`. If the vehicle
that enters at `t` has the finite exit time `e`, the departure count at `e` equals the vehicle's
number: `D e = N0 + A t`. For a strictly increasing `D` this makes `e` the only time with that
count; on a plateau `e` is the left end fixed by `linkExitTime`, not an arbitrary root. -/
lemma apply_eq_label_of_linkExitTime_eq (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (hc : Continuous D)
    {t e : ℝ≥0} (hcaus : D t ≤ N0 + A t) (he : linkExitTime N0 A D t = e) :
    D e = N0 + A t := by
  unfold linkExitTime at he
  have hH : ∃ j, t ≤ j ∧ (fun s (_ : Unit) => D s) j () ∈ Set.Ici (N0 + A t) := by
    by_contra hc'
    push Not at hc'
    have htop : MeasureTheory.hittingAfter (fun s (_ : Unit) => D s) (Set.Ici (N0 + A t)) t () = ⊤ :=
      MeasureTheory.hittingAfter_eq_top_iff.mpr hc'
    rw [htop] at he
    exact absurd he.symm WithTop.coe_ne_top
  have hsInf : sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} = e := by
    have h2 := he
    unfold MeasureTheory.hittingAfter at h2
    rw [ite_eq_left hH] at h2
    exact WithTop.coe_eq_coe.mp h2
  have hne : {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}.Nonempty := hH
  have hbdd : BddBelow {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
    ⟨t, fun i hi => hi.1⟩
  have hle : N0 + A t ≤ D e := by
    have hmem : e ∈ closure {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} := by
      rw [← hsInf]
      exact csInf_mem_closure hne hbdd
    have himg : D '' closure {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} ⊆
        closure (D '' {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}) :=
      image_closure_subset_closure_image hc
    have hsub : D '' {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} ⊆
        Set.Ici (N0 + A t) := by
      rintro y ⟨i, hi, rfl⟩
      exact hi.2
    have hDmem : D e ∈ closure (D '' {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}) :=
      himg ⟨e, hmem, rfl⟩
    have hclosed : closure (D '' {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)}) ⊆
        Set.Ici (N0 + A t) :=
      closure_minimal hsub isClosed_Ici
    exact Set.mem_Ici.mp (hclosed hDmem)
  have hte : t ≤ e := by
    rw [← hsInf]
    exact le_csInf hne (fun i hi => hi.1)
  rcases eq_or_lt_of_le hte with rfl | hlt
  · exact le_antisymm hcaus hle
  · have hge : D e ≤ N0 + A t := by
      by_contra hcon
      push Not at hcon
      obtain ⟨m, hcm, hme⟩ := exists_between hcon
      have hmem2 : D ⁻¹' (Set.Ioi m) ∈ nhds e := hc.continuousAt (Ioi_mem_nhds hme)
      obtain ⟨l, u, hleu, hsub2⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0, lt_of_le_of_lt (zero_le : (0:ℝ≥0) ≤ t) hlt⟩ (exists_gt e)).mp hmem2
      have hmax : max l t < e := max_lt hleu.1 hlt
      obtain ⟨i, himax, hie⟩ := exists_between hmax
      have hli : l < i := lt_of_le_of_lt (le_max_left l t) himax
      have hiu : i < u := lt_trans hie hleu.2
      have hti : t ≤ i := le_trans (le_max_right l t) himax.le
      have hDi : m < D i := hsub2 ⟨hli, hiu⟩
      have hiH : i ∈ {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
        ⟨hti, Set.mem_Ici.mpr (le_trans hcm.le hDi.le)⟩
      have hle_i : sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} ≤ i :=
        csInf_le hbdd hiH
      rw [hsInf] at hle_i
      exact absurd hle_i (not_le_of_gt hie)
    exact le_antisymm hge hle

private theorem coe_nnreal_sInf {S : Set ℝ≥0} (hne : S.Nonempty) :
    ((sInf S : ℝ≥0) : ℝ≥0∞) = sInf ((fun x : ℝ≥0 => (x : ℝ≥0∞)) '' S) := by
  apply le_antisymm
  · apply le_sInf
    rintro y ⟨x, hx, rfl⟩
    rw [ENNReal.coe_le_coe]
    exact csInf_le ⟨0, fun _ _ => zero_le⟩ hx
  · apply le_of_not_gt
    intro hlt
    obtain ⟨z, haz, hzt⟩ := exists_between hlt
    have hz_top : z ≠ ⊤ := by
      rintro rfl
      exact not_top_lt hzt
    obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.mp hz_top
    have har : sInf S < r := ENNReal.coe_lt_coe.mp haz
    have hrlb : ∀ x ∈ S, r ≤ x := by
      intro x hx
      by_contra hle
      push Not at hle
      have hmem : (↑x : ℝ≥0∞) ∈ (fun x : ℝ≥0 => (↑x : ℝ≥0∞)) '' S := ⟨x, hx, rfl⟩
      have hle2 : sInf ((fun x : ℝ≥0 => (↑x : ℝ≥0∞)) '' S) ≤ ↑x := sInf_le hmem
      have hlt2 : (↑x : ℝ≥0∞) < ↑r := ENNReal.coe_lt_coe.mpr hle
      exact lt_irrefl _ (lt_of_le_of_lt hle2 (lt_trans hlt2 hzt))
    have hra : r ≤ sInf S := le_csInf hne hrlb
    exact absurd hra (not_le_of_gt har)

private theorem delay_eq_coe_sInf (R D : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hne : {τ : ℝ≥0 | R t ≤ D (t + τ)}.Nonempty) :
    Cslib.Algorithms.Networking.NetworkCalculus.delay R D t =
      ((sInf {τ : ℝ≥0 | R t ≤ D (t + τ)} : ℝ≥0) : ℝ≥0∞) := by
  unfold Cslib.Algorithms.Networking.NetworkCalculus.delay
  have hrange : Set.range (fun u : Subtype (fun τ => R t ≤ D (t + τ)) => (↑u.val : ℝ≥0∞)) =
      (fun x : ℝ≥0 => (↑x : ℝ≥0∞)) '' {τ : ℝ≥0 | R t ≤ D (t + τ)} := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h1 : (⨅ u : Subtype (fun τ => R t ≤ D (t + τ)), (↑u.val : ℝ≥0∞)) =
      sInf (Set.range (fun u : Subtype (fun τ => R t ≤ D (t + τ)) => (↑u.val : ℝ≥0∞))) := rfl
  rw [h1, hrange]
  exact (coe_nnreal_sInf hne).symm

private theorem shift_sInf_eq (t : ℝ≥0) (c : ℝ≥0) (D : ℝ≥0 → ℝ≥0)
    (hne : {j : ℝ≥0 | t ≤ j ∧ c ≤ D j}.Nonempty) :
    t + sInf {τ : ℝ≥0 | c ≤ D (t + τ)} = sInf {j : ℝ≥0 | t ≤ j ∧ c ≤ D j} := by
  have himg : {j : ℝ≥0 | t ≤ j ∧ c ≤ D j} = (fun τ => t + τ) '' {τ : ℝ≥0 | c ≤ D (t + τ)} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨htj, hDj⟩
      refine ⟨j - t, ?_, add_tsub_cancel_of_le htj⟩
      rwa [add_tsub_cancel_of_le htj]
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨le_add_right le_rfl, hτ⟩
  have hneS : {τ : ℝ≥0 | c ≤ D (t + τ)}.Nonempty := by
    obtain ⟨j, htj, hDj⟩ := hne
    refine ⟨j - t, ?_⟩
    show c ≤ D (t + (j - t))
    rwa [add_tsub_cancel_of_le htj]
  rw [himg]
  apply le_antisymm
  · apply le_csInf (hneS.image _)
    rintro x ⟨τ, hτ, rfl⟩
    exact add_le_add_right (csInf_le ⟨0, fun _ _ => zero_le⟩ hτ) t
  · apply le_of_not_gt
    intro hlt
    obtain ⟨r, htr, hrs⟩ := exists_between hlt
    have htz : t ≤ r := le_trans (le_add_right le_rfl) htr.le
    have hbdd : BddBelow ((fun τ => t + τ) '' {τ : ℝ≥0 | c ≤ D (t + τ)}) := by
      refine ⟨t, fun x hx => ?_⟩
      obtain ⟨τ, _, rfl⟩ := hx
      exact le_add_right le_rfl
    have hmem : ∀ τ ∈ {τ : ℝ≥0 | c ≤ D (t + τ)}, r - t ≤ τ := by
      intro τ hτ
      by_contra hle
      push Not at hle
      have h1 : t + τ < r := by
        calc t + τ < t + (r - t) := add_lt_add_right hle t
          _ = r := add_tsub_cancel_of_le htz
      have h2 : r < t + τ := lt_of_lt_of_le hrs (csInf_le hbdd ⟨τ, hτ, rfl⟩)
      exact lt_irrefl _ (lt_trans h2 h1)
    have hle3 : r - t ≤ sInf {τ : ℝ≥0 | c ≤ D (t + τ)} := le_csInf hneS hmem
    have hle4 : t + (r - t) ≤ t + sInf {τ : ℝ≥0 | c ≤ D (t + τ)} := add_le_add_right hle3 t
    rw [add_tsub_cancel_of_le htz] at hle4
    exact absurd hle4 (not_le_of_gt htr)

/-! ## C. Network-calculus delay -/

/-- **Physical-to-canonical bridge.** The exit time of the vehicle that enters at `t` equals
the entry time plus the network-calculus virtual delay of the offset arrival count
`fun s => N0 + A s` against the departure count `D`, as an identity in `ℝ≥0∞` with no
hypotheses. Both sides are `⊤` exactly when the departure count never reaches `N0 + A t` at or
after `t`. This is the stated agreement of the two owner declarations,
`MeasureTheory.hittingAfter` and `Cslib.Algorithms.Networking.NetworkCalculus.delay`. -/
theorem linkExitTime_eq_add_delay (N0 : ℝ≥0) (A D : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    (linkExitTime N0 A D t : ℝ≥0∞) =
      (t : ℝ≥0∞) +
        Cslib.Algorithms.Networking.NetworkCalculus.delay (fun s => N0 + A s) D t := by
  by_cases hH : (∃ j, t ≤ j ∧ (fun s (_ : Unit) => D s) j () ∈ Set.Ici (N0 + A t))
  · have hHne : {j : ℝ≥0 | t ≤ j ∧ N0 + A t ≤ D j}.Nonempty := hH
    have hSeq := shift_sInf_eq t (N0 + A t) D hHne
    have hneS : {τ : ℝ≥0 | (fun s => N0 + A s) t ≤ D (t + τ)}.Nonempty := by
      obtain ⟨j, htj, hDj⟩ := hHne
      refine ⟨j - t, ?_⟩
      show N0 + A t ≤ D (t + (j - t))
      rwa [add_tsub_cancel_of_le htj]
    have hdelay : Cslib.Algorithms.Networking.NetworkCalculus.delay (fun s => N0 + A s) D t =
        ((sInf {τ : ℝ≥0 | N0 + A t ≤ D (t + τ)} : ℝ≥0) : ℝ≥0∞) :=
      delay_eq_coe_sInf (fun s => N0 + A s) D t hneS
    have hSets : {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} =
        {j : ℝ≥0 | t ≤ j ∧ N0 + A t ≤ D j} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    have hlink : (linkExitTime N0 A D t : ℝ≥0∞) =
        ((sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} : ℝ≥0) : ℝ≥0∞) := by
      have h0 : linkExitTime N0 A D t =
          ((sInf {i : ℝ≥0 | t ≤ i ∧ (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} : ℝ≥0) :
            WithTop ℝ≥0) := by
        unfold linkExitTime MeasureTheory.hittingAfter
        rw [ite_eq_left hH]
      exact h0
    rw [hlink, hdelay, ← ENNReal.coe_add, hSeq, hSets]
  · have htop : linkExitTime N0 A D t = ⊤ := by
      unfold linkExitTime MeasureTheory.hittingAfter
      rw [ite_eq_right hH]
    have hempty : ∀ u : Subtype (fun τ => (fun s => N0 + A s) t ≤ D (t + τ)), False :=
      fun u => hH ⟨t + u.val, le_add_right le_rfl, Set.mem_Ici.mpr u.property⟩
    have h2 : (⨅ u : Subtype (fun τ => (fun s => N0 + A s) t ≤ D (t + τ)), (↑u.val : ℝ≥0∞)) = ⊤ :=
      le_antisymm le_top (le_iInf fun u => False.elim (hempty u))
    rw [htop]
    unfold Cslib.Algorithms.Networking.NetworkCalculus.delay
    rw [h2]
    exact (add_top _).symm

end FluidDynamics.Traffic.ExitTime

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.SymbolicDynamics.FullShift
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Sequences

/-!
# AMR 43, Problem 1: Hochman aperiodic conjugacy question

The aperiodic parts of the full 2-shift and the proper 3-colouring shift are not conjugate.

Source record `AMR-043-0001__4400001`.
-/

@[expose] public section

namespace MathlibExt.Dynamics.AMR43Problem1Wanted

open SymbolicDynamics.FullShift

/-- **The full 2-shift.** $X$ is the space of all two-sided sequences
$x = (x_i)_{i \in \mathbb{Z}}$ with every $x_i \in \{0, 1\}$, carrying the product topology.

Source: [AMR-043-0001]. -/
abbrev X : Type := FullShiftSpace 2

/-- **The full 3-shift.** The space of all two-sided sequences $y = (y_i)_{i \in \mathbb{Z}}$
with every $y_i \in \{0, 1, 2\}$, carrying the product topology. It is the ambient space of the
proper 3-colouring shift.

Source: [AMR-043-0001]. -/
abbrev YAmb : Type := FullShiftSpace 3

/-- **The proper 3-colouring shift.** $Y$ is the set of sequences $y = (y_i)_{i \in \mathbb{Z}}$
in the full 3-shift (so every $y_i \in \{0, 1, 2\}$) such that $y_i \ne y_{i+1}$ for every
$i \in \mathbb{Z}$.

It is a mixing shift of finite type.

Source: [AMR-043-0001]. -/
def Y : Set YAmb := { y | ∀ i : ℤ, y i ≠ y (i + 1) }

/-- **Aperiodic part of the full 2-shift.** Let $\sigma$ be the left shift on the full 2-shift
$X$, given by $(\sigma x)_i = x_{i+1}$. The aperiodic part of $X$ is the set of all $x \in X$
that are not periodic for $\sigma$, that is, with $\sigma^n x \ne x$ for every $n \ge 1$.

Source: [AMR-043-0001]. -/
def AperiodicX : Set X := (Function.periodicPts (unitShift 2))ᶜ

/-- **Aperiodic part of the 3-colouring shift.** Let $\sigma$ be the left shift on the full
3-shift, given by $(\sigma y)_i = y_{i+1}$. The aperiodic part of the proper 3-colouring shift
$Y$ is the set of all $y \in Y$ that are not periodic for $\sigma$, that is, with
$\sigma^n y \ne y$ for every $n \ge 1$.

Source: [AMR-043-0001]. -/
def AperiodicY : Set YAmb := Y \ Function.periodicPts (unitShift 3)

private theorem unitShift_mem_periodicPts_iff {N : ℕ} (x : FullShiftSpace N) :
    unitShift N x ∈ Function.periodicPts (unitShift N) ↔
      x ∈ Function.periodicPts (unitShift N) := by
  constructor
  · rintro ⟨n, hn, hper⟩
    refine ⟨n, hn, ?_⟩
    apply (shiftHomeomorph N).injective
    change unitShift N ((unitShift N)^[n] x) = unitShift N x
    rw [(Function.Commute.self_iterate (unitShift N) n).eq]
    exact hper
  · rintro ⟨n, hn, hper⟩
    exact ⟨n, hn, hper.apply⟩

/-- **Shift on the aperiodic part of the full 2-shift.** The left shift $\sigma$, given by
$(\sigma x)_i = x_{i+1}$, maps the aperiodic part of the full 2-shift $X$ into itself; this is
the self-map of the aperiodic part of $X$ obtained by restricting $\sigma$ to it.

Source: [AMR-043-0001]. -/
def shiftXRes (a : ↥AperiodicX) : ↥AperiodicX :=
  ⟨unitShift 2 a, by
    exact fun h ↦ a.property
      ((unitShift_mem_periodicPts_iff (N := 2) (a : X)).mp h)⟩

/-- **Shift on the aperiodic part of the 3-colouring shift.** The left shift $\sigma$, given by
$(\sigma y)_i = y_{i+1}$, maps the aperiodic part of the proper 3-colouring shift $Y$ into
itself; this is the self-map of the aperiodic part of $Y$ obtained by restricting $\sigma$
to it.

Source: [AMR-043-0001]. -/
def shiftYRes (a : ↥AperiodicY) : ↥AperiodicY :=
  ⟨unitShift 3 a, by
    have ha : (a : YAmb) ∈ Y ∧ (a : YAmb) ∉ Function.periodicPts (unitShift 3) :=
      a.property
    constructor
    · change ∀ i : ℤ, unitShift 3 (a : YAmb) i ≠ unitShift 3 (a : YAmb) (i + 1)
      intro i
      simpa [unitShift_apply, add_assoc, add_comm, add_left_comm] using ha.1 (1 + i)
    · exact fun h ↦ ha.2
        ((unitShift_mem_periodicPts_iff (N := 3) (a : YAmb)).mp h)⟩

/-- **Hochman's aperiodic conjugacy question.** Let $X$ be the full 2-shift and $Y$ the proper
3-colouring shift, write $X \setminus \mathrm{Per}(X)$ and $Y \setminus \mathrm{Per}(Y)$ for
their aperiodic parts with the subspace topologies, and let $\sigma$ be the left shift
$(\sigma z)_i = z_{i+1}$ on each. The statement is that there is a homeomorphism
$e \colon X \setminus \mathrm{Per}(X) \to Y \setminus \mathrm{Per}(Y)$ with
$e(\sigma a) = \sigma(e(a))$ for every $a \in X \setminus \mathrm{Per}(X)$, that is, the two
aperiodic parts are topologically conjugate.

Source: [AMR-043-0001] Hochman problem 1. -/
def conjecture : Prop :=
  ∃ e : Homeomorph ↥AperiodicX ↥AperiodicY,
    ∀ a : ↥AperiodicX, e (shiftXRes a) = shiftYRes (e a)

open Filter Topology

private theorem unitShift_iterate_apply {N : ℕ} (n : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    (unitShift N)^[n] x i = x ((n : ℤ) + i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, unitShift_apply]
    congr 1
    omega

private theorem periodic_iff_coordinates {N n : ℕ} {x : FullShiftSpace N} :
    Function.IsPeriodicPt (unitShift N) n x ↔ ∀ i : ℤ, x ((n : ℤ) + i) = x i := by
  change (unitShift N)^[n] x = x ↔ _
  rw [funext_iff]
  simp only [unitShift_iterate_apply]

private theorem shiftXRes_iterate_apply (n : ℕ) (x : ↥AperiodicX) (i : ℤ) :
    (shiftXRes^[n] x).val i = x.val ((n : ℤ) + i) := by
  have h : Function.Semiconj Subtype.val shiftXRes (unitShift 2) := fun _ ↦ rfl
  rw [h.iterate_right n x, unitShift_iterate_apply]

private theorem shiftYRes_iterate_apply (n : ℕ) (y : ↥AperiodicY) (i : ℤ) :
    (shiftYRes^[n] y).val i = y.val ((n : ℤ) + i) := by
  have h : Function.Semiconj Subtype.val shiftYRes (unitShift 3) := fun _ ↦ rfl
  rw [h.iterate_right n y, unitShift_iterate_apply]

private theorem conjugacy_iterate_apply (e : ↥AperiodicX ≃ₜ ↥AperiodicY)
    (he : Function.Semiconj e shiftXRes shiftYRes) (n : ℕ) (x : ↥AperiodicX) (i : ℤ) :
    (e (shiftXRes^[n] x)).val i = (e x).val ((n : ℤ) + i) := by
  rw [he.iterate_right n x, shiftYRes_iterate_apply]

/-- The binary configuration with ones at 0 and n. At n = 0 it has a single one. -/
private def marked (n : ℕ) : ↥AperiodicX :=
  ⟨fun i ↦ if i = 0 ∨ i = (n : ℤ) then 1 else 0, by
    intro hp
    obtain ⟨d, hd, hper⟩ := Function.mem_periodicPts.mp hp
    have h := periodic_iff_coordinates.mp hper (n : ℤ)
    have h₀ : (d : ℤ) + n ≠ 0 := by omega
    have h₁ : (d : ℤ) + n ≠ n := by omega
    simp [h₀, h₁] at h⟩

private theorem tendsto_iff_eventually_coordinate {N : ℕ} {l : Filter ℕ}
    {f : ℕ → FullShiftSpace N} {p : FullShiftSpace N} :
    Tendsto f l (𝓝 p) ↔ ∀ i : ℤ, ∀ᶠ n in l, f n i = p i := by
  rw [tendsto_pi_nhds]
  simp only [nhds_discrete (Fin N), tendsto_pure]

private theorem eventually_agrees_on_interval {N : ℕ} {f : ℕ → FullShiftSpace N}
    {p : FullShiftSpace N} (h : Tendsto f atTop (𝓝 p)) (a b : ℤ) :
    ∀ᶠ n in atTop, ∀ i : ℤ, a ≤ i → i < b → f n i = p i := by
  have hw := (eventually_all_finset (Finset.Ico a b)).mpr
    (fun i _ ↦ tendsto_iff_eventually_coordinate.mp h i)
  filter_upwards [hw] with n hn i hi hj
  exact hn i (Finset.mem_Ico.mpr ⟨hi, hj⟩)

private theorem limit_mem_Y {f : ℕ → YAmb} {p : YAmb} (h : Tendsto f atTop (𝓝 p))
    (hf : ∀ n, f n ∈ Y) : p ∈ Y := by
  intro i
  have h₀ := tendsto_iff_eventually_coordinate.mp h i
  have h₁ := tendsto_iff_eventually_coordinate.mp h (i + 1)
  obtain ⟨n, hn₀, hn₁⟩ := (h₀.and h₁).exists
  rw [← hn₀, ← hn₁]
  exact hf n i

private theorem periodic_of_zero_limit (e : ↥AperiodicX ≃ₜ ↥AperiodicY)
    (f : ℕ → ↥AperiodicX) {p : YAmb}
    (hf : Tendsto (fun n ↦ (f n).val) atTop (𝓝 (fun _ ↦ 0)))
    (he : Tendsto (fun n ↦ (e (f n)).val) atTop (𝓝 p)) :
    p ∈ Function.periodicPts (unitShift 3) := by
  by_contra hp
  let y : ↥AperiodicY := ⟨p, limit_mem_Y he (fun n ↦ (e (f n)).property.1), hp⟩
  have hy : Tendsto (fun n ↦ e (f n)) atTop (𝓝 y) := tendsto_subtype_rng.mpr he
  have h := ((continuous_subtype_val.comp e.symm.continuous).tendsto y).comp hy
  have hx : Tendsto (fun n ↦ (f n).val) atTop (𝓝 (e.symm y).val) := by
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h
  have hz := tendsto_nhds_unique hx hf
  apply (e.symm y).property
  rw [hz]
  exact Function.mk_mem_periodicPts Nat.one_pos (by rfl)

/-- Near a long zero block, an image following a periodic pattern cannot depart at its centre. -/
private theorem exists_continuation_radius (e : ↥AperiodicX ≃ₜ ↥AperiodicY)
    {d : ℕ} (hd : 0 < d) :
    ∃ R : ℕ, ∀ (x : ↥AperiodicX) (q : YAmb),
      Function.IsPeriodicPt (unitShift 3) d q →
      (∀ i : ℤ, -(R : ℤ) ≤ i → i ≤ R → x.val i = 0) →
      (∀ i : ℤ, -(R : ℤ) ≤ i → i < 0 → (e x).val i = q i) →
      (e x).val 0 = q 0 := by
  classical
  by_contra! h
  choose x q hq hzero hagree hdiff using h
  obtain ⟨⟨y, p⟩, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq (fun n ↦ ((e (x n)).val, q n))
  have hy : Tendsto (fun n ↦ (e (x (φ n))).val) atTop (𝓝 y) :=
    (continuous_fst.tendsto (y, p)).comp hlim
  have hp : Tendsto (fun n ↦ q (φ n)) atTop (𝓝 p) :=
    (continuous_snd.tendsto (y, p)).comp hlim
  have hx : Tendsto (fun n ↦ (x (φ n)).val) atTop (𝓝 (fun _ ↦ 0)) := by
    apply tendsto_iff_eventually_coordinate.mpr
    intro i
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop i.natAbs] with n hn
    exact hzero (φ n) i (by omega) (by omega)
  obtain ⟨m, hm, hym⟩ := Function.mem_periodicPts.mp
    (periodic_of_zero_limit e (fun n ↦ x (φ n)) hx hy)
  have hpd : Function.IsPeriodicPt (unitShift 3) d p := by
    apply periodic_iff_coordinates.mpr
    intro i
    have h₁ := tendsto_iff_eventually_coordinate.mp hp ((d : ℤ) + i)
    have h₂ := tendsto_iff_eventually_coordinate.mp hp i
    obtain ⟨n, hn₁, hn₂⟩ := (h₁.and h₂).exists
    rw [← hn₁, ← hn₂]
    exact periodic_iff_coordinates.mp (hq (φ n)) i
  have hleft (i : ℤ) (hi : i < 0) : y i = p i := by
    have h₁ := tendsto_iff_eventually_coordinate.mp hy i
    have h₂ := tendsto_iff_eventually_coordinate.mp hp i
    obtain ⟨n, hn₁, hn₂, hn⟩ :=
      (h₁.and (h₂.and (hφ.tendsto_atTop.eventually_ge_atTop i.natAbs))).exists
    rw [← hn₁, ← hn₂]
    exact hagree (φ n) i (by omega) hi
  have hne : y 0 ≠ p 0 := by
    obtain ⟨n, hn₁, hn₂⟩ := ((tendsto_iff_eventually_coordinate.mp hy 0).and
      (tendsto_iff_eventually_coordinate.mp hp 0)).exists
    rw [← hn₁, ← hn₂]
    exact hdiff (φ n)
  -- Two periodic configurations agreeing on a left half-line agree at the origin.
  let i : ℤ := -((m * d : ℕ) : ℤ)
  have hi : i < 0 := by
    have hmd := Nat.mul_pos hm hd
    omega
  have hyi := periodic_iff_coordinates.mp (hym.mul_const d) i
  have hpi := periodic_iff_coordinates.mp (hpd.const_mul m) i
  dsimp only [i] at hyi hpi
  rw [add_neg_cancel] at hyi hpi
  exact hne (hyi.trans ((hleft i hi).trans hpi.symm))

private theorem shifted_single_mark_tendsto :
    Tendsto (fun n : ℕ ↦ (shiftXRes^[n] (marked 0)).val) atTop (𝓝 (fun _ ↦ 0)) := by
  apply tendsto_iff_eventually_coordinate.mpr
  intro i
  filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with n hn
  have hi : (n : ℤ) + i ≠ 0 := by omega
  simp [shiftXRes_iterate_apply, marked, hi]

private theorem marked_tendsto :
    Tendsto marked atTop (𝓝 (marked 0)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_eventually_coordinate.mpr
  intro i
  filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with n hn
  have hi : i ≠ (n : ℤ) := by omega
  simp [marked, hi]

private theorem recentered_marks_tendsto :
    Tendsto (fun n : ℕ ↦ shiftXRes^[n] (marked n)) atTop (𝓝 (marked 0)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_eventually_coordinate.mpr
  intro i
  filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with n hn
  have hi : (n : ℤ) + i ≠ 0 := by omega
  simp [shiftXRes_iterate_apply, marked, hi]

/--
**The aperiodic parts of the full 2-shift and the 3-colouring shift are not conjugate.**
Let $X$ be the full 2-shift, $Y$ the proper 3-colouring shift, and $\sigma$ the left shift on
each. There is no homeomorphism $e$ from the aperiodic part of $X$ onto the aperiodic part of
$Y$, each with the subspace topology, such that $e(\sigma a) = \sigma(e(a))$ for every $a$ in the
aperiodic part of $X$; that is, Hochman's aperiodic conjugacy question has a negative answer.

Salo proves that every conjugacy between infinite transitive shifts of finite type minus
periodic points extends to a conjugacy of the shifts of finite type; since the full 2-shift
has fixed points and the proper 3-colouring shift has none, the aperiodic parts are not
conjugate.

Source: Ville Salo, Conjugacy of transitive SFTs minus
periodic points, Proc. London Math. Soc. (accepted; arXiv v3 2023), arXiv:2104.09860,
https://arxiv.org/abs/2104.09860. Moved from `OpenConjectures/Dynamics/AMR43Problem1`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  rintro ⟨e, he⟩
  have hcomm : Function.Semiconj e shiftXRes shiftYRes := he
  -- Images of shifts of the single mark have a periodic limit.
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq
    (fun n : ℕ ↦ (e (shiftXRes^[n] (marked 0))).val)
  have hpY := limit_mem_Y hp (fun n ↦ (e (shiftXRes^[φ n] (marked 0))).property.1)
  obtain ⟨d, hd, hper⟩ := Function.mem_periodicPts.mp (periodic_of_zero_limit e
    (fun n ↦ shiftXRes^[φ n] (marked 0)) (shifted_single_mark_tendsto.comp hφ.tendsto_atTop) hp)
  obtain ⟨R, hstep⟩ := exists_continuation_radius e hd
  obtain ⟨k, hk, hseed⟩ := ((hφ.tendsto_atTop.eventually_ge_atTop (R + 1)).and
    (eventually_agrees_on_interval hp (-(R : ℤ)) 0)).exists
  let s := φ k
  have hs : R < s := hk
  let q : YAmb := fun i ↦ p (i - s)
  have hqY : q ∈ Y := by
    intro i
    simpa only [q, add_right_comm i 1 (- (s : ℤ)), sub_eq_add_neg] using hpY (i - s)
  have hqper (i : ℤ) : q ((d : ℤ) + i) = q i := by
    simpa only [q, add_sub_assoc] using periodic_iff_coordinates.mp hper (i - s)
  have hsingle (i : ℤ) (hlo : (s : ℤ) - R ≤ i) (hhi : i < s) :
      (e (marked 0)).val i = q i := by
    have h := hseed (i - s) (by omega) (by omega)
    change (e (shiftXRes^[s] (marked 0))).val (i - s) = q i at h
    rwa [conjugacy_iterate_apply e hcomm, add_sub_cancel] at h
  -- Both marked configurations, viewed from either mark, converge to the single mark.
  let K := R + 1
  have hcont := continuous_subtype_val.comp e.continuous
  have hnear := (hcont.tendsto (marked 0)).comp marked_tendsto
  have hfar := (hcont.tendsto (marked 0)).comp recentered_marks_tendsto
  have hstart := eventually_agrees_on_interval hnear ((s : ℤ) - R) s
  have hend := tendsto_iff_eventually_coordinate.mp hfar (-(K : ℤ))
  have hagrees : ∀ᶠ n : ℕ in atTop, q ((n : ℤ) - K) = (e (marked 0)).val (-(K : ℤ)) := by
    filter_upwards [eventually_ge_atTop (s + K), hstart, hend] with n hn hstart hend
    -- Continue the pattern through the gap, stopping K positions before the second mark.
    have hgap (j : ℕ) (hj : s ≤ j) (hj' : j ≤ n - K + 1) :
        ∀ i : ℤ, (s : ℤ) - R ≤ i → i < (j : ℤ) → (e (marked n)).val i = q i := by
      induction j, hj using Nat.le_induction with
      | base =>
        intro i hlo hhi
        exact (hstart i hlo hhi).trans (hsingle i hlo hhi)
      | succ j hsj ih =>
        intro i hlo hhi
        by_cases hi : i < (j : ℤ)
        · exact ih (by omega) i hlo hi
        have hij : i = (j : ℤ) := by omega
        subst i
        let x := shiftXRes^[j] (marked n)
        let r : YAmb := fun i ↦ q ((j : ℤ) + i)
        have hr : Function.IsPeriodicPt (unitShift 3) d r := by
          apply periodic_iff_coordinates.mpr
          intro i
          simpa only [r, add_left_comm (j : ℤ) (d : ℤ) i] using
            hqper ((j : ℤ) + i)
        have hzero (i : ℤ) (ha : -(R : ℤ) ≤ i) (hb : i ≤ R) : x.val i = 0 := by
          have h₀ : (j : ℤ) + i ≠ 0 := by omega
          have h₁ : (j : ℤ) + i ≠ n := by omega
          simp [x, shiftXRes_iterate_apply, marked, h₀, h₁]
        have hl (i : ℤ) (ha : -(R : ℤ) ≤ i) (hb : i < 0) : (e x).val i = r i := by
          rw [conjugacy_iterate_apply e hcomm]
          exact ih (by omega) _ (by omega) (by omega)
        simpa only [x, r, conjugacy_iterate_apply e hcomm, add_zero] using hstep x r hr hzero hl
    have hlast := hgap (n - K + 1) (by omega) le_rfl ((n : ℤ) - K) (by omega) (by omega)
    change (e (shiftXRes^[n] (marked n))).val (-(K : ℤ)) = _ at hend
    rw [conjugacy_iterate_apply e hcomm] at hend
    exact hlast.symm.trans hend
  -- Consecutive distances between the marks force consecutive colours to agree.
  obtain ⟨m, hm⟩ := eventually_atTop.mp hagrees
  have h₀ := hm m le_rfl
  have h₁ := hm (m + 1) (Nat.le_succ m)
  apply hqY ((m : ℤ) - K)
  rw [show (m : ℤ) - K + 1 = ((m + 1 : ℕ) : ℤ) - K by omega]
  exact h₀.trans h₁.symm

end MathlibExt.Dynamics.AMR43Problem1Wanted

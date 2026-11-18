/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonnegativity of classical scalar parabolic solutions

For a classical solution of `c_t - D * c_xx + k * c = s` on the closed
cylinder `[0, T] × [0, L]`, with `D > 0`, nonnegative reaction and source
fields, and nonnegative initial and Dirichlet boundary data, the solution
is nonnegative on the whole cylinder, including the initial and boundary
faces. The statement is conditional on the displayed derivative data; it
is a comparison theorem for a given classical solution, not an existence
claim.

## Key results

- `parabolic_solution_nonneg`: the nonnegative-data comparison theorem.

The proof is the compact negative-minimum argument: if a negative value
occurred, perturbing by `ε * (t + 1)` would force a strictly negative
minimum at an interior spatial point and a positive time, where the
Fermat conditions and the equation contradict the sign of the source.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.ScalarParabolicComparison

private theorem hasDerivAt_add {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x := by
  apply HasDerivAt.of_isLittleO
  have h := hf.isLittleO.add hg.isLittleO
  have hfun : (fun x' : ℝ => (f x' + g x') - (f x + g x) - (x' - x) • (f' + g')) =
      (fun x' : ℝ => (f x' - f x - (x' - x) • f') + (g x' - g x - (x' - x) • g')) := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  exact h

private theorem hasDerivAt_sub {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - g y) (f' - g') x := by
  apply HasDerivAt.of_isLittleO
  have h := hf.isLittleO.sub hg.isLittleO
  have hfun : (fun x' : ℝ => (f x' - g x') - (f x - g x) - (x' - x) • (f' - g')) =
      (fun x' : ℝ => (f x' - f x - (x' - x) • f') - (g x' - g x - (x' - x) • g')) := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  exact h

private theorem hasDerivAt_const_mul {f : ℝ → ℝ} {f' x C : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => C * f y) (C * f') x := by
  apply HasDerivAt.of_isLittleO
  have h := hf.isLittleO.const_mul_left C
  have hfun : (fun x' : ℝ => C * f x' - C * f x - (x' - x) • (C * f')) =
      (fun x' : ℝ => C * (f x' - f x - (x' - x) • f')) := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  exact h

private theorem hasDerivAt_neg {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => -f y) (-f') x := by
  apply HasDerivAt.of_isLittleO
  have h := hf.isLittleO.const_mul_left (-1)
  have hfun : (fun x' : ℝ => -f x' - -f x - (x' - x) • (-f')) =
      (fun x' : ℝ => (-1) * (f x' - f x - (x' - x) • f')) := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  exact h

private theorem hasDerivAt_add_const {f : ℝ → ℝ} {f' x C : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => f y + C) f' x := by
  have h := hasDerivAt_add hf (hasDerivAt_const x C)
  simpa using h

private theorem hasDerivAt_affine {a b x : ℝ} :
    HasDerivAt (fun y => a * y + b) a x := by
  apply HasDerivAt.of_isLittleO
  have hfun : (fun x' : ℝ => (a * x' + b) - (a * x + b) - (x' - x) • a) =
      fun _ => 0 := by
    funext y
    simp only [smul_eq_mul]
    ring
  rw [hfun]
  exact Asymptotics.isLittleO_zero _ _

private theorem isMinOn_hasDerivAt_le_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhdsWithin x (Set.Iio x)) :
    f' ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hc : 0 < f' / 2 := by linarith
  have hlit : (fun x' : ℝ => f x' - f x - (x' - x) • f') =o[nhdsWithin x (Set.Iio x)]
      fun x' => x' - x :=
    hf.isLittleO.mono nhdsWithin_le_nhds
  have hbound := hlit.bound hc
  have hIio : ∀ᶠ y in nhdsWithin x (Set.Iio x), y ∈ Set.Iio x :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
  have hs : ∀ᶠ y in nhdsWithin x (Set.Iio x), y ∈ s :=
    Filter.eventually_of_mem hmem (fun y hy => hy)
  obtain ⟨y, hby, hylt, hys⟩ := (hbound.and (hIio.and hs)).exists
  have hlt : y < x := hylt
  have hfx : f x ≤ f y := hmin hys
  have hyx : y - x < 0 := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul] at hby
  have habs : |y - x| = -(y - x) := abs_of_neg hyx
  rw [habs] at hby
  have hkey : f y - f x - (y - x) * f' ≤ (f' / 2) * (-(y - x)) := (abs_le.mp hby).2
  have hring : (f' / 2) * (-(y - x)) + (y - x) * f' = (f' / 2) * (y - x) := by ring
  have hle2 : f y - f x ≤ (f' / 2) * (y - x) := by linarith
  have hneg : (f' / 2) * (y - x) < 0 := mul_neg_of_pos_of_neg (by linarith) hyx
  have hlt2 : f y - f x < 0 := lt_of_le_of_lt hle2 hneg
  have hylt2 : f y < f x := by linarith
  exact (not_lt_of_ge hfx) hylt2

private theorem isMinOn_hasDerivAt_nonneg {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhdsWithin x (Set.Ioi x)) :
    0 ≤ f' := by
  by_contra hpos
  push Not at hpos
  have hc : 0 < -f' / 2 := by linarith
  have hlit : (fun x' : ℝ => f x' - f x - (x' - x) • f') =o[nhdsWithin x (Set.Ioi x)]
      fun x' => x' - x :=
    hf.isLittleO.mono nhdsWithin_le_nhds
  have hbound := hlit.bound hc
  have hIoi : ∀ᶠ y in nhdsWithin x (Set.Ioi x), y ∈ Set.Ioi x :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
  have hs : ∀ᶠ y in nhdsWithin x (Set.Ioi x), y ∈ s :=
    Filter.eventually_of_mem hmem (fun y hy => hy)
  obtain ⟨y, hby, hylt, hys⟩ := (hbound.and (hIoi.and hs)).exists
  have hlt : x < y := hylt
  have hfx : f x ≤ f y := hmin hys
  have hyx : 0 < y - x := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul] at hby
  have habs : |y - x| = (y - x) := abs_of_pos hyx
  rw [habs] at hby
  have hkey : f y - f x - (y - x) * f' ≤ (-f' / 2) * (y - x) := (abs_le.mp hby).2
  have hring : (-f' / 2) * (y - x) + (y - x) * f' = (f' / 2) * (y - x) := by ring
  have hle2 : f y - f x ≤ (f' / 2) * (y - x) := by linarith
  have hneg : (f' / 2) * (y - x) < 0 := mul_neg_of_neg_of_pos (by linarith) hyx
  have hlt2 : f y - f x < 0 := lt_of_le_of_lt hle2 hneg
  have hylt2 : f y < f x := by linarith
  exact (not_lt_of_ge hfx) hylt2

private theorem isMinOn_hasDerivAt_eq_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmin : IsMinOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 := by
  apply le_antisymm
  · exact isMinOn_hasDerivAt_le_zero hf hmin (mem_nhdsWithin_of_mem_nhds hmem)
  · exact isMinOn_hasDerivAt_nonneg hf hmin (mem_nhdsWithin_of_mem_nhds hmem)

private theorem isMaxOn_hasDerivAt_eq_zero {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    {s : Set ℝ} (hmax : IsMaxOn f s x) (hmem : s ∈ nhds x) :
    f' = 0 := by
  have hmin : IsMinOn (fun y => -f y) s x :=
    Filter.eventually_principal.mpr (fun y hy => by
      have h : f y ≤ f x := hmax hy
      change -f x ≤ -f y
      linarith)
  have h0 : -f' = 0 :=
    isMinOn_hasDerivAt_eq_zero (hasDerivAt_neg hf) hmin hmem
  linarith

private theorem rolle_eq_zero {f : ℝ → ℝ} {f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (heq : f a = f b) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_refl a, hab.le⟩
  obtain ⟨m, hms, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  obtain ⟨M, hMs, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  by_cases heqMM : f m = f M
  · have hconst : ∀ y ∈ Set.Icc a b, f y = f m := by
      intro y hy
      apply le_antisymm
      · have h1 : f y ≤ f M := hmax hy
        rw [← heqMM] at h1
        exact h1
      · exact hmin hy
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
      change a < (a + b) / 2 ∧ (a + b) / 2 < b
      constructor <;> linarith
    refine ⟨(a + b) / 2, hmid, ?_⟩
    have hmid' : a < (a + b) / 2 ∧ (a + b) / 2 < b := hmid
    have hIoo_mem : Set.Ioo a b ∈ nhds ((a + b) / 2) :=
      Ioo_mem_nhds hmid'.1 hmid'.2
    have hev : ∀ᶠ y in nhds ((a + b) / 2), (fun _ => f m) y = f y :=
      Filter.eventually_of_mem hIoo_mem (fun y hy => by
        have hyIcc : y ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hy
        change f m = f y
        exact (hconst y hyIcc).symm)
    have hfc : HasDerivAt (fun _ => f m) (f' ((a + b) / 2)) ((a + b) / 2) :=
      HasDerivAt.congr_of_eventuallyEq (hderiv _ hmid) hev
    have hcz : HasDerivAt (fun _ => f m) 0 ((a + b) / 2) :=
      hasDerivAt_const _ _
    exact hfc.unique hcz
  · have haIcc : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
    have hbIcc : b ∈ Set.Icc a b := ⟨hab.le, le_refl b⟩
    have hma : f m ≤ f a := hmin haIcc
    have hMb : f b ≤ f M := hmax hbIcc
    by_cases hlt1 : f m < f a
    · have hmIoo : m ∈ Set.Ioo a b := by
        have hms' : a ≤ m ∧ m ≤ b := hms
        have hne_a : m ≠ a := by
          intro hcon
          rw [hcon] at hlt1
          exact (lt_irrefl _ hlt1)
        have hne_b : m ≠ b := by
          intro hcon
          rw [hcon] at hlt1
          rw [heq] at hlt1
          exact (lt_irrefl _ hlt1)
        change a < m ∧ m < b
        exact ⟨lt_of_le_of_ne hms'.1 (Ne.symm hne_a), lt_of_le_of_ne hms'.2 hne_b⟩
      have hmIoo' : a < m ∧ m < b := hmIoo
      have hmem : Set.Icc a b ∈ nhds m := by
        have hIoo : Set.Ioo a b ∈ nhds m := Ioo_mem_nhds hmIoo'.1 hmIoo'.2
        exact Filter.mem_of_superset hIoo Set.Ioo_subset_Icc_self
      exact ⟨m, hmIoo, isMinOn_hasDerivAt_eq_zero (hderiv m hmIoo) hmin hmem⟩
    · push Not at hlt1
      have hmeq : f m = f a := le_antisymm hma hlt1
      have h1 : f a ≤ f M := by
        have h := hMb
        rw [← heq] at h
        exact h
      have hne2 : f a ≠ f M := fun hcon => heqMM (hmeq.trans hcon)
      have hlt2 : f a < f M := lt_of_le_of_ne h1 hne2
      have hMIoo : M ∈ Set.Ioo a b := by
        have hMs' : a ≤ M ∧ M ≤ b := hMs
        have hne_a : M ≠ a := by
          intro hcon
          rw [hcon] at hlt2
          exact (lt_irrefl _ hlt2)
        have hne_b : M ≠ b := by
          intro hcon
          rw [hcon] at hlt2
          rw [heq] at hlt2
          exact (lt_irrefl _ hlt2)
        change a < M ∧ M < b
        exact ⟨lt_of_le_of_ne hMs'.1 (Ne.symm hne_a), lt_of_le_of_ne hMs'.2 hne_b⟩
      have hMIoo' : a < M ∧ M < b := hMIoo
      have hmem : Set.Icc a b ∈ nhds M := by
        have hIoo : Set.Ioo a b ∈ nhds M := Ioo_mem_nhds hMIoo'.1 hMIoo'.2
        exact Filter.mem_of_superset hIoo Set.Ioo_subset_Icc_self
      exact ⟨M, hMIoo, isMaxOn_hasDerivAt_eq_zero (hderiv M hMIoo) hmax hmem⟩

private theorem mvt_slope {f : ℝ → ℝ} {f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y) :
    ∃ c ∈ Set.Ioo a b, f b - f a = f' c * (b - a) := by
  have hg_deriv : ∀ y ∈ Set.Icc a b,
      HasDerivAt (fun y => (b - a) * f y - (f b - f a) * y)
        ((b - a) * f' y - (f b - f a)) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => (b - a) * f y) ((b - a) * f' y) y :=
      hasDerivAt_const_mul (hderiv y hy)
    have h2 : HasDerivAt (fun y => (f b - f a) * y) (f b - f a) y := by
      have h := hasDerivAt_const_mul (C := (f b - f a)) (hasDerivAt_id' y)
      simpa using h
    exact hasDerivAt_sub h1 h2
  have hg_cont : ContinuousOn (fun y => (b - a) * f y - (f b - f a) * y)
      (Set.Icc a b) :=
    HasDerivAt.continuousOn (fun y hy => hg_deriv y hy)
  have heqg : (fun y => (b - a) * f y - (f b - f a) * y) a =
      (fun y => (b - a) * f y - (f b - f a) * y) b := by
    change (b - a) * f a - (f b - f a) * a = (b - a) * f b - (f b - f a) * b
    ring
  obtain ⟨c, hcIoo, hc0⟩ := rolle_eq_zero hab hg_cont
    (fun y hy => hg_deriv y (Set.Ioo_subset_Icc_self hy)) heqg
  have hc0' : (b - a) * f' c - (f b - f a) = 0 := hc0
  refine ⟨c, hcIoo, ?_⟩
  have hcomm : (b - a) * f' c = f' c * (b - a) := mul_comm _ _
  linarith

private theorem second_deriv_nonneg_of_isMinOn {f g gd : ℝ → ℝ} {x0 a b : ℝ}
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (g y) y)
    (hg : ∀ y ∈ Set.Icc a b, HasDerivAt g (gd y) y)
    (hx0 : x0 ∈ Set.Ioo a b)
    (hmin : IsMinOn f (Set.Icc a b) x0) :
    0 ≤ gd x0 := by
  by_contra hneg
  push Not at hneg
  have hx0' : a < x0 ∧ x0 < b := hx0
  have hx0Icc : x0 ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx0
  have hIcc_mem : Set.Icc a b ∈ nhds x0 :=
    Filter.mem_of_superset (Ioo_mem_nhds hx0'.1 hx0'.2) Set.Ioo_subset_Icc_self
  have hgx0 : g x0 = 0 :=
    isMinOn_hasDerivAt_eq_zero (hf x0 hx0Icc) hmin hIcc_mem
  have hc : 0 < -gd x0 / 2 := by linarith
  have hbound1 : ∀ᶠ y in nhds x0,
      ‖g y - g x0 - (y - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖y - x0‖ :=
    (hg x0 hx0Icc).isLittleO.bound hc
  have hset : {y : ℝ | ‖g y - g x0 - (y - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖y - x0‖} ∈
      nhds x0 :=
    hbound1
  obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hset
  have hxu' : l < x0 ∧ x0 < u := hxu
  set y1 : ℝ := max ((l + x0) / 2) ((a + x0) / 2) with hy1
  have h1 : (l + x0) / 2 < x0 := by linarith
  have h2 : (a + x0) / 2 < x0 := by linarith
  have hy1_lt : y1 < x0 := max_lt_iff.mpr ⟨h1, h2⟩
  have hy1_ge1 : (l + x0) / 2 ≤ y1 := le_max_left _ _
  have hy1_ge2 : (a + x0) / 2 ≤ y1 := le_max_right _ _
  have hy1_gt_a : a < y1 := by
    have hmid_a : a < (a + x0) / 2 := by linarith
    exact lt_of_lt_of_le hmid_a hy1_ge2
  have hsub_Icc : Set.Icc y1 x0 ⊆ Set.Icc a b := by
    intro y hy
    have hy' : y1 ≤ y ∧ y ≤ x0 := hy
    change a ≤ y ∧ y ≤ b
    exact ⟨le_trans hy1_gt_a.le hy'.1, le_trans hy'.2 hx0'.2.le⟩
  have hf_sub : ∀ y ∈ Set.Icc y1 x0, HasDerivAt f (g y) y := by
    intro y hy
    exact hf y (hsub_Icc hy)
  obtain ⟨c, hcIoo, hslope⟩ := mvt_slope hy1_lt hf_sub
  have hslope' : f x0 - f y1 = g c * (x0 - y1) := hslope
  have hc' : y1 < c ∧ c < x0 := hcIoo
  have hc_gt_l : l < c := by
    have h1' : l < (l + x0) / 2 := by linarith
    linarith
  have hc_lt_u : c < u := lt_trans hc'.2 hxu'.2
  have hc_mem : c ∈ Set.Ioo l u := ⟨hc_gt_l, hc_lt_u⟩
  have hbound_c : ‖g c - g x0 - (c - x0) • gd x0‖ ≤ (-gd x0 / 2) * ‖c - x0‖ :=
    hsub hc_mem
  have hcx0 : c - x0 < 0 := by linarith
  have h : |g c - g x0 - (c - x0) * gd x0| ≤ -gd x0 / 2 * |c - x0| := by
    have h := hbound_c
    simp only [Real.norm_eq_abs, smul_eq_mul] at h
    exact h
  have habs : |c - x0| = -(c - x0) := abs_of_neg hcx0
  rw [habs, hgx0] at h
  have hlow : -(-gd x0 / 2 * -(c - x0)) ≤ g c - 0 - (c - x0) * gd x0 :=
    (abs_le.mp h).1
  have hring : -(-gd x0 / 2 * -(c - x0)) + (c - x0) * gd x0 =
      (gd x0 / 2) * (c - x0) := by ring
  have hpos : 0 < (gd x0 / 2) * (c - x0) :=
    mul_pos_of_neg_of_neg (by linarith) hcx0
  have hgc_eq : g c = (g c - 0 - (c - x0) * gd x0) + (c - x0) * gd x0 := by ring
  have hgc_pos : 0 < g c := by linarith
  have hy1c : 0 < x0 - y1 := by linarith
  have hprod : 0 < g c * (x0 - y1) := mul_pos hgc_pos hy1c
  have hfx0 : f x0 ≤ f y1 := by
    have hy1_mem : y1 ∈ Set.Icc a b := by
      change a ≤ y1 ∧ y1 ≤ b
      exact ⟨hy1_gt_a.le, le_trans hy1_lt.le hx0'.2.le⟩
    exact hmin hy1_mem
  linarith

/-- Nonnegativity for a classical scalar parabolic solution: let
`c` solve `c_t - D * c_xx + k * c = s` on the closed cylinder
`[0, T] × [0, L]` in the sense that its time derivative `ct`,
first and second spatial derivatives `cx`, `cxx` are given
functions related by the displayed `HasDerivAt` data, with
`D > 0`, `k ≥ 0`, `s ≥ 0` pointwise on the cylinder, nonnegative
initial data `c 0 x ≥ 0` on `[0, L]`, and nonnegative Dirichlet
data `c t 0 ≥ 0`, `c t L ≥ 0` on `[0, T]`. Then `c t x ≥ 0` on the
whole cylinder. This is a comparison theorem for a given
classical solution, not an existence claim. The proof is the
compact negative-minimum argument applied to
`c + ε * (t + 1)`, then `ε → 0`. -/
theorem parabolic_solution_nonneg {D L T : ℝ} (hD : 0 < D)
    (hL : 0 < L) (hT : 0 < T)
    {c ct cx cxx k s : ℝ → ℝ → ℝ}
    (hct : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun τ : ℝ => c τ x) (ct t x) t)
    (hcx : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun y : ℝ => c t y) (cx t x) x)
    (hcxx : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      HasDerivAt (fun y : ℝ => cx t y) (cxx t x) x)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.Icc 0 L))
    (hPDE : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      ct t x - D * cxx t x + k t x * c t x = s t x)
    (hk : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L → 0 ≤ k t x)
    (hs : ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L → 0 ≤ s t x)
    (hinit : ∀ x : ℝ, x ∈ Set.Icc 0 L → 0 ≤ c 0 x)
    (hb0 : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t 0)
    (hbL : ∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ c t L)
    {t x : ℝ} (ht : t ∈ Set.Icc 0 T) (hx : x ∈ Set.Icc 0 L) :
    0 ≤ c t x := by
  have key : ∀ eps : ℝ, 0 < eps → ∀ t x : ℝ, t ∈ Set.Icc 0 T → x ∈ Set.Icc 0 L →
      0 ≤ c t x + (eps * t + eps) := by
    intro eps heps t x ht hx
    have hcont_eps : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps))
        (Set.Icc 0 T ×ˢ Set.Icc 0 L) := by
      have haff : Continuous (fun r : ℝ => eps * r + eps) := by
        rw [continuous_iff_continuousAt]
        intro r
        exact (hasDerivAt_affine (a := eps) (b := eps) (x := r)).continuousAt
      have h1 : ContinuousOn (fun p : ℝ × ℝ => eps * p.1 + eps)
          (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
        haff.continuousOn.comp continuous_fst.continuousOn (fun p _ => Set.mem_univ _)
      exact hcont.add h1
    have hrect_compact : IsCompact (Set.Icc 0 T ×ˢ Set.Icc 0 L) :=
      isCompact_Icc.prod isCompact_Icc
    have hrect_ne : (Set.Icc 0 T ×ˢ Set.Icc 0 L).Nonempty :=
      ⟨(0, 0), Set.mk_mem_prod ⟨le_refl 0, hT.le⟩ ⟨le_refl 0, hL.le⟩⟩
    obtain ⟨p0, hp0mem, hmin0⟩ := hrect_compact.exists_isMinOn hrect_ne hcont_eps
    obtain ⟨t0, x0⟩ := p0
    have hpair : t0 ∈ Set.Icc 0 T ∧ x0 ∈ Set.Icc 0 L := hp0mem
    have ht0 : t0 ∈ Set.Icc 0 T := hpair.1
    have hx0 : x0 ∈ Set.Icc 0 L := hpair.2
    have hmin_time : IsMinOn (fun τ => c τ x0 + (eps * τ + eps)) (Set.Icc 0 T) t0 :=
      Filter.eventually_principal.mpr (fun τ hτ => by
        have hmem : (τ, x0) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := Set.mk_mem_prod hτ hx0
        have h := hmin0 hmem
        change c t0 x0 + (eps * t0 + eps) ≤ c τ x0 + (eps * τ + eps)
        exact h)
    have hmin_space : IsMinOn (fun y => c t0 y + (eps * t0 + eps)) (Set.Icc 0 L) x0 :=
      Filter.eventually_principal.mpr (fun y hy => by
        have hmem : (t0, y) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 L := Set.mk_mem_prod ht0 hy
        have h := hmin0 hmem
        change c t0 x0 + (eps * t0 + eps) ≤ c t0 y + (eps * t0 + eps)
        exact h)
    have htime_deriv : HasDerivAt (fun τ => c τ x0 + (eps * τ + eps)) (ct t0 x0 + eps) t0 :=
      hasDerivAt_add (hct t0 x0 ht0 hx0)
        (hasDerivAt_affine (a := eps) (b := eps) (x := t0))
    by_contra hneg2
    push Not at hneg2
    have hle : (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps)) (t0, x0) ≤
        (fun p : ℝ × ℝ => c p.1 p.2 + (eps * p.1 + eps)) (t, x) :=
      hmin0 (Set.mk_mem_prod ht hx)
    have hle' : c t0 x0 + (eps * t0 + eps) ≤ c t x + (eps * t + eps) := hle
    have hmin_neg : c t0 x0 + (eps * t0 + eps) < 0 := by linarith
    have ht0' : 0 ≤ t0 ∧ t0 ≤ T := ht0
    have hx0' : 0 ≤ x0 ∧ x0 ≤ L := hx0
    have ht0_ne : t0 ≠ 0 := by
      intro hcon
      have h1 : 0 ≤ c 0 x0 := hinit x0 hx0
      have h2 : c t0 x0 + (eps * t0 + eps) = c 0 x0 + (eps * 0 + eps) := by rw [hcon]
      have h3 : 0 < eps * 0 + eps := by
        have heq : eps * 0 + eps = eps := by ring
        linarith
      linarith
    have hx0_ne0 : x0 ≠ 0 := by
      intro hcon
      have h1 : 0 ≤ c t0 0 := hb0 t0 ht0
      have h2 : c t0 x0 + (eps * t0 + eps) = c t0 0 + (eps * t0 + eps) := by rw [hcon]
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      have h3 : 0 < eps * t0 + eps := by linarith
      linarith
    have hx0_neL : x0 ≠ L := by
      intro hcon
      have h1 : 0 ≤ c t0 L := hbL t0 ht0
      have h2 : c t0 x0 + (eps * t0 + eps) = c t0 L + (eps * t0 + eps) := by rw [hcon]
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      have h3 : 0 < eps * t0 + eps := by linarith
      linarith
    have hx0Ioo : x0 ∈ Set.Ioo 0 L := by
      change 0 < x0 ∧ x0 < L
      exact ⟨lt_of_le_of_ne hx0'.1 (Ne.symm hx0_ne0), lt_of_le_of_ne hx0'.2 hx0_neL⟩
    have hct_le : ct t0 x0 + eps ≤ 0 := by
      by_cases ht0T : t0 = T
      · have hmem_time : Set.Icc 0 T ∈ nhdsWithin t0 (Set.Iio t0) := by
          rw [ht0T]
          have hIoi : Set.Ioi 0 ∈ nhds T := Ioi_mem_nhds hT
          have h1 : Set.Ioi 0 ∈ nhdsWithin T (Set.Iio T) :=
            mem_nhdsWithin_of_mem_nhds hIoi
          have h2 : Set.Iio T ∈ nhdsWithin T (Set.Iio T) := self_mem_nhdsWithin
          have hinter : Set.Ioi 0 ∩ Set.Iio T ∈ nhdsWithin T (Set.Iio T) :=
            Filter.inter_mem h1 h2
          apply Filter.mem_of_superset hinter
          intro y hy
          have hy' : 0 < y ∧ y < T := hy
          change 0 ≤ y ∧ y ≤ T
          exact ⟨hy'.1.le, hy'.2.le⟩
        exact isMinOn_hasDerivAt_le_zero htime_deriv hmin_time hmem_time
      · have ht0Ioo : t0 ∈ Set.Ioo 0 T := by
          change 0 < t0 ∧ t0 < T
          exact ⟨lt_of_le_of_ne ht0'.1 (Ne.symm ht0_ne), lt_of_le_of_ne ht0'.2 ht0T⟩
        have ht0Ioo' : 0 < t0 ∧ t0 < T := ht0Ioo
        have hmem_time_nhds : Set.Icc 0 T ∈ nhds t0 :=
          Filter.mem_of_superset (Ioo_mem_nhds ht0Ioo'.1 ht0Ioo'.2)
            Set.Ioo_subset_Icc_self
        have hct_eq : ct t0 x0 + eps = 0 :=
          isMinOn_hasDerivAt_eq_zero htime_deriv hmin_time hmem_time_nhds
        exact le_of_eq hct_eq
    have hcxx_nonneg : 0 ≤ cxx t0 x0 :=
      second_deriv_nonneg_of_isMinOn (g := fun y => cx t0 y) (gd := fun y => cxx t0 y)
        (fun y hy => hasDerivAt_add_const (C := eps * t0 + eps) (hcx t0 y ht0 hy))
        (fun y hy => hcxx t0 y ht0 hy)
        hx0Ioo hmin_space
    have hpde := hPDE t0 x0 ht0 hx0
    have hk0 : 0 ≤ k t0 x0 := hk t0 x0 ht0 hx0
    have hs0 : 0 ≤ s t0 x0 := hs t0 x0 ht0 hx0
    have hE_pos : 0 < eps * t0 + eps := by
      have hmul : 0 ≤ eps * t0 := mul_nonneg heps.le ht0'.1
      linarith
    have hkE : 0 ≤ k t0 x0 * (eps * t0 + eps) := mul_nonneg hk0 hE_pos.le
    have hdist : k t0 x0 * (c t0 x0 + (eps * t0 + eps)) =
        k t0 x0 * c t0 x0 + k t0 x0 * (eps * t0 + eps) := by ring
    have hLHS_eq : (ct t0 x0 + eps) - D * cxx t0 x0 + k t0 x0 * (c t0 x0 + (eps * t0 + eps)) =
        s t0 x0 + eps + k t0 x0 * (eps * t0 + eps) := by linarith
    have hLHS_pos : 0 < (ct t0 x0 + eps) - D * cxx t0 x0 +
        k t0 x0 * (c t0 x0 + (eps * t0 + eps)) := by
      rw [hLHS_eq]
      linarith
    have hDc : 0 ≤ D * cxx t0 x0 := mul_nonneg hD.le hcxx_nonneg
    have hkV : k t0 x0 * (c t0 x0 + (eps * t0 + eps)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hk0 hmin_neg.le
    have hLHS_nonpos : (ct t0 x0 + eps) - D * cxx t0 x0 +
        k t0 x0 * (c t0 x0 + (eps * t0 + eps)) ≤ 0 := by
      linarith
    linarith
  by_contra hneg
  push Not at hneg
  have ht' : 0 ≤ t ∧ t ≤ T := ht
  have ht1 : 0 < t + 1 := by linarith
  have hcn : 0 < -(c t x) := by linarith
  have hpos2 : 0 < -(c t x) / (t + 1) := div_pos hcn ht1
  obtain ⟨eps, heps0, hepilt⟩ := exists_between hpos2
  have hkey := key eps heps0 t x ht hx
  have hmul : eps * (t + 1) < -(c t x) := by
    have h := mul_lt_mul_of_pos_right hepilt ht1
    rw [div_mul_cancel₀ _ (ne_of_gt ht1)] at h
    exact h
  have hring : eps * t + eps = eps * (t + 1) := by ring
  linarith

end MathlibExt.Analysis.PDE.ScalarParabolicComparison

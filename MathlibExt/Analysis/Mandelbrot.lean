/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ComplexAnalysis/Mandelbrot.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `mandelbrot_connected`, manifest revision 1.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The adapted portions are the definitions `Tc` and `Mandelbrot` and the statement of
`mandelbrot_connected`. ATLAS previously recorded the statement as a Batteries wanted theorem in
`WantedExt/Analysis/MandelbrotWanted.lean`. This module supplies its proof and preserves the
names, definitions, statement and declaration docstrings. The upstream problem is archived.
lean-eval ships no NOTICE file.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.LocalAtTarget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Mandelbrot set is connected (Douady–Hubbard)

The Mandelbrot set `M = { c ∈ ℂ | T_c^n(0) stays bounded }`, where
`T_c(z) = z² + c`, is the parameter set for which the critical orbit
of `0` under the quadratic family is bounded. Douady and Hubbard proved
in 1982 (full development 1984–85) that `M` is connected.

## Proof

Write `Pₖ(c) = T_c^[k](0)`. The compact sublevel sets `|Pₙ₊₁(c)| ≤ 3` decrease to the
Mandelbrot set. It suffices to show that each level curve `|Pₙ₊₁(c)| = 3` is connected.

On this curve every earlier iterate has norm strictly less than three. Starting with the known
orbit and keeping its last value fixed, deform the recursions to pure squaring by replacing
the summand `c` in step `k` by `t^(2^(k+1)) c` as `t` goes from one to zero. At each step
the square root can be continued by homotopy lifting. A zero radicand would express the last
value as an earlier critical iterate times a scalar of norm at most one.

At the endpoint this gives a continuous `d`-th root of `Pₙ₊₁` on the level curve, for
`d = 2^n`. The root maps onto a circle because the polynomial is open, the power map is locally
injective there, and the level curve is compact. Each nonzero complex number has `d` distinct
`d`-th roots, while a fiber of the polynomial has at most `d` points. Thus the root is also
injective and identifies the level curve with the circle.
-/

@[expose] public section

namespace MathlibExt.Analysis.MandelbrotWanted.ComplexAnalysis.MandelbrotProblem

open Function Metric Set

/-- **The quadratic family.** For $c \in \mathbb{C}$, $T_c \colon \mathbb{C} \to \mathbb{C}$ is the
map $T_c(z) = z^2 + c$. -/
def Tc (c : ℂ) (z : ℂ) : ℂ := z ^ 2 + c

/-- **The Mandelbrot set.** The Mandelbrot set is the set of all $c \in \mathbb{C}$ for which the
orbit of $0$ under $T_c(z) = z^2 + c$ is bounded: there is a real number $M$ with
$|T_c^n(0)| \le M$ for every $n \in \mathbb{N}$, where $T_c^n$ is the $n$-th iterate of $T_c$
and $T_c^0$ is the identity. -/
def Mandelbrot : Set ℂ :=
  { c : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ M }

private def orbit (n : ℕ) (c : ℂ) := (Tc c)^[n] 0

private theorem orbit_succ (n : ℕ) (c : ℂ) : orbit (n + 1) c = orbit n c ^ 2 + c :=
  Function.iterate_succ_apply' (Tc c) n 0

private theorem orbit_one (c : ℂ) : orbit 1 c = c := by simp [orbit, Tc]

private theorem orbit_zero_param (n : ℕ) : orbit n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit_succ, ih]

private theorem continuous_orbit (n : ℕ) : Continuous (orbit n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (ih.pow 2).add continuous_id |>.congr (fun c => (orbit_succ n c).symm)

private theorem norm_succ_ge {c : ℂ} {n : ℕ} (hn : 3 ≤ ‖orbit n c‖) (hc : ‖c‖ ≤ ‖orbit n c‖) :
    ‖orbit n c‖ + 1 ≤ ‖orbit (n + 1) c‖ := by
  have ht := norm_sub_le (orbit n c ^ 2 + c) c
  rw [add_sub_cancel_right, norm_pow] at ht
  rw [orbit_succ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (norm_nonneg (orbit n c))]

private theorem norm_add_ge {c : ℂ} {n : ℕ} (hn : 3 ≤ ‖orbit n c‖) (hc : ‖c‖ ≤ ‖orbit n c‖) :
    ∀ k : ℕ, ‖orbit n c‖ + k ≤ ‖orbit (n + k) c‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ‖orbit n c‖ ≤ ‖orbit (n + k) c‖ :=
      le_trans (le_add_of_nonneg_right (Nat.cast_nonneg k)) ih
    have hg := norm_succ_ge (hn.trans hk) (hc.trans hk)
    change ‖orbit n c‖ + ((k + 1 : ℕ) : ℝ) ≤ ‖orbit ((n + k) + 1) c‖
    rw [Nat.cast_succ]
    linarith

private theorem zero_mem : (0 : ℂ) ∈ Mandelbrot :=
  ⟨0, fun n => by change ‖orbit n 0‖ ≤ 0; simp [orbit_zero_param]⟩

private theorem notMem_of_escape {c : ℂ} {n : ℕ} (hn : 3 ≤ ‖orbit n c‖) (hc : ‖c‖ ≤ ‖orbit n c‖) :
    c ∉ Mandelbrot := by
  rintro ⟨bound, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_gt bound
  have hb : ‖orbit (n + k) c‖ ≤ bound := hB _
  have := norm_add_ge hn hc k
  linarith [norm_nonneg (orbit n c)]

private theorem norm_param_le_orbit {c : ℂ} (hc : 3 ≤ ‖c‖) (n : ℕ) :
    ‖c‖ ≤ ‖orbit (n + 1) c‖ := by
  have hg := norm_add_ge (n := 1) (c := c) (by simpa [orbit_one] using hc) (by simp [orbit_one]) n
  rw [orbit_one, Nat.add_comm 1 n] at hg
  linarith [Nat.cast_nonneg (α := ℝ) n]

private def sublevel (n : ℕ) : Set ℂ := {c | ‖orbit (n + 1) c‖ ≤ 3}

private theorem antitone_sublevel : Antitone sublevel := by
  apply antitone_nat_of_succ_le
  intro n c
  change ‖orbit (n + 2) c‖ ≤ 3 → ‖orbit (n + 1) c‖ ≤ 3
  intro h
  by_contra! hn
  have hc : ‖c‖ ≤ ‖orbit (n + 1) c‖ := by
    rcases le_total 3 ‖c‖ with h | h
    · exact norm_param_le_orbit h n
    · exact h.trans hn.le
  linarith [norm_succ_ge hn.le hc]

private theorem isClosed_sublevel (n : ℕ) : IsClosed (sublevel n) :=
  isClosed_le (continuous_orbit (n + 1)).norm continuous_const

private theorem isCompact_sublevel (n : ℕ) : IsCompact (sublevel n) := by
  apply (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset (isClosed_sublevel n)
  intro c hc
  have := antitone_sublevel (Nat.zero_le n) hc
  simpa [sublevel, orbit_one, mem_closedBall, dist_zero_right] using this

private theorem mandelbrot_eq_iInter : Mandelbrot = ⋂ n, sublevel n := by
  ext c
  simp only [mem_iInter]
  constructor
  · intro hm n
    change ‖orbit (n + 1) c‖ ≤ 3
    by_contra! hn
    apply notMem_of_escape hn.le _ hm
    rcases le_total ‖c‖ 3 with hc | hc
    · exact hc.trans hn.le
    · exact norm_param_le_orbit hc n
  · intro h
    refine ⟨3, fun n => ?_⟩
    cases n with
    | zero => norm_num
    | succ n => exact h n

private theorem connected_of_preconnected_sublevels (h : ∀ n, IsPreconnected (sublevel n)) :
    IsConnected Mandelbrot := by
  refine ⟨⟨0, zero_mem⟩, ?_⟩
  rw [mandelbrot_eq_iInter]
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter isClosed_sublevel)).2
  intro u v hu hv hcover huv
  obtain ⟨a, b, ha, hb, hua, hvb, hab⟩ := normal_separation hu hv huv
  let s := sublevel 0 \ (a ∪ b)
  have hsc : IsCompact s := (isCompact_sublevel 0).diff (ha.union hb)
  have hsd : Disjoint s (⋂ n, sublevel n) := by
    apply Set.disjoint_left.2
    intro c hc hcp
    exact hc.2 ((hcover hcp).elim (fun h => Or.inl (hua h)) (fun h => Or.inr (hvb h)))
  obtain ⟨n, hn⟩ := hsc.elim_directed_family_closed sublevel isClosed_sublevel hsd
    antitone_sublevel.directed_ge
  have hsub : sublevel n ⊆ a ∪ b := by
    intro c hc
    by_contra h'
    exact Set.disjoint_left.1 hn ⟨antitone_sublevel (Nat.zero_le n) hc, h'⟩ hc
  rcases (h n).subset_or_subset ha hb hab hsub with hn | hn
  · left
    intro c hc
    exact (hcover hc).resolve_right fun h =>
      Set.disjoint_left.1 hab (hn (iInter_subset sublevel n hc)) (hvb h)
  · right
    intro c hc
    exact (hcover hc).resolve_left fun h =>
      Set.disjoint_left.1 hab (hua h) (hn (iInter_subset sublevel n hc))

private def levelCurve (n : ℕ) : Set ℂ := {c | ‖orbit (n + 1) c‖ = 3}

private theorem norm_orbit_lt_of_mem_levelCurve {n m : ℕ} (hm : m < n + 1) (c : levelCurve n) :
    ‖orbit m c.val‖ < 3 := by
  by_contra! hn
  cases m with
  | zero => norm_num [orbit] at hn
  | succ m =>
    have hc : ‖(c : ℂ)‖ ≤ ‖orbit (m + 1) c‖ := by
      rcases le_total 3 ‖(c : ℂ)‖ with h | h
      · exact norm_param_le_orbit h m
      · exact h.trans hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hm)
    have he := norm_add_ge hn hc k
    rw [← hk] at he
    have hv : ‖orbit (n + 1) c‖ = 3 := c.property
    have : 0 < k := by omega
    linarith [show (0 : ℝ) < k by exact_mod_cast this]

/-- The last `m` steps of the iteration in coordinates scaled by successive powers of `t`. -/
private def scaledIterate (c t : ℂ) (k : ℕ) : ℕ → ℂ → ℂ
  | 0, z => z
  | m + 1, z => scaledIterate c t (k + 1) m (z ^ 2 + t ^ (2 ^ (k + 1)) * c)

private theorem scaledIterate_mul (c t z : ℂ) (k m : ℕ) :
    scaledIterate c t k m (t ^ (2 ^ k) * z) = t ^ (2 ^ (k + m)) * (Tc c)^[m] z := by
  induction m generalizing k z with
  | zero => simp [scaledIterate]
  | succ m ih =>
    rw [scaledIterate, mul_pow, ← pow_mul, ← pow_succ, ← mul_add, ih,
      Function.iterate_succ_apply, Nat.succ_add]
    rfl

private theorem scaledIterate_zero (c z : ℂ) (k m : ℕ) : scaledIterate c 0 k m z = z ^ (2 ^ m) := by
  induction m generalizing z k with
  | zero => simp [scaledIterate]
  | succ m ih =>
    simp only [scaledIterate, zero_pow (by positivity : 2 ^ (k + 1) ≠ 0), zero_mul, add_zero, ih,
      ← pow_mul]
    rw [pow_succ']

open unitInterval in
private theorem sqrt_lift {A : Type*} [TopologicalSpace A]
    (H : C(I × A, ℂ)) (f : C(A, ℂ)) (hne : ∀ x, H x ≠ 0) (h0 : ∀ a, H (0, a) = (f a) ^ 2) :
    ∃ L : C(I × A, ℂ), (∀ x, (L x) ^ 2 = H x) ∧ ∀ a, L (0, a) = f a := by
  let H' : C(I × A, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨H x, hne x⟩, H.continuous.subtype_mk _⟩
  have hf (a : A) : f a ≠ 0 := by
    intro e
    exact hne (0, a) (by simp [h0, e])
  let f' : C(A, {z : ℂ // z ≠ 0}) := ⟨fun a => ⟨f a, hf a⟩, f.continuous.subtype_mk _⟩
  let cov := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  have init (a : A) : H' (0, a) = ⟨(f' a).val ^ 2, pow_ne_zero 2 (f' a).property⟩ :=
    Subtype.ext (h0 a)
  let L := cov.liftHomotopy H' f' init
  exact ⟨⟨fun x => (L x).val, continuous_subtype_val.comp L.continuous⟩,
    fun x => congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H' f' init) x),
    fun a => congrArg Subtype.val (cov.liftHomotopy_zero H' f' init a)⟩

open unitInterval in
private def scale (t : I) : ℂ := ((1 - (t : ℝ) : ℝ) : ℂ)

open unitInterval in
private theorem lift_scaledIterate (n k m : ℕ) (hs : k + m = n) :
    ∃ Y : C(I × levelCurve n, ℂ),
      (∀ x, scaledIterate x.2.val (scale x.1) k m (Y x) = orbit (n + 1) x.2) ∧
      ∀ c, Y (0, c) = orbit (k + 1) c := by
  induction m generalizing k with
  | zero =>
    subst n
    exact ⟨⟨fun x => orbit (k + 1) x.2,
      (continuous_orbit _).comp (continuous_subtype_val.comp continuous_snd)⟩,
      fun _ => rfl, fun _ => rfl⟩
  | succ m ih =>
    obtain ⟨Y, hY, hY0⟩ := ih (k + 1) (by omega)
    let H : C(I × levelCurve n, ℂ) :=
      ⟨fun x => Y x - scale x.1 ^ (2 ^ (k + 1)) * x.2.val, by unfold scale; fun_prop⟩
    let f : C(levelCurve n, ℂ) :=
      ⟨fun c => orbit (k + 1) c, (continuous_orbit _).comp continuous_subtype_val⟩
    -- A zero radicand forces a shorter critical orbit to reach the final level.
    have hnz (x : I × levelCurve n) : H x ≠ 0 := by
      intro he
      change Y x - _ = 0 at he
      have ht := hY x
      rw [sub_eq_zero.mp he, scaledIterate_mul] at ht
      have hiter : (Tc x.2.val)^[m] x.2.val = orbit (m + 1) x.2.val := by
        simp [orbit, Function.iterate_succ_apply, Tc]
      rw [hiter] at ht
      have hsm : ‖scale x.1‖ ≤ 1 := by
        rw [scale, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr x.1.property.2)]
        linarith [x.1.property.1]
      have hle := pow_le_one₀ (n := 2 ^ (k + 1 + m)) (norm_nonneg _) hsm
      have hp := norm_orbit_lt_of_mem_levelCurve (n := n) (m := m + 1) (by omega) x.2
      have hnr := congrArg norm ht
      rw [norm_mul, norm_pow, show ‖orbit (n + 1) x.2‖ = 3 from x.2.property] at hnr
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (norm_nonneg (orbit (m + 1) x.2))]
    have h0 (c : levelCurve n) : H (0, c) = (f c) ^ 2 := by
      change Y (0, c) - _ = _
      rw [hY0, orbit_succ]
      simp [f, scale]
    obtain ⟨L, hL, hL0⟩ := sqrt_lift H f hnz h0
    refine ⟨L, fun x => ?_, hL0⟩
    rw [scaledIterate, hL]
    change scaledIterate _ _ _ _ ((Y x - _) + _) = _
    simpa only [sub_add_cancel] using hY x

open unitInterval in
private theorem exists_root_on_levelCurve (n : ℕ) :
    ∃ F : C(levelCurve n, ℂ), ∀ c, (F c) ^ (2 ^ n) = orbit (n + 1) c := by
  obtain ⟨Y, hY, _⟩ := lift_scaledIterate n 0 n (Nat.zero_add n)
  refine ⟨⟨fun c => Y (1, c), Y.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    fun c => ?_⟩
  simpa [scale, scaledIterate_zero] using hY (1, c)

open Polynomial Topology

private noncomputable def orbitPoly : ℕ → ℂ[X]
  | 0 => X
  | n + 1 => (orbitPoly n) ^ 2 + X

private theorem eval_orbitPoly (n : ℕ) (c : ℂ) : (orbitPoly n).eval c = orbit (n + 1) c := by
  induction n with
  | zero => simp [orbitPoly, orbit_one]
  | succ n ih => rw [orbitPoly, eval_add, eval_pow, eval_X, ih, orbit_succ (n + 1)]

private theorem natDegree_orbitPoly (n : ℕ) : (orbitPoly n).natDegree = 2 ^ n := by
  induction n with
  | zero => simp [orbitPoly]
  | succ n ih =>
    have h : (X : ℂ[X]).natDegree < ((orbitPoly n) ^ 2).natDegree := by
      rw [natDegree_X, natDegree_pow, ih]
      have := Nat.two_pow_pos n
      omega
    rw [orbitPoly, natDegree_add_eq_left_of_natDegree_lt h, natDegree_pow, ih, pow_succ']

private theorem isOpenMap_of_lift {A D E : Type*} [TopologicalSpace A] [TopologicalSpace D]
    [TopologicalSpace E] {f : A → D} {g : D → E} (hf : Continuous f) (hg : Continuous g)
    (hi : IsLocallyInjective g) (ho : IsOpenMap (g ∘ f)) : IsOpenMap f := by
  intro u hu
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨v, hv, hvfa, hinj⟩ := hi (f a)
  let w := u ∩ f ⁻¹' v
  have hw : IsOpen w := hu.inter (hv.preimage hf)
  have hwa : a ∈ w := ⟨ha, hvfa⟩
  refine Filter.mem_of_superset
    (((ho w hw).preimage hg).inter hv |>.mem_nhds (x := f a) ⟨⟨a, hwa, rfl⟩, hvfa⟩) ?_
  rintro y ⟨⟨b, hb, he⟩, hy⟩
  exact ⟨b, hb.1, hinj hb.2 hy he⟩

private theorem injective_on_fiber {q : ℂ[X]} {d : ℕ} (hd : q.natDegree = d) (hd0 : d ≠ 0)
    {a w : ℂ} (ha : a ≠ 0) (haw : a ^ d = w)
    (f : (q.eval ⁻¹' {w}) → {z : ℂ | z ^ d = w}) (hs : Surjective f) : Injective f := by
  classical
  have hnc : q ≠ C w := by
    intro e
    exact hd0 (by rw [← hd, e, natDegree_C])
  have hfin : (q.eval ⁻¹' {w}).Finite := by
    rw [preimage_eval_singleton hnc]
    exact rootSet_finite ..
  let := hfin.to_subtype
  apply (hs.bijective_of_nat_card_le ?_).1
  have hleft : (q.eval ⁻¹' {w}).ncard ≤ d := by
    rw [preimage_eval_singleton hnc, ← hd, ← natDegree_sub_C (p := q) (a := w)]
    exact ncard_rootSet_le ..
  have hright : d ≤ Nat.card {z : ℂ | z ^ d = w} := by
    let s := nthRootsFinset d (1 : ℂ)
    have hcast : Nat.card s = d := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (Complex.isPrimitiveRoot_exp d hd0).card_nthRootsFinset
    let g (u : s) : {z : ℂ | z ^ d = w} :=
      ⟨a * u.val, by
        change (a * u.val) ^ d = w
        rw [mul_pow, (mem_nthRootsFinset (Nat.pos_of_ne_zero hd0) _).mp u.property, mul_one, haw]⟩
    have hT : {z : ℂ | z ^ d = w}.Finite := by
      exact (nthRootsFinset d w).finite_toSet.subset fun z hz =>
        (mem_nthRootsFinset (Nat.pos_of_ne_zero hd0) _).2 hz
    let := hT.to_subtype
    apply hcast.ge.trans
    exact Nat.card_le_card_of_injective g fun x y h =>
      Subtype.ext (mul_left_cancel₀ ha (congrArg Subtype.val h))
  exact hleft.trans hright

private theorem isConnected_levelCurve (n : ℕ) : IsConnected (levelCurve n) := by
  classical
  let q := orbitPoly n
  let d := 2 ^ n
  have hd : q.natDegree = d := natDegree_orbitPoly n
  have hd0 : d ≠ 0 := pow_ne_zero _ (by decide)
  let S : Set ℂ := {z | ‖z‖ = 3}
  let T := (fun z : ℂ => z ^ d) ⁻¹' S
  let D := q.eval ⁻¹' S
  have hD : levelCurve n = D := by ext c; simp [levelCurve, D, S, q, eval_orbitPoly]
  have hq := q.isOpenQuotientMap_eval (hd ▸ hd0)
  obtain ⟨u, hu⟩ := hq.surjective (3 : ℂ)
  have huD : u ∈ D := by change ‖q.eval u‖ = _; simp [hu]
  obtain ⟨F, hF⟩ := exists_root_on_levelCurve n
  let f (x : D) : T := ⟨F ⟨x, hD.symm.subset x.property⟩, by
    change ‖(F _) ^ d‖ = 3
    rw [hF]
    exact hD.symm.subset x.property⟩
  have hf (x : D) : (f x).val ^ d = q.eval x.val := (hF _).trans (eval_orbitPoly n x).symm
  let g := S.restrictPreimage (fun z : ℂ => z ^ d)
  have hg : IsCoveringMap g := by
    apply IsCoveringMapOn.isCoveringMap_restrictPreimage
    apply (isCoveringMapOn_npow d (𝕜 := ℂ) (by exact_mod_cast hd0)).mono
    intro z hz he
    have h : ‖z‖ = 3 := hz
    simp_all
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    apply F.continuous.comp
    exact continuous_subtype_val.subtype_mk _
  have hgf : g ∘ f = S.restrictPreimage q.eval := by ext x; exact hf x
  have hop : IsOpenMap f :=
    isOpenMap_of_lift hfc hg.continuous hg.isLocalHomeomorph.isLocallyInjective
      (hgf ▸ hq.isOpenMap.restrictPreimage S)
  have hTc : IsConnected T := by
    let a := (f ⟨u, huD⟩).val
    have ha : ‖a‖ ^ d = 3 := by rw [← norm_pow]; exact (f ⟨u, huD⟩).property
    have ee : T = sphere 0 ‖a‖ := by
      ext z
      change ‖z ^ d‖ = 3 ↔ _
      rw [norm_pow, ← ha, pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd0]
      simp
    rw [ee]
    exact isConnected_sphere (by simp) 0 (norm_nonneg _)
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.1 hTc.2
  have hcompact : IsCompact D := by
    rw [← hD]
    apply (isCompact_sublevel n).of_isClosed_subset (isClosed_eq (continuous_orbit _).norm
      continuous_const)
    exact fun c hc => le_of_eq hc
  let := isCompact_iff_compactSpace.1 hcompact
  -- The lifted map has nonempty open and closed image in the root circle.
  have hsurj : Surjective f := by
    apply range_eq_univ.1
    apply IsClopen.eq_univ
    · exact ⟨(isCompact_range hfc).isClosed, hop.isOpen_range⟩
    · exact ⟨_, ⟨⟨u, huD⟩, rfl⟩⟩
  -- Over each polynomial value the lift surjects onto all its distinct roots.
  have hinj : Injective f := by
    intro x y he
    let w := q.eval x.val
    have hw : ‖w‖ = 3 := x.property
    have hy : q.eval y.val = w := by rw [← hf, ← he, hf]
    let L (v : q.eval ⁻¹' {w}) : {z : ℂ | z ^ d = w} :=
      ⟨(f ⟨v, by change ‖q.eval v.val‖ = 3; rw [show q.eval v.val = w from v.property, hw]⟩).val,
        (hf _).trans v.property⟩
    have hLs : Surjective L := by
      intro t
      have ht : t.val ∈ T := by change ‖t.val ^ d‖ = 3; rw [t.property, hw]
      obtain ⟨v, hv⟩ := hsurj ⟨t, ht⟩
      have hvw : q.eval v.val = w := by rw [← hf, hv]; exact t.property
      exact ⟨⟨v, hvw⟩, Subtype.ext (congrArg (fun t : T => t.val) hv)⟩
    have hne : (f x).val ≠ 0 := by
      intro h
      have h' := hf x
      rw [h, zero_pow hd0] at h'
      change ‖q.eval x.val‖ = 3 at hw
      rw [← h'] at hw
      norm_num at hw
    have hLi := injective_on_fiber hd hd0 hne (hf x) L hLs
    have hxy := @hLi ⟨x.val, rfl⟩ ⟨y.val, hy⟩ (Subtype.ext (congrArg (fun t : T => t.val) he))
    exact Subtype.ext (congrArg (fun t : q.eval ⁻¹' {w} => t.val) hxy)
  let e := (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hfc hop
  rw [hD, isConnected_iff_connectedSpace]
  let := isConnected_iff_connectedSpace.1 hTc
  exact e.symm.surjective.connectedSpace e.symm.continuous

/-- In a closed separation, the side that misses the level curve is clopen in the plane. -/
private theorem sublevel_subset_of_levelCurve_subset (n : ℕ) {u v : Set ℂ}
    (hu : IsClosed u) (hv : IsClosed v) (hc : sublevel n ⊆ u ∪ v) (hd : Disjoint u v)
    (hb : levelCurve n ⊆ u) : sublevel n ⊆ u := by
  have he : sublevel n ∩ v = {c | ‖orbit (n + 1) c‖ < 3} ∩ uᶜ := by
    ext c
    constructor
    · rintro ⟨hk, hv'⟩
      have hn : c ∉ u := fun h => Set.disjoint_left.1 hd h hv'
      exact ⟨lt_of_le_of_ne hk (fun e => hn (hb e)), hn⟩
    · rintro ⟨hlt, hn⟩
      have hk : c ∈ sublevel n := (show ‖orbit (n + 1) c‖ < 3 from hlt).le
      exact ⟨hk, (hc hk).resolve_left hn⟩
  have hcl : IsClopen (sublevel n ∩ v) :=
    ⟨(isClosed_sublevel n).inter hv,
      he ▸ (isOpen_lt (continuous_orbit _).norm continuous_const).inter hu.isOpen_compl⟩
  intro c h
  by_contra hn
  have hall := hcl.eq_univ ⟨c, h, (hc h).resolve_left hn⟩
  obtain ⟨b, hb'⟩ := (isConnected_levelCurve n).nonempty
  exact Set.disjoint_left.1 hd (hb hb') ((Set.eq_univ_iff_forall.1 hall b).2)

/-- **The Mandelbrot set is connected (Douady–Hubbard).** The Mandelbrot set, the set of all
$c \in \mathbb{C}$ for which the sequence $(T_c^n(0))_{n \ge 0}$ of iterates of $0$ under
$T_c(z) = z^2 + c$ is bounded, is a nonempty connected subset of $\mathbb{C}$.

Source: A. Douady and J. H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math.
Orsay 84-02, 85-04. Listed as §62 in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `mandelbrot_connected`. -/
theorem mandelbrot_connected : IsConnected Mandelbrot := by
  apply connected_of_preconnected_sublevels
  intro n
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_sublevel n)).2
  intro u v hu hv hc hd
  have hcov : levelCurve n ⊆ u ∪ v := fun c h => hc (le_of_eq h)
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed
    (isClosed_eq (continuous_orbit (n + 1)).norm continuous_const)).1 (isConnected_levelCurve n).2
    u v hu hv hcov hd with h | h
  · exact Or.inl (sublevel_subset_of_levelCurve_subset n hu hv hc hd h)
  · exact Or.inr (sublevel_subset_of_levelCurve_subset n hv hu (union_comm u v ▸ hc) hd.symm h)

end MathlibExt.Analysis.MandelbrotWanted.ComplexAnalysis.MandelbrotProblem

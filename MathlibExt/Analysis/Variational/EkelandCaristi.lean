/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Set

namespace MetaMathlibExt

/-!
# Ekeland variational principle and Caristi fixed-point theorem
-/

/--
**Ekeland variational principle without a nonemptiness assumption.** Let $(X, d)$ be a complete
metric space, let $f : X \to \mathbb{R}$ be lower semicontinuous and bounded below, and let
$\varepsilon > 0$. If $x_0 \in X$ satisfies $f(x_0) \le f(x) + \varepsilon$ for every $x \in X$,
then there is $x_\varepsilon \in X$ with $f(x_\varepsilon) \le f(x_0)$,
$d(x_\varepsilon, x_0) \le 1$, and $f(x_\varepsilon) < f(y) + \varepsilon\, d(x_\varepsilon, y)$
for every $y \ne x_\varepsilon$.

The space $X$ is not separately assumed nonempty, since the point $x_0$ already lies in it.
-/
theorem ekeland_variational_principle_general
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {f : X → ℝ} (hf_lsc : LowerSemicontinuous f)
    (hf_bdd : BddBelow (range f))
    {ε : ℝ} (hε : 0 < ε)
    {x₀ : X} (hx₀ : ∀ x, f x₀ ≤ f x + ε) :
    ∃ xε : X, f xε ≤ f x₀ ∧ dist xε x₀ ≤ 1 ∧
      ∀ y, y ≠ xε → f xε < f y + ε * dist xε y := by
  have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε
  -- Slice sets `S x = {y | f y + ε * dist y x ≤ f x}`.
  set S : X → Set X := fun x => { y | f y + ε * dist y x ≤ f x } with hSdef
  have hcont : ∀ x : X, Continuous fun y : X => ε * dist y x := fun x =>
    continuous_const.mul (continuous_id.dist continuous_const)
  have hSclosed : ∀ x : X, IsClosed (S x) := fun x =>
    (hf_lsc.add (hcont x).lowerSemicontinuous).isClosed_preimage _
  have hmem_self : ∀ x : X, x ∈ S x := by
    intro x
    change f x + ε * dist x x ≤ f x
    rw [dist_self, mul_zero, add_zero]
  have htrans : ∀ x y z : X, y ∈ S x → z ∈ S y → z ∈ S x := by
    intro x y z hy hz
    have hy' : f y + ε * dist y x ≤ f x := hy
    have hz' : f z + ε * dist z y ≤ f y := hz
    change f z + ε * dist z x ≤ f x
    have htri : dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    have hmul : ε * dist z x ≤ ε * dist z y + ε * dist y x := by
      have h := mul_le_mul_of_nonneg_left htri hεnn
      rwa [mul_add] at h
    linarith
  have himg_bdd : ∀ x : X, BddBelow (f '' S x) := by
    intro x
    obtain ⟨b, hb⟩ := hf_bdd
    exact ⟨b, by rintro _ ⟨y, _, rfl⟩; exact hb (Set.mem_range_self y)⟩
  have himg_ne : ∀ x : X, (f '' S x).Nonempty := fun x => ⟨f x, x, hmem_self x, rfl⟩
  -- Near-minimizer inside each slice, with error scaled by `ε`.
  have key : ∀ n : ℕ, ∀ x : X,
      ∃ y : X, y ∈ S x ∧ f y < sInf (f '' S x) + (1 / 2 : ℝ) ^ n * ε := by
    intro n x
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n * ε :=
      mul_pos (pow_pos (by norm_num) _) hε
    have hlt : sInf (f '' S x) < sInf (f '' S x) + (1 / 2 : ℝ) ^ n * ε := by
      linarith
    rw [csInf_lt_iff (himg_bdd x) (himg_ne x)] at hlt
    obtain ⟨b, ⟨y, hy, rfl⟩, hb⟩ := hlt
    exact ⟨y, hy, hb⟩
  choose g hgS hgf using key
  -- The Ekeland approximating sequence.
  set seq : ℕ → X :=
    fun n => Nat.rec (motive := fun _ => X) x₀ (fun n prev => g (n + 1) prev) n with hseqdef
  have hseq0 : seq 0 = x₀ := rfl
  have hseqS : ∀ n : ℕ, seq (n + 1) = g (n + 1) (seq n) := fun n => rfl
  have hseq_mem : ∀ n : ℕ, seq (n + 1) ∈ S (seq n) := by
    intro n
    rw [hseqS n]
    exact hgS (n + 1) (seq n)
  have hseq_f : ∀ n : ℕ,
      f (seq (n + 1)) < sInf (f '' S (seq n)) + (1 / 2 : ℝ) ^ (n + 1) * ε := by
    intro n
    rw [hseqS n]
    exact hgf (n + 1) (seq n)
  -- Later points lie in earlier slices.
  have hnest : ∀ n m : ℕ, n ≤ m → seq m ∈ S (seq n) := by
    intro n m hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    clear hnm
    induction k with
    | zero => exact hmem_self _
    | succ k ih =>
      have e : n + (k + 1) = (n + k) + 1 := by omega
      rw [e]
      exact htrans _ _ _ ih (hseq_mem _)
  have hsub : ∀ n : ℕ, S (seq (n + 1)) ⊆ S (seq n) := by
    intro n y hy
    exact htrans _ _ _ (hseq_mem n) hy
  have hmono : ∀ n : ℕ, sInf (f '' S (seq n)) ≤ sInf (f '' S (seq (n + 1))) := by
    intro n
    apply csInf_le_csInf (himg_bdd (seq n)) (himg_ne (seq (n + 1)))
    intro _ hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hsub n hy, rfl⟩
  -- Diameter bound: points of later slices are exponentially close to the center.
  have hbound : ∀ n : ℕ, 1 ≤ n → ∀ y : X,
      y ∈ S (seq n) → dist y (seq n) ≤ (1 / 2 : ℝ) ^ n := by
    intro n hn y hy
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hy' : f y + ε * dist y (seq (m + 1)) ≤ f (seq (m + 1)) := hy
    have hlow : sInf (f '' S (seq (m + 1))) ≤ f y :=
      csInf_le (himg_bdd _) ⟨y, hy, rfl⟩
    have hup : f (seq (m + 1)) < sInf (f '' S (seq m)) + (1 / 2 : ℝ) ^ (m + 1) * ε :=
      hseq_f m
    have hle : sInf (f '' S (seq m)) ≤ sInf (f '' S (seq (m + 1))) := hmono m
    have h1 : ε * dist y (seq (m + 1)) ≤ (1 / 2 : ℝ) ^ (m + 1) * ε := by linarith
    rw [mul_comm ((1 / 2 : ℝ) ^ (m + 1)) ε] at h1
    exact le_of_mul_le_mul_left h1 hε
  -- The geometric majorant tends to zero.
  have htend : Filter.Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 := h0.const_mul 2
    simpa using h1
  have hcauchy : CauchySeq seq := by
    rw [Metric.cauchySeq_iff]
    intro η hη
    have hev : ∀ᶠ n : ℕ in Filter.atTop, 2 * (1 / 2 : ℝ) ^ n < η :=
      htend (Iio_mem_nhds hη)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨max N 1, fun m hm n hn => ?_⟩
    have h1 : dist (seq m) (seq (max N 1)) ≤ (1 / 2 : ℝ) ^ (max N 1) :=
      hbound _ (le_max_right _ _) _ (hnest _ _ hm)
    have h2 : dist (seq n) (seq (max N 1)) ≤ (1 / 2 : ℝ) ^ (max N 1) :=
      hbound _ (le_max_right _ _) _ (hnest _ _ hn)
    have htri : dist (seq m) (seq n)
        ≤ dist (seq m) (seq (max N 1)) + dist (seq (max N 1)) (seq n) :=
      dist_triangle _ _ _
    rw [dist_comm (seq (max N 1)) (seq n)] at htri
    have h4 : 2 * (1 / 2 : ℝ) ^ (max N 1) < η := hN _ (le_max_left _ _)
    linarith
  obtain ⟨xε, hxε⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- The limit lies in every slice, by closedness.
  have hlim_mem : ∀ n : ℕ, xε ∈ S (seq n) := by
    intro n
    apply (hSclosed (seq n)).mem_of_tendsto hxε
    rw [Filter.eventually_atTop]
    exact ⟨n, fun m hm => hnest n m hm⟩
  have hmem0 : xε ∈ S x₀ := by
    have h := hlim_mem 0
    rwa [hseq0] at h
  have hmem0' : f xε + ε * dist xε x₀ ≤ f x₀ := hmem0
  have hf_le : f xε ≤ f x₀ := by
    have hnn : (0 : ℝ) ≤ ε * dist xε x₀ := mul_nonneg hεnn dist_nonneg
    linarith
  have hdist1 : dist xε x₀ ≤ 1 := by
    have hle : ε * dist xε x₀ ≤ ε * 1 := by
      have hx := hx₀ xε
      rw [mul_one]
      linarith
    exact le_of_mul_le_mul_left hle hε
  -- The limit slice is a singleton, since slice diameters go to zero.
  have hsing : ∀ y : X, y ∈ S xε → y = xε := by
    intro y hy
    have hyn : ∀ n : ℕ, y ∈ S (seq n) := fun n => htrans _ _ _ (hlim_mem n) hy
    have hle : ∀ n : ℕ, dist y xε ≤ 2 * (1 / 2 : ℝ) ^ n := by
      intro n
      have h1 : dist y (seq (max n 1)) ≤ (1 / 2 : ℝ) ^ (max n 1) :=
        hbound _ (le_max_right _ _) _ (hyn _)
      have h2 : dist xε (seq (max n 1)) ≤ (1 / 2 : ℝ) ^ (max n 1) :=
        hbound _ (le_max_right _ _) _ (hlim_mem _)
      have htri : dist y xε ≤ dist y (seq (max n 1)) + dist (seq (max n 1)) xε :=
        dist_triangle _ _ _
      rw [dist_comm (seq (max n 1)) xε] at htri
      have hpow : (1 / 2 : ℝ) ^ (max n 1) ≤ (1 / 2 : ℝ) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
      linarith
    have h0 : dist y xε ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend hle
    have h00 : dist y xε = 0 := le_antisymm h0 dist_nonneg
    exact dist_eq_zero.mp h00
  refine ⟨xε, hf_le, hdist1, fun y hyne => ?_⟩
  have hyout : y ∉ S xε := fun hy => hyne (hsing y hy)
  have hlt : f xε < f y + ε * dist y xε := lt_of_not_ge hyout
  rw [dist_comm]
  exact hlt

/--
**Ekeland variational principle.** Let $(X, d)$ be a nonempty complete metric space, let
$f : X \to \mathbb{R}$ be lower semicontinuous and bounded below, and let $\varepsilon > 0$. If
$x_0 \in X$ satisfies $f(x_0) \le f(x) + \varepsilon$ for every $x \in X$, then there is
$x_\varepsilon \in X$ with $f(x_\varepsilon) \le f(x_0)$, $d(x_\varepsilon, x_0) \le 1$, and
$f(x_\varepsilon) < f(y) + \varepsilon\, d(x_\varepsilon, y)$ for every $y \ne x_\varepsilon$.

Source: I. Ekeland, J. Math. Anal. Appl. 47 (1974), 324-353, DOI 10.1016/0022-247X(74)90025-0.
It follows from `ekeland_variational_principle_general`; the instance `[Nonempty X]` is unused and
keeps the source's shape.
Proves `Wanted` entry `ekeland_variational_principle`.
-/
theorem ekeland_variational_principle
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {f : X → ℝ} (hf_lsc : LowerSemicontinuous f)
    (hf_bdd : BddBelow (range f))
    {ε : ℝ} (hε : 0 < ε)
    {x₀ : X} (hx₀ : ∀ x, f x₀ ≤ f x + ε) :
    ∃ xε : X, f xε ≤ f x₀ ∧ dist xε x₀ ≤ 1 ∧
      ∀ y, y ≠ xε → f xε < f y + ε * dist xε y :=
  ekeland_variational_principle_general hf_lsc hf_bdd hε hx₀

/--
**Caristi fixed-point theorem.** Let $(X, d)$ be a nonempty complete metric space and let
$\varphi : X \to \mathbb{R}$ be lower semicontinuous and bounded below. If a map $T : X \to X$
satisfies $d(x, T x) \le \varphi(x) - \varphi(T x)$ for every $x \in X$, then $T$ has a fixed
point: there is $x \in X$ with $T x = x$.

Source: J. Caristi, Trans. Amer. Math. Soc. 215 (1976), 241-251, DOI
10.1090/S0002-9947-1976-0394329-4.
Proves `Wanted` entry `caristi_fixedPoint`.
-/
theorem caristi_fixedPoint
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {φ : X → ℝ} (hφ_lsc : LowerSemicontinuous φ)
    (hφ_bdd : BddBelow (range φ))
    {T : X → X} (hT : ∀ x, dist x (T x) ≤ φ x - φ (T x)) :
    ∃ x, T x = x := by
  -- Brønsted order sets: `S x` collects points reachable from `x` with paid displacement.
  set S : X → Set X := fun x => {y | dist x y ≤ φ x - φ y} with hS_def
  have hSx_mem : ∀ x : X, x ∈ S x := by
    intro x
    simp only [hS_def, Set.mem_ofPred_eq, dist_self, sub_self, le_refl]
  -- Each `S x` is closed: it is a sublevel set of a lower semicontinuous function.
  have hS_closed : ∀ x : X, IsClosed (S x) := by
    intro x
    have hcont : Continuous (fun y => dist x y) :=
      Continuous.dist continuous_const continuous_id
    have hlsc : LowerSemicontinuous (fun y => dist x y + φ y) :=
      hcont.lowerSemicontinuous.add hφ_lsc
    have heq : S x = (fun y => dist x y + φ y) ⁻¹' Iic (φ x) := by
      ext y
      simp only [hS_def, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact hlsc.isClosed_preimage _
  have hT_mem : ∀ x : X, T x ∈ S x := fun x => hT x
  -- Order sets are nested along the order.
  have hS_nested : ∀ x y : X, y ∈ S x → S y ⊆ S x := by
    intro x y hy z hz
    simp only [hS_def, Set.mem_ofPred_eq] at hy hz ⊢
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ (φ x - φ y) + (φ y - φ z) := add_le_add hy hz
      _ = φ x - φ z := by ring
  -- Moving inside `S x` does not increase `φ`.
  have hφ_le : ∀ x y : X, y ∈ S x → φ y ≤ φ x := by
    intro x y hy
    simp only [hS_def, Set.mem_ofPred_eq] at hy
    have hnn : 0 ≤ dist x y := dist_nonneg
    linarith
  have hbdd_of_subset : ∀ s : Set ℝ, s ⊆ range φ → BddBelow s := by
    intro s hs
    obtain ⟨b, hb⟩ := hφ_bdd
    exact ⟨b, fun z hz => hb (hs hz)⟩
  -- At each step we can pick a point of `S x` whose `φ`-value is nearly minimal.
  have hstep : ∀ n : ℕ, ∀ x : X, ∃ y ∈ S x, φ y < sInf (φ '' S x) + (2 : ℝ)⁻¹ ^ n := by
    intro n x
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
    have hne : (φ '' S x).Nonempty := ⟨φ x, x, hSx_mem x, rfl⟩
    have hlt : sInf (φ '' S x) < sInf (φ '' S x) + (2 : ℝ)⁻¹ ^ n := by linarith
    obtain ⟨a, ha_mem, ha_lt⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨y, hy_mem, rfl⟩ := ha_mem
    exact ⟨y, hy_mem, ha_lt⟩
  choose F hF using hstep
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  let x : ℕ → X := fun n => Nat.rec (motive := fun _ => X) x₀ (fun n ih => F n ih) n
  have hmem : ∀ n : ℕ, x (n + 1) ∈ S (x n) := fun n => (hF n (x n)).1
  have hφstep : ∀ n : ℕ, φ (x (n + 1)) < sInf (φ '' S (x n)) + (2 : ℝ)⁻¹ ^ n :=
    fun n => (hF n (x n)).2
  -- Every tail of the sequence stays in the current order set.
  have htail : ∀ n k : ℕ, n ≤ k → x k ∈ S (x n) := by
    intro n k hnk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    clear hnk
    induction d with
    | zero => simpa using hSx_mem (x n)
    | succ d ih =>
        have heq : n + (d + 1) = (n + d) + 1 := by ring
        rw [heq]
        exact hS_nested _ _ ih (hmem (n + d))
  have hanti : Antitone (φ ∘ x) := by
    apply antitone_nat_of_succ_le
    intro n
    change φ (x (n + 1)) ≤ φ (x n)
    exact hφ_le _ _ (hmem n)
  have hrange_bdd : BddBelow (range (φ ∘ x)) :=
    hbdd_of_subset _ (Set.range_comp_subset_range x φ)
  set L : ℝ := ⨅ i, (φ ∘ x) i with hL_def
  have hφ_lim : Filter.Tendsto (φ ∘ x) Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hrange_bdd
  -- The sequence is Cauchy since `φ`-values converge and bound the distances.
  have hC : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hφ_lim) (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have e1 : dist (φ (x m)) L < ε / 2 := hN m hm
    have e2 : dist (φ (x n)) L < ε / 2 := hN n hn
    rw [Real.dist_eq] at e1 e2
    rw [abs_lt] at e1 e2
    rcases le_total m n with hmn | hmn
    · have h1 : dist (x m) (x n) ≤ φ (x m) - φ (x n) := htail m n hmn
      linarith [e1.1, e1.2, e2.1, e2.2]
    · have h1 : dist (x n) (x m) ≤ φ (x n) - φ (x m) := htail n m hmn
      rw [dist_comm]
      linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨xstar, hx_lim⟩ := cauchySeq_tendsto_of_complete hC
  -- The limit lies in every order set, since they are closed and contain tails.
  have hstar : ∀ n : ℕ, xstar ∈ S (x n) := by
    intro n
    exact (hS_closed (x n)).mem_of_tendsto hx_lim
      (Filter.eventually_atTop.mpr ⟨n, fun k hk => htail n k hk⟩)
  -- Lower semicontinuity bounds `φ` at the limit by the infimum of the values.
  have hφstar : φ xstar ≤ L := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hC' : IsClosed (φ ⁻¹' Iic (L + ε)) := hφ_lsc.isClosed_preimage (L + ε)
    have hev : ∀ᶠ k : ℕ in Filter.atTop, x k ∈ φ ⁻¹' Iic (L + ε) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hφ_lim) ε hε
      rw [Filter.eventually_atTop]
      refine ⟨N, fun k hk => ?_⟩
      have e : dist (φ (x k)) L < ε := hN k hk
      rw [Real.dist_eq, abs_lt] at e
      simp only [Set.mem_preimage, Set.mem_Iic]
      linarith [e.2]
    have hmem' := hC'.mem_of_tendsto hx_lim hev
    simpa using hmem'
  have hpow_lim : Filter.Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  -- Points of `S xstar` sit above the infimum `L`.
  have hLy : ∀ y : X, y ∈ S xstar → L ≤ φ y := by
    intro y hy
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hpow_lim) ε hε
    have e : (2 : ℝ)⁻¹ ^ N < ε := by
      have h : dist ((2 : ℝ)⁻¹ ^ N) 0 < ε := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_pos (pow_pos (by norm_num) N)] at h
      exact h
    have hL1 : L ≤ φ (x (N + 1)) := ciInf_le hrange_bdd (N + 1)
    have hL2 : φ (x (N + 1)) < sInf (φ '' S (x N)) + (2 : ℝ)⁻¹ ^ N := hφstep N
    have hL3 : sInf (φ '' S (x N)) ≤ φ y :=
      csInf_le (hbdd_of_subset _ (image_subset_range φ (S (x N))))
        ⟨y, hS_nested _ _ (hstar N) hy, rfl⟩
    linarith
  -- Hence `S xstar` is a singleton: distances to the limit are squeezed to zero.
  have hdist0 : ∀ y : X, y ∈ S xstar → dist xstar y = 0 := by
    intro y hy
    have hLHS : Filter.Tendsto (fun n : ℕ => dist (x n) y) Filter.atTop (nhds (dist xstar y)) :=
      hx_lim.dist tendsto_const_nhds
    have hRHS : Filter.Tendsto (fun n : ℕ => φ (x n) - φ y) Filter.atTop (nhds (L - φ y)) :=
      hφ_lim.sub tendsto_const_nhds
    have hle : dist xstar y ≤ L - φ y := by
      apply le_of_tendsto_of_tendsto hLHS hRHS
      exact Filter.Eventually.of_forall (fun n => hS_nested _ _ (hstar n) hy)
    have hnn : 0 ≤ dist xstar y := dist_nonneg
    have hLb := hLy y hy
    linarith
  have huniq : ∀ y : X, y ∈ S xstar → xstar = y := by
    intro y hy
    exact dist_eq_zero.mp (hdist0 y hy)
  -- `T xstar ∈ S xstar`, so it must equal `xstar`.
  have hfix : xstar = T xstar := huniq _ (hT_mem xstar)
  exact ⟨xstar, hfix.symm⟩

end MetaMathlibExt

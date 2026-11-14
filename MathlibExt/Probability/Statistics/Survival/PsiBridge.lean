/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
public import MathlibExt.Probability.Statistics.ContinuousProductIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The Ψ bridge: T77's product integral satisfies T78's hypothesis bundle

`MathlibExt.Probability.Statistics.ContinuousProductIntegral` (T78) proves Hadamard
differentiability of the continuous-time product integral and the continuous-time Kaplan–Meier
limit law from the hypothesis predicate `IsStieltjesProductIntegral τ P Ψ D S C` on
`ℓ^∞([0, τ])`. `MathlibExt.Analysis.StieltjesProductIntegral` (T77) constructs the product
integral `productIntegral A a b = ∏_{(a, b]} (1 + dA)` as a refinement limit. This file connects
the two: it builds `P = productIntegralLInfty τ` from T77's construction and proves that it
satisfies `IsStieltjesProductIntegral` once the Duhamel operator `Ψ` is supplied.

## The Duhamel operator is a hypothesis

The Duhamel operator `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]` as a continuous linear
map on `ℓ^∞([0, τ])`, bounded in the sup norm of `h`, is the subject of a separate task (T239),
which is not imported. Its properties enter through the predicate `IsPsiOperator τ Ψ D S C`:

* `norm_le`: `‖Ψ A B‖ ≤ C` for `A, B ∈ D` (the integration-by-parts bound);
* `tendsto_duhamel`, `tendsto_psiSum`: `Ψ A B h t` is the refinement limit of the **two-tag
  sums** `psiSum A B h t`, which tag `P(A)(0, ·]` at the left and `P(B)(·, t]` at the right end of
  each cell (T125's `twoTagSum`, the shape of T77's `duhamelSum`), for `h = B - A` and for
  `h ∈ S`.

T77 proves that the sums for `h = B - A` converge (`tendsto_duhamelSum`), so `tendsto_duhamel` only
asks that `Ψ A B` take that limit as its value at `B - A`. For `h` continuous and of bounded
variation (the class used in `isStieltjesProductIntegral_productIntegralLInfty_continuous`) the
sums are expected to converge as well, because `h` has no jump to collide with those of `P(A)` and
`P(B)`; this is not proved here, and it is part of what T239 must supply.

## Main statements

* `productIntegral_pureJumpFun`: **multi-jump product integral**: for an integrator with finitely
  many jumps, `∏_{(a, b]} (1 + dA) = ∏_{a < s j ≤ b} (1 + a j)`. T77's `productIntegral_step`
  is the one-jump case. `productIntegral_pureJump_fin` is the form of T78's `pureJump` field.
* `IsPsiOperator.duhamel`: the **Duhamel equation** `P B - P A = Ψ A B (B - A)`, derived from
  T77's `tendsto_duhamelSum` (it is not assumed).
* `IsPsiOperator.abs_productIntegral_sub_le`: the product integral over every subinterval
  `(u, t]` is Lipschitz in the integrator for the sup norm, `|P(B)(u, t] - P(A)(u, t]| ≤
  C ‖B - A‖`, from the Duhamel equation, the bound on `Ψ` and multiplicativity, applied to the
  integrators frozen before `u` (`freeze`).
* `IsPsiOperator.norm_sub_le`, `IsPsiOperator.tendsto`: **continuity of `Ψ` in `B`**:
  `‖Ψ A B h - Ψ A A h‖ ≤ exp(V τ - V 0) · C ‖B - A‖ · (U τ - U 0)` for `A` controlled by `V` and
  `h ∈ S` controlled by `U`, hence `Ψ A B h → Ψ A A h` as `B → A` within `D`.
* `continuous_subset_closure_isBV`: continuous functions are uniform limits of continuous
  functions of bounded variation (Weierstrass).
* `isStieltjesProductIntegral_productIntegralLInfty`: **the bridge**: T77's product integral,
  with a Duhamel operator satisfying `IsPsiOperator`, satisfies T78's `IsStieltjesProductIntegral`
  on a domain `D` of integrators of bounded variation that is closed under `freeze`;
  `isStieltjesProductIntegral_productIntegralLInfty_continuous` takes `S` to be the continuous
  functions of bounded variation, so no density hypothesis remains.

## Hypotheses on the domain

`D` must consist of integrators of bounded variation (`IsBV`) and be closed under `freeze A u`
(`t ↦ A (max t u)`). A total-variation ball centered at `0`, the classical domain of the
Duhamel bound, has both properties (a ball `{A | TV(A - A₀) ≤ R}` around a non-constant `A₀`
need not be closed under `freeze`). The continuity of `Ψ` in `B` uses the closure under
`freeze`: the Lipschitz bound on subintervals is obtained by applying the Duhamel equation to
frozen integrators. Without a bound on the total variation the sup-norm continuity fails (see
the test file: `2 (n + 1)²` alternating jumps of size `1/(n + 1)` have sup norm at most
`1/(n + 1)` and a product integral at most `1/2`).

## References

* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §20.3.
-/

@[expose] public section

open Filter Topology Finset
open MathlibExt.Analysis.StieltjesProductIntegral
open MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
open MathlibExt.Probability.Statistics.ContinuousProductIntegral
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.Survival.PsiBridge

/-! ### Product integrals of pure-jump integrators -/

section PureJump

variable {ι : Type*}

/-- The **pure-jump integrator** with jumps `a j` at the times `s j`, `j ∈ T`:
`t ↦ ∑_{j ∈ T, s j ≤ t} a j`. -/
noncomputable def pureJumpFun (T : Finset ι) (s a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ T with s j ≤ t, a j

/-- The increment of a pure-jump integrator over `(y, x]` is the sum of the jumps there. -/
theorem pureJumpFun_sub (T : Finset ι) (s a : ι → ℝ) {x y : ℝ} (hyx : y ≤ x) :
    pureJumpFun T s a x - pureJumpFun T s a y = ∑ j ∈ T with y < s j ∧ s j ≤ x, a j := by
  simp only [pureJumpFun, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : s j ≤ y
  · have h2 : s j ≤ x := h1.trans hyx
    simp [h1, h2, not_lt.2 h1]
  · by_cases h2 : s j ≤ x
    · simp [h1, h2, lt_of_not_ge h1]
    · simp [h1, h2]

/-- A pure-jump integrator is controlled by the pure-jump integrator of the absolute jumps. -/
theorem isControl_pureJumpFun (T : Finset ι) (s a : ι → ℝ) (lo hi : ℝ) :
    IsControl (pureJumpFun T s a) (pureJumpFun T s fun j => |a j|) lo hi := by
  intro x y _ hyx _
  rw [pureJumpFun_sub T s a hyx, pureJumpFun_sub T s _ hyx]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Product integral of a pure-jump integrator with finitely many jumps**: if the jump times
`s j`, `j ∈ T`, are distinct, then `∏_{(lo, hi]} (1 + dA) = ∏_{lo < s j ≤ hi} (1 + a j)`.
The proof splits `[lo, hi]` at the first jump in `(lo, hi]` by multiplicativity
(`productIntegral_mul`) and uses the one-jump case `productIntegral_step` of T77 there. -/
theorem productIntegral_pureJumpFun (T : Finset ι) (s a : ι → ℝ) (hs : Set.InjOn s T)
    {lo hi : ℝ} (hlh : lo ≤ hi) :
    productIntegral (pureJumpFun T s a) lo hi = ∏ j ∈ T with lo < s j ∧ s j ≤ hi, (1 + a j) := by
  classical
  suffices H : ∀ n : ℕ, ∀ lo : ℝ, lo ≤ hi →
      (T.filter fun j => lo < s j ∧ s j ≤ hi).card = n →
      productIntegral (pureJumpFun T s a) lo hi =
        ∏ j ∈ T with lo < s j ∧ s j ≤ hi, (1 + a j) from H _ lo hlh rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hlh hn
  set F := T.filter fun j => lo < s j ∧ s j ≤ hi with hF
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · -- no jump in `(lo, hi]`: the integrator is constant there
    have hcongr : ∀ x ∈ Set.Icc lo hi,
        pureJumpFun T s a x = (fun _ => pureJumpFun T s a lo) x := by
      intro x hx
      have hempty : (T.filter fun j => lo < s j ∧ s j ≤ x) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun j hjT hj => ?_
        have hjF : j ∈ F := Finset.mem_filter.2 ⟨hjT, hj.1, hj.2.trans hx.2⟩
        rw [hFe] at hjF
        exact Finset.notMem_empty j hjF
      have := pureJumpFun_sub T s a hx.1
      rw [hempty, sum_empty] at this
      simp only
      linarith
    rw [productIntegral_congr hlh hcongr, productIntegral_const, hFe, prod_empty]
  · obtain ⟨j₀, hj₀F, hmin⟩ := F.exists_min_image s hFne
    have hj₀ := Finset.mem_filter.1 hj₀F
    have hloc : lo < s j₀ := hj₀.2.1
    have hchi : s j₀ ≤ hi := hj₀.2.2
    -- the only jump in `(lo, s j₀]` is `j₀`
    have hleft : (T.filter fun j => lo < s j ∧ s j ≤ s j₀) = {j₀} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hjT, h1, h2⟩
        have hjF : j ∈ F := Finset.mem_filter.2 ⟨hjT, h1, h2.trans hchi⟩
        exact hs hjT hj₀.1 (le_antisymm h2 (hmin j hjF))
      · rintro rfl
        exact ⟨hj₀.1, hloc, le_rfl⟩
    -- the jumps in `(s j₀, hi]` are the other jumps in `(lo, hi]`
    have hright : (T.filter fun j => s j₀ < s j ∧ s j ≤ hi) = F.erase j₀ := by
      ext j
      simp only [Finset.mem_erase, hF, Finset.mem_filter]
      constructor
      · rintro ⟨hjT, h1, h2⟩
        refine ⟨fun h => ?_, hjT, hloc.trans h1, h2⟩
        rw [h] at h1
        exact lt_irrefl _ h1
      · rintro ⟨hne, hjT, h1, h2⟩
        refine ⟨hjT, lt_of_le_of_ne (hmin j (Finset.mem_filter.2 ⟨hjT, h1, h2⟩)) fun h => ?_,
          h2⟩
        exact hne (hs hjT hj₀.1 h.symm)
    -- left piece: a single step at `s j₀`
    have hconst : ∀ x ∈ Set.Icc lo (s j₀),
        pureJumpFun T s a x =
          (fun t => if s j₀ ≤ t then pureJumpFun T s a (s j₀) else pureJumpFun T s a lo) x := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with hxc | hxc
      · subst hxc
        simp only [le_refl, ite_true]
      · simp only [not_le.2 hxc, ite_false]
        have hempty : (T.filter fun j => lo < s j ∧ s j ≤ x) = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun j hjT hj => ?_
          have := hmin j (Finset.mem_filter.2 ⟨hjT, hj.1, hj.2.trans (hxc.le.trans hchi)⟩)
          linarith [hj.2]
        have := pureJumpFun_sub T s a hx.1
        rw [hempty, sum_empty] at this
        linarith
    have hstep : productIntegral (pureJumpFun T s a) lo (s j₀) = 1 + a j₀ := by
      rw [productIntegral_congr hloc.le hconst, productIntegral_step hloc le_rfl,
        pureJumpFun_sub T s a hloc.le, hleft, sum_singleton]
    -- right piece: fewer jumps, induction
    have hcard : (T.filter fun j => s j₀ < s j ∧ s j ≤ hi).card < n := by
      rw [hright, ← hn, Finset.card_erase_of_mem hj₀F]
      exact Nat.sub_lt (Finset.card_pos.2 hFne) one_pos
    rw [productIntegral_mul hloc.le hchi (isControl_pureJumpFun T s a lo hi), hstep,
      ih _ hcard (s j₀) hchi rfl, hright]
    exact Finset.mul_prod_erase F (fun j => 1 + a j) hj₀F

/-- **Multi-jump product integral, in the form of T78's `pureJump` field**: if `A` agrees on
`[0, t]` with `x ↦ ∑_{s j ≤ x} a j`, for jump times `0 < s 0 < s 1 < ⋯`, then
`∏_{(0, t]} (1 + dA) = ∏_{s j ≤ t} (1 + a j)`. -/
theorem productIntegral_pureJump_fin {k : ℕ} (s a : Fin k → ℝ) (hs : StrictMono s)
    (hpos : ∀ j, 0 < s j) {A : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ x ∈ Set.Icc 0 t, A x = ∑ j with s j ≤ x, a j) :
    productIntegral A 0 t = ∏ j with s j ≤ t, (1 + a j) := by
  rw [productIntegral_congr ht hA]
  refine (productIntegral_pureJumpFun univ s a hs.injective.injOn ht).trans ?_
  congr 1
  exact Finset.filter_congr fun j _ => ⟨fun h => h.2, fun h => ⟨hpos j, h⟩⟩

end PureJump

/-! ### Integrators in `ℓ^∞([0, τ])` -/

/-- `ℓ^∞([0, τ])`: bounded real functions on `[0, τ]` with the sup norm (as in
`ContinuousProductIntegral`). -/
local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

section LInfty

variable {τ : ℝ}

/-- The extension of `A ∈ ℓ^∞([0, τ])` to `ℝ` by `0` outside `[0, τ]`. Only its values on
`[0, τ]` are ever used. -/
noncomputable def extendIcc (A : 𝔻[τ]) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc 0 τ then A ⟨t, ht⟩ else 0

theorem extendIcc_of_mem (A : 𝔻[τ]) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    extendIcc A t = A ⟨t, ht⟩ :=
  dite_eq_left_of_eq_true (eq_true ht)

theorem extendIcc_sub (A B : 𝔻[τ]) : extendIcc (B - A) = extendIcc B - extendIcc A := by
  funext t
  by_cases ht : t ∈ Set.Icc 0 τ
  · simp [extendIcc, ht]
  · simp [extendIcc, ht]

theorem extendIcc_zero : extendIcc (0 : 𝔻[τ]) = fun _ => 0 := by
  funext t
  by_cases ht : t ∈ Set.Icc 0 τ
  · simp [extendIcc, ht]
  · simp [extendIcc, ht]

/-- `A ∈ ℓ^∞([0, τ])` has **bounded variation**: its extension has a monotone control on
`[0, τ]` (equivalently, bounded variation there, by `exists_control_of_boundedVariationOn`). -/
def IsBV (A : 𝔻[τ]) : Prop :=
  ∃ V : ℝ → ℝ, IsControl (extendIcc A) V 0 τ

/-- A control is not affected by changing the function outside `[a, b]`. -/
theorem isControl_of_eqOn {A B V : ℝ → ℝ} {a b : ℝ} (hc : IsControl A V a b)
    (h : ∀ x ∈ Set.Icc a b, A x = B x) : IsControl B V a b := fun x y hy hyx hx => by
  rw [← h x ⟨hy.trans hyx, hx⟩, ← h y ⟨hy, hyx.trans hx⟩]
  exact hc x y hy hyx hx

/-- The product integral of a controlled `A ∈ ℓ^∞([0, τ])` over any `(u, t] ⊆ [0, τ]` is bounded
by `exp (V τ - V 0)`. -/
theorem abs_productIntegral_extendIcc_le {A : 𝔻[τ]} {V : ℝ → ℝ}
    (hV : IsControl (extendIcc A) V 0 τ) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ τ) :
    |productIntegral (extendIcc A) u t| ≤ Real.exp (V τ - V 0) := by
  refine (abs_productIntegral_le_exp hut (hV.mono hu ht)).trans (Real.exp_le_exp.2 ?_)
  have h1 := hV.sub_nonneg le_rfl hu (hut.trans ht)
  have h2 := hV.sub_nonneg (hu.trans hut) ht le_rfl
  linarith

open scoped Classical in
/-- **T77's product integral as a map on `ℓ^∞([0, τ])`**: `A ↦ (t ↦ ∏_{(0, t]} (1 + dA))` for
integrators of bounded variation (where the product integral exists and is bounded), and `0`
otherwise. -/
noncomputable def productIntegralLInfty (τ : ℝ) (A : 𝔻[τ]) : 𝔻[τ] :=
  if hA : IsBV A then
    ⟨fun t => productIntegral (extendIcc A) 0 t,
      memℓp_infty_iff.2 (by
        obtain ⟨V, hV⟩ := hA
        refine ⟨Real.exp (V τ - V 0), ?_⟩
        rintro _ ⟨t, rfl⟩
        simp only [Real.norm_eq_abs]
        exact abs_productIntegral_extendIcc_le hV le_rfl t.2.1 t.2.2)⟩
  else 0

theorem productIntegralLInfty_apply {A : 𝔻[τ]} (hA : IsBV A) (t : Set.Icc (0 : ℝ) τ) :
    productIntegralLInfty τ A t = productIntegral (extendIcc A) 0 t := by
  rw [productIntegralLInfty, dite_eq_left_of_eq_true (eq_true hA)]

theorem productIntegralLInfty_apply_mk {A : 𝔻[τ]} (hA : IsBV A) {t : ℝ}
    (ht : t ∈ Set.Icc 0 τ) :
    productIntegralLInfty τ A ⟨t, ht⟩ = productIntegral (extendIcc A) 0 t :=
  productIntegralLInfty_apply hA ⟨t, ht⟩

/-- **The pure-jump field of T78** for `productIntegralLInfty`: a pure-jump integrator with
jump times `0 < s 0 < s 1 < ⋯` is of bounded variation and its product integral is the finite
product of `1 + jump`. -/
theorem productIntegralLInfty_pureJump {k : ℕ} (s a : Fin k → ℝ) (hs : StrictMono s)
    (hpos : ∀ j, 0 < s j) (A : 𝔻[τ]) (hA : ∀ t, A t = ∑ j with s j ≤ (t : ℝ), a j)
    (t : Set.Icc (0 : ℝ) τ) :
    productIntegralLInfty τ A t = ∏ j with s j ≤ (t : ℝ), (1 + a j) := by
  have hext : ∀ x ∈ Set.Icc (0 : ℝ) τ, extendIcc A x = pureJumpFun univ s a x := fun x hx => by
    rw [extendIcc_of_mem A hx, hA]
    rfl
  have hbv : IsBV A :=
    ⟨_, isControl_of_eqOn (isControl_pureJumpFun univ s a 0 τ) fun x hx => (hext x hx).symm⟩
  rw [productIntegralLInfty_apply hbv]
  exact productIntegral_pureJump_fin s a hs hpos t.2.1 fun x hx => hext x ⟨hx.1, hx.2.trans t.2.2⟩

/-! ### Freezing an integrator -/

/-- The integrator `A` **frozen before `u`**: `t ↦ A (max t u)`. Its product integral over
`(0, t]` is that of `A` over `(u, t]` (`productIntegral_extendIcc_freeze`). -/
noncomputable def freeze (A : 𝔻[τ]) (u : Set.Icc (0 : ℝ) τ) : 𝔻[τ] :=
  ⟨fun t => A ⟨max (t : ℝ) u, le_max_of_le_left t.2.1, max_le t.2.2 u.2.2⟩,
    memℓp_infty_iff.2 ⟨‖A‖, by
      rintro _ ⟨t, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero A _⟩⟩

theorem freeze_apply (A : 𝔻[τ]) (u t : Set.Icc (0 : ℝ) τ) :
    freeze A u t = A ⟨max (t : ℝ) u, le_max_of_le_left t.2.1, max_le t.2.2 u.2.2⟩ :=
  rfl

theorem extendIcc_freeze (A : 𝔻[τ]) (u : Set.Icc (0 : ℝ) τ) {y : ℝ} (hy : y ∈ Set.Icc 0 τ) :
    extendIcc (freeze A u) y = extendIcc A (max y u) := by
  rw [extendIcc_of_mem _ hy, extendIcc_of_mem _ ⟨le_max_of_le_left hy.1, max_le hy.2 u.2.2⟩]
  rfl

theorem isControl_freeze {A : 𝔻[τ]} {V : ℝ → ℝ} (hV : IsControl (extendIcc A) V 0 τ)
    (u : Set.Icc (0 : ℝ) τ) :
    IsControl (extendIcc (freeze A u)) (fun y => V (max y u)) 0 τ := by
  intro x y hy hyx hx
  rw [extendIcc_freeze A u ⟨hy.trans hyx, hx⟩, extendIcc_freeze A u ⟨hy, hyx.trans hx⟩]
  exact hV _ _ (le_max_of_le_left hy) (max_le_max hyx le_rfl) (max_le hx u.2.2)

theorem IsBV.freeze {A : 𝔻[τ]} (hA : IsBV A) (u : Set.Icc (0 : ℝ) τ) : IsBV (freeze A u) := by
  obtain ⟨V, hV⟩ := hA
  exact ⟨_, isControl_freeze hV u⟩

/-- The product integral of the frozen integrator over `(0, t]` is the product integral of `A`
over `(u, t]` (multiplicativity, and the frozen integrator is constant on `[0, u]`). -/
theorem productIntegral_extendIcc_freeze {A : 𝔻[τ]} {V : ℝ → ℝ}
    (hV : IsControl (extendIcc A) V 0 τ) (u : Set.Icc (0 : ℝ) τ) {t : ℝ} (hut : (u : ℝ) ≤ t)
    (ht : t ≤ τ) :
    productIntegral (extendIcc (freeze A u)) 0 t = productIntegral (extendIcc A) u t := by
  have hc := (isControl_freeze hV u).mono le_rfl ht
  rw [productIntegral_mul u.2.1 hut hc]
  have hcongr₁ : ∀ y ∈ Set.Icc (0 : ℝ) u,
      extendIcc (freeze A u) y = (fun _ => extendIcc A u) y := fun y hy => by
    rw [extendIcc_freeze A u ⟨hy.1, hy.2.trans u.2.2⟩, max_eq_right hy.2]
  have hcongr₂ : ∀ y ∈ Set.Icc (u : ℝ) t, extendIcc (freeze A u) y = extendIcc A y :=
    fun y hy => by
      rw [extendIcc_freeze A u ⟨u.2.1.trans hy.1, hy.2.trans ht⟩, max_eq_left hy.1]
  rw [productIntegral_congr u.2.1 hcongr₁, productIntegral_const,
    productIntegral_congr hut hcongr₂, one_mul]

theorem norm_freeze_sub_le (A B : 𝔻[τ]) (u : Set.Icc (0 : ℝ) τ) :
    ‖freeze B u - freeze A u‖ ≤ ‖B - A‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun t => ?_
  have e : (freeze B u - freeze A u) t =
      (B - A) ⟨max (t : ℝ) u, le_max_of_le_left t.2.1, max_le t.2.2 u.2.2⟩ := by
    rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply]
    rfl
  rw [e]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ _

/-! ### The Duhamel operator as a hypothesis -/

/-- The **two-tag Duhamel sum** for `Ψ A B h t` over the partition of `[0, t]` generated by `s`:
`∑ P(A)(0, u] (h x - h u) P(B)(x, t]` over the cells `(u, x]`, i.e. T125's `twoTagSum` of
`P(A)(0, ·]` (left tags) and `P(B)(·, t]` (right tags) against `h`. For `h = B - A` it is T77's
`duhamelSum` (`duhamelSum_eq_twoTagSum`). -/
noncomputable def psiSum (A B h : 𝔻[τ]) (t : ℝ) (s : Finset ℝ) : ℝ :=
  twoTagSum (productIntegral (extendIcc A) 0) (fun x => productIntegral (extendIcc B) x t)
    (extendIcc h) (partitionPts 0 t s)

/-- **Hypotheses on the Duhamel operator** `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]`
(T239, not imported): on the domain `D`, the continuous linear maps `Ψ A B` on `ℓ^∞([0, τ])` are
bounded by `C`, and their values at `B - A` and at `h ∈ S` are the refinement limits of the
two-tag sums `psiSum`. -/
structure IsPsiOperator (τ : ℝ) (Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]) (D S : Set 𝔻[τ])
    (C : ℝ) : Prop where
  /-- The integration-by-parts bound: `‖Ψ A B‖ ≤ C` in operator norm. -/
  norm_le : ∀ A ∈ D, ∀ B ∈ D, ‖Ψ A B‖ ≤ C
  /-- At `h = B - A`, `Ψ A B h t` is the limit of T77's Duhamel sums. -/
  tendsto_duhamel : ∀ A ∈ D, ∀ B ∈ D, ∀ t : Set.Icc (0 : ℝ) τ,
    Tendsto (psiSum A B (B - A) t) atTop (𝓝 (Ψ A B (B - A) t))
  /-- On the class `S`, `Ψ A B h t` is the limit of the two-tag sums. -/
  tendsto_psiSum : ∀ A ∈ D, ∀ B ∈ D, ∀ h ∈ S, ∀ t : Set.Icc (0 : ℝ) τ,
    Tendsto (psiSum A B h t) atTop (𝓝 (Ψ A B h t))

namespace IsPsiOperator

variable {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D S : Set 𝔻[τ]} {C : ℝ}

/-- **The Duhamel equation** `P B - P A = Ψ A B (B - A)` for T77's product integral, derived from
T77's convergence of the Duhamel sums `tendsto_duhamelSum`. -/
theorem duhamel (hΨ : IsPsiOperator τ Ψ D S C) (hD : ∀ A ∈ D, IsBV A) {A B : 𝔻[τ]}
    (hA : A ∈ D) (hB : B ∈ D) :
    productIntegralLInfty τ B - productIntegralLInfty τ A = Ψ A B (B - A) := by
  obtain ⟨V, hV⟩ := hD A hA
  obtain ⟨W, hW⟩ := hD B hB
  refine lp.ext (funext fun t => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, productIntegralLInfty_apply ⟨W, hW⟩,
    productIntegralLInfty_apply ⟨V, hV⟩]
  refine tendsto_nhds_unique ?_ (hΨ.tendsto_duhamel A hA B hB t)
  refine (tendsto_duhamelSum t.2.1 (hV.mono le_rfl t.2.2) (hW.mono le_rfl t.2.2)).congr
    fun s => ?_
  rw [duhamelSum_eq_twoTagSum, psiSum, extendIcc_sub]

/-- **Sup-norm Lipschitz bound on every subinterval**: `|P(B)(u, t] - P(A)(u, t]| ≤ C ‖B - A‖`
for `A, B ∈ D` and `0 ≤ u ≤ t ≤ τ`. -/
theorem abs_productIntegral_sub_le (hΨ : IsPsiOperator τ Ψ D S C) (hD : ∀ A ∈ D, IsBV A)
    (hfreeze : ∀ A ∈ D, ∀ u, freeze A u ∈ D) {A B : 𝔻[τ]} (hA : A ∈ D) (hB : B ∈ D)
    (u : Set.Icc (0 : ℝ) τ) {t : ℝ} (hut : (u : ℝ) ≤ t) (ht : t ≤ τ) :
    |productIntegral (extendIcc B) u t - productIntegral (extendIcc A) u t| ≤ C * ‖B - A‖ := by
  obtain ⟨V, hV⟩ := hD A hA
  obtain ⟨W, hW⟩ := hD B hB
  have hAu := hfreeze A hA u
  have hBu := hfreeze B hB u
  have htI : t ∈ Set.Icc (0 : ℝ) τ := ⟨u.2.1.trans hut, ht⟩
  have key : (productIntegralLInfty τ (freeze B u) - productIntegralLInfty τ (freeze A u))
      ⟨t, htI⟩ = Ψ (freeze A u) (freeze B u) (freeze B u - freeze A u) ⟨t, htI⟩ := by
    rw [hΨ.duhamel hD hAu hBu]
  rw [lp.coeFn_sub, Pi.sub_apply, productIntegralLInfty_apply_mk (hD _ hBu),
    productIntegralLInfty_apply_mk (hD _ hAu), productIntegral_extendIcc_freeze hW u hut ht,
    productIntegral_extendIcc_freeze hV u hut ht] at key
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hΨ.norm_le _ hAu _ hBu)
  rw [key, ← Real.norm_eq_abs]
  calc ‖Ψ (freeze A u) (freeze B u) (freeze B u - freeze A u) ⟨t, htI⟩‖
      ≤ ‖Ψ (freeze A u) (freeze B u) (freeze B u - freeze A u)‖ :=
        lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
    _ ≤ ‖Ψ (freeze A u) (freeze B u)‖ * ‖freeze B u - freeze A u‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖B - A‖ :=
        mul_le_mul (hΨ.norm_le _ hAu _ hBu) (norm_freeze_sub_le A B u) (norm_nonneg _) hC0

/-- **Quantitative continuity of `Ψ` in the second integrator**: for `A ∈ D` controlled by `V`
and `h ∈ S` controlled by `U`, `‖Ψ A B h - Ψ A A h‖ ≤ exp (V τ - V 0) · C ‖B - A‖ ·
(U τ - U 0)`. -/
theorem norm_sub_le (hΨ : IsPsiOperator τ Ψ D S C) (hτ : 0 ≤ τ) (hD : ∀ A ∈ D, IsBV A)
    (hfreeze : ∀ A ∈ D, ∀ u, freeze A u ∈ D) {A B h : 𝔻[τ]} (hA : A ∈ D) (hB : B ∈ D)
    (hh : h ∈ S) {V U : ℝ → ℝ} (hV : IsControl (extendIcc A) V 0 τ)
    (hU : IsControl (extendIcc h) U 0 τ) :
    ‖Ψ A B h - Ψ A A h‖ ≤ Real.exp (V τ - V 0) * (C * ‖B - A‖) * (U τ - U 0) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hΨ.norm_le A hA B hB)
  set M := Real.exp (V τ - V 0) * (C * ‖B - A‖) with hMdef
  have hM : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (mul_nonneg hC0 (norm_nonneg _))
  have hK : 0 ≤ M * (U τ - U 0) := mul_nonneg hM (hU.sub_nonneg le_rfl hτ le_rfl)
  refine lp.norm_le_of_forall_le hK fun t => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  have hlim := ((hΨ.tendsto_psiSum A hA B hB h hh t).sub
    (hΨ.tendsto_psiSum A hA A hA h hh t)).abs
  refine le_of_tendsto hlim (Eventually.of_forall fun s => ?_)
  have hsplit : psiSum A B h t s - psiSum A A h t s = ∑ x ∈ partitionPts 0 (t : ℝ) s,
      (productIntegral (extendIcc A) 0 (prev (partitionPts 0 (t : ℝ) s) x) *
        (productIntegral (extendIcc B) x t - productIntegral (extendIcc A) x t)) *
      (extendIcc h x - extendIcc h (prev (partitionPts 0 (t : ℝ) s) x)) := by
    rw [psiSum, psiSum, twoTagSum, twoTagSum, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [hsplit]
  refine (abs_sum_cells_mul_le (M := M) t.2.1 (hU.mono le_rfl t.2.2) _ s fun x hx => ?_).trans ?_
  · have hxI := mem_Icc_of_mem_partitionPts t.2.1 hx
    have huI := mem_Icc_of_mem_partitionPts t.2.1 (prev_mem hx)
    rw [abs_mul]
    exact mul_le_mul (abs_productIntegral_extendIcc_le hV le_rfl huI.1 (huI.2.trans t.2.2))
      (hΨ.abs_productIntegral_sub_le hD hfreeze hA hB ⟨x, hxI.1, hxI.2.trans t.2.2⟩ hxI.2 t.2.2)
      (abs_nonneg _) (Real.exp_pos _).le
  · have := hU.sub_nonneg t.2.1 t.2.2 le_rfl
    exact mul_le_mul_of_nonneg_left (by linarith) hM

/-- **Continuity of `Ψ` in the second integrator** at `B = A`, along `D`, on the class `S`: the
`tendsto` field of T78's `IsDuhamelProductIntegral`. -/
theorem tendsto (hΨ : IsPsiOperator τ Ψ D S C) (hD : ∀ A ∈ D, IsBV A)
    (hfreeze : ∀ A ∈ D, ∀ u, freeze A u ∈ D) (hS : ∀ h ∈ S, IsBV h) {A : 𝔻[τ]} (hA : A ∈ D)
    {h : 𝔻[τ]} (hh : h ∈ S) :
    Tendsto (fun B => Ψ A B h) (𝓝[D] A) (𝓝 (Ψ A A h)) := by
  by_cases hτ : 0 ≤ τ
  swap
  · have hsub : ∀ f g : 𝔻[τ], f = g := fun f g =>
      lp.ext (funext fun t => absurd (t.2.1.trans t.2.2) hτ)
    exact tendsto_const_nhds.congr fun B => hsub _ _
  obtain ⟨V, hV⟩ := hD A hA
  obtain ⟨U, hU⟩ := hS h hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : Tendsto (fun B : 𝔻[τ] => ‖B - A‖) (𝓝[D] A) (𝓝 0) := by
    have : Tendsto (fun B : 𝔻[τ] => ‖B - A‖) (𝓝 A) (𝓝 ‖A - A‖) :=
      ((continuous_id.sub continuous_const).norm).tendsto A
    rw [sub_self, norm_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := ((hnorm.const_mul C).const_mul (Real.exp (V τ - V 0))).mul_const (U τ - U 0)
  rw [mul_zero, mul_zero, zero_mul] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with B hB
  exact hΨ.norm_sub_le hτ hD hfreeze hA hB hh hV hU

end IsPsiOperator

/-! ### Density of continuous functions of bounded variation -/

/-- Every continuous `h ∈ ℓ^∞([0, τ])` is a uniform limit of continuous functions of bounded
variation (polynomials, by Weierstrass). -/
theorem continuous_subset_closure_isBV :
    {h : 𝔻[τ] | Continuous fun t ↦ h t} ⊆
      closure {h : 𝔻[τ] | (Continuous fun t ↦ h t) ∧ IsBV h} := by
  intro h hh
  by_cases hτ : 0 ≤ τ
  swap
  · refine subset_closure ⟨hh, fun x => 0, fun x y hy hyx hx => ?_⟩
    exact absurd (hy.trans (hyx.trans hx)) hτ
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcont : ContinuousOn (extendIcc h) (Set.Icc 0 τ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.Icc (0 : ℝ) τ).domRestrict (extendIcc h) = fun t => h t :=
      funext fun t => extendIcc_of_mem h t.2
    rw [this]
    exact hh
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 τ (extendIcc h) hcont (ε / 2)
    (half_pos hε)
  have hpt : ∀ t : Set.Icc (0 : ℝ) τ, |p.eval (t : ℝ) - h t| < ε / 2 := fun t => by
    have := hp t t.2
    rwa [extendIcc_of_mem h t.2] at this
  let g : 𝔻[τ] := ⟨fun t => p.eval (t : ℝ), memℓp_infty_iff.2 ⟨‖h‖ + ε / 2, by
    rintro _ ⟨t, rfl⟩
    have h1 := hpt t
    have h2 := lp.norm_apply_le_norm ENNReal.top_ne_zero h t
    simp only [Real.norm_eq_abs] at h2 ⊢
    have h3 := abs_sub_abs_le_abs_sub (p.eval (t : ℝ)) (h t)
    linarith⟩⟩
  have hg : ∀ t : Set.Icc (0 : ℝ) τ, g t = p.eval (t : ℝ) := fun _ => rfl
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · simp only [hg]
    exact p.continuous.comp continuous_subtype_val
  · refine ⟨_, isControl_of_eqOn (exists_control_of_boundedVariationOn
      (boundedVariationOn_polynomial_eval p hτ)) fun x hx => ?_⟩
    rw [extendIcc_of_mem g hx, hg]
  · rw [dist_eq_norm]
    refine (lp.norm_le_of_forall_le (half_pos hε).le fun t => ?_).trans_lt (half_lt_self hε)
    rw [lp.coeFn_sub, Pi.sub_apply, hg, Real.norm_eq_abs, abs_sub_comm]
    exact (hpt t).le

/-! ### The bridge -/

/-- **The Ψ bridge.** T77's product integral `productIntegralLInfty τ`, together with a Duhamel
operator `Ψ` satisfying `IsPsiOperator` (T239's operator, a hypothesis here), satisfies T78's
hypothesis bundle `IsStieltjesProductIntegral` on a domain `D` of integrators of bounded variation
closed under `freeze`, for a class `S` of integrators of bounded variation that is uniformly dense
in `C[0, τ]`. The Duhamel equation, the continuity of `Ψ` in `B` and the pure-jump formula are
proved, not assumed. -/
theorem isStieltjesProductIntegral_productIntegralLInfty
    {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D S : Set 𝔻[τ]} {C : ℝ}
    (hΨ : IsPsiOperator τ Ψ D S C) (hD : ∀ A ∈ D, IsBV A)
    (hfreeze : ∀ A ∈ D, ∀ u, freeze A u ∈ D) (hS : ∀ h ∈ S, IsBV h)
    (hdense : {h : 𝔻[τ] | Continuous fun t ↦ h t} ⊆ closure S) :
    IsStieltjesProductIntegral τ (productIntegralLInfty τ) Ψ D S C where
  duhamel _ hA _ hB := hΨ.duhamel hD hA hB
  norm_le := hΨ.norm_le
  tendsto _ hA _ hs := hΨ.tendsto hD hfreeze hS hA hs
  continuous_subset_closure := hdense
  pureJump s a hs hpos A hA t := productIntegralLInfty_pureJump s a hs hpos A hA t

/-- **The Ψ bridge for the continuous integrators of bounded variation**: with `S` the continuous
functions of bounded variation, the density hypothesis is discharged by
`continuous_subset_closure_isBV`. -/
theorem isStieltjesProductIntegral_productIntegralLInfty_continuous
    {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D : Set 𝔻[τ]} {C : ℝ}
    (hΨ : IsPsiOperator τ Ψ D {h | (Continuous fun t ↦ h t) ∧ IsBV h} C)
    (hD : ∀ A ∈ D, IsBV A) (hfreeze : ∀ A ∈ D, ∀ u, freeze A u ∈ D) :
    IsStieltjesProductIntegral τ (productIntegralLInfty τ) Ψ D
      {h | (Continuous fun t ↦ h t) ∧ IsBV h} C :=
  isStieltjesProductIntegral_productIntegralLInfty hΨ hD hfreeze (fun _ hh => hh.2)
    continuous_subset_closure_isBV

end LInfty

end MathlibExt.Probability.Statistics.Survival.PsiBridge

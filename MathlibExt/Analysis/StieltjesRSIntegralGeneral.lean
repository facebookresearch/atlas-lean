/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Duhamel operator `Ψ A B` as a continuous linear map on `ℓ^∞`

For integrators `A`, `B` of bounded variation on `[0, τ]`, the **Duhamel operator** of the
product integral (Gill–Johansen 1990) is
`Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]`, where `P(A)(u, v] = ∏_{(u,v]} (1 + dA)`.
This file defines the Riemann–Stieltjes integral this formula needs for a general integrator `h`
and builds `Ψ A B` as a continuous linear map on `ℓ^∞([0, τ])` whose operator norm is bounded in
terms of the total variations of `A` and `B` only:
`‖Ψ A B h‖ ≤ 6 exp (V(A)) exp (V(B)) ‖h‖_∞`.

## The integral

On a cell `(u, x]` of a partition the integrand `s ↦ P(A)(0, s) P(B)(s, t]` is evaluated with
`P(A)(0, ·]` at the left endpoint `u` and `P(B)(·, t]` at the right endpoint `x`; this is the
shape of the Duhamel sums `duhamelSum` of `MathlibExt.Analysis.StieltjesProductIntegral` and
the two-tag sums `twoTagSum F G h P = ∑ F(u) (h x - h u) G(x)` of
`MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous`. `HasTwoTagRSIntegral F G h a b I` says
that these sums converge to `I` along refinement of partitions of `[a, b]`, for an arbitrary
integrator `h : ℝ → ℝ`; with `G = 1` it is the left-endpoint integral `∫ F dh`
(`hasTwoTagRSIntegral_one_iff`). `HasDuhamelIntegral A B h a b I` is the instance with the
Duhamel kernel, and `hasDuhamelIntegral_sub` is the Duhamel identity in integral form:
`∫_{(a,b]} P(A)(a, s) d(B - A)(s) P(B)(s, b] = P(B)(a, b] - P(A)(a, b]`. Tagging the two factors
at opposite ends is what makes the integral of `h = B - A` exist when `B` jumps
(`hasDuhamelIntegral_sub`): with a single tag the kernel and the integrator jump on the same side
at the jumps of `B` (see the module docstrings of `MathlibExt.Analysis.StieltjesRSIntegral` and
`StieltjesRSIntegralLeftContinuous`).

## The operator

The refinement integral need not exist for a bounded `h` (the test file gives a bounded `h` for
which it does not), so it does not by itself define a map on all of `ℓ^∞`. The sums are, however,
bounded by `6 P(V)(0,τ] P(W)(0,τ] ‖h‖_∞` uniformly in the partition
(`abs_twoTagSum_duhamel_le`; `V`, `W` are controls of `A`, `B`). `Ψ` is defined as the limit of the
sums along one fixed ultrafilter `refinementUltrafilter` finer than the refinement filter
`atTop`: a bounded net has a limit along an ultrafilter, the limit is linear in the net, and it
equals the refinement limit whenever that exists. Hence:

* `psi τ A B : 𝔻[τ] →L[ℝ] 𝔻[τ]`, with `𝔻[τ] = lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞`, is a
  continuous linear map for all `A`, `B` of bounded variation on `[0, τ]` (and `0` otherwise);
* `psi_apply_eq_of_hasDuhamelIntegral`: **wherever the integral exists, `Ψ A B h t` is the
  integral**;
* `norm_psi_le`: `‖Ψ A B‖ ≤ 6 exp (V(A)) exp (V(B))`, where `V(·)` is the total variation on
  `[0, τ]`;
* `psi_apply_sub`: the **Duhamel equation** `Ψ A B (B - A) t = P(B)(0, t] - P(A)(0, t]` in
  `ℓ^∞`.

Where the integral does not exist, `Ψ A B h t` is the limit selected by the fixed ultrafilter
and **nothing is claimed about it**. This file proves that the integral exists only for
`h = B - A` (`hasDuhamelIntegral_sub`, used by `psi_apply_sub`). For step, continuous or regulated
`h`, existence of the integral is **not proved here and remains to be proved**; until it is,
`psi_apply_eq_of_hasDuhamelIntegral` identifies `Ψ A B h t` with the integral for such `h` only
conditionally on that existence.

## The three properties as a predicate

`IsPsiCLM τ Ψ` collects exactly the three properties above, stated with the merged primitives
`twoTagSum`, `partitionPts`, `productIntegral` and `eVariationOn` only, so that a file that does
not import this one can restate it verbatim and take `Ψ` as an explicit hypothesis.
`isPsiCLM_psi` proves that `psi τ` satisfies it. The integrators `A`, `B` are functions `ℝ → ℝ`
(the input of `productIntegral`); the integrator `h ∈ ℓ^∞` enters the sums through its extension
by `0` outside `[0, τ]` (`extendIcc`), whose values outside `[0, t]` are never read.

## Main definitions

* `HasTwoTagRSIntegral F G h a b I`, `HasDuhamelIntegral A B h a b I`: the integrals.
* `refinementUltrafilter`, `twoTagLim`: the ultrafilter limit of the two-tag sums.
* `extendIcc h`: a bounded function on `[0, τ]` extended by `0`.
* `psiFun`, `psiConst`, `psiOfBV`, `psi`: the Duhamel operator and its norm bound.
* `IsPsiCLM`: the three properties of `psi τ` as a predicate on operators.

## Main results

* `hasDuhamelIntegral_sub`: the Duhamel identity as a two-tag integral.
* `isControl_productIntegral_left`, `isControl_productIntegral_right`: the two kernel factors
  are controlled by `P(V)(a, ·]` and `-P(W)(·, t]`.
* `abs_twoTagSum_duhamel_le`: the uniform-in-the-partition sup-norm bound on the sums.
* `HasTwoTagRSIntegral.twoTagLim_eq`, `twoTagLim_add`, `twoTagLim_smul`, `abs_twoTagLim_le`.
* `psi_apply_eq_of_hasDuhamelIntegral`, `norm_psi_apply_le`, `norm_psi_le`, `psi_apply_sub`,
  `isPsiCLM_psi`.

## Source receipt (reuse search, 2026-11-13)

Mathlib v4.35.0 has no Riemann–Stieltjes integral and no product integral. Reused from the merged
`MathlibExt.Analysis.StieltjesProductIntegral` (T77): `productIntegral`, `IsControl`,
`exists_control_of_boundedVariationOn`, `productIntegral_mul`, `abs_productIntegral_le`,
`abs_productIntegral_sub_one_add_le`, `one_add_sub_le_productIntegral_of_control`,
`productIntegral_le_exp`, `duhamelSum`, `tendsto_duhamelSum`, `partitionPts`, `prev`. Reused from
`MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous` (T207): `twoTagSum`,
`duhamelSum_eq_twoTagSum`, `twoTagSum_sub_right`, `abs_twoTagSum_le_of_abs_le` (the bound on
two-tag sums), `leftSum`, `HasLeftRSIntegral`. Reused from Mathlib: `lp`, `memℓp_infty`,
`lp.norm_le_of_forall_le`, `LinearMap.mkContinuous`, `Ultrafilter.of`,
`IsCompact.ultrafilter_le_nhds`. The hypothesis predicate
`MathlibExt.Probability.Statistics.ContinuousProductIntegral.IsStieltjesProductIntegral` (T78)
does not take `psi` as it stands. Its `Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]` takes the integrators
in `ℓ^∞([0, τ])`, while `psi τ A B` takes functions `A B : ℝ → ℝ`; and its `norm_le` field asks for
one constant `C` with `‖Ψ A B‖ ≤ C` for all `A`, `B` in a domain `D`, while the bound
`6 exp (V(A)) exp (V(B))` proved here depends on `A` and `B`. Obtaining that API from `psi` needs
an extension map from `ℓ^∞([0, τ])` to functions `ℝ → ℝ` and a domain `D` on which the total
variations over `[0, τ]` are uniformly bounded, by `M` say, so that `C = 6 exp M exp M` works. The
other fields of that predicate (continuity of `Ψ` in `B` on a class whose closure contains
`C[0, τ]`, and the product integral of pure-jump integrators) are not treated here.

## References

* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §20.3.
-/

open Filter Topology Finset
open scoped ENNReal

@[expose] public section

namespace MathlibExt.Analysis.StieltjesRSIntegralGeneral

open MathlibExt.Analysis.StieltjesProductIntegral
  MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous

/-! ### The two-tag Riemann–Stieltjes integral for a general integrator -/

section TwoTagIntegral

variable {F G h g : ℝ → ℝ} {a b I J : ℝ}

/-- `I` is the **two-tag Riemann–Stieltjes integral** `∫_{(a,b]} F(s) dh(s) G(s)`: the sums
`∑ F(u) (h x - h u) G(x)` over the cells `(u, x]` of the partitions of `[a, b]` converge to `I`
along refinement. No regularity of `h` is assumed. -/
def HasTwoTagRSIntegral (F G h : ℝ → ℝ) (a b I : ℝ) : Prop :=
  Tendsto (fun s => twoTagSum F G h (partitionPts a b s)) atTop (𝓝 I)

theorem HasTwoTagRSIntegral.unique (hI : HasTwoTagRSIntegral F G h a b I)
    (hJ : HasTwoTagRSIntegral F G h a b J) : I = J :=
  tendsto_nhds_unique hI hJ

theorem twoTagSum_add_right (P : Finset ℝ) :
    twoTagSum F G (h + g) P = twoTagSum F G h P + twoTagSum F G g P := by
  simp only [twoTagSum, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem twoTagSum_smul_right (c : ℝ) (P : Finset ℝ) :
    twoTagSum F G (c • h) P = c * twoTagSum F G h P := by
  simp only [twoTagSum, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- With `G = 1` the two-tag sum is the left-endpoint sum. -/
theorem twoTagSum_one_right (F h : ℝ → ℝ) (P : Finset ℝ) :
    twoTagSum F (fun _ => 1) h P = leftSum F h P := by
  simp only [twoTagSum, leftSum, mul_one]

/-- With `G = 1` the two-tag integral is the left-endpoint integral `∫ₐᵇ F dh`. -/
theorem hasTwoTagRSIntegral_one_iff :
    HasTwoTagRSIntegral F (fun _ => 1) h a b I ↔ HasLeftRSIntegral F h a b I := by
  unfold HasTwoTagRSIntegral HasLeftRSIntegral leftPartitionSum
  simp only [twoTagSum_one_right]

/-- The two-tag sums over partitions of `[a, b]` only read `h` on `[a, b]`. -/
theorem twoTagSum_partitionPts_congr (hab : a ≤ b) (hhg : ∀ x ∈ Set.Icc a b, h x = g x)
    (s : Finset ℝ) :
    twoTagSum F G h (partitionPts a b s) = twoTagSum F G g (partitionPts a b s) := by
  refine sum_congr rfl fun x hx => ?_
  rw [hhg x (mem_Icc_of_mem_partitionPts hab hx),
    hhg _ (mem_Icc_of_mem_partitionPts hab (prev_mem hx))]

theorem HasTwoTagRSIntegral.congr (hab : a ≤ b) (hI : HasTwoTagRSIntegral F G h a b I)
    (hhg : ∀ x ∈ Set.Icc a b, h x = g x) : HasTwoTagRSIntegral F G g a b I :=
  Filter.Tendsto.congr (fun s => twoTagSum_partitionPts_congr hab hhg s) hI

end TwoTagIntegral

/-- `I` is the **Duhamel integral** `∫_{(a,b]} P(A)(a, s) dh(s) P(B)(s, b]` of the integrator `h`:
the two-tag integral with `F = P(A)(a, ·]` (left tags) and `G = P(B)(·, b]` (right tags). -/
def HasDuhamelIntegral (A B h : ℝ → ℝ) (a b I : ℝ) : Prop :=
  HasTwoTagRSIntegral (productIntegral A a) (fun x => productIntegral B x b) h a b I

/-- **Duhamel identity, integral form**: for controlled integrators,
`∫_{(a,b]} P(A)(a, s) d(B - A)(s) P(B)(s, b] = P(B)(a, b] - P(A)(a, b]`. -/
theorem hasDuhamelIntegral_sub {A B V W : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : IsControl A V a b) (hB : IsControl B W a b) :
    HasDuhamelIntegral A B (B - A) a b (productIntegral B a b - productIntegral A a b) :=
  Filter.Tendsto.congr (fun s => duhamelSum_eq_twoTagSum A B a b s) (tendsto_duhamelSum hab hA hB)

/-! ### The kernel factors are controlled -/

section Kernel

variable {A B V W h : ℝ → ℝ} {a b : ℝ}

/-- The product integral of a control is at least `1`. -/
theorem one_le_productIntegral_control (hab : a ≤ b) (hc : IsControl A V a b) :
    1 ≤ productIntegral V a b := by
  have h1 := one_add_sub_le_productIntegral_of_control hab hc
  have h2 := hc.sub_nonneg le_rfl hab le_rfl
  linarith

/-- The product integral of a control over a subinterval is at most the one over the interval. -/
theorem productIntegral_control_le (hc : IsControl A V a b) {c d : ℝ} (hac : a ≤ c)
    (hcd : c ≤ d) (hdb : d ≤ b) : productIntegral V c d ≤ productIntegral V a b := by
  have e1 : productIntegral V a b = productIntegral V a c * productIntegral V c b :=
    productIntegral_mul hac (hcd.trans hdb) hc.self
  have e2 : productIntegral V c b = productIntegral V c d * productIntegral V d b :=
    productIntegral_mul hcd hdb (hc.self.mono hac le_rfl)
  have h1 : 1 ≤ productIntegral V a c :=
    one_le_productIntegral_control hac (hc.mono le_rfl (hcd.trans hdb))
  have h2 : 1 ≤ productIntegral V c d := one_le_productIntegral_control hcd (hc.mono hac hdb)
  have h3 : 1 ≤ productIntegral V d b :=
    one_le_productIntegral_control hdb (hc.mono (hac.trans hcd) le_rfl)
  have hy0 : 0 ≤ productIntegral V c d := by linarith
  rw [e1, e2]
  calc productIntegral V c d ≤ productIntegral V c d * productIntegral V d b :=
        le_mul_of_one_le_right hy0 h3
    _ ≤ productIntegral V a c * (productIntegral V c d * productIntegral V d b) :=
        le_mul_of_one_le_left (mul_nonneg hy0 (by linarith)) h1

/-- `|P(A)(a, b] - 1| ≤ P(V)(a, b] - 1` for a control `V`. -/
theorem abs_productIntegral_sub_one_le (hab : a ≤ b) (hc : IsControl A V a b) :
    |productIntegral A a b - 1| ≤ productIntegral V a b - 1 := by
  have h1 := abs_productIntegral_sub_one_add_le hab hc
  have h2 := hc b a le_rfl hab le_rfl
  rw [show productIntegral A a b - 1 =
    (productIntegral A a b - (1 + (A b - A a))) + (A b - A a) by ring]
  exact (abs_add_le _ _).trans (by linarith)

/-- The **left kernel factor** `u ↦ P(A)(a, u]` is controlled by `u ↦ P(V)(a, u]`. -/
theorem isControl_productIntegral_left (hc : IsControl A V a b) :
    IsControl (productIntegral A a) (productIntegral V a) a b := by
  intro x y hy hyx hx
  have hcx : IsControl A V a x := hc.mono le_rfl hx
  have e1 : productIntegral A a x = productIntegral A a y * productIntegral A y x :=
    productIntegral_mul hy hyx hcx
  have e2 : productIntegral V a x = productIntegral V a y * productIntegral V y x :=
    productIntegral_mul hy hyx hcx.self
  have hy' : |productIntegral A a y| ≤ productIntegral V a y :=
    abs_productIntegral_le hy (hc.mono le_rfl (hyx.trans hx))
  have hyx' : |productIntegral A y x - 1| ≤ productIntegral V y x - 1 :=
    abs_productIntegral_sub_one_le hyx (hc.mono hy hx)
  rw [e1, e2]
  have k1 : productIntegral A a y * productIntegral A y x - productIntegral A a y =
      productIntegral A a y * (productIntegral A y x - 1) := by ring
  have k2 : productIntegral V a y * productIntegral V y x - productIntegral V a y =
      productIntegral V a y * (productIntegral V y x - 1) := by ring
  rw [k1, k2, abs_mul]
  exact mul_le_mul hy' hyx' (abs_nonneg _) ((abs_nonneg _).trans hy')

/-- The **right kernel factor** `x ↦ P(B)(x, t]` is controlled on `[a, t]` by the monotone
function `x ↦ -P(W)(x, t]`. -/
theorem isControl_productIntegral_right {t : ℝ} (hc : IsControl B W a t) :
    IsControl (fun x => productIntegral B x t) (fun x => -productIntegral W x t) a t := by
  intro x y hy hyx hx
  change |productIntegral B x t - productIntegral B y t| ≤
    -productIntegral W x t - -productIntegral W y t
  have hcy : IsControl B W y t := hc.mono hy le_rfl
  have e1 : productIntegral B y t = productIntegral B y x * productIntegral B x t :=
    productIntegral_mul hyx hx hcy
  have e2 : productIntegral W y t = productIntegral W y x * productIntegral W x t :=
    productIntegral_mul hyx hx hcy.self
  have hx' : |productIntegral B x t| ≤ productIntegral W x t :=
    abs_productIntegral_le hx (hc.mono (hy.trans hyx) le_rfl)
  have hyx' : |productIntegral B y x - 1| ≤ productIntegral W y x - 1 :=
    abs_productIntegral_sub_one_le hyx (hc.mono hy hx)
  rw [e1, e2]
  have k1 : productIntegral B x t - productIntegral B y x * productIntegral B x t =
      -((productIntegral B y x - 1) * productIntegral B x t) := by ring
  have k2 : -productIntegral W x t - -(productIntegral W y x * productIntegral W x t) =
      (productIntegral W y x - 1) * productIntegral W x t := by ring
  rw [k1, k2, abs_neg, abs_mul]
  exact mul_le_mul hyx' hx' (abs_nonneg _) ((abs_nonneg _).trans hyx')

/-- **Uniform sup-norm bound for the Duhamel sums.** For controls `V`, `W` of `A`, `B` on
`[a, b]`, `a ≤ t ≤ b` and `|h| ≤ R` on `[a, t]`, every two-tag sum of the Duhamel kernel over a
partition of `[a, t]` is at most `6 P(V)(a, b] P(W)(a, b] R` in absolute value. -/
theorem abs_twoTagSum_duhamel_le (hA : IsControl A V a b) (hB : IsControl B W a b) {t : ℝ}
    (hat : a ≤ t) (htb : t ≤ b) {R : ℝ} (hR : ∀ x ∈ Set.Icc a t, |h x| ≤ R) (s : Finset ℝ) :
    |twoTagSum (productIntegral A a) (fun x => productIntegral B x t) h (partitionPts a t s)| ≤
      6 * productIntegral V a b * productIntegral W a b * R := by
  have hab : a ≤ b := hat.trans htb
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR a ⟨le_rfl, hat⟩)
  have hKA : 1 ≤ productIntegral V a b := one_le_productIntegral_control hab hA
  have hKB : 1 ≤ productIntegral W a b := one_le_productIntegral_control hab hB
  have hM : ∀ x ∈ Set.Icc a t, |productIntegral A a x| ≤ productIntegral V a b := fun x hx =>
    (abs_productIntegral_le hx.1 (hA.mono le_rfl (hx.2.trans htb))).trans
      (productIntegral_control_le hA le_rfl hx.1 (hx.2.trans htb))
  have hN : ∀ x ∈ Set.Icc a t, |productIntegral B x t| ≤ productIntegral W a b := fun x hx =>
    (abs_productIntegral_le hx.2 (hB.mono hx.1 htb)).trans
      (productIntegral_control_le hB hx.1 hx.2 htb)
  have hF := (isControl_productIntegral_left hA).mono le_rfl htb
  have hG := isControl_productIntegral_right (hB.mono le_rfl htb)
  have key := abs_twoTagSum_le_of_abs_le hat hR hM hN hF hG s
  simp only [productIntegral_self] at key
  have hVt : productIntegral V a t ≤ productIntegral V a b :=
    productIntegral_control_le hA le_rfl hat htb
  have hWt : productIntegral W a t ≤ productIntegral W a b :=
    productIntegral_control_le hB le_rfl hat htb
  have h1 : productIntegral W a b * (productIntegral V a t - 1) ≤
      productIntegral W a b * productIntegral V a b :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : productIntegral V a b * (productIntegral W a t - 1) ≤
      productIntegral V a b * productIntegral W a b :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine key.trans ?_
  rw [show 6 * productIntegral V a b * productIntegral W a b * R =
    R * (6 * productIntegral V a b * productIntegral W a b) by ring]
  exact mul_le_mul_of_nonneg_left (by linarith) hR0

end Kernel

/-! ### The ultrafilter limit of the two-tag sums -/

/-- A fixed ultrafilter on the finite sets of reals that refines `atTop` (the refinement filter on
partitions). Limits along it extend refinement limits to every bounded net. -/
noncomputable def refinementUltrafilter : Ultrafilter (Finset ℝ) :=
  Ultrafilter.of atTop

theorem refinementUltrafilter_le : (refinementUltrafilter : Filter (Finset ℝ)) ≤ atTop :=
  Ultrafilter.of_le _

/-- A bounded net converges along `refinementUltrafilter`. -/
theorem tendsto_refinementUltrafilter {u : Finset ℝ → ℝ} {R : ℝ} (hu : ∀ s, |u s| ≤ R) :
    Tendsto u (refinementUltrafilter : Filter (Finset ℝ))
      (𝓝 (limUnder (refinementUltrafilter : Filter (Finset ℝ)) u)) := by
  refine tendsto_nhds_limUnder ?_
  obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := -R) (b := R)).ultrafilter_le_nhds
    (Ultrafilter.map u refinementUltrafilter) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact Filter.mem_map.2 (Filter.univ_mem' fun s => abs_le.1 (hu s)))
  rw [Ultrafilter.coe_map] at hx
  exact ⟨x, hx⟩

section TwoTagLim

variable {F G h g : ℝ → ℝ} {a b I : ℝ}

/-- The limit of the two-tag sums along `refinementUltrafilter`. It is the two-tag integral when
that exists (`HasTwoTagRSIntegral.twoTagLim_eq`) and is linear in `h` on integrators with bounded
sums; otherwise its value is a convention. -/
noncomputable def twoTagLim (F G h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  limUnder (refinementUltrafilter : Filter (Finset ℝ))
    fun s => twoTagSum F G h (partitionPts a b s)

/-- **Agreement**: where the two-tag integral exists, `twoTagLim` is the integral. -/
theorem HasTwoTagRSIntegral.twoTagLim_eq (hI : HasTwoTagRSIntegral F G h a b I) :
    twoTagLim F G h a b = I :=
  (Filter.Tendsto.mono_left hI refinementUltrafilter_le).limUnder_eq

theorem abs_twoTagLim_le {R : ℝ} (hR : ∀ s, |twoTagSum F G h (partitionPts a b s)| ≤ R) :
    |twoTagLim F G h a b| ≤ R :=
  le_of_tendsto' (tendsto_refinementUltrafilter hR).abs hR

theorem twoTagLim_add (hh : ∃ R, ∀ s, |twoTagSum F G h (partitionPts a b s)| ≤ R)
    (hg : ∃ R, ∀ s, |twoTagSum F G g (partitionPts a b s)| ≤ R) :
    twoTagLim F G (h + g) a b = twoTagLim F G h a b + twoTagLim F G g a b := by
  obtain ⟨R, hR⟩ := hh
  obtain ⟨R', hR'⟩ := hg
  unfold twoTagLim
  refine Filter.Tendsto.limUnder_eq ?_
  exact ((tendsto_refinementUltrafilter hR).add (tendsto_refinementUltrafilter hR')).congr
    fun s => (twoTagSum_add_right _).symm

theorem twoTagLim_smul (c : ℝ) (hh : ∃ R, ∀ s, |twoTagSum F G h (partitionPts a b s)| ≤ R) :
    twoTagLim F G (c • h) a b = c * twoTagLim F G h a b := by
  obtain ⟨R, hR⟩ := hh
  unfold twoTagLim
  refine Filter.Tendsto.limUnder_eq ?_
  exact ((tendsto_refinementUltrafilter hR).const_mul c).congr
    fun s => (twoTagSum_smul_right c _).symm

end TwoTagLim

/-! ### The Duhamel operator on `ℓ^∞([0, τ])` -/

local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

section Operator

variable {τ : ℝ} {A B : ℝ → ℝ}

/-- A bounded function on `[0, τ]`, extended by `0` outside `[0, τ]`. -/
noncomputable def extendIcc (h : 𝔻[τ]) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc 0 τ then h ⟨x, hx⟩ else 0

theorem extendIcc_of_mem (h : 𝔻[τ]) {x : ℝ} (hx : x ∈ Set.Icc 0 τ) :
    extendIcc h x = h ⟨x, hx⟩ :=
  dite_eq_left hx

theorem extendIcc_coe (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) : extendIcc h t = h t :=
  dite_eq_left t.2

theorem extendIcc_add (h g : 𝔻[τ]) : extendIcc (h + g) = extendIcc h + extendIcc g := by
  funext x
  by_cases hx : x ∈ Set.Icc 0 τ <;> simp [extendIcc, hx]

theorem extendIcc_smul (c : ℝ) (h : 𝔻[τ]) : extendIcc (c • h) = c • extendIcc h := by
  funext x
  by_cases hx : x ∈ Set.Icc 0 τ <;> simp [extendIcc, hx]

theorem abs_extendIcc_le (h : 𝔻[τ]) (x : ℝ) : |extendIcc h x| ≤ ‖h‖ := by
  by_cases hx : x ∈ Set.Icc 0 τ
  · rw [extendIcc_of_mem h hx, ← Real.norm_eq_abs]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero h _
  · simp [extendIcc, hx]

/-- The value `Ψ A B h t`: the ultrafilter limit of the Duhamel sums of `h` on `[0, t]`. -/
noncomputable def psiFun (τ : ℝ) (A B : ℝ → ℝ) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) : ℝ :=
  twoTagLim (productIntegral A 0) (fun x => productIntegral B x t) (extendIcc h) 0 t

/-- The operator-norm bound `6 exp (V(A)) exp (V(B))`, with `V(·)` the total variation on
`[0, τ]`. -/
noncomputable def psiConst (τ : ℝ) (A B : ℝ → ℝ) : ℝ :=
  6 * Real.exp (eVariationOn A (Set.Icc 0 τ)).toReal *
    Real.exp (eVariationOn B (Set.Icc 0 τ)).toReal

theorem psiConst_nonneg : 0 ≤ psiConst τ A B := by
  unfold psiConst
  positivity

theorem variationOnFromTo_sub_eq (hτ : 0 ≤ τ) (A : ℝ → ℝ) :
    variationOnFromTo A (Set.Icc 0 τ) 0 τ - variationOnFromTo A (Set.Icc 0 τ) 0 0 =
      (eVariationOn A (Set.Icc 0 τ)).toReal := by
  rw [variationOnFromTo.self, sub_zero, variationOnFromTo.eq_of_le _ _ hτ, Set.inter_self]

theorem bddSum_psi (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) :
    ∃ R, ∀ s, |twoTagSum (productIntegral A 0) (fun x => productIntegral B x t) (extendIcc h)
      (partitionPts 0 t s)| ≤ R :=
  ⟨_, abs_twoTagSum_duhamel_le (h := extendIcc h) (exists_control_of_boundedVariationOn hA)
    (exists_control_of_boundedVariationOn hB) t.2.1 t.2.2 fun x _ => abs_extendIcc_le h x⟩

theorem abs_psiFun_le (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) :
    |psiFun τ A B h t| ≤ psiConst τ A B * ‖h‖ := by
  have hτ : (0 : ℝ) ≤ τ := t.2.1.trans t.2.2
  have hcA := exists_control_of_boundedVariationOn hA
  have hcB := exists_control_of_boundedVariationOn hB
  have hlim := abs_twoTagLim_le (abs_twoTagSum_duhamel_le (h := extendIcc h) hcA hcB t.2.1 t.2.2
    fun x _ => abs_extendIcc_le h x)
  have eA := productIntegral_le_exp hτ hcA
  have eB := productIntegral_le_exp hτ hcB
  rw [variationOnFromTo_sub_eq hτ] at eA eB
  have pB : 0 ≤ productIntegral (variationOnFromTo B (Set.Icc 0 τ) 0) 0 τ := by
    linarith [one_le_productIntegral_control hτ hcB]
  have hAB := mul_le_mul_of_nonneg_right (mul_le_mul eA eB pB (Real.exp_pos _).le)
    (norm_nonneg h)
  refine hlim.trans ?_
  unfold psiConst
  linarith

theorem psiFun_add (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h g : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) :
    psiFun τ A B (h + g) t = psiFun τ A B h t + psiFun τ A B g t := by
  rw [psiFun, psiFun, psiFun, extendIcc_add]
  exact twoTagLim_add (bddSum_psi hA hB h t) (bddSum_psi hA hB g t)

theorem psiFun_smul (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (c : ℝ) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) :
    psiFun τ A B (c • h) t = c * psiFun τ A B h t := by
  rw [psiFun, psiFun, extendIcc_smul]
  exact twoTagLim_smul c (bddSum_psi hA hB h t)

/-- The Duhamel operator for integrators of bounded variation on `[0, τ]`, as a continuous linear
map on `ℓ^∞([0, τ])`. -/
noncomputable def psiOfBV (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) : 𝔻[τ] →L[ℝ] 𝔻[τ] :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨psiFun τ A B h, memℓp_infty ⟨psiConst τ A B * ‖h‖, by
          rintro _ ⟨t, rfl⟩
          exact (Real.norm_eq_abs _).le.trans (abs_psiFun_le hA hB h t)⟩⟩
      map_add' := fun h g => lp.ext <| by
        rw [lp.coeFn_add]
        funext t
        exact psiFun_add hA hB h g t
      map_smul' := fun c h => lp.ext <| by
        rw [lp.coeFn_smul]
        funext t
        exact psiFun_smul hA hB c h t }
    (psiConst τ A B) fun h =>
      lp.norm_le_of_forall_le (mul_nonneg psiConst_nonneg (norm_nonneg h)) fun t =>
        (Real.norm_eq_abs _).le.trans (abs_psiFun_le hA hB h t)

open Classical in
/-- **The Duhamel operator** `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]` as a continuous
linear map on `ℓ^∞([0, τ])`, for integrators `A`, `B` of bounded variation on `[0, τ]` (and `0`
otherwise). Its value is the Duhamel integral wherever that exists
(`psi_apply_eq_of_hasDuhamelIntegral`); elsewhere it is not specified. -/
noncomputable def psi (τ : ℝ) (A B : ℝ → ℝ) : 𝔻[τ] →L[ℝ] 𝔻[τ] :=
  if hAB : BoundedVariationOn A (Set.Icc 0 τ) ∧ BoundedVariationOn B (Set.Icc 0 τ) then
    psiOfBV hAB.1 hAB.2
  else 0

theorem psi_apply (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) :
    psi τ A B h t = psiFun τ A B h t := by
  rw [psi, dite_eq_left ⟨hA, hB⟩]
  rfl

/-- **`Ψ` is the Duhamel integral wherever the integral exists.** -/
theorem psi_apply_eq_of_hasDuhamelIntegral (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) {I : ℝ}
    (hI : HasDuhamelIntegral A B (extendIcc h) 0 t I) : psi τ A B h t = I := by
  rw [psi_apply hA hB]
  exact HasTwoTagRSIntegral.twoTagLim_eq hI

/-- **Sup-norm bound**: `‖Ψ A B h‖_∞ ≤ 6 exp (V(A)) exp (V(B)) ‖h‖_∞`. -/
theorem norm_psi_apply_le (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (h : 𝔻[τ]) :
    ‖psi τ A B h‖ ≤ psiConst τ A B * ‖h‖ :=
  lp.norm_le_of_forall_le (mul_nonneg psiConst_nonneg (norm_nonneg h)) fun t => by
    rw [psi_apply hA hB, Real.norm_eq_abs]
    exact abs_psiFun_le hA hB h t

/-- **Operator-norm bound**: `‖Ψ A B‖ ≤ 6 exp (V(A)) exp (V(B))`, depending on `A` and `B` only
through their total variations on `[0, τ]`. -/
theorem norm_psi_le (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) : ‖psi τ A B‖ ≤ psiConst τ A B :=
  ContinuousLinearMap.opNorm_le_bound _ psiConst_nonneg (norm_psi_apply_le hA hB)

/-- **Duhamel equation in `ℓ^∞`**: if `d ∈ ℓ^∞([0, τ])` is `B - A` on `[0, τ]`, then
`Ψ A B d t = P(B)(0, t] - P(A)(0, t]`. -/
theorem psi_apply_sub (hA : BoundedVariationOn A (Set.Icc 0 τ))
    (hB : BoundedVariationOn B (Set.Icc 0 τ)) (d : 𝔻[τ])
    (hd : ∀ t : Set.Icc (0 : ℝ) τ, d t = B t - A t) (t : Set.Icc (0 : ℝ) τ) :
    psi τ A B d t = productIntegral B 0 t - productIntegral A 0 t := by
  refine psi_apply_eq_of_hasDuhamelIntegral hA hB d t ?_
  refine HasTwoTagRSIntegral.congr t.2.1 (hasDuhamelIntegral_sub t.2.1
    ((exists_control_of_boundedVariationOn hA).mono le_rfl t.2.2)
    ((exists_control_of_boundedVariationOn hB).mono le_rfl t.2.2)) fun x hx => ?_
  have hxτ : x ∈ Set.Icc 0 τ := ⟨hx.1, hx.2.trans t.2.2⟩
  rw [extendIcc_of_mem d hxτ, hd ⟨x, hxτ⟩]
  rfl

end Operator

/-! ### The three properties as a predicate -/

/-- **The Ψ-CLM hypotheses.** `Ψ` assigns to integrators `A`, `B : ℝ → ℝ` a continuous linear map
on `ℓ^∞([0, τ])` such that, for `A`, `B` of bounded variation on `[0, τ]`:

* `apply_eq`: `Ψ A B h t` is the Duhamel integral `∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]`
  (the refinement limit of the two-tag sums, `h` extended by `0` outside `[0, τ]`) whenever that
  integral exists;
* `norm_le`: `‖Ψ A B‖ ≤ 6 exp (V(A)) exp (V(B))`, `V(·)` the total variation on `[0, τ]`;
* `duhamel`: `Ψ A B d t = P(B)(0, t] - P(A)(0, t]` for `d = B - A` on `[0, τ]`.

Only merged primitives (`twoTagSum`, `partitionPts`, `productIntegral`, `eVariationOn`) appear, so
the predicate can be restated verbatim by a file that does not import this one. -/
structure IsPsiCLM (τ : ℝ) (Ψ : (ℝ → ℝ) → (ℝ → ℝ) → 𝔻[τ] →L[ℝ] 𝔻[τ]) : Prop where
  apply_eq : ∀ A B : ℝ → ℝ, BoundedVariationOn A (Set.Icc 0 τ) →
    BoundedVariationOn B (Set.Icc 0 τ) → ∀ (h : 𝔻[τ]) (t : Set.Icc (0 : ℝ) τ) (I : ℝ),
      Tendsto (fun s => twoTagSum (productIntegral A 0) (fun x => productIntegral B x t)
        (fun x => if hx : x ∈ Set.Icc 0 τ then h ⟨x, hx⟩ else 0) (partitionPts 0 t s))
        atTop (𝓝 I) →
      Ψ A B h t = I
  norm_le : ∀ A B : ℝ → ℝ, BoundedVariationOn A (Set.Icc 0 τ) →
    BoundedVariationOn B (Set.Icc 0 τ) →
      ‖Ψ A B‖ ≤ 6 * Real.exp (eVariationOn A (Set.Icc 0 τ)).toReal *
        Real.exp (eVariationOn B (Set.Icc 0 τ)).toReal
  duhamel : ∀ A B : ℝ → ℝ, BoundedVariationOn A (Set.Icc 0 τ) →
    BoundedVariationOn B (Set.Icc 0 τ) → ∀ d : 𝔻[τ],
      (∀ t : Set.Icc (0 : ℝ) τ, d t = B t - A t) →
      ∀ t : Set.Icc (0 : ℝ) τ, Ψ A B d t = productIntegral B 0 t - productIntegral A 0 t

/-- The Duhamel operator `psi τ` satisfies the Ψ-CLM hypotheses. -/
theorem isPsiCLM_psi (τ : ℝ) : IsPsiCLM τ (psi τ) :=
  ⟨fun _ _ hA hB h t _ hI => psi_apply_eq_of_hasDuhamelIntegral hA hB h t hI,
    fun _ _ hA hB => norm_psi_le hA hB, fun _ _ hA hB d hd t => psi_apply_sub hA hB d hd t⟩

end MathlibExt.Analysis.StieltjesRSIntegralGeneral

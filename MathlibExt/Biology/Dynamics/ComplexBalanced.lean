/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Order.Compact

/-!
# Complex-balanced mass-action systems (Horn–Jackson)

A chemical reaction network on a finite set `S` of species has reactions `r : ρ`, each turning
a source complex `src r : S → ℕ` into a product complex `prod r : S → ℕ`. With rate constants
`k`, mass-action kinetics gives the vector field
`f(c) = ∑_r k r c^{src r} (prod r - src r)`, where `c^y = ∏_s c_s ^ y_s` (`massActionField`).
The stoichiometric subspace `𝒮` is the span of the reaction vectors `prod r - src r`.

Concentrations `c` are **complex balanced** (`IsComplexBalanced`) if at every complex `z` the
total mass-action rate of the reactions with source `z` equals the total rate of the
reactions with product `z`. A complex-balanced `c` is an equilibrium,
`f(c) = 0` (`massActionField_eq_zero_of_isComplexBalanced`, for all real `c` and `k`).

Horn and Jackson showed that once a mass-action system with positive rate constants has one
positive complex-balanced equilibrium `c*`, its positive equilibria are completely described.

## Main results

Throughout, `k r > 0` for all reactions and `c*` is a positive complex-balanced equilibrium.

* `helmholtzRate_nonpos`, `helmholtzRate_eq_zero_iff`: for `c > 0`, the derivative of the
  pseudo-Helmholtz function `G(c) = ∑_s c_s (log c_s - log c*_s - 1)` along the vector field,
  `∑_s (log c_s - log c*_s) f_s(c)` (`helmholtzRate`), is `≤ 0`, and `= 0` exactly at
  equilibria.
* `hasDerivAt_pseudoHelmholtz`, `antitoneOn_pseudoHelmholtz`: this is the time derivative of
  `G` along a positive solution, so `G` is nonincreasing along positive solutions.
* `isComplexBalanced_of_massActionField_eq_zero`: every positive equilibrium is complex
  balanced.
* `positiveEquilibria_eq`: the positive equilibria are exactly the `c > 0` with
  `log c - log c*` orthogonal (for the dot product) to `𝒮`.
* `existsUnique_equilibrium_of_isComplexBalanced`: each positive stoichiometric compatibility
  class `(x₀ + 𝒮) ∩ ℝ_{>0}^S`, `x₀ > 0`, contains exactly one positive equilibrium.

The last two rest on two facts about an arbitrary subspace `W` of `S → ℝ` (Birch's theorem):
`exists_pos_sub_mem_log_orthogonal` (for positive `a`, `b` there is `c > 0` with
`c - b ∈ W` and `log c - log a ⊥ W`) and `eq_of_sub_mem_log_orthogonal` (such `c` is unique).

Existence of a positive complex-balanced equilibrium (for weakly reversible networks of
deficiency zero this is the theorem of Horn and Feinberg, 1972) is not proved here; it is
recorded in `WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`. Asymptotic stability and
global convergence are not covered.

## References

* F. Horn and R. Jackson, "General mass action kinetics", Arch. Rational Mech. Anal. 47 (1972)
  81–116.
* M. W. Birch, "Maximum likelihood in three-way contingency tables", J. R. Stat. Soc. B 25
  (1963) 220–233.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), ch. 15.
* J. Gunawardena, "Chemical reaction network theory for in-silico biologists", lecture notes
  (2003).
-/

@[expose] public section

open Finset Real

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

/-- A chemical reaction network on the species `S` with reactions indexed by `ρ`: reaction `r`
turns the source complex `src r` into the product complex `prod r` (stoichiometric
coefficients). -/
structure ReactionNetwork (S ρ : Type*) where
  /-- The source (reactant) complex of each reaction. -/
  src : ρ → S → ℕ
  /-- The product complex of each reaction. -/
  prod : ρ → S → ℕ

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The stoichiometric subspace: the span of the reaction vectors `prod r - src r`. -/
def stoichiometricSubspace : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range fun r s => (N.prod r s : ℝ) - N.src r s)

/-- The mass-action vector field with rate constants `k`:
`x ↦ ∑_r k r (∏_s x_s ^ (src r s)) (prod r - src r)`. -/
noncomputable def massActionField [Fintype S] [Fintype ρ] (k : ρ → ℝ) (x : S → ℝ) :
    S → ℝ :=
  fun s => ∑ r, k r * (∏ s', x s' ^ N.src r s') * ((N.prod r s : ℝ) - N.src r s)

/-- The mass-action rate `k r * ∏_s c_s ^ (src r s)` of reaction `r` at concentrations `c`. -/
noncomputable def rate [Fintype S] (k : ρ → ℝ) (c : S → ℝ) (r : ρ) : ℝ :=
  k r * ∏ s, c s ^ N.src r s

/-- Concentrations `c` are complex balanced for the rate constants `k`: at every complex `z`,
the total rate of the reactions with source `z` equals the total rate of the reactions with
product `z`. (Complexes that occur in no reaction give `0 = 0`.)

Source: Horn & Jackson (1972); Feinberg (2019), ch. 15. -/
def IsComplexBalanced [Fintype S] [Fintype ρ] (k : ρ → ℝ) (c : S → ℝ) : Prop :=
  ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), N.rate k c r =
    ∑ r ∈ univ.filter (fun r => N.prod r = z), N.rate k c r

/-- The pseudo-Helmholtz function `G(c) = ∑_s c_s (log c_s - log c*_s - 1)` relative to the
reference concentrations `cstar` (Horn & Jackson 1972). It is meaningful for positive `c`
and `cstar`; elsewhere `Real.log` takes junk values. -/
noncomputable def pseudoHelmholtz [Fintype S] (cstar c : S → ℝ) : ℝ :=
  ∑ s, c s * (Real.log (c s) - Real.log (cstar s) - 1)

/-- The rate of change of the pseudo-Helmholtz function along the mass-action vector field,
`∑_s (log c_s - log c*_s) f_s(c)`: the derivative of `pseudoHelmholtz cstar` at `c > 0`
applied to `massActionField k c` (`hasDerivAt_pseudoHelmholtz`). -/
noncomputable def helmholtzRate [Fintype S] [Fintype ρ] (k : ρ → ℝ) (cstar c : S → ℝ) : ℝ :=
  ∑ s, (Real.log (c s) - Real.log (cstar s)) * N.massActionField k c s

/-- Complex balance at `c` rewrites the rate-weighted sum of any function of the products as
the same sum over the sources. -/
private theorem sum_rate_mul_prod_eq [Fintype S] [Fintype ρ] {k : ρ → ℝ} {c : S → ℝ}
    (h : N.IsComplexBalanced k c) (g : (S → ℕ) → ℝ) :
    ∑ r, N.rate k c r * g (N.prod r) = ∑ r, N.rate k c r * g (N.src r) := by
  let T : Finset (S → ℕ) := univ.image N.src ∪ univ.image N.prod
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := T) (g := N.prod)
      (fun r _ => by simp [T]),
    ← Finset.sum_fiberwise_of_maps_to (s := univ) (t := T) (g := N.src)
      (fun r _ => by simp [T])]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h₁ : ∑ r ∈ univ.filter (N.prod · = z), N.rate k c r * g (N.prod r) =
      ∑ r ∈ univ.filter (N.prod · = z), N.rate k c r * g z :=
    Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]
  have h₂ : ∑ r ∈ univ.filter (N.src · = z), N.rate k c r * g (N.src r) =
      ∑ r ∈ univ.filter (N.src · = z), N.rate k c r * g z :=
    Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.1 hr).2]
  rw [h₁, h₂, ← Finset.sum_mul, ← Finset.sum_mul, h z]

/-- A complex-balanced state is an equilibrium of the mass-action system (for all real `c`
and `k`). Source: Horn & Jackson (1972). -/
theorem massActionField_eq_zero_of_isComplexBalanced [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    {c : S → ℝ} (h : N.IsComplexBalanced k c) : N.massActionField k c = 0 := by
  funext s
  have := N.sum_rate_mul_prod_eq h (fun z => (z s : ℝ))
  simp only [massActionField, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
  simpa [rate, sub_eq_zero] using this

/-- The pairing `∑_s z_s μ_s` of a complex `z` with a vector `μ`. -/
private noncomputable def pairing [Fintype S] (μ : S → ℝ) (z : S → ℕ) : ℝ :=
  ∑ s, (z s : ℝ) * μ s

/-- For positive `c` and `c*`, `rate k c r = rate k c* r * exp ⟨src r, log c - log c*⟩`. -/
private theorem rate_eq_mul_exp [Fintype S] {k : ρ → ℝ} {cstar c : S → ℝ}
    (hcstar : ∀ s, 0 < cstar s) (hc : ∀ s, 0 < c s) (r : ρ) :
    N.rate k c r = N.rate k cstar r *
      Real.exp (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r)) := by
  simp only [rate, pairing, Real.exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Real.exp_nat_mul, Real.exp_sub, Real.exp_log (hc s), Real.exp_log (hcstar s), ← mul_pow,
    mul_div_cancel₀ _ (hcstar s).ne']

/-- `helmholtzRate` as a sum over reactions. -/
private theorem helmholtzRate_eq_sum [Fintype S] [Fintype ρ] (k : ρ → ℝ) (cstar c : S → ℝ) :
    N.helmholtzRate k cstar c = ∑ r, N.rate k c r *
      (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.prod r) -
        pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r)) := by
  simp only [helmholtzRate, massActionField, rate, pairing, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `exp b - exp a - exp a (b - a) ≥ 0`, with equality only for `a = b`. -/
private theorem exp_gap_nonneg (a b : ℝ) :
    0 ≤ Real.exp b - Real.exp a - Real.exp a * (b - a) := by
  have h := Real.add_one_le_exp (b - a)
  have he : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  nlinarith [Real.exp_pos a]

/-- The equality case of `exp_gap_nonneg`. -/
private theorem eq_of_exp_gap_eq_zero {a b : ℝ}
    (h : Real.exp b - Real.exp a - Real.exp a * (b - a) = 0) : a = b := by
  by_contra hab
  have hlt := Real.add_one_lt_exp (sub_ne_zero.2 (Ne.symm hab))
  have he : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  rw [he] at h
  nlinarith [Real.exp_pos a]

/-- The Horn–Jackson identity: for positive `c`, `c*` with `c*` complex balanced,
`helmholtzRate = - ∑_r rate k c* r · (exp B_r - exp A_r - exp A_r (B_r - A_r))`. -/
private theorem helmholtzRate_eq_neg_sum [Fintype S] [Fintype ρ] {k : ρ → ℝ} {cstar : S → ℝ}
    (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar) {c : S → ℝ}
    (hc : ∀ s, 0 < c s) :
    N.helmholtzRate k cstar c = -∑ r, N.rate k cstar r *
      (Real.exp (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.prod r)) -
        Real.exp (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r)) -
        Real.exp (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r)) *
          (pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.prod r) -
            pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r))) := by
  set μ : S → ℝ := fun s => Real.log (c s) - Real.log (cstar s)
  have key := N.sum_rate_mul_prod_eq hcb (fun z => Real.exp (pairing μ z))
  rw [helmholtzRate_eq_sum]
  simp only [N.rate_eq_mul_exp hcstar hc, mul_sub, Finset.sum_sub_distrib, key]
  rw [← sub_eq_zero]
  simp only [neg_sub, mul_assoc]
  ring

/-- If `A_r = B_r` for every reaction, then `c` is complex balanced. -/
private theorem isComplexBalanced_of_pairing_eq [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    {c : S → ℝ} (hc : ∀ s, 0 < c s)
    (h : ∀ r, pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r) =
      pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.prod r)) :
    N.IsComplexBalanced k c := by
  intro z
  set μ : S → ℝ := fun s => Real.log (c s) - Real.log (cstar s)
  have h₁ : ∑ r ∈ univ.filter (N.src · = z), N.rate k c r =
      ∑ r ∈ univ.filter (N.src · = z), N.rate k cstar r * Real.exp (pairing μ z) :=
    Finset.sum_congr rfl fun r hr => by
      rw [N.rate_eq_mul_exp hcstar hc, (Finset.mem_filter.1 hr).2]
  have h₂ : ∑ r ∈ univ.filter (N.prod · = z), N.rate k c r =
      ∑ r ∈ univ.filter (N.prod · = z), N.rate k cstar r * Real.exp (pairing μ z) :=
    Finset.sum_congr rfl fun r hr => by
      rw [N.rate_eq_mul_exp hcstar hc, h r, (Finset.mem_filter.1 hr).2]
  rw [h₁, h₂, ← Finset.sum_mul, ← Finset.sum_mul, hcb z]

/-- Mass-action rates are positive at positive rate constants and concentrations. -/
private theorem rate_pos [Fintype S] {k : ρ → ℝ} (hk : ∀ r, 0 < k r) {c : S → ℝ}
    (hc : ∀ s, 0 < c s) (r : ρ) : 0 < N.rate k c r :=
  mul_pos (hk r) (Finset.prod_pos fun s _ => pow_pos (hc s) _)

/-- If the Horn–Jackson rate vanishes, `A_r = B_r` for every reaction. -/
private theorem pairing_eq_of_helmholtzRate_eq_zero [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    (hk : ∀ r, 0 < k r) {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s)
    (hcb : N.IsComplexBalanced k cstar) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    (h0 : N.helmholtzRate k cstar c = 0) (r : ρ) :
    pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.src r) =
      pairing (fun s => Real.log (c s) - Real.log (cstar s)) (N.prod r) := by
  rw [N.helmholtzRate_eq_neg_sum hcstar hcb hc, neg_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun r _ =>
      mul_nonneg (N.rate_pos hk hcstar r).le (exp_gap_nonneg _ _)] at h0
  exact eq_of_exp_gap_eq_zero
    ((mul_eq_zero.1 (h0 r (Finset.mem_univ r))).resolve_left (N.rate_pos hk hcstar r).ne')

/-- **Horn–Jackson inequality.** If `c*` is a positive complex-balanced equilibrium for
positive rate constants, the pseudo-Helmholtz function does not increase along the
mass-action vector field at any positive `c`. Source: Horn & Jackson (1972);
Feinberg (2019), ch. 15. -/
theorem helmholtzRate_nonpos [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) : N.helmholtzRate k cstar c ≤ 0 := by
  rw [N.helmholtzRate_eq_neg_sum hcstar hcb hc, neg_nonpos]
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg (N.rate_pos hk hcstar r).le (exp_gap_nonneg _ _)

/-- **Equality in the Horn–Jackson inequality.** Under the hypotheses of
`helmholtzRate_nonpos`, the rate of change of the pseudo-Helmholtz function vanishes at a
positive `c` exactly when `c` is an equilibrium. Source: Horn & Jackson (1972). -/
theorem helmholtzRate_eq_zero_iff [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    {c : S → ℝ} (hc : ∀ s, 0 < c s) :
    N.helmholtzRate k cstar c = 0 ↔ N.massActionField k c = 0 := by
  refine ⟨fun h0 => N.massActionField_eq_zero_of_isComplexBalanced
    (N.isComplexBalanced_of_pairing_eq hcstar hcb hc
      (N.pairing_eq_of_helmholtzRate_eq_zero hk hcstar hcb hc h0)), fun hf => ?_⟩
  simp [helmholtzRate, hf]

/-- **Horn–Jackson.** If a mass-action system with positive rate constants has a positive
complex-balanced equilibrium, then every positive equilibrium is complex balanced.
Source: Horn & Jackson (1972); Feinberg (2019), ch. 15. -/
theorem isComplexBalanced_of_massActionField_eq_zero [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    (hk : ∀ r, 0 < k r) {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s)
    (hcb : N.IsComplexBalanced k cstar) {c : S → ℝ} (hc : ∀ s, 0 < c s)
    (hf : N.massActionField k c = 0) : N.IsComplexBalanced k c :=
  N.isComplexBalanced_of_pairing_eq hcstar hcb hc
    (N.pairing_eq_of_helmholtzRate_eq_zero hk hcstar hcb hc
      ((N.helmholtzRate_eq_zero_iff hk hcstar hcb hc).2 hf))

/-- The dot product of `μ` with the reaction vector of `r` is `B_r - A_r`. -/
private theorem dotProduct_reactionVector [Fintype S] (μ : S → ℝ) (r : ρ) :
    μ ⬝ᵥ (fun s => (N.prod r s : ℝ) - N.src r s) = pairing μ (N.prod r) - pairing μ (N.src r) := by
  simp only [dotProduct, pairing, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Horn–Jackson: the positive equilibria.** If `c*` is a positive complex-balanced
equilibrium for positive rate constants, the positive equilibria are exactly the positive
`c` whose `log c - log c*` is orthogonal (for the dot product) to the stoichiometric
subspace. Source: Horn & Jackson (1972); Feinberg (2019), ch. 15. -/
theorem positiveEquilibria_eq [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar) :
    {c : S → ℝ | (∀ s, 0 < c s) ∧ N.massActionField k c = 0} =
      {c | (∀ s, 0 < c s) ∧ ∀ v ∈ N.stoichiometricSubspace,
        (fun s => Real.log (c s) - Real.log (cstar s)) ⬝ᵥ v = 0} := by
  ext c
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hc => ⟨fun hf v hv => ?_, fun horth => ?_⟩
  · have hpe := N.pairing_eq_of_helmholtzRate_eq_zero hk hcstar hcb hc
      ((N.helmholtzRate_eq_zero_iff hk hcstar hcb hc).2 hf)
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨r, rfl⟩ := hv
      rw [dotProduct_reactionVector, hpe r, sub_self]
    | zero => exact dotProduct_zero _
    | add u w _ _ hu hw => rw [dotProduct_add, hu, hw, add_zero]
    | smul a u _ hu => rw [dotProduct_smul, hu, smul_zero]
  · refine N.massActionField_eq_zero_of_isComplexBalanced
      (N.isComplexBalanced_of_pairing_eq hcstar hcb hc fun r => ?_)
    have := horth _ (Submodule.subset_span ⟨r, rfl⟩)
    rw [dotProduct_reactionVector, sub_eq_zero] at this
    exact this.symm

end ReactionNetwork

/-- In finite dimension a subspace of `S → ℝ` is its own double orthogonal complement for the
dot product. -/
private theorem mem_of_forall_dotProduct_eq_zero [Fintype S] (W : Submodule ℝ (S → ℝ))
    {w : S → ℝ} (h : ∀ μ : S → ℝ, (∀ v ∈ W, μ ⬝ᵥ v = 0) → w ⬝ᵥ μ = 0) : w ∈ W := by
  let W' : Submodule ℝ (EuclideanSpace ℝ S) :=
    W.comap (WithLp.linearEquiv 2 ℝ (S → ℝ)).toLinearMap
  have hw : WithLp.toLp 2 w ∈ W'ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_orthogonal] at hu
    have hu' : ∀ v ∈ W, WithLp.ofLp u ⬝ᵥ v = 0 := by
      intro v hv
      have := hu (WithLp.toLp 2 v) hv
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa [dotProduct_comm] using this
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa using h _ hu'
  rw [Submodule.orthogonal_orthogonal] at hw
  exact hw

/-- A coercivity bound: `a e^t - b t ≥ m |t| - (b + 1)^2 / (2a)` for `0 < a`, `0 < m ≤ b`,
`m ≤ 1`. -/
private theorem coercive_bound {a b m : ℝ} (ha : 0 < a) (hmb : m ≤ b) (hm1 : m ≤ 1) (t : ℝ) :
    m * |t| - (b + 1) ^ 2 / (2 * a) ≤ a * Real.exp t - b * t := by
  have hC : 0 ≤ (b + 1) ^ 2 / (2 * a) := by positivity
  have he := Real.exp_pos t
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have hq := Real.quadratic_le_exp_of_nonneg ht
    have key : (b + 1) * t - (b + 1) ^ 2 / (2 * a) ≤ a * (t ^ 2 / 2) := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (a * t - (b + 1))]
    nlinarith [mul_le_mul_of_nonneg_left hq ha.le]
  · rw [abs_of_nonpos ht]
    nlinarith [mul_pos ha he]

/-- **Birch's theorem, existence.** For any subspace `W` of `S → ℝ` and positive `a`, `b`
there is a positive `c` with `c - b ∈ W` and `log c - log a` orthogonal to `W` (for the dot
product). Source: Birch (1963); Horn & Jackson (1972). -/
theorem exists_pos_sub_mem_log_orthogonal [Fintype S] (W : Submodule ℝ (S → ℝ))
    {a b : S → ℝ} (ha : ∀ s, 0 < a s) (hb : ∀ s, 0 < b s) :
    ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ c - b ∈ W ∧
      ∀ v ∈ W, (fun s => Real.log (c s) - Real.log (a s)) ⬝ᵥ v = 0 := by
  -- The orthogonal complement `V` of `W` and the strictly convex, coercive `F` on it.
  let V : Submodule ℝ (S → ℝ) :=
    { carrier := {μ | ∀ v ∈ W, μ ⬝ᵥ v = 0}
      add_mem' := fun hμ hν v hv => by rw [add_dotProduct, hμ v hv, hν v hv, add_zero]
      zero_mem' := fun v _ => zero_dotProduct v
      smul_mem' := fun r μ hμ v hv => by rw [smul_dotProduct, hμ v hv, smul_zero] }
  let F : (S → ℝ) → ℝ := fun μ => ∑ s, (a s * Real.exp (μ s) - b s * μ s)
  have hFc : Continuous F := by fun_prop
  -- A uniform slope `m ≤ min_s (b s) ∧ m ≤ 1`.
  set m : ℝ := 1 / (1 + ∑ s, 1 / b s) with hm_def
  have hsum : 0 ≤ ∑ s, 1 / b s := Finset.sum_nonneg fun s _ => (one_div_pos.2 (hb s)).le
  have hm : 0 < m := by positivity
  have hmb : ∀ s, m ≤ b s := by
    intro s
    have h1 : 1 / b s ≤ ∑ s, 1 / b s :=
      Finset.single_le_sum (f := fun s => 1 / b s)
        (fun s _ => (one_div_pos.2 (hb s)).le) (Finset.mem_univ s)
    rw [hm_def, div_le_iff₀ (by positivity)]
    have := hb s
    rw [div_le_iff₀ this] at h1
    nlinarith
  have hm1 : m ≤ 1 := by
    rw [hm_def, div_le_one (by positivity)]
    linarith
  set C : ℝ := ∑ s, (b s + 1) ^ 2 / (2 * a s)
  have hFbound : ∀ μ, m * ‖μ‖ - C ≤ F μ := by
    intro μ
    have hnorm : ‖μ‖ ≤ ∑ s, |μ s| := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun s _ => abs_nonneg _)).2 fun s => ?_
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun s => |μ s|) (fun s _ => abs_nonneg _)
        (Finset.mem_univ s)
    calc m * ‖μ‖ - C ≤ ∑ s, (m * |μ s| - (b s + 1) ^ 2 / (2 * a s)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          gcongr
      _ ≤ F μ := Finset.sum_le_sum fun s _ => coercive_bound (ha s) (hmb s) hm1 (μ s)
  -- `F` attains its minimum on `V`.
  have hlim : Filter.Tendsto (fun ν : V => F ν) (Filter.cocompact V) Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun ν => hFbound ν) ?_
    refine Filter.tendsto_atTop_add_const_right _ (-C) ?_
    exact (tendsto_norm_cocompact_atTop.const_mul_atTop hm).congr fun ν => rfl
  obtain ⟨⟨μ, hμV⟩, hmin⟩ :=
    (hFc.comp continuous_subtype_val).exists_forall_le (β := V) hlim
  -- First-order condition: `w = a e^μ - b` is orthogonal to `V`.
  let w : S → ℝ := fun s => a s * Real.exp (μ s) - b s
  have hw : ∀ v ∈ V, w ⬝ᵥ v = 0 := by
    intro v hv
    have hderiv : HasDerivAt (fun t : ℝ => F (μ + t • v)) (w ⬝ᵥ v) 0 := by
      simp only [F, w, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine HasDerivAt.fun_sum fun s _ => ?_
      have hl : HasDerivAt (fun t : ℝ => μ s + t * v s) (v s) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v s)).const_add (μ s)
      have := ((hl.exp.const_mul (a s)).sub (hl.const_mul (b s)))
      convert this using 1
      simp only [zero_mul, add_zero]
      ring
    exact IsLocalMin.hasDerivAt_eq_zero
      (Filter.Eventually.of_forall fun t => by
        simpa using hmin ⟨μ + t • v, V.add_mem hμV (V.smul_mem t hv)⟩) hderiv
  refine ⟨fun s => a s * Real.exp (μ s), fun s => mul_pos (ha s) (Real.exp_pos _), ?_, ?_⟩
  · exact mem_of_forall_dotProduct_eq_zero W fun ν hν => hw ν hν
  · intro v hv
    have hlog : (fun s => Real.log (a s * Real.exp (μ s)) - Real.log (a s)) = μ := by
      funext s
      rw [Real.log_mul (ha s).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    rw [hlog]
    exact hμV v hv

/-- **Birch's theorem, uniqueness.** Two positive vectors whose difference lies in a subspace
`W` and whose logarithms differ by a vector orthogonal to `W` are equal.
Source: Birch (1963); Horn & Jackson (1972). -/
theorem eq_of_sub_mem_log_orthogonal [Fintype S] {W : Submodule ℝ (S → ℝ)} {c d : S → ℝ}
    (hc : ∀ s, 0 < c s) (hd : ∀ s, 0 < d s) (hW : c - d ∈ W)
    (horth : ∀ v ∈ W, (fun s => Real.log (c s) - Real.log (d s)) ⬝ᵥ v = 0) : c = d := by
  have h0 := horth _ hW
  simp only [dotProduct, Pi.sub_apply] at h0
  have hnn : ∀ s ∈ univ, 0 ≤ (Real.log (c s) - Real.log (d s)) * (c s - d s) := by
    intro s _
    rcases le_total (c s) (d s) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.2 (Real.log_le_log (hc s) h)) (sub_nonpos.2 h)
    · exact mul_nonneg (sub_nonneg.2 (Real.log_le_log (hd s) h)) (sub_nonneg.2 h)
  funext s
  have hs := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 s (Finset.mem_univ s)
  rcases mul_eq_zero.1 hs with h | h
  · exact Real.log_injOn_pos (hc s) (hd s) (sub_eq_zero.1 h)
  · exact sub_eq_zero.1 h

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- **Horn–Jackson: one equilibrium per compatibility class.** If a mass-action system with
positive rate constants has a positive complex-balanced equilibrium, then each positive
stoichiometric compatibility class `(x₀ + 𝒮) ∩ ℝ_{>0}^S`, `x₀ > 0`, contains exactly one
positive equilibrium. Source: Horn & Jackson (1972); Feinberg (2019), ch. 15. -/
theorem existsUnique_equilibrium_of_isComplexBalanced [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    (hk : ∀ r, 0 < k r) {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s)
    (hcb : N.IsComplexBalanced k cstar) {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    ∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0 := by
  have hE := N.positiveEquilibria_eq hk hcstar hcb
  obtain ⟨c, hc, hcW, horth⟩ :=
    exists_pos_sub_mem_log_orthogonal N.stoichiometricSubspace hcstar hx₀
  have hcE : c ∈ {c : S → ℝ | (∀ s, 0 < c s) ∧ N.massActionField k c = 0} := by
    rw [hE]; exact ⟨hc, horth⟩
  refine ⟨c, ⟨hc, hcW, hcE.2⟩, fun y ⟨hy, hyW, hyf⟩ => ?_⟩
  have hyE : y ∈ {c : S → ℝ | (∀ s, 0 < c s) ∧ N.massActionField k c = 0} := ⟨hy, hyf⟩
  rw [hE] at hyE
  refine eq_of_sub_mem_log_orthogonal (W := N.stoichiometricSubspace) hy hc ?_
    fun v hv => ?_
  · simpa using N.stoichiometricSubspace.sub_mem hyW hcW
  · have h := congrArg₂ (· - ·) (hyE.2 v hv) (horth v hv)
    simp only [sub_zero, ← sub_dotProduct] at h
    convert h using 2
    funext s
    simp only [Pi.sub_apply]
    ring

/-- The pseudo-Helmholtz function has time derivative `helmholtzRate` along a solution of the
mass-action system, at any time where the solution is positive. -/
theorem hasDerivAt_pseudoHelmholtz [Fintype S] [Fintype ρ] {k : ρ → ℝ} (cstar : S → ℝ)
    {x : ℝ → S → ℝ} {t : ℝ} (hx : HasDerivAt x (N.massActionField k (x t)) t)
    (hpos : ∀ s, 0 < x t s) :
    HasDerivAt (fun τ => pseudoHelmholtz cstar (x τ)) (N.helmholtzRate k cstar (x t)) t := by
  unfold pseudoHelmholtz helmholtzRate
  refine HasDerivAt.fun_sum fun s _ => ?_
  have hs : HasDerivAt (fun τ => x τ s) (N.massActionField k (x t) s) t := hasDerivAt_pi.1 hx s
  have hl := ((hs.log (hpos s).ne').sub_const (Real.log (cstar s))).sub_const 1
  convert hs.mul hl using 1
  rw [mul_div_cancel₀ _ (hpos s).ne']
  ring

/-- **The pseudo-Helmholtz function does not increase along solutions.** Along a solution of a
mass-action system with positive rate constants and a positive complex-balanced equilibrium
`c*`, positive and differentiable (two-sided) at every `t ≥ 0`, `G(x t)` is nonincreasing on
`[0, ∞)`.
Source: Horn & Jackson (1972). -/
theorem antitoneOn_pseudoHelmholtz [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {cstar : S → ℝ} (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    {x : ℝ → S → ℝ} (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
    (hpos : ∀ t, 0 ≤ t → ∀ s, 0 < x t s) :
    AntitoneOn (fun t => pseudoHelmholtz cstar (x t)) (Set.Ici 0) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (fun τ => pseudoHelmholtz cstar (x τ))
      (N.helmholtzRate k cstar (x t)) t := fun t ht =>
    N.hasDerivAt_pseudoHelmholtz cstar (hx t ht) (hpos t ht)
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) fun t ht => ?_
  · rw [interior_Ici] at ht
    exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at ht
    rw [(hd t (le_of_lt ht)).deriv]
    exact N.helmholtzRate_nonpos hk hcstar hcb (hpos t (le_of_lt ht))

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced

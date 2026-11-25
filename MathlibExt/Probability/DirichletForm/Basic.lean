/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.MetricSpace.Lipschitz

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetric forms, closability and Dirichlet forms on `L²(X; m)`

This file sets up the basic notions of the theory of Dirichlet forms as in
M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd
revised and extended edition, de Gruyter Studies in Mathematics 19, 2011, §1.1:

* a **symmetric form** on `L²(X; m)`: a nonnegative definite symmetric bilinear form `E` on a
  dense linear subspace `D[E]` (conditions (E.1), (E.2));
* `E₁(u, v) = E(u, v) + (u, v)`, and the form is **closed** when `D[E]` is complete for `E₁`
  (condition (E.3));
* the form is **closable** when it satisfies condition (1.1.2): an `E`-Cauchy sequence in `D[E]`
  tending to `0` in `L²` has energy tending to `0`;
* the **unit contraction** `u ↦ (0 ∨ u) ∧ 1` operates on `E` when `D[E]` is stable under it and it
  does not increase the energy (condition (E.4)′, `UnitContractionOperates`);
* a **Dirichlet form** is a closed symmetric form on which the unit contraction operates.

FOT define "Markovian" by the ε-regularised condition (E.4). They note (§1.1) that
(E.4)″ ⇒ (E.4)′ ⇒ (E.4), that the three are equivalent for closed forms (Theorem 1.4.1), and that
Markovian closable forms that are not closed need not satisfy (E.4)′. So `UnitContractionOperates`
is FOT's "Markovian" only for closed forms; for closable forms it is strictly stronger. Dirichlet
forms are closed, so FOT's definition of a Dirichlet form is recovered. The bilinear map is defined
on all of `L²`, but only its values on `D[E]` enter the definitions (a bilinear form on a subspace
always extends linearly).

The non-symmetric theory of Z.-M. Ma and M. Röckner (*Introduction to the Theory of
(Non-Symmetric) Dirichlet Forms*, Springer, 1992) replaces symmetry by a sector condition and
asks the unit contraction condition in both orders; see M. Röckner and B. Schmuland,
*Canad. J. Math.* 47 (1995), Definitions 0.2 and 0.3. It is not formalised here.

## Main definitions

* `SymmetricForm m`, `SymmetricForm.energyOne`.
* `SymmetricForm.IsClosed`, `SymmetricForm.IsClosable`.
* `unitContractionLp`, `SymmetricForm.UnitContractionOperates`, `SymmetricForm.IsDirichletForm`.

## Main results

* `SymmetricForm.isClosable_of_le`: a form with a closed extension is closable (FOT §1.1).
* `SymmetricForm.isClosable_of_isClosed`: closed forms are closable.
* `unitContractionLp_ae_eq`, `norm_unitContractionLp_le`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace MathlibExt.Probability.DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- **Symmetric form on `L²(X; m)`.** A dense linear subspace `D[E]` of `L²(X; m)` and a bilinear
form `E` that is symmetric and nonnegative on `D[E]` (Fukushima, Oshima and Takeda, *Dirichlet
Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1, conditions (E.1) and (E.2)). The
bilinear map is given on all of `L²`; only its values on `D[E]` matter. -/
structure SymmetricForm (m : Measure X) where
  /-- The domain `D[E]`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The domain is dense in `L²(X; m)`. -/
  dense : Dense (domain : Set (Lp ℝ 2 m))
  /-- The bilinear form. -/
  form : Lp ℝ 2 m →ₗ[ℝ] Lp ℝ 2 m →ₗ[ℝ] ℝ
  /-- Symmetry on the domain. -/
  symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- Nonnegativity on the domain. -/
  nonneg : ∀ u ∈ domain, 0 ≤ form u u

namespace SymmetricForm

variable (E : SymmetricForm m)

/-- **The form `E₁`.** `E₁(u, v) = E(u, v) + (u, v)_{L²}` (Fukushima, Oshima and Takeda,
*Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, equation (1.1.1) with `α = 1`). -/
noncomputable def energyOne (u v : Lp ℝ 2 m) : ℝ :=
  E.form u v + ⟪u, v⟫

/-- **Closed symmetric form.** Every `E₁`-Cauchy sequence in `D[E]` converges in `E₁` to an
element of `D[E]` (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
Processes*, 2nd ed., 2011, §1.1, condition (E.3)). -/
def IsClosed : Prop :=
  ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ E.domain) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, E.energyOne (u n - u k) (u n - u k) < ε) →
    ∃ w ∈ E.domain, Tendsto (fun n => E.energyOne (u n - w) (u n - w)) atTop (𝓝 0)

/-- **Closable symmetric form.** If `uₙ ∈ D[E]` is `E`-Cauchy and `uₙ → 0` in `L²`, then
`E(uₙ, uₙ) → 0` (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
2nd ed., 2011, §1.1, condition (1.1.2)); equivalently (FOT, §1.1) the form has a closed extension,
and then a smallest one. -/
def IsClosable : Prop :=
  ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ E.domain) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, E.form (u n - u k) (u n - u k) < ε) →
    Tendsto (fun n => ‖u n‖) atTop (𝓝 0) →
    Tendsto (fun n => E.form (u n) (u n)) atTop (𝓝 0)

/-- **`E₁` dominates the squared norm.** For `u ∈ D[E]`, `‖u‖² ≤ E₁(u, u)`. -/
theorem norm_sq_le_energyOne {u : Lp ℝ 2 m} (hu : u ∈ E.domain) : ‖u‖ ^ 2 ≤ E.energyOne u u := by
  unfold energyOne
  rw [real_inner_self_eq_norm_sq]
  linarith [E.nonneg u hu]

/-- **`E₁` dominates `E`.** `E(u, u) ≤ E₁(u, u)` for every `u`. -/
theorem form_le_energyOne (u : Lp ℝ 2 m) : E.form u u ≤ E.energyOne u u := by
  unfold energyOne
  rw [real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖u‖]

/-- **A form with a closed extension is closable.** If `E'` is a closed symmetric form with
`D[E] ⊆ D[E']` and `E' = E` on `D[E]`, then `E` is closable (Fukushima, Oshima and Takeda,
*Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1: "a necessary and
sufficient condition for a symmetric form to possess a closed extension is that the symmetric
form is closable"; this is the necessity). -/
theorem isClosable_of_le {E' : SymmetricForm m} (hle : E.domain ≤ E'.domain)
    (heq : ∀ u ∈ E.domain, ∀ v ∈ E.domain, E'.form u v = E.form u v) (hE' : E'.IsClosed) :
    E.IsClosable := by
  intro u hu hcau h0
  have hu' : ∀ n, u n ∈ E'.domain := fun n => hle (hu n)
  -- `u` is `E'₁`-Cauchy.
  have hcau' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      E'.energyOne (u n - u k) (u n - u k) < ε := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hcau (ε / 2) (by positivity)
    set δ : ℝ := min 1 (ε / 16) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε / 16 := min_le_right _ _
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h0) δ hδ0
    refine ⟨max N₁ N₂, fun n hn k hk => ?_⟩
    have hn₂ : ‖u n‖ < δ := by
      have := hN₂ n (le_of_max_le_right hn); rwa [Real.dist_eq, sub_zero, abs_norm] at this
    have hk₂ : ‖u k‖ < δ := by
      have := hN₂ k (le_of_max_le_right hk); rwa [Real.dist_eq, sub_zero, abs_norm] at this
    have hnorm : ‖u n - u k‖ < 2 * δ :=
      (norm_sub_le _ _).trans_lt (by linarith)
    have hsq : ‖u n - u k‖ ^ 2 < ε / 2 := by
      have h0' : 0 ≤ ‖u n - u k‖ := norm_nonneg _
      nlinarith
    have hform := hN₁ n (le_of_max_le_left hn) k (le_of_max_le_left hk)
    unfold energyOne
    rw [real_inner_self_eq_norm_sq,
      heq _ (E.domain.sub_mem (hu n) (hu k)) _ (E.domain.sub_mem (hu n) (hu k))]
    linarith
  obtain ⟨w, hw, hlim⟩ := hE' u hu' hcau'
  -- `uₙ → w` in `L²`, hence `w = 0`.
  have hnorm_lim : Tendsto (fun n => ‖u n - w‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => ‖u n - w‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _)
        (fun n => E'.norm_sq_le_energyOne (E'.domain.sub_mem (hu' n) hw)) hlim
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hw0 : w = 0 := by
    have h1 : Tendsto u atTop (𝓝 w) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_lim
    have h2 : Tendsto u atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr h0
    exact tendsto_nhds_unique h1 h2
  subst hw0
  refine squeeze_zero (fun n => E.nonneg _ (hu n)) (fun n => ?_) hlim
  rw [sub_zero, ← heq _ (hu n) _ (hu n)]
  exact E'.form_le_energyOne (u n)

/-- **Closed forms are closable.** A closed symmetric form satisfies condition (1.1.2) of
Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011,
§1.1 (it is its own closed extension). -/
theorem isClosable_of_isClosed (hE : E.IsClosed) : E.IsClosable :=
  isClosable_of_le E (E' := E) le_rfl (fun _ _ _ _ => rfl) hE

end SymmetricForm

/-- **The unit clamp `t ↦ (0 ∨ t) ∧ 1` is `1`-Lipschitz.** -/
theorem lipschitzWith_unitClamp : LipschitzWith 1 fun t : ℝ => max 0 (min t 1) :=
  (LipschitzWith.id.min_const 1).const_max 0

/-- **Unit contraction on `L²`.** For `u ∈ L²(X; m)`, the class of `(0 ∨ u) ∧ 1`, defined by
composing with the `1`-Lipschitz map `t ↦ max 0 (min t 1)`, which fixes `0` (Fukushima, Oshima and
Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1, condition (E.4)′). -/
noncomputable def unitContractionLp (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  lipschitzWith_unitClamp.compLp (by simp) u

/-- **The unit contraction on `L²` is pointwise.** `(0 ∨ u) ∧ 1` is a.e. equal to
`x ↦ max 0 (min (u x) 1)`. -/
theorem unitContractionLp_ae_eq (u : Lp ℝ 2 m) :
    unitContractionLp u =ᵐ[m] fun x => max 0 (min (u x) 1) :=
  LipschitzWith.coeFn_compLp _ _ u

/-- **The unit contraction does not increase the `L²` norm.** `‖(0 ∨ u) ∧ 1‖₂ ≤ ‖u‖₂`, since
`|(0 ∨ t) ∧ 1| ≤ |t|` pointwise. -/
theorem norm_unitContractionLp_le (u : Lp ℝ 2 m) : ‖unitContractionLp u‖ ≤ ‖u‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [unitContractionLp_ae_eq u] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_max_left 0 (min (u x) 1), abs_nonneg (u x)]
  · exact max_le (abs_nonneg _) ((min_le_left _ _).trans (le_abs_self _))

namespace SymmetricForm

variable (E : SymmetricForm m)

/-- **The unit contraction operates on a form.** For every `u ∈ D[E]`, the unit contraction
`v = (0 ∨ u) ∧ 1` lies in `D[E]` and `E(v, v) ≤ E(u, u)` (Fukushima, Oshima and Takeda,
*Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1, condition (E.4)′). By
their Theorem 1.4.1 this is equivalent, for closed forms, to their Markov condition (E.4). For
closable forms that are not closed it is strictly stronger than (E.4): FOT §1.1 note that
Markovian closable forms need not satisfy (E.4)′. -/
def UnitContractionOperates : Prop :=
  ∀ u ∈ E.domain, unitContractionLp u ∈ E.domain ∧
    E.form (unitContractionLp u) (unitContractionLp u) ≤ E.form u u

/-- **Dirichlet form.** A closed symmetric form on `L²(X; m)` on which the unit contraction
operates (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd
ed., 2011, §1.1: "a Dirichlet form is by definition a symmetric form on `L²(X; m)` which is not
only Markovian but also closed"; for closed forms Markovian (E.4) and the unit contraction
condition (E.4)′ are equivalent, as FOT note on the same page and prove in Theorem 1.4.1). -/
def IsDirichletForm : Prop :=
  E.IsClosed ∧ E.UnitContractionOperates

end SymmetricForm

end MathlibExt.Probability.DirichletForm

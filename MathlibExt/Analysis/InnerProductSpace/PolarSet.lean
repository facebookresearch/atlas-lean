/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

/-!
# Polar of a set in a real inner-product space

This module defines the convex-geometry **polar** of a set `A` in a real
inner-product space `E`:
`A° = {y : E | ∀ x ∈ A, ⟪x, y⟫_ℝ ≤ 1}`.

The convention is the one-sided real inner-product bound `⟪x, y⟫_ℝ ≤ 1`, as used
in convex geometry and polar duality (the bipolar theorem for convex bodies).

This is deliberately distinct from the API already in Mathlib:

* `LinearMap.polar B A = {y | ∀ x ∈ A, ‖B x y‖ ≤ 1}` takes the **absolute
  value / norm** `‖·‖ ≤ 1` (the balanced/symmetric polar). Specialized to an
  inner-product pairing it can be compared with `polarSet` in the same space,
  and the two agree when `A` is closed under negation (in particular, when `A`
  is balanced). `NormedSpace.polar A` instead lives in the continuous dual
  space; its preimage under the inner-product embedding `E → (E →L[ℝ] ℝ)` is
  `{y | ∀ x ∈ A, |⟪x, y⟫_ℝ| ≤ 1}` (a norm-based, hence balanced, variant),
  which agrees with the one-sided `polarSet A` only when `A` is closed under
  negation. Without that hypothesis the two are distinct comparable
  constructions, and identifying the dual with `E` itself would additionally
  need completeness/Riesz hypotheses not assumed here.
* `Set.innerDualCone` / `PointedCone.dual` use the sign condition `0 ≤ ⟪x, y⟫`
  (the inner dual cone), not `≤ 1`.
* `Submodule.dualAnnihilator` uses the linear condition `= 0`.

The inner product is written `inner ℝ x y`, i.e. `𝕜 = ℝ` made explicit.
-/

namespace MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Polar of a set.** Let $E$ be a real inner product space. The polar of a set $A \subseteq E$
is the set $A^\circ = \{y \in E : \langle x, y \rangle \le 1 \text{ for all } x \in A\}$. This
uses the one-sided bound $\langle x, y \rangle \le 1$, not $|\langle x, y \rangle| \le 1$. -/
def polarSet (A : Set E) : Set E := {y | ∀ x ∈ A, inner ℝ x y ≤ 1}

/-- **Membership in the polar.** Let $E$ be a real inner product space, $A \subseteq E$ and
$y \in E$. Then $y$ lies in the polar $A^\circ$ of $A$ if and only if $\langle x, y \rangle \le 1$
for every $x \in A$. -/
theorem mem_polarSet {A : Set E} {y : E} :
    y ∈ polarSet A ↔ ∀ x ∈ A, inner ℝ x y ≤ 1 := Iff.rfl

/-- **Polar of the empty set.** In a real inner product space $E$, the polar of the empty
set is all of $E$, since the defining condition is vacuous. -/
@[simp] theorem polarSet_empty : polarSet (∅ : Set E) = Set.univ := by
  simp [polarSet]

/-- **The origin lies in every polar.** In a real inner product space $E$, for every set
$A \subseteq E$ the origin $0$ lies in the polar $A^\circ$ of $A$, since
$\langle x, 0 \rangle = 0 \le 1$ for every $x \in A$. -/
@[simp] theorem zero_mem_polarSet (A : Set E) : (0 : E) ∈ polarSet A := by
  intro x _
  simp

/-- **The polar reverses inclusion.** Let $A$ and $B$ be subsets of a real inner product space.
If $A \subseteq B$, then the polar $B^\circ$ of $B$ is contained in the polar $A^\circ$ of $A$. -/
theorem polarSet_subset_polarSet {A B : Set E} (h : A ⊆ B) :
    polarSet B ⊆ polarSet A := fun _ hy x hx => hy x (h hx)

end MetaMathlibExt

namespace MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The closed unit ball is self-polar.** In a real inner product space $E$, the polar of the
closed unit ball $\{x \in E : \|x\| \le 1\}$ is the closed unit ball itself. -/
theorem polarSet_closedUnitBall :
    polarSet (Metric.closedBall (0 : E) 1) = Metric.closedBall 0 1 := by
  ext y
  constructor
  · intro hy
    have h := hy (‖y‖⁻¹ • y) (inv_norm_smul_mem_unitClosedBall y)
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    by_cases hz : ‖y‖ = 0
    · simp [hz]
    · have hid : ‖y‖⁻¹ * ‖y‖ ^ 2 = ‖y‖ := by field_simp
      rw [hid] at h
      simpa [mem_closedBall_iff_norm] using h
  · intro hy x hx
    have hy' : ‖y‖ ≤ 1 := by simpa [mem_closedBall_iff_norm] using hy
    have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall_iff_norm] using hx
    have hxy := real_inner_le_norm x y
    nlinarith [norm_nonneg x, norm_nonneg y]

end MetaMathlibExt

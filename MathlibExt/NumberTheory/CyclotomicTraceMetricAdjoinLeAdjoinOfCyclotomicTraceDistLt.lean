/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CyclotomicTraceMetric
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Tactic.Linarith

/-!
# Krasner-type lemma for the cyclotomic trace metric

If `β` is closer to `α` than half the distance from `α` to any of its distinct
`ℚ`-conjugates, then `ℚ(α)` is contained in `ℚ(β)` as subfields of the `p`-th
cyclotomic field.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 4.
-/

namespace MetaMathlibExt

@[expose] public section

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

private theorem cyclotomicTraceDist_triangle (hp : p.Prime) (x y z : K) :
    cyclotomicTraceDist p x z ≤ cyclotomicTraceDist p x y + cyclotomicTraceDist p y z := by
  have htri := (cyclotomicTraceNorm_isNorm (K := K) hp).2.1
  have hdecomp : x - z = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
  simp only [cyclotomicTraceDist, hdecomp]
  exact htri _ _

/-- **Krasner-type lemma for the cyclotomic trace metric.** Let $p$ be a prime and let $K$ be a
field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed primitive $p$-th
root of unity $\omega \in K$. Write $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$ for the trace
metric on $K$, where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $\alpha, \beta \in K$ and suppose that $d(\alpha, \beta) < d(\alpha, \sigma(\alpha)) / 2$ for
every automorphism $\sigma$ of $K$ over $\mathbb{Q}$ with $\sigma(\alpha) \ne \alpha$. Then
$\mathbb{Q}(\alpha) \subseteq \mathbb{Q}(\beta)$ as subfields of $K$.

Since $K / \mathbb{Q}$ is Galois, the elements $\sigma(\alpha) \ne \alpha$ are exactly the
conjugates of $\alpha$ over $\mathbb{Q}$ other than $\alpha$ itself.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 4 (`integers-2025-A10-thm-4`). -/
public theorem adjoin_le_adjoin_of_cyclotomicTraceDist_lt (hp : p.Prime)
    {α β : K}
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ α ≠ α →
      cyclotomicTraceDist p α β < cyclotomicTraceDist p α (σ α) / 2) :
    IntermediateField.adjoin ℚ {α} ≤ IntermediateField.adjoin ℚ {β} := by
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {β})]
  refine (IntermediateField.mem_fixedField_iff _ _).mpr ?_
  intro σ hσ
  have hσ := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
  have hβ : σ β = β := hσ β (IntermediateField.subset_adjoin ℚ {β} (by simp))
  by_contra hne
  have hlt := h σ hne
  have hinv := cyclotomicTraceDist_algEquiv hp σ α β
  rw [hβ] at hinv
  have htri := cyclotomicTraceDist_triangle hp α β (σ α)
  have hsymm := cyclotomicTraceDist_comm (p := p) β (σ α)
  linarith

end

end MetaMathlibExt

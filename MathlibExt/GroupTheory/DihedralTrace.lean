/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion

/-!
# Traces under a dihedral action

Let a group `G` act on an abelian group `M` by automorphisms, let `H ≤ G` be a finite subgroup and
let `τ ∈ G` satisfy `τ h = h⁻¹ τ` for all `h ∈ H`. If `τ y = ε σ' y + t` with `σ' ∈ H`, `ε = ±1`
and `t` torsion, then the trace `Y = ∑_{h ∈ H} h y` satisfies `τ Y = ε Y + t'` with
`t' = ∑_{h ∈ H} h⁻¹ t` torsion (`DistribMulAction.smul_sum_smul_eq_of_mul_eq_inv_mul`).

This is the step in Gross's proof of Proposition 5.4 of *Kolyvagin's work on modular elliptic
curves* (1991), p. 243, that passes from the action of complex conjugation on the Heegner point
`y_n` (Proposition 5.3) to its action on a trace over `G_n`, using the commutation relation
`τσ = σ⁻¹τ`.
-/

@[expose] public section

namespace DistribMulAction

open Finset

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- **Traces under a dihedral action.** Let $M$ be an abelian group on which a group $G$ acts by
automorphisms, let $H \le G$ be a finite subgroup, and let $\tau \in G$ satisfy
$\tau h = h^{-1} \tau$ for every $h \in H$. Let $y \in M$, $\sigma' \in H$,
$\varepsilon \in \{1, -1\}$ (a unit of $\mathbb{Z}$) and $t \in M$ a torsion element with
$\tau y = \varepsilon \, \sigma' y + t$. Then $Y = \sum_{h \in H} h y$ satisfies
$\tau Y = \varepsilon Y + t'$ with $t' = \sum_{h \in H} h^{-1} t$, and $t'$ is a torsion element
of $M$.

Source: B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and
arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
235–256: proof of Proposition 5.4, p. 243 ("For any $\sigma \in G_n$ we have the commutation
relation $\tau\sigma = \sigma^{-1}\tau$"), applied to the hypothesis
$y_n^\tau = \varepsilon \cdot y_n^{\sigma'} + (\text{torsion})$ of Proposition 5.3, p. 243. -/
theorem smul_sum_smul_eq_of_mul_eq_inv_mul (H : Subgroup G) [Fintype H] {τ : G}
    (hτ : ∀ h ∈ H, τ * h = h⁻¹ * τ) {σ' : G} (hσ' : σ' ∈ H) (ε : ℤˣ) {y t : M}
    (ht : IsOfFinAddOrder t) (hy : τ • y = (ε : ℤ) • σ' • y + t) :
    τ • ∑ h : H, (h : G) • y = (ε : ℤ) • ∑ h : H, (h : G) • y + ∑ h : H, (h : G)⁻¹ • t ∧
      IsOfFinAddOrder (∑ h : H, (h : G)⁻¹ • t) := by
  refine ⟨?_, ?_⟩
  · -- `h ↦ h⁻¹ σ'` is a bijection of `H`
    let e : H ≃ H := (Equiv.inv H).trans (Equiv.mulRight ⟨σ', hσ'⟩)
    have hsum : ∑ h : H, (h : G)⁻¹ • σ' • y = ∑ h : H, (h : G) • y := by
      refine Fintype.sum_equiv e _ _ fun h => ?_
      simp [e, mul_smul]
    calc τ • ∑ h : H, (h : G) • y = ∑ h : H, (h : G)⁻¹ • τ • y := by
          rw [smul_sum]
          refine Fintype.sum_congr _ _ fun h => ?_
          rw [← mul_smul, ← mul_smul, hτ h h.2]
      _ = (ε : ℤ) • ∑ h : H, (h : G) • y + ∑ h : H, (h : G)⁻¹ • t := by
          simp_rw [hy, smul_add, smul_comm _ ((ε : ℤ)), sum_add_distrib, ← smul_sum, hsum]
  · refine AddSubmonoid.sum_mem (AddCommMonoid.addTorsion M) fun h _ => ?_
    obtain ⟨n, hn, hnt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, by rw [smul_comm, hnt, smul_zero]⟩

end DistribMulAction

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Tactic.Choose

@[expose] public section

/-!
# Dual submodules commute with localized spans

For a domain `A` with fraction field `K`, a bilinear form `B` on a `K`-vector
space `V`, a finitely generated `A`-submodule `M`, and a submonoid `S ≤ A⁰`,
the `B`-dual over the localization `Aₛ` of the localized span of `M` is the
localized span of the original `A`-dual of `M`.
-/

namespace LinearMap

namespace BilinForm

variable {A K V : Type*} [CommRing A] [IsDomain A] [Field K]
variable [Algebra A K] [IsFractionRing A K]
variable [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
variable (B : LinearMap.BilinForm K V) (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)

/-- **Dual submodules commute with localization.** Let $A$ be an integral domain with fraction
field $K$, let $V$ be a $K$-vector space that is also an $A$-module compatibly with $A \to K$, and
let $B$ be a $K$-bilinear form on $V$. For a subring $R \subseteq K$ and an $R$-submodule $N$ of
$V$, write $N^\vee_R = \{x \in V : B(x, y) \in R \text{ for all } y \in N\}$ for the dual of $N$
over $R$. Let $S$ be a submonoid of $A$ consisting of non-zero-divisors, and let
$A_S = \{a/s : a \in A,\ s \in S\} \subseteq K$ be the localization of $A$ at $S$. Then for every
finitely generated $A$-submodule $M$ of $V$, the dual over $A_S$ of the $A_S$-span of $M$ equals
the $A_S$-span of the dual $M^\vee_A$ of $M$ over $A$. -/
theorem dualSubmodule_span_localization (M : Submodule A V) (hM : M.FG) :
    let Aₛ := Localization.subalgebra.ofField K S hS
    B.dualSubmodule (Submodule.span Aₛ (M : Set V)) =
      Submodule.span Aₛ (B.dualSubmodule M : Set V) := by
  intro Aₛ
  apply le_antisymm
  · intro x hx
    obtain ⟨T, hT⟩ := hM
    classical
    -- Each generator pairing lies in `Aₛ`; pick one denominator per generator.
    have hmem : ∀ u : ↥T, ∃ sp : A × S,
        B x (u : V) * algebraMap A K sp.2 = algebraMap A K sp.1 := by
      intro u
      have hmemT : (u : V) ∈ (T : Set V) := u.2
      have htM : (u : V) ∈ (M : Set V) := by
        rw [← hT]
        exact Submodule.subset_span hmemT
      have hyt : (u : V) ∈ Submodule.span Aₛ (M : Set V) :=
        Submodule.subset_span htM
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp ((mem_dualSubmodule B).mp hx _ hyt)
      have hcar : (c : K) ∈ Localization.subalgebra.ofField K S hS := c.2
      obtain ⟨a, s, hs, has⟩ := hcar
      refine ⟨(a, ⟨s, hs⟩), ?_⟩
      have hcoe : (c : K) = B x (u : V) := by
        rw [← hc]
        rfl
      have hs0 : algebraMap A K s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change B x (u : V) * algebraMap A K s = algebraMap A K a
      rw [← hcoe, has, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    choose sp hsp using hmem
    -- Common denominator: product over the finite generating set.
    set s₀ : A := ∏ u : ↥T, ((sp u).2 : A) with hs₀
    have hs₀S : s₀ ∈ S := by
      rw [hs₀]
      exact Submonoid.prod_mem S (fun u _ => (sp u).2.2)
    -- `s₀ • x` lies in the original dual.
    have hsm : s₀ • x ∈ B.dualSubmodule M := by
      refine (mem_dualSubmodule B).mpr ?_
      intro y hy
      rw [← hT] at hy
      refine Submodule.span_induction (p := fun y _ => B (s₀ • x) y ∈ (1 : Submodule A K))
        ?_ ?_ ?_ ?_ (x := y) hy
      · intro z hz
        have hzT : z ∈ T := hz
        let u : ↥T := ⟨z, hzT⟩
        have key : B x z * algebraMap A K s₀ ∈ algebraMap A K '' Set.univ := by
          have hdiv : s₀ = ((sp u).2 : A) * ∏ v ∈ Finset.univ.erase u, ((sp v).2 : A) :=
            (Finset.mul_prod_erase _ _ (Finset.mem_univ u)).symm
          refine ⟨(sp u).1 * ∏ v ∈ Finset.univ.erase u, ((sp v).2 : A),
            Set.mem_univ _, ?_⟩
          rw [hdiv, map_mul, map_mul, ← mul_assoc, hsp u]
        obtain ⟨a, _, ha⟩ := key
        rw [BilinForm.smul_left_of_tower, Algebra.smul_def, mul_comm]
        exact Submodule.mem_one.mpr ⟨a, ha⟩
      · simp [BilinForm.zero_right]
      · intro a b _ _ ha hb
        rw [BilinForm.add_right]
        exact Submodule.add_mem (1 : Submodule A K) ha hb
      · intro r z _ hz
        rw [BilinForm.smul_right_of_tower]
        exact Submodule.smul_mem _ _ hz
    -- `algebraMap A Aₛ s₀` is a unit, so `x` is an `Aₛ`-multiple of `s₀ • x`.
    have hunit : IsUnit (algebraMap A Aₛ s₀) :=
      IsLocalization.map_units Aₛ ⟨s₀, hs₀S⟩
    obtain ⟨u, hu⟩ := hunit
    have hrec : x = ((u⁻¹ : Units Aₛ) : Aₛ) • (s₀ • x) := by
      change x = (u⁻¹ : Units Aₛ) • (s₀ • x)
      rw [eq_inv_smul_iff]
      change (u : Aₛ) • x = s₀ • x
      rw [hu, IsScalarTower.algebraMap_smul Aₛ s₀ x]
    rw [hrec]
    apply Submodule.smul_mem
    exact Submodule.subset_span hsm
  · rw [Submodule.span_le]
    intro x hx
    refine (mem_dualSubmodule B).mpr ?_
    intro y hy
    refine Submodule.span_induction (p := fun y _ => B x y ∈ (1 : Submodule Aₛ K))
      ?_ ?_ ?_ ?_ (x := y) hy
    · intro z hz
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp ((mem_dualSubmodule B).mp hx z hz)
      exact Submodule.mem_one.mpr ⟨algebraMap A Aₛ a, by
        rw [← IsScalarTower.algebraMap_apply A Aₛ K]
        exact ha⟩
    · simp [BilinForm.zero_right]
    · intro a b _ _ ha hb
      rw [BilinForm.add_right]
      exact Submodule.add_mem (1 : Submodule Aₛ K) ha hb
    · intro r z _ hz
      rw [BilinForm.smul_right_of_tower]
      exact Submodule.smul_mem _ _ hz

end BilinForm

end LinearMap

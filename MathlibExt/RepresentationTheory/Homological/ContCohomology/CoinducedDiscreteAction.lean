/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.RepresentationTheory.Continuous.TopRep
import MathlibExt.RepresentationTheory.Continuous.ContinuousActionBridge
import MathlibExt.RepresentationTheory.Continuous.FiniteQuotientFactorization
import MathlibExt.Topology.ContinuousMap.CompactDiscrete

/-!
# Discreteness and joint continuity of compact-open coinduction

For a compact group and a discrete coefficient representation, compact-open
coinduction has discrete carrier topology.  For a compact totally
disconnected group, joint continuity of the source action also gives joint
continuity of the coinduced action.

The continuity proof factors each continuous coefficient function through a
finite open-normal quotient, then intersects its right-invariance subgroup
with an open-normal subgroup fixing the finite range of the function.

This file installs no global topology or continuity instance.  It makes no
canonical-cokernel discreteness, coefficient-LES, Serre-sequence,
dimension-shift, edge, VM2, or norm-residue claim.

## Main declarations

* `ContinuousCohomology.coinduced_discrete`
* `ContinuousCohomology.coinduced_action_isContinuous`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Representation ContRepresentation

namespace ContinuousCohomology

universe u v w

variable {k : Type u} {G : Type v}
variable [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compact-open coinduction of a discrete coefficient over a compact group
has discrete carrier topology. -/
theorem coinduced_discrete
    [CompactSpace G] (X : TopRep.{max v w, u, v} k G)
    [DiscreteTopology X] : DiscreteTopology X.coind₁ :=
  ContinuousMap.discreteTopology_of_compact_domain

/-- Under the standard joint-action hypothesis, compact-open coinduction
over a compact totally disconnected group again has jointly continuous
action. -/
theorem coinduced_action_isContinuous
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (X : TopRep.{max v w, u, v} k G) [DiscreteTopology X]
    (hX : ((TopRep.toActionTopModFunc (k := k) (G := G)).obj X).IsContinuous) :
    ((TopRep.toActionTopModFunc (k := k) (G := G)).obj X.coind₁).IsContinuous := by
  let A := (TopRep.toActionTopModFunc (k := k) (G := G)).obj X.coind₁
  apply (Action.isContinuous_def A).2
  let _ : DiscreteTopology ((forget₂ _ TopCat).obj A) := coinduced_discrete X
  let hcont : ContinuousSMul G ((forget₂ _ TopCat).obj A) :=
    (continuousSMul_iff_stabilizer_isOpen).2 (by
      intro F
      change C(G, X) at F
      let c : (Fin 1 → G) → X := fun x => F (x 0)
      have hc : Continuous c := F.continuous.comp (continuous_apply 0)
      obtain ⟨U, cbar, hcbar⟩ :=
        exists_openNormalSubgroup_quotient_factor_fin_of_discreteTopology c hc
      have hright (x h : G) (hh : h ∈ U) : F (x * h) = F x := by
        have hq : QuotientGroup.mk' U.toSubgroup (x * h) =
            QuotientGroup.mk' U.toSubgroup x := by
          rw [map_mul]
          have hhone : QuotientGroup.mk' U.toSubgroup h = 1 :=
            (QuotientGroup.eq_one_iff h).2 hh
          rw [hhone, mul_one]
        have h₁ := hcbar (fun _ : Fin 1 => x * h)
        have h₂ := hcbar (fun _ : Fin 1 => x)
        change cbar (fun _ : Fin 1 => QuotientGroup.mk' U.toSubgroup (x * h)) =
          F (x * h) at h₁
        change cbar (fun _ : Fin 1 => QuotientGroup.mk' U.toSubgroup x) =
          F x at h₂
        rw [show (fun _ : Fin 1 => QuotientGroup.mk' U.toSubgroup (x * h)) =
            (fun _ : Fin 1 => QuotientGroup.mk' U.toSubgroup x) by
              funext i
              exact hq] at h₁
        exact h₁.symm.trans h₂
      let hrange : (Set.range F).Finite :=
        (isCompact_range F.continuous).finite_of_discrete
      let values : Finset X := hrange.toFinset
      let V₀ : OpenNormalSubgroup G :=
        { toOpenSubgroup := ⊤, isNormal' := Subgroup.normal_top }
      obtain ⟨V, _hV, hfix⟩ :=
        TopRep.exists_openNormal_le_fix_finset_of_action_isContinuous
          hX V₀ values
      let W : OpenNormalSubgroup G := U ⊓ V
      apply Subgroup.isOpen_mono (H₁ := W.toSubgroup)
      · intro h hh
        change X.coind₁.ρ h F = F
        apply ContinuousMap.ext
        intro x
        change X.ρ h (F (h⁻¹ * x)) = F x
        have hconj : x⁻¹ * h⁻¹ * x ∈ U := by
          change x⁻¹ * h⁻¹ * x ∈ U.toSubgroup
          have hU : h ∈ U := (inf_le_left : W ≤ U) hh
          simpa only [inv_inv] using
            ((inferInstance : U.toSubgroup.Normal).conj_mem
              h⁻¹ (U.inv_mem hU) x⁻¹)
        have hF : F (h⁻¹ * x) = F x := by
          rw [show h⁻¹ * x = x * (x⁻¹ * h⁻¹ * x) by group]
          exact hright x (x⁻¹ * h⁻¹ * x) hconj
        rw [hF]
        apply hfix ⟨h, (inf_le_right : W ≤ V) hh⟩ (F x)
        change F x ∈ hrange.toFinset
        exact hrange.mem_toFinset.mpr ⟨x, rfl⟩
      · exact W.isOpen)
  exact hcont.continuous_smul

end ContinuousCohomology

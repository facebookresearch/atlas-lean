/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueTwoPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentationAction

/-! Actual Conway transport of the genuine neighborhood quotients. It reduces the source
residue abelianity input to the single actual base-point quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Conway source automorphisms carry genuine first-neighborhood groups to the
corresponding first-neighborhood groups. -/
theorem co1ResidueLocal_action_mem (g : Co1) (p : MonsterCo1GeometryPoint)
    (x : Co1UniversalPresentation) (hx : x ∈ co1ResidueLocal p) :
    co1UniversalActionEnd g x ∈ co1ResidueLocal (g • p) := by
  have hle : co1ResidueLocal p ≤
      (co1ResidueLocal (g • p)).comap (co1UniversalActionEnd g) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    rcases hy with rfl | ⟨q, hq, rfl⟩
    · change co1UniversalActionEnd g (PresentedGroup.of p) ∈ co1ResidueLocal (g • p)
      rw [co1UniversalActionEnd_point]
      exact co1ResidueLocal_point_mem _
    · change co1UniversalActionEnd g (PresentedGroup.of q) ∈ co1ResidueLocal (g • p)
      rw [co1UniversalActionEnd_point]
      exact co1ResidueLocal_neighbor_mem _ _ (monsterCo1GeometryAdjacent_smul g p q hq)
  exact hle hx

/-- The genuine source action restricted to the actual neighborhood groups. -/
def co1ResidueLocalTransport (g : Co1) (p : MonsterCo1GeometryPoint) :
    co1ResidueLocal p →* co1ResidueLocal (g • p) where
  toFun x := ⟨co1UniversalActionEnd g x.val, co1ResidueLocal_action_mem g p x.val x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (co1UniversalActionEnd g) a.val b.val)

/-- The distinguished source point is transported to the distinguished point of the new
neighborhood group. -/
theorem co1ResidueLocalTransport_base (g : Co1) (p : MonsterCo1GeometryPoint) :
    co1ResidueLocalTransport g p (co1ResidueBase p) = co1ResidueBase (g • p) :=
  Subtype.ext (co1UniversalActionEnd_point g p)

/-- Actual transport preserves, and reflects, the genuine central cyclic point kernel. -/
theorem co1ResidueLocalTransport_kernel_iff (g : Co1) (p : MonsterCo1GeometryPoint)
    (x : co1ResidueLocal p) :
    co1ResidueLocalTransport g p x ∈ co1ResidueBaseKernel (g • p) ↔
      x ∈ co1ResidueBaseKernel p := by
  rw [co1ResidueBaseKernel_mem_iff, co1ResidueBaseKernel_mem_iff]
  have hinj : Function.Injective (co1ResidueLocalTransport g p) := by
    intro a b h
    apply Subtype.ext
    exact (co1UniversalActionEnd_inverse g).injective
      (congrArg (fun y : co1ResidueLocal (g • p) => y.val) h)
  constructor
  · rintro (h1 | h2)
    · exact Or.inl (hinj (h1.trans (map_one _).symm))
    · exact Or.inr (hinj (h2.trans (co1ResidueLocalTransport_base g p).symm))
  · rintro (rfl | rfl)
    · exact Or.inl (map_one _)
    · exact Or.inr (co1ResidueLocalTransport_base g p)

/-- The actual Conway action descends to the central point quotients. -/
def co1ResidueQuotientTransport (g : Co1) (p : MonsterCo1GeometryPoint) :
    Co1ResidueLocalQuotient p →* Co1ResidueLocalQuotient (g • p) :=
  QuotientGroup.map (co1ResidueBaseKernel p) (co1ResidueBaseKernel (g • p))
    (co1ResidueLocalTransport g p) (fun x hx =>
      (co1ResidueLocalTransport_kernel_iff g p x).mpr hx)

/-- No new kernel is introduced by actual transport between residue quotients. -/
theorem co1ResidueQuotientTransport_injective (g : Co1) (p : MonsterCo1GeometryPoint) :
    Function.Injective (co1ResidueQuotientTransport g p) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      intro h
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hm : co1ResidueLocalTransport g p (a / b) ∈ co1ResidueBaseKernel (g • p) := by
        rw [map_div]
        exact QuotientGroup.eq_iff_div_mem.mp h
      exact (co1ResidueLocalTransport_kernel_iff g p (a / b)).mp hm

/-- Abelianity of the single actual base residue suffices for every actual residue quotient,
using original Co1 point transitivity and the faithful source action. -/
theorem co1ResidueQuotientsAbelian_of_base
    (hbase : ∀ a b : Co1ResidueLocalQuotient monsterCo1GeometryBasePoint, Commute a b) :
    co1ResidueQuotientsAbelian := by
  intro p a b
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hp : g⁻¹ • p = monsterCo1GeometryBasePoint := by
    rw [← hg, inv_smul_smul]
  have ht : ∀ x y : Co1ResidueLocalQuotient (g⁻¹ • p), Commute x y := by
    rw [hp]
    exact hbase
  apply (co1ResidueQuotientTransport_injective g⁻¹ p)
  rw [map_mul, map_mul]
  exact (ht _ _).eq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- From the actual code conjugates to the actual projected normal subgroup.
The full centralizer inclusion remains an explicit geometric prerequisite. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationSigns

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The projected local intersection is normal in the actual Conway quotient. -/
theorem generatedNormal_localProjection_normal (N : Subgroup ↥G) [N.Normal] :
    ((N.comap localIntoGenerated).map projH).Normal :=
  Subgroup.Normal.map inferInstance projH projH_surjective

/-- The full centralizer inclusion supplies local lifts of every actual source y_d. -/
theorem sourceGeneratedY_mem_local_range_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (d : Fin 4096) (ε : ZMod 2) : sourceGeneratedY d ε ∈ localIntoGenerated.range :=
  hC (sourceGeneratedY_mem_centralizer d ε)

/-- Embedded Q in a normal subgroup kills every prescribed source Golay sign
in the local Conway quotient once the full centralizer inclusion is established. -/
theorem sourceGeneratedSign_mem_normal_projection_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup ↥G) [N.Normal] (hQ : qIntoGenerated.range ≤ N) (d : Fin 4096) :
    (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∈
      (N.comap localIntoGenerated).map projH := by
  obtain ⟨h, hy⟩ := sourceGeneratedY_mem_local_range_of_centralizer_le_local hC d 0
  exact sourceGeneratedSign_mem_normal_projection N hQ d 0 h hy

/-- Every actual Golay code sign is covered by the published source labels. -/
theorem golaySign_mem_normal_projection_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup ↥G) [N.Normal] (hQ : qIntoGenerated.range ≤ N) (c : golayCode) :
    (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈
      (N.comap localIntoGenerated).map projH := by
  obtain ⟨a, ha⟩ := c.property
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.2 a
  have hc : sourceGeneratedSignCode d = c := by
    apply Subtype.ext
    change golayEncoder (golayLabelCoefficients d) = c.val
    rw [hd, ha]
  rw [← hc]
  exact sourceGeneratedSign_mem_normal_projection_of_centralizer_le_local hC N hQ d

/-- The actual three-bases class lies in that projected normal subgroup too. -/
theorem co1XiClass_mem_normal_projection_of_centralizer_le_local
    (hC : Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≤ localIntoGenerated.range)
    (N : Subgroup ↥G) [N.Normal] (hQ : qIntoGenerated.range ≤ N) :
    co1XiClass ∈ (N.comap localIntoGenerated).map projH := by
  let := generatedNormal_localProjection_normal N
  apply co1XiClass_mem_of_reflectionClass_mem
  exact golaySign_mem_normal_projection_of_centralizer_le_local hC N hQ co1ReflectionCode

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Normal-subgroup binary image and its actual Conway invariance. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The binary image of a Q subgroup, as a genuine F₂ submodule. -/
def qSubgroupBinaryImage (L : Subgroup Q) : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {v | ofAdd v ∈ L.map qQuotHom}
  zero_mem' := (L.map qQuotHom).one_mem
  add_mem' hv hw := (L.map qQuotHom).mul_mem hv hw
  smul_mem' c v hv := by
    change ofAdd (c • v) ∈ L.map qQuotHom
    change ofAdd v ∈ L.map qQuotHom at hv
    have hc : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    rcases hc with rfl | rfl
    · rw [zero_smul, ofAdd_zero]
      exact (L.map qQuotHom).one_mem
    · rw [one_smul]
      exact hv

/-- The binary image of the actual Q intersection of a local subgroup. -/
noncomputable def localNormalQImage (K : Subgroup H) : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  qSubgroupBinaryImage (K.comap inclQ)

/-- The local image contains the binary coordinates of each actual Q element it contains. -/
theorem mem_localNormalQImage_of_mem (K : Subgroup H) (q : Q) (hq : inclQ q ∈ K) :
    toAdd (qQuotHom q) ∈ localNormalQImage K := by
  exact Subgroup.mem_map_of_mem qQuotHom hq

/-- Fiber conjugation descends to the genuine quotient local group. -/
theorem inclQ_spinConjugation (f : localFiberSubgroup) (q : Q) :
    inclQ (spinConjugation f.val.1 q) = localFiberIntoH f * inclQ q * (localFiberIntoH f)⁻¹ := by
  change QuotientGroup.mk' localDiagonalSubgroup
    (localFiberIncl (spinConjugation f.val.1 q)) = _
  rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
  rfl

/-- The binary Q image of a normal local subgroup is invariant under its actual Conway action. -/
theorem localNormalQImage_invariant (K : Subgroup H) [hK : K.Normal]
    (h : H) (v : Fin 24 → ZMod 2) (hv : v ∈ localNormalQImage K) :
    co1BinaryAction (projH h) v ∈ localNormalQImage K := by
  induction h using QuotientGroup.induction_on with
  | H f =>
    obtain ⟨q, hq, hqv⟩ := hv
    have hqv : toAdd (qQuotHom q) = v := congrArg toAdd hqv
    have hm : inclQ (spinConjugation f.val.1 q) ∈ K := by
      rw [inclQ_spinConjugation]
      exact hK.conj_mem _ hq _
    have hi := mem_localNormalQImage_of_mem K (spinConjugation f.val.1 q) hm
    rw [← qBinaryAction_apply] at hi
    change spinBinaryAction f.val.1 (toAdd (qQuotHom q)) ∈ localNormalQImage K at hi
    rw [f.property, hqv] at hi
    exact hi

/-- The normal local Q image is invariant under every element of the genuine Conway quotient. -/
theorem localNormalQImage_co1_invariant (K : Subgroup H) [K.Normal]
    (c : Co1) (v : Fin 24 → ZMod 2) (hv : v ∈ localNormalQImage K) :
    co1BinaryAction c v ∈ localNormalQImage K := by
  obtain ⟨h, rfl⟩ := projH_surjective c
  exact localNormalQImage_invariant K h v hv

/-- Center containment plus a full binary image forces a Q subgroup to be all of Q. -/
theorem qSubgroup_eq_top_of_binaryImage_eq_top (L : Subgroup Q)
    (hz : centerQ ≤ L) (hi : qSubgroupBinaryImage L = ⊤) : L = ⊤ := by
  apply top_unique
  intro q _
  have hq : toAdd (qQuotHom q) ∈ qSubgroupBinaryImage L := by
    rw [hi]; exact Submodule.mem_top
  obtain ⟨k, hk, he⟩ := hq
  have hdiff : k⁻¹ * q ∈ centerQ := by
    rw [← qQuotHom_ker]
    change qQuotHom (k⁻¹ * q) = 1
    rw [map_mul, map_inv, he]
    exact inv_mul_cancel _
  have hm := L.mul_mem hk (hz hdiff)
  simpa only [mul_inv_cancel_left] using hm

/-- The genuine central element generates the whole extraspecial center. -/
theorem centerQ_le_of_central_mem (L : Subgroup Q) (hz : qCentralInvolution ∈ L) :
    centerQ ≤ L := by
  intro q hq
  by_cases h : q = 1
  · rw [h]; exact L.one_mem
  · rw [qCentralInvolution_eq_of_mem_center_ne_one q hq h]
    exact hz

/-- A local subgroup containing z and having full binary Q image contains embedded Q. -/
theorem inclQ_range_le_of_localNormalQImage_eq_top (K : Subgroup H)
    (hz : inclQ qCentralInvolution ∈ K) (hi : localNormalQImage K = ⊤) : inclQ.range ≤ K := by
  have he : K.comap inclQ = ⊤ :=
    qSubgroup_eq_top_of_binaryImage_eq_top (K.comap inclQ)
      (centerQ_le_of_central_mem _ hz) hi
  rintro h ⟨q, rfl⟩
  have hq : q ∈ K.comap inclQ := by rw [he]; exact Subgroup.mem_top _
  exact hq

/-- A spanning actual Conway orbit in the binary image exhausts embedded Q. -/
theorem inclQ_range_le_of_binaryOrbit_span_eq_top (K : Subgroup H) [K.Normal]
    (hz : inclQ qCentralInvolution ∈ K) (q : Q) (hq : inclQ q ∈ K)
    (hspan : Submodule.span (ZMod 2)
      {v | ∃ c : Co1, v = co1BinaryAction c (toAdd (qQuotHom q))} = ⊤) :
    inclQ.range ≤ K := by
  apply inclQ_range_le_of_localNormalQImage_eq_top K hz
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro v ⟨c, rfl⟩
  exact localNormalQImage_co1_invariant K c _ (mem_localNormalQImage_of_mem K q hq)

/-- An explicit Ω orbit-span certificate forces embedded Q into every normal subgroup
with nontrivial intersection with H. The span hypothesis is the remaining finite linear input. -/
theorem generated_q_range_le_of_Omega_orbit_span (N : Subgroup ↥G) [N.Normal]
    (hN : N.comap localIntoGenerated ≠ ⊥)
    (hspan : Submodule.span (ZMod 2)
      {v | ∃ c : Co1, v = co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ))} = ⊤) :
    qIntoGenerated.range ≤ N := by
  have hz := generatedCentral_mem_of_nontrivial_local_intersection N hN
  have ho := sourceOmegaQ_mem_of_generatedCentral_mem N hz
  have hQ := inclQ_range_le_of_binaryOrbit_span_eq_top (N.comap localIntoGenerated)
    hz sourceOmegaQ ho hspan
  rintro g ⟨q, rfl⟩
  exact hQ ⟨q, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

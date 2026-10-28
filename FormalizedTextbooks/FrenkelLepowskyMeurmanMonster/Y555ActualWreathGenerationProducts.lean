/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local diagonal and opposite triality generate both Monster factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82SourceBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The second projection of a subgroup containing the actual local diagonal and opposite
triality contains the defining generators of the actual group G. -/
theorem y555ActualProduct_second_eq_top (K : Subgroup (G × G))
    (hH : ∀ h : H, (localIntoGenerated h, localIntoGenerated h) ∈ K)
    (hτ : (extraIntoGenerated, extraIntoGenerated⁻¹) ∈ K) :
    K.map (MonoidHom.snd G G) = ⊤ := by
  apply generated_subgroup_eq_top_of_local_range_le_extra_mem
  · rintro _ ⟨h, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(localIntoGenerated h, localIntoGenerated h), hH h, rfl⟩
  · exact Subgroup.mem_map.mpr
      ⟨(extraIntoGenerated, extraIntoGenerated⁻¹)⁻¹, K.inv_mem hτ, inv_inv _⟩

/-- Surjectivity of the second projection makes the pure second-factor intersection normal
in the actual group, although the product subgroup itself need not be normal. -/
theorem y555ActualProduct_right_normal (K : Subgroup (G × G))
    (hK : K.map (MonoidHom.snd G G) = ⊤) :
    (K.comap (MonoidHom.inr G G)).Normal := by
  constructor
  intro n hn g
  obtain ⟨p, hp, he⟩ := Subgroup.mem_map.mp (hK ▸ Subgroup.mem_top g)
  change (1, g * n * g⁻¹) ∈ K
  have hm := K.mul_mem (K.mul_mem hp hn) (K.inv_mem hp)
  convert hm using 1
  apply Prod.ext
  · simp
  · change g * n * g⁻¹ = p.2 * n * p.2⁻¹
    exact congrArg (fun a : G => a * n * a⁻¹) he.symm

/-- The actual triality signs produce a nontrivial pure second-factor element from the
local diagonal and opposite triality; this rules out a diagonal product subgroup. -/
theorem y555ActualProduct_right_central (K : Subgroup (G × G))
    (hH : ∀ h : H, (localIntoGenerated h, localIntoGenerated h) ∈ K)
    (hτ : (extraIntoGenerated, extraIntoGenerated⁻¹) ∈ K) :
    (1, qIntoGenerated qCentralInvolution) ∈ K := by
  let z := qIntoGenerated qCentralInvolution
  let w := centralSignIntoGenerated 2
  let u := centralSignIntoGenerated 1
  have hz : (z, z) ∈ K := hH (inclQ qCentralInvolution)
  have hw : (w, w) ∈ K := by
    have hq : (qIntoGenerated sourceOmegaQ, qIntoGenerated sourceOmegaQ) ∈ K :=
      hH (inclQ sourceOmegaQ)
    rw [qIntoGenerated_sourceOmegaQ] at hq
    exact hq
  have hew : extraIntoGenerated⁻¹ * z * extraIntoGenerated = w :=
    monsterSourceY_inverse_central_sign.symm
  have heu : extraIntoGenerated * z * extraIntoGenerated⁻¹ = u := by
    apply Subtype.ext
    exact localCentralGriess_conjugate
  have hwu : w⁻¹ * u = z := by
    apply Subtype.ext
    change (trialityCentralSign 2)⁻¹ * trialityCentralSign 1 =
      localCentralGriess
    rw [localCentralGriess_eq_trialityCentralSign]
    have hi : (trialityCentralSign 2)⁻¹ = trialityCentralSign 2 := by
      apply inv_eq_of_mul_eq_one_left
      exact trialityCentralSign_square 2
    rw [hi, ← trialityCentralSign_zero_mul_one, mul_assoc,
      trialityCentralSign_square, mul_one]
  have hm := K.mul_mem (K.inv_mem hw)
    (K.mul_mem (K.mul_mem (K.inv_mem hτ) hz) hτ)
  convert hm using 1
  apply Prod.ext
  · change 1 = w⁻¹ * (extraIntoGenerated⁻¹ * z * extraIntoGenerated)
    rw [hew, inv_mul_cancel]
  · change z = w⁻¹ * (extraIntoGenerated * z * extraIntoGenerated⁻¹)
    rw [heu, hwu]

/-- The actual local diagonal and opposite triality generate the full product G × G.
The proof uses the already proved full centralizer and normal generation of actual G. -/
theorem y555ActualProduct_eq_top (K : Subgroup (G × G))
    (hH : ∀ h : H, (localIntoGenerated h, localIntoGenerated h) ∈ K)
    (hτ : (extraIntoGenerated, extraIntoGenerated⁻¹) ∈ K) : K = ⊤ := by
  let N := K.comap (MonoidHom.inr G G)
  let : N.Normal := y555ActualProduct_right_normal K (y555ActualProduct_second_eq_top K hH hτ)
  have hz : qIntoGenerated qCentralInvolution ∈ N := y555ActualProduct_right_central K hH hτ
  have hN : N ≠ ⊥ := by
    intro he
    rw [he, Subgroup.mem_bot] at hz
    apply qCentralInvolution_ne_one
    apply qIntoGenerated_injective
    exact hz.trans qIntoGenerated.map_one.symm
  have hNt : N = ⊤ := generated_normal_eq_top_of_centralizer_le_local
    generatedCentralizer_eq_local_range.le N hN
  have hr (g : G) : (1, g) ∈ K := by
    change g ∈ N
    rw [hNt]
    exact Subgroup.mem_top g
  have hL : K.comap (MonoidHom.inl G G) = ⊤ := by
    apply generated_subgroup_eq_top_of_local_range_le_extra_mem
    · rintro _ ⟨h, rfl⟩
      have hm := K.mul_mem (hH h) (hr (localIntoGenerated h)⁻¹)
      simpa using hm
    · have hm := K.mul_mem hτ (hr extraIntoGenerated)
      simpa using hm
  apply top_unique
  rintro ⟨g, h⟩ _
  have hl : (g, 1) ∈ K := by
    change g ∈ K.comap (MonoidHom.inl G G)
    rw [hL]
    exact Subgroup.mem_top g
  simpa using K.mul_mem hl (hr h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

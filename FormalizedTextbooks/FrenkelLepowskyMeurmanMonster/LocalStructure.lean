/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Elementary extraspecial-group facts for the concrete FLM coordinate model. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open NormalizedCocycleExtension Multiplicative
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The extension carrier consists of 24 base bits and one central bit. -/
def qCoordinateEquiv : Q ≃ ((Fin 24 → ZMod 2) × ZMod 2) where
  toFun g := (toAdd g.base, toAdd g.coeff)
  invFun p := ⟨ofAdd p.1, ofAdd p.2⟩
  left_inv g := by cases g; rfl
  right_inv p := by cases p; rfl

instance qFinite : Finite Q := Finite.of_equiv _ qCoordinateEquiv.symm

/-- The extraspecial coordinate group has order `2^25`. -/
theorem q_card : Nat.card Q = 2 ^ 25 := by
  rw [Nat.card_congr qCoordinateEquiv]
  simp [ZMod.card]

/-- The center consists of the two central bits. -/
theorem centerQ_card : Nat.card ↥centerQ = 2 := by
  rw [Nat.card_congr (Equiv.ofBijective centerMap centerMap_bijective)]
  change Nat.card (ZMod 2) = 2
  simp [ZMod.card]

/-- Every commutator has trivial base coordinate. -/
theorem q_commutator_le_center : commutator Q ≤ centerQ := by
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  rw [← qQuotHom_ker]
  change qQuotHom ⁅g, h⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- The distinguished central involution. -/
def qCentralInvolution : Q := ⟨1, ofAdd 1⟩

private def qFirstUnit : Q := ⟨ofAdd (Pi.single (0 : Fin 24) 1), 1⟩
private def qSecondUnit : Q := ⟨ofAdd (Pi.single (12 : Fin 24) 1), 1⟩

private theorem q_units_relation :
    qFirstUnit * qSecondUnit = qCentralInvolution * (qSecondUnit * qFirstUnit) := by
  apply Extension.ext
  · change ofAdd (Pi.single (0 : Fin 24) 1) * ofAdd (Pi.single 12 1) =
        1 * (ofAdd (Pi.single 12 1) * ofAdd (Pi.single 0 1))
    rw [one_mul, mul_comm]
  · change 1 * 1 * qCocycle.cocycle qFirstUnit.base qSecondUnit.base =
        ofAdd 1 * (1 * 1 * qCocycle.cocycle qSecondUnit.base qFirstUnit.base) *
          qCocycle.cocycle 1 (qSecondUnit.base * qFirstUnit.base)
    rw [qCocycle.one_left]
    simp only [one_mul, mul_one]
    apply toAdd.injective
    change qBeta (Pi.single 0 1) (Pi.single 12 1) =
      1 + qBeta (Pi.single 12 1) (Pi.single 0 1)
    have hb : qBeta (Pi.single (0 : Fin 24) 1) (Pi.single 12 1) = 1 := by
      simpa using qBeta_single_second (Pi.single (0 : Fin 24) 1) (0 : Fin 12)
    have hb' : qBeta (Pi.single (12 : Fin 24) 1) (Pi.single 0 1) = 0 := by
      simpa using qBeta_right_single_first (Pi.single (12 : Fin 24) 1) (0 : Fin 12)
    rw [hb, hb', add_zero]

/-- A pair of coordinate generators has commutator equal to the central involution. -/
theorem qCentralInvolution_mem_commutator : qCentralInvolution ∈ commutator Q := by
  have heq : ⁅qFirstUnit, qSecondUnit⁆ = qCentralInvolution := by
    rw [commutatorElement_def, q_units_relation]
    group
  rw [← heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have h : c.val < 2 := c.val_lt
  have hv : c.val = 0 ∨ c.val = 1 := by omega
  rcases hv with h | h
  · left; exact (ZMod.val_injective 2) h
  · right; exact (ZMod.val_injective 2) h

/-- In this nondegenerate coordinate extension, the center is exactly the derived subgroup. -/
theorem centerQ_eq_commutator : centerQ = commutator Q := by
  apply le_antisymm
  · intro g hg
    have hb := (q_mem_center_iff_base_eq_one g).mp hg
    rcases zmod_two_cases (toAdd g.coeff) with hc | hc
    · have he : g = 1 := Extension.ext hb (congrArg ofAdd hc)
      rw [he]; exact Subgroup.one_mem _
    · have he : g = qCentralInvolution := by
        apply Extension.ext hb
        exact congrArg ofAdd hc
      rw [he]; exact qCentralInvolution_mem_commutator
  · exact q_commutator_le_center

/-- Read one of the 24 quotient coordinates. -/
def qCoordinateHom (i : Fin 24) : Q →* Multiplicative (ZMod 2) where
  toFun g := ofAdd (toAdd g.base i)
  map_one' := rfl
  map_mul' _g _h := rfl

private theorem qCoordinateHom_cases (i : Fin 24) (g : Q) :
    qCoordinateHom i g = 1 ∨ qCoordinateHom i g = ofAdd 1 := by
  rcases zmod_two_cases (toAdd g.base i) with h | h
  · left; exact congrArg ofAdd h
  · right; exact congrArg ofAdd h

/-- Each single-coordinate kernel is a maximal subgroup of index two. -/
theorem qCoordinateHom_ker_isCoatom (i : Fin 24) : IsCoatom (qCoordinateHom i).ker := by
  refine ⟨?_, ?_⟩
  · intro h
    have hm : (⟨ofAdd (Pi.single i 1), 1⟩ : Q) ∈ (qCoordinateHom i).ker := by
      rw [h]; exact Subgroup.mem_top _
    change ofAdd (Pi.single i 1 i) = 1 at hm
    have hz : (1 : ZMod 2) = 0 := by simpa using congrArg toAdd hm
    exact one_ne_zero hz
  · intro K hK
    obtain ⟨g, hgK, hg⟩ := SetLike.exists_of_lt hK
    have hg1 : qCoordinateHom i g = ofAdd 1 :=
      (qCoordinateHom_cases i g).resolve_left hg
    apply top_unique
    intro x _
    rcases qCoordinateHom_cases i x with hx | hx
    · exact hK.le (show x ∈ (qCoordinateHom i).ker from hx)
    · have hm : g⁻¹ * x ∈ (qCoordinateHom i).ker := by
        change qCoordinateHom i (g⁻¹ * x) = 1
        rw [map_mul, map_inv, hg1, hx, inv_mul_cancel]
      have := K.mul_mem hgK (hK.le hm)
      simpa only [mul_inv_cancel_left] using this

/-- Frattini elements have every quotient coordinate zero. -/
theorem q_frattini_le_center : frattini Q ≤ centerQ := by
  intro g hg
  apply (q_mem_center_iff_base_eq_one g).mpr
  apply toAdd.injective
  funext i
  have hm := frattini_le_coatom (qCoordinateHom_ker_isCoatom i) hg
  change ofAdd (toAdd g.base i) = 1 at hm
  exact congrArg toAdd hm

/-- A central supplement to any subgroup forces it to be normal; its commutators then lie inside. -/
private theorem q_center_le_of_sup_eq_top (K : Subgroup Q) (h : K ⊔ centerQ = ⊤) :
    centerQ ≤ K := by
  have hn : K.Normal := Subgroup.normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← h]
    exact sup_le K.le_normalizer (by
      change Subgroup.center Q ≤ Subgroup.normalizer (K : Set Q)
      exact Subgroup.center_le_normalizer (K : Set Q)))
  rw [centerQ_eq_commutator, commutator_def, ← h]
  rw [Subgroup.commutator_sup_right]
  apply sup_le
  · exact Subgroup.commutator_le_left _ _
  · change ⁅Subgroup.center Q, K ⊔ centerQ⁆ ≤ K
    rw [Subgroup.commutator_center_left]
    exact bot_le

/-- The center lies in every maximal subgroup, so is contained in the Frattini subgroup. -/
theorem q_center_le_frattini : centerQ ≤ frattini Q := by
  change centerQ ≤ Order.radical (Subgroup Q)
  unfold Order.radical
  apply le_iInf
  intro K
  apply le_iInf
  intro hK
  by_contra h
  have hs : K < K ⊔ centerQ := lt_of_le_of_ne le_sup_left (by
    intro he
    exact h (he ▸ le_sup_right))
  have ht : K ⊔ centerQ = ⊤ := hK.2 _ hs
  exact h (q_center_le_of_sup_eq_top K ht)

/-- Center, derived subgroup, and Frattini subgroup coincide in the plus-type extraspecial group. -/
theorem commutatorQ_eq_frattini : commutator Q = frattini Q := by
  rw [← centerQ_eq_commutator]
  exact le_antisymm q_center_le_frattini q_frattini_le_center

/-- All ten extraspecial and quadratic-form clauses of the first milestone. -/
theorem q_extraspecial_structure :
    Nat.card Q = 2 ^ 25 ∧
    centerQ = commutator Q ∧
    commutator Q = frattini Q ∧
    Nat.card ↥centerQ = 2 ∧
    Function.Bijective ⇑centerMap ∧
    Nonempty ((Q ⧸ centerQ) ≃* Multiplicative (Fin 24 → ZMod 2)) ∧
    qQuotHom.ker = centerQ ∧
    qQuotHom.range = ⊤ ∧
    (∀ g : Q, ∃ _hz : g * g ∈ centerQ,
      squareQuad (toAdd (qQuotHom g)) = toAdd (centerMap ⟨g * g, _hz⟩)) ∧
    (∃ e : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2]
        ((Fin 12 → ZMod 2) × (Fin 12 → ZMod 2)),
      ∀ v, squareQuad v = hyperbolicFun (e v)) := by
  exact ⟨q_card, centerQ_eq_commutator, commutatorQ_eq_frattini, centerQ_card,
    centerMap_bijective, ⟨qQuotientEquiv⟩, qQuotHom_ker, qQuotHom_range,
    fun g => ⟨q_square_mem_center g, squareQuad_eq_centerMap_square g⟩,
    qHyperbolicEquiv, qHyperbolicEquiv_form⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

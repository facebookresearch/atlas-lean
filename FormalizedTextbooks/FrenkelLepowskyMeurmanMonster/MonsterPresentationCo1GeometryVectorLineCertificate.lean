/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite binary tests certify genuine full two-core orbits of actual source points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryOrbitTwo
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineAction

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Distinct complete binary coordinates imply distinct actual source points. -/
theorem monsterCo1GeometryVectorPoint_ne (p q : MonsterCo1GeometryPoint)
    (u v : Fin 24 → ZMod 2) (hp : p.val = u) (hq : q.val = v) (h : u ≠ v) : p ≠ q := by
  intro he
  exact h (hp.symm.trans ((congrArg Subtype.val he).trans hq))

/-- Complete actual twelve-generator preservation and one swapping test certify an original
genuine source line after actual Conway transport. -/
theorem monsterCo1GeometryVectorLine_certificate (g : Co1)
    (p q r : MonsterCo1GeometryPoint) (u v : Fin 24 → ZMod 2) (w : Fin 12)
    (hp : g • monsterCo1GeometryBasePoint = p)
    (hq : (g⁻¹ • q).val = u) (hr : (g⁻¹ • r).val = v)
    (hbu : (Pi.single 11 (1 : ZMod 2)) ≠ u)
    (hbv : (Pi.single 11 (1 : ZMod 2)) ≠ v) (huv : u ≠ v)
    (hu : ∀ k : Fin 12, monsterCo1GeometrySignBinary k *ᵥ u = u ∨
      monsterCo1GeometrySignBinary k *ᵥ u = v)
    (hv : ∀ k : Fin 12, monsterCo1GeometrySignBinary k *ᵥ v = u ∨
      monsterCo1GeometrySignBinary k *ᵥ v = v)
    (hw : monsterCo1GeometrySignBinary w *ᵥ u = v) :
    monsterCo1GeometryLine p q r := by
  have hl : monsterCo1GeometryAnchoredLine monsterCo1GeometryBasePoint
      (g⁻¹ • q) (g⁻¹ • r) := by
    apply monsterCo1GeometryAnchoredLine_of_basis_signs
    · exact monsterCo1GeometryVectorPoint_ne _ _ _ _
        monsterCo1GeometryBasePoint_binary hq hbu
    · exact monsterCo1GeometryVectorPoint_ne _ _ _ _
        monsterCo1GeometryBasePoint_binary hr hbv
    · exact monsterCo1GeometryVectorPoint_ne _ _ _ _ hq hr huv
    · intro k t ht
      rcases ht with rfl | ht
      · rcases hu k with hk | hk
        · exact Or.inl (Subtype.ext (by
            change co1BinaryAction (monsterCo1GeometryBasisSignClass k) (g⁻¹ • q).val = _
            rw [monsterCo1GeometryBasisSignClass, monsterCo1GeometrySign_binary, hq, hk]))
        · exact Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext (by
            change co1BinaryAction (monsterCo1GeometryBasisSignClass k) (g⁻¹ • q).val = _
            rw [monsterCo1GeometryBasisSignClass, monsterCo1GeometrySign_binary, hq, hr, hk])))
      · have ht' := Set.mem_singleton_iff.mp ht
        subst t
        rcases hv k with hk | hk
        · exact Or.inl (Subtype.ext (by
            change co1BinaryAction (monsterCo1GeometryBasisSignClass k) (g⁻¹ • r).val = _
            rw [monsterCo1GeometryBasisSignClass, monsterCo1GeometrySign_binary, hr, hq, hk]))
        · exact Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext (by
            change co1BinaryAction (monsterCo1GeometryBasisSignClass k) (g⁻¹ • r).val = _
            rw [monsterCo1GeometryBasisSignClass, monsterCo1GeometrySign_binary, hr, hk])))
    · refine ⟨w, Subtype.ext ?_⟩
      change co1BinaryAction (monsterCo1GeometryBasisSignClass w) (g⁻¹ • q).val = _
      rw [monsterCo1GeometryBasisSignClass, monsterCo1GeometrySign_binary, hq, hr, hw]
  have ht := monsterCo1GeometryAnchoredLine_smul g _ _ _ hl
  exact Or.inl (by simpa only [hp, smul_inv_smul] using ht)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

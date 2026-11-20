/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentExchangeSupportTag











open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



def componentExchangeSupportFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :=
  {d : leftRowSupportIndex ends m j k l zero //
    exchangeFirstRow ends d.1 (m \ d.1) k zero = R.1}

noncomputable instance instFintypeComponentExchangeSupportFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype (componentExchangeSupportFiber ends m j k l zero R) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun d =>
    exchangeFirstRow ends d.1 (m \ d.1) k zero = R.1) (by simp)


def rightRowDataIndexFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :=
  {d : rightRowData ends m j k l zero // d.1 = R}

noncomputable instance instFintypeRightRowDataIndexFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype (rightRowDataIndexFiber ends m j k l zero R) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun d => d.1 = R) (by simp)



noncomputable def rightRowDataIndexFiberEquiv
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    rightRowDataIndexFiber ends m j k l zero R ≃
      boundarySector ends R.1 {j, k} × boundarySector ends (m \ R.1) ∅ where
  toFun d := d.2 ▸ d.1.2
  invFun p := ⟨⟨R, p⟩, rfl⟩
  left_inv d := by
    rcases d with ⟨⟨K, p⟩, hK⟩
    dsimp at hK ⊢
    subst K
    rfl
  right_inv p := rfl



theorem rightRowDataIndexFiber_card_eq_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype.card (rightRowDataIndexFiber ends m j k l zero R) =
      rowSupportWeight ends m R.1 := by
  classical
  rw [Fintype.card_congr
    (rightRowDataIndexFiberEquiv ends m j k l zero R), Fintype.card_prod]
  rcases R.2.2.2.1 with ⟨P, hPsub, hPsrc⟩
  let hP : boundarySector ends R.1 {j, k} := ⟨P, hPsub, hPsrc⟩
  rw [boundarySector_card_eq_cycle ends R.1 {j, k} hP]
  rfl




noncomputable def componentExchangeSupportFiberEmbedding
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (R : rightRowSupportIndex ends m j k l zero) :
    componentExchangeSupportFiber ends m j k l zero R ↪
      rightRowDataIndexFiber ends m j k l zero R where
  toFun d := ⟨componentExchangeSupportTag ends m j k l zero
      hloop hjk hkl hk0 d.1, by
    apply Subtype.ext
    exact d.2⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    apply componentExchangeSupportTag_injective
      ends m j k l zero hloop hjk hkl hk0
    exact congrArg Subtype.val hde



theorem card_componentExchangeSupportFiber_le_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype.card (componentExchangeSupportFiber ends m j k l zero R) ≤
      rowSupportWeight ends m R.1 := by
  rw [← rightRowDataIndexFiber_card_eq_weight ends m j k l zero R]
  exact Fintype.card_le_of_injective
    (componentExchangeSupportFiberEmbedding ends m j k l zero
      hloop hjk hkl hk0 R)
    (componentExchangeSupportFiberEmbedding ends m j k l zero
      hloop hjk hkl hk0 R).injective



theorem leftRowData_card_eq_leftRowSupportIndex_of_unit_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K →
      rowSupportWeight ends m K = 1) :
    Fintype.card (leftRowData ends m j k l zero) =
      Fintype.card (leftRowSupportIndex ends m j k l zero) := by
  classical
  rw [leftRowData_card_eq_weightedSum]
  calc
    (∑ K ∈ leftRowSupports ends m j k l zero,
        rowSupportWeight ends m K) =
        ∑ K ∈ leftRowSupports ends m j k l zero, 1 := by
      apply Finset.sum_congr rfl
      intro K hK
      have hK' : K ⊆ m ∧ LeftRowSupport ends m j k l zero K := by
        simpa [leftRowSupports] using hK
      exact hunit K hK'.1 hK'.2
    _ = (leftRowSupports ends m j k l zero).card := by simp
    _ = Fintype.card (leftRowSupportIndex ends m j k l zero) := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun K => by
        simp [leftRowSupports])





theorem GrahamWeightedRowMinor_of_unit_left_support_weights
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K →
      rowSupportWeight ends m K = 1) :
    GrahamWeightedRowMinor ends m j k l zero := by
  unfold GrahamWeightedRowMinor
  rw [← leftRowData_card_eq_weightedSum,
    leftRowData_card_eq_leftRowSupportIndex_of_unit_weight ends m j k l zero hunit,
    ← rightRowData_card_eq_weightedSum]
  exact card_leftRowSupportIndex_le_rightRowData
    ends m j k l zero hloop hjk hkl hk0

end StatMech.GrahamGHS.FourColor

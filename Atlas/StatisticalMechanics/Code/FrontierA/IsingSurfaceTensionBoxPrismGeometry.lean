/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionSheetGauge

namespace StatMech.FrontierA

open StatMech Lattice Sharpness


abbrev CenteredInt (n : Nat) := {z : Int // z.natAbs <= n}



def finOddEquivCenteredInt (n : Nat) : Fin (2 * n + 1) ≃ CenteredInt n where
  toFun i := ⟨(i.val : Int) - n, by
    have hi := i.isLt
    omega⟩
  invFun z := ⟨(z.1 + n).toNat, by
    have hzLower : -(n : Int) <= z.1 := by
      have := z.2
      omega
    have hzUpper : z.1 <= n := by
      have := z.2
      omega
    have hnonneg : 0 <= z.1 + n := by omega
    have hcast : ((z.1 + n).toNat : Int) = z.1 + n :=
      Int.toNat_of_nonneg hnonneg
    omega⟩
  left_inv i := by
    apply Fin.ext
    change (((i.val : Int) - n + n).toNat) = i.val
    rw [sub_add_cancel]
    exact Int.toNat_natCast i.val
  right_inv z := by
    apply Subtype.ext
    change ((((z.1 + n).toNat : Nat) : Int) - n) = z.1
    have hzLower : -(n : Int) <= z.1 := by
      have := z.2
      omega
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n)]
    ring

@[simp] theorem finOddEquivCenteredInt_apply_val
    (n : Nat) (i : Fin (2 * n + 1)) :
    (finOddEquivCenteredInt n i).1 = (i.val : Int) - n := rfl



def rectangularPrismSiteCentered (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite
      (2 * n + 1) (2 * n + 1) n) : Site 3 :=
  fun i => if i = (0 : Fin 3) then (finOddEquivCenteredInt n v.x).1
    else if i = (1 : Fin 3) then (finOddEquivCenteredInt n v.y).1
    else (finOddEquivCenteredInt n v.z).1

def rectangularPrismSiteEquivSctBox (n : Nat) :
    StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n ≃
      {x : Site 3 // x ∈ box 3 n} where
  toFun v := ⟨rectangularPrismSiteCentered n v, by
    intro i
    fin_cases i
    · exact (finOddEquivCenteredInt n v.x).2
    · exact (finOddEquivCenteredInt n v.y).2
    · exact (finOddEquivCenteredInt n v.z).2⟩
  invFun z :=
    ⟨(finOddEquivCenteredInt n).symm ⟨z.1 0, z.2 0⟩,
      (finOddEquivCenteredInt n).symm ⟨z.1 1, z.2 1⟩,
      (finOddEquivCenteredInt n).symm ⟨z.1 2, z.2 2⟩⟩
  left_inv v := by
    rcases v with ⟨x, y, z⟩
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    simp only [rectangularPrismSiteCentered, if_pos, Fin.isValue]
    exact ⟨(finOddEquivCenteredInt n).symm_apply_apply x,
      (finOddEquivCenteredInt n).symm_apply_apply y,
      (finOddEquivCenteredInt n).symm_apply_apply z⟩
  right_inv z := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [rectangularPrismSiteCentered]


def reflectThirdBoxEquiv (n : Nat) :
    {x : Site 3 // x ∈ box 3 n} ≃ {x : Site 3 // x ∈ box 3 n} where
  toFun x := ⟨fun i => if i = (2 : Fin 3) then -x.1 i else x.1 i, by
    intro i
    by_cases hi : i = (2 : Fin 3)
    · subst i
      simpa using x.2 (2 : Fin 3)
    · simpa [hi] using x.2 i
  ⟩
  invFun x := ⟨fun i => if i = (2 : Fin 3) then -x.1 i else x.1 i, by
    intro i
    by_cases hi : i = (2 : Fin 3)
    · subst i
      simpa using x.2 (2 : Fin 3)
    · simpa [hi] using x.2 i
  ⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = (2 : Fin 3) <;> simp [hi]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = (2 : Fin 3) <;> simp [hi]




def rectangularPrismSiteEquivSctBoxDobrushin (n : Nat) :
    StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n ≃
      {x : Site 3 // x ∈ box 3 n} :=
  (rectangularPrismSiteEquivSctBox n).trans (reflectThirdBoxEquiv n)

@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_zero
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 0 =
      (v.x.val : Int) - n := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]

@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_one
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 1 =
      (v.y.val : Int) - n := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]

@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_two
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 2 =
      (n : Int) - v.z.val := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]




theorem interfaceField_rectangularPrismSiteEquivSctBoxDobrushin
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    StatMech.Ising.interfaceField (⟨2, by omega⟩ : Fin 3)
        (rectangularPrismSiteEquivSctBoxDobrushin n v).1 =
      decide (v.z.val <= n) := by
  change decide (0 <=
      (rectangularPrismSiteEquivSctBoxDobrushin n v).1 2) = _
  rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_two]
  simp only [sub_nonneg]
  norm_cast



def rectangularPrismConfigEquivSctBoxDobrushin (n : Nat) :
    StatMech.Ising.RectangularPrismConfig (2 * n + 1) (2 * n + 1) n ≃
      ({x : Site 3 // x ∈ box 3 n} -> Bool) :=
  Equiv.arrowCongr (rectangularPrismSiteEquivSctBoxDobrushin n)
    (Equiv.refl Bool)

@[simp] theorem rectangularPrismConfigEquivSctBoxDobrushin_apply
    (n : Nat)
    (sigma : StatMech.Ising.RectangularPrismConfig
      (2 * n + 1) (2 * n + 1) n)
    (v : StatMech.Ising.RectangularPrismSite
      (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismConfigEquivSctBoxDobrushin n sigma
        (rectangularPrismSiteEquivSctBoxDobrushin n v) = sigma v := by
  simp [rectangularPrismConfigEquivSctBoxDobrushin]

end StatMech.FrontierA

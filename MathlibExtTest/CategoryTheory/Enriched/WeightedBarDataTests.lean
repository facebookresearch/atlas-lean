/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Enriched.WeightedBarData

/-!
# Weighted-bar data public contract

Selective public-contract coverage for the strict ordinary weighted bar data.
-/

namespace CategoryTheory.StrictOrdinaryWeightedBar.WeightedBarDataTests

open CategoryTheory
open CategoryTheory.StrictOrdinaryWeightedBar

universe vJ uJ vC uC uW

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (W : Jᵒᵖ ⥤ Type uW) (F : J ⥤ C)
variable [∀ n, Limits.HasCoproduct (fun p : WIdx J W n => F.obj p.1.left)]

/-! ## Packaged data -/

example (n : ℕ) : (wbarData W F).obj n = wbarObj W F n :=
  wbarData_obj W F n

example {n : ℕ} (i : Fin (n + 2)) : (wbarData W F).δ i = wbarδ W F n i :=
  wbarData_δ W F i

example {n : ℕ} (i : Fin (n + 1)) : (wbarData W F).σ i = wbarσ W F n i :=
  wbarData_σ W F i

/-! ## Dispatch -/

example (n : ℕ) : wbarδ W F n 0 = wbarFaceZero W F n :=
  wbarδ_zero W F n

example (n : ℕ) : wbarδ W F n (Fin.last (n + 1)) = wbarFaceLast W F n :=
  wbarδ_last W F n

example (n : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1)) :
    wbarδ W F n i = wbarFaceInner W F n i hi0 hiLast :=
  wbarδ_inner W F n i hi0 hiLast

example (n : ℕ) (i : Fin (n + 1)) (p : WIdx J W n) :
    wbarIncl W F n p ≫ wbarσ W F n i =
      wDegInnerComponent F i p.1 ≫
        wbarIncl W F (n + 1) (wDegInnerIdx W n i p) :=
  wbarσ_ι W F n i p

example (n : ℕ) : wbarσ W F n 0 = wbarDegZero W F n :=
  wbarσ_zero W F n

/-! ## Simplicial identities -/

example (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j) :
    wbarσ W F n j ≫ wbarσ W F (n + 1) i.castSucc =
      wbarσ W F n i ≫ wbarσ W F (n + 1) j.succ :=
  wbar_σ_comp_σ W F n h

example (n : ℕ) {i : Fin (n + 1)} :
    wbarσ W F n i ≫ wbarδ W F n i.castSucc = 𝟙 (wbarObj W F n) :=
  wbar_δ_comp_σ_self W F n

example (n : ℕ) {i : Fin (n + 1)} :
    wbarσ W F n i ≫ wbarδ W F n i.succ = 𝟙 (wbarObj W F n) :=
  wbar_δ_comp_σ_succ W F n

example (n : ℕ) {i j : Fin (n + 2)} (h : i ≤ j) :
    wbarδ W F (n + 1) j.succ ≫ wbarδ W F n i =
      wbarδ W F (n + 1) i.castSucc ≫ wbarδ W F n j :=
  wbar_δ_comp_δ W F n h

example : wbarσ W F 1 (0 : Fin 1).succ ≫ wbarδ W F 1 (0 : Fin 2).castSucc =
    wbarδ W F 0 0 ≫ wbarσ W F 0 0 :=
  wbar_δ_comp_σ_of_le W F 0 (by decide)

example : wbarσ W F 1 (0 : Fin 1).castSucc ≫ wbarδ W F 1 (Fin.last 1).succ =
    wbarδ W F 0 (Fin.last 1) ≫ wbarσ W F 0 0 :=
  wbar_δ_comp_σ_of_gt W F 0 (by decide)

end CategoryTheory.StrictOrdinaryWeightedBar.WeightedBarDataTests

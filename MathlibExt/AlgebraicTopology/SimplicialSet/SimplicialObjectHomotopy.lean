/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# From combinatorial homotopies to simplicial-set homotopies

A combinatorial `SimplicialObject.Homotopy` between maps of simplicial sets
determines a cylinder map `X ⊗ Δ[1] ⟶ Y`.  In degree `n`, an interval simplex
is determined by the number of its initial zeroes.  Cut zero uses the second
endpoint, while cut `j + 1` uses `H.h j` followed by face `j + 1`.

This is inverse, on combinatorial homotopies, to Mathlib's existing
`SSet.Homotopy.toSimplicialObjectHomotopy`.  This file contains no realization,
weak-equivalence, extra-degeneracy, model-category, or edgewise result.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet.stdSimplex

/-- The `n`-simplices of `Δ[1]` are classified by their number of initial
zeroes. -/
noncomputable def objMk₁Equiv (n : ℕ) :
    Fin (n + 2) ≃ (Δ[1] : SSet.{u}).obj (op ⦋n⦌) :=
  Equiv.ofBijective objMk₁ objMk₁_bijective

@[simp]
theorem objMk₁Equiv_apply (n : ℕ) (i : Fin (n + 2)) :
    objMk₁Equiv.{u} n i = objMk₁ i :=
  rfl

@[simp]
theorem objMk₁Equiv_symm_objMk₁ (n : ℕ) (i : Fin (n + 2)) :
    (objMk₁Equiv.{u} n).symm (objMk₁ i) = i :=
  (objMk₁Equiv.{u} n).symm_apply_apply i

end SSet.stdSimplex

namespace CategoryTheory.SimplicialObject.Homotopy

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

/-- Degree-`n` function underlying the cylinder map of a combinatorial
simplicial homotopy. -/
private noncomputable def toSSetHomotopyMapApp
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (X ⊗ (Δ[1] : SSet.{u})).obj (op ⦋n⦌) →
      Y.obj (op ⦋n⦌) := fun z =>
  Fin.cases (g.app (op ⦋n⦌) z.1)
    (fun j => (H.h j ≫ Y.δ j.succ) z.1)
    ((SSet.stdSimplex.objMk₁Equiv n).symm z.2)

@[simp]
private theorem toSSetHomotopyMapApp_objMk₁_zero
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (x : X.obj (op ⦋n⦌)) :
    toSSetHomotopyMapApp H n
        (x, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
      g.app (op ⦋n⦌) x := by
  simp [toSSetHomotopyMapApp]

@[simp]
private theorem toSSetHomotopyMapApp_objMk₁_succ
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (x : X.obj (op ⦋n⦌)) (j : Fin (n + 1)) :
    toSSetHomotopyMapApp H n
        (x, SSet.stdSimplex.objMk₁ j.succ) =
      (H.h j ≫ Y.δ j.succ) x := by
  simp [toSSetHomotopyMapApp]

/-- Components of the cylinder map before the naturality proof. -/
private noncomputable def toSSetHomotopyMapAppNat
    (H : SimplicialObject.Homotopy f g)
    (a : SimplexCategoryᵒᵖ) :
    (X ⊗ (Δ[1] : SSet.{u})).obj a ⟶ Y.obj a := by
  induction a using Opposite.rec with
  | _ a =>
      induction a using SimplexCategory.rec with
      | _ n => exact ↾(toSSetHomotopyMapApp H n)

/-- Simplex operators for which the cut formula is natural. -/
private abbrev toSSetHomotopyMapNaturality
    (H : SimplicialObject.Homotopy f g) :
    MorphismProperty SimplexCategory :=
  (MorphismProperty.naturalityProperty
    (toSSetHomotopyMapAppNat H)).unop

private theorem toSSetHomotopyMapNaturality_δ
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) :
    toSSetHomotopyMapNaturality H (SimplexCategory.δ i) := by
  change (X ⊗ (Δ[1] : SSet.{u})).map (SimplexCategory.δ i).op ≫
      toSSetHomotopyMapAppNat H (op ⦋n⦌) =
    toSSetHomotopyMapAppNat H (op ⦋n + 1⦌) ≫
      Y.map (SimplexCategory.δ i).op
  ext z
  rcases z with ⟨x, t⟩
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
  change toSSetHomotopyMapApp H n
      (X.δ i x, (Δ[1] : SSet.{u}).δ i
        (SSet.stdSimplex.objMk₁ k)) =
    Y.δ i
      (toSSetHomotopyMapApp H (n + 1)
        (x, SSet.stdSimplex.objMk₁ k))
  induction k using Fin.cases with
  | zero =>
      rw [SSet.stdSimplex.δ_objMk₁_of_le (0 : Fin (n + 3)) i (by simp)]
      simp [toSSetHomotopyMapApp, ← SSet.δ_naturality_apply]
  | succ j =>
      simp only [toSSetHomotopyMapApp_objMk₁_succ]
      simp only [types_comp_apply]
      by_cases hij : i ≤ j
      · have hcut : i.castSucc < j.succ := by simpa
        rw [SSet.stdSimplex.δ_objMk₁_of_lt j.succ i hcut]
        induction j using Fin.cases with
        | zero =>
            have hi : i = 0 := by
              apply Fin.ext
              exact Nat.eq_zero_of_le_zero
                (Fin.le_iff_val_le_val.mp hij)
            subst i
            simp only [Fin.succ_zero_eq_one, Fin.pred_one,
              toSSetHomotopyMapApp_objMk₁_zero]
            rw [SSet.δ_naturality_apply]
            have hH := ConcreteCategory.congr_hom
              (H.h_zero_comp_δ_zero (n + 1)) x
            rw [← hH]
            exact Y.δ_comp_δ_self_apply (i := (0 : Fin (n + 2))) _
        | succ j =>
            simp only [Fin.pred_succ,
              toSSetHomotopyMapApp_objMk₁_succ]
            by_cases hij' : i ≤ j.castSucc
            · have hface : i.castSucc < j.succ.succ := by simpa
              rw [Y.δ_comp_δ'_apply hface]
              simp only [Fin.pred_succ]
              have hH := ConcreteCategory.congr_hom
                (H.h_succ_comp_δ_castSucc_of_lt i j hij') x
              simp only [types_comp_apply] at hH
              rw [hH]
              rfl
            · have hi : i = j.succ := by
                exact le_antisymm hij
                  (Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hij'))
              subst i
              have hH := ConcreteCategory.congr_hom
                (H.h_castSucc_comp_δ_succ_of_lt j.succ j (by simp)) x
              simp only [types_comp_apply] at hH
              simp only [types_comp_apply]
              rw [← hH]
              have hAdj := ConcreteCategory.congr_hom
                (H.h_succ_comp_δ_castSucc_succ j) x
              simp only [types_comp_apply] at hAdj
              rw [← Y.δ_comp_δ_self_apply
                (i := j.succ) ((H.h j.castSucc) x)]
              rw [← Y.δ_comp_δ_self_apply
                (i := j.succ) ((H.h j.succ) x)]
              simp only [← Fin.succ_castSucc]
              rw [hAdj]
      · have hji : j < i := lt_of_not_ge hij
        have hcut : j.succ ≤ i.castSucc := by simpa
        rw [SSet.stdSimplex.δ_objMk₁_of_le j.succ i hcut]
        have hjlast : j ≠ Fin.last (n + 1) :=
          Fin.ne_last_of_lt (hji.trans_le i.le_last)
        obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last hjlast
        have hk : j.castSucc.succ.castPred (by simp) = j.succ := by
          apply Fin.ext
          rfl
        rw [hk]
        rw [toSSetHomotopyMapApp_objMk₁_succ]
        change (H.h j ≫ Y.δ j.succ) (X.δ i x) =
          Y.δ i ((H.h j.castSucc ≫ Y.δ j.castSucc.succ) x)
        simp only [types_comp_apply]
        have hH := ConcreteCategory.congr_hom
          (H.h_castSucc_comp_δ_succ_of_lt i j hji) x
        simp only [types_comp_apply] at hH
        rw [← hH]
        have hindex : j.succ.castSucc = j.castSucc.succ := by
          apply Fin.ext
          rfl
        have hcond : j.succ.castSucc ≤ i.castSucc := by
          rw [hindex]
          exact hcut
        have hδ := Y.δ_comp_δ''_apply
          (i := j.succ.castSucc) (j := i)
          hcond
          ((H.h j.castSucc) x)
        have hcast :
            j.succ.castSucc.castLT
                (Nat.lt_of_le_of_lt
                  (Fin.le_iff_val_le_val.mp hcond) i.is_lt) =
              j.succ := by
          apply Fin.ext
          rfl
        rw [hcast] at hδ
        exact hδ

private theorem toSSetHomotopyMapNaturality_σ
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i : Fin (n + 1)) :
    toSSetHomotopyMapNaturality H (SimplexCategory.σ i) := by
  change (X ⊗ (Δ[1] : SSet.{u})).map (SimplexCategory.σ i).op ≫
      toSSetHomotopyMapAppNat H (op ⦋n + 1⦌) =
    toSSetHomotopyMapAppNat H (op ⦋n⦌) ≫
      Y.map (SimplexCategory.σ i).op
  ext z
  rcases z with ⟨x, t⟩
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
  change toSSetHomotopyMapApp H (n + 1)
      (X.σ i x, (Δ[1] : SSet.{u}).σ i
        (SSet.stdSimplex.objMk₁ k)) =
    Y.σ i
      (toSSetHomotopyMapApp H n
        (x, SSet.stdSimplex.objMk₁ k))
  induction k using Fin.cases with
  | zero =>
      rw [SSet.stdSimplex.σ_objMk₁_of_le (0 : Fin (n + 2)) i (by simp)]
      simp [toSSetHomotopyMapApp, ← SSet.σ_naturality_apply]
  | succ j =>
      simp only [toSSetHomotopyMapApp_objMk₁_succ]
      simp only [types_comp_apply]
      by_cases hji : j < i
      · have hcut : j.succ ≤ i.castSucc := by simpa
        rw [SSet.stdSimplex.σ_objMk₁_of_le j.succ i hcut]
        have hk : j.succ.castSucc = j.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hk]
        rw [toSSetHomotopyMapApp_objMk₁_succ]
        simp only [types_comp_apply]
        have hH := ConcreteCategory.congr_hom
          (H.h_comp_σ_succ_of_lt i j hji.le) x
        simp only [types_comp_apply] at hH
        rw [← hH]
        have hδ := Y.δ_comp_σ_of_le_apply
          (i := j.succ) (j := i) (by simpa using hji)
          ((H.h j) x)
        have hcast : j.succ.castSucc = j.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hcast] at hδ
        exact hδ
      · have hij : i ≤ j := le_of_not_gt hji
        have hcut : i.castSucc < j.succ := by simpa
        rw [SSet.stdSimplex.σ_objMk₁_of_lt j.succ i hcut]
        rw [toSSetHomotopyMapApp_objMk₁_succ]
        simp only [types_comp_apply]
        have hH := ConcreteCategory.congr_hom
          (H.h_comp_σ_castSucc_of_le i j hij) x
        simp only [types_comp_apply] at hH
        rw [← hH]
        exact Y.δ_comp_σ_of_gt_apply hcut ((H.h j) x)

private theorem toSSetHomotopyMapNaturality_eq_top
    (H : SimplicialObject.Homotopy f g) :
    toSSetHomotopyMapNaturality H = ⊤ := by
  apply SimplexCategory.morphismProperty_eq_top
  · exact toSSetHomotopyMapNaturality_δ H
  · exact toSSetHomotopyMapNaturality_σ H

/-- The cylinder map induced by a combinatorial simplicial homotopy. -/
noncomputable def toSSetHomotopyMap
    (H : SimplicialObject.Homotopy f g) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y where
  app := toSSetHomotopyMapAppNat H
  naturality {a b} φ :=
    (toSSetHomotopyMapNaturality_eq_top H).symm.le
      φ.unop (by simp)

/-- At cut zero, the cylinder map is the second endpoint. -/
@[simp]
theorem toSSetHomotopyMap_app_objMk₁_zero
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (x : X.obj (op ⦋n⦌)) :
    (ConcreteCategory.hom
      (X := X.obj (op ⦋n⦌) ⊗ (Δ[1] : SSet.{u}).obj (op ⦋n⦌))
      (Y := Y.obj (op ⦋n⦌))
      (H.toSSetHomotopyMap.app (op ⦋n⦌)))
        (x, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) =
      g.app (op ⦋n⦌) x :=
  toSSetHomotopyMapApp_objMk₁_zero H n x

/-- At cut `j + 1`, the cylinder map is `H.h j` followed by face
`j + 1`. -/
@[simp]
theorem toSSetHomotopyMap_app_objMk₁_succ
    (H : SimplicialObject.Homotopy f g) (n : ℕ)
    (x : X.obj (op ⦋n⦌)) (j : Fin (n + 1)) :
    (ConcreteCategory.hom
      (X := X.obj (op ⦋n⦌) ⊗ (Δ[1] : SSet.{u}).obj (op ⦋n⦌))
      (Y := Y.obj (op ⦋n⦌))
      (H.toSSetHomotopyMap.app (op ⦋n⦌)))
        (x, SSet.stdSimplex.objMk₁ j.succ) =
      (H.h j ≫ Y.δ j.succ) x :=
  toSSetHomotopyMapApp_objMk₁_succ H n x j

private theorem ι₀_app_snd_eq_objMk₁_last
    (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (SSet.ι₀.app (op ⦋n⦌) x).2 =
      SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) := by
  ext k
  change (0 : ℕ) = _
  rw [SSet.stdSimplex.objMk₁_apply]
  simp

private theorem ι₁_app_snd_eq_objMk₁_zero
    (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    (SSet.ι₁.app (op ⦋n⦌) x).2 =
      SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) := by
  ext k
  change (1 : ℕ) = _
  rw [SSet.stdSimplex.objMk₁_apply]
  simp

/-- A combinatorial simplicial homotopy gives a simplicial-set cylinder
homotopy with the same orientation. -/
noncomputable def toSSetHomotopy
    (H : SimplicialObject.Homotopy f g) :
    SSet.Homotopy f g where
  h := H.toSSetHomotopyMap
  h₀ := by
    ext a x
    induction a using Opposite.rec with
    | _ a =>
        induction a using SimplexCategory.rec with
        | _ n =>
            change toSSetHomotopyMapApp H n (SSet.ι₀.app (op ⦋n⦌) x) =
              f.app (op ⦋n⦌) x
            have hp : SSet.ι₀.app (op ⦋n⦌) x =
                (x, SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) := by
              apply Prod.ext
              · exact SSet.ι₀_app_fst x
              · exact ι₀_app_snd_eq_objMk₁_last n x
            rw [hp]
            have hlast : Fin.last (n + 1) = (Fin.last n).succ := by
              apply Fin.ext
              rfl
            rw [hlast, toSSetHomotopyMapApp_objMk₁_succ]
            exact ConcreteCategory.congr_hom
              (H.h_last_comp_δ_last n) x
  h₁ := by
    ext a x
    induction a using Opposite.rec with
    | _ a =>
        induction a using SimplexCategory.rec with
        | _ n =>
            change toSSetHomotopyMapApp H n (SSet.ι₁.app (op ⦋n⦌) x) =
              g.app (op ⦋n⦌) x
            have hp : SSet.ι₁.app (op ⦋n⦌) x =
                (x, SSet.stdSimplex.objMk₁ (0 : Fin (n + 2))) := by
              apply Prod.ext
              · exact SSet.ι₁_app_fst x
              · exact ι₁_app_snd_eq_objMk₁_zero n x
            rw [hp, toSSetHomotopyMapApp_objMk₁_zero]
  rel := by
    ext a z
    exact z.1.2.elim

@[reassoc]
theorem toSSetHomotopy_h₀
    (H : SimplicialObject.Homotopy f g) :
    SSet.ι₀ ≫ H.toSSetHomotopy.h = f :=
  H.toSSetHomotopy.h₀

@[reassoc]
theorem toSSetHomotopy_h₁
    (H : SimplicialObject.Homotopy f g) :
    SSet.ι₁ ≫ H.toSSetHomotopy.h = g :=
  H.toSSetHomotopy.h₁

/-- Converting a combinatorial homotopy to a cylinder homotopy and back
recovers the original combinatorial homotopy. -/
@[simp]
theorem toSSetHomotopy_toSimplicialObjectHomotopy
    (H : SimplicialObject.Homotopy f g) :
    H.toSSetHomotopy.toSimplicialObjectHomotopy = H := by
  apply SimplicialObject.Homotopy.ext
  funext n i
  ext x
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy,
    TypeCat.Fun.toFun_apply, TypeCat.hom_ofHom]
  change (H.toSSetHomotopyMap.app (op ⦋n + 1⦌))
      (((SSet.yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u})).app
        (op ⦋n + 1⦌))
        (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val) =
    H.h i x
  have hp :
      ((SSet.yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u})).app
        (op ⦋n + 1⦌))
          (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val =
        (X.σ i x, SSet.stdSimplex.objMk₁ i.succ.castSucc) := by
    apply Prod.ext
    · change (SSet.yonedaEquiv.symm x).app (op ⦋n + 1⦌)
          (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ i)) =
        X.σ i x
      rw [SSet.yonedaEquiv_symm_app]
      rw [Equiv.apply_symm_apply]
      rfl
    · change SSet.stdSimplex.objMk₁ i.succ.castSucc =
        SSet.stdSimplex.objMk₁ i.succ.castSucc
      rfl
  rw [hp]
  have hcut : i.succ.castSucc = i.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hcut]
  change (ConcreteCategory.hom
      (X := X.obj (op ⦋n + 1⦌) ⊗ (Δ[1] : SSet.{u}).obj (op ⦋n + 1⦌))
      (Y := Y.obj (op ⦋n + 1⦌))
      (H.toSSetHomotopyMap.app (op ⦋n + 1⦌)))
      (X.σ i x, SSet.stdSimplex.objMk₁ i.castSucc.succ) = H.h i x
  have hSucc := toSSetHomotopyMap_app_objMk₁_succ H (n + 1) (X.σ i x) i.castSucc
  refine hSucc.trans ?_
  simp only [types_comp_apply]
  have hH := ConcreteCategory.congr_hom
    (H.h_comp_σ_succ_of_lt i i le_rfl) x
  simp only [types_comp_apply] at hH
  rw [← hH]
  have hindex : i.castSucc.succ = i.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact Y.δ_comp_σ_self_apply i.succ ((H.h i) x)

end CategoryTheory.SimplicialObject.Homotopy

end

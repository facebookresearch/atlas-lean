/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontRestriction

/-!
# All original simplex-operator laws of the whole Hom construction

The entire enriched simplex constructed from a supplied original Hom
simplex commutes with every actual right-join operator. Original
front, last and empty reverse intervals remain separate in the proof.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomWholeOperators
open SimplicialEnrichment HomSimplex HomSimplexOperators HomSimplexNaturality PathMaximumOperators
variable {C : Carrier.{u}} {n m : ℕ} (x y : C)

private theorem whole_ext {A B : Carrier.{u}} (F G : A ⟶ B)
    (ho : ∀ a, F.obj a = G.obj a) (hm : ∀ a b, F.map a b ≍ G.map a b) : F = G := by
  refine EnrichedFunctor.ext SSet.{u} ho ?_
  intro a b
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hm a b))

private theorem front_hom_at {X : SSet.{u}} (τ : (Δ[m] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))
    {a b : Fin (m + 2)} (i j : Fin (m + 1)) (hi : a = i.castSucc) (hj : b = j.castSucc)
    (U : X ⟶ nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))) :
    U ≫ homMap x y τ a b ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        ((congrArg (HomSimplex.object x y) hi).trans (object_front x y i))
        ((congrArg (HomSimplex.object x y) hj).trans (object_front x y j))) = toUnit X ≫
          eId SSet.{u} x := by
  subst a
  subst b
  have h := homMap_front x y τ i j
  have hU : U ≫ toUnit _ = toUnit X := by ext q p; rfl
  exact (Category.assoc U _ _).trans
    ((congrArg (fun f => U ≫ f) h).trans
      ((Category.assoc U _ _).symm.trans (congrArg (fun f => f ≫ eId SSet.{u} x) hU)))

private theorem homMap_last_heq (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) (i : Fin (n + 1)) :
    homMap x y τ i.castSucc (Fin.last (n + 1)) ≍ lastMap x y τ i :=
  (comp_eqToHom_heq _ _).symm.trans (heq_of_eq (homMap_last x y τ i))

private theorem homMap_front_heq (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) (i j : Fin (n + 1)) :
    homMap x y τ i.castSucc j.castSucc ≍
      (toUnit (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
        j.castSucc))) ≫ eId
        SSet.{u} x) :=
  (comp_eqToHom_heq _ _).symm.trans (heq_of_eq (homMap_front x y τ i j))

/-- The entire original enriched simplex follows every actual front simplex operator joined
with the last identity. -/
theorem simplex_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) (τ : (Δ[m] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) :
    coherentSimplexMap (extension θ) ≫ simplex x y τ = simplex x y (SSet.stdSimplex.map θ ≫ τ) := by
  let F := coherentSimplexMap (extension θ)
  let L := F ≫ simplex x y τ
  let R := simplex x y (SSet.stdSimplex.map θ ≫ τ)
  have ho : ∀ a : coherentSimplex.{u} ⦋n + 1⦌, L.obj a = R.obj a :=
    fun a => object_naturality x y θ a.as.down
  apply whole_ext L R ho
  intro a b
  cases a with | mk a =>
    cases a with | up a =>
      cases b with | mk b =>
        cases b with | up b =>
          cases a using Fin.lastCases with
          | last =>
            cases b using Fin.lastCases with
            | last =>
              have hId := L.map_id (.mk (ULift.up (Fin.last (n + 1))))
              have hRI := R.map_id (.mk (ULift.up (Fin.last (n + 1))))
              let e := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
                (ho (.mk (ULift.up (Fin.last (n + 1))))) (ho (.mk (ULift.up (Fin.last (n + 1))))))
              have h : L.map (.mk (ULift.up (Fin.last (n + 1)))) (.mk (ULift.up (Fin.last (n
                + 1)))) ≫ e =
                  R.map (.mk (ULift.up (Fin.last (n + 1)))) (.mk (ULift.up (Fin.last (n +
                    1)))) := by
                let := HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (Fin.last (n + 1)))
                apply (cancel_epi (eId SSet.{u} (.mk (ULift.up (Fin.last (n + 1))) :
                  coherentSimplex.{u} ⦋n + 1⦌))).mp
                exact (Category.assoc _ _ _).symm.trans
                  ((congrArg (fun f => f ≫ e) hId).trans
                    ((EqualityTransport.identity (ho (.mk (ULift.up (Fin.last (n +
                      1)))))).trans hRI.symm))
              exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)
            | cast j =>
              apply (conj_eqToHom_iff_heq _ _ rfl (congrArg₂ (fun a b : C =>
                a ⟶[SSet.{u}] b) (ho (.mk
                (ULift.up (Fin.last (n + 1))))) (ho (.mk (ULift.up j.castSucc))))).mp
              rw [eqToHom_refl, Category.id_comp]
              apply HomUnitsAndEmpty.empty_hom_ext
                (show ¬(ULift.up.{u} (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2))) ≤
                  ULift.up j.castSucc
                  from not_le.mpr (Fin.castSucc_lt_last j))
          | cast i =>
            cases b using Fin.lastCases with
            | last =>
              have h := last_hom_operator x y θ τ i
              have hL : L.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up (Fin.last (n + 1)))) ≍
                  lastMap x y (SSet.stdSimplex.map θ ≫ τ) i :=
                (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)
              exact hL.trans (homMap_last_heq x y (SSet.stdSimplex.map θ ≫ τ) i).symm
            | cast j =>
              have h := front_hom_at x y τ (θ.toOrderHom i) (θ.toOrderHom j)
                (extension_front θ i) (extension_front θ j) (F.map (.mk (ULift.up i.castSucc)) (.mk
                  (ULift.up j.castSucc)))
              have hL : L.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up j.castSucc)) ≍
                  (toUnit (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
                    j.castSucc))) ≫ eId SSet.{u} x) :=
                (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)
              exact hL.trans (homMap_front_heq x y (SSet.stdSimplex.map θ ≫ τ) i j).symm

end CategoryTheory.CoherentRealization.HomWholeOperators

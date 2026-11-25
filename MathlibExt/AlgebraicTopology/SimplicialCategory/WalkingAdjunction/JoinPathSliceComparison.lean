/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinder
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction

/-!
# The actual join-slice to path-slice comparison

The original cylinder-to-cone map turns every whole join cone into
its actual internal path. The original base and apex equations give
the canonical map from the existing join slice to the existing path
slice, with the identical leading projection. Whole precomposition
and postcomposition equations make this map natural in the original
ambient simplicial set. This constructs the map and its readback;
categorical equivalence is a separate geometric theorem.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeCylinder

/-- The actual internal path of a whole original join cone. -/
def pathOfJoinCone {A H : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H) : A ⟶ pathSpace H :=
  MonoidalClosed.curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ coneCylinder A ≫ q)

/-- Initial evaluation retains the entire original cone base. -/
theorem pathOfJoinCone_zero {A H : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    pathOfJoinCone q ≫ eval₀ = joinInl A Δ[0] ≫ q := by
  rw [comp_eval₀_eq_ι₀_braiding_uncurry, pathOfJoinCone, MonoidalClosed.uncurry_curry,
    SymmetricCategory.symmetry_assoc, ← Category.assoc, coneCylinder_zero]

/-- Final evaluation retains the entire original constant cone apex. -/
theorem pathOfJoinCone_one {A H : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    pathOfJoinCone q ≫ eval₁ = SSet.stdSimplex.isTerminalObj₀.from A ≫ joinInr A Δ[0] ≫ q := by
  rw [comp_eval₁_eq_ι₁_braiding_uncurry, pathOfJoinCone, MonoidalClosed.uncurry_curry,
    SymmetricCategory.symmetry_assoc, ← Category.assoc, coneCylinder_one, Category.assoc]

/-- Precomposition of the whole cone is precomposition of its actual internal path. -/
theorem pathOfJoinCone_precomp {A B H : SSet.{u}} (p : B ⟶ A) (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    pathOfJoinCone ((join.map p).app Δ[0] ≫ q) = p ≫ pathOfJoinCone q := by
  apply MonoidalClosed.uncurry_injective
  simp only [pathOfJoinCone, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  have ht : (p ▷ (Δ[1] : SSet.{u})) ≫ coneCylinder A ≫ q =
      coneCylinder B ≫ (join.map p).app Δ[0] ≫ q :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ q) (coneCylinder_naturality p)).trans (Category.assoc _ _ _))
  exact (congrArg (fun h => (β_ (Δ[1] : SSet.{u}) B).hom ≫ h) ht).symm

/-- Postcomposition of the whole cone is the literal original internal-Hom map on its path. -/
theorem pathOfJoinCone_postcomp {A H K : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H) (p : H ⟶ K) :
    pathOfJoinCone (q ≫ p) = pathOfJoinCone q ≫ (ihom (Δ[1] : SSet.{u})).map p := by
  simpa only [pathOfJoinCone, Category.assoc] using
    MonoidalClosed.curry_natural_right ((β_ (Δ[1] : SSet.{u}) A).hom ≫ coneCylinder A ≫ q) p

/-- The map from the existing original join slice to the existing original path slice. -/
def joinToPath (H : SSet.{u}) (z : (Δ[0] : SSet.{u}) ⟶ H) : sliceOver H z ⟶ pathSliceOver z :=
  pathSliceOver.lift z (pathOfJoinCone (sliceOver.evaluation H z)) (by
    rw [pathOfJoinCone_one, sliceOver.joinInr_evaluation])

/-- Reading the whole underlying path returns the actual curried original join cone. -/
theorem joinToPath_fst (H : SSet.{u}) (z : (Δ[0] : SSet.{u}) ⟶ H) :
    joinToPath H z ≫ pathSliceOver.fst z = pathOfJoinCone (sliceOver.evaluation H z) :=
  pathSliceOver.lift_fst _ _ _

/-- The comparison fixes the identical whole original leading projection. -/
theorem joinToPath_proj (H : SSet.{u}) (z : (Δ[0] : SSet.{u}) ⟶ H) :
    joinToPath H z ≫ pathSliceOver.proj z = sliceOver.proj H z := by
  rw [pathSliceOver.proj, ← Category.assoc, joinToPath_fst, pathOfJoinCone_zero,
    sliceOver.joinInl_evaluation]

/-- The whole original join evaluation is natural under the actual ambient slice map. -/
theorem joinSlice_map_evaluation {H K : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H) (p : H ⟶ K) :
    (join.map (sliceOver.map H z p)).app Δ[0] ≫ sliceOver.evaluation K (z ≫ p) =
      sliceOver.evaluation H z ≫ p := by
  let g : {q : sliceOver H z ⋆ (Δ[0] : SSet.{u}) ⟶ K // joinInr (sliceOver H z) Δ[0] ≫ q = z ≫ p} :=
    ⟨sliceOver.evaluation H z ≫ p, by rw [← Category.assoc, sliceOver.joinInr_evaluation]⟩
  let L := (sliceOver.homEquiv K (z ≫ p) (sliceOver H z)).symm g
  have hL : L = sliceOver.map H z p := by
    dsimp only [L]
    rw [sliceOver.homEquiv_symm_apply]
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (join.map (SSet.yonedaEquiv.symm s)).app Δ[0] ≫ (sliceOver.evaluation H z ≫ p) = s.1 ≫ p
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ p) (sliceOver.evaluation_wholeMap H z n.unop s))
  have he := congrArg Subtype.val ((sliceOver.homEquiv K (z ≫ p) (sliceOver H z)).apply_symm_apply g)
  rw [sliceOver.homEquiv_apply] at he
  change (join.map L).app Δ[0] ≫ sliceOver.evaluation K (z ≫ p) = sliceOver.evaluation H z ≫ p at he
  rw [hL] at he
  exact he

/-- The actual comparison commutes with both original whole ambient slice maps. -/
theorem joinToPath_naturality {H K : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H) (p : H ⟶ K) :
    sliceOver.map H z p ≫ joinToPath K (z ≫ p) = joinToPath H z ≫ pathSliceOver.map z p := by
  apply pathSliceOver.hom_ext
  rw [Category.assoc, joinToPath_fst, Category.assoc, pathSliceOver.map_fst,
    ← Category.assoc, joinToPath_fst]
  rw [← pathOfJoinCone_precomp, joinSlice_map_evaluation, pathOfJoinCone_postcomp]

/-- In dimension zero the actual cylinder map is the original second projection. -/
theorem simplexCollapse_zero_dim : simplexCollapse.{u} 0 =
    CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) Δ[1] := by
  ext ⟨⟨m⟩⟩ : 3
  funext s
  apply SSet.stdSimplex.ext
  intro i
  change (if s.2 i = 0 then (s.1 i).castSucc else Fin.last 1) = s.2 i
  have hz : s.1 i = 0 := Fin.eq_zero _
  by_cases hy : s.2 i = 0
  · have hc : (s.1 i).castSucc = (0 : Fin 2) := congrArg Fin.castSucc hz
    exact (ite_eq_left hy).trans (hc.trans hy.symm)
  · have hone : s.2 i = 1 := by
      apply Fin.ext
      have hlt := (s.2 i).isLt
      have hne : (s.2 i).val ≠ 0 := fun h => hy (Fin.ext h)
      change (s.2 i).val = 1
      omega
    exact (ite_eq_right hy).trans hone.symm

/-- The whole name of an original cone edge is the canonical internal-Hom vertex name of that same edge. -/
theorem pathOfJoinCone_point_name {A H : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (p : (Δ[0] : SSet.{u}) ⟶ A) (e : (Δ[1] : SSet.{u}) ⟶ H)
    (hq : (join.map p).app Δ[0] ≫ q = (joinStdSimplexIso 0 0).hom ≫ e) :
    p ≫ pathOfJoinCone q = SSet.yonedaEquiv.symm (ihomVertexEquiv Δ[1] H e) := by
  have hpq : (p ▷ (Δ[1] : SSet.{u})) ≫ coneCylinder A ≫ q = simplexCollapse 0 ≫ e := by
    have hfac : (p ▷ (Δ[1] : SSet.{u})) ≫ coneCylinder A ≫ q =
        simplexCone 0 ≫ (join.map p).app Δ[0] ≫ q :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ q) (coneCylinder_simplex p)).trans (Category.assoc _ _ _))
    exact hfac.trans ((congrArg (fun h => simplexCone 0 ≫ h) hq).trans
      (by simp only [simplexCone, Category.assoc, Iso.inv_hom_id_assoc]))
  have hl : MonoidalClosed.uncurry (p ≫ pathOfJoinCone q) =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u}) Δ[0] ≫ e := by
    rw [MonoidalClosed.uncurry_natural_left, pathOfJoinCone, MonoidalClosed.uncurry_curry]
    rw [BraidedCategory.braiding_naturality_right_assoc]
    exact (congrArg (fun h => (β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫ h) hpq).trans
      ((congrArg (fun h => (β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫ h ≫ e) simplexCollapse_zero_dim).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun h => h ≫ e) (CartesianMonoidalCategory.braiding_hom_snd _ _))))
  have hr : MonoidalClosed.uncurry (SSet.yonedaEquiv.symm (ihomVertexEquiv Δ[1] H e)) =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u}) Δ[0] ≫ e := by
    rw [SSet.yonedaEquiv_symm_ihomVertexEquiv, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
    have hu : Δ0IsoUnit.hom = CartesianMonoidalCategory.toUnit (Δ[0] : SSet.{u}) :=
      CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    have ht : (Δ[1] : SSet.{u}) ◁ Δ0IsoUnit.hom ≫ (ρ_ (Δ[1] : SSet.{u})).hom =
        CartesianMonoidalCategory.fst (Δ[1] : SSet.{u}) Δ[0] := by
      rw [hu]
      exact CartesianMonoidalCategory.whiskerLeft_toUnit_comp_rightUnitor_hom _ _
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun h => h ≫ e) ht)
  exact MonoidalClosed.uncurry_injective (hl.trans hr.symm)

/-- Reading the original cone point returns the same entire edge through the canonical vertex dictionary. -/
theorem pathOfJoinCone_point {A H : SSet.{u}} (q : A ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (p : (Δ[0] : SSet.{u}) ⟶ A) (e : (Δ[1] : SSet.{u}) ⟶ H)
    (hq : (join.map p).app Δ[0] ≫ q = (joinStdSimplexIso 0 0).hom ≫ e) :
    SSet.yonedaEquiv (p ≫ pathOfJoinCone q) = ihomVertexEquiv Δ[1] H e :=
  (congrArg SSet.yonedaEquiv (pathOfJoinCone_point_name q p e hq)).trans (Equiv.apply_symm_apply _ _)

/-- The actual slice comparison retains the identical entire original edge at each classified cone point. -/
theorem joinToPath_point (H : SSet.{u}) (z : (Δ[0] : SSet.{u}) ⟶ H)
    (p : (Δ[0] : SSet.{u}) ⟶ sliceOver H z) (e : (Δ[1] : SSet.{u}) ⟶ H)
    (hq : (join.map p).app Δ[0] ≫ sliceOver.evaluation H z = (joinStdSimplexIso 0 0).hom ≫ e) :
    SSet.yonedaEquiv ((p ≫ joinToPath H z) ≫ pathSliceOver.fst z) = ihomVertexEquiv Δ[1] H e := by
  have hf : (p ≫ joinToPath H z) ≫ pathSliceOver.fst z = p ≫ pathOfJoinCone (sliceOver.evaluation H z) :=
    (Category.assoc _ _ _).trans (congrArg (fun h => p ≫ h) (joinToPath_fst H z))
  exact (congrArg SSet.yonedaEquiv hf).trans (pathOfJoinCone_point _ p e hq)

end SSet.WalkingAdjunction.ConeCylinder

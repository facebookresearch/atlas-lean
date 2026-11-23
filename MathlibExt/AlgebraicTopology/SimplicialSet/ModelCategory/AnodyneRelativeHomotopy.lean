/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomZero

/-!
# Relative homotopy extension across an anodyne map

Two maps from a simplicial set `Y` to a Kan complex that agree after an
anodyne map `i : X ⟶ Y` are simplicially homotopic.  The homotopy is constant
on `X`: its restriction along `i ⊗ Δ[1]` is the constant cylinder on the
common restriction.

The proof glues the two endpoint maps on `Y ⊗ ∂Δ[1]` to the constant cylinder
on `range i ⊗ Δ[1]`.  The resulting partial cylinder extends because the
pushout-product inclusion is anodyne.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

private noncomputable def endpointFaces {Y K : SSet.{u}} (a b : Y ⟶ K) :
    Fin 2 → ((Δ[0] : SSet.{u}) ⟶ (ihom Y).obj K) :=
  fun j ↦ yonedaEquiv.symm
    ((ihom₀Equiv Y K).symm (if j = 1 then a else b))

private theorem endpointFaces_isCompatible {Y K : SSet.{u}} (a b : Y ⟶ K) :
    boundary.IsCompatible (endpointFaces a b) :=
  trivial

private noncomputable def endpointMap {Y K : SSet.{u}} (a b : Y ⟶ K) :
    Y ⊗ (boundary 1 : SSet.{u}) ⟶ K :=
  uncurry ((endpointFaces_isCompatible a b).desc)

private lemma whiskerLeft_boundary_ι_endpointMap {Y K : SSet.{u}}
    (a b : Y ⟶ K) (j : Fin 2) :
    (Y ◁ boundary.ι j) ≫ endpointMap a b =
      (stdSimplex.rightUnitor Y).hom ≫ (if j = 1 then a else b) := by
  dsimp [endpointMap]
  rw [← MonoidalClosed.uncurry_natural_left, boundary.IsCompatible.ι_desc]
  apply (cancel_epi (stdSimplex.rightUnitor Y).inv).mp
  simp [endpointFaces]

private theorem anodyneExtensions_mono {X Y : SSet.{u}} {i : X ⟶ Y}
    (hi : anodyneExtensions i) : Mono i := by
  have hle : anodyneExtensions.{u} ≤ monomorphisms SSet.{u} := by
    rw [anodyneExtensions_eq_llp_rlp, ← modelCategoryQuillen.llp_rlp_I,
      ← rlp_monomorphisms]
    exact antitone_llp (antitone_rlp modelCategoryQuillen.J_le_monomorphisms)
  exact hle i hi

private theorem range_ι_mem_anodyneExtensions {X Y : SSet.{u}}
    (i : X ⟶ Y) [Mono i] (hi : anodyneExtensions i) :
    anodyneExtensions (Subcomplex.range i).ι := by
  let e : X ≅ (Subcomplex.range i : SSet.{u}) :=
    asIso (Subcomplex.toRange i)
  have hIso : Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
    Arrow.isoMk e (Iso.refl _) (by simp [e])
  exact (anodyneExtensions.arrow_mk_iso_iff hIso).mp hi

namespace anodyneExtensions

/-- Two maps to a Kan complex that agree after an anodyne map are homotopic,
with a homotopy constant on the source of the anodyne map. -/
theorem exists_homotopy_rel {X Y K : SSet.{u}} {i : X ⟶ Y}
    (hi : anodyneExtensions i) [KanComplex K]
    {a b : Y ⟶ K} (hab : i ≫ a = i ≫ b) :
    ∃ H : SSet.Homotopy a b,
      (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst X (Δ[1] : SSet.{u}) ≫ i ≫ a := by
  let _ : Mono i := anodyneExtensions_mono hi
  let A : Y.Subcomplex := Subcomplex.range i
  let T : (Δ[1] : SSet.{u}).Subcomplex := boundary 1
  let e : X ≅ (A : SSet.{u}) := asIso (Subcomplex.toRange i)
  let leftMap : Y ⊗ (T : SSet.{u}) ⟶ K := endpointMap a b
  let rightMap : (A : SSet.{u}) ⊗ Δ[1] ⟶ K :=
    (e.inv ▷ (Δ[1] : SSet.{u})) ≫
      fst X (Δ[1] : SSet.{u}) ≫ i ≫ a
  have hcompat :
      (A.ι ▷ (T : SSet.{u})) ≫ leftMap =
        ((A : SSet.{u}) ◁ T.ι) ≫ rightMap := by
    apply (cancel_epi (e.hom ▷ (T : SSet.{u}))).mp
    apply MonoidalClosed.curry_injective
    apply boundary.hom_ext
    intro j
    rw [← MonoidalClosed.curry_natural_left,
      ← MonoidalClosed.curry_natural_left]
    apply congrArg MonoidalClosed.curry
    dsimp [leftMap, rightMap, T]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    rw [show e.hom ≫ A.ι = i by simp [e, A]]
    rw [whiskerLeft_boundary_ι_endpointMap]
    rw [stdSimplex.rightUnitor_hom_naturality_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
    rw [MonoidalCategory.id_whiskerRight, Category.id_comp]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, boundary.ι_ι]
    rw [CartesianMonoidalCategory.whiskerLeft_fst_assoc]
    fin_cases j
    · change (stdSimplex.rightUnitor X).hom ≫ i ≫ b =
        (stdSimplex.rightUnitor X).hom ≫ i ≫ a
      simpa only [Category.assoc] using
        congrArg (fun f : X ⟶ K ↦ (stdSimplex.rightUnitor X).hom ≫ f) hab.symm
    · rfl
  let unionMap : (A.unionProd T : SSet.{u}) ⟶ K :=
    (Subcomplex.unionProd.isPushout A T).desc leftMap rightMap hcompat
  have hleft : Subcomplex.unionProd.ι₁ A T ≫ unionMap = leftMap := by
    simp [unionMap]
  have hright : Subcomplex.unionProd.ι₂ A T ≫ unionMap = rightMap := by
    simp [unionMap]
  have hA : anodyneExtensions A.ι := by
    simpa [A] using range_ι_mem_anodyneExtensions i hi
  have hUnion : anodyneExtensions (A.unionProd T).ι :=
    anodyneExtensions_unionProd_ι' A T hA
  obtain ⟨Hmap, hHmap⟩ :=
    anodyneExtensions.exists_lift_of_isFibrant unionMap hUnion
  have hboundaryComp (j : Fin 2) :
      (Y ◁ boundary.ι j) ≫ (Y ◁ T.ι) = Y ◁ stdSimplex.δ j := by
    dsimp [T]
    rw [← MonoidalCategory.whiskerLeft_comp, boundary.ι_ι]
  have hzero : SSet.ι₀ ≫ Hmap = a := by
    calc
      SSet.ι₀ ≫ Hmap =
          ((stdSimplex.rightUnitor Y).inv ≫
            (Y ◁ stdSimplex.δ (1 : Fin 2))) ≫ Hmap := by
              rw [stdSimplex.rightUnitor_inv_map_δ_one]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          ((Y ◁ boundary.ι (1 : Fin 2)) ≫ (Y ◁ T.ι)) ≫ Hmap := by
            rw [hboundaryComp]
            simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (1 : Fin 2)) ≫ (Y ◁ T.ι) ≫ Hmap := by
            simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (1 : Fin 2)) ≫
            Subcomplex.unionProd.ι₁ A T ≫ (A.unionProd T).ι ≫ Hmap := by
              rw [Subcomplex.unionProd.ι₁_ι_assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (1 : Fin 2)) ≫
            Subcomplex.unionProd.ι₁ A T ≫ unionMap := by
              rw [hHmap]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (1 : Fin 2)) ≫ leftMap := by
            rw [hleft]
      _ = a := by
        dsimp [leftMap, T]
        rw [whiskerLeft_boundary_ι_endpointMap]
        simp
  have hone : SSet.ι₁ ≫ Hmap = b := by
    calc
      SSet.ι₁ ≫ Hmap =
          ((stdSimplex.rightUnitor Y).inv ≫
            (Y ◁ stdSimplex.δ (0 : Fin 2))) ≫ Hmap := by
              rw [stdSimplex.rightUnitor_inv_map_δ_zero]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          ((Y ◁ boundary.ι (0 : Fin 2)) ≫ (Y ◁ T.ι)) ≫ Hmap := by
            rw [hboundaryComp]
            simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (0 : Fin 2)) ≫ (Y ◁ T.ι) ≫ Hmap := by
            simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (0 : Fin 2)) ≫
            Subcomplex.unionProd.ι₁ A T ≫ (A.unionProd T).ι ≫ Hmap := by
              rw [Subcomplex.unionProd.ι₁_ι_assoc]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (0 : Fin 2)) ≫
            Subcomplex.unionProd.ι₁ A T ≫ unionMap := by
              rw [hHmap]
      _ = (stdSimplex.rightUnitor Y).inv ≫
          (Y ◁ boundary.ι (0 : Fin 2)) ≫ leftMap := by
            rw [hleft]
      _ = b := by
        dsimp [leftMap, T]
        rw [whiskerLeft_boundary_ι_endpointMap]
        simp
  have hrel :
      (i ▷ (Δ[1] : SSet.{u})) ≫ Hmap =
        fst X (Δ[1] : SSet.{u}) ≫ i ≫ a := by
    calc
      (i ▷ (Δ[1] : SSet.{u})) ≫ Hmap =
          (e.hom ▷ (Δ[1] : SSet.{u})) ≫
            (A.ι ▷ (Δ[1] : SSet.{u})) ≫ Hmap := by
              rw [← MonoidalCategory.comp_whiskerRight_assoc]
              simp [e, A]
      _ = (e.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ (A.unionProd T).ι ≫ Hmap := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]
      _ = (e.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ unionMap := by
            rw [hHmap]
      _ = (e.hom ▷ (Δ[1] : SSet.{u})) ≫ rightMap := by
            rw [hright]
      _ = fst X (Δ[1] : SSet.{u}) ≫ i ≫ a := by
        dsimp [rightMap]
        rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
        simp
  let H : SSet.Homotopy a b :=
    { h := Hmap
      h₀ := hzero
      h₁ := hone
      rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }
  exact ⟨H, hrel⟩

end anodyneExtensions

end SSet

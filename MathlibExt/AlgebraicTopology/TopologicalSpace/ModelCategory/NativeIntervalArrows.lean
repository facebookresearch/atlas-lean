/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeInterval
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Original generator arrows for the native interval

The one-horn is identified with its unique zero-dimensional face. General
native realizations retain their whole endpoint isomorphisms to the original
finite realized generators. Each original interval endpoint is then compared
in the actual Arrow category with the corresponding original costar horn.
No model, lifting, cylinder, or localization data is a premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.IntervalArrows

private theorem otherEndpoint_ne (i : Fin 2) : i ≠ i.rev := by
  fin_cases i <;> decide

private theorem otherEndpoint_unique (i j : Fin 2) (h : j ≠ i.rev) : j = i := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- The actual one-horn has precisely the other face, with its chosen degeneracy inverse. -/
@[no_expose]
def hornOneIso (i : Fin 2) : (Δ[0] : SSet.{v}) ≅ (Λ[1, i.rev] : SSet.{v}) where
  hom := SSet.horn.ι i.rev i (otherEndpoint_ne i)
  inv := (SSet.horn.{v} 1 i.rev).ι ≫ SSet.stdSimplex.σ (0 : Fin 1)
  hom_inv_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    apply SSet.horn.hom_ext
    intro j hj
    have hji : j = i := otherEndpoint_unique i j hj
    subst j
    let f := SSet.horn.ι.{v} i.rev i (otherEndpoint_ne i)
    let g := (SSet.horn.{v} 1 i.rev).ι ≫ SSet.stdSimplex.σ (0 : Fin 1)
    have hfg : f ≫ g = 𝟙 (Δ[0] : SSet.{v}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have h : f ≫ (g ≫ f) = f := by
      rw [← Category.assoc, hfg, Category.id_comp]
    change (g ≫ f).app _ (SSet.horn.face i.rev i (otherEndpoint_ne i)) =
      SSet.horn.face i.rev i (otherEndpoint_ne i)
    simpa only [f, SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using
      congrArg SSet.yonedaEquiv h

/-- The chosen horn isomorphism retains the original coface after horn inclusion. -/
@[reassoc]
theorem hornOneIso_hom_ι (i : Fin 2) :
    (hornOneIso.{v} i).hom ≫ (SSet.horn.{v} 1 i.rev).ι = SSet.stdSimplex.δ i :=
  SSet.horn.ι_ι i.rev i (otherEndpoint_ne i)

private theorem hornOneIso_inv_private (i : Fin 2) :
    (hornOneIso.{v} i).inv =
      (SSet.horn.{v} 1 i.rev).ι ≫ SSet.stdSimplex.σ (0 : Fin 1) := rfl

/-- The chosen inverse retains the original horn inclusion and zero codegeneracy. -/
theorem hornOneIso_inv (i : Fin 2) :
    (hornOneIso.{v} i).inv =
      (SSet.horn.{v} 1 i.rev).ι ≫ SSet.stdSimplex.σ (0 : Fin 1) :=
  hornOneIso_inv_private i

/-- The entire coface arrow is isomorphic to the corresponding original one-horn arrow. -/
@[no_expose]
def cofaceHornArrowIso (i : Fin 2) :
    Arrow.mk (SSet.stdSimplex.{v}.δ i) ≅ Arrow.mk (SSet.horn.{v} 1 i.rev).ι :=
  Arrow.isoMk' (SSet.stdSimplex.{v}.δ i) (SSet.horn.{v} 1 i.rev).ι
    (hornOneIso i) (Iso.refl (Δ[1] : SSet.{v})) (by
      rw [Iso.refl_hom, Category.comp_id]
      exact hornOneIso_hom_ι i)

end SSet.IntervalArrows

namespace CGWH.IntervalArrows

private theorem finiteHorn_top (n : ℕ) (i : Fin (n + 2)) :
    CGWH.cgwhToTop.{u, v}.map (CGWH.realizedHornInclusion.{v, u} n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι := by
  change CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
      (CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedHornInclusion.{v, u} n i)) = _
  have h := congrArg
    (fun q => CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map q)
    (CGWH.cgwhToCompactlyGenerated_map_realizedHornInclusion n i)
  exact h.trans
    (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion n i)

private theorem finiteBoundary_top (n : ℕ) :
    CGWH.cgwhToTop.{u, v}.map (CGWH.realizedBoundaryInclusion.{v, u} n) =
      SSet.toTop.map (SSet.boundary.{v} n).ι := by
  change CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
      (CGWH.cgwhToCompactlyGenerated.{u, v}.map
        (CGWH.realizedBoundaryInclusion.{v, u} n)) = _
  have h := congrArg
    (fun q => CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map q)
    (CGWH.cgwhToCompactlyGenerated_map_realizedBoundaryInclusion n)
  exact h.trans
    (CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion n)

set_option backward.isDefEq.respectTransparency false in
/-- The whole native general realized horn arrow retains both original finite endpoints. -/
@[no_expose]
def generalHornArrowIso (n : ℕ) (i : Fin (n + 2)) :
    Arrow.mk (SSet.toCGWH.{u, v}.map (SSet.horn.{v} (n + 1) i).ι) ≅
      Arrow.mk (CGWH.realizedHornInclusion.{v, u} n i) :=
  Arrow.isoMk' _ _ (finiteRealizationIso _) (finiteRealizationIso _) (by
    apply CGWH.cgwhToTop.{u, v}.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    let s : SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet ⟶
        SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet :=
      CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
    let h : SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet ⟶
        SSet.toTop.obj (Δ[n + 1] : SSet.{v}) :=
      CGWH.cgwhToTop.map (CGWH.realizedHornInclusion.{v, u} n i)
    let t : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶
        SSet.toTop.obj (Δ[n + 1] : SSet.{v}) :=
      CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
    change s ≫ h = SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι ≫ t
    rw [show s = 𝟙 _ from finiteRealizationIso_hom_top _,
      show h = SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι from finiteHorn_top n i,
      show t = 𝟙 _ from finiteRealizationIso_hom_top _]
    simp only [Category.id_comp, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
private theorem generalHornArrowIso_square_private (n : ℕ) (i : Fin (n + 2)) :
    (finiteRealizationIso.{u, v} (SSet.horn.{v} (n + 1) i).toSSet).hom ≫
        CGWH.realizedHornInclusion.{v, u} n i =
      SSet.toCGWH.map (SSet.horn.{v} (n + 1) i).ι ≫
        (finiteRealizationIso.{u, v} (Δ[n + 1] : SSet.{v})).hom := by
  apply CGWH.cgwhToTop.{u, v}.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  let s : SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet ⟶
      SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet :=
    CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
  let h : SSet.toTop.obj (SSet.horn.{v} (n + 1) i).toSSet ⟶
      SSet.toTop.obj (Δ[n + 1] : SSet.{v}) :=
    CGWH.cgwhToTop.map (CGWH.realizedHornInclusion.{v, u} n i)
  let t : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶
      SSet.toTop.obj (Δ[n + 1] : SSet.{v}) :=
    CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
  change s ≫ h = SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι ≫ t
  rw [show s = 𝟙 _ from finiteRealizationIso_hom_top _,
    show h = SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι from finiteHorn_top n i,
    show t = 𝟙 _ from finiteRealizationIso_hom_top _]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The original finite/general comparison retains the complete horn commutative square. -/
@[reassoc]
theorem generalHornArrowIso_square (n : ℕ) (i : Fin (n + 2)) :
    (finiteRealizationIso.{u, v} (SSet.horn.{v} (n + 1) i).toSSet).hom ≫
        CGWH.realizedHornInclusion.{v, u} n i =
      SSet.toCGWH.map (SSet.horn.{v} (n + 1) i).ι ≫
        (finiteRealizationIso.{u, v} (Δ[n + 1] : SSet.{v})).hom :=
  generalHornArrowIso_square_private n i

set_option backward.isDefEq.respectTransparency false in
/-- The whole native general realized boundary arrow retains both original finite endpoints. -/
@[no_expose]
def generalBoundaryArrowIso (n : ℕ) :
    Arrow.mk (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} n).ι) ≅
      Arrow.mk (CGWH.realizedBoundaryInclusion.{v, u} n) :=
  Arrow.isoMk' _ _ (finiteRealizationIso _) (finiteRealizationIso _) (by
    apply CGWH.cgwhToTop.{u, v}.map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    let s : SSet.toTop.obj (SSet.boundary.{v} n).toSSet ⟶
        SSet.toTop.obj (SSet.boundary.{v} n).toSSet :=
      CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
    let h : SSet.toTop.obj (SSet.boundary.{v} n).toSSet ⟶
        SSet.toTop.obj (Δ[n] : SSet.{v}) :=
      CGWH.cgwhToTop.map (CGWH.realizedBoundaryInclusion.{v, u} n)
    let t : SSet.toTop.obj (Δ[n] : SSet.{v}) ⟶ SSet.toTop.obj (Δ[n] : SSet.{v}) :=
      CGWH.cgwhToTop.map (finiteRealizationIso.{u, v} _).hom
    change s ≫ h = SSet.toTop.map (SSet.boundary.{v} n).ι ≫ t
    rw [show s = 𝟙 _ from finiteRealizationIso_hom_top _,
      show h = SSet.toTop.map (SSet.boundary.{v} n).ι from finiteBoundary_top n,
      show t = 𝟙 _ from finiteRealizationIso_hom_top _]
    simp only [Category.id_comp, Category.comp_id])

end CGWH.IntervalArrows

namespace PointedCGWH.IntervalCoefficient

set_option backward.isDefEq.respectTransparency false in
private def endpointHornCGWHArrowIso (i : Fin 2) :
    Arrow.mk (zeroSimplexIsoPoint.{u, v}.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ i)) ≅
      Arrow.mk (CGWH.realizedHornInclusion.{v, u} 0 i.rev) :=
  Arrow.isoMk' _ _
    (zeroSimplexIsoPoint.symm ≪≫
      SSet.toCGWH.mapIso (SSet.IntervalArrows.hornOneIso i) ≪≫
        CGWH.finiteRealizationIso _)
    (CGWH.finiteRealizationIso _) (by
      dsimp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
      rw [Category.assoc, Category.assoc]
      rw [CGWH.IntervalArrows.generalHornArrowIso_square]
      rw [← Category.assoc
        (SSet.toCGWH.map (SSet.IntervalArrows.hornOneIso i).hom)
        (SSet.toCGWH.map (SSet.horn.{v} 1 i.rev).ι)]
      rw [← CategoryTheory.Functor.map_comp, SSet.IntervalArrows.hornOneIso_hom_ι]
      rw [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Each original native endpoint is the original costar one-horn up to whole Arrow iso. -/
@[no_expose]
def endpointHornArrowIso (i : Fin 2) :
    Arrow.mk (endpoint.{u, v} i) ≅
      Arrow.mk ((Under.costar CGWH.point.{u, v}).map
        (CGWH.realizedHornInclusion.{v, u} 0 i.rev)) := by
  rw [endpoint_eq]
  exact (Under.costar CGWH.point.{u, v}).mapArrow.mapIso (endpointHornCGWHArrowIso i)

set_option backward.isDefEq.respectTransparency false in
/-- Every property respecting whole Arrow isomorphisms sees the original horn endpoint. -/
theorem endpoint_property_iff (W : MorphismProperty PointedCGWH.{u, v})
    [W.RespectsIso] (i : Fin 2) :
    W (endpoint.{u, v} i) ↔
      W ((Under.costar CGWH.point.{u, v}).map
        (CGWH.realizedHornInclusion.{v, u} 0 i.rev)) :=
  W.arrow_mk_iso_iff (endpointHornArrowIso i)

end PointedCGWH.IntervalCoefficient

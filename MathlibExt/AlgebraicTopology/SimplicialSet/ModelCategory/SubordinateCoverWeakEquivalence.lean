/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ExInfinity
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFibrationHomotopyExtension
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Mesh
import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.RealizationLastVertexRelative
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains
public import Mathlib.Topology.Sets.OpenCover
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Subordinate singular complexes of open covers

For an arbitrary indexed open cover of a topological space, this file proves
that the simplicial inclusion from singular simplices contained in one cover
member to the full singular complex is a realization weak equivalence.

The proof combines strict mesh smallification, finite-stage compactness for
the Ex-infinity tower, connected-component and pointed homotopy-group
calculations, and a relative boundary correction in the Kan target.  The
finite-stage correction keeps the two iterated-unit routes distinct: their
comparison is a simplicial homotopy obtained only after the valid
weak-equivalence prefix, not a false literal endpoint equality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits Opposite Simplicial Topology HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial unitInterval SSet.modelCategoryQuillen

namespace AlgebraicTopology

private theorem stdSimplex_map_mono
    {m n : SimplexCategory} (f : m ⟶ n) [Mono f] :
    Mono (SSet.stdSimplex.map f :
      (SSet.stdSimplex.obj m : SSet.{u}) ⟶ SSet.stdSimplex.obj n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro j
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  apply SSet.stdSimplex.objEquiv.injective
  apply (cancel_mono f).1
  exact SSet.stdSimplex.objEquiv.symm.injective h

private theorem nondegenerateMap_injective_local
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (SSet.N.map f) := by
  intro x y hxy
  apply SSet.N.subcomplex_injective
  apply le_antisymm
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]

private theorem mono_nondegenerateNerve_map_local
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.nondegenerateNerve.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext
    (h := fun i => nondegenerateMap_injective_local f
      (congrArg (fun z => z.obj i) hab))
    (w := by intro i hi; subsingleton)

private theorem mono_sd_map_of_nonsingular_local
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] : Mono (SSet.sd.map f) := by
  have h : SSet.sd.map f ≫ (SSet.sdIsoNondegenerateNerve Y).hom =
      (SSet.sdIsoNondegenerateNerve X).hom ≫
        SSet.nondegenerateNerve.map f := by
    rw [SSet.sdIsoNondegenerateNerve_hom,
      SSet.sdIsoNondegenerateNerve_hom]
    exact SSet.sdToNondegenerateNerve.naturality f
  let _ : Mono (SSet.nondegenerateNerve.map f) :=
    mono_nondegenerateNerve_map_local f
  have : Mono ((SSet.sdIsoNondegenerateNerve X).hom ≫
      SSet.nondegenerateNerve.map f) := inferInstance
  exact mono_of_mono_fac h

private theorem mono_sdIter_map_of_nonsingular_local
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Mono ((SSet.sdIter k).map f) := by
  induction k with
  | zero => change Mono f; infer_instance
  | succ k ih =>
      rw [SSet.sdIter_map_succ]
      let _ : Mono ((SSet.sdIter k).map f) := ih
      exact mono_sd_map_of_nonsingular_local ((SSet.sdIter k).map f)

private noncomputable def geometricSubdivisionAdjunct
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _
    ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b)

private theorem geometricSubdivisionAdjunct_cell
    {X : TopCat.{u}} {n d k : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (cell : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    cell ≫ geometricSubdivisionAdjunct b k =
      sSetTopAdj.homEquiv _ _
        (SSet.toTop.map cell ≫
          (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b) := by
  rw [geometricSubdivisionAdjunct,
    sSetTopAdj.homEquiv_naturality_left]

private theorem geometricSubdivisionAdjunct_naturality_of_mono
    {X : TopCat.{u}} {m n k : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)]
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) :
    (SSet.sdIter k).map (SSet.stdSimplex.{u}.map f) ≫
        geometricSubdivisionAdjunct b k =
      geometricSubdivisionAdjunct
        (SSet.toTop.map (SSet.stdSimplex.{u}.map f) ≫ b) k := by
  unfold geometricSubdivisionAdjunct
  rw [← sSetTopAdj.homEquiv_naturality_left]
  apply congrArg (sSetTopAdj.homEquiv
    ((SSet.sdIter k).obj (Δ[m] : SSet.{u})) X)
  rw [← Category.assoc,
    SSet.toTopSdIterIso_hom_naturality_of_mono]
  rw [Category.assoc]

private theorem sSetTopAdj_homEquiv_symm_apply
    {K : SSet.{u}} {X : TopCat.{u}} {d : ℕ}
    (f : K ⟶ TopCat.toSSet.obj X) (z : K _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((sSetTopAdj.homEquiv K X).symm f)
        (SSet.toTop.map (SSet.yonedaEquiv.symm z)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
      X.toSSetObjEquiv _ (f.app _ z) q := by
  have hAdj := (sSetTopAdj.homEquiv K X).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at hAdj
  have hDown := congrArg (fun r => (r.app _ z).down) hAdj
  change ((sSetTopAdj.unit.app K).app _ z).down ≫
      (sSetTopAdj.homEquiv K X).symm f = (f.app _ z).down at hDown
  rw [sSetTopAdj_unit_app_app_down] at hDown
  have hpoint :
      (SSet.toTopSimplex.inv.app ⦋d⦌) (ULift.up q) =
        (SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q := by
    rfl
  calc
    ((sSetTopAdj.homEquiv K X).symm f)
        (SSet.toTop.map (SSet.yonedaEquiv.symm z)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
      ((sSetTopAdj.homEquiv K X).symm f)
        (SSet.toTop.map (SSet.yonedaEquiv.symm z)
          ((SSet.toTopSimplex.inv.app ⦋d⦌) (ULift.up q))) := by rw [hpoint]
    _ = (((SSet.toTopSimplex.inv.app ⦋d⦌ ≫
          SSet.toTop.map (SSet.yonedaEquiv.symm z)) ≫
        (sSetTopAdj.homEquiv K X).symm f) (ULift.up q)) := by rfl
    _ = (ConcreteCategory.hom
          ((ConcreteCategory.hom (f.app (Opposite.op ⦋d⦌))) z).down)
        (ULift.up q) :=
      ConcreteCategory.congr_hom hDown (ULift.up q)
    _ = X.toSSetObjEquiv _ (f.app _ z) q := by rfl

private theorem exists_subordinateSubdivision
    {X : TopCat.{u}} {n : ℕ} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) :
    ∃ (k : ℕ)
      (q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u})),
      q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
          geometricSubdivisionAdjunct b k := by
  obtain ⟨k, hk⟩ :=
    SSet.exists_sdIter_simplex_range_subset b U hU
  let g := geometricSubdivisionAdjunct b k
  have hg : SSet.Subcomplex.range g ≤
      AlgebraicTopology.subordinateCover (fun i => (U i : Set X)) := by
    intro a y hy
    obtain ⟨z, rfl⟩ := hy
    induction a using Opposite.rec
    rename_i a
    induction a using SimplexCategory.rec
    rename_i d
    let cell : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u}) :=
      SSet.yonedaEquiv.symm z
    obtain ⟨i, hi⟩ := hk cell
    apply (le_iSup (fun i => AlgebraicTopology.subordinateSet
      (X := X) (U i : Set X)) i)
    change Set.range (X.toSSetObjEquiv _ (g.app _ z)) ⊆ (U i : Set X)
    have hcell := geometricSubdivisionAdjunct_cell b cell
    have hy : SSet.yonedaEquiv (cell ≫ g) = g.app _ z := by
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    have htop := congrArg (sSetTopAdj.homEquiv
      (Δ[d] : SSet.{u}) X).symm hcell
    rw [Equiv.symm_apply_apply] at htop
    rw [← hy]
    intro y hyRange
    obtain ⟨z₀, rfl⟩ := hyRange
    apply hi
    let zTop : SSet.toTop.obj (Δ[d] : SSet.{u}) :=
      (SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀
    refine ⟨zTop, ?_⟩
    have heval := sSetTopAdj_homEquiv_symm_apply (cell ≫ g)
      (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) z₀
    have hinput :
        SSet.toTop.map (SSet.yonedaEquiv.symm
          (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀) = zTop := by
      simp [zTop]
    have hcomponent :
        ((cell ≫ g).app (Opposite.op ⦋d⦌))
            (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) =
          SSet.yonedaEquiv (cell ≫ g) := by
      rw [← SSet.yonedaEquiv_comp]
      simp
    have heval' :
        ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm (cell ≫ g)) zTop =
          X.toSSetObjEquiv _ (SSet.yonedaEquiv (cell ≫ g)) z₀ := by
      calc
        _ = ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm (cell ≫ g))
            (SSet.toTop.map (SSet.yonedaEquiv.symm
              (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
                ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀)) := by
          rw [hinput]
        _ = X.toSSetObjEquiv _
            (((cell ≫ g).app (Opposite.op ⦋d⦌))
              (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u})))) z₀ := heval
        _ = _ := congrArg
          (fun s => X.toSSetObjEquiv (Opposite.op ⦋d⦌) s z₀) hcomponent
    exact (ConcreteCategory.congr_hom htop zTop).symm.trans heval'
  let q := SSet.Subcomplex.lift g hg
  exact ⟨k, q, SSet.Subcomplex.lift_ι g hg⟩

/-!
Client-visible reconstruction of the private finite stages underlying
`SSet.exInfinity`.
-/

private noncomputable abbrev clientExIter : ℕ → SSet.{u} ⥤ SSet.{u} := fun n =>
  Nat.rec (Functor.id _) (fun _ F => F ⋙ SSet.ex) n

private noncomputable abbrev clientExTower (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  Functor.ofSequence
    (fun n => SSet.exUnit.app ((clientExIter n).obj X))

private theorem clientExTower_map_succ (X : SSet.{u}) (n : ℕ) :
    (clientExTower X).map (homOfLE (n.le_add_right 1)) =
      SSet.exUnit.app ((clientExIter n).obj X) := by
  unfold clientExTower
  exact Functor.ofSequence_map_homOfLE_succ _ n

private theorem clientExIter_succ_map {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (clientExIter (n + 1)).map f =
      SSet.ex.map ((clientExIter n).map f) := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev clientExTowerFunctor :
    SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) where
  obj X := clientExTower X
  map {X Y} f := NatTrans.ofSequence
    (fun n => (clientExIter n).map f)
    (fun n => by
      rw [clientExTower_map_succ, clientExTower_map_succ,
        clientExIter_succ_map]
      simpa only [Functor.id_map] using
        (SSet.exUnit.naturality ((clientExIter n).map f)).symm)
  map_id X := by
    apply NatTrans.ext
    funext n
    change (clientExIter n).map (𝟙 X) = 𝟙 ((clientExIter n).obj X)
    exact (clientExIter n).map_id X
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext n
    change (clientExIter n).map (f ≫ g) =
      (clientExIter n).map f ≫ (clientExIter n).map g
    exact (clientExIter n).map_comp f g

private theorem clientExInfinity_eq_towerFunctor :
    SSet.exInfinity.{u} = clientExTowerFunctor.{u} ⋙ Limits.colim := by
  unfold SSet.exInfinity clientExTowerFunctor clientExTower clientExIter
  rfl

private noncomputable abbrev clientExSmallTower (X : SSet.{u}) :
    CategoryTheory.AsSmall.{u} ℕ ⥤ SSet.{u} :=
  CategoryTheory.AsSmall.down ⋙ clientExTower X

private theorem clientExSmallDown_final :
    (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).IsRightAdjoint :=
    (CategoryTheory.AsSmall.equiv.{0, 0, u}
      (C := ℕ)).isRightAdjoint_inverse
  infer_instance

private noncomputable def clientExTowerColimitIso (X : SSet.{u}) :
    colimit (clientExSmallTower X) ≅ colimit (clientExTower X) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := clientExSmallDown_final
  exact Functor.Final.colimitIso CategoryTheory.AsSmall.down (clientExTower X)

set_option backward.isDefEq.respectTransparency false in
private theorem clientExTowerColimitIso_hom_ι (X : SSet.{u})
    (j : CategoryTheory.AsSmall.{u} ℕ) :
    colimit.ι (clientExSmallTower X) j ≫ (clientExTowerColimitIso X).hom =
      colimit.ι (clientExTower X) (CategoryTheory.AsSmall.down.obj j) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := clientExSmallDown_final
  unfold clientExTowerColimitIso
  exact Functor.Final.ι_colimitIso_hom
    CategoryTheory.AsSmall.down (clientExTower X) j

private theorem clientExists_exTower_factor
    (X K : SSet.{u}) [K.Finite]
    (f : K ⟶ SSet.exInfinity.obj X) :
    ∃ (j : CategoryTheory.AsSmall.{u} ℕ)
      (p : K ⟶ (clientExTower X).obj
        (CategoryTheory.AsSmall.down.obj j)),
        p ≫ colimit.ι (clientExTower X)
          (CategoryTheory.AsSmall.down.obj j) = f := by
  change K ⟶ colimit (clientExTower X) at f
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := clientExSmallDown_final
  let e := clientExTowerColimitIso X
  obtain ⟨j, p, hp⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit
      (X := K) (colimit.isColimit (clientExSmallTower X)) (f ≫ e.inv)
  refine ⟨j, p, ?_⟩
  have hp' : p ≫ colimit.ι (clientExSmallTower X) j = f ≫ e.inv := hp
  calc
    p ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj j) =
        p ≫ colimit.ι (clientExSmallTower X) j ≫ e.hom := by
      rw [clientExTowerColimitIso_hom_ι]
    _ = (p ≫ colimit.ι (clientExSmallTower X) j) ≫ e.hom := by
      rw [Category.assoc]
    _ = (f ≫ e.inv) ≫ e.hom := by rw [hp']
    _ = f := by simp

private theorem clientExists_exTower_later_eq
    (X K : SSet.{u}) [K.Finite]
    {i j : CategoryTheory.AsSmall.{u} ℕ}
    (f : K ⟶ (clientExTower X).obj
      (CategoryTheory.AsSmall.down.obj i))
    (g : K ⟶ (clientExTower X).obj
      (CategoryTheory.AsSmall.down.obj j))
    (h : f ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj i) =
      g ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj j)) :
    ∃ (k : CategoryTheory.AsSmall.{u} ℕ) (a : i ⟶ k) (b : j ⟶ k),
      f ≫ (clientExTower X).map (CategoryTheory.AsSmall.down.map a) =
        g ≫ (clientExTower X).map (CategoryTheory.AsSmall.down.map b) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := clientExSmallDown_final
  let e := clientExTowerColimitIso X
  have hsmall :
      f ≫ colimit.ι (clientExSmallTower X) i =
        g ≫ colimit.ι (clientExSmallTower X) j := by
    apply (cancel_mono e.hom).mp
    calc
      (f ≫ colimit.ι (clientExSmallTower X) i) ≫ e.hom =
          f ≫ colimit.ι (clientExTower X)
            (CategoryTheory.AsSmall.down.obj i) := by
        rw [Category.assoc, clientExTowerColimitIso_hom_ι]
      _ = g ≫ colimit.ι (clientExTower X)
          (CategoryTheory.AsSmall.down.obj j) := h
      _ = (g ≫ colimit.ι (clientExSmallTower X) j) ≫ e.hom := by
        rw [Category.assoc, clientExTowerColimitIso_hom_ι]
  obtain ⟨k, a, b, hab⟩ :=
    IsFinitelyPresentable.exists_eq_of_isColimit
      (X := K) (colimit.isColimit (clientExSmallTower X)) f g hsmall
  exact ⟨k, a, b, hab⟩

private theorem clientExIter_obj_ex (k : ℕ) (Z : SSet.{u}) :
    (clientExIter k).obj (SSet.ex.obj Z) =
      (clientExIter (k + 1)).obj Z := by
  induction k generalizing Z with
  | zero => rfl
  | succ k ih =>
      change SSet.ex.obj ((clientExIter k).obj (SSet.ex.obj Z)) =
        SSet.ex.obj ((clientExIter (k + 1)).obj Z)
      rw [ih]

private noncomputable def sdIterExIterHomEquiv (k : ℕ)
    (X Z : SSet.{u}) :
    ((SSet.sdIter k).obj X ⟶ Z) ≃
      (X ⟶ (clientExIter k).obj Z) :=
  match k with
  | 0 => Equiv.refl _
  | k + 1 => by
      let e := (SSet.sdExAdjunction.homEquiv
        ((SSet.sdIter k).obj X) Z).trans
          (sdIterExIterHomEquiv k X (SSet.ex.obj Z))
      simpa only [SSet.sdIter_obj_succ, clientExIter_obj_ex] using e

private noncomputable def adjExIter : ℕ → SSet.{u} ⥤ SSet.{u} := fun k =>
  Nat.rec (𝟭 _) (fun _ F => SSet.ex ⋙ F) k

private noncomputable def sdIterAdjunction (k : ℕ) :
    SSet.sdIter k ⊣ adjExIter k := by
  induction k with
  | zero => exact Adjunction.id
  | succ k ih =>
      simpa only [SSet.sdIter_succ, adjExIter] using
        ih.comp SSet.sdExAdjunction

private noncomputable def exCommuteClient (k : ℕ) :
    SSet.ex ⋙ clientExIter k ≅ clientExIter k ⋙ SSet.ex := by
  induction k with
  | zero => exact Functor.rightUnitor SSet.ex ≪≫
      (Functor.leftUnitor SSet.ex).symm
  | succ k ih =>
      simpa only [clientExIter] using
        (Functor.associator SSet.ex (clientExIter k) SSet.ex).symm ≪≫
          Functor.isoWhiskerRight ih SSet.ex

private noncomputable def adjExIterIsoClient (k : ℕ) :
    adjExIter k ≅ clientExIter k := by
  induction k with
  | zero => exact Iso.refl _
  | succ k ih =>
      simpa only [adjExIter, clientExIter] using
        Functor.isoWhiskerLeft SSet.ex ih ≪≫ exCommuteClient k

private theorem clientExTowerFunctor_map_app
    {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    (clientExTowerFunctor.map f).app k = (clientExIter k).map f := by
  rfl

private noncomputable def adjExIterIsoTowerObj
    (k : ℕ) (Z : SSet.{u}) :
    (adjExIter k).obj Z ≅ (clientExTower Z).obj k := by
  change (adjExIter k).obj Z ≅ (clientExIter k).obj Z
  exact (adjExIterIsoClient k).app Z

private noncomputable def sdIterClientHomEquiv (k : ℕ)
    (X Z : SSet.{u}) :
    ((SSet.sdIter k).obj X ⟶ Z) ≃
      (X ⟶ (clientExTower Z).obj k) :=
  (sdIterAdjunction k).homEquiv X Z |>.trans
    ((Iso.refl X).homCongr (adjExIterIsoTowerObj k Z))

private theorem sdIterClientHomEquiv_naturality_left
    {X Y Z : SSet.{u}} (k : ℕ) (f : X ⟶ Y)
    (g : (SSet.sdIter k).obj Y ⟶ Z) :
    sdIterClientHomEquiv k X Z ((SSet.sdIter k).map f ≫ g) =
      f ≫ sdIterClientHomEquiv k Y Z g := by
  simp only [sdIterClientHomEquiv, Equiv.trans_apply,
    (sdIterAdjunction k).homEquiv_naturality_left,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Category.assoc]

private theorem sdIterClientHomEquiv_naturality_right
    {X Y Z : SSet.{u}} (k : ℕ)
    (f : (SSet.sdIter k).obj X ⟶ Y) (g : Y ⟶ Z) :
    sdIterClientHomEquiv k X Z (f ≫ g) =
      sdIterClientHomEquiv k X Y f ≫
        (clientExTowerFunctor.map g).app k := by
  simp only [sdIterClientHomEquiv, Equiv.trans_apply]
  rw [(sdIterAdjunction k).homEquiv_naturality_right]
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Category.assoc]
  let m := (sdIterAdjunction k).homEquiv X Y f
  have hnat := (adjExIterIsoClient k).hom.naturality g
  have hnat' :
      (adjExIter k).map g ≫ (adjExIterIsoTowerObj k Z).hom =
        (adjExIterIsoTowerObj k Y).hom ≫
          (clientExTowerFunctor.map g).app k := by
    change (adjExIter k).map g ≫ ((adjExIterIsoClient k).app Z).hom =
      ((adjExIterIsoClient k).app Y).hom ≫ (clientExIter k).map g
    exact hnat
  simpa only [m, Category.assoc] using
    congrArg (fun h => m ≫ h) hnat'

private noncomputable def clientExTowerZeroHom (X : SSet.{u}) :
    X ⟶ (clientExTower X).obj 0 :=
  eqToHom (by rfl)

private theorem clientExTowerZeroHom_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ clientExTowerZeroHom Y =
      clientExTowerZeroHom X ≫ (clientExIter 0).map f := by
  rfl

private noncomputable def clientExTowerZeroMapRaw
    (X : SSet.{u}) (k : ℕ) :
    X ⟶ (clientExTower X).obj k :=
  clientExTowerZeroHom X ≫
    (clientExTower X).map (homOfLE (Nat.zero_le k))

private noncomputable def towerLastVertex
    (X : SSet.{u}) (k : ℕ) :
    (SSet.sdIter k).obj X ⟶ X :=
  (sdIterClientHomEquiv k X X).symm (clientExTowerZeroMapRaw X k)

private theorem towerLastVertex_mate (X : SSet.{u}) (k : ℕ) :
    sdIterClientHomEquiv k X X (towerLastVertex X k) =
      clientExTowerZeroMapRaw X k := by
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem clientExTowerZeroMapRaw_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    clientExTowerZeroMapRaw X k ≫
        (clientExTowerFunctor.map f).app k =
      f ≫ clientExTowerZeroMapRaw Y k := by
  have h := (clientExTowerFunctor.map f).naturality
    (homOfLE (Nat.zero_le k) : 0 ⟶ k)
  unfold clientExTowerZeroMapRaw
  rw [Category.assoc, h, ← Category.assoc]
  rw [clientExTowerFunctor_map_app,
    ← clientExTowerZeroHom_naturality]
  rw [Category.assoc]

private theorem towerLastVertex_promote
    {X Z : SSet.{u}} (f : X ⟶ Z) (k : ℕ) :
    sdIterClientHomEquiv k X Z (towerLastVertex X k ≫ f) =
      f ≫ clientExTowerZeroMapRaw Z k := by
  rw [sdIterClientHomEquiv_naturality_right,
    towerLastVertex_mate]
  exact clientExTowerZeroMapRaw_naturality f k

private theorem towerLastVertex_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    (SSet.sdIter k).map f ≫ towerLastVertex Y k =
      towerLastVertex X k ≫ f := by
  apply (sdIterClientHomEquiv k X Y).injective
  rw [sdIterClientHomEquiv_naturality_left,
    sdIterClientHomEquiv_naturality_right,
    towerLastVertex_mate, towerLastVertex_mate]
  exact (clientExTowerZeroMapRaw_naturality f k).symm

/-!
The recursive last vertex from the reviewed provider and the inverse mate
of the literal tower transition are not equal.  We compare their realizations
by a second face-preserving barycentric homotopy.
-/

private noncomputable def recursiveLastEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  SSet.toTop.map (SSet.sdIterLastVertex (Δ[n] : SSet.{u}) k)

private noncomputable def towerLastEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  SSet.toTop.map (towerLastVertex (Δ[n] : SSet.{u}) k)

private noncomputable def recursiveTowerBridgeHomotopy (n k : ℕ) :
    TopCat.Homotopy
      (SSet.toTop.map (SSet.sdIterLastVertex (Δ[n] : SSet.{u}) k))
      (towerLastEndpoint.{u} n k) := by
  let φ := (⦋n⦌.toTopHomeo.{u} :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ
      Convexity.StdSimplex ℝ (Fin (n + 1)))
  let p : C(SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (⟨φ, φ.continuous⟩ : C(_, _)).comp
      (recursiveLastEndpoint n k).hom
  let q : C(SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (⟨φ, φ.continuous⟩ : C(_, _)).comp
      (towerLastEndpoint n k).hom
  exact
    { toFun := fun z => φ.symm
        (Convexity.convexCombPair (R := ℝ)
          (unitInterval.symm z.1 : ℝ)
          (1 - (unitInterval.symm z.1 : ℝ))
          (unitInterval.symm z.1).property.1
          (by simpa using (unitInterval.symm z.1).property.2)
          (by ring) (p z.2) (q z.2))
      continuous_toFun := by
        apply φ.symm.continuous.comp
        rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
          (Fin (n + 1))).continuous_iff]
        unfold Function.comp
        refine continuous_pi (fun i => ?_)
        have hp : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (p z.2).weights i) :=
          (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
            (p.continuous.comp continuous_snd)
        have hq : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (q z.2).weights i) :=
          (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
            (q.continuous.comp continuous_snd)
        have h1 : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (unitInterval.symm z.1 : ℝ)) :=
          continuous_subtype_val.comp
            (unitInterval.continuous_symm.comp continuous_fst)
        have h2 : Continuous (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            1 - (unitInterval.symm z.1 : ℝ)) :=
          continuous_const.sub h1
        have hEq : (fun z : unitInterval ×
            SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =>
            (Convexity.convexCombPair (R := ℝ)
              (unitInterval.symm z.1 : ℝ)
              (1 - (unitInterval.symm z.1 : ℝ))
              (unitInterval.symm z.1).property.1
              (by simpa using (unitInterval.symm z.1).property.2)
              (by ring) (p z.2) (q z.2)).weights i) =
          (fun z => (unitInterval.symm z.1 : ℝ) * (p z.2).weights i +
            (1 - (unitInterval.symm z.1 : ℝ)) * (q z.2).weights i) := by
          funext z
          simp [Convexity.StdSimplex.weights_convexCombPair, smul_eq_mul]
        rw [hEq]
        exact (h1.mul hp).add (h2.mul hq)
      map_zero_left := by
        intro x
        simp [p, φ, recursiveLastEndpoint]
      map_one_left := by
        intro x
        simp [q, φ] }

private theorem recursiveTowerBridgeHomotopy_toTopHomeo_apply
    (n k : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    (⦋n⦌.toTopHomeo.{u})
        (recursiveTowerBridgeHomotopy n k (t, x)) =
      Convexity.convexCombPair (R := ℝ)
        (unitInterval.symm t : ℝ)
        (1 - (unitInterval.symm t : ℝ))
        (unitInterval.symm t).property.1
        (by simpa using (unitInterval.symm t).property.2)
        (by ring)
        ((⦋n⦌.toTopHomeo.{u}) (recursiveLastEndpoint n k x))
        ((⦋n⦌.toTopHomeo.{u}) (towerLastEndpoint n k x)) := by
  change (⦋n⦌.toTopHomeo.{u})
      ((⦋n⦌.toTopHomeo.{u}).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem recursiveLastEndpoint_naturality
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (k : ℕ) :
    SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ≫
        recursiveLastEndpoint.{u} n k =
      recursiveLastEndpoint.{u} m k ≫
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) := by
  unfold recursiveLastEndpoint
  rw [← SSet.toTop.map_comp, SSet.sdIterLastVertex_naturality,
    SSet.toTop.map_comp]

private theorem towerLastEndpoint_naturality
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (k : ℕ) :
    SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ≫
        towerLastEndpoint.{u} n k =
      towerLastEndpoint.{u} m k ≫
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) := by
  unfold towerLastEndpoint
  rw [← SSet.toTop.map_comp, towerLastVertex_naturality,
    SSet.toTop.map_comp]

private theorem recursiveTowerBridgeHomotopy_naturality
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (k : ℕ)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[m] : SSet.{u}))) :
    recursiveTowerBridgeHomotopy n k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) x) =
      SSet.toTop.map (SSet.stdSimplex.{u}.map f)
        (recursiveTowerBridgeHomotopy m k (t, x)) := by
  have hRec := ConcreteCategory.congr_hom
    (recursiveLastEndpoint_naturality f k) x
  have hTower := ConcreteCategory.congr_hom
    (towerLastEndpoint_naturality f k) x
  have hRecBary := congrArg (⦋n⦌.toTopHomeo.{u}) hRec
  have hTowerBary := congrArg (⦋n⦌.toTopHomeo.{u}) hTower
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hRecBary hTowerBary
  rw [SimplexCategory.toTopHomeo_naturality_apply] at hRecBary hTowerBary
  apply (⦋n⦌.toTopHomeo.{u}).injective
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [recursiveTowerBridgeHomotopy_toTopHomeo_apply,
    recursiveTowerBridgeHomotopy_toTopHomeo_apply]
  rw [hRecBary, hTowerBary]
  exact ((Convexity.StdSimplex.isAffineMap_map ℝ f).map_convexCombPair
    (unitInterval.symm t).property.1
    (by simpa using (unitInterval.symm t).property.2)
    (by ring)
    ((⦋m⦌.toTopHomeo.{u}) (recursiveLastEndpoint m k x))
    ((⦋m⦌.toTopHomeo.{u}) (towerLastEndpoint m k x))).symm

private theorem recursiveTowerBridgeHomotopy_face
    (n k : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    recursiveTowerBridgeHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x) =
      SSet.toTop.map (SSet.stdSimplex.δ i)
        (recursiveTowerBridgeHomotopy n k (t, x)) :=
  recursiveTowerBridgeHomotopy_naturality
    (SimplexCategory.δ i) k t x

private theorem recursiveTowerBridgeHomotopy_face_postcomp_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    b (recursiveTowerBridgeHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x)) = y := by
  rw [recursiveTowerBridgeHomotopy_face]
  exact ConcreteCategory.congr_hom hb
    (recursiveTowerBridgeHomotopy n k (t, x))

private theorem reviewedHomotopy_toTopHomeo_apply
    (n k : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    (⦋n⦌.toTopHomeo.{u})
        (SSet.toTopSdIterLastVertexHomotopy n k (t, x)) =
      Convexity.convexCombPair (R := ℝ)
        (unitInterval.symm t : ℝ)
        (1 - (unitInterval.symm t : ℝ))
        (unitInterval.symm t).property.1
        (by simpa using (unitInterval.symm t).property.2)
        (by ring)
        ((⦋n⦌.toTopHomeo.{u})
          ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom x))
        ((⦋n⦌.toTopHomeo.{u}) (recursiveLastEndpoint n k x)) := by
  change (⦋n⦌.toTopHomeo.{u})
      ((⦋n⦌.toTopHomeo.{u}).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem reviewedHomotopy_naturality_of_mono
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)] (k : ℕ)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[m] : SSet.{u}))) :
    SSet.toTopSdIterLastVertexHomotopy n k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) x) =
      SSet.toTop.map (SSet.stdSimplex.{u}.map f)
        (SSet.toTopSdIterLastVertexHomotopy m k (t, x)) := by
  have hGeom := ConcreteCategory.congr_hom
    (SSet.toTopSdIterIso_hom_naturality_of_mono
      (SSet.stdSimplex.{u}.map f) k) x
  have hLast := ConcreteCategory.congr_hom
    (recursiveLastEndpoint_naturality f k) x
  have hGeomBary := congrArg (⦋n⦌.toTopHomeo.{u}) hGeom
  have hLastBary := congrArg (⦋n⦌.toTopHomeo.{u}) hLast
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hGeomBary hLastBary
  rw [SimplexCategory.toTopHomeo_naturality_apply] at hGeomBary hLastBary
  apply (⦋n⦌.toTopHomeo.{u}).injective
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [reviewedHomotopy_toTopHomeo_apply,
    reviewedHomotopy_toTopHomeo_apply]
  rw [hGeomBary, hLastBary]
  exact ((Convexity.StdSimplex.isAffineMap_map ℝ f).map_convexCombPair
    (unitInterval.symm t).property.1
    (by simpa using (unitInterval.symm t).property.2)
    (by ring)
    ((⦋m⦌.toTopHomeo.{u})
      ((SSet.toTopSdIterIso (Δ[m] : SSet.{u}) k).hom x))
    ((⦋m⦌.toTopHomeo.{u}) (recursiveLastEndpoint m k x))).symm

private theorem reviewedHomotopy_face_postcomp_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    b (SSet.toTopSdIterLastVertexHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x)) = y := by
  rw [SSet.toTopSdIterLastVertexHomotopy_face]
  exact ConcreteCategory.congr_hom hb
    (SSet.toTopSdIterLastVertexHomotopy n k (t, x))

private noncomputable def geometricTowerHomotopy (n k : ℕ) :
    TopCat.Homotopy
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom
      (towerLastEndpoint.{u} n k) := by
  exact (SSet.toTopSdIterLastVertexHomotopy n k).trans
    (recursiveTowerBridgeHomotopy n k)

private theorem geometricTowerHomotopy_naturality_of_mono
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)] (k : ℕ)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[m] : SSet.{u}))) :
    geometricTowerHomotopy n k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) x) =
      SSet.toTop.map (SSet.stdSimplex.{u}.map f)
        (geometricTowerHomotopy m k (t, x)) := by
  simp only [geometricTowerHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact reviewedHomotopy_naturality_of_mono f k _ x
  · exact recursiveTowerBridgeHomotopy_naturality f k _ x

private theorem geometricTowerHomotopy_h_naturality_of_mono
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)] (k : ℕ) :
    (SSet.toTop.map
        ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ▷ TopCat.I) ≫
        (geometricTowerHomotopy n k).h =
      (geometricTowerHomotopy m k).h ≫
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) := by
  ext p
  exact geometricTowerHomotopy_naturality_of_mono f k
    (TopCat.I.homeomorph p.2) p.1

private noncomputable def geometricTowerAdjunctHomotopy
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    SSet.Homotopy
      (geometricSubdivisionAdjunct b k)
      (towerLastVertex (Δ[n] : SSet.{u}) k ≫
        sSetTopAdj.homEquiv _ _ b) := by
  let hTop : TopCat.Homotopy
      ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b)
      (towerLastEndpoint n k ≫ b) :=
    TopCat.Homotopy.comp (TopCat.Homotopy.refl b)
      (geometricTowerHomotopy n k)
  let hSing := TopCat.Homotopy.toSSet hTop
  refine
    { h := ((sSetTopAdj.unit.app
          ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h
      h₀ := ?_
      h₁ := ?_
      rel := ?_ }
  · calc
      SSet.ι₀ ≫
          ((sSetTopAdj.unit.app
              ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h =
        sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ≫
          TopCat.toSSet.map
            ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b) := by
        simp [hSing]
      _ = geometricSubdivisionAdjunct b k := by
        unfold geometricSubdivisionAdjunct
        rw [Adjunction.homEquiv_unit]
  · calc
      SSet.ι₁ ≫
          ((sSetTopAdj.unit.app
              ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) ▷
            (Δ[1] : SSet.{u})) ≫ hSing.h =
        sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ≫
          TopCat.toSSet.map (towerLastEndpoint n k ≫ b) := by
        simp [hSing]
      _ = sSetTopAdj.homEquiv _ _ (towerLastEndpoint n k ≫ b) := by
        rw [Adjunction.homEquiv_unit]
      _ = towerLastVertex (Δ[n] : SSet.{u}) k ≫
          sSetTopAdj.homEquiv _ _ b := by
        unfold towerLastEndpoint
        rw [sSetTopAdj.homEquiv_naturality_left]
  · ext _ ⟨⟨_, h⟩, _⟩
    cases h

private theorem geometricTowerAdjunctHomotopy_naturality_of_mono
    {X : TopCat.{u}} {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    [Mono (SSet.stdSimplex.{u}.map f)]
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f) ▷
        (Δ[1] : SSet.{u})) ≫
        (geometricTowerAdjunctHomotopy b k).h =
      (geometricTowerAdjunctHomotopy
        (SSet.toTop.map (SSet.stdSimplex.{u}.map f) ≫ b) k).h := by
  have hTop :
      (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) ▷ TopCat.I) ≫
          (TopCat.Homotopy.comp (TopCat.Homotopy.refl b)
            (geometricTowerHomotopy n k)).h =
        (TopCat.Homotopy.comp
          (TopCat.Homotopy.refl
            (SSet.toTop.map (SSet.stdSimplex.{u}.map f) ≫ b))
          (geometricTowerHomotopy m k)).h := by
    ext p
    exact congrArg b (geometricTowerHomotopy_naturality_of_mono f k
      (TopCat.I.homeomorph p.2) p.1)
  dsimp [geometricTowerAdjunctHomotopy]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  have hunit :
      (SSet.sdIter k).map (SSet.stdSimplex.{u}.map f) ≫
          sSetTopAdj.unit.app ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) =
        sSetTopAdj.unit.app ((SSet.sdIter k).obj (Δ[m] : SSet.{u})) ≫
          (SSet.toTop ⋙ TopCat.toSSet).map
            ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f)) := by
    simpa only [Functor.id_map] using
      sSetTopAdj.unit.naturality
        ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f))
  rw [hunit, MonoidalCategory.comp_whiskerRight_assoc]
  congr 1
  dsimp [TopCat.Homotopy.toSSet]
  rw [← MonoidalCategory.whisker_exchange_assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc,
    ← TopCat.toSSet.map_comp, hTop]

private theorem geometricTowerHomotopy_face_postcomp_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    b (geometricTowerHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x)) = y := by
  rw [geometricTowerHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · exact reviewedHomotopy_face_postcomp_constant n k i b y hb _ x
  · exact recursiveTowerBridgeHomotopy_face_postcomp_constant
      n k i b y hb _ x

private noncomputable def sdIterCylinderComparison
    (K : SSet.{u}) (k : ℕ) :
    (SSet.sdIter k).obj (K ⊗ (Δ[1] : SSet.{u})) ⟶
      (SSet.sdIter k).obj K ⊗ (Δ[1] : SSet.{u}) :=
  lift ((SSet.sdIter k).map (fst K (Δ[1] : SSet.{u})))
    ((SSet.sdIter k).map (snd K (Δ[1] : SSet.{u})) ≫
      towerLastVertex (Δ[1] : SSet.{u}) k)

private theorem sdIterCylinderComparison_zero
    (K : SSet.{u}) (k : ℕ) :
    (SSet.sdIter k).map (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫
        sdIterCylinderComparison K k =
      (SSet.ι₀ : (SSet.sdIter k).obj K ⟶
        (SSet.sdIter k).obj K ⊗ (Δ[1] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [sdIterCylinderComparison, ← (SSet.sdIter k).map_comp]
  · simp only [sdIterCylinderComparison, Category.assoc, lift_snd]
    rw [← Category.assoc, ← (SSet.sdIter k).map_comp]
    rw [towerLastVertex_naturality]
    ext a x
    rfl

private theorem sdIterCylinderComparison_one
    (K : SSet.{u}) (k : ℕ) :
    (SSet.sdIter k).map (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫
        sdIterCylinderComparison K k =
      (SSet.ι₁ : (SSet.sdIter k).obj K ⟶
        (SSet.sdIter k).obj K ⊗ (Δ[1] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [sdIterCylinderComparison, ← (SSet.sdIter k).map_comp]
  · simp only [sdIterCylinderComparison, Category.assoc, lift_snd]
    rw [← Category.assoc, ← (SSet.sdIter k).map_comp]
    rw [towerLastVertex_naturality]
    ext a x
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sdIterMateHomotopy
    {K Z : SSet.{u}} {k : ℕ}
    {r s : (SSet.sdIter k).obj K ⟶ Z}
    (H : SSet.Homotopy r s) :
    SSet.Homotopy
      (sdIterClientHomEquiv k K Z r)
      (sdIterClientHomEquiv k K Z s) where
  h := sdIterClientHomEquiv k (K ⊗ (Δ[1] : SSet.{u})) Z
    (sdIterCylinderComparison K k ≫ H.h)
  h₀ := by
    rw [← sdIterClientHomEquiv_naturality_left]
    apply congrArg (sdIterClientHomEquiv k K Z)
    rw [← Category.assoc, sdIterCylinderComparison_zero, H.h₀]
  h₁ := by
    rw [← sdIterClientHomEquiv_naturality_left]
    apply congrArg (sdIterClientHomEquiv k K Z)
    rw [← Category.assoc, sdIterCylinderComparison_one, H.h₁]
  rel := by
    ext _ ⟨⟨_, h⟩, _⟩
    cases h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def geometricTowerStageHomotopy
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    SSet.Homotopy
      (sdIterClientHomEquiv k (Δ[n] : SSet.{u})
        (TopCat.toSSet.obj X) (geometricSubdivisionAdjunct b k))
      (sSetTopAdj.homEquiv _ _ b ≫
        clientExTowerZeroMapRaw (TopCat.toSSet.obj X) k) := by
  let H := sdIterMateHomotopy (geometricTowerAdjunctHomotopy b k)
  refine
    { h := H.h
      h₀ := H.h₀
      h₁ := ?_
      rel := H.rel }
  rw [H.h₁]
  exact towerLastVertex_promote (sSetTopAdj.homEquiv _ _ b) k

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallificationImageStageHomotopy
    {X : TopCat.{u}} {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    {n k : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (hq : q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      geometricSubdivisionAdjunct b k) :
    SSet.Homotopy
      (sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _ q ≫
        (clientExTowerFunctor.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι).app k)
      (sSetTopAdj.homEquiv _ _ b ≫
        clientExTowerZeroMapRaw (TopCat.toSSet.obj X) k) := by
  let H := geometricTowerStageHomotopy b k
  have hsource :
      sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _ q ≫
          (clientExTowerFunctor.map
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι).app k =
        sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _
          (geometricSubdivisionAdjunct b k) := by
    rw [← sdIterClientHomEquiv_naturality_right, hq]
  refine
    { h := H.h
      h₀ := ?_
      h₁ := H.h₁
      rel := H.rel }
  rw [H.h₀]
  exact hsource.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homotopyPostcomp
    {A B C : SSet.{u}} {f g : A ⟶ B}
  (H : SSet.Homotopy f g) (p : B ⟶ C) :
    SSet.Homotopy (f ≫ p) (g ≫ p) where
  h := H.h ≫ p
  h₀ := by
    change SSet.ι₀ ≫ (H.h ≫ p) = f ≫ p
    rw [← Category.assoc, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (H.h ≫ p) = g ≫ p
    rw [← Category.assoc, H.h₁]
  rel := by
    ext _ ⟨⟨_, h⟩, _⟩
    cases h

private theorem clientExInfinityUnit_app_eq (X : SSet.{u}) :
    SSet.exInfinityUnit.app X =
      clientExTowerZeroHom X ≫ colimit.ι (clientExTower X) 0 := by
  unfold SSet.exInfinityUnit clientExTowerZeroHom
  rfl

private theorem clientExTowerZeroMapRaw_colimit
    (X : SSet.{u}) (k : ℕ) :
    clientExTowerZeroMapRaw X k ≫
        colimit.ι (clientExTower X) k =
      SSet.exInfinityUnit.app X := by
  rw [clientExInfinityUnit_app_eq]
  unfold clientExTowerZeroMapRaw
  rw [Category.assoc, colimit.w]

private theorem clientExInfinity_map_eq
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.exInfinity.map f =
      Limits.colimMap (clientExTowerFunctor.map f) := by
  unfold SSet.exInfinity clientExTowerFunctor clientExTower clientExIter
  rfl

private theorem clientExTower_colimit_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    (clientExTowerFunctor.map f).app k ≫
        colimit.ι (clientExTower Y) k =
      colimit.ι (clientExTower X) k ≫ SSet.exInfinity.map f := by
  rw [clientExInfinity_map_eq]
  exact (Limits.ι_colimMap (clientExTowerFunctor.map f) k).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallificationImageInfinityHomotopy
    {X : TopCat.{u}} {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    {n k : ℕ} (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (hq : q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      geometricSubdivisionAdjunct b k) :
    SSet.Homotopy
      ((sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _ q ≫
          colimit.ι (clientExTower
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X)) : SSet.{u})) k) ≫
        SSet.exInfinity.map (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι)
      (sSetTopAdj.homEquiv _ _ b ≫
        SSet.exInfinityUnit.app (TopCat.toSSet.obj X)) := by
  let j := (AlgebraicTopology.subordinateCover
    (fun i => (U i : Set X))).ι
  let Hstage := smallificationImageStageHomotopy U b q hq
  let H := homotopyPostcomp Hstage
    (colimit.ι (clientExTower (TopCat.toSSet.obj X)) k)
  have hsource :
      (sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _ q ≫
          (clientExTowerFunctor.map j).app k) ≫
        colimit.ι (clientExTower (TopCat.toSSet.obj X)) k =
      (sdIterClientHomEquiv k (Δ[n] : SSet.{u}) _ q ≫
          colimit.ι (clientExTower
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X)) : SSet.{u})) k) ≫
        SSet.exInfinity.map j := by
    simp only [Category.assoc]
    rw [clientExTower_colimit_naturality]
  have htarget :
      (sSetTopAdj.homEquiv _ _ b ≫
          clientExTowerZeroMapRaw (TopCat.toSSet.obj X) k) ≫
        colimit.ι (clientExTower (TopCat.toSSet.obj X)) k =
      sSetTopAdj.homEquiv _ _ b ≫
        SSet.exInfinityUnit.app (TopCat.toSSet.obj X) := by
    simp only [Category.assoc]
    rw [clientExTowerZeroMapRaw_colimit]
  refine
    { h := H.h
      h₀ := ?_
      h₁ := ?_
      rel := H.rel }
  · rw [H.h₀]
    exact hsource
  · rw [H.h₁]
    exact htarget

private noncomputable def meshStdToRealizationLocal (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)),
      SSet.toTop.obj (Δ[n] : SSet.{u})) :=
  ⟨fun z => (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm z,
    (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm.continuous⟩

private theorem image_range_sdIterCellMap_eq_local
    {X : TopCat.{u}} {n k d : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (cell : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    (b.hom.comp (meshStdToRealizationLocal.{u} n)) ''
        Set.range (SSet.sdIterCellMap n k cell).hom =
      Set.range
        (SSet.toTop.map cell ≫
          (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm x, ?_⟩
    simp [SSet.sdIterCellMap, meshStdToRealizationLocal]
  · rintro ⟨x, rfl⟩
    refine ⟨SSet.sdIterCellMap n k cell
        (SimplexCategory.toTopHomeo.{u} ⦋d⦌ x), ?_, ?_⟩
    · exact ⟨SimplexCategory.toTopHomeo.{u} ⦋d⦌ x, rfl⟩
    · simp [SSet.sdIterCellMap, meshStdToRealizationLocal]

private theorem exists_subordinateLift_of_range
    {X : TopCat.{u}} {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    {n k : ℕ} (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (hk : ∀ {d : ℕ}
      (cell : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      ∃ i,
        Set.range
          (SSet.toTop.map cell ≫
            (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom ⊆
          (U i : Set X)) :
    ∃ q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u}),
      q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
          geometricSubdivisionAdjunct b k := by
  let g := geometricSubdivisionAdjunct b k
  have hg : SSet.Subcomplex.range g ≤
      AlgebraicTopology.subordinateCover (fun i => (U i : Set X)) := by
    intro a y hy
    obtain ⟨z, rfl⟩ := hy
    induction a using Opposite.rec
    rename_i a
    induction a using SimplexCategory.rec
    rename_i d
    let cell : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u}) :=
      SSet.yonedaEquiv.symm z
    obtain ⟨i, hi⟩ := hk cell
    apply (le_iSup (fun i => AlgebraicTopology.subordinateSet
      (X := X) (U i : Set X)) i)
    change Set.range (X.toSSetObjEquiv _ (g.app _ z)) ⊆ (U i : Set X)
    have hcell := geometricSubdivisionAdjunct_cell b cell
    have hy : SSet.yonedaEquiv (cell ≫ g) = g.app _ z := by
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    have htop := congrArg (sSetTopAdj.homEquiv
      (Δ[d] : SSet.{u}) X).symm hcell
    rw [Equiv.symm_apply_apply] at htop
    rw [← hy]
    intro y hyRange
    obtain ⟨z₀, rfl⟩ := hyRange
    apply hi
    let zTop : SSet.toTop.obj (Δ[d] : SSet.{u}) :=
      (SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀
    refine ⟨zTop, ?_⟩
    have heval := sSetTopAdj_homEquiv_symm_apply (cell ≫ g)
      (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) z₀
    have hinput :
        SSet.toTop.map (SSet.yonedaEquiv.symm
          (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀) = zTop := by
      simp [zTop]
    have hcomponent :
        ((cell ≫ g).app (Opposite.op ⦋d⦌))
            (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) =
          SSet.yonedaEquiv (cell ≫ g) := by
      rw [← SSet.yonedaEquiv_comp]
      simp
    have heval' :
        ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
          (cell ≫ g)) zTop =
          X.toSSetObjEquiv _ (SSet.yonedaEquiv (cell ≫ g)) z₀ := by
      calc
        _ = ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
            (cell ≫ g))
            (SSet.toTop.map (SSet.yonedaEquiv.symm
              (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
                ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z₀)) := by
          rw [hinput]
        _ = X.toSSetObjEquiv _
            (((cell ≫ g).app (Opposite.op ⦋d⦌))
              (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u})))) z₀ := heval
        _ = _ := congrArg
          (fun s => X.toSSetObjEquiv (Opposite.op ⦋d⦌) s z₀) hcomponent
    exact (ConcreteCategory.congr_hom htop zTop).symm.trans heval'
  let q := SSet.Subcomplex.lift g hg
  exact ⟨q, SSet.Subcomplex.lift_ι g hg⟩
private theorem exInfinityUnit_W_of_kanComplex
    (Z : SSet.{u}) (hZ : Z.KanComplex) :
    SSet.KanComplex.W (SSet.exInfinityUnit.app Z) := by
  let hSource : ((𝟭 SSet.{u}).obj Z).KanComplex := by
    simpa only [Functor.id_obj] using hZ
  let hTarget : (SSet.exInfinity.obj Z).KanComplex :=
    SSet.exInfinity_kanComplex Z
  exact (@SSet.KanComplex.W_iff_realizationWeakEquivalence _ _
    hSource hTarget (SSet.exInfinityUnit.app Z)).mpr
      (SSet.exInfinityUnit_mem_realizationWeakEquivalences Z)

private def homotopyEdge
    {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g)
    (x : A _⦋0⦌) : B.Edge (f.app _ x) (g.app _ x) :=
  let h := H.toSimplicialObjectHomotopy
  SSet.Edge.mk (h.h 0 x)
    (by rw [← h.h_last_comp_δ_last 0]; rfl)
    (by rw [← SimplicialObject.Homotopy.h_zero_comp_δ_zero]; rfl)

private theorem piZero_yoneda_eq_of_homotopy
    {B : SSet.{u}} {f g : (Δ[0] : SSet.{u}) ⟶ B}
    (H : SSet.Homotopy f g) :
    SSet.π₀.mk (SSet.yonedaEquiv f) =
      SSet.π₀.mk (SSet.yonedaEquiv g) := by
  let x₀ : (Δ[0] : SSet.{u}) _⦋0⦌ :=
    SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have h := SSet.π₀.sound (homotopyEdge H x₀)
  dsimp only [x₀] at h
  simpa only [← SSet.yonedaEquiv_comp, Category.id_comp] using h

private theorem subordinateCover_mapπ₀_surjective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    Function.Surjective
      (SSet.mapπ₀ (SSet.exInfinity.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι)) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  have hη : SSet.KanComplex.W (SSet.exInfinityUnit.app B) :=
    exInfinityUnit_W_of_kanComplex B (TopCat.toSSet_obj_kanComplex X)
  intro z
  obtain ⟨zB, hzB⟩ := hη.bijective_mapπ₀.2 z
  induction zB using SSet.π₀.rec with
  | mk x =>
      let xmap : (Δ[0] : SSet.{u}) ⟶ B := SSet.yonedaEquiv.symm x
      let b : SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶ X :=
        (sSetTopAdj.homEquiv (Δ[0] : SSet.{u}) X).symm xmap
      obtain ⟨k, q, hq⟩ := exists_subordinateSubdivision U hU b
      let amap : (Δ[0] : SSet.{u}) ⟶ SSet.exInfinity.obj A :=
        sdIterClientHomEquiv k (Δ[0] : SSet.{u}) A q ≫
          colimit.ι (clientExTower A) k
      let H : SSet.Homotopy (amap ≫ ej)
          (xmap ≫ SSet.exInfinityUnit.app B) := by
        let H₀ := smallificationImageInfinityHomotopy U b q hq
        refine
          { h := H₀.h
            h₀ := H₀.h₀
            h₁ := ?_
            rel := H₀.rel }
        rw [H₀.h₁]
        change (sSetTopAdj.homEquiv _ _ b ≫
            SSet.exInfinityUnit.app B) =
          xmap ≫ SSet.exInfinityUnit.app B
        rw [Equiv.apply_symm_apply]
      refine ⟨SSet.π₀.mk (SSet.yonedaEquiv amap), ?_⟩
      have hH := piZero_yoneda_eq_of_homotopy H
      have htarget :
          SSet.π₀.mk (SSet.yonedaEquiv
            (xmap ≫ SSet.exInfinityUnit.app B)) = z := by
        calc
          _ = SSet.π₀.mk
              ((SSet.exInfinityUnit.app B).app _ x) := by
            rw [SSet.yonedaEquiv_comp]
            simp only [xmap, Equiv.apply_symm_apply]
          _ = SSet.mapπ₀ (SSet.exInfinityUnit.app B)
              (SSet.π₀.mk x) := by rfl
          _ = z := hzB
      calc
        SSet.mapπ₀ (SSet.exInfinity.map
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)
            (SSet.π₀.mk (SSet.yonedaEquiv amap)) =
          SSet.π₀.mk (SSet.yonedaEquiv (amap ≫ ej)) := by
            simp only [SSet.mapπ₀_mk, ← SSet.yonedaEquiv_comp, ej, j]
        _ = SSet.π₀.mk (SSet.yonedaEquiv
            (xmap ≫ SSet.exInfinityUnit.app B)) := hH
        _ = z := htarget

private theorem exUnit_app_down_local
    (Z : SSet.{u}) {n : SimplexCategory}
    (x : Z.obj (Opposite.op n)) :
    ULift.down ((SSet.exUnit.app Z).app (Opposite.op n) x) =
      SimplexCategory.lastVertex.app n ≫
        SSet.yonedaEquiv.symm x := by
  let α := SSet.stdSimplex.{u}.leftKanExtensionUnit
    SimplexCategory.sd.{u}
  have hα : SSet.sd.{u}.IsLeftKanExtension α := by
    change (SSet.stdSimplex.{u}.leftKanExtension
      SimplexCategory.sd.{u}).IsLeftKanExtension
        (SSet.stdSimplex.{u}.leftKanExtensionUnit
          SimplexCategory.sd.{u})
    infer_instance
  have happ :=
    @Presheaf.uliftYonedaAdjunction_homEquiv_app.{0, 0, u, 0, u + 1}
      SimplexCategory _ (SSet.{u}) _ SimplexCategory.sd.{u} _
      SSet.sd.{u} α hα Z Z (SSet.lastVertex.app Z)
      (Opposite.op n) x
  have happ' :
      (SSet.exUnit.app Z).app (Opposite.op n) x =
        ULift.up
          (SSet.stdSimplex.sdIso.inv.app n ≫
            SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
            SSet.lastVertex.app Z) := by
    simpa only [SSet.exUnit, α, SSet.sdExAdjunction,
      SSet.ex, SSet.sd, SSet.yonedaEquiv] using! happ
  have hdown := congrArg ULift.down happ'
  rw [SSet.lastVertex.naturality] at hdown
  rw [← Category.assoc, SSet.lastVertex_fac] at hdown
  exact hdown

private def zeroSubdivisionVertex :
    (SimplexCategory.sd.{u}.obj ⦋0⦌) _⦋0⦌ :=
  ComposableArrows.mk₀
    (SimplexCategory.sdSingletonChain ⦋0⦌ 0)

private noncomputable def zeroLastVertexSection :
    (Δ[0] : SSet.{u}) ⟶ SimplexCategory.sd.{u}.obj ⦋0⦌ :=
  SSet.yonedaEquiv.symm zeroSubdivisionVertex

private theorem zeroLastVertexSection_retraction :
    zeroLastVertexSection.{u} ≫
        SimplexCategory.lastVertex.app ⦋0⦌ =
      𝟙 (Δ[0] : SSet.{u}) := by
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem zeroChain_eq
    (S T : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin 1))) : S = T := by
  apply PartialOrder.NonemptyFiniteChains.ext
  ext a
  constructor
  · intro _
    obtain ⟨b, hb⟩ := T.nonempty
    simpa only [Subsingleton.elim a b] using hb
  · intro _
    obtain ⟨b, hb⟩ := S.nonempty
    simpa only [Subsingleton.elim a b] using hb

private theorem zeroLastVertexSection_section :
    SimplexCategory.lastVertex.app ⦋0⦌ ≫
        zeroLastVertexSection.{u} =
      𝟙 (SimplexCategory.sd.{u}.obj ⦋0⦌) := by
  ext d z
  apply ComposableArrows.ext
    (h := fun i => zeroChain_eq _ _)
    (w := by intro i hi; subsingleton)

private theorem exUnit_app_zero_surjective (Z : SSet.{u}) :
    Function.Surjective
      ((SSet.exUnit.app Z).app (Opposite.op ⦋0⦌)) := by
  intro z
  let x : Z _⦋0⦌ := SSet.yonedaEquiv
    (zeroLastVertexSection.{u} ≫ ULift.down z)
  refine ⟨x, ULift.down_injective ?_⟩
  rw [exUnit_app_down_local]
  change SimplexCategory.lastVertex.app ⦋0⦌ ≫
      SSet.yonedaEquiv.symm x = ULift.down z
  rw [show SSet.yonedaEquiv.symm x =
      zeroLastVertexSection.{u} ≫ ULift.down z by
    exact Equiv.symm_apply_apply _ _]
  rw [← Category.assoc, zeroLastVertexSection_section,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem clientExTowerZeroMapRaw_succ
    (Z : SSet.{u}) (k : ℕ) :
    clientExTowerZeroMapRaw Z (k + 1) =
      clientExTowerZeroMapRaw Z k ≫
        SSet.exUnit.app ((clientExIter k).obj Z) := by
  let a : 0 ⟶ k := homOfLE (Nat.zero_le k)
  let b : k ⟶ k + 1 := homOfLE (Nat.le_add_right k 1)
  let c : 0 ⟶ k + 1 := homOfLE (Nat.zero_le (k + 1))
  have hc : c = a ≫ b := Subsingleton.elim _ _
  unfold clientExTowerZeroMapRaw
  rw [show (homOfLE (Nat.zero_le (k + 1)) : 0 ⟶ k + 1) = c by rfl,
    hc, (clientExTower Z).map_comp, clientExTower_map_succ]
  exact (Category.assoc _ _ _).symm

private theorem clientExTowerZeroMapRaw_app_zero_surjective
    (Z : SSet.{u}) (k : ℕ) :
    Function.Surjective
      ((clientExTowerZeroMapRaw Z k).app (Opposite.op ⦋0⦌)) := by
  induction k with
  | zero =>
      intro z
      exact ⟨z, rfl⟩
  | succ k ih =>
      rw [clientExTowerZeroMapRaw_succ]
      exact (exUnit_app_zero_surjective ((clientExIter k).obj Z)).comp ih

set_option backward.isDefEq.respectTransparency false in
private theorem exInfinityUnit_app_zero_surjective (Z : SSet.{u}) :
    Function.Surjective
      ((SSet.exInfinityUnit.app Z).app (Opposite.op ⦋0⦌)) := by
  intro z
  let zmap : (Δ[0] : SSet.{u}) ⟶ SSet.exInfinity.obj Z :=
    SSet.yonedaEquiv.symm z
  obtain ⟨j, p, hp⟩ := clientExists_exTower_factor Z
    (Δ[0] : SSet.{u}) zmap
  let k : ℕ := CategoryTheory.AsSmall.down.obj j
  obtain ⟨x, hx⟩ := clientExTowerZeroMapRaw_app_zero_surjective Z k
    (SSet.yonedaEquiv p)
  refine ⟨x, ?_⟩
  have hunit := clientExTowerZeroMapRaw_colimit Z k
  calc
    (SSet.exInfinityUnit.app Z).app _ x =
        ((clientExTowerZeroMapRaw Z k ≫
          colimit.ι (clientExTower Z) k).app _) x := by
      exact congrArg
        (fun f => f.app (Opposite.op ⦋0⦌) x) hunit.symm
    _ = (colimit.ι (clientExTower Z) k).app _
        ((clientExTowerZeroMapRaw Z k).app _ x) := rfl
    _ = (colimit.ι (clientExTower Z) k).app _
        (SSet.yonedaEquiv p) := by rw [hx]
    _ = SSet.yonedaEquiv
        (p ≫ colimit.ι (clientExTower Z) k) := by
      exact (SSet.yonedaEquiv_comp p
        (colimit.ι (clientExTower Z) k)).symm
    _ = SSet.yonedaEquiv zmap := congrArg SSet.yonedaEquiv hp
    _ = z := by
      exact Equiv.apply_symm_apply _ _

private theorem sSetTopAdj_homEquiv_const_local
    (K : SSet.{u}) (X : TopCat.{u}) (y : X) :
    sSetTopAdj.homEquiv K X
        (TopCat.const (X := SSet.toTop.obj K) y) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  rw [Adjunction.homEquiv_unit, TopCat.toSSet_map_const,
    SSet.comp_const]

private theorem topAdjoint_face_constant
    {X : TopCat.{u}} {n : ℕ} (i : Fin (n + 2))
    (xmap : (Δ[n + 1] : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (v : (TopCat.toSSet.obj X) _⦋0⦌)
    (hface : SSet.stdSimplex.δ i ≫ xmap = SSet.const v) :
    SSet.toTop.map (SSet.stdSimplex.δ i) ≫
        (sSetTopAdj.homEquiv _ _).symm xmap =
      TopCat.const (TopCat.toSSetObj₀Equiv v) := by
  apply (sSetTopAdj.homEquiv (Δ[n] : SSet.{u}) X).injective
  rw [sSetTopAdj.homEquiv_naturality_left,
    Equiv.apply_symm_apply, hface,
    sSetTopAdj_homEquiv_const_local]
  rw [Equiv.symm_apply_apply]

private theorem geometricAdjunct_face_constant_local
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (v : (TopCat.toSSet.obj X) _⦋0⦌)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv v)) :
    (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        geometricSubdivisionAdjunct b k =
      SSet.const v := by
  let _ : Mono (SSet.stdSimplex.{u}.map
      (SimplexCategory.δ i)) := by
    change Mono (SSet.stdSimplex.δ i)
    infer_instance
  rw [show SSet.stdSimplex.δ i =
    SSet.stdSimplex.map (SimplexCategory.δ i) by rfl]
  rw [geometricSubdivisionAdjunct_naturality_of_mono]
  rw [show SSet.toTop.map (SSet.stdSimplex.map
      (SimplexCategory.δ i)) =
    SSet.toTop.map (SSet.stdSimplex.δ i) by rfl]
  rw [hb]
  have hconst :
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫
          TopCat.const (TopCat.toSSetObj₀Equiv v) =
        TopCat.const
          (X := SSet.toTop.obj ((SSet.sdIter k).obj
            (Δ[n] : SSet.{u})))
          (TopCat.toSSetObj₀Equiv v) := by
    apply TopCat.ext
    intro z
    rfl
  unfold geometricSubdivisionAdjunct
  rw [hconst, sSetTopAdj_homEquiv_const_local,
    Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem mate_const_colimit
    {Z : SSet.{u}} (z : Z _⦋0⦌) (k : ℕ) :
    sdIterClientHomEquiv k (Δ[0] : SSet.{u}) Z
          (SSet.const (X := (SSet.sdIter k).obj (Δ[0] : SSet.{u})) z) ≫
        colimit.ι (clientExTower Z) k =
      SSet.const ((SSet.exInfinityUnit.app Z).app _ z) := by
  have hc :
      SSet.const (X := (SSet.sdIter k).obj (Δ[0] : SSet.{u})) z =
        towerLastVertex (Δ[0] : SSet.{u}) k ≫
          SSet.const (X := (Δ[0] : SSet.{u})) z := by
    symm
    exact SSet.comp_const _ _
  rw [hc, towerLastVertex_promote]
  simp only [Category.assoc]
  rw [clientExTowerZeroMapRaw_colimit]
  exact SSet.const_comp z (SSet.exInfinityUnit.app Z)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def subordinateCover_lift_edge
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    {a₀ a₁ : (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}) _⦋0⦌}
    (e : (TopCat.toSSet.obj X).Edge
      ((AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι.app _ a₀)
      ((AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι.app _ a₁)) :
    (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})).Edge
      ((SSet.exInfinityUnit.app _).app _ a₀)
      ((SSet.exInfinityUnit.app _).app _ a₁) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let emap : (Δ[1] : SSet.{u}) ⟶ B :=
    SSet.yonedaEquiv.symm e.edge
  have hsrc : SSet.stdSimplex.δ 1 ≫ emap =
      SSet.const (j.app _ a₀) := by
    dsimp only [emap]
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      e.src_eq, SSet.yonedaEquiv_symm_zero]
  have htgt : SSet.stdSimplex.δ 0 ≫ emap =
      SSet.const (j.app _ a₁) := by
    dsimp only [emap]
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      e.tgt_eq, SSet.yonedaEquiv_symm_zero]
  let b : SSet.toTop.obj (Δ[1] : SSet.{u}) ⟶ X :=
    (sSetTopAdj.homEquiv (Δ[1] : SSet.{u}) X).symm emap
  have hbSrc : SSet.toTop.map (SSet.stdSimplex.δ 1) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv (j.app _ a₀)) :=
    topAdjoint_face_constant 1 emap (j.app _ a₀) hsrc
  have hbTgt : SSet.toTop.map (SSet.stdSimplex.δ 0) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv (j.app _ a₁)) :=
    topAdjoint_face_constant 0 emap (j.app _ a₁) htgt
  let hsmall := exists_subordinateSubdivision U hU b
  let k : ℕ := hsmall.choose
  let q : (SSet.sdIter k).obj (Δ[1] : SSet.{u}) ⟶ A :=
    hsmall.choose_spec.choose
  have hq : q ≫ j = geometricSubdivisionAdjunct b k :=
    hsmall.choose_spec.choose_spec
  have qsrc : (SSet.sdIter k).map (SSet.stdSimplex.δ 1) ≫ q =
      SSet.const (X := (SSet.sdIter k).obj (Δ[0] : SSet.{u})) a₀ := by
    apply (cancel_mono (f := j)).mp
    rw [Category.assoc, hq]
    rw [geometricAdjunct_face_constant_local 0 k 1 b (j.app _ a₀) hbSrc]
    rw [SSet.const_comp]
  have qtgt : (SSet.sdIter k).map (SSet.stdSimplex.δ 0) ≫ q =
      SSet.const (X := (SSet.sdIter k).obj (Δ[0] : SSet.{u})) a₁ := by
    apply (cancel_mono (f := j)).mp
    rw [Category.assoc, hq]
    rw [geometricAdjunct_face_constant_local 0 k 0 b (j.app _ a₁) hbTgt]
    rw [SSet.const_comp]
  let amap : (Δ[1] : SSet.{u}) ⟶ SSet.exInfinity.obj A :=
    sdIterClientHomEquiv k (Δ[1] : SSet.{u}) A q ≫
      colimit.ι (clientExTower A) k
  have amapSrc : SSet.stdSimplex.δ 1 ≫ amap =
      SSet.const ((SSet.exInfinityUnit.app A).app _ a₀) := by
    unfold amap
    rw [← Category.assoc, ← sdIterClientHomEquiv_naturality_left,
      qsrc, mate_const_colimit]
  have amapTgt : SSet.stdSimplex.δ 0 ≫ amap =
      SSet.const ((SSet.exInfinityUnit.app A).app _ a₁) := by
    unfold amap
    rw [← Category.assoc, ← sdIterClientHomEquiv_naturality_left,
      qtgt, mate_const_colimit]
  exact SSet.Edge.mk (SSet.yonedaEquiv amap)
    (SSet.yonedaEquiv.symm.injective (by
      rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        Equiv.symm_apply_apply, amapSrc,
        SSet.yonedaEquiv_symm_zero]))
    (SSet.yonedaEquiv.symm.injective (by
      rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        Equiv.symm_apply_apply, amapTgt,
        SSet.yonedaEquiv_symm_zero]))

private theorem subordinateCover_ι_app_zero_surjective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    Function.Surjective
      ((AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι.app (Opposite.op ⦋0⦌)) := by
  intro x
  obtain ⟨i, hi⟩ := hU.exists_mem (TopCat.toSSetObj₀Equiv x)
  refine ⟨⟨x, ?_⟩, rfl⟩
  apply (le_iSup
    (fun i => AlgebraicTopology.subordinateSet (X := X) (U i : Set X)) i)
  change Set.range (X.toSSetObjEquiv (Opposite.op ⦋0⦌) x) ⊆ U i
  rintro y ⟨z, rfl⟩
  obtain rfl := Subsingleton.elim z default
  exact hi

private theorem subordinateCover_piZero_eq_of_exInfinity_image_eq
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (a₀ a₁ : (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}) _⦋0⦌)
    (h : SSet.mapπ₀
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        (SSet.π₀.mk
          ((SSet.exInfinityUnit.app _).app _ a₀)) =
      SSet.mapπ₀
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        (SSet.π₀.mk
          ((SSet.exInfinityUnit.app _).app _ a₁))) :
    SSet.π₀.mk ((SSet.exInfinityUnit.app _).app _ a₀) =
      SSet.π₀.mk ((SSet.exInfinityUnit.app _).app _ a₁) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  have hη : SSet.KanComplex.W (SSet.exInfinityUnit.app B) :=
    exInfinityUnit_W_of_kanComplex B (TopCat.toSSet_obj_kanComplex X)
  have hnatural : j ≫ SSet.exInfinityUnit.app B =
      SSet.exInfinityUnit.app A ≫ ej := by
    simpa only [Functor.id_map] using
      SSet.exInfinityUnit.naturality j
  have himage :
      SSet.mapπ₀ (SSet.exInfinityUnit.app B)
          (SSet.π₀.mk (j.app _ a₀)) =
        SSet.mapπ₀ (SSet.exInfinityUnit.app B)
          (SSet.π₀.mk (j.app _ a₁)) := by
    calc
      SSet.mapπ₀ (SSet.exInfinityUnit.app B)
          (SSet.π₀.mk (j.app _ a₀)) =
          SSet.mapπ₀ (j ≫ SSet.exInfinityUnit.app B)
            (SSet.π₀.mk a₀) := by
              rfl
      _ = SSet.mapπ₀
          (SSet.exInfinityUnit.app A ≫ ej)
            (SSet.π₀.mk a₀) := by
              rw [hnatural]
      _ = SSet.mapπ₀ ej
          (SSet.π₀.mk
            ((SSet.exInfinityUnit.app A).app _ a₀)) := by
              rfl
      _ = SSet.mapπ₀ ej
          (SSet.π₀.mk
            ((SSet.exInfinityUnit.app A).app _ a₁)) := by
              exact h
      _ = SSet.mapπ₀
          (SSet.exInfinityUnit.app A ≫ ej)
            (SSet.π₀.mk a₁) := by
              rfl
      _ = SSet.mapπ₀ (j ≫ SSet.exInfinityUnit.app B)
            (SSet.π₀.mk a₁) := by
              rw [hnatural]
      _ = SSet.mapπ₀ (SSet.exInfinityUnit.app B)
          (SSet.π₀.mk (j.app _ a₁)) := by
              rfl
  have hbase : SSet.π₀.mk (j.app _ a₀) =
      SSet.π₀.mk (j.app _ a₁) :=
    hη.bijective_mapπ₀.1 himage
  rw [SSet.π₀.mk_eq_mk_iff] at hbase ⊢
  have liftEqv : ∀ {x y : B _⦋0⦌},
      Relation.EqvGen SSet.π₀Rel x y →
      ∀ (b₀ b₁ : A _⦋0⦌),
        x = j.app _ b₀ → y = j.app _ b₁ →
          Relation.EqvGen SSet.π₀Rel
            ((SSet.exInfinityUnit.app A).app _ b₀)
            ((SSet.exInfinityUnit.app A).app _ b₁) := by
    intro x y hxy
    induction hxy with
    | rel x y hrel =>
        intro b₀ b₁ hx hy
        subst x
        subst y
        obtain ⟨e⟩ := hrel
        exact Relation.EqvGen.rel _ _
          ⟨subordinateCover_lift_edge U hU e⟩
    | refl x =>
        intro b₀ b₁ hx hy
        have hb : b₀ = b₁ := by
          apply Subtype.ext
          exact hx.symm.trans hy
        subst b₁
        exact Relation.EqvGen.refl _
    | symm x y _ ih =>
        intro b₀ b₁ hx hy
        exact Relation.EqvGen.symm _ _ (ih b₁ b₀ hy hx)
    | trans x y z _ _ ih₀ ih₁ =>
        intro b₀ b₁ hx hz
        obtain ⟨m, hm⟩ := subordinateCover_ι_app_zero_surjective U hU y
        exact Relation.EqvGen.trans _ _ _
          (ih₀ b₀ m hx hm.symm) (ih₁ m b₁ hm.symm hz)
  exact liftEqv hbase a₀ a₁ rfl rfl

private theorem subordinateCover_mapπ₀_injective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    Function.Injective
      (SSet.mapπ₀ (SSet.exInfinity.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι)) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  intro z₀ z₁ h
  induction z₀ using SSet.π₀.rec with
  | mk x₀ =>
      induction z₁ using SSet.π₀.rec with
      | mk x₁ =>
          obtain ⟨a₀, ha₀⟩ :=
            exInfinityUnit_app_zero_surjective A x₀
          obtain ⟨a₁, ha₁⟩ :=
            exInfinityUnit_app_zero_surjective A x₁
          subst x₀
          subst x₁
          exact
            subordinateCover_piZero_eq_of_exInfinity_image_eq
              U hU a₀ a₁ h

private theorem subordinateCover_mapπ₀_bijective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    Function.Bijective
      (SSet.mapπ₀ (SSet.exInfinity.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι)) :=
  ⟨subordinateCover_mapπ₀_injective U hU,
    subordinateCover_mapπ₀_surjective U hU⟩

private theorem clientExTowerZeroMapRaw_transition
    (Z : SSet.{u}) {i k : CategoryTheory.AsSmall.{u} ℕ}
    (a : i ⟶ k) :
    clientExTowerZeroMapRaw Z (CategoryTheory.AsSmall.down.obj i) ≫
        (clientExTower Z).map (CategoryTheory.AsSmall.down.map a) =
      clientExTowerZeroMapRaw Z
        (CategoryTheory.AsSmall.down.obj k) := by
  unfold clientExTowerZeroMapRaw
  rw [Category.assoc, ← (clientExTower Z).map_comp]
  have h :
      (homOfLE (Nat.zero_le (CategoryTheory.AsSmall.down.obj i)) ≫
          CategoryTheory.AsSmall.down.map a) =
        homOfLE (Nat.zero_le
          (CategoryTheory.AsSmall.down.obj k)) :=
    Subsingleton.elim _ _
  rw [h]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_clientExTower_pointed_factor
    (Z : SSet.{u}) {n : ℕ} (z : Z _⦋0⦌)
    (p : (SSet.exInfinity.obj Z).PtSimplex n
      ((SSet.exInfinityUnit.app Z).app _ z)) :
    ∃ (k : CategoryTheory.AsSmall.{u} ℕ)
      (r : (Δ[n] : SSet.{u}) ⟶
        (clientExTower Z).obj (CategoryTheory.AsSmall.down.obj k)),
      r ≫ colimit.ι (clientExTower Z)
          (CategoryTheory.AsSmall.down.obj k) =
            SSet.RelativeMorphism.map p ∧
        (SSet.boundary n).ι ≫ r =
          SSet.const z ≫ clientExTowerZeroMapRaw Z
            (CategoryTheory.AsSmall.down.obj k) := by
  obtain ⟨i, r, hr⟩ := clientExists_exTower_factor Z
    (Δ[n] : SSet.{u}) (SSet.RelativeMorphism.map p)
  let c : (SSet.boundary n : SSet.{u}) ⟶
      (clientExTower Z).obj (CategoryTheory.AsSmall.down.obj i) :=
    SSet.const z ≫ clientExTowerZeroMapRaw Z
      (CategoryTheory.AsSmall.down.obj i)
  have hcolim :
      ((SSet.boundary n).ι ≫ r) ≫
          colimit.ι (clientExTower Z)
            (CategoryTheory.AsSmall.down.obj i) =
        c ≫ colimit.ι (clientExTower Z)
          (CategoryTheory.AsSmall.down.obj i) := by
    calc
      ((SSet.boundary n).ι ≫ r) ≫
          colimit.ι (clientExTower Z)
            (CategoryTheory.AsSmall.down.obj i) =
        (SSet.boundary n).ι ≫
          (r ≫ colimit.ι (clientExTower Z)
            (CategoryTheory.AsSmall.down.obj i)) := by
              rw [Category.assoc]
      _ = (SSet.boundary n).ι ≫
          SSet.RelativeMorphism.map p := by rw [hr]
      _ = SSet.const ((SSet.exInfinityUnit.app Z).app _ z) := by
        simpa only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
          using p.comm
      _ = c ≫ colimit.ι (clientExTower Z)
          (CategoryTheory.AsSmall.down.obj i) := by
        dsimp only [c]
        rw [Category.assoc, clientExTowerZeroMapRaw_colimit,
          SSet.const_comp]
        rfl
  obtain ⟨k, a, b, hab⟩ :=
    clientExists_exTower_later_eq Z (SSet.boundary n : SSet.{u})
      ((SSet.boundary n).ι ≫ r) c hcolim
  refine ⟨k, r ≫ (clientExTower Z).map
    (CategoryTheory.AsSmall.down.map a), ?_, ?_⟩
  · calc
      (r ≫ (clientExTower Z).map
          (CategoryTheory.AsSmall.down.map a)) ≫
          colimit.ι (clientExTower Z)
            (CategoryTheory.AsSmall.down.obj k) =
        r ≫ ((clientExTower Z).map
          (CategoryTheory.AsSmall.down.map a) ≫
            colimit.ι (clientExTower Z)
              (CategoryTheory.AsSmall.down.obj k)) := by
                rw [Category.assoc]
      _ = r ≫ colimit.ι (clientExTower Z)
          (CategoryTheory.AsSmall.down.obj i) := by
            rw [colimit.w]
      _ = SSet.RelativeMorphism.map p := by exact hr
  · have hba : CategoryTheory.AsSmall.down.map b =
        CategoryTheory.AsSmall.down.map a := Subsingleton.elim _ _
    calc
      (SSet.boundary n).ι ≫
          (r ≫ (clientExTower Z).map
            (CategoryTheory.AsSmall.down.map a)) =
        ((SSet.boundary n).ι ≫ r) ≫
          (clientExTower Z).map
            (CategoryTheory.AsSmall.down.map a) := by
              rw [Category.assoc]
      _ = c ≫ (clientExTower Z).map
          (CategoryTheory.AsSmall.down.map b) := hab
      _ = c ≫ (clientExTower Z).map
          (CategoryTheory.AsSmall.down.map a) := by rw [hba]
      _ = SSet.const z ≫
          (clientExTowerZeroMapRaw Z
              (CategoryTheory.AsSmall.down.obj i) ≫
            (clientExTower Z).map
              (CategoryTheory.AsSmall.down.map a)) := by
                rfl
      _ = SSet.const z ≫ clientExTowerZeroMapRaw Z
          (CategoryTheory.AsSmall.down.obj k) := by
            rw [clientExTowerZeroMapRaw_transition]

private noncomputable def stageTopAdjunct
    {X : TopCat.{u}} {n k : ℕ}
    (q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
      TopCat.toSSet.obj X) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X :=
  (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).inv ≫
    (sSetTopAdj.homEquiv _ _).symm q

private theorem geometricSubdivisionAdjunct_stageTopAdjunct
    {X : TopCat.{u}} {n k : ℕ}
    (q : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
      TopCat.toSSet.obj X) :
    geometricSubdivisionAdjunct (stageTopAdjunct q) k = q := by
  unfold geometricSubdivisionAdjunct stageTopAdjunct
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Equiv.apply_symm_apply]

private theorem geometricSubdivisionAdjunct_injective
    {X : TopCat.{u}} (n k : ℕ) :
    Function.Injective
      (fun b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X =>
        geometricSubdivisionAdjunct b k) := by
  intro b c h
  unfold geometricSubdivisionAdjunct at h
  have h' := (sSetTopAdj.homEquiv
    ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) X).injective h
  exact (cancel_epi
    (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom).mp h'

private theorem geometricSubdivisionAdjunct_const
    {X : TopCat.{u}} {n : ℕ} (k : ℕ)
    (z : (TopCat.toSSet.obj X) _⦋0⦌) :
    geometricSubdivisionAdjunct
        (TopCat.const (X := SSet.toTop.obj (Δ[n] : SSet.{u}))
          (TopCat.toSSetObj₀Equiv z)) k =
      SSet.const z := by
  unfold geometricSubdivisionAdjunct
  have hconst :
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫
          TopCat.const (TopCat.toSSetObj₀Equiv z) =
        TopCat.const
          (X := SSet.toTop.obj
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})))
          (TopCat.toSSetObj₀Equiv z) := by
    apply TopCat.ext
    intro x
    rfl
  rw [hconst, sSetTopAdj_homEquiv_const_local,
    Equiv.symm_apply_apply]

private theorem topFaceConstant_of_geometricFace
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (h : (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        geometricSubdivisionAdjunct b k = SSet.const z) :
    SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv z) := by
  let _ : Mono (SSet.stdSimplex.{u}.map
      (SimplexCategory.δ i)) := by
    change Mono (SSet.stdSimplex.δ i)
    infer_instance
  apply geometricSubdivisionAdjunct_injective n k
  calc
    geometricSubdivisionAdjunct
        (SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b) k =
      (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        geometricSubdivisionAdjunct b k := by
          exact (geometricSubdivisionAdjunct_naturality_of_mono
            (k := k) (SimplexCategory.δ i) b).symm
    _ = SSet.const z := h
    _ = geometricSubdivisionAdjunct
        (TopCat.const (TopCat.toSSetObj₀Equiv z)) k :=
      (geometricSubdivisionAdjunct_const k z).symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_pointed_stageTopAdjunct
    {X : TopCat.{u}} {n : ℕ}
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (p : (SSet.exInfinity.obj (TopCat.toSSet.obj X)).PtSimplex
      (n + 1) ((SSet.exInfinityUnit.app _).app _ z)) :
    ∃ (k : ℕ)
      (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X),
      sdIterClientHomEquiv k (Δ[n + 1] : SSet.{u}) _
          (geometricSubdivisionAdjunct b k) ≫
          colimit.ι (clientExTower (TopCat.toSSet.obj X)) k =
        SSet.RelativeMorphism.map p ∧
      ∀ i : Fin (n + 2),
        SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
          TopCat.const (TopCat.toSSetObj₀Equiv z) := by
  let B : SSet.{u} := TopCat.toSSet.obj X
  obtain ⟨ks, r, hr, hrBoundary⟩ :=
    exists_clientExTower_pointed_factor B z p
  let k : ℕ := CategoryTheory.AsSmall.down.obj ks
  let q : (SSet.sdIter k).obj (Δ[n + 1] : SSet.{u}) ⟶ B :=
    (sdIterClientHomEquiv k (Δ[n + 1] : SSet.{u}) B).symm r
  let b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X :=
    stageTopAdjunct q
  have hgeom : geometricSubdivisionAdjunct b k = q :=
    geometricSubdivisionAdjunct_stageTopAdjunct q
  have hmate : sdIterClientHomEquiv k
      (Δ[n + 1] : SSet.{u}) B q = r :=
    Equiv.apply_symm_apply _ _
  refine ⟨k, b, ?_, ?_⟩
  · rw [hgeom, hmate]
    exact hr
  · intro i
    apply topFaceConstant_of_geometricFace n k i b z
    rw [hgeom]
    apply (sdIterClientHomEquiv k
      (Δ[n] : SSet.{u}) B).injective
    calc
      sdIterClientHomEquiv k (Δ[n] : SSet.{u}) B
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫ q) =
        SSet.stdSimplex.δ i ≫ r := by
          rw [sdIterClientHomEquiv_naturality_left, hmate]
      _ = SSet.boundary.ι i ≫
          ((SSet.boundary (n + 1)).ι ≫ r) := by
            rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = SSet.boundary.ι i ≫
          (SSet.const z ≫ clientExTowerZeroMapRaw B k) := by
            rw [hrBoundary]
      _ = SSet.const z ≫ clientExTowerZeroMapRaw B k := by
            rw [← Category.assoc, SSet.comp_const]
      _ = sdIterClientHomEquiv k (Δ[n] : SSet.{u}) B
          (towerLastVertex (Δ[n] : SSet.{u}) k ≫
            SSet.const z) :=
        (towerLastVertex_promote (SSet.const z) k).symm
      _ = sdIterClientHomEquiv k (Δ[n] : SSet.{u}) B
          (SSet.const z) := by rw [SSet.comp_const]

private theorem geometricTowerTopHomotopy_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const y) :
    (SSet.toTop.map
        ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) ▷ TopCat.I) ≫
        (TopCat.Homotopy.comp (TopCat.Homotopy.refl b)
          (geometricTowerHomotopy (n + 1) k)).h =
      TopCat.const y := by
  apply TopCat.ext
  rintro ⟨x, t⟩
  exact geometricTowerHomotopy_face_postcomp_constant
    n k i b y hb (TopCat.I.homeomorph t) x

open MonoidalCategory Functor.LaxMonoidal in
private theorem toSSetHomotopy_precomp_constant
    {D E X : TopCat.{u}} {f g : D ⟶ X}
    (H : TopCat.Homotopy f g) (a : E ⟶ D) (y : X)
    (h : (a ▷ TopCat.I) ≫ H.h = TopCat.const y) :
    (TopCat.toSSet.map a ▷ (Δ[1] : SSet.{u})) ≫
        (TopCat.Homotopy.toSSet H).h =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  dsimp only [TopCat.Homotopy.toSSet]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    μ_natural_left_assoc, ← Functor.map_comp,
    h]
  rw [TopCat.toSSet_map_const, SSet.comp_const, SSet.comp_const]

set_option backward.isDefEq.respectTransparency false in
private theorem geometricTowerAdjunctHomotopy_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv z)) :
    ((SSet.sdIter k).map (SSet.stdSimplex.δ i) ▷
        (Δ[1] : SSet.{u})) ≫
        (geometricTowerAdjunctHomotopy b k).h =
      SSet.const z := by
  let hTop : TopCat.Homotopy
      ((SSet.toTopSdIterIso (Δ[n + 1] : SSet.{u}) k).hom ≫ b)
      (towerLastEndpoint (n + 1) k ≫ b) :=
    TopCat.Homotopy.comp (TopCat.Homotopy.refl b)
      (geometricTowerHomotopy (n + 1) k)
  let hSing := TopCat.Homotopy.toSSet hTop
  have hTopFace :
      (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) ▷ TopCat.I) ≫
          hTop.h =
        TopCat.const (TopCat.toSSetObj₀Equiv z) :=
    geometricTowerTopHomotopy_face_constant n k i b _ hb
  have hSingFace :
      (TopCat.toSSet.map (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i))) ▷
          (Δ[1] : SSet.{u})) ≫ hSing.h =
        SSet.const z := by
    simpa only [hSing, Equiv.symm_apply_apply] using
      toSSetHomotopy_precomp_constant hTop
        (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)))
        (TopCat.toSSetObj₀Equiv z) hTopFace
  have hunit := sSetTopAdj.unit.naturality
    ((SSet.sdIter k).map (SSet.stdSimplex.δ i))
  have hunit' :
      (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
          sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n + 1] : SSet.{u})) =
        sSetTopAdj.unit.app
            ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ≫
          TopCat.toSSet.map (SSet.toTop.map
            ((SSet.sdIter k).map (SSet.stdSimplex.δ i))) := by
    simpa only [Functor.id_map, Functor.comp_map] using hunit
  have hunitI := congrArg
    (fun f => f ▷ (Δ[1] : SSet.{u})) hunit'
  change
    ((SSet.sdIter k).map (SSet.stdSimplex.δ i) ▷
        (Δ[1] : SSet.{u})) ≫
      ((sSetTopAdj.unit.app
          ((SSet.sdIter k).obj (Δ[n + 1] : SSet.{u}))) ▷
        (Δ[1] : SSet.{u})) ≫ hSing.h = SSet.const z
  rw [← Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight]
  rw [hunitI]
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
    hSingFace, SSet.comp_const]

private theorem sdIterCylinderComparison_naturality
    {K L : SSet.{u}} (f : L ⟶ K) (k : ℕ) :
    (SSet.sdIter k).map (f ▷ (Δ[1] : SSet.{u})) ≫
        sdIterCylinderComparison K k =
      sdIterCylinderComparison L k ≫
        ((SSet.sdIter k).map f ▷ (Δ[1] : SSet.{u})) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, sdIterCylinderComparison,
      CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.whiskerRight_fst]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_fst]
    rw [← (SSet.sdIter k).map_comp
      (fst L (Δ[1] : SSet.{u})) f]
    rw [← (SSet.sdIter k).map_comp
      (f ▷ (Δ[1] : SSet.{u})) (fst K (Δ[1] : SSet.{u}))]
    exact congrArg (SSet.sdIter k).map
      (CartesianMonoidalCategory.whiskerRight_fst f _)
  · simp only [Category.assoc, sdIterCylinderComparison,
      CartesianMonoidalCategory.lift_snd,
      CartesianMonoidalCategory.whiskerRight_snd]
    rw [← Category.assoc, ← (SSet.sdIter k).map_comp]
    rw [CartesianMonoidalCategory.whiskerRight_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem sdIterMateHomotopy_precomp_constant
    {K L Z : SSet.{u}} {k : ℕ}
    {r s : (SSet.sdIter k).obj K ⟶ Z}
    (H : SSet.Homotopy r s) (f : L ⟶ K) (z : Z _⦋0⦌)
    (h : ((SSet.sdIter k).map f ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      SSet.const z) :
    (f ▷ (Δ[1] : SSet.{u})) ≫ (sdIterMateHomotopy H).h =
      SSet.const ((clientExTowerZeroMapRaw Z k).app _ z) := by
  change (f ▷ (Δ[1] : SSet.{u})) ≫
      sdIterClientHomEquiv k (K ⊗ (Δ[1] : SSet.{u})) Z
        (sdIterCylinderComparison K k ≫ H.h) = _
  rw [← sdIterClientHomEquiv_naturality_left]
  rw [← SSet.const_comp]
  rw [← towerLastVertex_promote]
  apply congrArg (sdIterClientHomEquiv k
    (L ⊗ (Δ[1] : SSet.{u})) Z)
  rw [← Category.assoc, sdIterCylinderComparison_naturality]
  calc
    (sdIterCylinderComparison L k ≫
        ((SSet.sdIter k).map f ▷ (Δ[1] : SSet.{u}))) ≫ H.h =
      sdIterCylinderComparison L k ≫
        (((SSet.sdIter k).map f ▷ (Δ[1] : SSet.{u})) ≫ H.h) :=
      Category.assoc _ _ _
    _ = sdIterCylinderComparison L k ≫ SSet.const z := by rw [h]
    _ = SSet.const z := SSet.comp_const _ _
    _ = towerLastVertex (L ⊗ (Δ[1] : SSet.{u})) k ≫
        SSet.const z := (SSet.comp_const _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem geometricTowerStageHomotopy_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv z)) :
    (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (geometricTowerStageHomotopy b k).h =
      SSet.const ((clientExTowerZeroMapRaw
        (TopCat.toSSet.obj X) k).app _ z) := by
  let H := geometricTowerAdjunctHomotopy b k
  change (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
      (sdIterMateHomotopy H).h = _
  exact sdIterMateHomotopy_precomp_constant H
    (SSet.stdSimplex.δ i) z
    (geometricTowerAdjunctHomotopy_face_constant n k i b z hb)

private theorem homotopyPostcomp_precomp_constant
    {A B C L : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (a : L ⟶ A) (z : B _⦋0⦌)
    (h : (a ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const z)
    (p : B ⟶ C) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ (homotopyPostcomp H p).h =
      SSet.const (p.app _ z) := by
  change (a ▷ (Δ[1] : SSet.{u})) ≫ (H.h ≫ p) = _
  rw [← Category.assoc, h, SSet.const_comp]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def geometricTowerInfinityHomotopy
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    SSet.Homotopy
      (sdIterClientHomEquiv k (Δ[n] : SSet.{u})
          (TopCat.toSSet.obj X) (geometricSubdivisionAdjunct b k) ≫
        colimit.ι (clientExTower (TopCat.toSSet.obj X)) k)
      (sSetTopAdj.homEquiv _ _ b ≫
        SSet.exInfinityUnit.app (TopCat.toSSet.obj X)) := by
  let H := homotopyPostcomp (geometricTowerStageHomotopy b k)
    (colimit.ι (clientExTower (TopCat.toSSet.obj X)) k)
  refine
    { h := H.h
      h₀ := H.h₀
      h₁ := ?_
      rel := H.rel }
  rw [H.h₁]
  simp only [Category.assoc]
  rw [clientExTowerZeroMapRaw_colimit]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem geometricTowerInfinityHomotopy_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv z)) :
    (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (geometricTowerInfinityHomotopy b k).h =
      SSet.const ((SSet.exInfinityUnit.app
        (TopCat.toSSet.obj X)).app _ z) := by
  let H := geometricTowerStageHomotopy b k
  have h := homotopyPostcomp_precomp_constant H
    (SSet.stdSimplex.δ i)
    ((clientExTowerZeroMapRaw (TopCat.toSSet.obj X) k).app _ z)
    (geometricTowerStageHomotopy_face_constant n k i b z hb)
    (colimit.ι (clientExTower (TopCat.toSSet.obj X)) k)
  change _ ≫ (homotopyPostcomp H _).h = _
  rw [h]
  apply congrArg SSet.const
  exact congrArg
    (fun f => f.app (Opposite.op ⦋0⦌) z)
    (clientExTowerZeroMapRaw_colimit (TopCat.toSSet.obj X) k)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pointedHomotopyOfFaceConstant
    {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    {p q : X.PtSimplex (n + 1) x}
    (H : SSet.Homotopy (SSet.RelativeMorphism.map p)
      (SSet.RelativeMorphism.map q))
    (hface : ∀ i : Fin (n + 2),
      (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        SSet.const x) :
    p.Homotopy q where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  rel := by
    rw [← cancel_epi (β_ _ _).hom]
    apply MonoidalClosed.curry_injective
    apply SSet.boundary.hom_ext
    intro i
    simp only [← MonoidalClosed.curry_natural_left]
    apply congrArg MonoidalClosed.curry
    rw [← cancel_epi (β_ _ _).hom]
    simp only [BraidedCategory.braiding_naturality_right_assoc,
      SymmetricCategory.symmetry_assoc]
    simp only [← MonoidalCategory.comp_whiskerRight_assoc,
      SSet.boundary.ι_ι, SSet.Subcomplex.ofSimplex_ι,
      SSet.comp_const]
    rw [hface i]

set_option backward.isDefEq.respectTransparency false in
private theorem smallificationImageInfinityHomotopy_face_constant
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X)
    (q : (SSet.sdIter k).obj (Δ[n + 1] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun a => (U a : Set X)) : SSet.{u}))
    (hq : q ≫ (AlgebraicTopology.subordinateCover
        (fun a => (U a : Set X))).ι =
      geometricSubdivisionAdjunct b k)
    (z : (TopCat.toSSet.obj X) _⦋0⦌)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b =
      TopCat.const (TopCat.toSSetObj₀Equiv z)) :
    (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (smallificationImageInfinityHomotopy U b q hq).h =
      SSet.const ((SSet.exInfinityUnit.app
        (TopCat.toSSet.obj X)).app _ z) := by
  let Hstage := smallificationImageStageHomotopy U b q hq
  have hStageFace :
      (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ Hstage.h =
        SSet.const ((clientExTowerZeroMapRaw
          (TopCat.toSSet.obj X) k).app _ z) := by
    change _ ≫ (geometricTowerStageHomotopy b k).h = _
    exact geometricTowerStageHomotopy_face_constant n k i b z hb
  have h := homotopyPostcomp_precomp_constant Hstage
    (SSet.stdSimplex.δ i)
    ((clientExTowerZeroMapRaw (TopCat.toSSet.obj X) k).app _ z)
    hStageFace
    (colimit.ι (clientExTower (TopCat.toSSet.obj X)) k)
  change _ ≫ (homotopyPostcomp Hstage _).h = _
  rw [h]
  apply congrArg SSet.const
  exact congrArg
    (fun f => f.app (Opposite.op ⦋0⦌) z)
    (clientExTowerZeroMapRaw_colimit (TopCat.toSSet.obj X) k)

set_option backward.isDefEq.respectTransparency false in
private theorem mate_const_colimit_general
    {K Z : SSet.{u}} (z : Z _⦋0⦌) (k : ℕ) :
    sdIterClientHomEquiv k K Z
          (SSet.const (X := (SSet.sdIter k).obj K) z) ≫
        colimit.ι (clientExTower Z) k =
      SSet.const ((SSet.exInfinityUnit.app Z).app _ z) := by
  have hc :
      SSet.const (X := (SSet.sdIter k).obj K) z =
        towerLastVertex K k ≫ SSet.const (X := K) z := by
    symm
    exact SSet.comp_const _ _
  rw [hc, towerLastVertex_promote, Category.assoc,
    clientExTowerZeroMapRaw_colimit, SSet.const_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_subordinate_pointed_lift_rel
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    (a : (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}) _⦋0⦌)
    (p : (SSet.exInfinity.obj (TopCat.toSSet.obj X)).PtSimplex
      (n + 1)
      ((SSet.exInfinityUnit.app (TopCat.toSSet.obj X)).app _
        ((AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι.app _ a))) :
    ∃ (q : (SSet.exInfinity.obj
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u})).PtSimplex
        (n + 1)
        ((SSet.exInfinityUnit.app _).app _ a))
      (hbase :
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι).app _
            ((SSet.exInfinityUnit.app _).app _ a) =
          (SSet.exInfinityUnit.app (TopCat.toSSet.obj X)).app _
            ((AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι.app _ a)),
      Nonempty ((SSet.PtSimplex.map
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι) hbase q).RelStruct₀ p) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  let z : B _⦋0⦌ := j.app _ a
  have hbase : ej.app _ ((SSet.exInfinityUnit.app A).app _ a) =
      (SSet.exInfinityUnit.app B).app _ z := by
    have hnat := SSet.exInfinityUnit.naturality j
    exact (congrArg
      (fun f => f.app (Opposite.op ⦋0⦌) a) hnat).symm
  let _ : (SSet.exInfinity.obj B).KanComplex :=
    SSet.exInfinity_kanComplex B
  obtain ⟨k₀, b, hpFactor, hb⟩ :=
    exists_pointed_stageTopAdjunct z p
  obtain ⟨k, q₀, hq₀⟩ := exists_subordinateSubdivision U hU b
  have q₀Face : ∀ i : Fin (n + 2),
      (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫ q₀ =
        SSet.const a := by
    intro i
    apply (cancel_mono (f := j)).mp
    rw [Category.assoc, hq₀]
    rw [geometricAdjunct_face_constant_local n k i b z (hb i)]
    rw [SSet.const_comp]
  let amap : (Δ[n + 1] : SSet.{u}) ⟶ SSet.exInfinity.obj A :=
    sdIterClientHomEquiv k (Δ[n + 1] : SSet.{u}) A q₀ ≫
      colimit.ι (clientExTower A) k
  have amapFace : ∀ i : Fin (n + 2),
      SSet.stdSimplex.δ i ≫ amap =
        SSet.const ((SSet.exInfinityUnit.app A).app _ a) := by
    intro i
    unfold amap
    rw [← Category.assoc, ← sdIterClientHomEquiv_naturality_left,
      q₀Face i, mate_const_colimit_general]
  let q : (SSet.exInfinity.obj A).PtSimplex (n + 1)
      ((SSet.exInfinityUnit.app A).app _ a) :=
    { map := amap
      comm := by
        apply SSet.boundary.hom_ext
        intro i
        simp only [SSet.boundary.ι_ι_assoc,
          SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
        rw [amapFace i] }
  let xmap : (Δ[n + 1] : SSet.{u}) ⟶ B :=
    sSetTopAdj.homEquiv _ _ b
  have xmapFace : ∀ i : Fin (n + 2),
      SSet.stdSimplex.δ i ≫ xmap = SSet.const z := by
    intro i
    unfold xmap
    rw [← sSetTopAdj.homEquiv_naturality_left, hb i,
      sSetTopAdj_homEquiv_const_local, Equiv.symm_apply_apply]
  let bp : B.PtSimplex (n + 1) z :=
    { map := xmap
      comm := by
        apply SSet.boundary.hom_ext
        intro i
        simp only [SSet.boundary.ι_ι_assoc,
          SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
        rw [xmapFace i] }
  let center : (SSet.exInfinity.obj B).PtSimplex (n + 1)
      ((SSet.exInfinityUnit.app B).app _ z) :=
    SSet.PtSimplex.map (SSet.exInfinityUnit.app B) rfl bp
  let image : (SSet.exInfinity.obj B).PtSimplex (n + 1)
      ((SSet.exInfinityUnit.app B).app _ z) :=
    SSet.PtSimplex.map ej hbase q
  let Hlift : SSet.Homotopy
      (SSet.RelativeMorphism.map image)
      (SSet.RelativeMorphism.map center) :=
    smallificationImageInfinityHomotopy U b q₀ hq₀
  have HliftFace : ∀ i : Fin (n + 2),
      (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ Hlift.h =
        SSet.const ((SSet.exInfinityUnit.app B).app _ z) := by
    intro i
    exact smallificationImageInfinityHomotopy_face_constant
      U n k i b q₀ hq₀ z (hb i)
  let HorigRaw := geometricTowerInfinityHomotopy b k₀
  let Horig : SSet.Homotopy
      (SSet.RelativeMorphism.map p)
      (SSet.RelativeMorphism.map center) :=
    { h := HorigRaw.h
      h₀ := by rw [HorigRaw.h₀, hpFactor]; rfl
      h₁ := HorigRaw.h₁
      rel := HorigRaw.rel }
  have HorigFace : ∀ i : Fin (n + 2),
      (SSet.stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ Horig.h =
        SSet.const ((SSet.exInfinityUnit.app B).app _ z) := by
    intro i
    exact geometricTowerInfinityHomotopy_face_constant
      n k₀ i b z (hb i)
  let PHlift : image.Homotopy center :=
    pointedHomotopyOfFaceConstant Hlift HliftFace
  let PHorig : p.Homotopy center :=
    pointedHomotopyOfFaceConstant Horig HorigFace
  exact ⟨q, hbase,
    ⟨PHlift.relStruct₀.trans PHorig.relStruct₀.symm⟩⟩

private theorem subordinateCover_piMap_surjective_at_unit
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    (a : (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}) _⦋0⦌)
    (hbase :
      (SSet.exInfinity.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι).app _
          ((SSet.exInfinityUnit.app _).app _ a) =
        (SSet.exInfinityUnit.app (TopCat.toSSet.obj X)).app _
          ((AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι.app _ a)) :
    Function.Surjective
      (SSet.KanComplex.π.map
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        hbase (n + 1)) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let _ : (SSet.exInfinity.obj A).KanComplex :=
    SSet.exInfinity_kanComplex A
  let _ : (SSet.exInfinity.obj B).KanComplex :=
    SSet.exInfinity_kanComplex B
  intro y
  induction y using SSet.KanComplex.π.rec with
  | mk p =>
      obtain ⟨q, hbase', hrel⟩ :=
        exists_subordinate_pointed_lift_rel U hU n a p
      refine ⟨SSet.KanComplex.π.mk q, ?_⟩
      rw [SSet.KanComplex.π.map_mk,
        SSet.KanComplex.π.mk_eq_mk_iff]
      simpa only using hrel

private theorem piMap_cast_target
    {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X ⟶ Y) (h : f.app _ x = y) (n : ℕ)
    (q : SSet.KanComplex.π n X x) :
    Equiv.cast (congrArg (SSet.KanComplex.π n Y) h)
        (SSet.KanComplex.π.map f rfl n q) =
      SSet.KanComplex.π.map f h n q := by
  subst y
  rfl

private theorem subordinateCover_piMap_surjective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    (x : (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})) _⦋0⦌) :
    Function.Surjective
      (SSet.KanComplex.π.map
        (x := x)
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        rfl (n + 1)) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  obtain ⟨a, ha⟩ := exInfinityUnit_app_zero_surjective A x
  subst x
  have hbase : ej.app _ ((SSet.exInfinityUnit.app A).app _ a) =
      (SSet.exInfinityUnit.app B).app _ (j.app _ a) := by
    have hnat := SSet.exInfinityUnit.naturality j
    exact (congrArg
      (fun f => f.app (Opposite.op ⦋0⦌) a) hnat).symm
  let e :
      SSet.KanComplex.π (n + 1) (SSet.exInfinity.obj B)
          (ej.app _ ((SSet.exInfinityUnit.app A).app _ a)) ≃
        SSet.KanComplex.π (n + 1) (SSet.exInfinity.obj B)
          ((SSet.exInfinityUnit.app B).app _ (j.app _ a)) :=
    Equiv.cast (congrArg
      (SSet.KanComplex.π (n + 1) (SSet.exInfinity.obj B)) hbase)
  have hs := subordinateCover_piMap_surjective_at_unit
    U hU n a hbase
  intro y
  obtain ⟨q, hq⟩ := hs (e y)
  refine ⟨q, e.injective ?_⟩
  calc
    e (SSet.KanComplex.π.map ej rfl (n + 1) q) =
        SSet.KanComplex.π.map ej hbase (n + 1) q :=
      piMap_cast_target ej hbase (n + 1) q
    _ = e y := hq

private theorem clientExIter_map_mono
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Mono ((clientExIter k).map f) := by
  induction k with
  | zero =>
      change Mono f
      infer_instance
  | succ k ih =>
      rw [clientExIter_succ_map]
      infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem clientExInfinity_map_mono
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.exInfinity.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  induction d using Opposite.rec
  rename_i d
  rw [mono_iff_injective]
  intro x y hxy
  let xmap : SSet.stdSimplex.obj d ⟶ SSet.exInfinity.obj X :=
    SSet.yonedaEquiv.symm x
  let ymap : SSet.stdSimplex.obj d ⟶ SSet.exInfinity.obj X :=
    SSet.yonedaEquiv.symm y
  have hmaps : xmap ≫ SSet.exInfinity.map f =
      ymap ≫ SSet.exInfinity.map f := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, xmap, ymap,
      Equiv.apply_symm_apply] using hxy
  obtain ⟨i, p, hp⟩ := clientExists_exTower_factor X
    (SSet.stdSimplex.obj d) xmap
  obtain ⟨j, q, hq⟩ := clientExists_exTower_factor X
    (SSet.stdSimplex.obj d) ymap
  let pf : SSet.stdSimplex.obj d ⟶
      (clientExTower Y).obj (CategoryTheory.AsSmall.down.obj i) :=
    p ≫ (clientExTowerFunctor.map f).app
      (CategoryTheory.AsSmall.down.obj i)
  let qf : SSet.stdSimplex.obj d ⟶
      (clientExTower Y).obj (CategoryTheory.AsSmall.down.obj j) :=
    q ≫ (clientExTowerFunctor.map f).app
      (CategoryTheory.AsSmall.down.obj j)
  have hpqColimit :
      pf ≫ colimit.ι (clientExTower Y)
          (CategoryTheory.AsSmall.down.obj i) =
        qf ≫ colimit.ι (clientExTower Y)
          (CategoryTheory.AsSmall.down.obj j) := by
    calc
      pf ≫ colimit.ι (clientExTower Y)
          (CategoryTheory.AsSmall.down.obj i) =
        (p ≫ colimit.ι (clientExTower X)
            (CategoryTheory.AsSmall.down.obj i)) ≫
          SSet.exInfinity.map f := by
            dsimp only [pf]
            simp only [Category.assoc]
            rw [clientExTower_colimit_naturality]
      _ = xmap ≫ SSet.exInfinity.map f := by rw [hp]
      _ = ymap ≫ SSet.exInfinity.map f := hmaps
      _ = (q ≫ colimit.ι (clientExTower X)
            (CategoryTheory.AsSmall.down.obj j)) ≫
          SSet.exInfinity.map f := by rw [hq]
      _ = qf ≫ colimit.ι (clientExTower Y)
          (CategoryTheory.AsSmall.down.obj j) := by
            dsimp only [qf]
            simp only [Category.assoc]
            rw [clientExTower_colimit_naturality]
  obtain ⟨k, ai, aj, hpq⟩ := clientExists_exTower_later_eq Y
    (SSet.stdSimplex.obj d) pf qf hpqColimit
  let pi := p ≫ (clientExTower X).map
    (CategoryTheory.AsSmall.down.map ai)
  let qj := q ≫ (clientExTower X).map
    (CategoryTheory.AsSmall.down.map aj)
  let fk := (clientExTowerFunctor.map f).app
    (CategoryTheory.AsSmall.down.obj k)
  have _ : Mono fk := by
    change Mono ((clientExIter
      (CategoryTheory.AsSmall.down.obj k)).map f)
    exact clientExIter_map_mono f _
  have hpqA : pi = qj := by
    apply (cancel_mono (f := fk)).mp
    calc
      pi ≫ fk = p ≫
          ((clientExTower X).map
              (CategoryTheory.AsSmall.down.map ai) ≫ fk) := by
            simp only [pi, Category.assoc]
      _ = p ≫ ((clientExTowerFunctor.map f).app
            (CategoryTheory.AsSmall.down.obj i) ≫
          (clientExTower Y).map
            (CategoryTheory.AsSmall.down.map ai)) := by
        rw [(clientExTowerFunctor.map f).naturality]
      _ = pf ≫ (clientExTower Y).map
          (CategoryTheory.AsSmall.down.map ai) := by
            simp only [pf, Category.assoc]
      _ = qf ≫ (clientExTower Y).map
          (CategoryTheory.AsSmall.down.map aj) := hpq
      _ = q ≫ ((clientExTowerFunctor.map f).app
            (CategoryTheory.AsSmall.down.obj j) ≫
          (clientExTower Y).map
            (CategoryTheory.AsSmall.down.map aj)) := by
            simp only [qf, Category.assoc]
      _ = q ≫ ((clientExTower X).map
            (CategoryTheory.AsSmall.down.map aj) ≫ fk) := by
        rw [(clientExTowerFunctor.map f).naturality]
      _ = qj ≫ fk := by simp only [qj, Category.assoc]
  apply SSet.yonedaEquiv.symm.injective
  calc
    SSet.yonedaEquiv.symm x = xmap := rfl
    _ = p ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj i) := hp.symm
    _ = pi ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj k) := by
      dsimp only [pi]
      simp only [Category.assoc]
      rw [colimit.w]
    _ = qj ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj k) := by rw [hpqA]
    _ = q ≫ colimit.ι (clientExTower X)
        (CategoryTheory.AsSmall.down.obj j) := by
      dsimp only [qj]
      simp only [Category.assoc]
      rw [colimit.w]
    _ = ymap := hq
    _ = SSet.yonedaEquiv.symm y := rfl

private theorem exists_relStruct_source_boundary
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    {x : A _⦋0⦌} {y : B _⦋0⦌}
    (hbase : f.app _ x = y) (n : ℕ)
    {p q : A.PtSimplex (n + 1) x}
    (r : (SSet.PtSimplex.map f hbase p).RelStruct₀
      (SSet.PtSimplex.map f hbase q)) :
    ∃ b : (SSet.boundary (n + 2) : SSet.{u}) ⟶ A,
      b ≫ f = (SSet.boundary (n + 2)).ι ≫ r.map := by
  let faces : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ A) :=
    Fin.cases (SSet.RelativeMorphism.map p)
      (Fin.cases (SSet.RelativeMorphism.map q)
        (fun _ => SSet.const x))
  have faces_map (i : Fin (n + 3)) :
      faces i ≫ f = SSet.stdSimplex.δ i ≫ r.map := by
    induction i using Fin.cases with
    | zero =>
        change SSet.RelativeMorphism.map p ≫ f =
          SSet.stdSimplex.δ 0 ≫ r.map
        exact r.δ_castSucc_map.symm
    | succ i =>
        induction i using Fin.cases with
        | zero =>
            change SSet.RelativeMorphism.map q ≫ f =
              SSet.stdSimplex.δ 1 ≫ r.map
            exact r.δ_succ_map.symm
        | succ i =>
            have hi : (0 : Fin (n + 2)).succ < i.succ.succ := by
              change 1 < i.val + 2
              omega
            simp only [faces, Fin.cases_succ, SSet.const_comp, hbase]
            exact (r.δ_map_of_gt i.succ.succ hi).symm
  have hf : SSet.boundary.IsCompatible faces := by
    rw [SSet.boundary.isCompatible_succ_iff]
    intro i j hij
    apply (cancel_mono (f := f)).mp
    simp only [Category.assoc, faces_map]
    rw [← SSet.stdSimplex.facePairComplIso_hom_ι'_assoc i j hij,
      ← SSet.stdSimplex.facePairComplIso_hom_ι_assoc i j hij]
  refine ⟨hf.desc, ?_⟩
  apply SSet.boundary.hom_ext
  intro i
  calc
    SSet.boundary.ι i ≫ (hf.desc ≫ f) =
        (SSet.boundary.ι i ≫ hf.desc) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = faces i ≫ f := by rw [hf.ι_desc]
    _ = SSet.stdSimplex.δ i ≫ r.map := faces_map i
    _ = (SSet.boundary.ι i ≫ (SSet.boundary (n + 2)).ι) ≫
        r.map := by rw [SSet.boundary.ι_ι]
    _ = SSet.boundary.ι i ≫
        ((SSet.boundary (n + 2)).ι ≫ r.map) :=
      Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_relStruct_common_stage
    {A B : SSet.{u}} (f : A ⟶ B)
    (n : ℕ) (rmap : (Δ[n + 2] : SSet.{u}) ⟶
      SSet.exInfinity.obj B)
    (b : (SSet.boundary (n + 2) : SSet.{u}) ⟶
      SSet.exInfinity.obj A)
    (hb : b ≫ SSet.exInfinity.map f =
      (SSet.boundary (n + 2)).ι ≫ rmap) :
    ∃ (k : CategoryTheory.AsSmall.{u} ℕ)
      (a : (SSet.boundary (n + 2) : SSet.{u}) ⟶
        (clientExTower A).obj (CategoryTheory.AsSmall.down.obj k))
      (r : (Δ[n + 2] : SSet.{u}) ⟶
        (clientExTower B).obj (CategoryTheory.AsSmall.down.obj k)),
      a ≫ colimit.ι (clientExTower A)
          (CategoryTheory.AsSmall.down.obj k) = b ∧
        r ≫ colimit.ι (clientExTower B)
          (CategoryTheory.AsSmall.down.obj k) = rmap ∧
        (SSet.boundary (n + 2)).ι ≫ r =
          a ≫ (clientExTowerFunctor.map f).app
            (CategoryTheory.AsSmall.down.obj k) := by
  obtain ⟨ia, a₀, ha₀⟩ := clientExists_exTower_factor A
    (SSet.boundary (n + 2) : SSet.{u}) b
  obtain ⟨ir, r₀, hr₀⟩ := clientExists_exTower_factor B
    (Δ[n + 2] : SSet.{u}) rmap
  let a₀f : (SSet.boundary (n + 2) : SSet.{u}) ⟶
      (clientExTower B).obj (CategoryTheory.AsSmall.down.obj ia) :=
    a₀ ≫ (clientExTowerFunctor.map f).app
      (CategoryTheory.AsSmall.down.obj ia)
  have hcolimit :
      ((SSet.boundary (n + 2)).ι ≫ r₀) ≫
          colimit.ι (clientExTower B)
            (CategoryTheory.AsSmall.down.obj ir) =
        a₀f ≫ colimit.ι (clientExTower B)
          (CategoryTheory.AsSmall.down.obj ia) := by
    calc
      ((SSet.boundary (n + 2)).ι ≫ r₀) ≫
          colimit.ι (clientExTower B)
            (CategoryTheory.AsSmall.down.obj ir) =
        (SSet.boundary (n + 2)).ι ≫ rmap := by
          rw [Category.assoc, hr₀]
      _ = b ≫ SSet.exInfinity.map f := hb.symm
      _ = (a₀ ≫ colimit.ι (clientExTower A)
            (CategoryTheory.AsSmall.down.obj ia)) ≫
          SSet.exInfinity.map f := by rw [ha₀]
      _ = a₀f ≫ colimit.ι (clientExTower B)
          (CategoryTheory.AsSmall.down.obj ia) := by
        dsimp only [a₀f]
        simp only [Category.assoc]
        rw [clientExTower_colimit_naturality]
  obtain ⟨k, ar, aa, hstage⟩ :=
    clientExists_exTower_later_eq B
      (SSet.boundary (n + 2) : SSet.{u})
      ((SSet.boundary (n + 2)).ι ≫ r₀) a₀f hcolimit
  let a := a₀ ≫ (clientExTower A).map
    (CategoryTheory.AsSmall.down.map aa)
  let r := r₀ ≫ (clientExTower B).map
    (CategoryTheory.AsSmall.down.map ar)
  refine ⟨k, a, r, ?_, ?_, ?_⟩
  · calc
      a ≫ colimit.ι (clientExTower A)
          (CategoryTheory.AsSmall.down.obj k) =
        a₀ ≫ ((clientExTower A).map
            (CategoryTheory.AsSmall.down.map aa) ≫
          colimit.ι (clientExTower A)
            (CategoryTheory.AsSmall.down.obj k)) := by
              simp only [a, Category.assoc]
      _ = a₀ ≫ colimit.ι (clientExTower A)
          (CategoryTheory.AsSmall.down.obj ia) := by rw [colimit.w]
      _ = b := ha₀
  · calc
      r ≫ colimit.ι (clientExTower B)
          (CategoryTheory.AsSmall.down.obj k) =
        r₀ ≫ ((clientExTower B).map
            (CategoryTheory.AsSmall.down.map ar) ≫
          colimit.ι (clientExTower B)
            (CategoryTheory.AsSmall.down.obj k)) := by
              simp only [r, Category.assoc]
      _ = r₀ ≫ colimit.ι (clientExTower B)
          (CategoryTheory.AsSmall.down.obj ir) := by rw [colimit.w]
      _ = rmap := hr₀
  · calc
      (SSet.boundary (n + 2)).ι ≫ r =
        ((SSet.boundary (n + 2)).ι ≫ r₀) ≫
          (clientExTower B).map
            (CategoryTheory.AsSmall.down.map ar) := by
              simp only [r, Category.assoc]
      _ = a₀f ≫ (clientExTower B).map
          (CategoryTheory.AsSmall.down.map aa) := hstage
      _ = a₀ ≫ ((clientExTowerFunctor.map f).app
            (CategoryTheory.AsSmall.down.obj ia) ≫
          (clientExTower B).map
            (CategoryTheory.AsSmall.down.map aa)) := by
              simp only [a₀f, Category.assoc]
      _ = a₀ ≫ ((clientExTower A).map
            (CategoryTheory.AsSmall.down.map aa) ≫
          (clientExTowerFunctor.map f).app
            (CategoryTheory.AsSmall.down.obj k)) := by
        rw [(clientExTowerFunctor.map f).naturality]
      _ = a ≫ (clientExTowerFunctor.map f).app
          (CategoryTheory.AsSmall.down.obj k) := by
            simp only [a, Category.assoc]

private theorem exists_extension_of_boundary_homotopy
    {Z : SSet.{u}} [Z.KanComplex] (N : ℕ)
    (g : (Δ[N] : SSet.{u}) ⟶ Z)
    (a : (SSet.boundary N : SSet.{u}) ⟶ Z)
    (H : SSet.Homotopy ((SSet.boundary N).ι ≫ g) a) :
    ∃ (g' : (Δ[N] : SSet.{u}) ⟶ Z)
      (H' : SSet.Homotopy g g'),
      (SSet.boundary N).ι ≫ g' = a ∧
        ((SSet.boundary N).ι ▷ (Δ[1] : SSet.{u})) ≫ H'.h = H.h := by
  let t : Z ⟶ (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.from Z
  let _ : HomotopicalAlgebra.Fibration t := by
    exact (HomotopicalAlgebra.isFibrant_iff_of_isTerminal t
      SSet.stdSimplex.isTerminalObj₀).mp (by infer_instance)
  let hB : (Δ[N] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.from _
  obtain ⟨ψ, hψ₀, hψbd, _⟩ :=
    SSet.homotopy_extension_property₀
      (SSet.boundary N).ι t H.h g H.h₀.symm hB
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  let g' : (Δ[N] : SSet.{u}) ⟶ Z := SSet.ι₁ ≫ ψ
  let H' : SSet.Homotopy g g' :=
    { h := ψ
      h₀ := hψ₀
      h₁ := rfl
      rel := by ext _ ⟨⟨_, h⟩, _⟩; cases h }
  refine ⟨g', H', ?_, ?_⟩
  · calc
      (SSet.boundary N).ι ≫ g' =
          SSet.ι₁ ≫
            (((SSet.boundary N).ι ▷ (Δ[1] : SSet.{u})) ≫ ψ) := by
              simp [g']
      _ = SSet.ι₁ ≫ H.h := by rw [hψbd]
      _ = a := H.h₁
  · exact hψbd

private theorem subordinateSimplex_global_range
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) {d : ℕ}
    (t : (Δ[d] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})) :
    ∃ i, Set.range
        ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
          (t ≫ (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)).hom ⊆
      (U i : Set X) := by
  let A := AlgebraicTopology.subordinateCover
    (X := X) (fun i => (U i : Set X))
  let j : (A : SSet.{u}) ⟶ TopCat.toSSet.obj X := A.ι
  let s : (A : SSet.{u}) _⦋d⦌ := SSet.yonedaEquiv t
  have hs := s.property
  change s.val ∈ A.obj (Opposite.op ⦋d⦌) at hs
  simp only [A, AlgebraicTopology.subordinateCover,
    Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨i, hi⟩ := hs
  refine ⟨i, ?_⟩
  change Set.range
      ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
        (t ≫ j)).hom ⊆ (U i : Set X)
  intro y
  rintro ⟨z, rfl⟩
  let q := (SimplexCategory.toTopHomeo.{u} ⦋d⦌) z
  have heval := sSetTopAdj_homEquiv_symm_apply (t ≫ j)
    (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) q
  have hinput :
      SSet.toTop.map (SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q) = z := by
    simp [q]
  have hcomponent :
      ((t ≫ j).app (Opposite.op ⦋d⦌))
          (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))) =
        j.app _ s := by
    change SSet.yonedaEquiv (t ≫ j) = _
    rw [SSet.yonedaEquiv_comp]
  apply hi
  refine ⟨q, ?_⟩
  calc
    X.toSSetObjEquiv _ s.val q =
        X.toSSetObjEquiv _ (j.app _ s) q := rfl
    _ = X.toSSetObjEquiv _
        (((t ≫ j).app _)
          (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u})))) q := by
            rw [hcomponent]
    _ = ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
        (t ≫ j))
          (SSet.toTop.map (SSet.yonedaEquiv.symm
            (SSet.yonedaEquiv (𝟙 (Δ[d] : SSet.{u}))))
              ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) :=
      heval.symm
    _ = ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
        (t ≫ j)) z := by rw [hinput]

private theorem range_postcomp_toSSetMap_le_subordinateCover
    {D X : TopCat.{u}} {K : SSet.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (g : K ⟶ TopCat.toSSet.obj D) (b : D ⟶ X)
    (i : ι) (hi : Set.range b ⊆ (U i : Set X)) :
    SSet.Subcomplex.range (g ≫ TopCat.toSSet.map b) ≤
      AlgebraicTopology.subordinateCover (fun i => (U i : Set X)) := by
  intro n y hy
  obtain ⟨z, rfl⟩ := hy
  apply (le_iSup (fun i => AlgebraicTopology.subordinateSet
    (X := X) (U i : Set X)) i)
  change Set.range (X.toSSetObjEquiv _
    ((g ≫ TopCat.toSSet.map b).app _ z)) ⊆ (U i : Set X)
  intro y
  rintro ⟨q, rfl⟩
  change X.toSSetObjEquiv _
    ((TopCat.toSSet.map b).app _ (g.app _ z)) q ∈ (U i : Set X)
  change b (D.toSSetObjEquiv _ (g.app _ z) q) ∈ (U i : Set X)
  apply hi
  exact ⟨D.toSSetObjEquiv _ (g.app _ z) q, rfl⟩

private theorem exists_subordinate_geometric_lift_of_simplex
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) {d : ℕ}
    (t : (Δ[d] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    ∃ q : (SSet.sdIter k).obj (Δ[d] : SSet.{u}) ⟶
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u}),
      q ≫ (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
        geometricSubdivisionAdjunct
          ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
            (t ≫ (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k := by
  let b := (sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
    (t ≫ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι)
  obtain ⟨i, hi⟩ := subordinateSimplex_global_range U t
  apply exists_subordinateLift_of_range U b
  intro e cell
  refine ⟨i, ?_⟩
  intro y
  rintro ⟨z, rfl⟩
  apply hi
  exact ⟨(SSet.toTopSdIterIso (Δ[d] : SSet.{u}) k).hom
    (SSet.toTop.map cell z), rfl⟩

private theorem geometricTowerAdjunctHomotopy_factor
    {X : TopCat.{u}} {d : ℕ}
    (b : SSet.toTop.obj (Δ[d] : SSet.{u}) ⟶ X) (k : ℕ) :
    (geometricTowerAdjunctHomotopy b k).h =
      (geometricTowerAdjunctHomotopy
        (𝟙 (SSet.toTop.obj (Δ[d] : SSet.{u}))) k).h ≫
        TopCat.toSSet.map b := by
  rfl

private theorem exists_subordinate_geometric_tower_homotopy_of_simplex
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) {d : ℕ}
    (t : (Δ[d] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    ∃ (q : (SSet.sdIter k).obj (Δ[d] : SSet.{u}) ⟶
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X)) : SSet.{u}))
        (H : SSet.Homotopy q (towerLastVertex (Δ[d] : SSet.{u}) k ≫ t)),
      q ≫ (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
        geometricSubdivisionAdjunct
          ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
            (t ≫ (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k ∧
      H.h ≫ (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
        (geometricTowerAdjunctHomotopy
          ((sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm
            (t ≫ (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k).h := by
  let A := AlgebraicTopology.subordinateCover
    (X := X) (fun i => (U i : Set X))
  let j : (A : SSet.{u}) ⟶ TopCat.toSSet.obj X := A.ι
  let b : SSet.toTop.obj (Δ[d] : SSet.{u}) ⟶ X :=
    (sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X).symm (t ≫ j)
  obtain ⟨q, hq⟩ := exists_subordinate_geometric_lift_of_simplex U t k
  obtain ⟨i, hi⟩ := subordinateSimplex_global_range U t
  let hUniversal := (geometricTowerAdjunctHomotopy
    (𝟙 (SSet.toTop.obj (Δ[d] : SSet.{u}))) k).h
  have hRangeUniversal :
      SSet.Subcomplex.range
          (hUniversal ≫ TopCat.toSSet.map b) ≤ A :=
    range_postcomp_toSSetMap_le_subordinateCover U hUniversal b i hi
  have hFactor :
      hUniversal ≫ TopCat.toSSet.map b =
        (geometricTowerAdjunctHomotopy b k).h := by
    symm
    exact geometricTowerAdjunctHomotopy_factor b k
  have hRange :
      SSet.Subcomplex.range (geometricTowerAdjunctHomotopy b k).h ≤ A := by
    rw [← hFactor]
    exact hRangeUniversal
  let hA : (SSet.sdIter k).obj (Δ[d] : SSet.{u}) ⊗ Δ[1] ⟶ A :=
    SSet.Subcomplex.lift (geometricTowerAdjunctHomotopy b k).h hRange
  have hAj : hA ≫ j = (geometricTowerAdjunctHomotopy b k).h := by
    exact SSet.Subcomplex.lift_ι _ _
  have hzero : SSet.ι₀ ≫ hA = q := by
    apply (cancel_mono j).1
    rw [Category.assoc, hAj,
      (geometricTowerAdjunctHomotopy b k).h₀]
    change geometricSubdivisionAdjunct b k = q ≫ j
    exact hq.symm
  have hone : SSet.ι₁ ≫ hA = towerLastVertex (Δ[d] : SSet.{u}) k ≫ t := by
    apply (cancel_mono j).1
    rw [Category.assoc, hAj,
      (geometricTowerAdjunctHomotopy b k).h₁]
    change towerLastVertex (Δ[d] : SSet.{u}) k ≫
        (sSetTopAdj.homEquiv (Δ[d] : SSet.{u}) X) b =
      (towerLastVertex (Δ[d] : SSet.{u}) k ≫ t) ≫ j
    rw [Category.assoc]
    congr 1
    exact (sSetTopAdj.homEquiv _ _).apply_symm_apply (t ≫ j)
  let H : SSet.Homotopy q
      (towerLastVertex (Δ[d] : SSet.{u}) k ≫ t) :=
    { h := hA
      h₀ := hzero
      h₁ := hone
      rel := by
        ext n ⟨⟨x, hx⟩, s⟩
        cases hx }
  refine ⟨q, H, ?_, ?_⟩
  · exact hq
  · exact hAj

private theorem subordinate_geometric_tower_homotopy_overlap
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono (SSet.stdSimplex.{u}.map f)]
    (t : (Δ[n] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ)
    {qₙ : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})}
    {qₘ : (SSet.sdIter k).obj (Δ[m] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})}
    (Hₙ : SSet.Homotopy qₙ
      (towerLastVertex (Δ[n] : SSet.{u}) k ≫ t))
    (Hₘ : SSet.Homotopy qₘ
      (towerLastVertex (Δ[m] : SSet.{u}) k ≫
        SSet.stdSimplex.{u}.map f ≫ t))
    (hHₙ : Hₙ.h ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      (geometricTowerAdjunctHomotopy
        ((sSetTopAdj.homEquiv (Δ[n] : SSet.{u}) X).symm
          (t ≫ (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)) k).h)
    (hHₘ : Hₘ.h ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      (geometricTowerAdjunctHomotopy
        ((sSetTopAdj.homEquiv (Δ[m] : SSet.{u}) X).symm
          ((SSet.stdSimplex.{u}.map f ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k).h) :
    ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f) ▷
        (Δ[1] : SSet.{u})) ≫ Hₙ.h = Hₘ.h := by
  apply (cancel_mono (AlgebraicTopology.subordinateCover
    (fun i => (U i : Set X))).ι).mp
  rw [Category.assoc, hHₙ, hHₘ,
    geometricTowerAdjunctHomotopy_naturality_of_mono]
  have hb :
      (sSetTopAdj.homEquiv (Δ[m] : SSet.{u}) X).symm
          ((SSet.stdSimplex.{u}.map f ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι) =
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) ≫
          (sSetTopAdj.homEquiv (Δ[n] : SSet.{u}) X).symm
            (t ≫ (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι) := by
    rw [Category.assoc,
      sSetTopAdj.homEquiv_naturality_left_symm]
  rw [hb]

private theorem subordinate_geometric_tower_map_overlap
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono (SSet.stdSimplex.{u}.map f)]
    (t : (Δ[n] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ)
    (hₙ : (SSet.sdIter k).obj (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (hₘ : (SSet.sdIter k).obj (Δ[m] : SSet.{u}) ⊗ Δ[1] ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (hhₙ : hₙ ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      (geometricTowerAdjunctHomotopy
        ((sSetTopAdj.homEquiv (Δ[n] : SSet.{u}) X).symm
          (t ≫ (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)) k).h)
    (hhₘ : hₘ ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      (geometricTowerAdjunctHomotopy
        ((sSetTopAdj.homEquiv (Δ[m] : SSet.{u}) X).symm
          ((SSet.stdSimplex.{u}.map f ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k).h) :
    ((SSet.sdIter k).map (SSet.stdSimplex.{u}.map f) ▷
        (Δ[1] : SSet.{u})) ≫ hₙ = hₘ := by
  apply (cancel_mono (AlgebraicTopology.subordinateCover
    (fun i => (U i : Set X))).ι).mp
  rw [Category.assoc, hhₙ, hhₘ,
    geometricTowerAdjunctHomotopy_naturality_of_mono]
  have hb :
      (sSetTopAdj.homEquiv (Δ[m] : SSet.{u}) X).symm
          ((SSet.stdSimplex.{u}.map f ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι) =
        SSet.toTop.map (SSet.stdSimplex.{u}.map f) ≫
          (sSetTopAdj.homEquiv (Δ[n] : SSet.{u}) X).symm
            (t ≫ (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι) := by
    rw [Category.assoc,
      sSetTopAdj.homEquiv_naturality_left_symm]
  rw [hb]

@[nolint unusedArguments] -- Dropping it would ripple through the private cell API below.
private noncomputable def nonsingularCellIncl
    (K : SSet.{u}) [K.Nonsingular] (s : K.N) :
    (Δ[s.dim] : SSet.{u}) ⟶ K :=
  SSet.yonedaEquiv.symm s.simplex

private theorem nonsingularCellIncl_naturality
    (K : SSet.{u}) [K.Nonsingular]
    {s s' : K.N} (φ : s ⟶ s') :
    SSet.stdSimplex.{u}.map (SSet.N.monoOfLE (leOfHom φ)) ≫
        nonsingularCellIncl K s' =
      nonsingularCellIncl K s :=
  SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom φ)

private noncomputable def subordinateCellGeometricLift
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) (s : K.N) :
    (SSet.sdIter k).obj (Δ[s.dim] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}) :=
  (exists_subordinate_geometric_tower_homotopy_of_simplex U
    (nonsingularCellIncl K s ≫ t) k).choose

private noncomputable def subordinateCellGeometricHomotopy
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) (s : K.N) :
    SSet.Homotopy (subordinateCellGeometricLift U t k s)
      (towerLastVertex (Δ[s.dim] : SSet.{u}) k ≫
        nonsingularCellIncl K s ≫ t) :=
  (exists_subordinate_geometric_tower_homotopy_of_simplex U
    (nonsingularCellIncl K s ≫ t) k).choose_spec.choose

private theorem subordinateCellGeometricHomotopy_postcomp
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) (s : K.N) :
    (subordinateCellGeometricHomotopy U t k s).h ≫
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
      (geometricTowerAdjunctHomotopy
        ((sSetTopAdj.homEquiv (Δ[s.dim] : SSet.{u}) X).symm
          ((nonsingularCellIncl K s ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k).h :=
  (exists_subordinate_geometric_tower_homotopy_of_simplex U
    (nonsingularCellIncl K s ≫ t) k).choose_spec.choose_spec.2

private theorem subordinateCellGeometricHomotopy_naturality
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) {s s' : K.N} (φ : s ⟶ s') :
    ((SSet.sdIter k).map (K.functorN'.map φ) ▷
        (Δ[1] : SSet.{u})) ≫
        (subordinateCellGeometricHomotopy U t k s').h =
      (subordinateCellGeometricHomotopy U t k s).h := by
  let f : ⦋s.dim⦌ ⟶ ⦋s'.dim⦌ := SSet.N.monoOfLE (leOfHom φ)
  have hmap : K.functorN'.map φ = SSet.stdSimplex.{u}.map f := rfl
  let _ : Mono f := by dsimp [f]; infer_instance
  let _ : Mono (SSet.stdSimplex.{u}.map f) := stdSimplex_map_mono f
  have hw :
      SSet.stdSimplex.{u}.map f ≫ nonsingularCellIncl K s' =
        nonsingularCellIncl K s :=
    nonsingularCellIncl_naturality K φ
  have ht :
      SSet.stdSimplex.{u}.map f ≫ (nonsingularCellIncl K s' ≫ t) =
        nonsingularCellIncl K s ≫ t := by
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ t) hw)
  rw [hmap]
  apply subordinate_geometric_tower_map_overlap U f
    (nonsingularCellIncl K s' ≫ t) k
  · exact subordinateCellGeometricHomotopy_postcomp U t k s'
  · rw [ht]
    exact subordinateCellGeometricHomotopy_postcomp U t k s

private noncomputable def subordinateCellHomotopyCocone
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    Cocone (K.functorN' ⋙ SSet.sdIter k ⋙
      MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) where
  pt := AlgebraicTopology.subordinateCover
    (X := X) (fun i => (U i : Set X))
  ι :=
    { app := fun s => (subordinateCellGeometricHomotopy U t k s).h
      naturality := fun _ _ φ =>
        subordinateCellGeometricHomotopy_naturality U t k φ }

set_option backward.isDefEq.respectTransparency false in
private theorem sdIter_nonsingularCellIncl_naturality
    (K : SSet.{u}) [K.Nonsingular] (k : ℕ)
    {s s' : K.N} (φ : s ⟶ s') :
    (SSet.sdIter k).map
        (SSet.stdSimplex.{u}.map
          (SSet.N.monoOfLE (leOfHom φ))) ≫
        (SSet.sdIter k).map (nonsingularCellIncl K s') =
      (SSet.sdIter k).map (nonsingularCellIncl K s) := by
  rw [← (SSet.sdIter k).map_comp]
  rw [nonsingularCellIncl_naturality K φ]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sdIterCellCocone
    (K : SSet.{u}) [K.Nonsingular] (k : ℕ) :
    Cocone (K.functorN' ⋙ SSet.sdIter k) where
  pt := (SSet.sdIter k).obj K
  ι :=
    { app := fun s => (SSet.sdIter k).map (nonsingularCellIncl K s)
      naturality := fun {s s'} φ => by
        dsimp [SSet.functorN', SSet.N.toSemiSimplexCategory]
        rw [Category.comp_id,
          SemiSimplexCategory.toSimplexCategory_map_homOfMono]
        exact sdIter_nonsingularCellIncl_naturality K k φ }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sdIterCellCylinderCocone
    (K : SSet.{u}) [K.Nonsingular] (k : ℕ) :
    Cocone (K.functorN' ⋙ SSet.sdIter k ⋙
      MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) where
  pt := (SSet.sdIter k).obj K ⊗ Δ[1]
  ι :=
    { app := fun s => (SSet.sdIter k).map (nonsingularCellIncl K s) ▷
        (Δ[1] : SSet.{u})
      naturality := fun {s s'} φ => by
        have h := congrArg (fun q => q ▷ (Δ[1] : SSet.{u}))
          (sdIter_nonsingularCellIncl_naturality K k φ)
        dsimp [SSet.functorN', SSet.N.toSemiSimplexCategory]
        rw [Category.comp_id,
          SemiSimplexCategory.toSimplexCategory_map_homOfMono]
        simpa only [MonoidalCategory.comp_whiskerRight] using h }

private noncomputable def isColimitSdIterCellCylinder
    (K : SSet.{u}) [K.Nonsingular] (k : ℕ) :
    IsColimit (sdIterCellCylinderCocone K k) := by
  change IsColimit
    ((MonoidalCategory.tensorRight (Δ[1] : SSet.{u})).mapCocone
      ((SSet.sdIter k).mapCocone K.coconeN'))
  exact isColimitOfPreserves
    (MonoidalCategory.tensorRight (Δ[1] : SSet.{u}))
    (by
      letI : PreservesColimitsOfSize (SSet.sdIter k) :=
        (sdIterAdjunction k).leftAdjoint_preservesColimits
      exact isColimitOfPreserves (SSet.sdIter k) K.isColimitCoconeN')

private noncomputable def isColimitSdIterCells
    (K : SSet.{u}) [K.Nonsingular] (k : ℕ) :
    IsColimit (sdIterCellCocone K k) := by
  change IsColimit ((SSet.sdIter k).mapCocone K.coconeN')
  letI : PreservesColimitsOfSize (SSet.sdIter k) :=
    (sdIterAdjunction k).leftAdjoint_preservesColimits
  exact isColimitOfPreserves (SSet.sdIter k) K.isColimitCoconeN'

private noncomputable def subordinateBoundaryGeometricTowerHomotopyMap
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    (SSet.sdIter k).obj K ⊗ Δ[1] ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}) :=
  (isColimitSdIterCellCylinder K k).desc
    (subordinateCellHomotopyCocone U t k)

private theorem subordinateBoundaryGeometricTowerHomotopyMap_cell
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) (s : K.N) :
    ((SSet.sdIter k).map (nonsingularCellIncl K s) ▷
        (Δ[1] : SSet.{u})) ≫
        subordinateBoundaryGeometricTowerHomotopyMap U t k =
      (subordinateCellGeometricHomotopy U t k s).h := by
  exact (isColimitSdIterCellCylinder K k).fac
    (subordinateCellHomotopyCocone U t k) s

set_option backward.isDefEq.respectTransparency false in
private theorem subordinateBoundaryGeometricTowerHomotopyMap_one
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    SSet.ι₁ ≫ subordinateBoundaryGeometricTowerHomotopyMap U t k =
      towerLastVertex K k ≫ t := by
  apply (isColimitSdIterCells K k).hom_ext
  intro s
  change (SSet.sdIter k).map (nonsingularCellIncl K s) ≫
      (SSet.ι₁ ≫ subordinateBoundaryGeometricTowerHomotopyMap U t k) =
    (SSet.sdIter k).map (nonsingularCellIncl K s) ≫
      (towerLastVertex K k ≫ t)
  rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
    subordinateBoundaryGeometricTowerHomotopyMap_cell,
    (subordinateCellGeometricHomotopy U t k s).h₁]
  exact (congrArg (fun q => q ≫ t)
    (towerLastVertex_naturality (nonsingularCellIncl K s) k)).symm

private noncomputable def subordinateBoundaryGeometricLift
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    (SSet.sdIter k).obj K ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}) :=
  SSet.ι₀ ≫ subordinateBoundaryGeometricTowerHomotopyMap U t k

private noncomputable def subordinateBoundaryGeometricTowerHomotopy
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    SSet.Homotopy (subordinateBoundaryGeometricLift U t k)
      (towerLastVertex K k ≫ t) where
  h := subordinateBoundaryGeometricTowerHomotopyMap U t k
  h₀ := rfl
  h₁ := subordinateBoundaryGeometricTowerHomotopyMap_one U t k
  rel := by
    ext n ⟨⟨x, hx⟩, s⟩
    cases hx

private noncomputable def clientExIterCompIso (a b : ℕ) :
    clientExIter a ⋙ clientExIter b ≅ clientExIter (a + b) := by
  induction b with
  | zero =>
      change clientExIter a ⋙ 𝟭 _ ≅ clientExIter a
      exact Functor.rightUnitor (clientExIter a)
  | succ b ih =>
      simpa only [clientExIter, Nat.add_succ] using
        (Functor.associator (clientExIter a) (clientExIter b) SSet.ex).symm ≪≫
          Functor.isoWhiskerRight ih SSet.ex

private noncomputable def doubleMateToInfinity
    {K A : SSet.{u}} (k l : ℕ)
    (q : (SSet.sdIter l).obj ((SSet.sdIter k).obj K) ⟶ A) :
    K ⟶ colimit (clientExTower A) :=
  sdIterClientHomEquiv k K ((clientExIter l).obj A)
      (sdIterClientHomEquiv l ((SSet.sdIter k).obj K) A q) ≫
    ((clientExIterCompIso l k).app A).hom ≫
    colimit.ι (clientExTower A) (l + k)

private noncomputable def doubleMateHomotopyToInfinity
    {K A : SSet.{u}} {k l : ℕ}
    {q q' : (SSet.sdIter l).obj ((SSet.sdIter k).obj K) ⟶ A}
    (H : SSet.Homotopy q q') :
    SSet.Homotopy (doubleMateToInfinity k l q)
      (doubleMateToInfinity k l q') := by
  let H₁ := sdIterMateHomotopy H
  let H₂ := sdIterMateHomotopy H₁
  let H₃ := homotopyPostcomp H₂ ((clientExIterCompIso l k).app A).hom
  let H₄ := homotopyPostcomp H₃
    (colimit.ι (clientExTower A) (l + k))
  exact H₄

set_option backward.isDefEq.respectTransparency false in
private theorem doubleMateToInfinity_naturality_left
    {K L A : SSet.{u}} (f : K ⟶ L) (k l : ℕ)
    (q : (SSet.sdIter l).obj ((SSet.sdIter k).obj L) ⟶ A) :
    doubleMateToInfinity k l
        ((SSet.sdIter l).map ((SSet.sdIter k).map f) ≫ q) =
      f ≫ doubleMateToInfinity k l q := by
  unfold doubleMateToInfinity
  have hinner := sdIterClientHomEquiv_naturality_left l
    ((SSet.sdIter k).map f) q
  rw [hinner]
  have houter :
      sdIterClientHomEquiv k K ((clientExIter l).obj A)
          ((SSet.sdIter k).map f ≫
            sdIterClientHomEquiv l ((SSet.sdIter k).obj L) A q) =
        f ≫ sdIterClientHomEquiv k L ((clientExIter l).obj A)
          (sdIterClientHomEquiv l ((SSet.sdIter k).obj L) A q) :=
    sdIterClientHomEquiv_naturality_left k f _
  rw [houter]
  simp only [Category.assoc]

private theorem inverseMate_boundary
    {A B : SSet.{u}} (f : A ⟶ B) (N k : ℕ)
    (a : (SSet.boundary N : SSet.{u}) ⟶ (clientExTower A).obj k)
    (r : (Δ[N] : SSet.{u}) ⟶ (clientExTower B).obj k)
    (h : (SSet.boundary N).ι ≫ r =
      a ≫ (clientExTowerFunctor.map f).app k) :
    (SSet.sdIter k).map (SSet.boundary N).ι ≫
        (sdIterClientHomEquiv k (Δ[N] : SSet.{u}) B).symm r =
      (sdIterClientHomEquiv k (SSet.boundary N : SSet.{u}) A).symm a ≫ f := by
  apply (sdIterClientHomEquiv k (SSet.boundary N : SSet.{u}) B).injective
  rw [sdIterClientHomEquiv_naturality_left,
    Equiv.apply_symm_apply,
    sdIterClientHomEquiv_naturality_right,
    Equiv.apply_symm_apply, h]

private noncomputable def geometricSubdivisionAdjunctGeneral
    {K : SSet.{u}} [K.Nonsingular] {X : TopCat.{u}}
    (b : SSet.toTop.obj K ⟶ X) (k : ℕ) :
    (SSet.sdIter k).obj K ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _ ((SSet.toTopSdIterIso K k).hom ≫ b)

private theorem geometricSubdivisionAdjunctGeneral_naturality_of_mono
    {K L : SSet.{u}} [K.Nonsingular] [L.Nonsingular]
    {X : TopCat.{u}} (f : K ⟶ L) [Mono f]
    (b : SSet.toTop.obj L ⟶ X) (k : ℕ) :
    (SSet.sdIter k).map f ≫ geometricSubdivisionAdjunctGeneral b k =
      geometricSubdivisionAdjunctGeneral (SSet.toTop.map f ≫ b) k := by
  unfold geometricSubdivisionAdjunctGeneral
  rw [← sSetTopAdj.homEquiv_naturality_left]
  apply congrArg (sSetTopAdj.homEquiv ((SSet.sdIter k).obj K) X)
  rw [← Category.assoc,
    SSet.toTopSdIterIso_hom_naturality_of_mono, Category.assoc]

private theorem subordinateCellGeometricLift_postcomp
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) (s : K.N) :
    subordinateCellGeometricLift U t k s ≫
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
      geometricSubdivisionAdjunct
        ((sSetTopAdj.homEquiv (Δ[s.dim] : SSet.{u}) X).symm
          ((nonsingularCellIncl K s ≫ t) ≫
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X))).ι)) k :=
  (exists_subordinate_geometric_tower_homotopy_of_simplex U
    (nonsingularCellIncl K s ≫ t) k).choose_spec.choose_spec.1

set_option backward.isDefEq.respectTransparency false in
private theorem subordinateBoundaryGeometricLift_postcomp
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {K : SSet.{u}} [K.Nonsingular]
    (t : K ⟶ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u}))
    (k : ℕ) :
    subordinateBoundaryGeometricLift U t k ≫
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι =
      geometricSubdivisionAdjunctGeneral
        ((sSetTopAdj.homEquiv K X).symm
          (t ≫ (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)) k := by
  apply (isColimitSdIterCells K k).hom_ext
  intro s
  let c := nonsingularCellIncl K s
  let _ : Mono c := by
    dsimp [c, nonsingularCellIncl]
    exact SSet.Nonsingular.mono' s.simplex s.nonDegenerate
  let b := (sSetTopAdj.homEquiv K X).symm
    (t ≫ (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι)
  have hbc : SSet.toTop.map c ≫ b =
      (sSetTopAdj.homEquiv (Δ[s.dim] : SSet.{u}) X).symm
        ((c ≫ t) ≫ (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι) := by
    symm
    rw [Category.assoc,
      sSetTopAdj.homEquiv_naturality_left_symm]
  have hrest :
      (SSet.sdIter k).map c ≫
          subordinateBoundaryGeometricLift U t k =
        subordinateCellGeometricLift U t k s := by
    unfold subordinateBoundaryGeometricLift
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      subordinateBoundaryGeometricTowerHomotopyMap_cell,
      (subordinateCellGeometricHomotopy U t k s).h₀]
  change (SSet.sdIter k).map c ≫
      ((subordinateBoundaryGeometricLift U t k) ≫
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι) =
    (SSet.sdIter k).map c ≫ geometricSubdivisionAdjunctGeneral b k
  rw [← Category.assoc,
    geometricSubdivisionAdjunctGeneral_naturality_of_mono]
  rw [hrest, subordinateCellGeometricLift_postcomp]
  rw [hbc]
  rfl

private theorem exists_sdIter_simplex_range_subset_after
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) (base : ℕ) :
    ∃ l : ℕ, ∀ {d : ℕ}
      (cell : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter (base + l)).obj (Δ[n] : SSet.{u})),
      ∃ i, Set.range
        (SSet.toTop.map cell ≫
          (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) (base + l)).hom ≫ b).hom ⊆
        (U i : Set X) := by
  let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
    b.hom.comp (meshStdToRealizationLocal.{u} n)
  obtain ⟨l, hl⟩ :=
    Convexity.StdSimplex.exists_iterate_diam_subordinate n g
      (fun i => (U i : Set X)) (fun i => (U i).isOpen) (by
        simp [hU.iSup_set_eq_univ])
  refine ⟨l, ?_⟩
  intro d cell
  let s := Set.range (SSet.sdIterCellMap n (base + l) cell).hom
  have hq0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hq1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]
    norm_num
  have hpow :
      ((n : ℝ) / ((n : ℝ) + 1)) ^ (base + l) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ l :=
    pow_le_pow_of_le_one hq0 hq1 (Nat.le_add_left l base)
  have hdiam : Metric.diam s ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ l *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n + 1)))) := by
    exact (SSet.diam_range_sdIterCellMap_le n (base + l) cell).trans
      (mul_le_mul_of_nonneg_right hpow Metric.diam_nonneg)
  obtain ⟨i, hi⟩ := hl s (Set.range_nonempty _) hdiam
  refine ⟨i, ?_⟩
  rw [← image_range_sdIterCellMap_eq_local b cell]
  simpa [g] using hi

private noncomputable def sdIterCompIso (a b : ℕ) :
    SSet.sdIter a ⋙ SSet.sdIter b ≅ SSet.sdIter (a + b) := by
  induction b with
  | zero =>
      change SSet.sdIter a ⋙ 𝟭 _ ≅ SSet.sdIter a
      exact Functor.rightUnitor (SSet.sdIter a)
  | succ b ih =>
      simpa only [SSet.sdIter_succ, Nat.add_succ] using
        (Functor.associator (SSet.sdIter a) (SSet.sdIter b) SSet.sd).symm ≪≫
          Functor.isoWhiskerRight ih SSet.sd

private noncomputable def sdIterNestedIso (k l : ℕ) :
    SSet.sdIter k ⋙ SSet.sdIter l ≅ SSet.sdIter (k + l) :=
  sdIterCompIso k l

private theorem exists_subordinateSubdivision_after
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    {n : ℕ} (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (base : ℕ) :
    ∃ (l : ℕ)
      (q : (SSet.sdIter (base + l)).obj (Δ[n] : SSet.{u}) ⟶
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u})),
      q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
        geometricSubdivisionAdjunct b (base + l) := by
  obtain ⟨l, hl⟩ := exists_sdIter_simplex_range_subset_after b U hU base
  obtain ⟨q, hq⟩ := exists_subordinateLift_of_range U b hl
  exact ⟨l, q, hq⟩

set_option backward.isDefEq.respectTransparency false in
private theorem toTopSdIterIso_nested
    (K : SSet.{u}) [K.Nonsingular] (k l : ℕ) :
    SSet.toTop.map ((sdIterNestedIso k l).app K).hom ≫
        (SSet.toTopSdIterIso K (k + l)).hom =
      (SSet.toTopSdIterIso ((SSet.sdIter k).obj K) l).hom ≫
        (SSet.toTopSdIterIso K k).hom := by
  induction l with
  | zero =>
      have h : ((sdIterNestedIso k 0).app K).hom = 𝟙 _ := by rfl
      rw [h]
      simp
  | succ l ih =>
      let f := ((sdIterNestedIso k l).app K).hom
      let _ : Mono f := by dsimp [f]; infer_instance
      let _ : SSet.Nonsingular ((SSet.sdIter k ⋙ SSet.sdIter l).obj K) := by
        change SSet.Nonsingular
          ((SSet.sdIter l).obj ((SSet.sdIter k).obj K))
        infer_instance
      change SSet.toTop.map (SSet.sd.map f) ≫
          ((SSet.toTopSdIso ((SSet.sdIter (k + l)).obj K) ≪≫
            SSet.toTopSdIterIso K (k + l)).hom) =
        (SSet.toTopSdIso ((SSet.sdIter l).obj
            ((SSet.sdIter k).obj K))).hom ≫
          (SSet.toTopSdIterIso ((SSet.sdIter k).obj K) l).hom ≫
            (SSet.toTopSdIterIso K k).hom
      rw [Iso.trans_hom]
      have hnat :
          SSet.toTop.map (SSet.sd.map f) ≫
              (SSet.toTopSdIso ((SSet.sdIter (k + l)).obj K)).hom =
            (SSet.toTopSdIso ((SSet.sdIter l).obj
              ((SSet.sdIter k).obj K))).hom ≫ SSet.toTop.map f :=
        SSet.toTopSdIso_hom_naturality_of_mono f
      calc
        SSet.toTop.map (SSet.sd.map f) ≫
            (SSet.toTopSdIso ((SSet.sdIter (k + l)).obj K)).hom ≫
              (SSet.toTopSdIterIso K (k + l)).hom =
          (SSet.toTop.map (SSet.sd.map f) ≫
            (SSet.toTopSdIso ((SSet.sdIter (k + l)).obj K)).hom) ≫
              (SSet.toTopSdIterIso K (k + l)).hom :=
            (Category.assoc _ _ _).symm
        _ = ((SSet.toTopSdIso ((SSet.sdIter l).obj
              ((SSet.sdIter k).obj K))).hom ≫ SSet.toTop.map f) ≫
              (SSet.toTopSdIterIso K (k + l)).hom := by rw [hnat]
        _ = (SSet.toTopSdIso ((SSet.sdIter l).obj
              ((SSet.sdIter k).obj K))).hom ≫
            (SSet.toTop.map f ≫
              (SSet.toTopSdIterIso K (k + l)).hom) :=
          Category.assoc _ _ _
        _ = (SSet.toTopSdIso ((SSet.sdIter l).obj
              ((SSet.sdIter k).obj K))).hom ≫
            ((SSet.toTopSdIterIso ((SSet.sdIter k).obj K) l).hom ≫
              (SSet.toTopSdIterIso K k).hom) := by rw [ih]

private theorem geometricSubdivisionAdjunct_nested
    {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X)
    (k l : ℕ) :
    ((sdIterNestedIso k l).app (Δ[n] : SSet.{u})).hom ≫
        geometricSubdivisionAdjunct b (k + l) =
      geometricSubdivisionAdjunctGeneral
        ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b) l := by
  unfold geometricSubdivisionAdjunct geometricSubdivisionAdjunctGeneral
  rw [← sSetTopAdj.homEquiv_naturality_left]
  apply congrArg
    (sSetTopAdj.homEquiv
      ((SSet.sdIter l).obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) X)
  rw [← Category.assoc, toTopSdIterIso_nested, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem subordinateNestedLift_boundary
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    {N k l : ℕ}
    (b : SSet.toTop.obj (Δ[N] : SSet.{u}) ⟶ X)
    (t : (SSet.sdIter k).obj (SSet.boundary N : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (q : (SSet.sdIter (k + l)).obj (Δ[N] : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u}))
    (hq : q ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι =
      geometricSubdivisionAdjunct b (k + l))
    (ht : (SSet.sdIter k).map (SSet.boundary N).ι ≫
        geometricSubdivisionAdjunct b k =
      t ≫ (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι) :
    (SSet.sdIter l).map ((SSet.sdIter k).map (SSet.boundary N).ι) ≫
        ((sdIterNestedIso k l).app (Δ[N] : SSet.{u})).hom ≫ q =
      subordinateBoundaryGeometricLift U t l := by
  let A := (AlgebraicTopology.subordinateCover
    (X := X) (fun i => (U i : Set X)) : SSet.{u})
  let j : A ⟶ TopCat.toSSet.obj X :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let f := (SSet.sdIter k).map (SSet.boundary N).ι
  let _ : Mono f := by
    dsimp [f]
    exact mono_sdIter_map_of_nonsingular_local (SSet.boundary N).ι k
  have htop : SSet.toTop.map f ≫
        (SSet.toTopSdIterIso (Δ[N] : SSet.{u}) k).hom ≫ b =
      (sSetTopAdj.homEquiv
        ((SSet.sdIter k).obj (SSet.boundary N : SSet.{u})) X).symm
        (t ≫ j) := by
    have h := congrArg
      (sSetTopAdj.homEquiv
        ((SSet.sdIter k).obj (SSet.boundary N : SSet.{u})) X).symm ht
    rw [sSetTopAdj.homEquiv_naturality_left_symm,
      geometricSubdivisionAdjunct, Equiv.symm_apply_apply] at h
    exact h
  apply (cancel_mono j).mp
  calc
    ((SSet.sdIter l).map f ≫
          ((sdIterNestedIso k l).app (Δ[N] : SSet.{u})).hom ≫ q) ≫ j =
        (SSet.sdIter l).map f ≫
          (((sdIterNestedIso k l).app (Δ[N] : SSet.{u})).hom ≫
            (q ≫ j)) := by simp only [Category.assoc]
    _ = (SSet.sdIter l).map f ≫
        (((sdIterNestedIso k l).app (Δ[N] : SSet.{u})).hom ≫
          geometricSubdivisionAdjunct b (k + l)) := by rw [hq]
    _ = (SSet.sdIter l).map f ≫
        geometricSubdivisionAdjunctGeneral
          ((SSet.toTopSdIterIso (Δ[N] : SSet.{u}) k).hom ≫ b) l := by
      rw [geometricSubdivisionAdjunct_nested]
    _ = geometricSubdivisionAdjunctGeneral
        (SSet.toTop.map f ≫
          (SSet.toTopSdIterIso (Δ[N] : SSet.{u}) k).hom ≫ b) l :=
      geometricSubdivisionAdjunctGeneral_naturality_of_mono f _ l
    _ = geometricSubdivisionAdjunctGeneral
        ((sSetTopAdj.homEquiv
          ((SSet.sdIter k).obj (SSet.boundary N : SSet.{u})) X).symm
          (t ≫ j)) l := by rw [htop]
    _ = subordinateBoundaryGeometricLift U t l ≫ j :=
      (subordinateBoundaryGeometricLift_postcomp U t l).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homotopyPrecomp
    {A B C : SSet.{u}} {r s : B ⟶ C}
    (H : SSet.Homotopy r s) (f : A ⟶ B) :
    SSet.Homotopy (f ≫ r) (f ≫ s) where
  h := (f ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    change SSet.ι₀ ≫ (f ▷ (Δ[1] : SSet.{u})) ≫ H.h = f ≫ r
    rw [SSet.ι₀_comp_assoc, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (f ▷ (Δ[1] : SSet.{u})) ≫ H.h = f ≫ s
    rw [SSet.ι₁_comp_assoc, H.h₁]
  rel := by
    ext n ⟨⟨x, hx⟩, z⟩
    cases hx

private noncomputable def standardCylinderProjectionHomotopy
    (X : SSet.{u}) :
    SSet.Homotopy
      ((fst X (Δ[1] : SSet.{u})) ≫ SSet.ι₀)
      (𝟙 (X ⊗ (Δ[1] : SSet.{u}))) where
  h :=
    lift
      (fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) ≫
        fst X (Δ[1] : SSet.{u}))
      ((snd X (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        (SSet.stdSimplex.homotopyConstFirstId.{u} 1).h)
  h₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  h₁ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rel := by
    ext a ⟨⟨x, hx⟩, t⟩
    all_goals
      have hx' : x ∈
          (∅ : Set ((X ⊗ (Δ[1] : SSet.{u})).obj a)) := by
        simpa using hx
      have : False := (Set.mem_empty_iff_false x).mp hx'
      exact this.elim

private theorem standardCylinderProjection_mem
    (X : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (fst X (Δ[1] : SSet.{u})) := by
  let p : X ⊗ (Δ[1] : SSet.{u}) ⟶ X :=
    fst X (Δ[1] : SSet.{u})
  let s : X ⟶ X ⊗ (Δ[1] : SSet.{u}) := SSet.ι₀
  have hps : SSet.Homotopy (p ≫ s) (𝟙 _) :=
    standardCylinderProjectionHomotopy X
  have hsp : SSet.Homotopy (s ≫ p) (𝟙 _) := by
    rw [SSet.ι₀_fst]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 X))
    exact SSet.RelativeMorphism.Homotopy.refl _
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
  exact TopCat.mem_of_eq_toFun
    (SSet.realizedHomotopyEquiv _ _ p s hps hsp) rfl

private noncomputable def standardPrecylinder (X : SSet.{u}) :
    Precylinder X :=
  { «I» := X ⊗ (Δ[1] : SSet.{u})
    i₀ := SSet.ι₀
    i₁ := SSet.ι₁
    π := fst X (Δ[1] : SSet.{u}) }

private theorem standardPrecylinder_i_mono (X : SSet.{u}) :
    Mono (standardPrecylinder X).i := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  induction n using Opposite.rec with
  | _ n =>
    induction n using SimplexCategory.rec with
    | _ m =>
      rw [mono_iff_injective]
      intro a b hab
      let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋m⦌)
      let hc : IsColimit (BinaryCofan.mk
          ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌))
          ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌))) :=
        mapIsColimitOfPreservesOfIsColimit ev _ _ (coprodIsCoprod X X)
      have hLeft (z : X.obj (op ⦋m⦌)) :
          (standardPrecylinder X).i.app (op ⦋m⦌)
              ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌) z) =
            SSet.ι₀.app (op ⦋m⦌) z := by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app
            (standardPrecylinder X).inl_i (op ⦋m⦌)) z
      have hRight (z : X.obj (op ⦋m⦌)) :
          (standardPrecylinder X).i.app (op ⦋m⦌)
              ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌) z) =
            SSet.ι₁.app (op ⦋m⦌) z := by
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app
            (standardPrecylinder X).inr_i (op ⦋m⦌)) z
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc a
      obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hc b
      rcases j with (_ | _) <;> rcases k with (_ | _)
      · have hx' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hLeft x, hLeft y] at hab
        have hxy : x = y := congrArg Prod.fst hab
        subst y
        rfl
      · have hx' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hLeft x, hRight y] at hab
        have h01 : (0 : Fin 2) = 1 :=
          congrArg (fun z => z.2 0) hab
        exact (zero_ne_one h01).elim
      · have hx' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inl : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hRight x, hLeft y] at hab
        have h10 : (1 : Fin 2) = 0 :=
          congrArg (fun z => z.2 0) hab
        exact (one_ne_zero h10).elim
      · have hx' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) x = a := by
          simpa [ev] using hx
        have hy' : ((coprod.inr : X ⟶ X ⨿ X).app (op ⦋m⦌)) y = b := by
          simpa [ev] using hy
        rw [← hx', ← hy'] at hab ⊢
        rw [hRight x, hRight y] at hab
        have hxy : x = y := congrArg Prod.fst hab
        subst y
        rfl

private noncomputable def standardCylinder (X : SSet.{u}) :
    Cylinder X :=
  { __ := standardPrecylinder X
    weakEquivalence_π := by
      rw [weakEquivalence_iff]
      exact standardCylinderProjection_mem X }

private noncomputable def simplicialHomotopyOfLeftRel
    {A B : SSet.{u}} [B.KanComplex]
    {f g : A ⟶ B} (h : LeftHomotopyRel f g) :
    SSet.Homotopy f g := by
  let P := standardCylinder A
  letI : P.IsGood :=
    { cofibration_i := by
        rw [cofibration_iff]
        exact standardPrecylinder_i_mono A }
  let H := h.leftHomotopy P
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      rel := by
        ext n ⟨⟨x, hx⟩, t⟩
        cases hx }

private noncomputable def simplicialHomotopyOfWeakPrecompCancellation
    {A B Z : SSet.{u}} [Z.KanComplex]
    (i : A ⟶ B) (hi : SSet.realizationWeakEquivalences i)
    {f g : B ⟶ Z} (h : i ≫ f = i ≫ g) :
    SSet.Homotopy f g := by
  letI : WeakEquivalence i :=
    (weakEquivalence_iff i).mpr hi
  have hClass :
      RightHomotopyClass.mk f = RightHomotopyClass.mk g := by
    apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z i).1
    simpa only [RightHomotopyClass.precomp_mk] using
      congrArg RightHomotopyClass.mk h
  have hRight : RightHomotopyRel f g :=
    (RightHomotopyClass.mk_eq_mk_iff f g).mp hClass
  exact simplicialHomotopyOfLeftRel hRight.leftHomotopyRel

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem clientExTowerZeroMapRaw_comp_grid
    (A : SSet.{u}) (k l : ℕ) :
    clientExTowerZeroMapRaw A k ≫
        (clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
        ((clientExIterCompIso l k).app A).hom =
      clientExTowerZeroMapRaw A (l + k) := by
  induction k with
  | zero =>
      have hzero : clientExTowerZeroMapRaw A 0 = 𝟙 A := by
        unfold clientExTowerZeroMapRaw clientExTowerZeroHom
        rw [Subsingleton.elim (homOfLE (Nat.zero_le 0)) (𝟙 0)]
        simp
      have hiso : ((clientExIterCompIso l 0).app A).hom = 𝟙 _ := rfl
      rw [hzero, hiso]
      change clientExTowerZeroMapRaw A l ≫ 𝟙 _ =
        clientExTowerZeroMapRaw A l
      exact Category.comp_id _
  | succ k ih =>
      have hunit₁ :
          SSet.exUnit.app ((clientExIter k).obj A) ≫
              SSet.ex.map ((clientExIter k).map
                (clientExTowerZeroMapRaw A l)) =
            (clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
              SSet.exUnit.app ((clientExIter k).obj
                ((clientExTower A).obj l)) := by
        simpa only [Functor.id_map] using
          (SSet.exUnit.naturality
            ((clientExIter k).map (clientExTowerZeroMapRaw A l))).symm
      have hunit₂ :
          SSet.exUnit.app ((clientExIter k).obj
                ((clientExTower A).obj l)) ≫
              SSet.ex.map (((clientExIterCompIso l k).app A).hom) =
            ((clientExIterCompIso l k).app A).hom ≫
              SSet.exUnit.app ((clientExIter (l + k)).obj A) := by
        change
          SSet.exUnit.app ((clientExIter l ⋙ clientExIter k).obj A) ≫
                SSet.ex.map (((clientExIterCompIso l k).app A).hom) =
            ((clientExIterCompIso l k).app A).hom ≫
              SSet.exUnit.app ((clientExIter (l + k)).obj A)
        simpa only [Functor.id_map] using
          (SSet.exUnit.naturality
            (((clientExIterCompIso l k).app A).hom)).symm
      rw [clientExTowerZeroMapRaw_succ]
      change
        (clientExTowerZeroMapRaw A k ≫
            SSet.exUnit.app ((clientExIter k).obj A)) ≫
            SSet.ex.map ((clientExIter k).map
              (clientExTowerZeroMapRaw A l)) ≫
            SSet.ex.map (((clientExIterCompIso l k).app A).hom) =
          clientExTowerZeroMapRaw A (l + k + 1)
      calc
        (clientExTowerZeroMapRaw A k ≫
              SSet.exUnit.app ((clientExIter k).obj A)) ≫
              SSet.ex.map ((clientExIter k).map
                (clientExTowerZeroMapRaw A l)) ≫
              SSet.ex.map (((clientExIterCompIso l k).app A).hom) =
            clientExTowerZeroMapRaw A k ≫
              (SSet.exUnit.app ((clientExIter k).obj A) ≫
                SSet.ex.map ((clientExIter k).map
                  (clientExTowerZeroMapRaw A l))) ≫
              SSet.ex.map (((clientExIterCompIso l k).app A).hom) := by
                simp only [Category.assoc]
        _ = clientExTowerZeroMapRaw A k ≫
              ((clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
                SSet.exUnit.app ((clientExIter k).obj
                  ((clientExTower A).obj l))) ≫
              SSet.ex.map (((clientExIterCompIso l k).app A).hom) := by
                rw [hunit₁]
        _ = (clientExTowerZeroMapRaw A k ≫
              (clientExIter k).map (clientExTowerZeroMapRaw A l)) ≫
              (SSet.exUnit.app ((clientExIter k).obj
                  ((clientExTower A).obj l)) ≫
                SSet.ex.map (((clientExIterCompIso l k).app A).hom)) := by
                  simp only [Category.assoc]
        _ = (clientExTowerZeroMapRaw A k ≫
              (clientExIter k).map (clientExTowerZeroMapRaw A l)) ≫
              (((clientExIterCompIso l k).app A).hom ≫
                SSet.exUnit.app ((clientExIter (l + k)).obj A)) := by
                  rw [hunit₂]
        _ = (clientExTowerZeroMapRaw A k ≫
              (clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
              ((clientExIterCompIso l k).app A).hom) ≫
              SSet.exUnit.app ((clientExIter (l + k)).obj A) := by
                simp only [Category.assoc]
        _ = clientExTowerZeroMapRaw A (l + k) ≫
              SSet.exUnit.app ((clientExIter (l + k)).obj A) := by rw [ih]
        _ = clientExTowerZeroMapRaw A (l + k + 1) :=
          (clientExTowerZeroMapRaw_succ A (l + k)).symm

private theorem clientExTowerZeroMapRaw_mem
    (A : SSet.{u}) (k : ℕ) :
    SSet.realizationWeakEquivalences (clientExTowerZeroMapRaw A k) := by
  induction k with
  | zero =>
      have hmap :
          (clientExTower A).map (homOfLE (Nat.zero_le 0)) = 𝟙 _ := by
        rw [Subsingleton.elim (homOfLE (Nat.zero_le 0)) (𝟙 0)]
        exact (clientExTower A).map_id 0
      unfold clientExTowerZeroMapRaw
      rw [hmap]
      let e : A ≅ (clientExTower A).obj 0 := eqToIso (by rfl)
      have he : clientExTowerZeroHom A = e.hom := by
        rfl
      have hzeroMem :
          SSet.realizationWeakEquivalences (clientExTowerZeroHom A) := by
        rw [he]
        exact SSet.realizationWeakEquivalences.of_isIso e.hom
      exact MorphismProperty.comp_mem SSet.realizationWeakEquivalences _ _
        hzeroMem
        (SSet.realizationWeakEquivalences.id_mem _)
  | succ k ih =>
      rw [clientExTowerZeroMapRaw_succ]
      exact MorphismProperty.comp_mem SSet.realizationWeakEquivalences _ _ ih
        (SSet.exUnit_app_mem_realizationWeakEquivalences _)

private noncomputable def alternateGridToInfinity
    (A : SSet.{u}) (k l : ℕ) :
    (clientExTower A).obj k ⟶ colimit (clientExTower A) :=
  (clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
    ((clientExIterCompIso l k).app A).hom ≫
    colimit.ι (clientExTower A) (l + k)

set_option backward.isDefEq.respectTransparency false in
private theorem alternateGridToInfinity_precomp
    (A : SSet.{u}) (k l : ℕ) :
    clientExTowerZeroMapRaw A k ≫ alternateGridToInfinity A k l =
      clientExTowerZeroMapRaw A k ≫
        colimit.ι (clientExTower A) k := by
  calc
    clientExTowerZeroMapRaw A k ≫ alternateGridToInfinity A k l =
        (clientExTowerZeroMapRaw A k ≫
          (clientExIter k).map (clientExTowerZeroMapRaw A l) ≫
          ((clientExIterCompIso l k).app A).hom) ≫
          colimit.ι (clientExTower A) (l + k) := by
            simp only [alternateGridToInfinity, Category.assoc]
    _ = clientExTowerZeroMapRaw A (l + k) ≫
          colimit.ι (clientExTower A) (l + k) := by
            rw [clientExTowerZeroMapRaw_comp_grid]
    _ = SSet.exInfinityUnit.app A :=
      clientExTowerZeroMapRaw_colimit A (l + k)
    _ = clientExTowerZeroMapRaw A k ≫
          colimit.ι (clientExTower A) k :=
      (clientExTowerZeroMapRaw_colimit A k).symm

private noncomputable def alternateGridToInfinityHomotopy
    (A : SSet.{u}) (k l : ℕ) :
    SSet.Homotopy (alternateGridToInfinity A k l)
      (colimit.ι (clientExTower A) k) := by
  let _ : (colimit (clientExTower A)).KanComplex := by
    change (SSet.exInfinity.obj A).KanComplex
    exact SSet.exInfinity_kanComplex A
  exact simplicialHomotopyOfWeakPrecompCancellation
    (clientExTowerZeroMapRaw A k)
    (clientExTowerZeroMapRaw_mem A k)
    (alternateGridToInfinity_precomp A k l)

set_option backward.isDefEq.respectTransparency false in
private theorem doubleMateToInfinity_towerLastVertex
    {K A : SSet.{u}} (k l : ℕ)
    (t : (SSet.sdIter k).obj K ⟶ A) :
    doubleMateToInfinity k l
        (towerLastVertex ((SSet.sdIter k).obj K) l ≫ t) =
      sdIterClientHomEquiv k K A t ≫
        alternateGridToInfinity A k l := by
  unfold doubleMateToInfinity alternateGridToInfinity
  rw [towerLastVertex_promote]
  rw [sdIterClientHomEquiv_naturality_right]
  rw [clientExTowerFunctor_map_app]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_subordinate_common_stage_boundary_filler
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    {N k : ℕ}
    (a : (SSet.boundary N : SSet.{u}) ⟶
      (clientExTower
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X)) : SSet.{u})).obj k)
    (r : (Δ[N] : SSet.{u}) ⟶
      (clientExTower (TopCat.toSSet.obj X)).obj k)
    (hboundary : (SSet.boundary N).ι ≫ r =
      a ≫ (clientExTowerFunctor.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι).app k) :
    ∃ g : (Δ[N] : SSet.{u}) ⟶
        SSet.exInfinity.obj
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X)) : SSet.{u}),
      (SSet.boundary N).ι ≫ g =
        a ≫ colimit.ι
          (clientExTower
            (AlgebraicTopology.subordinateCover
              (fun i => (U i : Set X)) : SSet.{u})) k := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let aMate : (SSet.sdIter k).obj (SSet.boundary N : SSet.{u}) ⟶ A :=
    (sdIterClientHomEquiv k (SSet.boundary N : SSet.{u}) A).symm a
  let rMate : (SSet.sdIter k).obj (Δ[N] : SSet.{u}) ⟶ B :=
    (sdIterClientHomEquiv k (Δ[N] : SSet.{u}) B).symm r
  have hMate :
      (SSet.sdIter k).map (SSet.boundary N).ι ≫ rMate =
        aMate ≫ j := by
    exact inverseMate_boundary j N k a r hboundary
  let b : SSet.toTop.obj (Δ[N] : SSet.{u}) ⟶ X :=
    stageTopAdjunct rMate
  have hgeom : geometricSubdivisionAdjunct b k = rMate :=
    geometricSubdivisionAdjunct_stageTopAdjunct rMate
  have hboundaryGeom :
      (SSet.sdIter k).map (SSet.boundary N).ι ≫
          geometricSubdivisionAdjunct b k =
        aMate ≫ j := by
    rw [hgeom]
    exact hMate
  obtain ⟨l, q, hq⟩ := exists_subordinateSubdivision_after U hU b k
  let qNested :
      (SSet.sdIter l).obj
          ((SSet.sdIter k).obj (Δ[N] : SSet.{u})) ⟶ A :=
    ((sdIterNestedIso k l).app (Δ[N] : SSet.{u})).hom ≫ q
  have hqBoundary :
      (SSet.sdIter l).map
          ((SSet.sdIter k).map (SSet.boundary N).ι) ≫ qNested =
        subordinateBoundaryGeometricLift U aMate l := by
    exact subordinateNestedLift_boundary U b aMate q hq hboundaryGeom
  let g₀ : (Δ[N] : SSet.{u}) ⟶ colimit (clientExTower A) :=
    doubleMateToInfinity k l qNested
  have hg₀Boundary :
      (SSet.boundary N).ι ≫ g₀ =
        doubleMateToInfinity k l
          (subordinateBoundaryGeometricLift U aMate l) := by
    rw [← doubleMateToInfinity_naturality_left]
    exact congrArg (doubleMateToInfinity k l) hqBoundary
  let Hraw := doubleMateHomotopyToInfinity
    (subordinateBoundaryGeometricTowerHomotopy U aMate l)
  let H₀ : SSet.Homotopy ((SSet.boundary N).ι ≫ g₀)
      (a ≫ alternateGridToInfinity A k l) :=
    { h := Hraw.h
      h₀ := by
        rw [Hraw.h₀]
        exact hg₀Boundary.symm
      h₁ := by
        change SSet.ι₁ ≫ Hraw.h =
          a ≫ alternateGridToInfinity A k l
        rw [Hraw.h₁, doubleMateToInfinity_towerLastVertex]
        dsimp only [aMate]
        rw [Equiv.apply_symm_apply]
      rel := Hraw.rel }
  let _ : (colimit (clientExTower A)).KanComplex := by
    change (SSet.exInfinity.obj A).KanComplex
    exact SSet.exInfinity_kanComplex A
  obtain ⟨g₁, _Hg₁, hg₁Boundary, _⟩ :=
    exists_extension_of_boundary_homotopy N g₀
      (a ≫ alternateGridToInfinity A k l) H₀
  let Hgrid := homotopyPrecomp
    (alternateGridToInfinityHomotopy A k l) a
  let H₁ : SSet.Homotopy ((SSet.boundary N).ι ≫ g₁)
      (a ≫ colimit.ι (clientExTower A) k) :=
    { h := Hgrid.h
      h₀ := Hgrid.h₀.trans hg₁Boundary.symm
      h₁ := Hgrid.h₁
      rel := Hgrid.rel }
  obtain ⟨g₂, _Hg₂, hg₂Boundary, _⟩ :=
    exists_extension_of_boundary_homotopy N g₁
      (a ≫ colimit.ι (clientExTower A) k) H₁
  exact ⟨g₂, hg₂Boundary⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_subordinate_source_relStruct₀
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    {x : (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})) _⦋0⦌}
    {y : (SSet.exInfinity.obj (TopCat.toSSet.obj X)) _⦋0⦌}
    (hbase : (SSet.exInfinity.map
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι).app _ x = y)
    {p q : (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})).PtSimplex (n + 1) x}
    (rTarget :
      (SSet.PtSimplex.map
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι) hbase p).RelStruct₀
      (SSet.PtSimplex.map
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι) hbase q)) :
    Nonempty (p.RelStruct₀ q) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  let _ : Mono j := by
    dsimp [j]
    infer_instance
  let _ : Mono ej := clientExInfinity_map_mono j
  obtain ⟨b, hb⟩ :=
    exists_relStruct_source_boundary ej hbase n rTarget
  obtain ⟨ks, a, r, ha, _hr, hstage⟩ :=
    exists_relStruct_common_stage j n rTarget.map b hb
  let k : ℕ := CategoryTheory.AsSmall.down.obj ks
  obtain ⟨g, hg⟩ :=
    exists_subordinate_common_stage_boundary_filler
      U hU a r hstage
  have hgBoundary :
      (SSet.boundary (n + 2)).ι ≫ g = b := by
    exact hg.trans ha
  have gface (i : Fin (n + 3)) :
      (SSet.stdSimplex.δ i ≫ g) ≫ ej =
        SSet.stdSimplex.δ i ≫ rTarget.map := by
    calc
      (SSet.stdSimplex.δ i ≫ g) ≫ ej =
          ((SSet.boundary.ι i ≫
            (SSet.boundary (n + 2)).ι) ≫ g) ≫ ej := by
              rw [SSet.boundary.ι_ι]
      _ = SSet.boundary.ι i ≫
          (((SSet.boundary (n + 2)).ι ≫ g) ≫ ej) := by
            simp only [Category.assoc]
      _ = SSet.boundary.ι i ≫ (b ≫ ej) := by
            rw [hgBoundary]
      _ = SSet.boundary.ι i ≫
          ((SSet.boundary (n + 2)).ι ≫ rTarget.map) := by
            rw [hb]
      _ = ((SSet.boundary.ι i ≫
          (SSet.boundary (n + 2)).ι) ≫ rTarget.map) := by
            simp only [Category.assoc]
      _ = SSet.stdSimplex.δ i ≫ rTarget.map := by
            rw [SSet.boundary.ι_ι]
  let rSource : p.RelStruct₀ q :=
    { map := g
      δ_castSucc_map := by
        apply (cancel_mono ej).mp
        change (SSet.stdSimplex.δ
            ((0 : Fin (n + 2)).castSucc) ≫ g) ≫ ej =
          SSet.RelativeMorphism.map p ≫ ej
        rw [gface ((0 : Fin (n + 2)).castSucc),
          rTarget.δ_castSucc_map]
        rfl
      δ_succ_map := by
        apply (cancel_mono ej).mp
        change (SSet.stdSimplex.δ
            ((0 : Fin (n + 2)).succ) ≫ g) ≫ ej =
          SSet.RelativeMorphism.map q ≫ ej
        rw [gface ((0 : Fin (n + 2)).succ),
          rTarget.δ_succ_map]
        rfl
      δ_map_of_lt := by
        intro i hi
        exact (Fin.not_lt_zero i hi).elim
      δ_map_of_gt := by
        intro i hi
        apply (cancel_mono ej).mp
        change (SSet.stdSimplex.δ i ≫ g) ≫ ej =
          SSet.const x ≫ ej
        rw [gface i, rTarget.δ_map_of_gt i hi,
          SSet.const_comp, hbase] }
  exact ⟨rSource⟩

private theorem subordinateCover_piMap_injective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    (x : (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})) _⦋0⦌) :
    Function.Injective
      (SSet.KanComplex.π.map
        (x := x)
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        rfl (n + 1)) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  let _ : (SSet.exInfinity.obj A).KanComplex :=
    SSet.exInfinity_kanComplex A
  let _ : (SSet.exInfinity.obj B).KanComplex :=
    SSet.exInfinity_kanComplex B
  intro pClass qClass hClass
  induction pClass using SSet.KanComplex.π.rec with
  | mk p =>
    induction qClass using SSet.KanComplex.π.rec with
    | mk q =>
      rw [SSet.KanComplex.π.map_mk,
        SSet.KanComplex.π.map_mk,
        SSet.KanComplex.π.mk_eq_mk_iff] at hClass
      rw [SSet.KanComplex.π.mk_eq_mk_iff]
      exact exists_subordinate_source_relStruct₀
        U hU n rfl hClass.some

private theorem subordinateCover_piMap_bijective
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (n : ℕ)
    (x : (SSet.exInfinity.obj
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X)) : SSet.{u})) _⦋0⦌) :
    Function.Bijective
      (SSet.KanComplex.π.map
        (x := x)
        (SSet.exInfinity.map
          (AlgebraicTopology.subordinateCover
            (fun i => (U i : Set X))).ι)
        rfl (n + 1)) :=
  ⟨subordinateCover_piMap_injective U hU n x,
    subordinateCover_piMap_surjective U hU n x⟩

private theorem exInfinity_subordinateCover_W
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    SSet.KanComplex.W
      (SSet.exInfinity.map
        (AlgebraicTopology.subordinateCover
          (fun i => (U i : Set X))).ι) := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let _ : (SSet.exInfinity.obj A).KanComplex :=
    SSet.exInfinity_kanComplex A
  let _ : (SSet.exInfinity.obj B).KanComplex :=
    SSet.exInfinity_kanComplex B
  apply (SSet.KanComplex.W_iff _).mpr
  exact ⟨subordinateCover_mapπ₀_bijective U hU,
    fun n x => subordinateCover_piMap_bijective U hU n x⟩

/-- The inclusion of singular simplices subordinate to an indexed open cover
is a realization weak equivalence. -/
theorem subordinateCover_ι_mem_realizationWeakEquivalences
    {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let B : SSet.{u} := TopCat.toSSet.obj X
  let j : A ⟶ B :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  let ej : SSet.exInfinity.obj A ⟶ SSet.exInfinity.obj B :=
    SSet.exInfinity.map j
  let _ : (SSet.exInfinity.obj A).KanComplex :=
    SSet.exInfinity_kanComplex A
  let _ : (SSet.exInfinity.obj B).KanComplex :=
    SSet.exInfinity_kanComplex B
  have hejW : SSet.KanComplex.W ej :=
    exInfinity_subordinateCover_W U hU
  have hej : SSet.realizationWeakEquivalences ej :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence ej).mp hejW
  have hηA : SSet.realizationWeakEquivalences
      (SSet.exInfinityUnit.app A) :=
    SSet.exInfinityUnit_mem_realizationWeakEquivalences A
  have hηB : SSet.realizationWeakEquivalences
      (SSet.exInfinityUnit.app B) :=
    SSet.exInfinityUnit_mem_realizationWeakEquivalences B
  have hnat : j ≫ SSet.exInfinityUnit.app B =
      SSet.exInfinityUnit.app A ≫ ej := by
    simpa only [Functor.id_map] using
      SSet.exInfinityUnit.naturality j
  have hcomp : SSet.realizationWeakEquivalences
      (j ≫ SSet.exInfinityUnit.app B) := by
    rw [hnat]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hηA hej
  exact SSet.realizationWeakEquivalences.of_postcomp
    j (SSet.exInfinityUnit.app B) hηB hcomp

end AlgebraicTopology

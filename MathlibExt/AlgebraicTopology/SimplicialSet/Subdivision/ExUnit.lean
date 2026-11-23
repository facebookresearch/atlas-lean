/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.LastVertex
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Nonsingular
import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.AnchoredNormalForm
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubdivisionAnodyne
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexFirstContraction
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import MathlibExt.CategoryTheory.NerveHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.Order.Preorder.Finite

/-!
# The unit from a simplicial set to its Kan Ex construction

This file constructs the mate of the last-vertex map under the subdivision--Ex
adjunction.  Its components are monomorphisms and realization weak
equivalences in every universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
  MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial

universe v u

namespace SSet

/-- The natural map from a simplicial set to its one-step Kan Ex construction,
defined as the mate of the last-vertex map. -/
noncomputable def exUnit :
    Functor.id (SSet.{u}) ⟶ SSet.ex.{u} where
  app X := (SSet.sdExAdjunction.homEquiv X X) (SSet.lastVertex.app X)
  naturality X Y f :=
    SSet.sdExAdjunction.homEquiv_naturality_left_square
      f (SSet.lastVertex.app Y) (SSet.lastVertex.app X) f
      (SSet.lastVertex.naturality f)

/-- The inverse mate of `exUnit` is the last-vertex map. -/
theorem exUnit_mate (X : SSet.{u}) :
    (SSet.sdExAdjunction.homEquiv X X).symm
        (SSet.exUnit.app X) =
      SSet.lastVertex.app X :=
  Equiv.symm_apply_apply _ _

/-- In restricted-Yoneda coordinates, `exUnit` is precomposition with the
representable last-vertex map. -/
private theorem exUnit_app_down
    (X : SSet.{u}) {n : SimplexCategory}
    (x : X.obj (Opposite.op n)) :
    ULift.down ((SSet.exUnit.app X).app (Opposite.op n) x) =
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
      SSet.sd.{u} α hα X X (SSet.lastVertex.app X)
      (Opposite.op n) x
  have happ' :
      (SSet.exUnit.app X).app (Opposite.op n) x =
        ULift.up
          (SSet.stdSimplex.sdIso.inv.app n ≫
            SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
            SSet.lastVertex.app X) := by
    simpa only [SSet.exUnit, α, SSet.sdExAdjunction,
      SSet.ex, SSet.sd, SSet.yonedaEquiv] using! happ
  have hdown := congrArg ULift.down happ'
  rw [SSet.lastVertex.naturality] at hdown
  rw [← Category.assoc, SSet.lastVertex_fac] at hdown
  exact hdown

/-- The initial segment ending at a vertex, regarded as a nonempty face. -/
private def prefixFace (n : SimplexCategory)
    (j : Fin (n.len + 1)) :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) where
  finset := Finset.univ.filter (fun i => i.down ≤ j)
  nonempty := ⟨ULift.up j, by simp⟩
  comparable _ _ := le_total _ _

/-- Initial segments increase with their terminal vertices. -/
private def prefixFaceOrderHom (n : SimplexCategory) :
    Fin (n.len + 1) →o
      PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) where
  toFun := prefixFace n
  monotone' i j hij x hx := by
    simp only [prefixFace, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hij

/-- The top-dimensional subdivision simplex formed by all initial segments. -/
private def prefixChain (n : SimplexCategory) :
    (SimplexCategory.sd.{u}.obj n).obj (Opposite.op n) :=
  (prefixFaceOrderHom n).monotone.functor

private theorem sdChainLast_prefixFace (n : SimplexCategory)
    (j : Fin (n.len + 1)) :
    SimplexCategory.sdChainLast n (prefixFace n j) = ULift.up j := by
  unfold SimplexCategory.sdChainLast prefixFace
  rw [Finset.max'_eq_iff]
  constructor
  · simp
  · intro b hb
    change b.down ≤ j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb

/-- Yoneda turns a top simplex in the representable subdivision into a map
from the corresponding standard simplex. -/
private noncomputable def rawPrefixSection (n : SimplexCategory)
    (z : (SimplexCategory.sd.{u}.obj n) _⦋n.len⦌) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  SSet.yonedaEquiv.{u}.symm z

private theorem rawPrefixSection_retraction (n : SimplexCategory)
    (z : (SimplexCategory.sd.{u}.obj n) _⦋n.len⦌)
    (hz : ∀ i : Fin (n.len + 1),
      SimplexCategory.sdChainLast n (z.obj i) = ULift.up i) :
    rawPrefixSection n z ≫ SimplexCategory.lastVertex.app n = 𝟙 _ := by
  apply SSet.yonedaEquiv.{u}.injective
  rw [SSet.yonedaEquiv_comp]
  have hsec := Equiv.apply_symm_apply SSet.yonedaEquiv.{u} z
  simp only [rawPrefixSection]
  rw [hsec]
  apply SSet.stdSimplex.ext
  intro i
  change SSet.stdSimplex.objEquiv.{u}
      ((SimplexCategory.lastVertex.app n).app _ z) i =
    SSet.stdSimplex.objEquiv.{u}
      (SSet.yonedaEquiv.{u} (𝟙 (SSet.stdSimplex.obj n))) i
  rw [SimplexCategory.lastVertex_app_objEquiv_apply,
    SSet.stdSimplex.objEquiv_yonedaEquiv_id.{u}]
  exact congrArg ULift.down (hz i)

/-- A representable-by-representable section of the last-vertex map.  It is
not asserted to be natural in the representing simplex. -/
private noncomputable def rawLastVertexSection (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  rawPrefixSection n (prefixChain n)

private theorem rawLastVertexSection_comp_lastVertex (n : SimplexCategory) :
    rawLastVertexSection n ≫ SimplexCategory.lastVertex.app n = 𝟙 _ := by
  apply rawPrefixSection_retraction n (prefixChain n)
  intro i
  change SimplexCategory.sdChainLast n (prefixFace n i) = ULift.up i
  exact sdChainLast_prefixFace n i

/-- Every component of the one-step Ex unit is a monomorphism. -/
theorem exUnit_app_mono (X : SSet.{u}) :
    Mono (SSet.exUnit.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  induction n using Opposite.rec with
  | _ n =>
      rw [mono_iff_injective]
      intro x y hxy
      apply SSet.yonedaEquiv.{u}.symm.injective
      have hxy' := congrArg ULift.down hxy
      rw [exUnit_app_down, exUnit_app_down] at hxy'
      calc
        SSet.yonedaEquiv.{u}.symm x =
            𝟙 _ ≫ SSet.yonedaEquiv.{u}.symm x := by rw [Category.id_comp]
        _ = (rawLastVertexSection n ≫
              SimplexCategory.lastVertex.app n) ≫
              SSet.yonedaEquiv.{u}.symm x := by
            rw [rawLastVertexSection_comp_lastVertex]
        _ = rawLastVertexSection n ≫
              (SimplexCategory.lastVertex.app n ≫
                SSet.yonedaEquiv.{u}.symm x) := by
            rw [Category.assoc]
        _ = rawLastVertexSection n ≫
              (SimplexCategory.lastVertex.app n ≫
                SSet.yonedaEquiv.{u}.symm y) := by rw [hxy']
        _ = (rawLastVertexSection n ≫
              SimplexCategory.lastVertex.app n) ≫
              SSet.yonedaEquiv.{u}.symm y := by
            rw [Category.assoc]
        _ = 𝟙 _ ≫ SSet.yonedaEquiv.{u}.symm y := by
            rw [rawLastVertexSection_comp_lastVertex]
        _ = SSet.yonedaEquiv.{u}.symm y := by rw [Category.id_comp]

/-! The following private argument proves that subdivision preserves arbitrary
monomorphisms.  Only the generating boundary inclusions use the
nonsingular-nerve description; arbitrary monomorphisms are then handled by
their relative-cell presentations. -/

private theorem nondegenerateMap_injective
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (SSet.N.map f) := by
  intro x y hxy
  apply SSet.N.subcomplex_injective
  apply le_antisymm
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]

private theorem mono_nondegenerateNerve_map
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.nondegenerateNerve.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext
    (h := fun j => nondegenerateMap_injective f
      (congrArg (fun z => z.obj j) hab))
    (w := by
      intro j hj
      subsingleton)

private theorem mono_sd_map_of_nonsingular
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] : Mono (SSet.sd.map f) := by
  have h :
      SSet.sd.map f ≫ (SSet.sdIsoNondegenerateNerve Y).hom =
        (SSet.sdIsoNondegenerateNerve X).hom ≫
          SSet.nondegenerateNerve.map f := by
    rw [SSet.sdIsoNondegenerateNerve_hom,
      SSet.sdIsoNondegenerateNerve_hom]
    exact SSet.sdToNondegenerateNerve.naturality f
  let _ : Mono (SSet.nondegenerateNerve.map f) :=
    mono_nondegenerateNerve_map f
  have : Mono ((SSet.sdIsoNondegenerateNerve X).hom ≫
      SSet.nondegenerateNerve.map f) := inferInstance
  exact mono_of_mono_fac h

private theorem mono_sd_map_boundary (n : ℕ) :
    Mono (SSet.sd.map (SSet.boundary.{u} n).ι) :=
  mono_sd_map_of_nonsingular (SSet.boundary.{u} n).ι

/-- Applying subdivision to an attachment square again gives an attachment
square, since subdivision is a left adjoint. -/
private noncomputable def mapAttachCellsSd
    {α : Type*} {A B : α → SSet.{u}}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : SSet.{u}} {f : X₁ ⟶ X₂}
    (c : AttachCells.{u} g f) :
    AttachCells.{u} (fun a => SSet.sd.map (g a)) (SSet.sd.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (SSet.sd.obj c.cofan₁.pt)
    (fun j => SSet.sd.map (c.cofan₁.inj j))
  cofan₂ := Cofan.mk (SSet.sd.obj c.cofan₂.pt)
    (fun j => SSet.sd.map (c.cofan₂.inj j))
  isColimit₁ := isColimitCofanMkObjOfIsColimit
    (G := SSet.sd) (f := fun j => A (c.π j))
    (fun j => c.cofan₁.inj j) c.isColimit₁
  isColimit₂ := isColimitCofanMkObjOfIsColimit
    (G := SSet.sd) (f := fun j => B (c.π j))
    (fun j => c.cofan₂.inj j) c.isColimit₂
  m := SSet.sd.map c.m
  hm j := by
    change SSet.sd.map (c.cofan₁.inj j) ≫ SSet.sd.map c.m =
      SSet.sd.map (g (c.π j)) ≫ SSet.sd.map (c.cofan₂.inj j)
    rw [← SSet.sd.map_comp, ← SSet.sd.map_comp, c.hm]
  g₁ := SSet.sd.map c.g₁
  g₂ := SSet.sd.map c.g₂
  isPushout := c.isPushout.map SSet.sd

private theorem mono_mapAttachCellsSd
    {α : Type*} {A B : α → SSet.{u}}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : SSet.{u}} {f : X₁ ⟶ X₂}
    (c : AttachCells.{u} g f) :
    (∀ a, Mono (SSet.sd.map (g a))) →
      Mono (SSet.sd.map f) := by
  intro hg
  let _ : (monomorphisms SSet.{u}).IsStableUnderCobaseChange := by
    rw [← MorphismProperty.functorCategory_monomorphisms]
    infer_instance
  let cm := mapAttachCellsSd g c
  have hbasic :
      ofHoms (fun a => SSet.sd.map (g a)) ≤
        monomorphisms SSet.{u} := by
    rintro _ _ _ ⟨a⟩
    exact monomorphisms.infer_property _
  have hle :
      (coproducts.{u} (ofHoms (fun a => SSet.sd.map (g a)))).pushouts ≤
        monomorphisms SSet.{u} := by
    calc
      _ ≤ (coproducts.{u} (monomorphisms SSet.{u})).pushouts :=
        pushouts_monotone (coproducts_monotone hbasic)
      _ ≤ (monomorphisms SSet.{u}).pushouts :=
        pushouts_monotone
          (MorphismProperty.coproducts_le
            (W := monomorphisms SSet.{u}))
      _ ≤ monomorphisms SSet.{u} :=
        MorphismProperty.pushouts_le
  have hm := hle _ cm.pushouts_coproducts
  simpa only [monomorphisms.iff] using hm

/-- Subdivision preserves every monomorphism of simplicial sets. -/
private theorem sd_map_mono
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Mono (SSet.sd.map i) := by
  let _ : PreservesWellOrderContinuousOfShape ℕ SSet.sd :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let c := SSet.relativeCellComplexOfMono i
  let tc := c.toTransfiniteCompositionOfShape.map SSet.sd
  have hstep (n : ℕ) (hn : ¬ IsMax n) :
      Mono ((c.F ⋙ SSet.sd).map (homOfLE (Order.le_succ n))) := by
    change Mono (SSet.sd.map (c.F.map (homOfLE (Order.le_succ n))))
    exact mono_mapAttachCellsSd
      (fun _ : Unit => (SSet.boundary.{u} n).ι)
      (c.attachCells n hn)
      (fun _ => mono_sd_map_boundary n)
  let htc : (monomorphisms SSet.{u}).TransfiniteCompositionOfShape ℕ
      (SSet.sd.map i) :=
    { __ := tc
      map_mem := fun n hn => by
        change Mono ((c.F ⋙ SSet.sd).map
          (homOfLE (Order.le_succ n)))
        exact hstep n hn }
  have hm : (monomorphisms SSet.{u}) (SSet.sd.map i) :=
    (MorphismProperty.transfiniteCompositionsOfShape_le
      (W := monomorphisms SSet.{u}) (J := ℕ)) _ htc.mem
  simpa only [monomorphisms.iff] using hm

/-! We next establish the representable case of last-vertex weakness by
contracting both source and target to their terminal vertices. -/

private theorem realizationWeakEquivalence_of_iso_square
    {A B A' B' : SSet.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : eA.hom ≫ f' = f ≫ eB.hom)
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences f' := by
  have hPost := RespectsIso.postcomp realizationWeakEquivalences eB.hom f hf
  rw [← h] at hPost
  exact (realizationWeakEquivalences.cancel_left_of_respectsIso eA.hom f').mp hPost

private theorem realizationWeakEquivalence_of_iso_square_rev
    {A B A' B' : SSet.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B')
    (h : eA.hom ≫ f' = f ≫ eB.hom)
    (hf' : realizationWeakEquivalences f') :
    realizationWeakEquivalences f := by
  have hPre := RespectsIso.precomp realizationWeakEquivalences
    eA.hom f' hf'
  rw [h] at hPre
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso
    f eB.hom).mp hPre

/-- The nerve of a category with a chosen terminal object contracts, after
realization, along the actual natural transformation to the constant
functor. -/
private theorem terminalNerveMap_mem
    {C : Type u} [Category.{v} C] {T : C} (hT : IsTerminal T) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) := by
  let N : SSet.{max u v} := CategoryTheory.nerve C
  let q : N ⟶ (Δ[0] : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.from N
  let x : N _⦋0⦌ := (Functor.const (Fin 1)).obj T
  let s : (Δ[0] : SSet.{max u v}) ⟶ N := SSet.const x
  let c : N ⟶ N := CategoryTheory.nerveMap ((Functor.const C).obj T)
  have hqs : q ≫ s = c := by
    ext n z
    rfl
  let η : Functor.id C ⟶ (Functor.const C).obj T :=
    { app := fun Z => hT.from Z
      naturality := by
        intro A B f
        exact hT.hom_ext _ _ }
  let H : SSet.Homotopy (𝟙 N) (q ≫ s) := by
    rw [hqs]
    simpa only [CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy η)
  let e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj N) (SSet.toTop.obj (Δ[0] : SSet.{max u v})) :=
    { toFun := (SSet.toTop.map q).hom
      invFun := (SSet.toTop.map s).hom
      left_inv := by
        refine ⟨?_⟩
        have h := SSet.realizeHomotopy N N (𝟙 N) (q ≫ s) H
        simpa [Functor.map_comp, TopCat.hom_comp,
          Functor.map_id, TopCat.hom_id] using h.symm
      right_inv := by
        refine ⟨?_⟩
        have hsq : s ≫ q = 𝟙 (Δ[0] : SSet.{max u v}) :=
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
        simpa [← TopCat.hom_comp, ← Functor.map_comp, hsq,
          Functor.map_id, TopCat.hom_id] using
            (ContinuousMap.Homotopy.refl
              (ContinuousMap.id (SSet.toTop.obj
                (Δ[0] : SSet.{max u v})))) }
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map q)
  exact TopCat.mem_of_eq_toFun e rfl

/-- The full face is terminal among nonempty faces of a finite ordinal. -/
private def fullChain (n : SimplexCategory) :
    PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1))) where
  finset := Finset.univ
  nonempty := by simp
  comparable _ _ := le_total _ _

private noncomputable def fullChain_isTerminal (n : SimplexCategory) :
    IsTerminal (fullChain n) :=
  IsTerminal.ofUniqueHom
    (fun S => homOfLE (by
      change S.finset ⊆ Finset.univ
      exact Finset.subset_univ _))
    (by
      intro S f
      subsingleton)

private theorem stdSimplex_to_zero_mem (n : SimplexCategory) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.stdSimplex.obj n : SSet.{u})) := by
  let e : (SSet.stdSimplex.obj n : SSet.{u}) ≅
      CategoryTheory.nerve (ULift.{u} (Fin (n.len + 1))) :=
    SSet.stdSimplex.isoNerve.{u} n.len
  have hN :
      realizationWeakEquivalences
        (SSet.stdSimplex.isTerminalObj₀.from
          (CategoryTheory.nerve
            (ULift.{u} (Fin (n.len + 1))) : SSet.{u})) :=
    terminalNerveMap_mem
      (isTerminalTop :
        IsTerminal (⊤ : ULift.{u} (Fin (n.len + 1))))
  apply realizationWeakEquivalence_of_iso_square
    e.symm (Iso.refl _)
    (SSet.stdSimplex.isTerminalObj₀.from
      (CategoryTheory.nerve
        (ULift.{u} (Fin (n.len + 1))) : SSet.{u}))
    (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.obj n : SSet.{u}))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    hN

private theorem sdStdSimplex_to_zero_mem (n : SimplexCategory) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.sd.obj (SSet.stdSimplex.obj n) : SSet.{u})) := by
  have hN :
      realizationWeakEquivalences
        (SSet.stdSimplex.isTerminalObj₀.from
          (SimplexCategory.sd.{u}.obj n)) := by
    exact terminalNerveMap_mem (fullChain_isTerminal n)
  apply realizationWeakEquivalence_of_iso_square_rev
    (SSet.stdSimplex.sdIso.{u}.app n) (Iso.refl _)
    (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.sd.obj (SSet.stdSimplex.obj n) : SSet.{u}))
    (SSet.stdSimplex.isTerminalObj₀.from
      (SimplexCategory.sd.{u}.obj n))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    hN

private theorem lastVertex_stdSimplex_mem (n : SimplexCategory) :
    realizationWeakEquivalences
      (SSet.lastVertex.app
        (SSet.stdSimplex.obj n : SSet.{u})) := by
  let q := SSet.stdSimplex.isTerminalObj₀.from
    (SSet.stdSimplex.obj n : SSet.{u})
  have hq := stdSimplex_to_zero_mem n
  have hcomp :
      SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u}) ≫ q =
        SSet.stdSimplex.isTerminalObj₀.from
          (SSet.sd.obj (SSet.stdSimplex.obj n) : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply MorphismProperty.of_postcomp realizationWeakEquivalences
    (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})) q hq
  rw [hcomp]
  exact sdStdSimplex_to_zero_mem n

/-! The representable calculation propagates through the skeletal relative
cell presentation.  At each successor, the two attachment squares form a
cofibrant cube; the boundary case is the preceding stage of the same
induction applied to a standard simplex. -/

private theorem relativeCellComplex_obj_eq_skeleton
    (X : SSet.{u}) (n : ℕ) :
    (SSet.relativeCellComplex X).F.obj n =
      (X.skeleton n : SSet.{u}) := by
  change ((SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι) n :
    X.Subcomplex) : SSet.{u}) = (X.skeleton n : SSet.{u})
  congr 1
  change Subcomplex.range ((⊥ : X.Subcomplex).ι) ⊔
      X.skeleton n = X.skeleton n
  rw [show Subcomplex.range ((⊥ : X.Subcomplex).ι) = ⊥ from
    Subfunctor.range_ι _]
  exact sup_eq_right.mpr bot_le

private theorem stdSimplex_skeleton_eq_boundary (n : ℕ) :
    (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).skeleton n =
      SSet.boundary n := by
  rw [SSet.stdSimplex.eq_boundary_iff]
  constructor
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    have hd : d < n :=
      SSet.dim_lt_of_nonDegenerate
        (X := (SSet.boundary n : SSet.{u}))
        ⟨⟨x.val, hx⟩,
          (SSet.Subcomplex.mem_nonDegenerate_iff
            (A := SSet.boundary n) ⟨x.val, hx⟩).2 x.property⟩ n
    exact SSet.mem_skeleton _ _ hd
  · intro htop
    let x : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).nonDegenerate n :=
      ⟨SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌),
        SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate n⟩
    have hx : x.val ∈
        ((SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}).skeleton n).obj _ := by
      rw [htop]
      exact Set.mem_univ _
    have hlt := (SSet.mem_skeleton_obj_iff_of_nonDegenerate
      (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) x n).mp hx
    omega

private theorem relativeCellComplex_stdSimplex_stage_eq_boundary
    (n : ℕ) :
    (SSet.relativeCellComplex
        (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u})).F.obj n =
      (SSet.boundary n : SSet.{u}) := by
  rw [relativeCellComplex_obj_eq_skeleton,
    stdSimplex_skeleton_eq_boundary]

private theorem lastVertex_cofan_mem
    {ι : Type u} (A : ι → SSet.{u}) (c : Cofan A)
    (hc : IsColimit c)
    (hA : ∀ i, SSet.realizationWeakEquivalences
      (SSet.lastVertex.app (A i))) :
    SSet.realizationWeakEquivalences
      (SSet.lastVertex.app c.pt) := by
  let F : Discrete ι ⥤ SSet.{u} :=
    Discrete.functor (fun i => SSet.sd.obj (A i))
  let G : Discrete ι ⥤ SSet.{u} := Discrete.functor A
  let α : F ⟶ G :=
    Discrete.natTrans (fun i => SSet.lastVertex.app (A i.as))
  let cF : Cofan (fun i => SSet.sd.obj (A i)) :=
    Cofan.mk (SSet.sd.obj c.pt)
      (fun i => SSet.sd.map (c.inj i))
  have hcF : IsColimit cF :=
    isColimitCofanMkObjOfIsColimit
      (G := SSet.sd) (f := A) (fun i => c.inj i) hc
  apply MorphismProperty.IsStableUnderColimitsOfShape.condition
    F G cF c hcF hc α
  · intro j
    exact hA j.as
  · intro j
    exact SSet.lastVertex.naturality (c.inj j.as)

private theorem attachCells_m_mono
    {α : Type*} {A B : α → SSet.{u}}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : SSet.{u}} {f : X₁ ⟶ X₂}
    (c : AttachCells.{u} g f) (hg : ∀ a, Mono (g a)) :
    Mono c.m := by
  let F : Discrete c.ι ⥤ SSet.{u} :=
    Discrete.functor (fun i => A (c.π i))
  let G : Discrete c.ι ⥤ SSet.{u} :=
    Discrete.functor (fun i => B (c.π i))
  let β : F ⟶ G :=
    Discrete.natTrans (fun i => g (c.π i.as))
  have hβ :
      (monomorphisms SSet.{u}).functorCategory (Discrete c.ι) β := by
    intro i
    change Mono (g (c.π i.as))
    exact hg (c.π i.as)
  have hm : (monomorphisms SSet.{u}) c.m :=
    MorphismProperty.IsStableUnderColimitsOfShape.condition
      F G c.cofan₁ c.cofan₂ c.isColimit₁ c.isColimit₂
      β hβ c.m (fun j => c.hm j.as)
  simpa only [monomorphisms.iff] using hm

open scoped SSet.modelCategoryQuillen in
private theorem realizationWeakEquivalence_map_of_isPushouts
    {A B X P A' B' X' P' : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'}
    {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Mono i] [Mono i']
    (ha : realizationWeakEquivalences a)
    (hb : realizationWeakEquivalences b)
    (hc : realizationWeakEquivalences c) :
    realizationWeakEquivalences d := by
  let _ : Cofibration i :=
    SSet.modelCategoryQuillen.cofibration_of_mono i
  let _ : Cofibration i' :=
    SSet.modelCategoryQuillen.cofibration_of_mono i'
  let _ : WeakEquivalence a := by
    rw [weakEquivalence_iff]
    exact ha
  let _ : WeakEquivalence b := by
    rw [weakEquivalence_iff]
    exact hb
  let _ : WeakEquivalence c := by
    rw [weakEquivalence_iff]
    exact hc
  have hd : WeakEquivalence d :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      sq sq' hi hg hp hq
  exact (weakEquivalence_iff (f := d)).mp hd

open scoped SSet.modelCategoryQuillen in
private theorem lastVertex_stage_mem :
    ∀ (n : ℕ) (X : SSet.{u}),
      realizationWeakEquivalences
        (SSet.lastVertex.app ((SSet.relativeCellComplex X).F.obj n)) := by
  intro n
  induction n with
  | zero =>
      intro X
      have hobj :
          (SSet.relativeCellComplex X).F.obj 0 =
            ((⊥ : X.Subcomplex) : SSet.{u}) := by
        rw [relativeCellComplex_obj_eq_skeleton,
          SSet.skeleton_zero]
      let hTgt : IsInitial ((⊥ : X.Subcomplex) : SSet.{u}) :=
        SSet.Subcomplex.isInitialBot
      let hSrc : IsInitial
          (SSet.sd.obj ((⊥ : X.Subcomplex) : SSet.{u})) :=
        hTgt.isInitialObj (G := SSet.sd)
      have hIso : IsIso
          (SSet.lastVertex.app ((⊥ : X.Subcomplex) : SSet.{u})) := by
        let e := hSrc.uniqueUpToIso hTgt
        have heq :
            SSet.lastVertex.app ((⊥ : X.Subcomplex) : SSet.{u}) =
              e.hom := hSrc.hom_ext _ _
        rw [heq]
        infer_instance
      rw [hobj]
      exact realizationWeakEquivalences.of_isIso _
  | succ n ih =>
      intro X
      let c := SSet.relativeCellComplex X
      let a := c.attachCells n (by simp)
      have hBoundary :
          realizationWeakEquivalences
            (SSet.lastVertex.app (SSet.boundary n : SSet.{u})) := by
        have h := ih (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u})
        rw [relativeCellComplex_stdSimplex_stage_eq_boundary] at h
        exact h
      have hA :
          realizationWeakEquivalences
            (SSet.lastVertex.app a.cofan₁.pt) :=
        lastVertex_cofan_mem
          (fun _ : a.ι => (SSet.boundary n : SSet.{u}))
          a.cofan₁ a.isColimit₁ (fun _ => hBoundary)
      have hB :
          realizationWeakEquivalences
            (SSet.lastVertex.app a.cofan₂.pt) :=
        lastVertex_cofan_mem
          (fun _ : a.ι => (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}))
          a.cofan₂ a.isColimit₂ (fun _ => lastVertex_stdSimplex_mem ⦋n⦌)
      have hX :
          realizationWeakEquivalences
            (SSet.lastVertex.app (c.F.obj n)) := ih X
      let _ : Mono a.m :=
        attachCells_m_mono
          (A := fun _ : Unit => (SSet.boundary.{u} n : SSet.{u}))
          (B := fun _ : Unit =>
            (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}))
          (fun _ => (SSet.boundary.{u} n).ι) a
          (fun _ => inferInstance)
      let _ : Mono (SSet.sd.map a.m) := sd_map_mono a.m
      exact realizationWeakEquivalence_map_of_isPushouts
        (a.isPushout.map SSet.sd).flip a.isPushout.flip
        (SSet.lastVertex.naturality a.m)
        (SSet.lastVertex.naturality a.g₁)
        (SSet.lastVertex.naturality a.g₂)
        (SSet.lastVertex.naturality
          (c.F.map (homOfLE (Order.le_succ n))))
        hA hB hX

/-- The last-vertex map is a realization weak equivalence on every simplicial
set.  The two rows are the skeletal sequence and its subdivision; subdivision
preserves the upper colimit and the upper transition monomorphisms. -/
private theorem lastVertex_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    realizationWeakEquivalences (SSet.lastVertex.app X) := by
  let _ : PreservesColimits SSet.sd.{u} :=
    SSet.sdExAdjunction.leftAdjoint_preservesColimits
  let c := SSet.relativeCellComplex X
  let G : ℕ ⥤ SSet.{u} := c.F
  let F : ℕ ⥤ SSet.{u} := c.F ⋙ SSet.sd
  let α : F ⟶ G :=
    { app := fun n => SSet.lastVertex.app (c.F.obj n)
      naturality := fun _ _ f =>
        SSet.lastVertex.naturality (c.F.map f) }
  let cG : Cocone G := Cocone.mk X c.incl
  let cF : Cocone F := SSet.sd.mapCocone cG
  have hcG : IsColimit cG := c.isColimit
  have hcF : IsColimit cF := isColimitOfPreserves SSet.sd hcG
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    α hcF hcG (SSet.lastVertex.app X)
  · intro n
    exact SSet.lastVertex.naturality (c.incl.app n)
  · intro i j f
    let _ : Mono (c.F.map f) := by
      change Mono (SSet.Subcomplex.homOfLE
        ((SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι)).monotone
          (leOfHom f)))
      infer_instance
    exact sd_map_mono (c.F.map f)
  · intro i j f
    change Mono (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι)).monotone
        (leOfHom f)))
    infer_instance
  · intro n
    exact lastVertex_stage_mem n X

/-- The last-vertex map is a realization weak equivalence on every
simplicial set. -/
theorem lastVertex_app_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    realizationWeakEquivalences (SSet.lastVertex.app X) :=
  lastVertex_mem_realizationWeakEquivalences X

private theorem sd_map_mem_realizationWeakEquivalences
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (SSet.sd.map f) := by
  have hcomp : realizationWeakEquivalences
      (SSet.sd.map f ≫ SSet.lastVertex.app Y) := by
    rw [SSet.lastVertex.naturality]
    exact MorphismProperty.comp_mem realizationWeakEquivalences
      (SSet.lastVertex.app X) f
      (lastVertex_mem_realizationWeakEquivalences X) hf
  exact MorphismProperty.of_postcomp realizationWeakEquivalences
    (SSet.sd.map f) (SSet.lastVertex.app Y)
    (lastVertex_mem_realizationWeakEquivalences Y) hcomp

open scoped SSet.modelCategoryQuillen in
private theorem sd_map_weakEquivalence
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    WeakEquivalence (SSet.sd.map f) := by
  rw [weakEquivalence_iff] at hf ⊢
  exact sd_map_mem_realizationWeakEquivalences f hf

open scoped SSet.modelCategoryQuillen in
private theorem sd_map_cofibration
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : Cofibration f) :
    Cofibration (SSet.sd.map f) := by
  let _ : Mono f := (SSet.modelCategoryQuillen.cofibration_iff f).mp hf
  let _ : Mono (SSet.sd.map f) := sd_map_mono f
  exact SSet.modelCategoryQuillen.cofibration_of_mono _

open scoped SSet.modelCategoryQuillen in
/-- Subdivision of a cylinder.  This is an abbreviation so that its endpoint
maps reduce to the mapped endpoint maps when constructing adjoint
homotopies. -/
private noncomputable abbrev sdCylinder
    {X : SSet.{u}} (Q : Cylinder X) :
    Cylinder (SSet.sd.obj X) where
  I := SSet.sd.obj Q.I
  i₀ := SSet.sd.map Q.i₀
  i₁ := SSet.sd.map Q.i₁
  π := SSet.sd.map Q.π
  i₀_π := by rw [← SSet.sd.map_comp, Q.i₀_π, SSet.sd.map_id]
  i₁_π := by rw [← SSet.sd.map_comp, Q.i₁_π, SSet.sd.map_id]
  weakEquivalence_π := sd_map_weakEquivalence Q.π inferInstance

open scoped SSet.modelCategoryQuillen in
private theorem sdCylinder_isGood
    {X : SSet.{u}} (Q : Cylinder X) [Q.IsGood] :
    (sdCylinder Q).IsGood := by
  refine { cofibration_i := ?_ }
  change Cofibration (coprod.desc (SSet.sd.map Q.i₀) (SSet.sd.map Q.i₁))
  have hEq :
      coprod.desc (SSet.sd.map Q.i₀) (SSet.sd.map Q.i₁) =
        coprodComparison SSet.sd X X ≫ SSet.sd.map Q.i := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc, ← Category.assoc, inl_coprodComparison,
        ← SSet.sd.map_comp, Precylinder.inl_i]
    · rw [coprod.inr_desc, ← Category.assoc, inr_coprodComparison,
        ← SSet.sd.map_comp, Precylinder.inr_i]
  rw [hEq, cofibration_iff]
  exact (cofibrations SSet.{u}).comp_mem _ _
    (by rw [← cofibration_iff]; infer_instance)
    (sd_map_cofibration Q.i inferInstance).mem

open scoped SSet.modelCategoryQuillen in
/-- The subdivision--Ex adjunction descends to left-homotopy classes for a
cofibrant source and a Kan target. -/
private noncomputable def sdExLeftHomotopyClassEquiv
    (X Y : SSet.{u}) [Y.KanComplex] :
    LeftHomotopyClass (SSet.sd.obj X) Y ≃
      LeftHomotopyClass X (SSet.ex.obj Y) where
  toFun := Quot.lift
    (fun f => LeftHomotopyClass.mk
      (SSet.sdExAdjunction.homEquiv X Y f))
    (fun f g h => LeftHomotopyClass.sound (by
      obtain ⟨Q, hQ⟩ := Cylinder.exists_very_good X
      let _ : Q.IsVeryGood := hQ
      let _ : (sdCylinder Q).IsGood := sdCylinder_isGood Q
      let H := h.leftHomotopy (sdCylinder Q)
      exact ⟨Q, ⟨{
        h := SSet.sdExAdjunction.homEquiv Q.I Y H.h
        h₀ := by
          rw [← SSet.sdExAdjunction.homEquiv_naturality_left, H.h₀]
        h₁ := by
          rw [← SSet.sdExAdjunction.homEquiv_naturality_left, H.h₁] }⟩⟩))
  invFun := Quot.lift
    (fun f => LeftHomotopyClass.mk
      ((SSet.sdExAdjunction.homEquiv X Y).symm f))
    (fun f g h => LeftHomotopyClass.sound (by
      obtain ⟨Q, hQ, ⟨H⟩⟩ := h.exists_good_cylinder
      let _ : Q.IsGood := hQ
      let _ : (sdCylinder Q).IsGood := sdCylinder_isGood Q
      exact ⟨sdCylinder Q, ⟨{
        h := (SSet.sdExAdjunction.homEquiv Q.I Y).symm H.h
        h₀ := by
          rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₀]
        h₁ := by
          rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₁] }⟩⟩))
  left_inv := by
    rintro ⟨f⟩
    exact congrArg LeftHomotopyClass.mk
      ((SSet.sdExAdjunction.homEquiv X Y).symm_apply_apply f)
  right_inv := by
    rintro ⟨f⟩
    exact congrArg LeftHomotopyClass.mk
      ((SSet.sdExAdjunction.homEquiv X Y).apply_symm_apply f)

open scoped SSet.modelCategoryQuillen in
private noncomputable def leftPrecompOfFibrant
    {A X Y : SSet.{u}} [Y.KanComplex] (i : A ⟶ X) :
    LeftHomotopyClass X Y → LeftHomotopyClass A Y := fun q =>
  (leftHomotopyClassEquivRightHomotopyClass
      (X := A) (Y := Y)).symm
    ((leftHomotopyClassEquivRightHomotopyClass
      (X := X) (Y := Y) q).precomp i)

open scoped SSet.modelCategoryQuillen in
@[simp]
private theorem leftPrecompOfFibrant_mk
    {A X Y : SSet.{u}} [Y.KanComplex]
    (i : A ⟶ X) (f : X ⟶ Y) :
    leftPrecompOfFibrant i (LeftHomotopyClass.mk f) =
      LeftHomotopyClass.mk (i ≫ f) := rfl

open scoped SSet.modelCategoryQuillen in
private theorem leftPrecompOfFibrant_bijective_of_weakEquivalence
    {A X Y : SSet.{u}} [Y.KanComplex] (i : A ⟶ X)
    [WeakEquivalence i] :
    Function.Bijective (leftPrecompOfFibrant (Y := Y) i) := by
  exact (leftHomotopyClassEquivRightHomotopyClass
      (X := A) (Y := Y)).symm.bijective.comp
    ((RightHomotopyClass.precomp_bijective_of_weakEquivalence Y i).comp
      (leftHomotopyClassEquivRightHomotopyClass
        (X := X) (Y := Y)).bijective)

open scoped SSet.modelCategoryQuillen in
private theorem postcomp_exUnit_bijective_aux
    (X Y : SSet.{u}) [Y.KanComplex]
    (E : LeftHomotopyClass (SSet.sd.obj X) Y ≃
      LeftHomotopyClass X (SSet.ex.obj Y))
    (hE : ∀ (f : SSet.sd.obj X ⟶ Y),
      E (LeftHomotopyClass.mk f) =
        LeftHomotopyClass.mk (SSet.sdExAdjunction.homEquiv X Y f))
    (hpre : Function.Bijective
      (leftPrecompOfFibrant (SSet.lastVertex.app X) :
        LeftHomotopyClass X Y →
          LeftHomotopyClass (SSet.sd.obj X) Y)) :
    Function.Bijective
      (fun q : LeftHomotopyClass X Y =>
        q.postcomp (SSet.exUnit.app Y)) := by
  have hfun : (fun q : LeftHomotopyClass X Y =>
      q.postcomp (SSet.exUnit.app Y)) =
      E ∘ leftPrecompOfFibrant (SSet.lastVertex.app X) := by
    funext q
    obtain ⟨f, rfl⟩ := q.mk_surjective
    change LeftHomotopyClass.mk (f ≫ SSet.exUnit.app Y) =
      E (leftPrecompOfFibrant (SSet.lastVertex.app X)
        (LeftHomotopyClass.mk f))
    rw [leftPrecompOfFibrant_mk, hE]
    apply congrArg LeftHomotopyClass.mk
    rw [SSet.sdExAdjunction.homEquiv_naturality_right]
    exact SSet.exUnit.naturality f
  rw [hfun]
  exact E.bijective.comp hpre

open scoped SSet.modelCategoryQuillen in
private theorem postcomp_exUnit_bijective
    (X Y : SSet.{u}) [Y.KanComplex] :
    Function.Bijective
      (fun q : LeftHomotopyClass X Y =>
        q.postcomp (SSet.exUnit.app Y)) := by
  let _ : WeakEquivalence (SSet.lastVertex.app X) := by
    rw [weakEquivalence_iff]
    exact lastVertex_mem_realizationWeakEquivalences X
  exact postcomp_exUnit_bijective_aux X Y
    (sdExLeftHomotopyClassEquiv X Y)
    (fun _ => rfl)
    (leftPrecompOfFibrant_bijective_of_weakEquivalence (Y := Y)
      (SSet.lastVertex.app X))

/-! A direct recognition lemma for the fibrant-target case.  We spell out
the standard good cylinder so that a left-homotopy inverse realizes to an
actual topological homotopy equivalence; no saturation or reflection theorem
for a raw homotopy quotient is assumed. -/

private noncomputable def evalCoprodEquiv (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) :
    (X ⨿ X).obj n ≃ X.obj n ⊕ X.obj n := by
  let ev : SSet.{u} ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  exact ((PreservesColimitPair.iso ev X X).symm ≪≫
    Types.binaryCoproductIso (X.obj n) (X.obj n)).toEquiv

@[simp]
private theorem evalCoprodEquiv_inl (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    evalCoprodEquiv X n
      ((coprod.inl : X ⟶ X ⨿ X).app n x) = Sum.inl x := by
  let ev : SSet.{u} ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let e := PreservesColimitPair.iso ev X X
  have hcomp : ev.map (coprod.inl : X ⟶ X ⨿ X) ≫ e.inv =
      coprod.inl := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    change ev.map (coprod.inl : X ⟶ X ⨿ X) =
      coprod.inl ≫ coprodComparison ev X X
    exact (inl_coprodComparison ev X X).symm
  have hcat : ev.map (coprod.inl : X ⟶ X ⨿ X) ≫ e.inv ≫
      (Types.binaryCoproductIso (X.obj n) (X.obj n)).hom =
      TypeCat.ofHom Sum.inl := by
    rw [← Category.assoc, hcomp]
    exact Types.binaryCoproductIso_inl_comp_hom _ _
  exact ConcreteCategory.congr_hom hcat x

@[simp]
private theorem evalCoprodEquiv_inr (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    evalCoprodEquiv X n
      ((coprod.inr : X ⟶ X ⨿ X).app n x) = Sum.inr x := by
  let ev : SSet.{u} ⥤ Type u :=
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let e := PreservesColimitPair.iso ev X X
  have hcomp : ev.map (coprod.inr : X ⟶ X ⨿ X) ≫ e.inv =
      coprod.inr := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    change ev.map (coprod.inr : X ⟶ X ⨿ X) =
      coprod.inr ≫ coprodComparison ev X X
    exact (inr_coprodComparison ev X X).symm
  have hcat : ev.map (coprod.inr : X ⟶ X ⨿ X) ≫ e.inv ≫
      (Types.binaryCoproductIso (X.obj n) (X.obj n)).hom =
      TypeCat.ofHom Sum.inr := by
    rw [← Category.assoc, hcomp]
    exact Types.binaryCoproductIso_inr_comp_hom _ _
  exact ConcreteCategory.congr_hom hcat x

private theorem endpointCoprod_inl_app (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (coprod.desc (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))
      SSet.ι₁).app n
        ((coprod.inl : X ⟶ X ⨿ X).app n x) =
      SSet.ι₀.app n x := by
  exact congrArg (fun k : X ⟶ X ⊗ (Δ[1] : SSet.{u}) => k.app n x)
    (coprod.inl_desc (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))
      (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})))

private theorem endpointCoprod_inr_app (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (coprod.desc (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))
      SSet.ι₁).app n
        ((coprod.inr : X ⟶ X ⨿ X).app n x) =
      SSet.ι₁.app n x := by
  exact congrArg (fun k : X ⟶ X ⊗ (Δ[1] : SSet.{u}) => k.app n x)
    (coprod.inr_desc (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))
      (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})))

private theorem endpointCoprod_mono (X : SSet.{u}) :
    Mono (coprod.desc
      (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) SSet.ι₁) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  induction n using Opposite.rec
  rename_i n
  induction n using SimplexCategory.rec
  rename_i m
  rw [mono_iff_injective]
  intro a b h
  let e := evalCoprodEquiv X (Opposite.op ⦋m⦌)
  generalize ha : e a = sa
  generalize hb : e b = sb
  rcases sa with x | x <;> rcases sb with y | y
  · have ha' : a =
        (coprod.inl : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) x := by
      apply e.injective
      rw [ha, evalCoprodEquiv_inl]
    have hb' : b =
        (coprod.inl : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) y := by
      apply e.injective
      rw [hb, evalCoprodEquiv_inl]
    subst a
    subst b
    rw [endpointCoprod_inl_app, endpointCoprod_inl_app] at h
    congr 1
    have h' := congrArg Prod.fst h
    exact (SSet.ι₀_app_fst x).symm.trans
      (h'.trans (SSet.ι₀_app_fst y))
  · have ha' : a =
        (coprod.inl : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) x := by
      apply e.injective
      rw [ha, evalCoprodEquiv_inl]
    have hb' : b =
        (coprod.inr : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) y := by
      apply e.injective
      rw [hb, evalCoprodEquiv_inr]
    subst a
    subst b
    rw [endpointCoprod_inl_app, endpointCoprod_inr_app] at h
    exfalso
    have h₀₁ := congrArg (fun z => z.2 0) h
    have hx := SSet.ι₀_app_snd_apply x (0 : Fin (m + 1))
    have hy := SSet.ι₁_app_snd_apply y (0 : Fin (m + 1))
    exact Fin.zero_ne_one (hx.symm.trans (h₀₁.trans hy))
  · have ha' : a =
        (coprod.inr : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) x := by
      apply e.injective
      rw [ha, evalCoprodEquiv_inr]
    have hb' : b =
        (coprod.inl : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) y := by
      apply e.injective
      rw [hb, evalCoprodEquiv_inl]
    subst a
    subst b
    rw [endpointCoprod_inr_app, endpointCoprod_inl_app] at h
    exfalso
    have h₁₀ := congrArg (fun z => z.2 0) h
    have hx := SSet.ι₁_app_snd_apply x (0 : Fin (m + 1))
    have hy := SSet.ι₀_app_snd_apply y (0 : Fin (m + 1))
    exact Fin.zero_ne_one (hx.symm.trans (h₁₀.trans hy)).symm
  · have ha' : a =
        (coprod.inr : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) x := by
      apply e.injective
      rw [ha, evalCoprodEquiv_inr]
    have hb' : b =
        (coprod.inr : X ⟶ X ⨿ X).app (Opposite.op ⦋m⦌) y := by
      apply e.injective
      rw [hb, evalCoprodEquiv_inr]
    subst a
    subst b
    rw [endpointCoprod_inr_app, endpointCoprod_inr_app] at h
    congr 1
    have h' := congrArg Prod.fst h
    exact (SSet.ι₁_app_fst x).symm.trans
      (h'.trans (SSet.ι₁_app_fst y))

private noncomputable def whiskerLeftHomotopy
    {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (Z : SSet.{u}) :
    SSet.Homotopy (Z ◁ f) (Z ◁ g) where
  h := (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h
  h₀ := by
    change SSet.ι₀ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫
      Z ◁ H.h = Z ◁ f
    calc
      SSet.ι₀ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h =
          Z ◁ (SSet.ι₀ ≫ H.h) := rfl
      _ = Z ◁ f := by rw [H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫
      Z ◁ H.h = Z ◁ g
    calc
      SSet.ι₁ ≫ (α_ Z X (Δ[1] : SSet.{u})).hom ≫ Z ◁ H.h =
          Z ◁ (SSet.ι₁ ≫ H.h) := rfl
      _ = Z ◁ g := by rw [H.h₁]
  rel := by
    ext m ⟨⟨x, hx⟩, t⟩ <;> cases hx

private noncomputable def endpointZeroBaseHomotopy (X : SSet.{u}) :
    SSet.Homotopy
      (fst X (Δ[1] : SSet.{u}) ≫ SSet.ι₀)
      (𝟙 (X ⊗ (Δ[1] : SSet.{u}))) where
  h := (whiskerLeftHomotopy
    (SSet.stdSimplex.homotopyConstFirstId.{u} 1) X).h
  h₀ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyConstFirstId.{u} 1) X).h₀]
    ext <;> simp
  h₁ := by
    rw [(whiskerLeftHomotopy
      (SSet.stdSimplex.homotopyConstFirstId.{u} 1) X).h₁]
    simp
  rel := by
    ext m ⟨⟨x, hx⟩, t⟩ <;> cases hx

private theorem fst_interval_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (fst X (Δ[1] : SSet.{u})) := by
  let Hright : SSet.Homotopy
      (SSet.ι₀ ≫ fst X (Δ[1] : SSet.{u})) (𝟙 X) := by
    rw [SSet.ι₀_fst]
    exact SSet.RelativeMorphism.Homotopy.refl _
  let e := SSet.realizedHomotopyEquiv
    (X ⊗ (Δ[1] : SSet.{u})) X
    (fst X (Δ[1] : SSet.{u})) SSet.ι₀
    (endpointZeroBaseHomotopy X) Hright
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (fst X (Δ[1] : SSet.{u})))
  exact TopCat.mem_of_eq_toFun e rfl

open scoped SSet.modelCategoryQuillen in
private noncomputable abbrev standardCylinder (X : SSet.{u}) :
    Cylinder X where
  I := X ⊗ (Δ[1] : SSet.{u})
  i₀ := SSet.ι₀
  i₁ := SSet.ι₁
  π := fst X (Δ[1] : SSet.{u})
  i₀_π := SSet.ι₀_fst X
  i₁_π := SSet.ι₁_fst X
  weakEquivalence_π :=
    (weakEquivalence_iff _).mpr
      (fst_interval_mem_realizationWeakEquivalences X)

open scoped SSet.modelCategoryQuillen in
private theorem standardCylinder_isGood (X : SSet.{u}) :
    (standardCylinder X).IsGood := by
  refine { cofibration_i := ?_ }
  rw [SSet.modelCategoryQuillen.cofibration_iff]
  exact endpointCoprod_mono X

open scoped SSet.modelCategoryQuillen in
private noncomputable def simplicialHomotopyOfLeftHomotopyRel
    {X Y : SSet.{u}} [Y.KanComplex] {f g : X ⟶ Y}
    (h : LeftHomotopyRel f g) : SSet.Homotopy f g := by
  let _ : (standardCylinder X).IsGood := standardCylinder_isGood X
  let H := h.leftHomotopy (standardCylinder X)
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁
      rel := by
        ext n ⟨⟨x, hx⟩, t⟩
        cases hx }

open scoped SSet.modelCategoryQuillen in
private theorem realizationWeakEquivalence_of_postcomp_leftClass_bijective
    {Y Z : SSet.{u}} [Y.KanComplex] [Z.KanComplex] (f : Y ⟶ Z)
    (hpost : ∀ (X : SSet.{u}), Function.Bijective
      (fun q : LeftHomotopyClass X Y => q.postcomp f)) :
    SSet.realizationWeakEquivalences f := by
  obtain ⟨q, hq⟩ := (hpost Z).surjective
    (LeftHomotopyClass.mk (𝟙 Z))
  obtain ⟨r, rfl⟩ := q.mk_surjective
  have hrfClass :
      LeftHomotopyClass.mk (r ≫ f) =
        LeftHomotopyClass.mk (𝟙 Z) := hq
  have hrf : LeftHomotopyRel (r ≫ f) (𝟙 Z) :=
    (LeftHomotopyClass.mk_eq_mk_iff _ _).mp hrfClass
  have hfrPost :
      (LeftHomotopyClass.mk (f ≫ r)).postcomp f =
        (LeftHomotopyClass.mk (𝟙 Y)).postcomp f := by
    change LeftHomotopyClass.mk ((f ≫ r) ≫ f) =
      LeftHomotopyClass.mk ((𝟙 Y) ≫ f)
    have hpre := LeftHomotopyClass.sound (hrf.precomp f)
    simpa only [Category.assoc, Category.id_comp,
      Category.comp_id] using hpre
  have hfrClass :
      LeftHomotopyClass.mk (f ≫ r) =
        LeftHomotopyClass.mk (𝟙 Y) :=
    (hpost Y).injective hfrPost
  have hfr : LeftHomotopyRel (f ≫ r) (𝟙 Y) :=
    (LeftHomotopyClass.mk_eq_mk_iff _ _).mp hfrClass
  have hW : SSet.KanComplex.W f :=
    SSet.KanComplex.W.of_homotopy f r
      (simplicialHomotopyOfLeftHomotopyRel hfr)
      (simplicialHomotopyOfLeftHomotopyRel hrf)
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence f).mp hW

open scoped SSet.modelCategoryQuillen in
private theorem exUnit_app_mem_realizationWeakEquivalences_of_kanComplex
    (Y : SSet.{u}) [Y.KanComplex] :
    realizationWeakEquivalences (SSet.exUnit.app Y) := by
  let _ : SSet.KanComplex (SSet.ex.obj Y) := by
    change HomotopicalAlgebra.IsFibrant (SSet.ex.obj Y)
    rw [HomotopicalAlgebra.isFibrant_iff]
    have hcomp : SSet.ex.map (terminal.from Y) ≫
        terminalComparison SSet.ex.{u} =
          terminal.from (SSet.ex.obj Y) := Subsingleton.elim _ _
    rw [← hcomp]
    infer_instance
  apply realizationWeakEquivalence_of_postcomp_leftClass_bijective
    (Y := Y) (Z := SSet.ex.obj Y)
  intro X
  exact postcomp_exUnit_bijective X Y

open scoped SSet.modelCategoryQuillen in
private theorem realizationWeakEquivalence_of_precomp_rightClass_bijective
    {A B : SSet.{u}} [A.KanComplex] [B.KanComplex] (f : A ⟶ B)
    (hpre : ∀ (Z : SSet.{u}), Z.KanComplex → Function.Bijective
      (fun q : RightHomotopyClass B Z => q.precomp f)) :
    SSet.realizationWeakEquivalences f := by
  obtain ⟨q, hq⟩ := (hpre A inferInstance).surjective
    (RightHomotopyClass.mk (𝟙 A))
  obtain ⟨g, rfl⟩ := q.mk_surjective
  have hfgClass :
      RightHomotopyClass.mk (f ≫ g) =
        RightHomotopyClass.mk (𝟙 A) := hq
  have hfg : RightHomotopyRel (f ≫ g) (𝟙 A) :=
    (RightHomotopyClass.mk_eq_mk_iff _ _).mp hfgClass
  have hgfPre :
      (RightHomotopyClass.mk (g ≫ f)).precomp f =
        (RightHomotopyClass.mk (𝟙 B)).precomp f := by
    change RightHomotopyClass.mk (f ≫ (g ≫ f)) =
      RightHomotopyClass.mk (f ≫ 𝟙 B)
    have hpost := RightHomotopyClass.sound (hfg.postcomp f)
    simpa only [Category.assoc, Category.comp_id,
      Category.id_comp] using hpost
  have hgfClass :
      RightHomotopyClass.mk (g ≫ f) =
        RightHomotopyClass.mk (𝟙 B) :=
    (hpre B inferInstance).injective hgfPre
  have hgf : RightHomotopyRel (g ≫ f) (𝟙 B) :=
    (RightHomotopyClass.mk_eq_mk_iff _ _).mp hgfClass
  have hW : SSet.KanComplex.W f :=
    SSet.KanComplex.W.of_homotopy f g
      (simplicialHomotopyOfLeftHomotopyRel hfg.leftHomotopyRel)
      (simplicialHomotopyOfLeftHomotopyRel hgf.leftHomotopyRel)
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence f).mp hW

open scoped SSet.modelCategoryQuillen in
private theorem weakEquivalence_of_fibrant_resolution_precomp_bijective
    {A B RA RB : SSet.{u}} (f : A ⟶ B)
    [RA.KanComplex] [RB.KanComplex]
    (iA : A ⟶ RA) (iB : B ⟶ RB)
    [WeakEquivalence iA] [WeakEquivalence iB]
    (Rf : RA ⟶ RB) (fac : iA ≫ Rf = f ≫ iB)
    (hpre : ∀ (Z : SSet.{u}), Z.KanComplex → Function.Bijective
      (fun q : RightHomotopyClass B Z => q.precomp f)) :
    WeakEquivalence f := by
  have hRfPre : ∀ (Z : SSet.{u}), Z.KanComplex → Function.Bijective
      (fun q : RightHomotopyClass RB Z => q.precomp Rf) := by
    intro Z hZ
    let _ : Z.KanComplex := hZ
    let hA :=
      RightHomotopyClass.precomp_bijective_of_weakEquivalence Z iA
    let hB :=
      RightHomotopyClass.precomp_bijective_of_weakEquivalence Z iB
    let hf := hpre Z hZ
    have hcomm (q : RightHomotopyClass RB Z) :
        (q.precomp Rf).precomp iA =
          (q.precomp iB).precomp f := by
      obtain ⟨q, rfl⟩ := q.mk_surjective
      change RightHomotopyClass.mk (iA ≫ Rf ≫ q) =
        RightHomotopyClass.mk (f ≫ iB ≫ q)
      rw [← Category.assoc, fac, Category.assoc]
    constructor
    · intro q₀ q₁ hq
      apply hB.injective
      apply hf.injective
      change q₀.precomp Rf = q₁.precomp Rf at hq
      change (q₀.precomp iB).precomp f =
        (q₁.precomp iB).precomp f
      rw [← hcomm, ← hcomm]
      exact congrArg (fun q => q.precomp iA) hq
    · intro r
      obtain ⟨s, hs⟩ := hf.surjective (r.precomp iA)
      obtain ⟨q, hq⟩ := hB.surjective s
      change q.precomp iB = s at hq
      change s.precomp f = r.precomp iA at hs
      refine ⟨q, hA.injective ?_⟩
      rw [hcomm, hq, hs]
  let _ : WeakEquivalence Rf :=
    (weakEquivalence_iff Rf).mpr
      (realizationWeakEquivalence_of_precomp_rightClass_bijective
        Rf hRfPre)
  let _ : WeakEquivalence (f ≫ iB) := by
    rw [← fac]
    infer_instance
  exact weakEquivalence_of_postcomp f iB

open scoped SSet.modelCategoryQuillen in
private theorem weakEquivalence_of_precomp_rightClass_bijective
    {A B : SSet.{u}} (f : A ⟶ B)
    (hpre : ∀ (Z : SSet.{u}), Z.KanComplex → Function.Bijective
      (fun q : RightHomotopyClass B Z => q.precomp f)) :
    WeakEquivalence f := by
  let Ac : CofibrantObject SSet.{u} := CofibrantObject.mk A
  let Bc : CofibrantObject SSet.{u} := CofibrantObject.mk B
  let RAc : BifibrantObject SSet.{u} :=
    CofibrantObject.bifibrantResolutionObj Ac
  let RBc : BifibrantObject SSet.{u} :=
    CofibrantObject.bifibrantResolutionObj Bc
  let RA : SSet.{u} := BifibrantObject.ι.obj RAc
  let RB : SSet.{u} := BifibrantObject.ι.obj RBc
  let iA : A ⟶ RA :=
    (CofibrantObject.iBifibrantResolutionObj Ac).hom
  let iB : B ⟶ RB :=
    (CofibrantObject.iBifibrantResolutionObj Bc).hom
  let Rf : RA ⟶ RB :=
    (CofibrantObject.bifibrantResolutionMap
      (CofibrantObject.homMk f)).hom
  let _ : RA.KanComplex := by
    change IsFibrant RA
    dsimp only [RA, RAc]
    infer_instance
  let _ : RB.KanComplex := by
    change IsFibrant RB
    dsimp only [RB, RBc]
    infer_instance
  let _ : WeakEquivalence iA := by
    dsimp only [iA, RA, RAc, Ac]
    infer_instance
  let _ : WeakEquivalence iB := by
    dsimp only [iB, RB, RBc, Bc]
    infer_instance
  have fac : iA ≫ Rf = f ≫ iB := by
    exact congrArg (fun k => k.hom)
      (CofibrantObject.bifibrantResolutionMap_fac
        (CofibrantObject.homMk f))
  exact weakEquivalence_of_fibrant_resolution_precomp_bijective
    f iA iB Rf fac hpre

/-! The Ex functor maps literal simplicial homotopies to literal simplicial
homotopies.  This supplies the well-defined map on right-homotopy classes
used by the arbitrary-target recognition argument. -/

private theorem exZeroTime {X : SSet.{u}}
    (n : SimplexCategoryᵒᵖ) (z : (SSet.ex.obj X).obj n) :
    SimplexCategory.lastVertex.app n.unop ≫
        SSet.yonedaEquiv.symm ((SSet.ι₀.app n z).2) =
      SSet.const
        (SSet.stdSimplex.const 1 0 (Opposite.op ⦋0⦌)) := by
  ext d s
  apply SSet.stdSimplex.ext
  intro i
  change (0 : Fin 2) = 0
  rfl

private theorem exOneTime {X : SSet.{u}}
    (n : SimplexCategoryᵒᵖ) (z : (SSet.ex.obj X).obj n) :
    SimplexCategory.lastVertex.app n.unop ≫
        SSet.yonedaEquiv.symm ((SSet.ι₁.app n z).2) =
      SSet.const
        (SSet.stdSimplex.const 1 1 (Opposite.op ⦋0⦌)) := by
  ext d s
  apply SSet.stdSimplex.ext
  intro i
  change (1 : Fin 2) = 1
  rfl

private noncomputable def exHomotopyMap
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.ex.obj X ⊗ (Δ[1] : SSet.{u}) ⟶ SSet.ex.obj Y where
  app n := by
    refine TypeCat.ofHom fun z => ULift.up ?_
    exact lift z.1.down
      (SimplexCategory.lastVertex.app n.unop ≫
        SSet.yonedaEquiv.symm z.2) ≫ H.h
  naturality n m θ := by
    ext z
    rcases z with ⟨sigma, t⟩
    apply ULift.down_injective
    change lift (SimplexCategory.sd.map θ.unop ≫ sigma.down)
        (SimplexCategory.lastVertex.app m.unop ≫
          SSet.yonedaEquiv.symm ((Δ[1] : SSet.{u}).map θ t)) ≫ H.h =
      SimplexCategory.sd.map θ.unop ≫
        lift sigma.down
          (SimplexCategory.lastVertex.app n.unop ≫
            SSet.yonedaEquiv.symm t) ≫ H.h
    rw [← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, lift_snd]
      have ht : SSet.stdSimplex.map θ.unop ≫
          SSet.yonedaEquiv.symm t =
        SSet.yonedaEquiv.symm ((Δ[1] : SSet.{u}).map θ t) := by
        simpa using SSet.yonedaEquiv_symm_naturality_left θ.unop t
      have hlv := SimplexCategory.lastVertex.naturality θ.unop
      calc
        _ = SimplexCategory.lastVertex.app m.unop ≫
            (SSet.stdSimplex.map θ.unop ≫
              SSet.yonedaEquiv.symm t) := by rw [ht]
        _ = (SimplexCategory.lastVertex.app m.unop ≫
              SSet.stdSimplex.map θ.unop) ≫
              SSet.yonedaEquiv.symm t := by simp only [Category.assoc]
        _ = (SimplexCategory.sd.map θ.unop ≫
              SimplexCategory.lastVertex.app n.unop) ≫
              SSet.yonedaEquiv.symm t := by rw [hlv]
        _ = _ := by simp only [Category.assoc]

private noncomputable def exMapHomotopy
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.ex.map f) (SSet.ex.map g) where
  h := exHomotopyMap H
  h₀ := by
    ext n z
    apply ULift.down_injective
    change lift z.down
        (SimplexCategory.lastVertex.app n.unop ≫
          SSet.yonedaEquiv.symm ((SSet.ι₀.app n z).2)) ≫ H.h =
      z.down ≫ f
    have hlift : lift z.down
        (SimplexCategory.lastVertex.app n.unop ≫
          SSet.yonedaEquiv.symm ((SSet.ι₀.app n z).2)) =
        z.down ≫ SSet.ι₀ := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [exZeroTime]
        simp
    rw [hlift, Category.assoc, H.h₀]
  h₁ := by
    ext n z
    apply ULift.down_injective
    change lift z.down
        (SimplexCategory.lastVertex.app n.unop ≫
          SSet.yonedaEquiv.symm ((SSet.ι₁.app n z).2)) ≫ H.h =
      z.down ≫ g
    have hlift : lift z.down
        (SimplexCategory.lastVertex.app n.unop ≫
          SSet.yonedaEquiv.symm ((SSet.ι₁.app n z).2)) =
        z.down ≫ SSet.ι₁ := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [exOneTime]
        simp
    rw [hlift, Category.assoc, H.h₁]
  rel := by
    ext n ⟨⟨x, hx⟩, t⟩
    cases hx

open scoped SSet.modelCategoryQuillen in
private theorem leftHomotopyRelOfSimplicialHomotopy
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    LeftHomotopyRel f g :=
  ⟨standardCylinder X, ⟨
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁ }⟩⟩

open scoped SSet.modelCategoryQuillen in
private noncomputable def exMapRightHomotopyClass
    {X Y : SSet.{u}} [Y.KanComplex] :
    RightHomotopyClass X Y →
      RightHomotopyClass (SSet.ex.obj X) (SSet.ex.obj Y) :=
  Quot.lift (fun f => RightHomotopyClass.mk (SSet.ex.map f))
    (fun _f _g h => RightHomotopyClass.sound
      ((leftHomotopyRelOfSimplicialHomotopy
        (exMapHomotopy
          (simplicialHomotopyOfLeftHomotopyRel
            h.leftHomotopyRel))).rightHomotopyRel))

open scoped SSet.modelCategoryQuillen in
@[simp]
private theorem exMapRightHomotopyClass_mk
    {X Y : SSet.{u}} [Y.KanComplex] (f : X ⟶ Y) :
    exMapRightHomotopyClass (RightHomotopyClass.mk f) =
      RightHomotopyClass.mk (SSet.ex.map f) := rfl

open scoped SSet.modelCategoryQuillen in
private noncomputable def rightHomotopyClassPostcomp
    {X Y Z : SSet.{u}} (p : Y ⟶ Z) :
    RightHomotopyClass X Y → RightHomotopyClass X Z :=
  Quot.lift (fun f => RightHomotopyClass.mk (f ≫ p))
    (fun _f _g h => RightHomotopyClass.sound (h.postcomp p))

open scoped SSet.modelCategoryQuillen in
@[simp]
private theorem rightHomotopyClassPostcomp_mk
    {X Y Z : SSet.{u}} (p : Y ⟶ Z) (f : X ⟶ Y) :
    rightHomotopyClassPostcomp p (RightHomotopyClass.mk f) =
      RightHomotopyClass.mk (f ≫ p) := rfl

private noncomputable def simplicialHomotopyPostcomp
    {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (p : Y ⟶ Z) :
    SSet.Homotopy (f ≫ p) (g ≫ p) where
  h := H.h ≫ p
  h₀ := by
    change SSet.ι₀ ≫ (H.h ≫ p) = f ≫ p
    rw [← Category.assoc, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (H.h ≫ p) = g ≫ p
    rw [← Category.assoc, H.h₁]
  rel := by
    ext n ⟨⟨x, hx⟩, t⟩
    cases hx

open scoped SSet.modelCategoryQuillen in
private theorem exUnit_precomp_rightHomotopyClass_bijective
    (eta : Functor.id (SSet.{u}) ⟶ SSet.ex.{u})
    (doubleUnit : ∀ (T : SSet.{u}), SSet.Homotopy
      (eta.app (SSet.ex.obj T)) (SSet.ex.map (eta.app T)))
    (X Z : SSet.{u}) [Z.KanComplex] [(SSet.ex.obj Z).KanComplex]
    [WeakEquivalence (eta.app Z)] :
    Function.Bijective
      (fun q : RightHomotopyClass (SSet.ex.obj X) Z =>
        q.precomp (eta.app X)) := by
  let _ : ((Functor.id (SSet.{u})).obj Z).KanComplex := by
    change Z.KanComplex
    infer_instance
  obtain ⟨r, hetaR, _hrEta⟩ :=
    RightHomotopyClass.whitehead (eta.app Z)
  let inv : RightHomotopyClass X Z →
      RightHomotopyClass (SSet.ex.obj X) Z := fun q =>
    rightHomotopyClassPostcomp r (exMapRightHomotopyClass q)
  have hright (q : RightHomotopyClass X Z) :
      (inv q).precomp (eta.app X) = q := by
    obtain ⟨f, rfl⟩ := q.mk_surjective
    change RightHomotopyClass.mk
        ((eta.app X ≫ SSet.ex.map f) ≫ r) =
      RightHomotopyClass.mk f
    have hnat := eta.naturality f
    change f ≫ eta.app Z = eta.app X ≫ SSet.ex.map f at hnat
    calc
      RightHomotopyClass.mk ((eta.app X ≫ SSet.ex.map f) ≫ r) =
          RightHomotopyClass.mk ((f ≫ eta.app Z) ≫ r) := by
        rw [hnat]
      _ = RightHomotopyClass.mk f := by
        apply RightHomotopyClass.sound
        simpa only [Category.assoc,
          Category.comp_id] using hetaR.precomp f
  have hleft (q : RightHomotopyClass (SSet.ex.obj X) Z) :
      inv (q.precomp (eta.app X)) = q := by
    obtain ⟨g, rfl⟩ := q.mk_surjective
    change RightHomotopyClass.mk
        (SSet.ex.map (eta.app X ≫ g) ≫ r) =
      RightHomotopyClass.mk g
    rw [SSet.ex.map_comp]
    let Hpost := simplicialHomotopyPostcomp (doubleUnit X)
      (SSet.ex.map g ≫ r)
    have hdouble : RightHomotopyClass.mk
        ((SSet.ex.map (eta.app X) ≫ SSet.ex.map g) ≫ r) =
        RightHomotopyClass.mk
          ((eta.app (SSet.ex.obj X) ≫ SSet.ex.map g) ≫ r) := by
      have hraw := RightHomotopyClass.sound
        (leftHomotopyRelOfSimplicialHomotopy
          Hpost).symm.rightHomotopyRel
      simpa only [Category.assoc] using hraw
    calc
      RightHomotopyClass.mk
          ((SSet.ex.map (eta.app X) ≫ SSet.ex.map g) ≫ r) =
          RightHomotopyClass.mk
            ((eta.app (SSet.ex.obj X) ≫ SSet.ex.map g) ≫ r) :=
        hdouble
      _ = RightHomotopyClass.mk ((g ≫ eta.app Z) ≫ r) := by
        have hnat := eta.naturality g
        change g ≫ eta.app Z =
          eta.app (SSet.ex.obj X) ≫ SSet.ex.map g at hnat
        rw [hnat]
      _ = RightHomotopyClass.mk g := by
        apply RightHomotopyClass.sound
        simpa only [Category.assoc,
          Category.comp_id] using hetaR.precomp g
  constructor
  · intro q₀ q₁ hq
    change q₀.precomp (eta.app X) =
      q₁.precomp (eta.app X) at hq
    exact (hleft q₀).symm.trans
      ((congrArg inv hq).trans (hleft q₁))
  · intro q
    exact ⟨inv q, hright q⟩

end SSet

namespace SimplexCategory

private noncomputable abbrev SdV (n : SimplexCategory) :=
  ULift.{u} (Fin (n.len + 1))

private noncomputable abbrev SdC (n : SimplexCategory) :=
  PartialOrder.NonemptyFiniteChains (SdV.{u} n)

private noncomputable abbrev SdCC (n : SimplexCategory) :=
  PartialOrder.NonemptyFiniteChains (SdC.{u} n)

private noncomputable def sdOuterLast (n : SimplexCategory)
    (S : SdCC.{u} n) : SdC.{u} n :=
  (S.finset.exists_maximal S.nonempty).choose

private theorem sdOuterLast_maximal (n : SimplexCategory)
    (S : SdCC.{u} n) :
    Maximal (fun T ↦ T ∈ S.finset) (sdOuterLast n S) :=
  (S.finset.exists_maximal S.nonempty).choose_spec

private theorem le_sdOuterLast (n : SimplexCategory)
    (S : SdCC.{u} n) (T : SdC.{u} n) (hT : T ∈ S.finset) :
    T ≤ sdOuterLast n S := by
  have hLast := (sdOuterLast_maximal n S).1
  rcases S.comparable ⟨T, hT⟩ ⟨sdOuterLast n S, hLast⟩ with h | h
  · exact h
  · exact (sdOuterLast_maximal n S).2 hT h

private def sdOuterLastOrderHom (n : SimplexCategory) :
    SdCC.{u} n →o SdC.{u} n where
  toFun := sdOuterLast n
  monotone' A B h := le_sdOuterLast n B (sdOuterLast n A)
    (h (sdOuterLast_maximal n A).1)

private noncomputable abbrev sdInnerMaximaOrderHom (n : SimplexCategory) :
    SdCC.{u} n →o SdC.{u} n :=
  PartialOrder.NonemptyFiniteChains.orderHomMap (sdLastVertexOrderHom n)

private theorem sdInnerMaxima_le_outerLast (n : SimplexCategory)
    (S : SdCC.{u} n) :
    sdInnerMaximaOrderHom n S ≤ sdOuterLastOrderHom n S := by
  intro x hx
  change x ∈ (S.map (sdLastVertexOrderHom n)).finset at hx
  rw [PartialOrder.NonemptyFiniteChains.mem_map_iff] at hx
  obtain ⟨T, hT, rfl⟩ := hx
  exact le_sdOuterLast n S T hT
    (Finset.max'_mem T.finset T.nonempty)

private def sdDoubleLastNatTrans (n : SimplexCategory) :
    (sdInnerMaximaOrderHom.{u} n).toFunctor ⟶
      (sdOuterLastOrderHom.{u} n).toFunctor where
  app S := homOfLE (sdInnerMaxima_le_outerLast n S)
  naturality _ _ _ := Subsingleton.elim _ _

private noncomputable def sdDoubleLastNerveHomotopy (n : SimplexCategory) :
    SSet.Homotopy
      (nerveMap (sdInnerMaximaOrderHom.{u} n).toFunctor)
      (nerveMap (sdOuterLastOrderHom.{u} n).toFunctor) :=
  NatTrans.nerveHomotopy (sdDoubleLastNatTrans.{u} n)

private theorem sdOuterLast_map {m n : SimplexCategory} (f : m ⟶ n)
    (S : SdCC.{u} m) :
    sdOuterLast n
        (S.map (PartialOrder.NonemptyFiniteChains.orderHomMap
          ((SimplexCategory.toPartOrd.map f).hom))) =
      (PartialOrder.NonemptyFiniteChains.orderHomMap
        ((SimplexCategory.toPartOrd.map f).hom)) (sdOuterLast m S) := by
  let g : SdC.{u} m →o SdC.{u} n :=
    PartialOrder.NonemptyFiniteChains.orderHomMap
      ((SimplexCategory.toPartOrd.map f).hom)
  change sdOuterLast n (S.map g) = g (sdOuterLast m S)
  apply le_antisymm
  · have hmem := (sdOuterLast_maximal n (S.map g)).1
    change sdOuterLast n (S.map g) ∈ (S.map g).finset at hmem
    rw [PartialOrder.NonemptyFiniteChains.mem_map_iff] at hmem
    obtain ⟨T, hT, hEq⟩ := hmem
    rw [← hEq]
    exact g.monotone (le_sdOuterLast m S T hT)
  · apply le_sdOuterLast n (S.map g)
    rw [PartialOrder.NonemptyFiniteChains.mem_map_iff]
    exact ⟨sdOuterLast m S, (sdOuterLast_maximal m S).1, rfl⟩

private noncomputable abbrev sdInnerMaxima (n : SimplexCategory)
    (S : SdCC.{u} n) : SdC.{u} n :=
  S.map (sdLastVertexOrderHom n)

private theorem sdInnerMaxima_map {m n : SimplexCategory} (f : m ⟶ n)
    (S : SdCC.{u} m) :
    sdInnerMaxima n
        (S.map (PartialOrder.NonemptyFiniteChains.orderHomMap
          ((SimplexCategory.toPartOrd.map f).hom))) =
      (sdInnerMaxima m S).map
        ((SimplexCategory.toPartOrd.map f).hom) := by
  let g₀ : SdV.{u} m →o SdV.{u} n :=
    (SimplexCategory.toPartOrd.map f).hom
  let g₁ : SdC.{u} m →o SdC.{u} n :=
    PartialOrder.NonemptyFiniteChains.orderHomMap g₀
  change (S.map g₁).map (sdLastVertexOrderHom n) =
    (S.map (sdLastVertexOrderHom m)).map g₀
  ext y
  simp only [PartialOrder.NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨Tn, ⟨Tm, hTm, rfl⟩, rfl⟩
    exact ⟨sdChainLast m Tm, ⟨Tm, hTm, rfl⟩,
      (sdChainLast_map f Tm).symm⟩
  · rintro ⟨x, ⟨Tm, hTm, hx⟩, hxy⟩
    subst x
    exact ⟨Tm.map g₀, ⟨Tm, hTm, rfl⟩,
      (sdChainLast_map f Tm).trans hxy⟩

private noncomputable def sdSdRepresentableIso (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj n)) ≅
      PartOrd.nerveFunctor.obj (PartOrd.of (SdCC.{u} n)) := by
  let _ : (SimplexCategory.sd.{u}.obj n).Nonsingular := by
    change (CategoryTheory.nerve (SdC.{u} n)).Nonsingular
    infer_instance
  exact SSet.sd.mapIso (SSet.stdSimplex.sdIso.app n) ≪≫
    SSet.sdIsoNondegenerateNerve (SimplexCategory.sd.{u}.obj n) ≪≫
    PartOrd.nerveFunctor.mapIso
      (PartOrd.Iso.mk
        (PartOrd.nerveNOrderIso
          (PartOrd.nonemptyFiniteChainsFunctor.obj
            (SimplexCategory.toPartOrd.obj n))))

end SimplexCategory


open CartesianMonoidalCategory MonoidalCategory

namespace SSet

private noncomputable def sdSdRepresentableMap
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      PartOrd.nerveFunctor.{u}.obj
        (PartOrd.of (SimplexCategory.SdCC.{u} n)) :=
  SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫
    SSet.sdToNondegenerateNerve.app
      (SimplexCategory.sd.{u}.obj n) ≫
    PartOrd.nerveFunctor.{u}.map
      (PartOrd.Iso.mk
        (PartOrd.nerveNOrderIso
          (PartOrd.nonemptyFiniteChainsFunctor.obj
            (SimplexCategory.toPartOrd.obj n)))).hom

private noncomputable def representableDoubleLastInner
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      SSet.sd.obj (SSet.stdSimplex.{u}.obj n) :=
  sdSdRepresentableMap n ≫
    CategoryTheory.nerveMap
      (SimplexCategory.sdInnerMaximaOrderHom.{u} n).toFunctor ≫
    SSet.stdSimplex.sdIso.inv.app n

private noncomputable def representableDoubleLastOuter
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      SSet.sd.obj (SSet.stdSimplex.{u}.obj n) :=
  sdSdRepresentableMap n ≫
    CategoryTheory.nerveMap
      (SimplexCategory.sdOuterLastOrderHom.{u} n).toFunctor ≫
    SSet.stdSimplex.sdIso.inv.app n

private noncomputable abbrev sdFaceMap
    {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.SdC.{u} m →o SimplexCategory.SdC.{u} n :=
  PartialOrder.NonemptyFiniteChains.orderHomMap
    ((SimplexCategory.toPartOrd.map f).hom)

private noncomputable abbrev sdDoubleFaceMap
    {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.SdCC.{u} m →o SimplexCategory.SdCC.{u} n :=
  PartialOrder.NonemptyFiniteChains.orderHomMap (sdFaceMap f)

private theorem sdSdRepresentableMap_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
        sdSdRepresentableMap n =
      sdSdRepresentableMap m ≫
        PartOrd.nerveFunctor.{u}.map
          (PartOrd.ofHom (sdDoubleFaceMap f)) := by
  have hA := SSet.stdSimplex.sdIso.hom.naturality f
  have hAA := congrArg SSet.sd.map hA
  simp only [Functor.map_comp] at hAA
  have hAA' :
      SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
          SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) =
        SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
          SSet.sd.map (SimplexCategory.sd.{u}.map f) := by
    simpa using hAA
  have hB := SSet.sdToNondegenerateNerve.naturality
    (SimplexCategory.sd.{u}.map f)
  have hC0 :=
    PartOrd.nerveFunctorCompNFunctorIso.{u}.hom.naturality
      (PartOrd.ofHom (sdFaceMap f))
  have hC := congrArg PartOrd.nerveFunctor.map hC0
  simp only [Functor.map_comp] at hC
  change SSet.nondegenerateNerve.map
      (SimplexCategory.sd.{u}.map f) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso
              (PartOrd.nonemptyFiniteChainsFunctor.obj
                (SimplexCategory.toPartOrd.obj n)))).hom =
    PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso
              (PartOrd.nonemptyFiniteChainsFunctor.obj
                (SimplexCategory.toPartOrd.obj m)))).hom ≫
      PartOrd.nerveFunctor.map
        (PartOrd.ofHom (sdDoubleFaceMap f)) at hC
  have hComp :
      SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
          (SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫
            SSet.sdToNondegenerateNerve.app
              (SimplexCategory.sd.{u}.obj n) ≫
            PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj n)))).hom) =
        SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
          SSet.sdToNondegenerateNerve.app
              (SimplexCategory.sd.{u}.obj m) ≫
          (PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj m)))).hom ≫
            PartOrd.nerveFunctor.map
              (PartOrd.ofHom (sdDoubleFaceMap f))) := by
    calc
      _ = (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
              SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n)) ≫
            SSet.sdToNondegenerateNerve.app
              (SimplexCategory.sd.{u}.obj n) ≫
            PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj n)))).hom := by
          cat_disch
      _ = (SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
              SSet.sd.map (SimplexCategory.sd.{u}.map f)) ≫
            SSet.sdToNondegenerateNerve.app
              (SimplexCategory.sd.{u}.obj n) ≫
            PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj n)))).hom := by
          rw [hAA']
      _ = SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
            (SSet.sd.map (SimplexCategory.sd.{u}.map f) ≫
              SSet.sdToNondegenerateNerve.app
                (SimplexCategory.sd.{u}.obj n)) ≫
            PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj n)))).hom := by
          cat_disch
      _ = SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
            (SSet.sdToNondegenerateNerve.app
                (SimplexCategory.sd.{u}.obj m) ≫
              SSet.nondegenerateNerve.map
                (SimplexCategory.sd.{u}.map f)) ≫
            PartOrd.nerveFunctor.map
              (PartOrd.Iso.mk
                (PartOrd.nerveNOrderIso
                  (PartOrd.nonemptyFiniteChainsFunctor.obj
                    (SimplexCategory.toPartOrd.obj n)))).hom := by
          rw [hB]
      _ = SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
            SSet.sdToNondegenerateNerve.app
                (SimplexCategory.sd.{u}.obj m) ≫
            (SSet.nondegenerateNerve.map
                (SimplexCategory.sd.{u}.map f) ≫
              PartOrd.nerveFunctor.map
                (PartOrd.Iso.mk
                  (PartOrd.nerveNOrderIso
                    (PartOrd.nonemptyFiniteChainsFunctor.obj
                      (SimplexCategory.toPartOrd.obj n)))).hom) := by
          cat_disch
      _ = SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
            SSet.sdToNondegenerateNerve.app
                (SimplexCategory.sd.{u}.obj m) ≫
            (PartOrd.nerveFunctor.map
                (PartOrd.Iso.mk
                  (PartOrd.nerveNOrderIso
                    (PartOrd.nonemptyFiniteChainsFunctor.obj
                      (SimplexCategory.toPartOrd.obj m)))).hom ≫
              PartOrd.nerveFunctor.map
        (PartOrd.ofHom (sdDoubleFaceMap f))) := by
          rw [hC]
          rfl
  simpa only [sdSdRepresentableMap, Category.assoc] using! hComp

private lemma iotaZero_whiskerRight (n : SimplexCategory) :
    SSet.ι₀ ≫
        (sdSdRepresentableMap n ▷
          (Δ[1] : SSet.{u})) =
      sdSdRepresentableMap n ≫
        SSet.ι₀ := by
  rfl

private lemma iotaOne_whiskerRight (n : SimplexCategory) :
    SSet.ι₁ ≫
        (sdSdRepresentableMap n ▷
          (Δ[1] : SSet.{u})) =
      sdSdRepresentableMap n ≫
        SSet.ι₁ := by
  rfl

private noncomputable def representableDoubleLastHomotopy
    (n : SimplexCategory) :
    SSet.Homotopy
      (representableDoubleLastInner n)
      (representableDoubleLastOuter n) where
  h := (sdSdRepresentableMap n ▷
      (Δ[1] : SSet.{u})) ≫
    (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h ≫
    SSet.stdSimplex.sdIso.inv.app n
  h₀ := by
    rw [← Category.assoc, iotaZero_whiskerRight]
    simp only [Category.assoc]
    rfl
  h₁ := by
    rw [← Category.assoc, iotaOne_whiskerRight]
    simp only [Category.assoc]
    rfl
  rel := by
    ext d x
    exact x.1.2.elim

private theorem sdDoubleLastNerveHomotopy_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    (PartOrd.nerveFunctor.{u}.map
          (PartOrd.ofHom (sdDoubleFaceMap f)) ▷
        (Δ[1] : SSet.{u})) ≫
        (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h =
      (SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫
        PartOrd.nerveFunctor.{u}.map
          (PartOrd.ofHom (sdFaceMap f)) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext _ _
  rintro ⟨S, t⟩
  dsimp [SimplexCategory.sdDoubleLastNerveHomotopy,
    CategoryTheory.NatTrans.nerveHomotopy,
    CategoryTheory.NatTrans.nerveHomotopyMap,
    CategoryTheory.NatTrans.nerveCylinderFunctor]
  let T : Fin (d.unop.len + 1) ⥤ Fin 2 :=
    (SSet.stdSimplex.asOrderHom t).toFunctor
  change
    ((CategoryTheory.NatTrans.nerveCylinderFunctor
        (SimplexCategory.sdDoubleLastNatTrans.{u} n)).mapComposableArrows _).obj
      ((((sdDoubleFaceMap f).toFunctor.mapComposableArrows _).obj S).prod' T) =
    ((sdFaceMap f).toFunctor.mapComposableArrows _).obj
      (((CategoryTheory.NatTrans.nerveCylinderFunctor
        (SimplexCategory.sdDoubleLastNatTrans.{u} m)).mapComposableArrows _).obj
          (S.prod' T))
  let Fout :=
    ((CategoryTheory.NatTrans.nerveCylinderFunctor
        (SimplexCategory.sdDoubleLastNatTrans.{u} n)).mapComposableArrows _).obj
      ((((sdDoubleFaceMap f).toFunctor.mapComposableArrows _).obj S).prod' T)
  let Gout :=
    ((sdFaceMap f).toFunctor.mapComposableArrows _).obj
      (((CategoryTheory.NatTrans.nerveCylinderFunctor
        (SimplexCategory.sdDoubleLastNatTrans.{u} m)).mapComposableArrows _).obj
          (S.prod' T))
  change Fout = Gout
  have hobj (i) : Fout.obj i = Gout.obj i := by
    change (CategoryTheory.NatTrans.nerveCylinderFunctor
          (SimplexCategory.sdDoubleLastNatTrans.{u} n)).obj
          (sdDoubleFaceMap f (S.obj i), T.obj i) =
      sdFaceMap f
        ((CategoryTheory.NatTrans.nerveCylinderFunctor
          (SimplexCategory.sdDoubleLastNatTrans.{u} m)).obj
            (S.obj i, T.obj i))
    generalize hi : T.obj i = k
    fin_cases k
    · change SimplexCategory.sdInnerMaxima n
          (sdDoubleFaceMap f (S.obj i)) =
        (SimplexCategory.sdInnerMaxima m (S.obj i)).map
          ((SimplexCategory.toPartOrd.map f).hom)
      exact SimplexCategory.sdInnerMaxima_map f (S.obj i)
    · change SimplexCategory.sdOuterLast n
          (sdDoubleFaceMap f (S.obj i)) =
        (SimplexCategory.sdOuterLast m (S.obj i)).map
          ((SimplexCategory.toPartOrd.map f).hom)
      exact SimplexCategory.sdOuterLast_map f (S.obj i)
  exact CategoryTheory.Functor.hext hobj (fun i j g =>
    Subsingleton.helim
      (congrArg₂ (fun A B => A ⟶ B) (hobj i) (hobj j)) _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem representableDoubleLastHomotopy_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫
        (representableDoubleLastHomotopy n).h =
      (representableDoubleLastHomotopy m).h ≫
        SSet.sd.map (SSet.stdSimplex.map f) := by
  have hMap := sdSdRepresentableMap_naturality f
  have hMapI := congrArg
    (fun k => k ▷ (Δ[1] : SSet.{u})) hMap
  simp only [comp_whiskerRight] at hMapI
  have hCore := sdDoubleLastNerveHomotopy_naturality f
  have hInv := SSet.stdSimplex.sdIso.inv.naturality f
  have hInv' : SimplexCategory.sd.{u}.map f ≫
        SSet.stdSimplex.sdIso.inv.app n =
      SSet.stdSimplex.sdIso.inv.app m ≫
        SSet.sd.map (SSet.stdSimplex.map f) := by
    simpa only [Functor.comp_map] using hInv
  have hSdMap : SimplexCategory.sd.{u}.map f =
      PartOrd.nerveFunctor.{u}.map
        (PartOrd.ofHom (sdFaceMap f)) := by
    rfl
  have hCore' :
      (PartOrd.nerveFunctor.{u}.map
            (PartOrd.ofHom (sdDoubleFaceMap f)) ▷
          (Δ[1] : SSet.{u})) ≫
          (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h =
        (SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫
          SimplexCategory.sd.{u}.map f := by
    rw [hCore, ← hSdMap]
  dsimp only [representableDoubleLastHomotopy]
  calc
    _ = ((SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
              (Δ[1] : SSet.{u})) ≫
            (sdSdRepresentableMap n ▷ (Δ[1] : SSet.{u}))) ≫
          (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h ≫
          SSet.stdSimplex.sdIso.inv.app n := by cat_disch
    _ = ((sdSdRepresentableMap m ▷ (Δ[1] : SSet.{u})) ≫
            (PartOrd.nerveFunctor.{u}.map
                (PartOrd.ofHom (sdDoubleFaceMap f)) ▷
              (Δ[1] : SSet.{u}))) ≫
          (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h ≫
          SSet.stdSimplex.sdIso.inv.app n := by rw [hMapI]
    _ = (sdSdRepresentableMap m ▷ (Δ[1] : SSet.{u})) ≫
          ((PartOrd.nerveFunctor.{u}.map
                (PartOrd.ofHom (sdDoubleFaceMap f)) ▷
              (Δ[1] : SSet.{u})) ≫
            (SimplexCategory.sdDoubleLastNerveHomotopy.{u} n).h) ≫
          SSet.stdSimplex.sdIso.inv.app n := by cat_disch
    _ = (sdSdRepresentableMap m ▷ (Δ[1] : SSet.{u})) ≫
          ((SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫
            SimplexCategory.sd.{u}.map f) ≫
          SSet.stdSimplex.sdIso.inv.app n := by
          simpa only [Category.assoc] using congrArg
            (fun k => (sdSdRepresentableMap m ▷
                (Δ[1] : SSet.{u})) ≫ k ≫
              SSet.stdSimplex.sdIso.inv.app n) hCore'
    _ = (sdSdRepresentableMap m ▷ (Δ[1] : SSet.{u})) ≫
          (SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫
          (SimplexCategory.sd.{u}.map f ≫
            SSet.stdSimplex.sdIso.inv.app n) := by cat_disch
    _ = (sdSdRepresentableMap m ▷ (Δ[1] : SSet.{u})) ≫
          (SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫
          (SSet.stdSimplex.sdIso.inv.app m ≫
            SSet.sd.map (SSet.stdSimplex.map f)) := by
          simpa only [Category.assoc] using congrArg
            (fun k => (sdSdRepresentableMap m ▷
                (Δ[1] : SSet.{u})) ≫
              (SimplexCategory.sdDoubleLastNerveHomotopy.{u} m).h ≫ k)
            hInv'
    _ = _ := by cat_disch

private noncomputable def doubleInterval
    (n : SimplexCategory) (t : (Δ[1] : SSet.{u}).obj (op n)) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      (Δ[1] : SSet.{u}) :=
  SSet.lastVertex.app
      (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ≫
    SSet.lastVertex.app (SSet.stdSimplex.{u}.obj n) ≫
    SSet.yonedaEquiv.symm t

private theorem doubleInterval_naturality
    {m n : SimplexCategory} (f : m ⟶ n)
    (t : (Δ[1] : SSet.{u}).obj (op n)) :
    SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
        doubleInterval n t =
      doubleInterval m ((Δ[1] : SSet.{u}).map f.op t) := by
  unfold doubleInterval
  rw [reassoc_of% SSet.lastVertex.naturality
    (SSet.sd.map (SSet.stdSimplex.map f))]
  rw [reassoc_of% SSet.lastVertex.naturality
    (SSet.stdSimplex.map f)]
  rw [SSet.yonedaEquiv_symm_naturality_left]

private theorem ex_obj_map_down
    (X : SSet.{u}) {m n : SimplexCategory} (f : m ⟶ n)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    ULift.down ((SSet.ex.obj X).map f.op sigma) =
      SimplexCategory.sd.map f ≫ ULift.down sigma := by
  rfl

private noncomputable def doubleMate
    (X : SSet.{u}) (n : SimplexCategory)
    (q : SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj n)) ⟶ X) :
    SSet.stdSimplex.obj n ⟶ SSet.ex.obj (SSet.ex.obj X) :=
  (SSet.sdExAdjunction.homEquiv
    (SSet.stdSimplex.obj n) (SSet.ex.obj X))
    ((SSet.sdExAdjunction.homEquiv
      (SSet.sd.obj (SSet.stdSimplex.obj n)) X) q)

private theorem doubleMate_naturality
    (X : SSet.{u}) {m n : SimplexCategory} (f : m ⟶ n)
    (q : SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj n)) ⟶ X) :
    SSet.stdSimplex.map f ≫ doubleMate X n q =
      doubleMate X m
        (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫ q) := by
  rw [doubleMate, ← SSet.sdExAdjunction.homEquiv_naturality_left]
  rw [doubleMate]
  congr 1
  rw [← SSet.sdExAdjunction.homEquiv_naturality_left]

set_option backward.isDefEq.respectTransparency false in
private theorem outerMate_yoneda_down
    (Y : SSet.{u}) (n : SimplexCategory)
    (r : SSet.sd.obj (SSet.stdSimplex.obj n) ⟶ Y) :
    ULift.down
        (SSet.yonedaEquiv
          ((SSet.sdExAdjunction.homEquiv
            (SSet.stdSimplex.obj n) Y) r)) =
      SSet.stdSimplex.sdIso.inv.app n ≫ r := by
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
      SSet.sd.{u} α hα (SSet.stdSimplex.obj n) Y r
      (Opposite.op n) (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))
  have happ' :
      SSet.yonedaEquiv
          ((SSet.sdExAdjunction.homEquiv
            (SSet.stdSimplex.obj n) Y) r) =
        ULift.up
          (SSet.stdSimplex.sdIso.inv.app n ≫
            SSet.sd.map
              (SSet.yonedaEquiv.symm
                (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n)))) ≫ r) := by
    simpa only [α, SSet.sdExAdjunction, SSet.ex, SSet.sd,
      SSet.yonedaEquiv] using! happ
  have hdown := congrArg ULift.down happ'
  have hdown' :
      ULift.down
          (SSet.yonedaEquiv
            ((SSet.sdExAdjunction.homEquiv
              (SSet.stdSimplex.obj n) Y) r)) =
        SSet.stdSimplex.sdIso.inv.app n ≫
          SSet.sd.map (𝟙 (SSet.stdSimplex.obj n)) ≫ r := by
    simpa only [Equiv.symm_apply_apply] using hdown
  calc
    _ = SSet.stdSimplex.sdIso.inv.app n ≫
        SSet.sd.map (𝟙 (SSet.stdSimplex.obj n)) ≫ r := hdown'
    _ = _ := by
      rw [SSet.sd.map_id]
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ r)
        (Category.comp_id (SSet.stdSimplex.sdIso.inv.app n))

set_option backward.isDefEq.respectTransparency false in
private theorem singleMate
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    (SSet.sdExAdjunction.homEquiv
      (SSet.stdSimplex.obj n) X)
        ((SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma) =
      SSet.yonedaEquiv.symm sigma := by
  apply SSet.yonedaEquiv.injective
  apply ULift.down_injective
  rw [outerMate_yoneda_down, Equiv.apply_symm_apply]
  exact Iso.inv_hom_id_assoc (SSet.stdSimplex.sdIso.app n)
    (ULift.down sigma)

private abbrev DoubleLastHomotopyFamily := ∀ n : SimplexCategory,
  SSet.Homotopy
    (SSet.sd.map
      (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})))
    (SSet.lastVertex.app
      (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})))

private noncomputable def qOf
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (z : (SSet.ex.obj X ⊗ (Δ[1] : SSet.{u})).obj (op n)) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj n)) ⟶ X :=
  lift (𝟙 _) (doubleInterval n z.2) ≫
    (H n).h ≫
      (SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down z.1

set_option backward.isDefEq.respectTransparency false in
private theorem qOf_naturality
    (H : DoubleLastHomotopyFamily.{u})
    (HchartNat : ∀ {m n : SimplexCategory} (f : m ⟶ n),
      (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫ (H n).h ≫
            (SSet.stdSimplex.sdIso.app n).hom =
        (H m).h ≫ (SSet.stdSimplex.sdIso.app m).hom ≫
          SimplexCategory.sd.map f)
    (X : SSet.{u}) {m n : SimplexCategory} (f : m ⟶ n)
    (z : (SSet.ex.obj X ⊗ (Δ[1] : SSet.{u})).obj (op n)) :
    SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
        qOf H X n z =
      qOf H X m
        ((SSet.ex.obj X ⊗ (Δ[1] : SSet.{u})).map f.op z) := by
  rcases z with ⟨sigma, t⟩
  change SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ≫
        qOf H X n ⟨sigma, t⟩ =
      qOf H X m
        ⟨(SSet.ex.obj X).map f.op sigma,
          (Δ[1] : SSet.{u}).map f.op t⟩
  let ff := SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f))
  have hlift :
      ff ≫ lift (𝟙 _) (doubleInterval n t) =
        lift (𝟙 _) (doubleInterval m
          ((Δ[1] : SSet.{u}).map f.op t)) ≫
            (ff ▷ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [ff]
    · simp only [Category.assoc, lift_snd, whiskerRight_snd]
      rw [← doubleInterval_naturality f t]
  unfold qOf
  rw [reassoc_of% hlift]
  rw [reassoc_of% HchartNat f]
  rw [ex_obj_map_down]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def packagedMap
    (H : DoubleLastHomotopyFamily.{u})
    (HchartNat : ∀ {m n : SimplexCategory} (f : m ⟶ n),
      (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫ (H n).h ≫
            (SSet.stdSimplex.sdIso.app n).hom =
        (H m).h ≫ (SSet.stdSimplex.sdIso.app m).hom ≫
          SimplexCategory.sd.map f)
    (X : SSet.{u}) :
    SSet.ex.obj X ⊗ (Δ[1] : SSet.{u}) ⟶
      SSet.ex.obj (SSet.ex.obj X) where
  app n := TypeCat.ofHom fun z =>
    SSet.yonedaEquiv
      (doubleMate X n.unop (qOf H X n.unop z))
  naturality n m f := by
    ext z
    change SSet.yonedaEquiv
        (doubleMate X m.unop
          (qOf H X m.unop
            ((SSet.ex.obj X ⊗ (Δ[1] : SSet.{u})).map f z))) =
      (SSet.ex.obj (SSet.ex.obj X)).map f
        (SSet.yonedaEquiv
          (doubleMate X n.unop (qOf H X n.unop z)))
    have hmap :
        (SSet.ex.obj (SSet.ex.obj X)).map f
            (SSet.yonedaEquiv
              (doubleMate X n.unop (qOf H X n.unop z))) =
          SSet.yonedaEquiv
            (SSet.stdSimplex.map f.unop ≫
              doubleMate X n.unop (qOf H X n.unop z)) := by
      simpa using SSet.yonedaEquiv_naturality f.unop
        (doubleMate X n.unop (qOf H X n.unop z))
    rw [hmap]
    congr 1
    rw [doubleMate_naturality]
    congr 1
    simpa using (qOf_naturality H HchartNat X f.unop z).symm

private theorem doubleInterval_zero
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    doubleInterval n ((SSet.ι₀.app (op n) sigma).2) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.{u}.symm 0) := by
  ext d s
  apply SSet.stdSimplex.ext
  intro i
  change (0 : Fin 2) = 0
  rfl

private theorem doubleInterval_one
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    doubleInterval n ((SSet.ι₁.app (op n) sigma).2) =
      SSet.const (SSet.stdSimplex.obj₀Equiv.{u}.symm 1) := by
  ext d s
  apply SSet.stdSimplex.ext
  intro i
  change (1 : Fin 2) = 1
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem qOf_zero
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    qOf H X n (SSet.ι₀.app (op n) sigma) =
      SSet.sd.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})) ≫
        (SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma := by
  unfold qOf
  rw [doubleInterval_zero X n sigma]
  change SSet.ι₀ ≫ (H n).h ≫
      (SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma = _
  rw [← Category.assoc, (H n).h₀]

set_option backward.isDefEq.respectTransparency false in
private theorem qOf_one
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    qOf H X n (SSet.ι₁.app (op n) sigma) =
      SSet.lastVertex.app
          (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})) ≫
        (SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma := by
  unfold qOf
  rw [doubleInterval_one X n sigma]
  change SSet.ι₁ ≫ (H n).h ≫
      (SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma = _
  rw [← Category.assoc, (H n).h₁]

set_option backward.isDefEq.respectTransparency false in
private theorem innerMate_zero
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    (SSet.sdExAdjunction.homEquiv
      (SSet.sd.obj (SSet.stdSimplex.obj n)) X)
        (qOf H X n (SSet.ι₀.app (op n) sigma)) =
      SSet.lastVertex.app (SSet.stdSimplex.obj n) ≫
        SSet.yonedaEquiv.symm sigma := by
  rw [qOf_zero]
  rw [SSet.sdExAdjunction.homEquiv_naturality_left]
  exact congrArg
    (fun k => SSet.lastVertex.app (SSet.stdSimplex.obj n) ≫ k)
    (singleMate X n sigma)

set_option backward.isDefEq.respectTransparency false in
private theorem innerMate_one
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    (SSet.sdExAdjunction.homEquiv
      (SSet.sd.obj (SSet.stdSimplex.obj n)) X)
        (qOf H X n (SSet.ι₁.app (op n) sigma)) =
      ((SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma) ≫
        SSet.exUnit.app X := by
  rw [qOf_one]
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  change SSet.exUnit.app (SSet.sd.obj (SSet.stdSimplex.obj n)) ≫
      SSet.ex.map
        ((SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma) = _
  exact (SSet.exUnit.naturality
    ((SSet.stdSimplex.sdIso.app n).hom ≫ ULift.down sigma)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem doubleMate_zero
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    doubleMate X n (qOf H X n (SSet.ι₀.app (op n) sigma)) =
      SSet.yonedaEquiv.symm sigma ≫
        SSet.exUnit.app (SSet.ex.obj X) := by
  unfold doubleMate
  rw [innerMate_zero]
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  change SSet.exUnit.app (SSet.stdSimplex.obj n) ≫
      SSet.ex.map (SSet.yonedaEquiv.symm sigma) = _
  exact (SSet.exUnit.naturality (SSet.yonedaEquiv.symm sigma)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem doubleMate_one
    (H : DoubleLastHomotopyFamily.{u})
    (X : SSet.{u}) (n : SimplexCategory)
    (sigma : (SSet.ex.obj X).obj (op n)) :
    doubleMate X n (qOf H X n (SSet.ι₁.app (op n) sigma)) =
      SSet.yonedaEquiv.symm sigma ≫
        SSet.ex.map (SSet.exUnit.app X) := by
  unfold doubleMate
  rw [innerMate_one]
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  rw [singleMate]

set_option backward.isDefEq.respectTransparency false in
private theorem packagedMap_zero
    (H : DoubleLastHomotopyFamily.{u})
    (HchartNat : ∀ {m n : SimplexCategory} (f : m ⟶ n),
      (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫ (H n).h ≫
            (SSet.stdSimplex.sdIso.app n).hom =
        (H m).h ≫ (SSet.stdSimplex.sdIso.app m).hom ≫
          SimplexCategory.sd.map f)
    (X : SSet.{u}) :
    SSet.ι₀ ≫ packagedMap H HchartNat X =
      SSet.exUnit.app (SSet.ex.obj X) := by
  ext n sigma
  induction n using Opposite.rec
  rename_i n
  change SSet.yonedaEquiv
      (doubleMate X n
        (qOf H X n (SSet.ι₀.app (op n) sigma))) = _
  rw [doubleMate_zero, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem packagedMap_one
    (H : DoubleLastHomotopyFamily.{u})
    (HchartNat : ∀ {m n : SimplexCategory} (f : m ⟶ n),
      (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫ (H n).h ≫
            (SSet.stdSimplex.sdIso.app n).hom =
        (H m).h ≫ (SSet.stdSimplex.sdIso.app m).hom ≫
          SimplexCategory.sd.map f)
    (X : SSet.{u}) :
    SSet.ι₁ ≫ packagedMap H HchartNat X =
      SSet.ex.map (SSet.exUnit.app X) := by
  ext n sigma
  induction n using Opposite.rec
  rename_i n
  change SSet.yonedaEquiv
      (doubleMate X n
        (qOf H X n (SSet.ι₁.app (op n) sigma))) = _
  rw [doubleMate_one, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply]
  rfl

private noncomputable def packagedHomotopy
    (H : DoubleLastHomotopyFamily.{u})
    (HchartNat : ∀ {m n : SimplexCategory} (f : m ⟶ n),
      (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫ (H n).h ≫
            (SSet.stdSimplex.sdIso.app n).hom =
        (H m).h ≫ (SSet.stdSimplex.sdIso.app m).hom ≫
          SimplexCategory.sd.map f)
    (X : SSet.{u}) :
    SSet.Homotopy (SSet.exUnit.app (SSet.ex.obj X))
      (SSet.ex.map (SSet.exUnit.app X)) where
  h := packagedMap H HchartNat X
  h₀ := packagedMap_zero H HchartNat X
  h₁ := packagedMap_one H HchartNat X
  rel := by
    ext n ⟨⟨x, hx⟩, t⟩
    cases hx


end SSet

namespace SimplexCategory

private noncomputable abbrev ProbeSdV (n : SimplexCategory) :=
  ULift.{u} (Fin (n.len + 1))

private noncomputable abbrev ProbeSdC (n : SimplexCategory) :=
  PartialOrder.NonemptyFiniteChains (ProbeSdV.{u} n)

private noncomputable abbrev ProbeSdCC (n : SimplexCategory) :=
  PartialOrder.NonemptyFiniteChains (ProbeSdC.{u} n)

private noncomputable abbrev probeLastVertexOrderHom
    (n : SimplexCategory) :
    (PartOrd.nonemptyFiniteChainsFunctor.obj
        (SimplexCategory.toPartOrd.obj n) : Type u) →o
      (SimplexCategory.toPartOrd.obj n : Type u) :=
  sdLastVertexOrderHom n

private noncomputable abbrev probeLastNerveMap
    (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶
      CategoryTheory.nerve (ULift.{u} (Fin (n.len + 1))) :=
  PartOrd.nerveFunctor.map
    (PartOrd.ofHom (probeLastVertexOrderHom n))

private noncomputable abbrev probeSdInnerMaximaOrderHom
    (n : SimplexCategory) :
    ProbeSdCC.{u} n →o ProbeSdC.{u} n :=
  PartialOrder.NonemptyFiniteChains.orderHomMap (sdLastVertexOrderHom n)

private noncomputable def probeSdOuterLast (n : SimplexCategory)
    (S : ProbeSdCC.{u} n) : ProbeSdC.{u} n :=
  (S.finset.exists_maximal S.nonempty).choose

private theorem probeSdOuterLast_maximal (n : SimplexCategory)
    (S : ProbeSdCC.{u} n) :
    Maximal (fun T ↦ T ∈ S.finset) (probeSdOuterLast n S) :=
  (S.finset.exists_maximal S.nonempty).choose_spec

private theorem probeLe_sdOuterLast (n : SimplexCategory)
    (S : ProbeSdCC.{u} n) (T : ProbeSdC.{u} n)
    (hT : T ∈ S.finset) : T ≤ probeSdOuterLast n S := by
  have hLast := (probeSdOuterLast_maximal n S).1
  rcases S.comparable ⟨T, hT⟩
      ⟨probeSdOuterLast n S, hLast⟩ with h | h
  · exact h
  · exact (probeSdOuterLast_maximal n S).2 hT h

private def probeSdOuterLastOrderHom (n : SimplexCategory) :
    ProbeSdCC.{u} n →o ProbeSdC.{u} n where
  toFun := probeSdOuterLast n
  monotone' A B h := probeLe_sdOuterLast n B (probeSdOuterLast n A)
    (h (probeSdOuterLast_maximal n A).1)

end SimplexCategory

namespace SSet

private noncomputable def probeFaceOrderIso (n : SimplexCategory) :
    (SSet.stdSimplex.{u}.obj n).N ≃o
      PartialOrder.NonemptyFiniteChains
        (ULift.{u} (Fin (n.len + 1))) :=
  (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} n.len)).trans
    (PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj n))

private noncomputable def probeFlagFaceToN (n : SimplexCategory)
    (T : SimplexCategory.ProbeSdC.{u} n) :
    (SSet.stdSimplex.{u}.obj n).N :=
  (SSet.sdFlagCarrierChain n (ComposableArrows.mk₀ T)).obj 0

private noncomputable def probeNToFlagFace (n : SimplexCategory)
    (x : (SSet.stdSimplex.{u}.obj n).N) :
    SimplexCategory.ProbeSdC.{u} n :=
  (SSet.sdFlagOfCarrierChain n (ComposableArrows.mk₀ x)).obj 0

private theorem probeNToFlagFace_flagFaceToN
    (n : SimplexCategory) (T : SimplexCategory.ProbeSdC.{u} n) :
    probeNToFlagFace n (probeFlagFaceToN n T) = T := by
  let c := SSet.sdFlagCarrierChain n (ComposableArrows.mk₀ T)
  have hc : ComposableArrows.mk₀ (c.obj 0) = c := by
    apply ComposableArrows.ext (h := fun i => by fin_cases i; rfl)
      (w := by intro i hi; omega)
  unfold probeNToFlagFace probeFlagFaceToN
  change (SSet.sdFlagOfCarrierChain n
    (ComposableArrows.mk₀ (c.obj 0))).obj 0 = T
  rw [hc]
  have hcomp := SSet.sdFlagOfCarrierChain_flagCarrierChain n
    (ComposableArrows.mk₀ T)
  change SSet.sdFlagOfCarrierChain n c =
    ComposableArrows.mk₀ T at hcomp
  exact congrArg (fun F => F.obj 0) hcomp

private theorem probeFlagFaceToN_nToFlagFace
    (n : SimplexCategory) (x : (SSet.stdSimplex.{u}.obj n).N) :
    probeFlagFaceToN n (probeNToFlagFace n x) = x := by
  let F := SSet.sdFlagOfCarrierChain n (ComposableArrows.mk₀ x)
  have hF : ComposableArrows.mk₀ (F.obj 0) = F := by
    apply ComposableArrows.ext (h := fun i => by fin_cases i; rfl)
      (w := by intro i hi; omega)
  unfold probeNToFlagFace probeFlagFaceToN
  change (SSet.sdFlagCarrierChain n
    (ComposableArrows.mk₀ (F.obj 0))).obj 0 = x
  rw [hF]
  have hcomp := SSet.sdFlagCarrierChain_flagOfCarrierChain n
    (ComposableArrows.mk₀ x)
  change SSet.sdFlagCarrierChain n F =
    ComposableArrows.mk₀ x at hcomp
  exact congrArg (fun c => c.obj 0) hcomp

private theorem probeSdFlagCarrierChain_obj_eq
    (n : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (i : Fin (d + 1)) :
    (SSet.sdFlagCarrierChain n F).obj i =
      probeFlagFaceToN n (F.obj i) := by
  let f := SimplexCategory.const ⦋0⦌ ⦋d⦌ i
  have h := SSet.sdFlagCarrierChain_obj_map n f F
  have hleft :
      (SimplexCategory.sd.{u}.obj n).map f.op F =
        ComposableArrows.mk₀ (F.obj i) := by
    apply ComposableArrows.ext (h := fun j => by fin_cases j; rfl)
      (w := by intro j hj; simp at hj)
  have hright :
      (SSet.nondegenerateNerve.obj
        (SSet.stdSimplex.{u}.obj n)).map f.op
          (SSet.sdFlagCarrierChain n F) =
        ComposableArrows.mk₀ ((SSet.sdFlagCarrierChain n F).obj i) := by
    apply ComposableArrows.ext (h := fun j => by fin_cases j; rfl)
      (w := by intro j hj; simp at hj)
  rw [hleft, hright] at h
  exact (congrArg (fun c => c.obj 0) h).symm

private theorem probeFlagFaceToN_injective (n : SimplexCategory) :
    Function.Injective (probeFlagFaceToN.{u} n) := by
  intro T U h
  exact (probeNToFlagFace_flagFaceToN n T).symm.trans
    ((congrArg (probeNToFlagFace n) h).trans
      (probeNToFlagFace_flagFaceToN n U))

private theorem probeFlagFaceToN_monotone (n : SimplexCategory) :
    Monotone (probeFlagFaceToN.{u} n) := by
  intro T U hTU
  let c : (SimplexCategory.sd.{u}.obj n) _⦋1⦌ :=
    ComposableArrows.mk₁ (homOfLE hTU)
  have hmono := (SSet.sdFlagCarrierChain n c).monotone
    (show (0 : Fin 2) ≤ 1 by omega)
  rw [probeSdFlagCarrierChain_obj_eq n c 0,
    probeSdFlagCarrierChain_obj_eq n c 1] at hmono
  change probeFlagFaceToN n T ≤ probeFlagFaceToN n U at hmono
  exact hmono

private theorem probeFlagFaceToN_le_iff (n : SimplexCategory)
    (T U : SimplexCategory.ProbeSdC.{u} n) :
    probeFlagFaceToN n T ≤ probeFlagFaceToN n U ↔ T ≤ U := by
  constructor
  · intro hTU
    let c : (CategoryTheory.nerve
        (SSet.stdSimplex.{u}.obj n).N) _⦋1⦌ :=
      ComposableArrows.mk₁ (homOfLE hTU)
    let F := SSet.sdFlagOfCarrierChain n c
    have hchain : SSet.sdFlagCarrierChain n F = c :=
      SSet.sdFlagCarrierChain_flagOfCarrierChain n c
    have hzero : F.obj 0 = T := by
      apply probeFlagFaceToN_injective n
      rw [← probeSdFlagCarrierChain_obj_eq n F 0, hchain]
      rfl
    have hone : F.obj 1 = U := by
      apply probeFlagFaceToN_injective n
      rw [← probeSdFlagCarrierChain_obj_eq n F 1, hchain]
      rfl
    rw [← hzero, ← hone]
    have hmono := F.monotone (Fin.zero_le (Fin.last 1))
    change F.obj 0 ≤ F.obj 1 at hmono
    exact hmono
  · intro hTU
    exact probeFlagFaceToN_monotone n hTU

private noncomputable def probeFlagFaceOrderIso (n : SimplexCategory) :
    SimplexCategory.ProbeSdC.{u} n ≃o
      (SSet.stdSimplex.{u}.obj n).N where
  toFun := probeFlagFaceToN n
  invFun := probeNToFlagFace n
  left_inv := probeNToFlagFace_flagFaceToN n
  right_inv := probeFlagFaceToN_nToFlagFace n
  map_rel_iff' := probeFlagFaceToN_le_iff n _ _

private theorem probeFlagFaceToN_map {m n : SimplexCategory}
    (f : m ⟶ n) (T : SimplexCategory.ProbeSdC.{u} m) :
    probeFlagFaceToN n
        (T.map ((SimplexCategory.toPartOrd.map f).hom)) =
      SSet.N.map (SSet.stdSimplex.map f)
        (probeFlagFaceToN m T) := by
  have h := SSet.sdFlagCarrierChain_map f (ComposableArrows.mk₀ T)
  have hleft :
      (SimplexCategory.sd.map f).app (op ⦋0⦌) (ComposableArrows.mk₀ T) =
        ComposableArrows.mk₀
          (T.map ((SimplexCategory.toPartOrd.map f).hom)) := by
    apply ComposableArrows.ext (h := fun i => rfl)
      (w := by intro i hi; subsingleton)
  have hright :
      (SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app (op ⦋0⦌)
          (SSet.sdFlagCarrierChain m (ComposableArrows.mk₀ T)) =
        ComposableArrows.mk₀
          (SSet.N.map (SSet.stdSimplex.map f)
            (probeFlagFaceToN m T)) := by
    let c := SSet.sdFlagCarrierChain m (ComposableArrows.mk₀ T)
    have hc : ComposableArrows.mk₀ (c.obj 0) = c := by
      apply ComposableArrows.ext (h := fun i => by fin_cases i; rfl)
        (w := by intro i hi; simp at hi)
    change (SSet.nondegenerateNerve.map
      (SSet.stdSimplex.map f)).app (op ⦋0⦌) c = _
    rw [← hc]
    rfl
  rw [hleft, hright] at h
  exact congrArg (fun c => c.obj 0) h

private theorem probeN_map_iso_hom {X Y : SSet.{u}}
    (e : X ≅ Y) (x : X.N) :
    SSet.N.map e.hom x = SSet.N.orderIsoOfIso e x := by
  rw [SSet.N.map_eq_mk]
  rfl

private theorem probeFaceOrderIso_map {m n : SimplexCategory}
    (f : m ⟶ n) (x : (SSet.stdSimplex.{u}.obj m).N) :
    probeFaceOrderIso n
        (SSet.N.map (SSet.stdSimplex.map f) x) =
      (probeFaceOrderIso m x).map
        ((SimplexCategory.toPartOrd.map f).hom) := by
  let nf : CategoryTheory.nerve
        (ULift.{u} (Fin (m.len + 1))) ⟶
      CategoryTheory.nerve
        (ULift.{u} (Fin (n.len + 1))) :=
    CategoryTheory.nerveMap
      ((SimplexCategory.toPartOrd.map f).hom.toFunctor)
  have hsquare :
      SSet.stdSimplex.map f ≫
          (SSet.stdSimplex.isoNerve.{u} n.len).hom =
        (SSet.stdSimplex.isoNerve.{u} m.len).hom ≫
          nf := by
    ext d s i
    rfl
  have hN :
      SSet.N.map (SSet.stdSimplex.isoNerve.{u} n.len).hom
          (SSet.N.map (SSet.stdSimplex.map f) x) =
        SSet.N.map
            nf
          (SSet.N.map (SSet.stdSimplex.isoNerve.{u} m.len).hom x) := by
    calc
      _ = SSet.N.map
          (SSet.stdSimplex.map f ≫
            (SSet.stdSimplex.isoNerve.{u} n.len).hom) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          ((SSet.stdSimplex.isoNerve.{u} m.len).hom ≫ nf) x := by
        rw [hsquare]
      _ = _ := (SSet.N.map_comp_apply _ _ _).symm
  change PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj n)
      (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} n.len)
        (SSet.N.map (SSet.stdSimplex.map f) x)) =
    (PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj m)
      (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} m.len) x)).map
        ((SimplexCategory.toPartOrd.map f).hom)
  rw [← probeN_map_iso_hom, ← probeN_map_iso_hom]
  rw [hN]
  have hnat := PartOrd.nerveNOrderIso_naturality
    (SimplexCategory.toPartOrd.map f)
      (SSet.N.map (SSet.stdSimplex.isoNerve.{u} m.len).hom x)
  change PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj n)
      (SSet.N.map nf
        (SSet.N.map (SSet.stdSimplex.isoNerve.{u} m.len).hom x)) = _ at hnat
  exact hnat

private noncomputable def probeFaceTwistOrderIso
    (n : SimplexCategory) :
    SimplexCategory.ProbeSdC.{u} n ≃o
      SimplexCategory.ProbeSdC.{u} n :=
  (probeFlagFaceOrderIso n).trans (probeFaceOrderIso n)

private theorem probeFaceTwist_map {m n : SimplexCategory}
    (f : m ⟶ n) (T : SimplexCategory.ProbeSdC.{u} m) :
    probeFaceTwistOrderIso n
        (T.map ((SimplexCategory.toPartOrd.map f).hom)) =
      (probeFaceTwistOrderIso m T).map
        ((SimplexCategory.toPartOrd.map f).hom) := by
  change probeFaceOrderIso n
      (probeFlagFaceToN n
        (T.map ((SimplexCategory.toPartOrd.map f).hom))) = _
  rw [probeFlagFaceToN_map, probeFaceOrderIso_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem probeFullFace_map_vertex
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    (SSet.sdFullFace.{u} ⦋0⦌).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ n j)).hom) =
      SimplexCategory.sdSingletonChain n j := by
  classical
  apply PartialOrder.NonemptyFiniteChains.ext
  ext y
  simp only [PartialOrder.NonemptyFiniteChains.mem_map_iff,
    SSet.mem_sdFullFace, SimplexCategory.sdSingletonChain,
    Finset.mem_singleton, true_and]
  constructor
  · rintro ⟨x, hxy⟩
    change ULift.up j = y at hxy
    exact hxy.symm
  · rintro rfl
    exact ⟨ULift.up 0, rfl⟩

private theorem probeFaceTwist_full_zero :
    probeFaceTwistOrderIso ⦋0⦌ (SSet.sdFullFace.{u} ⦋0⦌) =
      SSet.sdFullFace.{u} ⦋0⦌ := by
  apply PartialOrder.NonemptyFiniteChains.ext
  ext y
  constructor
  · intro _
    exact SSet.mem_sdFullFace _ _
  · intro _
    obtain ⟨z, hz⟩ :=
      (probeFaceTwistOrderIso ⦋0⦌
        (SSet.sdFullFace.{u} ⦋0⦌)).nonempty
    have hzy : z = y := by
      apply ULift.ext
      apply Fin.ext
      have hz := z.down.isLt
      have hy := y.down.isLt
      change z.down.val < 1 at hz
      change y.down.val < 1 at hy
      omega
    rwa [← hzy]

set_option backward.isDefEq.respectTransparency false in
private theorem probeFaceTwist_singleton
    (n : SimplexCategory) (j : Fin (n.len + 1)) :
    probeFaceTwistOrderIso.{u} n
        (SimplexCategory.sdSingletonChain.{u} n j) =
      SimplexCategory.sdSingletonChain.{u} n j := by
  let f := SimplexCategory.const ⦋0⦌ n j
  have h := probeFaceTwist_map f (SSet.sdFullFace.{u} ⦋0⦌)
  dsimp only [f] at h
  have hfull := probeFullFace_map_vertex.{u} n j
  have hzero := probeFaceTwist_full_zero.{u}
  calc
    _ = probeFaceTwistOrderIso n
        ((SSet.sdFullFace.{u} ⦋0⦌).map
          ((SimplexCategory.toPartOrd.map
            (SimplexCategory.const ⦋0⦌ n j)).hom)) :=
      congrArg (probeFaceTwistOrderIso n) hfull.symm
    _ = (probeFaceTwistOrderIso ⦋0⦌
          (SSet.sdFullFace.{u} ⦋0⦌)).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ n j)).hom) := h
    _ = (SSet.sdFullFace.{u} ⦋0⦌).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ n j)).hom) :=
      congrArg (fun T => T.map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ n j)).hom)) hzero
    _ = _ := hfull

private theorem probeFaceTwist_eq
    (n : SimplexCategory) (T : SimplexCategory.ProbeSdC.{u} n) :
    probeFaceTwistOrderIso n T = T := by
  apply PartialOrder.NonemptyFiniteChains.ext
  ext x
  let j : Fin (n.len + 1) := x.down
  have hmem : ULift.up j ∈
      (SimplexCategory.sdSingletonChain.{u} n j).finset := by
    simp [SimplexCategory.sdSingletonChain]
  constructor
  · intro hx
    have hsTw : SimplexCategory.sdSingletonChain.{u} n j ≤
        probeFaceTwistOrderIso n T := by
      intro y hy
      have hyx : y = ULift.up j := by
        simpa [SimplexCategory.sdSingletonChain] using hy
      rw [hyx, ULift.up_down]
      exact hx
    have htw : probeFaceTwistOrderIso n
          (SimplexCategory.sdSingletonChain.{u} n j) ≤
        probeFaceTwistOrderIso n T := by
      rw [probeFaceTwist_singleton]
      exact hsTw
    have hsT : SimplexCategory.sdSingletonChain.{u} n j ≤ T :=
      (probeFaceTwistOrderIso n).map_rel_iff.mp htw
    simpa [j, ULift.up_down] using hsT hmem
  · intro hx
    have hsT : SimplexCategory.sdSingletonChain.{u} n j ≤ T := by
      intro y hy
      have hyx : y = ULift.up j := by
        simpa [SimplexCategory.sdSingletonChain] using hy
      rw [hyx, ULift.up_down]
      exact hx
    have htw : probeFaceTwistOrderIso n
          (SimplexCategory.sdSingletonChain.{u} n j) ≤
        probeFaceTwistOrderIso n T :=
      (probeFaceTwistOrderIso n).map_rel_iff.mpr hsT
    rw [probeFaceTwist_singleton] at htw
    simpa [j, ULift.up_down] using htw hmem

private theorem probeFlagFaceToN_eq
    (n : SimplexCategory) (T : SimplexCategory.ProbeSdC.{u} n) :
    probeFlagFaceToN n T = (probeFaceOrderIso n).symm T := by
  apply (probeFaceOrderIso n).injective
  change probeFaceTwistOrderIso n T =
    probeFaceOrderIso n ((probeFaceOrderIso n).symm T)
  rw [OrderIso.apply_symm_apply]
  exact probeFaceTwist_eq n T

private theorem probeSdFlagCarrierChain_obj
    (n : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (i : Fin (d + 1)) :
    (SSet.sdFlagCarrierChain n F).obj i =
      (probeFaceOrderIso n).symm (F.obj i) := by
  calc
    _ = probeFlagFaceToN n (F.obj i) :=
      probeSdFlagCarrierChain_obj_eq n F i
    _ = _ := probeFlagFaceToN_eq n (F.obj i)

private theorem probeFaceOrderIso_last (n : SimplexCategory)
    (x : (SSet.stdSimplex.{u}.obj n).N) :
    SimplexCategory.sdChainLast n (probeFaceOrderIso n x) =
      ULift.up (SSet.stdSimplex.objEquiv x.simplex
        (Fin.last x.dim)) := by
  let y := SSet.N.orderIsoOfIso
    (SSet.stdSimplex.isoNerve.{u} n.len) x
  let T := PartOrd.nerveNOrderIso
    (SimplexCategory.toPartOrd.obj n) y
  change SimplexCategory.sdChainLast n T = _
  unfold SimplexCategory.sdChainLast
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    have hz' := (PartOrd.mem_nerveNOrderIso_finset
      (SimplexCategory.toPartOrd.obj n) y z).1 hz
    obtain ⟨j, rfl⟩ := hz'
    change ULift.up (SSet.stdSimplex.objEquiv x.simplex j) ≤
      ULift.up (SSet.stdSimplex.objEquiv x.simplex
        (Fin.last x.dim))
    exact (SSet.stdSimplex.objEquiv x.simplex).toOrderHom.monotone
      (Fin.le_last j)
  · apply Finset.le_max'
    apply (PartOrd.mem_nerveNOrderIso_finset
      (SimplexCategory.toPartOrd.obj n) y _).2
    refine ⟨Fin.last x.dim, ?_⟩
    change ULift.up (SSet.stdSimplex.objEquiv x.simplex
      (Fin.last x.dim)) = _
    rfl

private theorem probeSdOuterLast_eq_last (n : SimplexCategory)
    (x : (SimplexCategory.sd.{u}.obj n).N) :
    SimplexCategory.probeSdOuterLast n
        (PartOrd.nerveNOrderIso
          (PartOrd.nonemptyFiniteChainsFunctor.obj
            (SimplexCategory.toPartOrd.obj n)) x) =
      x.simplex.obj (Fin.last x.dim) := by
  let P := PartOrd.nonemptyFiniteChainsFunctor.obj
    (SimplexCategory.toPartOrd.obj n)
  let C := PartOrd.nerveNOrderIso P x
  change SimplexCategory.probeSdOuterLast n C = _
  have hlast : x.simplex.obj (Fin.last x.dim) ∈ C.finset :=
    (PartOrd.mem_nerveNOrderIso_finset P x _).2
      ⟨Fin.last x.dim, rfl⟩
  apply le_antisymm
  · have hout := (SimplexCategory.probeSdOuterLast_maximal n C).1
    obtain ⟨j, hj⟩ :=
      (PartOrd.mem_nerveNOrderIso_finset P x _).1 hout
    rw [← hj]
    exact x.simplex.monotone (Fin.le_last j)
  · exact SimplexCategory.probeLe_sdOuterLast n C _ hlast

private theorem probeEpi_map_last {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] :
    f.toOrderHom (Fin.last m) = Fin.last n := by
  apply le_antisymm (Fin.le_last _)
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp
    (inferInstance : Epi f)) (Fin.last n)
  rw [← hi]
  exact f.toOrderHom.monotone (Fin.le_last i)

private theorem probeN_map_last
    {P : Type u} [PartialOrder P]
    {k : SimplexCategory}
    (p : SSet.stdSimplex.obj k ⟶ CategoryTheory.nerve P)
    (x : (SSet.stdSimplex.obj k : SSet.{u}).N) :
    (SSet.N.map p x).simplex.obj
        (Fin.last (SSet.N.map p x).dim) =
      (p.app _ x.simplex).obj (Fin.last x.dim) := by
  let s : (CategoryTheory.nerve P).S := SSet.S.map p x.toS
  have hlast : s.toNπ.toOrderHom (Fin.last s.dim) =
      Fin.last s.toN.dim := probeEpi_map_last s.toNπ
  have h := congrArg (fun q => q.obj (Fin.last s.dim))
    (SSet.S.map_toNπ_op_apply s)
  change s.toN.simplex.obj
      (s.toNπ.toOrderHom (Fin.last s.dim)) =
    s.simplex.obj (Fin.last s.dim) at h
  rw [hlast] at h
  exact h

private theorem probeMap_simplex_last
    {P : Type u} [PartialOrder P]
    {k : SimplexCategory}
    (p : SSet.stdSimplex.obj k ⟶ CategoryTheory.nerve P)
    (x : (SSet.stdSimplex.obj k : SSet.{u}).N) :
    (p.app _ x.simplex).obj (Fin.last x.dim) =
      (p.app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm
          (SSet.stdSimplex.objEquiv x.simplex
            (Fin.last x.dim)))).obj 0 := by
  let v := SimplexCategory.const ⦋0⦌ ⦋x.dim⦌ (Fin.last x.dim)
  have hnat := p.naturality_apply v.op x.simplex
  have hobj := congrArg (fun c => c.obj 0) hnat
  change (p.app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm
        (SSet.stdSimplex.objEquiv x.simplex
          (Fin.last x.dim)))).obj 0 =
    (p.app (op ⦋x.dim⦌) x.simplex).obj (Fin.last x.dim) at hobj
  exact hobj.symm

set_option backward.isDefEq.respectTransparency false in
private theorem probeLastVertex_chart (n : SimplexCategory) :
    SSet.lastVertex.app (SSet.stdSimplex.{u}.obj n) ≫
        (SSet.stdSimplex.isoNerve.{u} n.len).hom =
      SSet.stdSimplex.sdIso.hom.app n ≫
        SimplexCategory.probeLastNerveMap.{u} n := by
  apply (cancel_epi (SSet.stdSimplex.sdIso.{u}.inv.app n)).mp
  calc
    _ = SimplexCategory.lastVertex.app n ≫
        (SSet.stdSimplex.isoNerve.{u} n.len).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (SSet.stdSimplex.isoNerve.{u} n.len).hom)
        (SSet.lastVertex_fac.{u} n)
    _ = SimplexCategory.probeLastNerveMap.{u} n := by
      unfold SimplexCategory.lastVertex
      dsimp only [SimplexCategory.sdRepresentableLastVertexApp,
        SimplexCategory.probeLastNerveMap]
      change (SimplexCategory.probeLastNerveMap.{u} n ≫
          (SSet.stdSimplex.isoNerve.{u} n.len).inv) ≫
        (SSet.stdSimplex.isoNerve.{u} n.len).hom =
          SimplexCategory.probeLastNerveMap.{u} n
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = SSet.stdSimplex.sdIso.inv.app n ≫
        SSet.stdSimplex.sdIso.hom.app n ≫
          SimplexCategory.probeLastNerveMap.{u} n := by
      exact (Iso.inv_hom_id_assoc (SSet.stdSimplex.sdIso.app n)
        (SimplexCategory.probeLastNerveMap.{u} n)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem probeInnerCarrier (n : SimplexCategory)
    (x : (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})).N) :
    (SSet.sdFlagCarrierChain n
      (ComposableArrows.mk₀
        ((PartOrd.nerveNOrderIso
          (PartOrd.nonemptyFiniteChainsFunctor.obj
            (SimplexCategory.toPartOrd.obj n))
          (SSet.N.map (SSet.stdSimplex.sdIso.hom.app n) x)).map
            (SimplexCategory.sdLastVertexOrderHom n)))).obj 0 =
      SSet.N.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x := by
  let P := PartOrd.nonemptyFiniteChainsFunctor.obj
    (SimplexCategory.toPartOrd.obj n)
  let Q := SimplexCategory.toPartOrd.obj n
  let h : P ⟶ Q :=
    PartOrd.ofHom (SimplexCategory.probeLastVertexOrderHom n)
  let x' : (SimplexCategory.sd.{u}.obj n).N :=
    SSet.N.map (SSet.stdSimplex.sdIso.hom.app n) x
  let C : PartialOrder.NonemptyFiniteChains P :=
    PartOrd.nerveNOrderIso P x'
  change (SSet.sdFlagCarrierChain n
    (ComposableArrows.mk₀ (C.map h.hom))).obj 0 = _
  have hcarrier := probeSdFlagCarrierChain_obj n
    (ComposableArrows.mk₀ (C.map h.hom)) 0
  change (SSet.sdFlagCarrierChain n
      (ComposableArrows.mk₀ (C.map h.hom))).obj 0 =
    (probeFaceOrderIso n).symm (C.map h.hom) at hcarrier
  rw [hcarrier]
  apply (probeFaceOrderIso n).injective
  rw [OrderIso.apply_symm_apply]
  change C.map h.hom = probeFaceOrderIso n
    (SSet.N.map
      (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x)
  change C.map h.hom = PartOrd.nerveNOrderIso Q
    (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} n.len)
      (SSet.N.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x))
  rw [← probeN_map_iso_hom]
  have hN :
      SSet.N.map (SSet.stdSimplex.isoNerve.{u} n.len).hom
          (SSet.N.map
            (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x) =
        SSet.N.map (SimplexCategory.probeLastNerveMap.{u} n) x' := by
    calc
      _ = SSet.N.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj n) ≫
            (SSet.stdSimplex.isoNerve.{u} n.len).hom) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          (SSet.stdSimplex.sdIso.hom.app n ≫
            SimplexCategory.probeLastNerveMap.{u} n) x :=
        congrArg (fun k => SSet.N.map k x)
          (probeLastVertex_chart.{u} n)
      _ = SSet.N.map (SimplexCategory.probeLastNerveMap.{u} n) x' :=
        (SSet.N.map_comp_apply _ _ _).symm
  rw [hN]
  have hnat := PartOrd.nerveNOrderIso_naturality h x'
  change PartOrd.nerveNOrderIso Q
      (SSet.N.map (SimplexCategory.probeLastNerveMap.{u} n) x') =
    C.map h.hom at hnat
  exact hnat.symm

private noncomputable def probeSdSdRepresentableMap
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      PartOrd.nerveFunctor.{u}.obj
        (PartOrd.of (SimplexCategory.ProbeSdCC.{u} n)) :=
  SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫
    SSet.sdToNondegenerateNerve.app
      (SimplexCategory.sd.{u}.obj n) ≫
    PartOrd.nerveFunctor.{u}.map
      (PartOrd.Iso.mk
        (PartOrd.nerveNOrderIso
          (PartOrd.nonemptyFiniteChainsFunctor.obj
            (SimplexCategory.toPartOrd.obj n)))).hom

private noncomputable def probeRepresentableDoubleLastInner
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      SSet.sd.obj (SSet.stdSimplex.{u}.obj n) :=
  probeSdSdRepresentableMap n ≫
    CategoryTheory.nerveMap
      (SimplexCategory.probeSdInnerMaximaOrderHom.{u} n).toFunctor ≫
  SSet.stdSimplex.sdIso.inv.app n

private noncomputable def probeRepresentableDoubleLastOuter
    (n : SimplexCategory) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj n)) ⟶
      SSet.sd.obj (SSet.stdSimplex.{u}.obj n) :=
  probeSdSdRepresentableMap n ≫
    CategoryTheory.nerveMap
      (SimplexCategory.probeSdOuterLastOrderHom.{u} n).toFunctor ≫
  SSet.stdSimplex.sdIso.inv.app n

set_option backward.isDefEq.respectTransparency false in
private theorem probeInner_eq (n : SimplexCategory) :
    probeRepresentableDoubleLastInner n =
      SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})) := by
  ext d S
  induction d using Opposite.rec
  rename_i d
  induction d using SimplexCategory.rec
  rename_i k
  apply CategoryTheory.injective_of_mono
    ((SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌))
  change (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
      ((probeRepresentableDoubleLastInner n).app (op ⦋k⦌) S) =
    (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
      ((SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) S)
  have hleft :
      (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
          ((probeRepresentableDoubleLastInner n).app (op ⦋k⦌) S) =
        (CategoryTheory.nerveMap
          (SimplexCategory.probeSdInnerMaximaOrderHom.{u} n).toFunctor).app (op ⦋k⦌)
            ((probeSdSdRepresentableMap n).app (op ⦋k⦌) S) := by
    change (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
        ((SSet.stdSimplex.sdIso.{u}.app n).inv.app (op ⦋k⦌)
          ((CategoryTheory.nerveMap
            (SimplexCategory.probeSdInnerMaximaOrderHom.{u} n).toFunctor).app (op ⦋k⦌)
              ((probeSdSdRepresentableMap n).app (op ⦋k⦌) S))) = _
    exact ConcreteCategory.congr_hom
      (Iso.inv_hom_id_app (SSet.stdSimplex.sdIso.{u}.app n) (op ⦋k⦌)) _
  rw [hleft]
  apply ComposableArrows.ext (h := fun i => ?_) (w := by
    intro i hi
    subsingleton)
  let cAll := (SSet.sdToNondegenerateNerve.app
    (SSet.sd.obj (SSet.stdSimplex.obj n))).app (op ⦋k⦌) S
  let x : (SSet.sd.obj (SSet.stdSimplex.obj n)).N := cAll.obj i
  let P := PartOrd.nonemptyFiniteChainsFunctor.obj
    (SimplexCategory.toPartOrd.obj n)
  let x' : (SimplexCategory.sd.{u}.obj n).N :=
    SSet.N.map (SSet.stdSimplex.sdIso.hom.app n) x
  let C : PartialOrder.NonemptyFiniteChains P :=
    PartOrd.nerveNOrderIso P x'
  have hchart : ((probeSdSdRepresentableMap n).app (op ⦋k⦌) S).obj i = C := by
    have hnat := SSet.sdToNondegenerateNerve.naturality
      (SSet.stdSimplex.sdIso.hom.app n)
    have happ := congrArg (fun g => g.app (op ⦋k⦌) S) hnat
    change (SSet.sdToNondegenerateNerve.app
        (SimplexCategory.sd.obj n)).app (op ⦋k⦌)
          ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n)).app (op ⦋k⦌) S) =
      (SSet.nondegenerateNerve.map
        (SSet.stdSimplex.sdIso.hom.app n)).app (op ⦋k⦌) cAll at happ
    change (PartOrd.nerveNOrderIso P
      (((SSet.sdToNondegenerateNerve.app
        (SimplexCategory.sd.obj n)).app (op ⦋k⦌)
          ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n)).app (op ⦋k⦌) S)).obj i)) = C
    rw [happ]
    rfl
  change SimplexCategory.probeSdInnerMaximaOrderHom.{u} n
      (((probeSdSdRepresentableMap n).app (op ⦋k⦌) S).obj i) = _
  rw [hchart]
  change C.map (SimplexCategory.sdLastVertexOrderHom n) = _
  apply (probeFaceOrderIso n).symm.injective
  have hinner := probeInnerCarrier.{u} n x
  have hcarrier := probeSdFlagCarrierChain_obj n
    (ComposableArrows.mk₀
      (C.map (SimplexCategory.sdLastVertexOrderHom n))) 0
  change (SSet.sdFlagCarrierChain n
      (ComposableArrows.mk₀
        (C.map (SimplexCategory.sdLastVertexOrderHom n)))).obj 0 =
    (probeFaceOrderIso n).symm
      (C.map (SimplexCategory.sdLastVertexOrderHom n)) at hcarrier
  have hleftCarrier :
      (probeFaceOrderIso n).symm
          (C.map (SimplexCategory.sdLastVertexOrderHom n)) =
        SSet.N.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x := by
    exact hcarrier.symm.trans hinner
  rw [hleftCarrier]
  symm
  calc
    _ = (SSet.sdFlagCarrierChain n
        ((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋k⦌)
          ((SSet.sd.map
            (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) S))).obj i :=
      (probeSdFlagCarrierChain_obj n _ i).symm
    _ = SSet.N.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x := by
      let y := (SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) S
      let F := (SSet.stdSimplex.sdIso.hom.app n).app (op ⦋k⦌) y
      have hiso : (SSet.stdSimplex.sdIso.inv.app n).app (op ⦋k⦌) F = y := by
        exact ConcreteCategory.congr_hom
          (Iso.hom_inv_id_app (SSet.stdSimplex.sdIso.{u}.app n) (op ⦋k⦌)) y
      have hnat := SSet.sdToNondegenerateNerve.naturality
        (SSet.lastVertex.app (SSet.stdSimplex.obj n))
      have happ := congrArg (fun g => g.app (op ⦋k⦌) S) hnat
      change (SSet.sdToNondegenerateNerve.app
          (SSet.stdSimplex.obj n)).app (op ⦋k⦌)
            ((SSet.sd.map
              (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) S) =
        (SSet.nondegenerateNerve.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) cAll at happ
      have hchain : SSet.sdFlagCarrierChain n F =
          (SSet.nondegenerateNerve.map
            (SSet.lastVertex.app (SSet.stdSimplex.obj n))).app (op ⦋k⦌) cAll := by
        unfold SSet.sdFlagCarrierChain
        rw [hiso]
        exact happ
      have hobj := congrArg (fun c => c.obj i) hchain
      change (SSet.sdFlagCarrierChain n F).obj i =
        SSet.N.map (SSet.lastVertex.app (SSet.stdSimplex.obj n)) x at hobj
      exact hobj

set_option backward.isDefEq.respectTransparency false in
private theorem probeOuter_eq (n : SimplexCategory) :
    probeRepresentableDoubleLastOuter n =
      SSet.lastVertex.app
        (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})) := by
  ext d S
  induction d using Opposite.rec
  rename_i d
  induction d using SimplexCategory.rec
  rename_i k
  obtain ⟨a, rfl⟩ := SSet.SdAnchoredFlag.toSimplex_surjective
    (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})) k S
  apply CategoryTheory.injective_of_mono
    ((SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌))
  change (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
      ((probeRepresentableDoubleLastOuter n).app (op ⦋k⦌) a.toSimplex) =
    (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
      ((SSet.lastVertex.app
        (SSet.sd.obj (SSet.stdSimplex.obj n))).app (op ⦋k⦌) a.toSimplex)
  have hleft :
      (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
          ((probeRepresentableDoubleLastOuter n).app (op ⦋k⦌) a.toSimplex) =
        (CategoryTheory.nerveMap
          (SimplexCategory.probeSdOuterLastOrderHom.{u} n).toFunctor).app (op ⦋k⦌)
            ((probeSdSdRepresentableMap n).app (op ⦋k⦌) a.toSimplex) := by
    change (SSet.stdSimplex.sdIso.{u}.app n).hom.app (op ⦋k⦌)
        ((SSet.stdSimplex.sdIso.{u}.app n).inv.app (op ⦋k⦌)
          ((CategoryTheory.nerveMap
            (SimplexCategory.probeSdOuterLastOrderHom.{u} n).toFunctor).app (op ⦋k⦌)
              ((probeSdSdRepresentableMap n).app (op ⦋k⦌) a.toSimplex))) = _
    exact ConcreteCategory.congr_hom
      (Iso.inv_hom_id_app (SSet.stdSimplex.sdIso.{u}.app n) (op ⦋k⦌)) _
  rw [hleft]
  apply ComposableArrows.ext (h := fun i => ?_) (w := by
    intro i hi
    subsingleton)
  let p := SSet.yonedaEquiv.symm a.carrier.simplex
  let p' := p ≫ SSet.stdSimplex.sdIso.hom.app n
  let cAll := SSet.sdFlagCarrierChain
    ⦋a.carrier.dim⦌ a.flag
  let c : (SSet.stdSimplex.{u}.obj ⦋a.carrier.dim⦌).N := cAll.obj i
  let x : (SSet.sd.obj (SSet.stdSimplex.obj n)).N :=
    SSet.N.map p c
  let x' : (SimplexCategory.sd.{u}.obj n).N :=
    SSet.N.map (SSet.stdSimplex.sdIso.hom.app n) x
  let P := PartOrd.nonemptyFiniteChainsFunctor.obj
    (SimplexCategory.toPartOrd.obj n)
  let C : PartialOrder.NonemptyFiniteChains P :=
    PartOrd.nerveNOrderIso P x'
  have hchart :
      ((probeSdSdRepresentableMap n).app (op ⦋k⦌)
        a.toSimplex).obj i = C := by
    have hnat := SSet.sdToNondegenerateNerve.naturality
      (SSet.stdSimplex.sdIso.hom.app n)
    have happ := congrArg (fun g => g.app (op ⦋k⦌) a.toSimplex) hnat
    change (SSet.sdToNondegenerateNerve.app
        (SimplexCategory.sd.obj n)).app (op ⦋k⦌)
          ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n)).app
            (op ⦋k⦌) a.toSimplex) =
      (SSet.nondegenerateNerve.map
        (SSet.stdSimplex.sdIso.hom.app n)).app (op ⦋k⦌)
          ((SSet.sdToNondegenerateNerve.app
            (SSet.sd.obj (SSet.stdSimplex.obj n))).app
              (op ⦋k⦌) a.toSimplex) at happ
    have ha := a.sdToNondegenerateNerve_toSimplex
    change (SSet.sdToNondegenerateNerve.app
      (SSet.sd.obj (SSet.stdSimplex.obj n))).app
        (op ⦋k⦌) a.toSimplex =
      (SSet.nondegenerateNerve.map p).app (op ⦋k⦌) cAll at ha
    change PartOrd.nerveNOrderIso P
      (((SSet.sdToNondegenerateNerve.app
        (SimplexCategory.sd.obj n)).app (op ⦋k⦌)
          ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n)).app
            (op ⦋k⦌) a.toSimplex)).obj i) = C
    rw [happ, ha]
    rfl
  change SimplexCategory.probeSdOuterLast n
      (((probeSdSdRepresentableMap n).app (op ⦋k⦌)
        a.toSimplex).obj i) = _
  rw [hchart]
  have hxprime : x' = SSet.N.map p' c := by
    dsimp only [x', x, p']
    exact SSet.N.map_comp_apply p
      (SSet.stdSimplex.sdIso.hom.app n) c
  have houter := probeSdOuterLast_eq_last.{u} n x'
  change SimplexCategory.probeSdOuterLast n C =
    x'.simplex.obj (Fin.last x'.dim) at houter
  rw [houter, hxprime]
  refine (probeN_map_last p' c).trans ?_
  have hcFace := probeSdFlagCarrierChain_obj ⦋a.carrier.dim⦌ a.flag i
  change c = (probeFaceOrderIso ⦋a.carrier.dim⦌).symm
    (a.flag.obj i) at hcFace
  have hface : probeFaceOrderIso ⦋a.carrier.dim⦌ c =
      a.flag.obj i := by
    rw [hcFace, OrderIso.apply_symm_apply]
  have hmax := probeFaceOrderIso_last ⦋a.carrier.dim⦌ c
  rw [hface] at hmax
  have hmaxDown := congrArg ULift.down hmax
  change (SimplexCategory.sdChainLast ⦋a.carrier.dim⦌
      (a.flag.obj i)).down =
    SSet.stdSimplex.objEquiv c.simplex (Fin.last c.dim) at hmaxDown
  have hlastVertex := a.lastVertex_toSimplex_vertex i
  have hisoNat := (SSet.stdSimplex.sdIso.hom.app n).naturality_apply
    (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
    ((SSet.lastVertex.app
      (SSet.sd.obj (SSet.stdSimplex.obj n))).app
        (op ⦋k⦌) a.toSimplex)
  have hisoObjRaw := congrArg (fun z => z.obj 0) hisoNat
  have hisoObj :
      (((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋k⦌)
        ((SSet.lastVertex.app
          (SSet.sd.obj (SSet.stdSimplex.obj n))).app
            (op ⦋k⦌) a.toSimplex)).obj i) =
      ((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋0⦌)
        ((SSet.sd.obj (SSet.stdSimplex.obj n)).map
          (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
            ((SSet.lastVertex.app
              (SSet.sd.obj (SSet.stdSimplex.obj n))).app
                (op ⦋k⦌) a.toSimplex))).obj 0 := by
    change ((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋0⦌)
        ((SSet.sd.obj (SSet.stdSimplex.obj n)).map
          (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
            ((SSet.lastVertex.app
              (SSet.sd.obj (SSet.stdSimplex.obj n))).app
                (op ⦋k⦌) a.toSimplex))).obj 0 =
      (((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋k⦌)
        ((SSet.lastVertex.app
          (SSet.sd.obj (SSet.stdSimplex.obj n))).app
            (op ⦋k⦌) a.toSimplex)).obj i) at hisoObjRaw
    exact hisoObjRaw.symm
  have hIsoVertex := congrArg
    (fun z => ((SSet.stdSimplex.sdIso.hom.app n).app
      (op ⦋0⦌) z).obj 0) hlastVertex
  change ((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋0⦌)
      ((SSet.sd.obj (SSet.stdSimplex.obj n)).map
        (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
          ((SSet.lastVertex.app
            (SSet.sd.obj (SSet.stdSimplex.obj n))).app
              (op ⦋k⦌) a.toSimplex))).obj 0 =
    (p'.app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm
        (SimplexCategory.sdChainLast ⦋a.carrier.dim⦌
          (a.flag.obj i)).down)).obj 0 at hIsoVertex
  have hRhs :
      (((SSet.stdSimplex.sdIso.hom.app n).app (op ⦋k⦌)
        ((SSet.lastVertex.app
          (SSet.sd.obj (SSet.stdSimplex.obj n))).app
            (op ⦋k⦌) a.toSimplex)).obj i) =
      (p'.app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm
          (SimplexCategory.sdChainLast ⦋a.carrier.dim⦌
            (a.flag.obj i)).down)).obj 0 :=
    hisoObj.trans hIsoVertex
  rw [hmaxDown] at hRhs
  exact (probeMap_simplex_last p' c).trans hRhs.symm

private theorem probeRepresentableDoubleLastInner_eq
    (n : SimplexCategory) :
    probeRepresentableDoubleLastInner n =
      representableDoubleLastInner n := by
  rfl

private theorem probeRepresentableDoubleLastOuter_eq
    (n : SimplexCategory) :
    probeRepresentableDoubleLastOuter n =
      representableDoubleLastOuter n := by
  rfl

private theorem representableDoubleLastInner_eq (n : SimplexCategory) :
    representableDoubleLastInner n =
      SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})) := by
  calc
    _ = probeRepresentableDoubleLastInner n :=
      (probeRepresentableDoubleLastInner_eq n).symm
    _ = _ := probeInner_eq n

private theorem representableDoubleLastOuter_eq (n : SimplexCategory) :
    representableDoubleLastOuter n =
      SSet.lastVertex.app
        (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u})) := by
  calc
    _ = probeRepresentableDoubleLastOuter n :=
      (probeRepresentableDoubleLastOuter_eq n).symm
    _ = _ := probeOuter_eq n

private noncomputable abbrev representableDoubleLastActualHomotopy
    (n : SimplexCategory) :
    SSet.Homotopy
      (SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u})))
      (SSet.lastVertex.app
        (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u}))) where
  h := (representableDoubleLastHomotopy n).h
  h₀ := by
    change SSet.ι₀ ≫ (representableDoubleLastHomotopy n).h =
      SSet.sd.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj n : SSet.{u}))
    rw [(representableDoubleLastHomotopy n).h₀,
      representableDoubleLastInner_eq]
  h₁ := by
    change SSet.ι₁ ≫ (representableDoubleLastHomotopy n).h =
      SSet.lastVertex.app
        (SSet.sd.obj (SSet.stdSimplex.obj n : SSet.{u}))
    rw [(representableDoubleLastHomotopy n).h₁,
      representableDoubleLastOuter_eq]
  rel := (representableDoubleLastHomotopy n).rel

set_option backward.isDefEq.respectTransparency false in
private theorem representableDoubleLastHomotopy_chart_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
          (Δ[1] : SSet.{u})) ≫
        (representableDoubleLastHomotopy n).h ≫
        SSet.stdSimplex.sdIso.hom.app n =
      (representableDoubleLastHomotopy m).h ≫
        SSet.stdSimplex.sdIso.hom.app m ≫
        SimplexCategory.sd.{u}.map f := by
  calc
    _ = ((SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map f)) ▷
            (Δ[1] : SSet.{u})) ≫
          (representableDoubleLastHomotopy n).h) ≫
          SSet.stdSimplex.sdIso.hom.app n := by cat_disch
    _ = ((representableDoubleLastHomotopy m).h ≫
          SSet.sd.map (SSet.stdSimplex.map f)) ≫
          SSet.stdSimplex.sdIso.hom.app n := by
      rw [representableDoubleLastHomotopy_naturality f]
    _ = (representableDoubleLastHomotopy m).h ≫
          (SSet.sd.map (SSet.stdSimplex.map f) ≫
            SSet.stdSimplex.sdIso.hom.app n) := by cat_disch
    _ = (representableDoubleLastHomotopy m).h ≫
          (SSet.stdSimplex.sdIso.hom.app m ≫
            SimplexCategory.sd.{u}.map f) := by
      have hnat := SSet.stdSimplex.sdIso.hom.naturality f
      have hnat' :
          SSet.sd.map (SSet.stdSimplex.map f) ≫
              SSet.stdSimplex.sdIso.hom.app n =
            SSet.stdSimplex.sdIso.hom.app m ≫
              SimplexCategory.sd.{u}.map f := by
        simpa only [Functor.comp_map] using hnat
      simpa only [Category.assoc] using congrArg
        (fun k => (representableDoubleLastHomotopy m).h ≫ k) hnat'
    _ = _ := by cat_disch

private noncomputable def exUnit_ex_homotopy (X : SSet.{u}) :
    SSet.Homotopy
      (SSet.exUnit.app (SSet.ex.obj X))
      (SSet.ex.map (SSet.exUnit.app X)) :=
  packagedHomotopy
    (fun n => representableDoubleLastActualHomotopy n)
    (fun f => representableDoubleLastHomotopy_chart_naturality f)
    X

open scoped SSet.modelCategoryQuillen in
/-- Every component of the one-step Ex unit is a realization weak
equivalence. -/
theorem exUnit_app_mem_realizationWeakEquivalences (X : SSet.{u}) :
    SSet.realizationWeakEquivalences (SSet.exUnit.app X) := by
  have hpre : ∀ (Z : SSet.{u}), Z.KanComplex → Function.Bijective
      (fun q : RightHomotopyClass (SSet.ex.obj X) Z =>
        q.precomp (SSet.exUnit.app X)) := by
    intro Z hZ
    let _ : Z.KanComplex := hZ
    let _ : SSet.KanComplex (SSet.ex.obj Z) := by
      change HomotopicalAlgebra.IsFibrant (SSet.ex.obj Z)
      rw [HomotopicalAlgebra.isFibrant_iff]
      have hcomp : SSet.ex.map (terminal.from Z) ≫
          terminalComparison SSet.ex.{u} =
            terminal.from (SSet.ex.obj Z) := Subsingleton.elim _ _
      rw [← hcomp]
      infer_instance
    let _ : WeakEquivalence (SSet.exUnit.app Z) :=
      (weakEquivalence_iff _).mpr
        (exUnit_app_mem_realizationWeakEquivalences_of_kanComplex Z)
    exact exUnit_precomp_rightHomotopyClass_bijective
      SSet.exUnit exUnit_ex_homotopy X Z
  have hWeak : WeakEquivalence (SSet.exUnit.app X) :=
    weakEquivalence_of_precomp_rightClass_bijective
      (SSet.exUnit.app X) hpre
  exact (weakEquivalence_iff _).mp hWeak

end SSet

end

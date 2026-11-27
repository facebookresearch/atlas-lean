/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SplitHomotopyEquivOver
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOverTrivialFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Contractions of simplicial objects over a fixed base

A trivial Kan–Quillen fibration `E → B` has a strict section and a homotopy over `B`
from projection followed by section to the identity of `E`. For a simplicial object
in the set slice over `A`, this yields a simplicial section and contraction of its point
map to the constant terminal slice object, with every prism operator remaining over `A`.

Any functor from the slice to a preadditive category transports this contraction to a
chain homotopy equivalence of alternating-face complexes. In an abelian target the
alternating map induced by the point augmentation is consequently a quasi-isomorphism.
The base-set, target-object, and target-morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite HomotopicalAlgebra AlgebraicTopology
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

universe u v w

namespace SSet.SplitHomotopyEquivOver

/--
The split homotopy equivalence over `B` associated to a trivial fibration `p : E → B`:
a strict section of `p` and a homotopy over `B` from `p` followed by that section to
the identity of `E`.
-/
def ofTrivialFibration {E B : SSet.{u}} (p : E ⟶ B)
    (hp : trivialFibrations SSet.{u} p) : SSet.SplitHomotopyEquivOver p := by
  let d : ((⊥ : B.Subcomplex) : SSet.{u}) ⟶ B := (⊥ : B.Subcomplex).ι
  let a : ((⊥ : B.Subcomplex) : SSet.{u}) ⟶ E :=
    (SSet.Subcomplex.isInitialBot (X := B)).to E
  letI : Cofibration d := SSet.modelCategoryQuillen.cofibration_of_mono d
  letI : Fibration p := (mem_trivialFibrations_iff p).mp hp |>.1
  letI : WeakEquivalence p := (mem_trivialFibrations_iff p).mp hp |>.2
  letI : HasLiftingProperty d p := ModelCategory.cm4b d p
  let sq : CommSq a d p (𝟙 B) :=
    ⟨(SSet.Subcomplex.isInitialBot (X := B)).hom_ext _ _⟩
  let s : B ⟶ E := sq.lift
  have hs : s ≫ p = 𝟙 B := sq.fac_right
  refine
    { section_ := s
      section_comp := hs
      homotopyOver := SSet.HomotopyRelOver.ofTrivialFibration
        (⊥ : E.Subcomplex) p hp (p ≫ s) (𝟙 E)
        ((SSet.Subcomplex.isInitialBot (X := E)).hom_ext _ _) ?_ }
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

end SSet.SplitHomotopyEquivOver

namespace CategoryTheory.SimplicialObject

variable {A : Type u} (X : SimplicialObject (Over A))

/--
The simplicial set obtained by forgetting the maps to `A` from a simplicial object
in `Over A`.
-/
abbrev sliceUnderlying : SSet.{u} := X ⋙ Over.forget A

/--
The simplicial map from the underlying diagram to the constant set `A`, whose
components are the structure maps of its slice objects.
-/
def slicePoint : sliceUnderlying X ⟶ (SimplicialObject.const (Type u)).obj A where
  app i := (X.obj i).hom
  naturality {i j} f := by
    change (X.map f).left ≫ (X.obj j).hom = (X.obj i).hom ≫ 𝟙 A
    rw [Category.comp_id]
    exact (X.map f).w

/--
The simplicial map in `Over A` from the diagram to the constant object `A → A`.
-/
def slicePointOver : X ⟶
    (SimplicialObject.const (Over A)).obj (Over.mk (𝟙 A)) where
  app i := Over.homMk (X.obj i).hom (by
    change (X.obj i).hom ≫ 𝟙 A = (X.obj i).hom
    exact Category.comp_id _)
  naturality {i j} f := by
    apply Over.OverMorphism.ext
    change (X.map f).left ≫ (X.obj j).hom = (X.obj i).hom ≫ 𝟙 A
    rw [Category.comp_id]
    exact (X.map f).w

/--
If the underlying point map is a trivial fibration, its strict section as a simplicial
map from the constant terminal object of `Over A` to the given diagram.
-/
def sliceSectionOfTrivialFibration
    (hp : trivialFibrations SSet.{u} (slicePoint X)) :
    (SimplicialObject.const (Over A)).obj (Over.mk (𝟙 A)) ⟶ X where
  app i := Over.homMk
    ((SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X) hp).section_.app i)
    (congrArg (fun f => f.app i)
      (SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X) hp).section_comp)
  naturality {i j} f := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X) hp).section_.naturality f

/--
The section of a trivial point fibration followed by the slice point map is the
identity on the constant terminal slice object.
-/
@[reassoc]
theorem sliceSectionOfTrivialFibration_point
    (hp : trivialFibrations SSet.{u} (slicePoint X)) :
    sliceSectionOfTrivialFibration X hp ≫ slicePointOver X =
      𝟙 ((SimplicialObject.const (Over A)).obj (Over.mk (𝟙 A))) := by
  apply NatTrans.ext
  funext i
  apply Over.OverMorphism.ext
  exact congrArg (fun f => f.app i)
    (SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X) hp).section_comp

/--
Every contraction prism operator commutes with the structure map to `A`, sending
the degree-`n` point map to the degree-`n + 1` point map after the operator.
-/
theorem sliceContraction_operator_point
    (hp : trivialFibrations SSet.{u} (slicePoint X)) {n : ℕ} (i : Fin (n + 1)) :
    ((SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X)
      hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h
        i) ≫
        (X.obj (op ⦋n + 1⦌)).hom = (X.obj (op ⦋n⦌)).hom := by
  let p := slicePoint X
  let E := SSet.SplitHomotopyEquivOver.ofTrivialFibration p hp
  let H := E.homotopyOver.toHomotopyRel.toHomotopy
  have hOver : H.h ≫ p = fst _ _ ≫ p := by
    change E.homotopyOver.h ≫ p = _
    rw [E.homotopyOver.over_eq, Category.assoc, E.section_comp, Category.comp_id]
  ext x
  let z : ((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj (op ⦋n + 1⦌) :=
    (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1
  let y : (Δ[n] : SSet.{u}) ⟶ sliceUnderlying X := SSet.yonedaEquiv.symm x
  have h := congrArg
    (fun f => f.app (op ⦋n + 1⦌) ((y ▷ (Δ[1] : SSet.{u})).app (op ⦋n + 1⦌) z))
    hOver
  change p.app (op ⦋n + 1⦌) (H.toSimplicialObjectHomotopy.h i x) =
    p.app (op ⦋n + 1⦌) (y.app (op ⦋n + 1⦌) z.1) at h
  have hn := congrArg (fun f => f x)
    (p.naturality (SSet.stdSimplex.objEquiv z.1).op)
  change p.app (op ⦋n + 1⦌)
    ((sliceUnderlying X).map (SSet.stdSimplex.objEquiv z.1).op x) =
      p.app (op ⦋n⦌) x at hn
  rw [SSet.yonedaEquiv_symm_app] at h
  exact h.trans hn

/--
The simplicial homotopy in `Over A` from the point map followed by its strict section
to the identity of the given simplicial slice diagram.
-/
def sliceContractionOfTrivialFibration
    (hp : trivialFibrations SSet.{u} (slicePoint X)) :
    SimplicialObject.Homotopy
      (slicePointOver X ≫ sliceSectionOfTrivialFibration X hp) (𝟙 X) where
  h i := Over.homMk
    ((SSet.SplitHomotopyEquivOver.ofTrivialFibration (slicePoint X)
      hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h
        i)
    (sliceContraction_operator_point X hp i)
  h_zero_comp_δ_zero n := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_zero_comp_δ_zero
        n
  h_last_comp_δ_last n := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_last_comp_δ_last
        n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt
        i j hij
  h_succ_comp_δ_castSucc_succ j := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ
        j
  h_castSucc_comp_δ_succ_of_lt i j hij := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt
        i j hij
  h_comp_σ_castSucc_of_le i j hij := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_comp_σ_castSucc_of_le
        i j hij
  h_comp_σ_succ_of_lt i j hij := by
    apply Over.OverMorphism.ext
    exact (SSet.SplitHomotopyEquivOver.ofTrivialFibration
      (slicePoint X) hp).homotopyOver.toHomotopyRel.toHomotopy.toSimplicialObjectHomotopy.h_comp_σ_succ_of_lt
        i j hij

/--
For any functor `F : Over A ⥤ D` to a preadditive category, a trivial underlying
point fibration yields a chain homotopy equivalence between the alternating complex
of the diagram after `F` and that of the constant terminal slice object after `F`.
-/
def alternatingSlicePointHomotopyEquiv
    {D : Type v} [Category.{w} D] [Preadditive D] (F : Over A ⥤ D)
    (hp : trivialFibrations SSet.{u} (slicePoint X)) :
    HomotopyEquiv ((alternatingFaceMapComplex D).obj (X ⋙ F))
      ((alternatingFaceMapComplex D).obj
        (((SimplicialObject.const (Over A)).obj (Over.mk (𝟙 A))) ⋙ F)) where
  hom := (alternatingFaceMapComplex D).map (Functor.whiskerRight (slicePointOver X) F)
  inv := (alternatingFaceMapComplex D).map
    (Functor.whiskerRight (sliceSectionOfTrivialFibration X hp) F)
  homotopyHomInvId := by
    simpa only [SimplicialObject.whiskering, Functor.whiskeringRight,
      Functor.map_comp, Functor.map_id, Functor.whiskerRight_comp,
      Functor.whiskerRight_id'] using
        ((sliceContractionOfTrivialFibration X hp).whiskerRight F).toChainHomotopy
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← Functor.map_comp, ← Functor.whiskerRight_comp,
      sliceSectionOfTrivialFibration_point, Functor.whiskerRight_id', Functor.map_id])

/--
For a functor from `Over A` to an abelian category, the point map of a simplicial
slice diagram induces an alternating-face quasi-isomorphism if its underlying
simplicial-set point map is a trivial fibration.
-/
theorem quasiIso_alternatingSlicePoint
    {D : Type v} [Category.{w} D] [Abelian D] (F : Over A ⥤ D)
    (hp : trivialFibrations SSet.{u} (slicePoint X)) :
    QuasiIso ((alternatingFaceMapComplex D).map
      (Functor.whiskerRight (slicePointOver X) F)) :=
  (alternatingSlicePointHomotopyEquiv X F hp).quasiIso_hom

end CategoryTheory.SimplicialObject

end

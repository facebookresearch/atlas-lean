/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Tests for binary products of direct simplicial-set realization in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped MonoidalCategory Simplicial

namespace MathlibExtTest.SSet.CGWHRealizationProductTests

section PublicSurface

#check SSet.realizationProdIsoCGWH
#check SSet.realizationProdIsoCGWH_hom
#check SSet.toCGWH_preservesBinaryProducts
#check SSet.realizationProdIsoCGWH_hom_fst
#check SSet.realizationProdIsoCGWH_hom_snd
#check SSet.realizationProdIsoCGWH_naturality
#check SSet.realizationProdIsoCGWH_forget

end PublicSurface

section Core

variable (X Y : SSet.{v})

example : SSet.toCGWH.{u, v}.obj (X ⨯ Y) ≅
    SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y :=
  SSet.realizationProdIsoCGWH X Y

example : (SSet.realizationProdIsoCGWH.{u, v} X Y).hom =
    Limits.prodComparison SSet.toCGWH.{u, v} X Y :=
  SSet.realizationProdIsoCGWH_hom X Y

example : PreservesLimitsOfShape (Discrete WalkingPair)
    SSet.toCGWH.{u, v} := inferInstance

example : IsIso (Limits.prodComparison SSet.toCGWH.{u, v} X Y) :=
  inferInstance

example : Function.Bijective
    (CGWH.prodComparisonToTop
      (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y)) :=
  CGWH.prodComparisonToTop_bijective _ _

example : (SSet.realizationProdIsoCGWH.{u, v} X Y).hom ≫
      Limits.prod.fst =
    SSet.toCGWH.{u, v}.map (Limits.prod.fst : X ⨯ Y ⟶ X) :=
  SSet.realizationProdIsoCGWH_hom_fst X Y

example : (SSet.realizationProdIsoCGWH.{u, v} X Y).hom ≫
      Limits.prod.snd =
    SSet.toCGWH.{u, v}.map (Limits.prod.snd : X ⨯ Y ⟶ Y) :=
  SSet.realizationProdIsoCGWH_hom_snd X Y

example :
    (SSet.realizationProdIsoCGWH.{u, v} X Y).hom ≫
        (SSet.realizationProdIsoCGWH X Y).inv = 𝟙 _ := by
  exact (SSet.realizationProdIsoCGWH X Y).hom_inv_id

example :
    (SSet.realizationProdIsoCGWH.{u, v} X Y).inv ≫
        (SSet.realizationProdIsoCGWH X Y).hom = 𝟙 _ := by
  exact (SSet.realizationProdIsoCGWH X Y).inv_hom_id

example {X X' Y Y' : SSet.{v}} (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.toCGWH.{u, v}.map (Limits.prod.map f g) ≫
        (SSet.realizationProdIsoCGWH X' Y').hom =
      (SSet.realizationProdIsoCGWH X Y).hom ≫
        Limits.prod.map (SSet.toCGWH.map f) (SSet.toCGWH.map g) :=
  SSet.realizationProdIsoCGWH_naturality f g

example :
    CGWH.cgwhToTop.{u, v}.map
          (SSet.realizationProdIsoCGWH X Y).hom ≫
        CGWH.prodComparisonToTop
          (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y) =
      (SSet.realizationToTopIso.{u, v}).hom.app (X ⨯ Y) ≫
        Limits.prodComparison SSet.toTop X Y ≫
        Limits.prod.map
          ((SSet.realizationToTopIso.{u, v}).inv.app X)
          ((SSet.realizationToTopIso.{u, v}).inv.app Y) ≫
        (TopCat.prodIsoProd
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj X))
          (CGWH.cgwhToTop.obj (SSet.toCGWH.{u, v}.obj Y))).hom :=
  SSet.realizationProdIsoCGWH_forget X Y

end Core

section Coherence

variable (X Y Z K : SSet.{v})

example :
    SSet.toCGWH.{u, v}.map (Limits.prod.braiding X Y).hom ≫
        (SSet.realizationProdIsoCGWH Y X).hom =
      (SSet.realizationProdIsoCGWH X Y).hom ≫
        (Limits.prod.braiding
          (SSet.toCGWH.{u, v}.obj X)
          (SSet.toCGWH.{u, v}.obj Y)).hom := by
  simpa only [SSet.realizationProdIsoCGWH_hom] using
    (Limits.map_braiding_hom_comp_prodComparison
      SSet.toCGWH.{u, v} (A := Y) (B := X))

example :
    SSet.toCGWH.{u, v}.map (Limits.prod.associator X Y Z).hom ≫
        (SSet.realizationProdIsoCGWH X (Y ⨯ Z)).hom ≫
        Limits.prod.map (𝟙 _)
          (SSet.realizationProdIsoCGWH Y Z).hom =
      (SSet.realizationProdIsoCGWH (X ⨯ Y) Z).hom ≫
        Limits.prod.map (SSet.realizationProdIsoCGWH X Y).hom (𝟙 _) ≫
        (Limits.prod.associator
          (SSet.toCGWH.{u, v}.obj X)
          (SSet.toCGWH.{u, v}.obj Y)
          (SSet.toCGWH.{u, v}.obj Z)).hom := by
  simp only [SSet.realizationProdIsoCGWH_hom]
  apply Limits.prod.hom_ext
  · simp
    rw [← SSet.toCGWH.map_comp, ← SSet.toCGWH.map_comp]
    simp
  · apply Limits.prod.hom_ext
    · simp
      rw [← Category.assoc, ← SSet.toCGWH.map_comp,
        ← SSet.toCGWH.map_comp, ← SSet.toCGWH.map_comp]
      simp
    · simp
      rw [← Category.assoc, ← SSet.toCGWH.map_comp,
        ← SSet.toCGWH.map_comp]
      simp

example (f : K ⟶ X) (g : K ⟶ Y) :
    SSet.toCGWH.{u, v}.map (Limits.prod.lift f g) ≫
        (SSet.realizationProdIsoCGWH X Y).hom =
      Limits.prod.lift (SSet.toCGWH.map f) (SSet.toCGWH.map g) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_fst,
      Limits.prod.lift_fst, ← SSet.toCGWH.map_comp, Limits.prod.lift_fst]
  · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_snd,
      Limits.prod.lift_snd, ← SSet.toCGWH.map_comp, Limits.prod.lift_snd]

example (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    SSet.toCGWH.{u, v}.map
          (Limits.prod.lift (SSet.const (X := K) x) (SSet.const (X := K) y)) ≫
        (SSet.realizationProdIsoCGWH X Y).hom =
      Limits.prod.lift
        (SSet.toCGWH.map (SSet.const (X := K) x))
        (SSet.toCGWH.map (SSet.const (X := K) y)) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_fst,
      Limits.prod.lift_fst, ← SSet.toCGWH.map_comp, Limits.prod.lift_fst]
  · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_snd,
      Limits.prod.lift_snd, ← SSet.toCGWH.map_comp, Limits.prod.lift_snd]

example (x : X _⦋0⦌) :
    SSet.realizedVertex x =
      SSet.toTop.map (SSet.const (X := Δ[0]) x) default :=
  SSet.realizedVertex_eq_const x

example (y : Y _⦋0⦌) :
    SSet.realizedVertex y =
      SSet.toTop.map (SSet.const (X := Δ[0]) y) default :=
  SSet.realizedVertex_eq_const y

end Coherence

section Vertex

variable (X Y : SSet.{v}) (z : (X ⨯ Y) _⦋0⦌)

example :
    CGWH.prodComparisonToTop
        (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y)
      (CGWH.cgwhToTop.map
        (SSet.realizationProdIsoCGWH X Y).hom (SSet.realizedVertex z)) =
      (SSet.realizedVertex
          ((Limits.prod.fst : X ⨯ Y ⟶ X).app _ z),
        SSet.realizedVertex
          ((Limits.prod.snd : X ⨯ Y ⟶ Y).app _ z)) := by
  apply Prod.ext
  · have hf := congrArg (fun q ↦ q ≫ TopCat.prodFst)
      (SSet.realizationProdIsoCGWH_forget.{u, v} X Y)
    dsimp [SSet.realizationToTopIso] at hf
    simp at hf
    have hp := ConcreteCategory.congr_hom hf (SSet.realizedVertex z)
    rw [SSet.realizationProdIsoCGWH_hom]
    exact hp.trans
      (SSet.realizedVertex_naturality
        (Limits.prod.fst : X ⨯ Y ⟶ X) z).symm
  · have hs := congrArg (fun q ↦ q ≫ TopCat.prodSnd)
      (SSet.realizationProdIsoCGWH_forget.{u, v} X Y)
    dsimp [SSet.realizationToTopIso] at hs
    simp at hs
    have hp := ConcreteCategory.congr_hom hs (SSet.realizedVertex z)
    rw [SSet.realizationProdIsoCGWH_hom]
    exact hp.trans
      (SSet.realizedVertex_naturality
        (Limits.prod.snd : X ⨯ Y ⟶ Y) z).symm

end Vertex

section UniverseMatrix

#check @SSet.realizationProdIsoCGWH.{0, 0}
#check @SSet.realizationProdIsoCGWH.{1, 1}
#check @SSet.realizationProdIsoCGWH.{0, 1}
#check @SSet.realizationProdIsoCGWH.{1, 0}

#check @SSet.realizationProdIsoCGWH_hom.{0, 0}
#check @SSet.realizationProdIsoCGWH_hom.{1, 1}
#check @SSet.realizationProdIsoCGWH_hom.{0, 1}
#check @SSet.realizationProdIsoCGWH_hom.{1, 0}

#check @SSet.realizationProdIsoCGWH_hom_fst.{0, 0}
#check @SSet.realizationProdIsoCGWH_hom_fst.{1, 1}
#check @SSet.realizationProdIsoCGWH_hom_fst.{0, 1}
#check @SSet.realizationProdIsoCGWH_hom_fst.{1, 0}

#check @SSet.realizationProdIsoCGWH_hom_snd.{0, 0}
#check @SSet.realizationProdIsoCGWH_hom_snd.{1, 1}
#check @SSet.realizationProdIsoCGWH_hom_snd.{0, 1}
#check @SSet.realizationProdIsoCGWH_hom_snd.{1, 0}

#check @SSet.realizationProdIsoCGWH_naturality.{0, 0}
#check @SSet.realizationProdIsoCGWH_naturality.{1, 1}
#check @SSet.realizationProdIsoCGWH_naturality.{0, 1}
#check @SSet.realizationProdIsoCGWH_naturality.{1, 0}

#check @SSet.realizationProdIsoCGWH_forget.{0, 0}
#check @SSet.realizationProdIsoCGWH_forget.{1, 1}
#check @SSet.realizationProdIsoCGWH_forget.{0, 1}
#check @SSet.realizationProdIsoCGWH_forget.{1, 0}
#check @SSet.realizationProdIsoCGWH_forget.{u, v}

#synth PreservesLimitsOfShape (Discrete WalkingPair) SSet.toCGWH.{0, 0}
#synth PreservesLimitsOfShape (Discrete WalkingPair) SSet.toCGWH.{1, 1}
#synth PreservesLimitsOfShape (Discrete WalkingPair) SSet.toCGWH.{0, 1}
#synth PreservesLimitsOfShape (Discrete WalkingPair) SSet.toCGWH.{1, 0}

end UniverseMatrix

section FiniteTransports

variable (A B : SSet.{v}) [A.Finite] [B.Finite]

example : True := by
  fail_if_success
    let _ : SSet.Finite (A ⨯ B) := inferInstance
  fail_if_success
    let _ : T2Space ↑(SSet.toTop.obj A ⨯ SSet.toTop.obj B) :=
      inferInstance
  fail_if_success
    let _ : CompactSpace (SSet.toCGWH.{u, v}.obj A) := inferInstance
  fail_if_success
    let _ : T2Space (SSet.toCGWH.{u, v}.obj A) := inferInstance
  fail_if_success
    let _ : LocallyCompactSpace (SSet.toCGWH.{u, v}.obj A) :=
      inferInstance
  let tensorProdIso : A ⊗ B ≅ A ⨯ B :=
    IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B)
      (limit.isLimit _)
  let _ : SSet.Finite (A ⨯ B) :=
    SSet.finite_of_iso tensorProdIso
  have : CompactSpace (SSet.toTop.obj (A ⨯ B)) := inferInstance
  let selectedToRaw := TopCat.homeoOfIso
    (TopCat.prodIsoProd (SSet.toTop.obj A) (SSet.toTop.obj B))
  let _ : T2Space ↑(SSet.toTop.obj A ⨯ SSet.toTop.obj B) :=
    selectedToRaw.symm.t2Space
  have : T2Space ↑(SSet.toTop.obj A ⨯ SSet.toTop.obj B) :=
    inferInstance
  let eA := TopCat.homeoOfIso
    (SSet.realizationToTopIso.{u, v}.app A)
  let _ : CompactSpace (SSet.toCGWH.{u, v}.obj A) :=
    eA.symm.compactSpace
  let _ : T2Space (SSet.toCGWH.{u, v}.obj A) :=
    eA.symm.t2Space
  let _ : LocallyCompactSpace (SSet.toCGWH.{u, v}.obj A) :=
    inferInstance
  have : LocallyCompactSpace (SSet.toCGWH.{u, v}.obj A) :=
    inferInstance
  have _ := SSet.realizationProdIsoCGWH.{u, v} A B
  trivial

end FiniteTransports

section Negative

variable (X Y : SSet.{v})

example : True := by
  fail_if_success
    let _ : PreservesLimitsOfShape (Discrete WalkingPair)
      SSet.toTop.{v} := inferInstance
  fail_if_success
    let _ : IsIso (Limits.prodComparison SSet.toTop X Y) := inferInstance
  fail_if_success
    let _ : IsIso (CGWH.prodComparisonToTop
      (SSet.toCGWH.{u, v}.obj X) (SSet.toCGWH.{u, v}.obj Y)) :=
      inferInstance
  fail_if_success
    have : CGWH.cgwhToTop.obj
        (SSet.toCGWH.{u, v}.obj X ⨯ SSet.toCGWH.{u, v}.obj Y) =
      TopCat.of (↑(SSet.toTop.obj X) × ↑(SSet.toTop.obj Y)) := rfl
  trivial

/-- error: Unknown identifier `ProductAdmissible` -/
#guard_msgs (error, substring := true) in
#check ProductAdmissible

/-- error: Unknown identifier `prodComparison_toTop_bijective` -/
#guard_msgs (error, substring := true) in
#check prodComparison_toTop_bijective

/-- error: Unknown identifier `prodComparison_forget` -/
#guard_msgs (error, substring := true) in
#check prodComparison_forget

/-- error: Unknown identifier `prodComparison_toCGWH_bijective` -/
#guard_msgs (error, substring := true) in
#check prodComparison_toCGWH_bijective

/-- error: Unknown identifier `prodComparison_toTop_isIso_of_finite` -/
#guard_msgs (error, substring := true) in
#check prodComparison_toTop_isIso_of_finite

/-- error: Unknown identifier `prodComparison_toCGWH_isIso_of_finite` -/
#guard_msgs (error, substring := true) in
#check prodComparison_toCGWH_isIso_of_finite

/-- error: Unknown identifier `exists_finite_subcomplex_factor` -/
#guard_msgs (error, substring := true) in
#check exists_finite_subcomplex_factor

/-- error: Unknown identifier `prodComparison_inverse_continuous` -/
#guard_msgs (error, substring := true) in
#check prodComparison_inverse_continuous

/-- error: Unknown identifier `realizationProdIsoCGWH_exists` -/
#guard_msgs (error, substring := true) in
#check realizationProdIsoCGWH_exists

/-- error: Unknown constant `CGWH.modelCategory` -/
#guard_msgs (error, substring := true) in
#check CGWH.modelCategory

/-- error: Unknown constant `SSet.sSetCGWHQuillenAdj` -/
#guard_msgs (error, substring := true) in
#check SSet.sSetCGWHQuillenAdj

end Negative

end MathlibExtTest.SSet.CGWHRealizationProductTests

#print axioms SSet.realizationProdIsoCGWH
#print axioms SSet.realizationProdIsoCGWH_hom
#print axioms SSet.toCGWH_preservesBinaryProducts
#print axioms SSet.realizationProdIsoCGWH_hom_fst
#print axioms SSet.realizationProdIsoCGWH_hom_snd
#print axioms SSet.realizationProdIsoCGWH_naturality
#print axioms SSet.realizationProdIsoCGWH_forget

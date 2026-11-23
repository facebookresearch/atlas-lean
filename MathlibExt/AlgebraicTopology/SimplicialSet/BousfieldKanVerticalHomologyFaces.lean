/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalHomology

/-!
# Horizontal faces on Bousfield--Kan vertical homology

The coproduct isomorphism computing vertical homology of the Bousfield--Kan
bicomplex commutes with every outer face.  The zeroth face uses functoriality
of coefficient homology; the last and interior faces additionally use
functoriality on equality transports.

These are facewise results.  They identify the input needed for the
horizontal alternating differential.  Packaging into a complex occurs in
`BousfieldKanVerticalHomologyComplex`; the page and convergence statements
are in `BousfieldKanSpectralSequence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v

namespace SSet

variable {J : Type w} [Category.{v} J]

/-- Homology carries the equality transport used by the last weighted-bar
face to the corresponding equality transport on homology. -/
theorem wbarFaceLastComponent_homology
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    {n : ℕ} (s : SrepBridge.SrepIdx J (n + 1)) (q : ℕ) :
    SSet.homologyMap (SrepBridge.srepFaceLastComponent D s) R q =
      SrepBridge.srepFaceLastComponent
        (D ⋙ SSet.homologyFunctor R q) s := by
  unfold SrepBridge.srepFaceLastComponent
  exact CategoryTheory.eqToHom_map (SSet.homologyFunctor R q) _

/-- Homology carries the equality transport used by an interior weighted-
bar face to the corresponding equality transport on homology. -/
theorem wbarFaceInnerComponent_homology
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    {n : ℕ} (i : Fin (n + 2)) (hi0 : i ≠ 0)
    [NeZero (n + 1)] (s : SrepBridge.SrepIdx J (n + 1)) (q : ℕ) :
    SSet.homologyMap
        (StrictOrdinaryWeightedBar.wFaceInnerComponent D i hi0 s) R q =
      StrictOrdinaryWeightedBar.wFaceInnerComponent
        (D ⋙ SSet.homologyFunctor R q) i hi0 s := by
  unfold StrictOrdinaryWeightedBar.wFaceInnerComponent
  exact CategoryTheory.eqToHom_map (SSet.homologyFunctor R q) _

/-- Last-face map obtained by applying homology to every coefficient
component. -/
noncomputable def wbarVerticalHomologyFaceLast
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (n q : ℕ) :
    (∐ fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) ⟶
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n =>
          (D.obj x.1.left).homology R q :=
  Sigma.map'
    (StrictOrdinaryWeightedBar.wFaceLastIdx
      (CategoryBar.replUnit J) n)
    (fun x => SSet.homologyMap
      (SrepBridge.srepFaceLastComponent D x.1) R q)

@[reassoc]
theorem wbarVerticalHomologyFaceLast_ι
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ)
    (x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1)) :
    Sigma.ι (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) x ≫
        wbarVerticalHomologyFaceLast R D n q =
      SSet.homologyMap
          (SrepBridge.srepFaceLastComponent D x.1) R q ≫
        Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n =>
            (D.obj y.1.left).homology R q)
          (StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit J) n x) := by
  exact Sigma.ι_comp_map' _ _ _

/-- Last face of the weighted bar on the homology diagram, retyped on the
expanded coproduct objects. -/
noncomputable def wbarVerticalHomologyTargetFaceLast
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (n q : ℕ) :
    (∐ fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) ⟶
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n =>
          (D.obj x.1.left).homology R q :=
  StrictOrdinaryWeightedBar.wbarFaceLast
    (CategoryBar.replUnit J) (D ⋙ SSet.homologyFunctor R q) n

@[reassoc]
theorem wbarVerticalHomologyTargetFaceLast_ι
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ)
    (x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1)) :
    Sigma.ι (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) x ≫
        wbarVerticalHomologyTargetFaceLast R D n q =
      SrepBridge.srepFaceLastComponent
          (D ⋙ SSet.homologyFunctor R q) x.1 ≫
        Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n =>
            (D.obj y.1.left).homology R q)
          (StrictOrdinaryWeightedBar.wFaceLastIdx
            (CategoryBar.replUnit J) n x) := by
  exact StrictOrdinaryWeightedBar.wbarFaceLast_ι
    (CategoryBar.replUnit J) (D ⋙ SSet.homologyFunctor R q) n x

/-- Interior-face map obtained by applying homology to every coefficient
component. -/
noncomputable def wbarVerticalHomologyFaceInner
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)] :
    (∐ fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) ⟶
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n =>
          (D.obj x.1.left).homology R q :=
  Sigma.map'
    (StrictOrdinaryWeightedBar.wFaceInnerIdx
      (CategoryBar.replUnit J) n i hiLast)
    (fun x => SSet.homologyMap
      (StrictOrdinaryWeightedBar.wFaceInnerComponent D i hi0 x.1) R q)

@[reassoc]
theorem wbarVerticalHomologyFaceInner_ι
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)]
    (x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1)) :
    Sigma.ι (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) x ≫
        wbarVerticalHomologyFaceInner R D n q i hi0 hiLast =
      SSet.homologyMap
          (StrictOrdinaryWeightedBar.wFaceInnerComponent
            D i hi0 x.1) R q ≫
        Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n =>
            (D.obj y.1.left).homology R q)
          (StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit J) n i hiLast x) := by
  exact Sigma.ι_comp_map' _ _ _

/-- Interior face of the weighted bar on the homology diagram, retyped on
the expanded coproduct objects. -/
noncomputable def wbarVerticalHomologyTargetFaceInner
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)] :
    (∐ fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) ⟶
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) n =>
          (D.obj x.1.left).homology R q :=
  StrictOrdinaryWeightedBar.wbarFaceInner
    (CategoryBar.replUnit J) (D ⋙ SSet.homologyFunctor R q)
      n i hi0 hiLast

@[reassoc]
theorem wbarVerticalHomologyTargetFaceInner_ι
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)]
    (x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1)) :
    Sigma.ι (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) =>
        (D.obj x.1.left).homology R q) x ≫
        wbarVerticalHomologyTargetFaceInner R D n q i hi0 hiLast =
      StrictOrdinaryWeightedBar.wFaceInnerComponent
          (D ⋙ SSet.homologyFunctor R q) i hi0 x.1 ≫
        Sigma.ι (fun y : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n =>
            (D.obj y.1.left).homology R q)
          (StrictOrdinaryWeightedBar.wFaceInnerIdx
            (CategoryBar.replUnit J) n i hiLast x) := by
  exact StrictOrdinaryWeightedBar.wbarFaceInner_ι
    (CategoryBar.replUnit J) (D ⋙ SSet.homologyFunctor R q)
      n i hi0 hiLast x

/-- Lightweight weighted-bar form of the vertical homology coproduct
isomorphism. -/
noncomputable def wbarVerticalHomologyIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (p q : ℕ) :
    (StrictOrdinaryWeightedBar.wbarObj
      (CategoryBar.replUnit J) D p).homology R q ≅
      ∐ fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) p =>
          (D.obj x.1.left).homology R q :=
  homologySigmaIso
    (fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) p => D.obj x.1.left) R q
-- Explicit diagram parameters keep elaboration of the dependent coproduct map bounded.
/-- The vertical homology coproduct isomorphism commutes with the zeroth
outer face. -/
theorem wbarVerticalHomologyIso_faceZero
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) :
    SSet.homologyMap
        (StrictOrdinaryWeightedBar.wbarFaceZero
          (CategoryBar.replUnit J) D n) R q ≫
        (wbarVerticalHomologyIso R D n q).hom =
      (wbarVerticalHomologyIso R D (n + 1) q).hom ≫
        StrictOrdinaryWeightedBar.wbarFaceZero
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n := by
  change SSet.homologyMap
      (Sigma.map'
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit J) n)
        (fun x => SrepBridge.srepFaceZeroComponent D x.1)) R q ≫
      (homologySigmaIso
        (fun x : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => D.obj x.1.left) R q).hom =
    (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left) R q).hom ≫
      Sigma.map'
        (StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit J) n)
        (fun x => SSet.homologyMap
          (SrepBridge.srepFaceZeroComponent D x.1) R q)
  exact homologySigmaIso_naturality
    (F := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left)
    (G := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => D.obj x.1.left)
    (StrictOrdinaryWeightedBar.wFaceZeroIdx
      (CategoryBar.replUnit J) n)
    (fun x => SrepBridge.srepFaceZeroComponent D x.1) R q
-- Explicit diagram parameters keep elaboration of the dependent coproduct map bounded.
/-- The vertical homology coproduct isomorphism commutes with the last outer
face. -/
theorem wbarVerticalHomologyIso_faceLast
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) :
    SSet.homologyMap
        (StrictOrdinaryWeightedBar.wbarFaceLast
          (CategoryBar.replUnit J) D n) R q ≫
        (wbarVerticalHomologyIso R D n q).hom =
      (wbarVerticalHomologyIso R D (n + 1) q).hom ≫
        StrictOrdinaryWeightedBar.wbarFaceLast
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n := by
  change SSet.homologyMap
      (Sigma.map'
        (StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit J) n)
        (fun x => SrepBridge.srepFaceLastComponent D x.1)) R q ≫
      (homologySigmaIso
        (fun x : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => D.obj x.1.left) R q).hom =
    (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left) R q).hom ≫
      StrictOrdinaryWeightedBar.wbarFaceLast
        (CategoryBar.replUnit J)
        (D ⋙ SSet.homologyFunctor R q) n
  have hNat := homologySigmaIso_naturality
    (F := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left)
    (G := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => D.obj x.1.left)
    (StrictOrdinaryWeightedBar.wFaceLastIdx
      (CategoryBar.replUnit J) n)
    (fun x => SrepBridge.srepFaceLastComponent D x.1) R q
  change _ = _ ≫ wbarVerticalHomologyFaceLast R D n q at hNat
  have hFace :
      wbarVerticalHomologyFaceLast R D n q =
      wbarVerticalHomologyTargetFaceLast R D n q := by
    apply Sigma.hom_ext
    intro x
    rw [wbarVerticalHomologyFaceLast_ι,
      wbarVerticalHomologyTargetFaceLast_ι,
      wbarFaceLastComponent_homology]
  simpa [wbarVerticalHomologyTargetFaceLast] using hNat.trans (congrArg
    (fun k => (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left) R q).hom ≫ k)
    hFace)
-- Explicit diagram parameters keep elaboration of the dependent coproduct map bounded.
/-- The vertical homology coproduct isomorphism commutes with every interior
outer face. -/
theorem wbarVerticalHomologyIso_faceInner
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0)
    (hiLast : i ≠ Fin.last (n + 1)) [NeZero (n + 1)] :
    SSet.homologyMap
        (StrictOrdinaryWeightedBar.wbarFaceInner
          (CategoryBar.replUnit J) D n i hi0 hiLast) R q ≫
        (wbarVerticalHomologyIso R D n q).hom =
      (wbarVerticalHomologyIso R D (n + 1) q).hom ≫
        StrictOrdinaryWeightedBar.wbarFaceInner
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n i hi0 hiLast := by
  change SSet.homologyMap
      (Sigma.map'
        (StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit J) n i hiLast)
        (fun x => StrictOrdinaryWeightedBar.wFaceInnerComponent
          D i hi0 x.1)) R q ≫
      (homologySigmaIso
        (fun x : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => D.obj x.1.left) R q).hom =
    (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left) R q).hom ≫
      StrictOrdinaryWeightedBar.wbarFaceInner
        (CategoryBar.replUnit J)
        (D ⋙ SSet.homologyFunctor R q) n i hi0 hiLast
  have hNat := homologySigmaIso_naturality
    (F := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left)
    (G := fun x : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n => D.obj x.1.left)
    (StrictOrdinaryWeightedBar.wFaceInnerIdx
      (CategoryBar.replUnit J) n i hiLast)
    (fun x => StrictOrdinaryWeightedBar.wFaceInnerComponent
      D i hi0 x.1) R q
  change _ = _ ≫
    wbarVerticalHomologyFaceInner R D n q i hi0 hiLast at hNat
  have hFace :
      wbarVerticalHomologyFaceInner R D n q i hi0 hiLast =
      wbarVerticalHomologyTargetFaceInner R D n q i hi0 hiLast := by
    apply Sigma.hom_ext
    intro x
    rw [wbarVerticalHomologyFaceInner_ι,
      wbarVerticalHomologyTargetFaceInner_ι,
      wbarFaceInnerComponent_homology]
  simpa [wbarVerticalHomologyTargetFaceInner] using hNat.trans (congrArg
    (fun k => (homologySigmaIso
      (fun x : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => D.obj x.1.left) R q).hom ≫ k)
    hFace)

/-- The weighted-bar vertical-homology coproduct isomorphisms commute with
every outer face. -/
theorem wbarVerticalHomologyIso_face
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) (i : Fin (n + 2)) :
    SSet.homologyMap
        (StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit J) D n i) R q ≫
        (wbarVerticalHomologyIso R D n q).hom =
      (wbarVerticalHomologyIso R D (n + 1) q).hom ≫
        StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n i := by
  by_cases h0 : i = 0
  · subst i
    rw [StrictOrdinaryWeightedBar.wbarδ_zero,
      StrictOrdinaryWeightedBar.wbarδ_zero]
    exact wbarVerticalHomologyIso_faceZero R D n q
  by_cases hlast : i = Fin.last (n + 1)
  · subst i
    rw [StrictOrdinaryWeightedBar.wbarδ_last,
      StrictOrdinaryWeightedBar.wbarδ_last]
    exact wbarVerticalHomologyIso_faceLast R D n q
  · let _ : NeZero (n + 1) := ⟨by omega⟩
    rw [StrictOrdinaryWeightedBar.wbarδ_inner
          (CategoryBar.replUnit J) D n i h0 hlast,
      StrictOrdinaryWeightedBar.wbarδ_inner
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n i h0 hlast]
    exact wbarVerticalHomologyIso_faceInner R D n q i h0 hlast

end SSet

end

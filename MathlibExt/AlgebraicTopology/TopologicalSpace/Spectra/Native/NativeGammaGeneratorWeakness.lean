/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalSphereCoefficientComparison
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Original native integer homotopy representatives

The original free/evaluation Quillen pair and the original sphere coefficient
isomorphism realize each orthogonal integer homotopy class by an actual map
from the same free representation sphere. The actual varying-degree diagram
and its original quotient legs retain every index and degree.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

/-- The complete original n-step map in the varying-degree integer diagram. -/
def integerStageAdvance (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ) :
    ((integerDiagonalFunctor q).obj X).obj t ⟶
      ((integerDiagonalFunctor q).obj X).obj (t + n) :=
  ((integerDiagonalFunctor q).obj X).map (homOfLE (Nat.le_add_right t n))

/-- Every original n-step action preserves its actual integer quotient leg. -/
theorem integerStageAdvance_leg (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ) :
    integerStageAdvance q X t n ≫ integerPiLeg q X (t + n) = integerPiLeg q X t := by
  let D := (integerDiagonalFunctor q).obj X
  let L := GrpCat.FilteredColimits.colimitCocone D
  let a := homOfLE (Nat.le_add_right t n)
  have h := L.ι.naturality a
  change D.map a ≫ L.ι.app (t + n) = L.ι.app t ≫ 𝟙 L.pt at h
  change D.map a ≫ L.ι.app (t + n) = L.ι.app t
  exact h.trans (Category.comp_id (L.ι.app t))

/-- The original stage representative denotes the same element after advancing. -/
theorem integerStageAdvance_leg_apply (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v})
    (t n : ℕ) (x : ((integerDiagonalFunctor q).obj X).obj t) :
    (integerPiLeg q X (t + n)).hom ((integerStageAdvance q X t n).hom x) =
      (integerPiLeg q X t).hom x :=
  ConcreteCategory.congr_hom (integerStageAdvance_leg q X t n) x

/-- Every original target arrow preserves the full n-step diagram map. -/
theorem integerStageAdvance_naturality (q : ℤ) {X Y : Actual.OrthogonalCarrier.{u, v}}
    (g : X ⟶ Y) (t n : ℕ) :
    integerStageAdvance q X t n ≫ ((integerDiagonalFunctor q).map g).app (t + n) =
      ((integerDiagonalFunctor q).map g).app t ≫ integerStageAdvance q Y t n :=
  ((integerDiagonalFunctor q).map g).naturality (homOfLE (Nat.le_add_right t n))

/-- The actual degree and actual level retain the same original integer. -/
theorem integerStageAdvance_degree (q : ℤ) (t n : ℕ) :
    ((integerTailPositiveIndex q + (t + n) + 1 : ℕ) : ℤ) -
      ((integerTailLevel q + (t + n) : ℕ) : ℤ) = q :=
  integerPi_stage_degree q (t + n)

section NativeRepresentatives

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- Both original sphere comparisons identify the same representation sphere. -/
def nativeSphereSourceIso (d : ℕ) :
    PointedCGWH.SphereHom.sphere.{u, v} d ≅ PointedCGWH.orthogonalSphere.{u, v} d :=
  PointedCGWH.SphereHom.sphereCanonicalIso d ≪≫
    originalSymmetricOrthogonalCoefficientIso.{u, v}
      (HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.finiteIndex d)

/-- Every level class keeps both actual free/evaluation localized Hom functions. -/
def nativeSpherePiHomEquiv (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    (X : Actual.OrthogonalCarrier.{u, v}) :
    PointedCGWH.piN d (X.toEnrichedFunctor.obj a) ≃
      ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).obj
          (Free.object a (PointedCGWH.orthogonalSphere.{u, v} d)) ⟶
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).obj X) :=
  (FreeSphereHom.freeSpherePiHomEquiv a d X).trans
    (((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).mapIso
      ((Free.functor a).mapIso (nativeSphereSourceIso d))).homCongr (Iso.refl _))

/-- An actual free map represents every original scalar-sphere homotopy class. -/
theorem actualFreeSphereRepresentative {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
    (a : I) (d : ℕ) (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (x : PointedCGWH.piN d (X.toEnrichedFunctor.obj a)) :
    ∃ f : Free.object a (PointedCGWH.SphereHom.sphere d) ⟶ X,
      FreeSphereHom.freeSpherePiHomEquiv a d X x =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} d) :=
    FreeSphereHom.sphere_isCofibrant d
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAtEvaluation_isQuillenAdjunction a
  let _ : IsCofibrant (Free.object a (PointedCGWH.SphereHom.sphere d)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Free.adjunction a) inferInstance
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (Free.object a (PointedCGWH.SphereHom.sphere d)) X
    (FreeSphereHom.freeSpherePiHomEquiv a d X x)
  exact ⟨f, hf.symm⟩

/-- Every actual cube class retains its original free representation-sphere source. -/
theorem actualNativeSphereRepresentative (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    (X : Actual.OrthogonalCarrier.{u, v})
    (x : PointedCGWH.piN d (X.toEnrichedFunctor.obj a)) :
    ∃ f : Free.object a (PointedCGWH.orthogonalSphere.{u, v} d) ⟶ X,
      nativeSpherePiHomEquiv a d X x =
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f := by
  obtain ⟨f, hf⟩ := actualFreeSphereRepresentative a d X x
  let e := (Free.functor a).mapIso (nativeSphereSourceIso.{u, v} d)
  refine ⟨e.inv ≫ f, ?_⟩
  change ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).mapIso e).inv ≫
      FreeSphereHom.freeSpherePiHomEquiv a d X x ≫ 𝟙 _ = _
  rw [hf, Category.comp_id, Functor.map_comp]
  rfl

/-- Every target map preserves the complete original free/sphere comparison. -/
theorem nativeSpherePiHomEquiv_naturality (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (g : X ⟶ Y)
    (x : PointedCGWH.piN d (X.toEnrichedFunctor.obj a)) :
    nativeSpherePiHomEquiv a d Y (PointedCGWH.piNMap d (component g a) x) =
      nativeSpherePiHomEquiv a d X x ≫
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g := by
  simp only [nativeSpherePiHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  have h := FreeSphereHom.freeSpherePiHomEquiv_naturality a d g x
  let pre := ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).mapIso
    ((Free.functor a).mapIso (nativeSphereSourceIso.{u, v} d))).inv
  exact (congrArg (fun z => pre ≫ z) h).trans
    (Category.assoc pre (FreeSphereHom.freeSpherePiHomEquiv a d X x)
      ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g)).symm

/-- Every integer class has a genuine map at its original varying-degree stage. -/
theorem actualIntegerNativeSphereRepresentative (q : ℤ)
    (X : Actual.OrthogonalCarrier.{u, v}) (α : (integerPiFunctor q).obj X) :
    ∃ (t : ℕ) (x : PointedCGWH.piN (integerTailPositiveIndex q + t + 1)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))))
      (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X),
      nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (integerTailPositiveIndex q + t + 1) X x =
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f ∧
      (integerPiLeg q X t).hom x = α := by
  obtain ⟨⟨t, x⟩, hx⟩ := Quot.exists_rep α
  obtain ⟨f, hf⟩ := actualNativeSphereRepresentative
    (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
    (integerTailPositiveIndex q + t + 1) X x
  exact ⟨t, x, f, hf, hx⟩

/-- The original null map factors through the actual native zero diagram. -/
def nativeNullMap (A X : Actual.OrthogonalCarrier.{u, v}) : A ⟶ X :=
  Diagrams.toZero A ≫ Diagrams.zeroTo X

/-- The complete positive-degree correspondence preserves the same original null map. -/
theorem nativeSpherePiHomEquiv_one (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    (X : Actual.OrthogonalCarrier.{u, v}) :
    nativeSpherePiHomEquiv a (d + 1) X
        (1 : PointedCGWH.piN (d + 1) (X.toEnrichedFunctor.obj a)) =
      (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (nativeNullMap (Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1))) X) := by
  let Z : Actual.OrthogonalCarrier.{u, v} := Diagrams.zeroDiagram
  let g : Z ⟶ X := Diagrams.zeroTo X
  obtain ⟨f, hf⟩ := actualNativeSphereRepresentative a (d + 1) Z 1
  have hZero : f = Diagrams.toZero
      (Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1))) :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  have hPoint : PointedCGWH.piNMap (d + 1) (component g a) 1 = 1 := by
    have h := (PointedCGWH.piNPositiveMap d (component g a)).hom.map_one
    exact (PointedCGWH.piNPositiveMap_apply d (component g a) 1).symm.trans h
  have hNat := nativeSpherePiHomEquiv_naturality a (d + 1) g 1
  have hNull := hf.trans (congrArg
    (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map hZero)
  calc
    _ = nativeSpherePiHomEquiv a (d + 1) X
        (PointedCGWH.piNMap (d + 1) (component g a) 1) :=
      congrArg (nativeSpherePiHomEquiv a (d + 1) X) hPoint.symm
    _ = nativeSpherePiHomEquiv a (d + 1) Z 1 ≫
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g := hNat
    _ = (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (Diagrams.toZero (Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1)))) ≫
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g :=
      congrArg (fun z => z ≫ (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g) hNull
    _ = _ := (Functor.map_comp (toHomotopyCategory Actual.OrthogonalCarrier.{u, v})
      (Diagrams.toZero (Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1)))) g).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse function detects the actual null map in the original native category. -/
theorem nativeSpherePiHomEquiv_null_iff (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    (X : Actual.OrthogonalCarrier.{u, v})
    (f : Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1)) ⟶ X) :
    (nativeSpherePiHomEquiv a (d + 1) X).symm
        ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f) = 1 ↔
      (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f =
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
          (nativeNullMap (Free.object a (PointedCGWH.orthogonalSphere.{u, v} (d + 1))) X) := by
  let e := nativeSpherePiHomEquiv a (d + 1) X
  have hNull := nativeSpherePiHomEquiv_one a d X
  constructor
  · intro h
    have he : (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f = e 1 :=
      (Equiv.symm_apply_eq e).mp h
    exact he.trans hNull
  · intro h
    apply (Equiv.symm_apply_eq e).mpr
    exact h.trans hNull.symm

end NativeRepresentatives

/-- The actual quotient leg kills a class exactly at an original later stage. -/
theorem canonicalGroupLeg_one_iff_later (D : ℕ ⥤ GrpCat.{v}) (t : ℕ) (x : D.obj t) :
    ((GrpCat.FilteredColimits.colimitCocone D).ι.app t).hom x = 1 ↔
      ∃ (m : ℕ) (f : t ⟶ m), (D.map f).hom x = 1 := by
  let _ : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, 0, 0} (forget GrpCat.{v})
  let hE := isColimitOfPreserves (forget GrpCat.{v})
    (GrpCat.FilteredColimits.colimitCoconeIsColimit D)
  have hEq := Types.FilteredColimit.isColimit_eq_iff' hE x (1 : D.obj t)
  constructor
  · intro hx
    have hSame : ((GrpCat.FilteredColimits.colimitCocone D).ι.app t).hom x =
        ((GrpCat.FilteredColimits.colimitCocone D).ι.app t).hom 1 :=
      hx.trans (((GrpCat.FilteredColimits.colimitCocone D).ι.app t).hom.map_one).symm
    obtain ⟨m, f, h⟩ := hEq.mp hSame
    exact ⟨m, f, h.trans (D.map f).hom.map_one⟩
  · rintro ⟨m, f, hf⟩
    have hSame := hEq.mpr ⟨m, f, hf.trans ((D.map f).hom.map_one).symm⟩
    exact hSame.trans ((GrpCat.FilteredColimits.colimitCocone D).ι.app t).hom.map_one

/-- The same stage representative becomes null after an actual n-step advance. -/
theorem integerLeg_one_iff_advance (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v})
    (t : ℕ) (x : ((integerDiagonalFunctor q).obj X).obj t) :
    (integerPiLeg q X t).hom x = 1 ↔
      ∃ n : ℕ, (integerStageAdvance q X t n).hom x = 1 := by
  let D := (integerDiagonalFunctor q).obj X
  constructor
  · intro hx
    obtain ⟨m, f, hf⟩ := (canonicalGroupLeg_one_iff_later D t x).mp hx
    let g : m ⟶ t + m := homOfLE (Nat.le_add_left m t)
    have hArrow : f ≫ g = homOfLE (Nat.le_add_right t m) := Subsingleton.elim _ _
    have hMap := ConcreteCategory.congr_hom (D.map_comp f g) x
    have hOne : ((D.map g).hom) ((D.map f).hom x) = 1 :=
      (congrArg (D.map g).hom hf).trans (D.map g).hom.map_one
    refine ⟨m, ?_⟩
    exact (congrArg (fun a => (D.map a).hom x) hArrow).symm.trans (hMap.trans hOne)
  · rintro ⟨n, hn⟩
    exact (canonicalGroupLeg_one_iff_later D t x).mpr
      ⟨t + n, homOfLE (Nat.le_add_right t n), hn⟩

section KernelRepresentatives

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 1024 in
/-- Every kernel class has an actual later free map with the same literal null target composite. -/
theorem integerKernelRepresentative (q : ℤ) {X Y : Actual.OrthogonalCarrier.{u, v}}
    (g : X ⟶ Y) (α : (integerPiFunctor q).obj X)
    (hα : ((integerPiFunctor q).map g).hom α = 1) :
    ∃ (t : ℕ) (x : PointedCGWH.piN (integerTailPositiveIndex q + t + 1)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))))
      (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X),
      nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (integerTailPositiveIndex q + t + 1) X x =
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f ∧
      (integerPiLeg q X t).hom x = α ∧
      (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (f ≫ g) =
        (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeNullMap _ Y) := by
  obtain ⟨t, x, _, _, hx⟩ := actualIntegerNativeSphereRepresentative q X α
  let DY := (integerDiagonalFunctor q).obj Y
  let u := (integerDiagonalFunctor q).map g
  let a : DY.obj t := (u.app t).hom x
  have hNat := ConcreteCategory.congr_hom (integerPiLeg_naturality_component q g t) x
  have hStage := congrArg (fun f => f.hom x) (integerDiagonalFunctor_map_stage q g t)
  have hLeg : (integerPiLeg q Y t).hom a = 1 :=
    (congrArg (integerPiLeg q Y t).hom hStage).trans
      (hNat.symm.trans ((congrArg ((integerPiFunctor q).map g).hom hx).trans hα))
  obtain ⟨s, hs⟩ := (integerLeg_one_iff_advance q Y t a).mp hLeg
  let k := integerTailPositiveIndex q + (t + s)
  let r := integerTailLevel q + (t + s)
  let xp : PointedCGWH.piN (k + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)) :=
    (integerStageAdvance q X t s).hom x
  have hAdvance := ConcreteCategory.congr_hom (integerStageAdvance_naturality q g t s) x
  have hImage : (u.app (t + s)).hom xp = 1 := hAdvance.trans hs
  have hEval := congrArg (fun f => f.hom xp) (integerDiagonalFunctor_map_stage q g (t + s))
  have hCube : PointedCGWH.piNMap (k + 1)
      (component g (OrthogonalOperatorIndex.ofIndex r)) xp = 1 :=
    (PointedCGWH.piNPositiveMap_apply k (component g (OrthogonalOperatorIndex.ofIndex r)) xp).symm.trans
      (hEval.symm.trans hImage)
  obtain ⟨f, hf⟩ := actualNativeSphereRepresentative
    (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + s)))
    (integerTailPositiveIndex q + (t + s) + 1) X xp
  have hSource : (integerPiLeg q X (t + s)).hom xp = α :=
    (integerStageAdvance_leg_apply q X t s x).trans hx
  have hPost := nativeSpherePiHomEquiv_naturality
    (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + s)))
    (integerTailPositiveIndex q + (t + s) + 1) g xp
  rw [hCube, hf] at hPost
  have hComp : (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (f ≫ g) =
      (toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeNullMap _ Y) :=
    ((toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map_comp f g).trans
      (hPost.symm.trans (nativeSpherePiHomEquiv_one
        (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + s)))
        (integerTailPositiveIndex q + (t + s)) Y))
  refine Exists.intro (t + s) ?_
  refine Exists.intro xp ?_
  refine Exists.intro f ?_
  constructor
  · exact hf
  · constructor
    · exact hSource
    · exact hComp

end KernelRepresentatives
end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness

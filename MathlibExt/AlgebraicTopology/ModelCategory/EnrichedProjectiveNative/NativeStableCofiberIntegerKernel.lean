/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.Algebra.Category.Grp.FilteredKernelRepresentatives

/-!
# Cofiber kernels and suspension in integer stable homotopy

A class killed by the cofibrant cofiber inclusion admits a sphere representative at a
later level and a suspended preimage. These constructions are transported by the
cofibrant-replacement counit to the integer stable homotopy groups of the given enriched
spectrum, in every integer degree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  HomotopicalAlgebra.EnrichedProjective.Native.Replacement.isCofibrant_cofibrantReplacement

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I}

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev C := (Carrier.{u, v} (I := I))
private abbrev Index := I
private abbrev H := toHomotopyCategory (Carrier.{u, v} (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev cone := OriginalICone.cone (B := B) (I := I)
private abbrev ι := OriginalICone.inclusion (B := B) (I := I)
private abbrev c := OriginalISuspension.cocone (B := B) (I := I)
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := I)
private abbrev CQ := CofiberNullity.cofiberQ (B := B) (I := I)

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerKernel

open HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom

/-- Every original integer kernel class has a later actual native stage with literal null image. -/
theorem inclusion_kernel_level_representative (q : ℤ) (F : Arrow (C.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj ((Q (I := I)).obj F.right))
    (hx : ((integerPiFunctor j q).map (inclusion F)).hom x = 1) :
    ∃ (n : ℕ) (z : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
      (((Q (I := I)).obj F.right).toEnrichedFunctor.obj
        (sourceIndex j (integerTailLevel q + n)))),
      (integerPiLeg j q ((Q (I := I)).obj F.right) n).hom z = x ∧
      PointedCGWH.piNMap (integerTailPositiveIndex q + n + 1)
        (component (inclusion F)
          (sourceIndex j (integerTailLevel q + n))) z =
        PointedCGWH.SphereHom.nullCube (integerTailPositiveIndex q + n + 1)
          ((CQ.obj F).toEnrichedFunctor.obj
            (sourceIndex j (integerTailLevel q + n))) := by
  let D := (integerDiagonalFunctor j q).obj ((Q (I := I)).obj F.right)
  let E := (integerDiagonalFunctor j q).obj (CQ.obj F)
  let alpha : D ⟶ E := (integerDiagonalFunctor j q).map (inclusion F)
  have hx' : (GrpCat.FilteredColimits.colimitMap alpha).hom x = 1 := hx
  obtain ⟨n, m, h, z, hz, hn⟩ :=
    GrpCat.FilteredColimits.colimitMap_kernel_representative alpha x hx'
  let b := D.map (homOfLE h) z
  refine ⟨m, b, ?_, ?_⟩
  · change (GrpCat.FilteredColimits.colimitCocone D).ι.app m (D.map (homOfLE h) z) = x
    exact (ConcreteCategory.congr_hom
      ((GrpCat.FilteredColimits.colimitCocone D).ι.naturality (homOfLE h)) z).trans hz
  · have hb : alpha.app m b = 1 :=
      (ConcreteCategory.congr_hom (alpha.naturality (homOfLE h)) z).trans hn
    have hm := integerDiagonalFunctor_map_stage j q (inclusion F) m
    have hb' : PointedCGWH.piNMap (integerTailPositiveIndex q + m + 1)
        (component (inclusion F)
          (sourceIndex j (integerTailLevel q + m))) b =
      (1 : (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + m)).obj
        ((CQ.obj F).toEnrichedFunctor.obj
          (sourceIndex j (integerTailLevel q + m)))) := by
      exact (PointedCGWH.piNPositiveMap_apply (integerTailPositiveIndex q + m)
        (component (inclusion F)
          (sourceIndex j
            (integerTailLevel q + m))) b).symm.trans
          ((ConcreteCategory.congr_hom hm b).symm.trans hb)
    exact hb'.trans (PointedCGWH.SphereHom.nullCube_eq_one
      (integerTailPositiveIndex q + m)
      ((CQ.obj F).toEnrichedFunctor.obj
        (sourceIndex j (integerTailLevel q + m)))).symm

/-- The original Q-counit inverse retains the input class and all later native null-map data. -/
theorem original_inclusion_kernel_level_representative (q : ℤ) (F : Arrow (C.{u, v} (I := I)))
    (x : (integerPiHoFunctor j q).obj ((H (I := I)).obj F.right))
    (hx : (inclusionInteger (j := j) q F).hom x = 1) :
    ∃ (n : ℕ) (z : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
      (((Q (I := I)).obj F.right).toEnrichedFunctor.obj
        (sourceIndex j (integerTailLevel q + n)))),
      (integerPiLeg j q ((Q (I := I)).obj F.right) n).hom z =
        ((integerPiHoFunctor j q).map (qCounitHoIso F.right).inv).hom x ∧
      PointedCGWH.piNMap (integerTailPositiveIndex q + n + 1)
        (component (inclusion F)
          (sourceIndex j (integerTailLevel q + n))) z =
        PointedCGWH.SphereHom.nullCube (integerTailPositiveIndex q + n + 1)
          ((CQ.obj F).toEnrichedFunctor.obj
            (sourceIndex j (integerTailLevel q + n))) := by
  apply inclusion_kernel_level_representative (j := j) q F
    (((integerPiHoFunctor j q).map (qCounitHoIso F.right).inv).hom x)
  exact (ConcreteCategory.congr_hom (inclusionInteger_formula (j := j) q F) x).symm.trans hx

/-- Each source sphere is the original free native spectrum at the same actual dimension. -/
def sphereSource (m d : ℕ) : (C.{u, v} (I := I)) :=
  (EnrichedFunctorCat.Free.functor
    (sourceIndex j m)).obj
      (PointedCGWH.SphereHom.sphere d)

/-- The original free/evaluation Quillen adjunction proves source cofibrancy. -/
theorem sphereSource_isCofibrant (m d : ℕ) : IsCofibrant (sphereSource.{u, v} (j := j) m d) := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} d) := sphere_isCofibrant d
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
    (sourceIndex j m)).IsQuillenAdjunction :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAtEvaluation_isQuillenAdjunction _
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := EnrichedFunctorCat.Free.adjunction _) inferInstance

/-- The actual complete Hom function of a given native evaluated cube class. -/
def levelSphereClass (m d : ℕ) (Y : (C.{u, v} (I := I)))
    (z : PointedCGWH.piN d (Y.toEnrichedFunctor.obj
      (sourceIndex j m))) :
    (H (I := I)).obj (sphereSource (j := j) m d) ⟶ (H (I := I)).obj Y :=
  freeSpherePiHomEquiv (B := B)
    (sourceIndex j m) d Y z

/-- Every literal level null image is the same whole original coefficient null Hom map. -/
theorem levelSphereClass_null_composite (F : Arrow (C.{u, v} (I := I))) (m d : ℕ)
    (z : PointedCGWH.piN d (((Q (I := I)).obj F.right).toEnrichedFunctor.obj
      (sourceIndex j m)))
    (hz : PointedCGWH.piNMap d
      (component (inclusion F) (sourceIndex j m)) z =
      PointedCGWH.SphereHom.nullCube d ((CQ.obj F).toEnrichedFunctor.obj
        (sourceIndex j m))) :
    levelSphereClass (j := j) m d ((Q (I := I)).obj F.right) z ≫ (H (I := I)).map (inclusion F) =
      OrdinaryHoCofiberKernel.nullHom (sphereSource (j := j) m d) (CQ.obj F) := by
  have h := freeSpherePiHomEquiv_naturality (B := B)
    (sourceIndex j m) d (inclusion F) z
  exact h.symm.trans ((congrArg
    (freeSpherePiHomEquiv (B := B)
      (sourceIndex j m) d (CQ.obj F)) hz).trans
        (freeSpherePiHomEquiv_null (B := B)
          (sourceIndex j m) d (CQ.obj F)))

/-- The actual fundamental lemma realizes that same original null coefficient by a strict map. -/
theorem levelSphereClass_null_representative (F : Arrow (C.{u, v} (I := I))) (m d : ℕ)
    (z : PointedCGWH.piN d (((Q (I := I)).obj F.right).toEnrichedFunctor.obj
      (sourceIndex j m)))
    (hz : PointedCGWH.piNMap d
      (component (inclusion F) (sourceIndex j m)) z =
      PointedCGWH.SphereHom.nullCube d ((CQ.obj F).toEnrichedFunctor.obj
        (sourceIndex j m))) :
    ∃ g : sphereSource (j := j) m d ⟶ (Q (I := I)).obj F.right,
      (H (I := I)).map g = levelSphereClass (j := j) m d ((Q (I := I)).obj F.right) z ∧
      (H (I := I)).map (g ≫ inclusion F) = OrdinaryHoCofiberKernel.nullHom (sphereSource (j := j)
        m d) (CQ.obj F) := by
  let _ : IsCofibrant (sphereSource.{u, v} (j := j) m d) := sphereSource_isCofibrant (j := j) m d
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization (H (I := I)) (sphereSource (j := j) m d) ((Q
    (I := I)).obj F.right)
    (levelSphereClass (j := j) m d ((Q (I := I)).obj F.right) z)
  refine ⟨g, hg, ?_⟩
  rw [(H (I := I)).map_comp, hg]
  exact levelSphereClass_null_composite (j := j) F m d z hz

/-- The genuine original suspended coefficient lift keeps exactly the same full Q-arrow. -/
theorem sphereSuspendedLift_of_null (F : Arrow (C.{u, v} (I := I))) (m d : ℕ)
    (g : sphereSource (j := j) m d ⟶ (Q (I := I)).obj F.right)
    (hg : (H (I := I)).map (g ≫ inclusion F) =
      OrdinaryHoCofiberKernel.nullHom (sphereSource (j := j) m d) (CQ.obj F)) :
    ∃ k : (H (I := I)).obj ((S (I := I)).obj (sphereSource (j := j) m d)) ⟶ (H (I := I)).obj ((S
      (I := I)).obj ((Q (I := I)).obj F.left)),
      k ≫ (H (I := I)).map ((S (I := I)).map ((Q (I := I)).map F.hom)) = (H (I := I)).map ((S (I
        := I)).map g) := by
  let _ : IsCofibrant (sphereSource.{u, v} (j := j) m d) := sphereSource_isCofibrant (j := j) m d
  have hNull : (H (I := I)).map (g ≫ inclusion F) = (H (I := I)).map
      (OrdinaryHoChosenPuppe.nullMap Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (sphereSource (j := j) m d) (CQ.obj F)) := by
    rw [OrdinaryHoChosenPuppe.actualNullMap_eq_chosen]
    exact hg
  exact OriginalFiberComparison.originalQCoefficientLift_of_null (B := B) F
    (sphereSource (j := j) m d) g hNull

/-- The universal native cube class is the actual inverse Hom image of the source identity. -/
def universalSphereClass (m d : ℕ) :
    PointedCGWH.piN d ((sphereSource.{u, v} (j := j) m d).toEnrichedFunctor.obj
      (sourceIndex j m)) :=
  (freeSpherePiHomEquiv (B := B)
    (sourceIndex j m) d (sphereSource (j := j) m d)).symm
      (𝟙 ((H (I := I)).obj (sphereSource (j := j) m d)))

/-- Every strict representative sends the actual universal source class to its same input cube. -/
theorem universalSphereClass_map (m d : ℕ) {Y : (C.{u, v} (I := I))}
    (g : sphereSource (j := j) m d ⟶ Y)
    (z : PointedCGWH.piN d (Y.toEnrichedFunctor.obj
      (sourceIndex j m)))
    (hg : (H (I := I)).map g = levelSphereClass (j := j) m d Y z) :
    PointedCGWH.piNMap d
      (component g (sourceIndex j m))
      (universalSphereClass (j := j) m d) = z := by
  apply (freeSpherePiHomEquiv (B := B)
    (sourceIndex j m) d Y).injective
  have h := freeSpherePiHomEquiv_naturality (B := B)
    (sourceIndex j m) d g (universalSphereClass (j := j) m d)
  have hId := (freeSpherePiHomEquiv (B := B)
    (sourceIndex j m)
    d (sphereSource (j := j) m d)).apply_symm_apply
      (𝟙 ((H (I := I)).obj (sphereSource (j := j) m d)))
  exact h.trans ((congrArg (fun t => t ≫ (H (I := I)).map g) hId).trans
    ((Category.id_comp ((H (I := I)).map g)).trans hg))

/-- The actual original integer source class uses the same positive-stage quotient leg. -/
def universalIntegerClass (q : ℤ) (n : ℕ) :
    (integerPiFunctor j q).obj
      (sphereSource (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1)) :=
  (integerPiLeg j q
    (sphereSource (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1)) n).hom
      (universalSphereClass (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1))

/-- The full original quotient map of the strict coefficient retains the exact input class. -/
theorem universalIntegerClass_map (q : ℤ) (n : ℕ) {Y : (C.{u, v} (I := I))}
    (g : sphereSource (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) ⟶ Y)
    (z : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
      (Y.toEnrichedFunctor.obj
        (sourceIndex j (integerTailLevel q + n))))
    (hg : (H (I := I)).map g = levelSphereClass (j := j) (integerTailLevel q + n)
      (integerTailPositiveIndex q + n + 1) Y z) :
    ((integerPiFunctor j q).map g).hom (universalIntegerClass (j := j) q n) =
      (integerPiLeg j q Y n).hom z := by
  have h := ConcreteCategory.congr_hom (integerPiLeg_naturality_component j q g n)
    (universalSphereClass (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1))
  have hcube := (PointedCGWH.piNPositiveMap_apply (integerTailPositiveIndex q + n)
    (component g (sourceIndex j (integerTailLevel q + n)))
    (universalSphereClass (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n +
      1))).trans
      (universalSphereClass_map (j := j) (integerTailLevel q + n)
        (integerTailPositiveIndex q + n + 1) g z hg)
  exact h.trans (congrArg (integerPiLeg j q Y n).hom hcube)

/-- Every integer kernel class has its actual universal coefficient and suspended lift. -/
theorem original_inclusion_kernel_suspended_lift (q : ℤ) (F : Arrow (C.{u, v} (I := I)))
    (x : (integerPiHoFunctor j q).obj ((H (I := I)).obj F.right))
    (hx : (inclusionInteger (j := j) q F).hom x = 1) :
    ∃ (n : ℕ)
      (g : sphereSource (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) ⟶
        (Q (I := I)).obj F.right)
      (k : (H (I := I)).obj ((S (I := I)).obj (sphereSource (j := j) (integerTailLevel q + n)
        (integerTailPositiveIndex q + n + 1))) ⟶ (H (I := I)).obj ((S (I := I)).obj ((Q (I :=
          I)).obj F.left))),
      ((integerPiFunctor j q).map g).hom (universalIntegerClass (j := j) q n) =
        ((integerPiHoFunctor j q).map (qCounitHoIso F.right).inv).hom x ∧
      k ≫ (H (I := I)).map ((S (I := I)).map ((Q (I := I)).map F.hom)) = (H (I := I)).map ((S (I
        := I)).map g) := by
  obtain ⟨n, z, hz, hnull⟩ := original_inclusion_kernel_level_representative (j := j) q F x hx
  obtain ⟨g, hg, hgn⟩ := levelSphereClass_null_representative (j := j) F
    (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) z hnull
  obtain ⟨k, hk⟩ := sphereSuspendedLift_of_null (j := j) F
    (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) g hgn
  exact ⟨n, g, k, (universalIntegerClass_map (j := j) q n g z hg).trans hz, hk⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uD vD uE vE

omit B in
private theorem naturalSuspendedCoefficient {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] (T' : D ⥤ E) (W : D ⥤ GrpCat.{v})
    (P' : E ⥤ GrpCat.{v}) (u' : W ⟶ T' ⋙ P')
    {A X Y : D} (f : X ⟶ Y) (g : A ⟶ Y) (k : T'.obj A ⟶ T'.obj X)
    (hk : k ≫ T'.map f = T'.map g) (a : W.obj A) :
    (P'.map (T'.map f)).hom ((P'.map k).hom ((u'.app A).hom a)) =
      (u'.app Y).hom ((W.map g).hom a) := by
  have h := (P'.map_comp k (T'.map f)).symm.trans (P'.congr_map hk)
  have hn := ConcreteCategory.congr_hom (u'.naturality g) a
  exact (ConcreteCategory.congr_hom h ((u'.app A).hom a)).trans hn.symm

private abbrev cι : CofibrantObject (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I)) :=
  CofibrantObject.ι

/-- The same whole native cofibrant unit is projected to its original Ho integer groups. -/
def cofibrantHoSuspensionIntegerUnit (q : ℤ) :
    cι (I := I) ⋙ integerPiFunctor j q ⟶
      ((cι (I := I) ⋙ (S (I := I))) ⋙ (H (I := I))) ⋙ integerPiHoFunctor j (q + 1) :=
  (cofibrantISuspensionPiNatIso (j := j) q).hom ≫
    (Functor.associator (cι (I := I)) (S (I := I)) (integerPiFunctor j (q + 1))).inv ≫
    (projectedIntegerClassNatIso (j := j) (cι (I := I) ⋙ (S (I := I))) (q + 1)).inv

private theorem cofibrantHoSuspensionIntegerUnit_app (q : ℤ)
    (X : (Carrier.{u, v} (I := I))) [IsCofibrant X] :
    (cofibrantHoSuspensionIntegerUnit (j := j) q).app (CofibrantObject.mk X) =
      (cofibrantISuspensionPiIso (j := j) q X).hom := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The same actual suspended free coefficient maps to the original full I-Q unit class. -/
theorem original_inclusion_kernel_suspended_image (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj F.right) (hx : (inclusionInteger (j := j) q F).hom x = 1) :
    ∃ a : (originalISuspensionQFunctor (I := I) ⋙ integerPiFunctor j (q + 1)).obj F.left,
      @Eq ((originalISuspensionQFunctor (I := I) ⋙ integerPiFunctor j (q + 1)).obj F.right)
        (((originalISuspensionQFunctor (I := I) ⋙ integerPiFunctor j (q + 1)).map F.hom).hom a)
        (((integerISuspensionPiNatIso (j := j) q).hom.app F.right).hom x) := by
  obtain ⟨n, g, k, hg, hk⟩ := original_inclusion_kernel_suspended_lift (j := j) q F x hx
  let A := sphereSource (j := j) (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1)
  let _ : IsCofibrant A := sphereSource_isCofibrant (j := j) _ _
  let eA := cofibrantISuspensionPiIso (j := j) q A
  let eY := cofibrantISuspensionPiIso (j := j) q ((Q (I := I)).obj F.right)
  let a := universalIntegerClass (j := j) q n
  let pk := (integerPiHoFunctor j (q + 1)).map k
  let Xc := CofibrantObject.mk ((Q (I := I)).obj F.left)
  let Yc := CofibrantObject.mk ((Q (I := I)).obj F.right)
  let Ac := CofibrantObject.mk A
  let T' := (cι (I := I) ⋙ (S (I := I))) ⋙ (H (I := I))
  have hImage := naturalSuspendedCoefficient T' (cι (I := I) ⋙ integerPiFunctor j q)
    (integerPiHoFunctor j (q + 1)) (cofibrantHoSuspensionIntegerUnit (j := j) q)
    (X := Xc) (Y := Yc) (A := Ac) (CofibrantObject.homMk ((Q (I := I)).map F.hom))
    (CofibrantObject.homMk g) k hk a
  change ((integerPiHoFunctor j (q + 1)).map
    ((H (I := I)).map ((S (I := I)).map ((Q (I := I)).map F.hom)))).hom
      (pk.hom (((cofibrantHoSuspensionIntegerUnit (j := j) q).app Ac).hom a)) =
    ((cofibrantHoSuspensionIntegerUnit (j := j) q).app Yc).hom
      (((integerPiFunctor j q).map g).hom a) at hImage
  rw [integerPiHoFunctor_map (j := j)] at hImage
  rw [cofibrantHoSuspensionIntegerUnit_app (j := j),
    cofibrantHoSuspensionIntegerUnit_app (j := j)] at hImage
  refine ⟨pk.hom (eA.hom.hom a), ?_⟩
  rw [qCounitHoIso_integer_inverse (j := j)] at hg
  have hResult := hImage.trans (congrArg eY.hom.hom hg)
  have hWord := ConcreteCategory.congr_hom
    (integerISuspensionPiNatIso_hom_word (j := j) q F.right) x
  exact hResult.trans hWord.symm

/-- The full original I-Q inverse restores a preimage of the unchanged input map
at every integer. -/
theorem original_inclusion_kernel_preimage (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj F.right) (hx : (inclusionInteger (j := j) q F).hom x = 1) :
    ∃ y : (integerPiFunctor j q).obj F.left,
      ((integerPiFunctor j q).map F.hom).hom y = x := by
  obtain ⟨a, ha⟩ := original_inclusion_kernel_suspended_image (j := j) q F x hx
  let eX := (integerISuspensionPiNatIso (j := j) q).app F.left
  let eY := (integerISuspensionPiNatIso (j := j) q).app F.right
  refine ⟨eX.inv.hom a, ?_⟩
  apply eY.groupIsoToMulEquiv.injective
  have hn := ConcreteCategory.congr_hom
    ((integerISuspensionPiNatIso (j := j) q).hom.naturality F.hom) (eX.inv.hom a)
  have he := ConcreteCategory.congr_hom eX.inv_hom_id a
  exact hn.trans ((congrArg
    ((originalISuspensionQFunctor (I := I) ⋙ integerPiFunctor j (q + 1)).map F.hom).hom
      he).trans ha)

end HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerKernel

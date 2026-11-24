/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_QMCanonicalPol.lean`,
`Definitions/Def_AlgebraicGeometry_PolarisedAbelianScheme.lean`
and
`Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw

@[expose] public section

noncomputable section

/-!
# Canonical polarization data on a relative group law

A sheaf of modules is locally isomorphic to another on the base scheme when
every point has a Zariski neighbourhood on which their pullbacks are
isomorphic.  For a relative group law, the negation and addition morphisms,
the Mumford bundle built from a sheaf and a chosen dual sheaf, its kernel
conditions, and Rosati compatibility with an action are defined directly
from the group law on points.  Canonical polarization data packages an
invertible sheaf that is symmetric, has kernel contained in the
`2`-torsion, is fppf-locally a tensor product of a kernel-trivial sheaf
with its negation pullback, has positive geometric global-section rank in
every algebraically closed fibre, and is Rosati compatible.
-/

namespace MathlibExt.AlgebraicGeometry.QMCanonicalPol

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

universe u v

/-- The structure sheaf as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Local triviality of rank one, on actual Zariski open subschemes. -/
def IsLineBundle {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ structureModule U)

/-- The structure sheaf is invertible: it is trivial on the whole scheme. -/
theorem isLineBundle_structureModule (X : Scheme.{u}) :
    IsLineBundle (structureModule X) := fun _ ↦
  ⟨⊤, trivial,
    ⟨((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

/-- The tensor product of sheaves of modules: the sheafification of the
tensor product of the underlying presheaves of modules. -/
def moduleTensor (X : Scheme.{u}) (L M : X.Modules) : X.Modules :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (U.obj L) (U.obj M))

/-- Two sheaves of modules are locally isomorphic when every point has a
Zariski neighbourhood on which their pullbacks are isomorphic. -/
def LocIsoOnBase {X : Scheme.{u}} (M M' : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      (Scheme.Modules.pullback U.ι).obj M')

/-- Every sheaf of modules is locally isomorphic to itself. -/
theorem locIsoOnBase_refl {X : Scheme.{u}} (M : X.Modules) :
    LocIsoOnBase M M :=
  fun _ ↦ ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

/-- Local isomorphism of sheaves of modules is symmetric. -/
theorem locIsoOnBase_symm {X : Scheme.{u}} {M M' : X.Modules}
    (h : LocIsoOnBase M M') : LocIsoOnBase M' M :=
  fun x ↦ (h x).imp fun _ ⟨hx, ⟨e⟩⟩ ↦ ⟨hx, ⟨e.symm⟩⟩

variable {S : Type u} [CommRing S] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of S)} (G : RelativeGroupLaw S f)

/-- The negation morphism of a relative group law. -/
def negMor : A ⟶ A := (G.inv f (𝟙 (Over.mk f))).left

/-- Negation is a morphism over the base. -/
theorem negMor_over : negMor G ≫ f = f := Over.w _

/-- The addition morphism of a relative group law. -/
def addMor : pullback f f ⟶ A :=
  (G.mul (pullback.fst f f ≫ f)
    (Over.homMk (pullback.fst f f) rfl)
    (Over.homMk (pullback.snd f f) pullback.condition.symm)).left

/-- Addition is a morphism over the first projection. -/
theorem addMor_over : addMor G ≫ f = pullback.fst f f ≫ f := Over.w _

/-- The Mumford bundle of a sheaf `L` with chosen dual sheaf `Ldual`. -/
def mumfordBundle (L Ldual : A.Modules) : (pullback f f).Modules :=
  moduleTensor _
    ((Scheme.Modules.pullback (addMor G)).obj L)
    (moduleTensor _
      ((Scheme.Modules.pullback (pullback.fst f f)).obj Ldual)
      ((Scheme.Modules.pullback (pullback.snd f f)).obj Ldual))

/-- Slicing a point of the group law into the Mumford bundle. -/
def sliceAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x : Over.mk t ⟶ Over.mk f) : pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ x.left)
    (by
      have hx : x.left ≫ f = t := Over.w x
      calc pullback.fst f t ≫ f = pullback.snd f t ≫ t :=
            pullback.condition
        _ = pullback.snd f t ≫ x.left ≫ f := by
            rw [hx])

/-- A sheaf is symmetric when its negation pullback is locally isomorphic
to it. -/
def IsSymmetric (L : A.Modules) : Prop :=
  LocIsoOnBase ((Scheme.Modules.pullback (negMor G)).obj L) L

/-- The kernel of the Mumford bundle is trivial. -/
def KernelTrivial (L Ldual : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of S)) (x : Over.mk t ⟶ Over.mk f),
    LocIsoOnBase
        ((Scheme.Modules.pullback (sliceAt x)).obj
          (mumfordBundle G L Ldual))
        (structureModule _) →
      x = G.one t

/-- The kernel of the Mumford bundle consists of `2`-torsion points. -/
def KernelIsTwoTorsion (L Ldual : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of S)) (x : Over.mk t ⟶ Over.mk f),
    LocIsoOnBase
        ((Scheme.Modules.pullback (sliceAt x)).obj
          (mumfordBundle G L Ldual))
        (structureModule _) ↔
      G.mul t x x = G.one t

/-- The first Rosati lift of a point of the action. -/
def rosatiLiftLeft {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (b : I) :
    pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b)
    (by
      have h : act b ≫ f = f := act_over b
      calc pullback.fst f f ≫ f = pullback.snd f f ≫ f :=
            pullback.condition
        _ = pullback.snd f f ≫ act b ≫ f := by
            rw [h])

/-- The second Rosati lift of a point of the action. -/
def rosatiLiftRight {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (star : I → I) (b : I) :
    pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
    (by
      calc pullback.fst f f ≫ act (star b) ≫ f
          = pullback.fst f f ≫ f := by
            rw [act_over]
        _ = pullback.snd f f ≫ f := pullback.condition)

/-- Rosati compatibility of the Mumford bundle with an action and its
involution. -/
def RosatiCompatible (L Ldual : A.Modules) {I : Type v}
    (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase
      ((Scheme.Modules.pullback
          (rosatiLiftLeft act act_over b)).obj
        (mumfordBundle G L Ldual))
      ((Scheme.Modules.pullback
          (rosatiLiftRight act act_over star b)).obj
        (mumfordBundle G L Ldual))

/-- A point of a pulled-back group law, viewed as a point of the
original group law after base change. -/
def baseChangePoint {S' : Type u} [CommRing S'] (ψ : S →+* S')
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : Over.mk t' ⟶
      Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))) :
    Over.mk (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟶ Over.mk f :=
  Over.homMk (P.left ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))
    (by
      have hP : P.left ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom ψ)) = t' :=
        Over.w P
      calc (P.left ≫
            pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) ≫ f
          = P.left ≫ (pullback.snd f
              (Spec.map (CommRingCat.ofHom ψ)) ≫
              Spec.map (CommRingCat.ofHom ψ)) := by
            rw [Category.assoc, pullback.condition]
        _ = t' ≫ Spec.map (CommRingCat.ofHom ψ) := by
            rw [← Category.assoc, hP])

/-- The rank of global sections of `L` in the geometric fibre over an
algebraically closed field. -/
def geomFibreH0Finrank (G : RelativeGroupLaw S f) (L : A.Modules) (k : Type u) [Field k]
    (sk : S →+* k) : ℕ :=
  letI : Algebra k Γ(Limits.pullback f
      (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module k Γ((Scheme.Modules.pullback
      (Limits.pullback.fst f
        (Spec.map (CommRingCat.ofHom sk)))).obj L, ⊤) :=
    Module.compHom _
      (algebraMap k Γ(Limits.pullback f
        (Spec.map (CommRingCat.ofHom sk)), ⊤))
  Module.finrank k Γ((Scheme.Modules.pullback
      (Limits.pullback.fst f
        (Spec.map (CommRingCat.ofHom sk)))).obj L, ⊤)

/-- Canonical polarization data for a sheaf `L` with chosen dual `Ldual`:
`L` is invertible and symmetric, its Mumford kernel is `2`-torsion,
fppf-locally it is a kernel-trivial sheaf tensored with its negation
pullback, its geometric global-section rank is positive, and it is
Rosati compatible with the action. -/
structure CanonicalPolarizationData {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (star : I → I)
    (L Ldual : A.Modules) : Prop where
  /-- The sheaf is invertible. -/
  isLineBundle : IsLineBundle L
  /-- The sheaf is symmetric. -/
  isSymmetric : IsSymmetric G L
  /-- The Mumford kernel is contained in the `2`-torsion. -/
  kernelIsTwoTorsion : KernelIsTwoTorsion G L Ldual
  /-- Fppf-locally the sheaf has the canonical tensor form. -/
  locallyCanonicalForm :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (G' : RelativeGroupLaw S'
          (pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : Over.mk t' ⟶
              Over.mk (pullback.snd f
                (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            ((G'.mul t' P Q).left ≫
                pullback.fst f
                  (Spec.map (CommRingCat.ofHom (algebraMap S S')))) =
              (G.mul (t' ≫
                  Spec.map (CommRingCat.ofHom (algebraMap S S')))
                (baseChangePoint (algebraMap S S') P)
                (baseChangePoint (algebraMap S S') Q)).left) →
        ∃ (L₀ L₀dual :
            (pullback f
              (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules),
          IsLineBundle L₀ ∧ KernelTrivial G' L₀ L₀dual ∧
          LocIsoOnBase
            ((Scheme.Modules.pullback
              (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj L)
            (moduleTensor _ L₀
              ((Scheme.Modules.pullback (negMor G')).obj L₀))
  /-- The geometric global-section rank is positive. -/
  positiveRank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    0 < geomFibreH0Finrank G L k sk
  /-- The sheaf is Rosati compatible with the action. -/
  rosatiCompatible : RosatiCompatible G L Ldual act act_over star

/-- The identity point always satisfies the `2`-torsion equation, so the
right-hand side of the kernel condition is not vacuous. -/
theorem mul_one_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    G.mul t (G.one t) (G.one t) = G.one t := G.one_mul t _

end MathlibExt.AlgebraicGeometry.QMCanonicalPol

end

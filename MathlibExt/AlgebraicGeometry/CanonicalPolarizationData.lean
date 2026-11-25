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

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import MathlibExt.AlgebraicGeometry.BundleTrace
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor

@[expose] public section

noncomputable section

/-!
# Canonical polarization data on a relative group law

Two sheaves of modules on a scheme over a base are locally isomorphic over
the base when every point of the base has a Zariski neighbourhood over whose
inverse image they are isomorphic.  For a relative group law, the negation
and addition morphisms, the Mumford bundle `m^* L ⊗ p₁^* L^∨ ⊗ p₂^* L^∨`
built from a sheaf `L` and its dual `L^∨ = 𝓗om(L, 𝒪)`, its kernel
conditions, and Rosati compatibility with an action are defined directly
from the group law on points.  Canonical polarization data packages an
invertible sheaf that is symmetric, whose Mumford kernel is exactly the
`2`-torsion, that after a faithfully flat extension of the base ring is a
tensor product of a kernel-trivial sheaf with its negation pullback, that
has positive geometric global-section rank in every algebraically closed
fibre, and that is Rosati compatible.

Line bundles, the structure sheaf and the tensor product are those of
`CoherentCurveLinearSeries` and `SchemeModulesTensor`; the dual is the sheaf
Hom `BundleTrace.homSheaf` into the structure sheaf.
-/

namespace MathlibExt.AlgebraicGeometry.QMCanonicalPol

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor

universe u v

/-- Two sheaves of modules on `X` are locally isomorphic over the base
`g : X ⟶ Y` when every point of `Y` has an open neighbourhood `U` such that
their restrictions to the inverse image `g ⁻¹ᵁ U` are isomorphic. -/
def LocIsoOnBase {X Y : Scheme.{u}} (g : X ⟶ Y) (M M' : X.Modules) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅
      (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M')

/-- Every sheaf of modules is locally isomorphic to itself over the base. -/
theorem locIsoOnBase_refl {X Y : Scheme.{u}} (g : X ⟶ Y) (M : X.Modules) :
    LocIsoOnBase g M M :=
  fun _ ↦ ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

/-- Local isomorphism over the base is symmetric. -/
theorem locIsoOnBase_symm {X Y : Scheme.{u}} {g : X ⟶ Y} {M M' : X.Modules}
    (h : LocIsoOnBase g M M') : LocIsoOnBase g M' M :=
  fun y ↦ (h y).imp fun _ ⟨hy, ⟨e⟩⟩ ↦ ⟨hy, ⟨e.symm⟩⟩

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

/-- The Mumford bundle `m^* L ⊗ p₁^* L^∨ ⊗ p₂^* L^∨` on `A ×_S A`, where
`L^∨ = 𝓗om(L, 𝒪_A)` is the dual of `L`: the sheaf Hom from `L` into the
structure sheaf. -/
def mumfordBundle (L : A.Modules) : (pullback f f).Modules :=
  moduleTensor _
    ((Scheme.Modules.pullback (addMor G)).obj L)
    (moduleTensor _
      ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (BundleTrace.homSheaf A L (structureModule A)))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (BundleTrace.homSheaf A L (structureModule A))))

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
to it over the base. -/
def IsSymmetric (L : A.Modules) : Prop :=
  LocIsoOnBase f ((Scheme.Modules.pullback (negMor G)).obj L) L

/-- The kernel of the Mumford bundle is trivial: a point over an affine
test scheme `Spec R` whose slice of the Mumford bundle is locally trivial
over `Spec R` is the identity point. -/
def KernelTrivial (L : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of S)) (x : Over.mk t ⟶ Over.mk f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt x)).obj (mumfordBundle G L))
        (structureModule _) →
      x = G.one t

/-- The kernel of the Mumford bundle is exactly the `2`-torsion: a point
over an affine test scheme `Spec R` lies in the kernel, that is, its slice
of the Mumford bundle is locally trivial over `Spec R`, if and only if it is
killed by `2`.  This is the kernel of a sheaf of the canonical form
`L₀ ⊗ (-1)^* L₀` with `L₀` principal: there
`φ_L = φ_{L₀} + φ_{(-1)^* L₀} = 2 φ_{L₀}` with `φ_{L₀}` an isomorphism, so
`ker φ_L = A[2]`. -/
def KernelIsTwoTorsion (L : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of S)) (x : Over.mk t ⟶ Over.mk f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt x)).obj (mumfordBundle G L))
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
involution: the two Rosati lifts pull the Mumford bundle back to sheaves
that are locally isomorphic over the base. -/
def RosatiCompatible (L : A.Modules) {I : Type v}
    (act : I → (A ⟶ A)) (act_over : ∀ b, act b ≫ f = f)
    (star : I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase (pullback.fst f f ≫ f)
      ((Scheme.Modules.pullback
          (rosatiLiftLeft act act_over b)).obj
        (mumfordBundle G L))
      ((Scheme.Modules.pullback
          (rosatiLiftRight act act_over star b)).obj
        (mumfordBundle G L))

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

/-- Canonical polarization data for a sheaf `L`: `L` is invertible and
symmetric, its Mumford kernel is exactly the `2`-torsion, after a faithfully
flat extension of the base ring it is a kernel-trivial sheaf tensored with
its negation pullback, its geometric global-section rank is positive, and it
is Rosati compatible with the action. -/
structure CanonicalPolarizationData {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (star : I → I)
    (L : A.Modules) : Prop where
  /-- The sheaf is invertible. -/
  isLineBundle : IsLineBundle L
  /-- The sheaf is symmetric. -/
  isSymmetric : IsSymmetric G L
  /-- The Mumford kernel is exactly the `2`-torsion. -/
  kernelIsTwoTorsion : KernelIsTwoTorsion G L
  /-- After a faithfully flat extension `S → S'` of the base ring (an fpqc
  cover: finite presentation is not required), the sheaf has the canonical
  tensor form `L₀ ⊗ (-1)^* L₀` with `L₀` invertible and kernel-trivial,
  locally over `Spec S'`. -/
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
        ∃ L₀ :
            (pullback f
              (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          IsLineBundle L₀ ∧ KernelTrivial G' L₀ ∧
          LocIsoOnBase
            (pullback.snd f
              (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback
              (pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj L)
            (moduleTensor _ L₀
              ((Scheme.Modules.pullback (negMor G')).obj L₀))
  /-- The geometric global-section rank is positive. -/
  positiveRank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    0 < geomFibreH0Finrank G L k sk
  /-- The sheaf is Rosati compatible with the action. -/
  rosatiCompatible : RosatiCompatible G L act act_over star

/-- The identity point always satisfies the `2`-torsion equation, so the
right-hand side of the kernel condition is not vacuous. -/
theorem mul_one_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    G.mul t (G.one t) (G.one t) = G.one t := G.one_mul t _

end MathlibExt.AlgebraicGeometry.QMCanonicalPol

end

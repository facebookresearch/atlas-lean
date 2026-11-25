/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_PolarisedAbelianScheme.lean`,
`Definitions/Def_JacJ1Iface.lean`,
`Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean`,
`Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean`,
`Definitions/Def_CerednikDrinfeld_QMCanonicalPol.lean`,
`Definitions/Def_CerednikDrinfeld_QMStructureOnPolarised.lean`,
`Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_IsPullback_trans.lean`
and
`P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_IsPullback_trans.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.BundleTrace
public import MathlibExt.AlgebraicGeometry.ProjSpace
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree
public import MathlibExt.AlgebraicGeometry.SchemeHomOver
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor


/-!
# Polarised abelian schemes with quaternion multiplication

A polarised abelian scheme is an abelian scheme equipped with a very
ample polarisation line bundle and a full level structure. A quaternion
multiplication structure is an action of an order in a quaternion
algebra by group endomorphisms, compatible with the level points, whose
polarisation is locally the cube of a canonical polarisation for the
action. Pullback of such a structure along a ring homomorphism is
transitive.

## Implementation notes

Very ampleness is `Scheme.Modules.ClosedImmersionBySections`: some
presentation of the sheaf by global sections maps the scheme to
projective space over the base by a closed immersion.

The tensor product of sheaves of modules is
`SchemeModulesTensor.moduleTensor`, the sheafified tensor product of the
underlying presheaves of modules, and the dual of a sheaf of modules is
its Hom sheaf `BundleTrace.homSheaf` into the structure sheaf. These
agree up to canonical isomorphism with the monoidal operations of the
source, and the conditions below use them only up to local isomorphism
(`LocIsoOnBase`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BundleTrace (homSheaf)
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor (moduleTensor)

open scoped Quaternion

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- Push a point forward along a morphism over the base. -/
def mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  P ≫ Over.homMk φ hφ

@[simp]
theorem mapPt_left {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : (mapPt φ hφ P).left = P.left ≫ φ := rfl

/-- Reindex a point along a morphism of test schemes. -/
def compPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) : SchemeHomOver t' f :=
  Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ P

/-- View a point as a point over a different, equal, base morphism. -/
def toPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {T : Scheme.{u}} {t u : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) (h : P.left ≫ f = u) : SchemeHomOver u f :=
  Over.homMk P.left h

/-- Pull a point back along a morphism of schemes over different bases:
given `g : A' ⟶ A` with `g ≫ f = f' ≫ ψ`, a point of `A'` over `t'`
gives a point of `A` over `t' ≫ ψ`. -/
def pullPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {S' : Type u} [CommRing S'] {f' : A' ⟶ Spec (CommRingCat.of S')}
    {ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)}
    (g : A' ⟶ A) (hg : g ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  Over.homMk (P.left ≫ g) (by
    have hw : P.left ≫ f' = t' := Over.w P
    show (P.left ≫ g) ≫ f = t' ≫ ψ
    rw [Category.assoc, hg, ← Category.assoc, hw])

@[simp]
theorem pullPt_left {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {S' : Type u} [CommRing S'] {f' : A' ⟶ Spec (CommRingCat.of S')}
    {ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)}
    (g : A' ⟶ A) (hg : g ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' f') : (pullPt g hg P).left = P.left ≫ g := rfl

/-- The left morphism of a group-law multiplication depends only on the
left morphisms of the factors. -/
theorem RelativeGroupLaw.mul_left_congr {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    {x₁ y₁ : SchemeHomOver t₁ f} {x₂ y₂ : SchemeHomOver t₂ f}
    (hx : x₁.left = x₂.left) (hy : y₁.left = y₂.left) :
    (L.mul t₁ x₁ y₁).left = (L.mul t₂ x₂ y₂).left := by
  subst ht
  have hx' : x₁ = x₂ := Over.OverMorphism.ext hx
  have hy' : y₁ = y₂ := Over.OverMorphism.ext hy
  subst hx'; subst hy'; rfl

/-- Push a point forward along an endomorphism over the base. -/
abbrev pushPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A) (hφ : φ ≫ f = f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    SchemeHomOver t f :=
  mapPt φ hφ P

namespace RelativeGroupLaw

/-- Finite linear combinations of points with natural coefficients. -/
def finComb {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) : SchemeHomOver t f :=
  letI := L.pointGroup t
  (List.ofFn fun i => x i ^ c i).prod

end RelativeGroupLaw

/-- The usual package of properties of an abelian scheme. -/
structure AbelianSchemePropertyBundle {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) : Prop where
  /-- The structure morphism is smooth. -/
  smooth : Smooth f
  /-- The structure morphism is proper. -/
  proper : IsProper f
  /-- Every fibre is connected. -/
  connectedFibres : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})
  /-- The scheme carries a relative group law. -/
  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

namespace Scheme.Modules

/-- A sheaf of modules is invertible if it is locally isomorphic to the
structure sheaf. -/
structure IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  /-- Every point has a neighbourhood trivialising the sheaf. -/
  exists_trivialization : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

section ProjPresentation

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}}

/-- A presentation of `M` by `N + 1` global sections `σ i` over `Spec R`: a
morphism `toProj` from `X` to projective `N`-space over `R`, lying over `f`,
such that on every open contained in the preimage of the chart `D₊(X i)` the
section `σ i` freely generates `M`, and on the preimage of `D₊(X i)` the
pullback of the coordinate ratio `X j / X i` carries `σ i` to `σ j`. -/
structure ProjPresentation (M : X.Modules) (f : X ⟶ Spec (.of R)) (N : ℕ) where
  /-- The global sections. -/
  σ : Fin (N + 1) → Γ(M, ⊤)
  /-- The morphism to projective `N`-space over `R`. -/
  toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
  /-- The morphism to projective space lies over `f`. -/
  toProj_π : toProj ≫ ProjSpace.π R N = f
  /-- On every open contained in the preimage of `D₊(X i)`, the section
  `σ i` freely generates `M`. -/
  frame : ∀ (i : Fin (N + 1)) (V : X.Opens),
    V ≤ toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i) →
    Function.Bijective fun g : Γ(X, V) =>
      g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))
  /-- On the preimage of `D₊(X i)`, the pullback of the coordinate ratio
  `X j / X i` carries `σ i` to `σ j`. -/
  app_ratio_smul : ∀ i j : Fin (N + 1),
    (toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i))
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
            (MvPolynomial.isHomogeneous_X R i)) 1 (MvPolynomial.X j)
          (by
            simpa using (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
              (MvPolynomial.isHomogeneous_X R j))))) •
        M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (MvPolynomial.X i) ≤ ⊤)).op (σ i) =
      M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (MvPolynomial.X i) ≤ ⊤)).op (σ j)

/-- `M` is very ample relative to `f`: some presentation of `M` by global
sections over `Spec R` maps `X` to projective space over `R` by a closed
immersion. -/
def ClosedImmersionBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsClosedImmersion 𝔓.toProj

end ProjPresentation

end Scheme.Modules

/-- Two sheaves of modules are locally isomorphic over the base. -/
def LocIsoOnBase {S' : Type u} [CommRing S'] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of S')) (M M' : X.Modules) : Prop :=
  ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens,
    s ∈ U ∧ Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅
      (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M')

namespace Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
  (L : RelativeGroupLaw S f)

/-- The inversion morphism `A ⟶ A` of a relative group law: the inverse of
the tautological point `𝟙 A`. -/
def negMor : A ⟶ A :=
  (L.inv f (𝟙 (Over.mk f))).left

/-- The addition morphism `A ×_S A ⟶ A` of a relative group law: the
product of the two projections. -/
def addMor : pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f)
    (Over.homMk (U := Over.mk (pullback.fst f f ≫ f)) (V := Over.mk f)
      (pullback.fst f f) rfl)
    (Over.homMk (U := Over.mk (pullback.fst f f ≫ f)) (V := Over.mk f)
      (pullback.snd f f) pullback.condition.symm)).left

/-- A sheaf of modules is symmetric if its pullback along the inversion is
locally isomorphic to it over the base. -/
def IsSymmetric (𝓛 : A.Modules) : Prop :=
  LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) 𝓛

/-- The Mumford bundle `m^* 𝓛 ⊗ (p₁^* 𝓛^∨ ⊗ p₂^* 𝓛^∨)` on `A ×_S A`, where
`m` is the addition, `p₁` and `p₂` are the projections, and `𝓛^∨` is the
Hom sheaf from `𝓛` to the structure sheaf. -/
def mumfordBundle (𝓛 : A.Modules) : (pullback f f).Modules :=
  moduleTensor _ ((Scheme.Modules.pullback (addMor f L)).obj 𝓛)
    (moduleTensor _
      ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (homSheaf A 𝓛 (SheafOfModules.unit A.ringCatSheaf)))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (homSheaf A 𝓛 (SheafOfModules.unit A.ringCatSheaf))))

/-- The slice `A ×_S T ⟶ A ×_S A`, `(a, s) ↦ (a, x s)`, of a point `x` of
`A` over `T`. -/
def sliceAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ x.left) (by
    have hx : x.left ≫ f = t := Over.w x
    rw [Category.assoc, hx]
    exact pullback.condition)

/-- The kernel of the Mumford map of `𝓛` is trivial: a point over an affine
base at whose slice the Mumford bundle is locally trivial over the base is
the identity. -/
def KernelTrivial (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))
        (SheafOfModules.unit (pullback f t).ringCatSheaf) →
      x = L.one t

/-- The kernel of the Mumford map of `𝓛` is the two-torsion: the Mumford
bundle is locally trivial over the base at the slice of a point over an
affine base exactly when the point is two-torsion. -/
def KernelIsTwoTorsion (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛))
        (SheafOfModules.unit (pullback f t).ringCatSheaf) ↔
      L.mul t x x = L.one t

/-- Rosati compatibility of an action `ι` with an involution `star`: for each
`b`, the pullbacks of the Mumford bundle along `1 × ι b` and `ι (star b) × 1`
are locally isomorphic over the base. -/
def RosatiCompatible (𝓛 : A.Modules) {I : Type*} (ι : I → (A ⟶ A))
    (hι : ∀ b, ι b ≫ f = f) (star : I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase (pullback.fst f f ≫ f)
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ ι b)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj
        (mumfordBundle f L 𝓛))
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f ≫ ι (star b)) (pullback.snd f f)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj
        (mumfordBundle f L 𝓛))

end Polarisation

/-- The finrank of the global sections of a sheaf on a geometric fibre. -/
noncomputable def Scheme.Modules.geomFibreH0Finrank {S : Type u} [CommRing S]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (M : A.Modules)
    (k : Type u) [Field k] (sk : S →+* k) : ℕ :=
  letI : Algebra k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module k
      Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤) :=
    Module.compHom _ (algebraMap k
      Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
  Module.finrank k
    Γ((Scheme.Modules.pullback
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤)

variable {S : Type u} [CommRing S]

/-- The geometric point of `Spec S` at a map to a field. -/
def geomPoint (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom sk)

/-- The dual-number thickening of a geometric point. -/
def tangentBase (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp sk))

/-- The zero section of the dual-number thickening. -/
def tangentZero (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

/-- Scaling the dual-number coordinate. -/
def tangentScale (k : Type u) [Field k] (c : k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)

/-- A point over dual numbers is a tangent vector if it reduces to the
identity point. -/
def IsTangentVector {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)
    (P : SchemeHomOver (tangentBase k sk) f) : Prop :=
  tangentZero k ≫ P.left = (L.one (geomPoint k sk)).left

/-- Canonical polarisation data for an action `act` with involution `star`
on a relative group law `L`: an invertible sheaf `𝓛` that is symmetric,
whose Mumford kernel is the two-torsion, such that after a faithfully flat
base change `S → S'`, for every group law `L'` on the base change
compatible with `L`, the pullback of `𝓛` is locally isomorphic over the
base to `𝓛₀ ⊗ [-1]^* 𝓛₀` for an invertible `𝓛₀` with trivial Mumford
kernel, which has positive geometric fibre rank, and which is Rosati
compatible with `act` and `star`. -/
def IsCanonicalPolData {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {I : Type*} (act : I → (A ⟶ A))
    (act_over : ∀ x : I, act x ≫ f = f) (star : I → I) (𝓛 : A.Modules) :
    Prop :=
  Scheme.Modules.IsInvertible 𝓛 ∧ Polarisation.IsSymmetric f L 𝓛 ∧
  Polarisation.KernelIsTwoTorsion f L 𝓛 ∧
  (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
    Module.FaithfullyFlat S S' ∧
    ∀ (L' : RelativeGroupLaw S'
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
        (P Q : SchemeHomOver t'
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
          (L'.mul t' P Q).left ≫
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
              (pullPt (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                pullback.condition P)
              (pullPt (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                pullback.condition Q)).left) →
      ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧
        Polarisation.KernelTrivial
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ((Scheme.Modules.pullback
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛)
          (moduleTensor _ 𝓛₀
            ((Scheme.Modules.pullback
              (Polarisation.negMor
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                L')).obj 𝓛₀))) ∧
  (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk) ∧
  Polarisation.RosatiCompatible f L 𝓛 act act_over star

/-- A polarised abelian scheme of dimension `g`, polarisation degree
parameter `d` and level `n` over `S`. -/
structure PolarisedAbelianScheme (g d n : ℕ) (S : Type u) [CommRing S] :
    Type (u + 1) where
  /-- The underlying scheme. -/
  A : Scheme.{u}
  /-- The structure morphism. -/
  f : A ⟶ Spec (CommRingCat.of S)
  /-- The relative group law. -/
  L : RelativeGroupLaw S f
  /-- The group law is commutative. -/
  comm : L.IsCommutative
  /-- The abelian-scheme properties. -/
  bundle : AbelianSchemePropertyBundle f
  /-- Every fibre has dimension `g`. -/
  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)),
    topologicalKrullDim ↥(f.base ⁻¹' {s}) = g
  /-- The level points. -/
  P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f
  /-- The level points are `n`-torsion. -/
  P_torsion : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) =
    L.one (𝟙 (Spec (CommRingCat.of S)))
  /-- The level points are independent over an algebraically closed field. -/
  P_indep : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (c c' : Fin (2 * g) → Fin n),
    L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => compPt (Spec.map (CommRingCat.ofHom sk)) (by simp) (P i)) (fun i => (c i : ℕ)) =
      L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => compPt (Spec.map (CommRingCat.ofHom sk)) (by simp) (P i)) (fun i => (c' i : ℕ)) →
      c = c'
  /-- The level points span the `n`-torsion over an algebraically closed
  field. -/
  P_span : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
    L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q =
      L.one (Spec.map (CommRingCat.ofHom sk)) →
      ∃ c : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => compPt (Spec.map (CommRingCat.ofHom sk)) (by simp) (P i))
          (fun i => (c i : ℕ)) = Q
  /-- The polarisation sheaf. -/
  pol : A.Modules
  /-- The polarisation sheaf is invertible. -/
  pol_isInvertible : Scheme.Modules.IsInvertible pol
  /-- The polarisation sheaf is very ample relative to the base: some
  presentation of it by global sections maps `A` to projective space over
  `S` by a closed immersion. -/
  pol_veryAmple : Scheme.Modules.ClosedImmersionBySections pol f
  /-- The polarisation has geometric fibre rank `d`. -/
  pol_finrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    Scheme.Modules.geomFibreH0Finrank f pol k sk = d

namespace PolarisedAbelianScheme

variable {g d n : ℕ}

/-- An isomorphism of polarised abelian schemes. -/
def Iso {S : Type u} [CommRing S] (u u' : PolarisedAbelianScheme g d n S) :
    Prop :=
  ∃ (e : u.A ≅ u'.A) (he : e.hom ≫ u'.f = u.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (x y : SchemeHomOver t u.f),
      mapPt e.hom he (u.L.mul t x y) =
        u'.L.mul t (mapPt e.hom he x) (mapPt e.hom he y)) ∧
    (∀ i, (u.P i).left ≫ e.hom = (u'.P i).left) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)),
      ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj
          ((Scheme.Modules.pullback e.hom).obj u'.pol) ≅
          (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol))

/-- Pullback of a polarised abelian scheme along a ring homomorphism. -/
def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S') :
    Prop :=
  ∃ (gA : u'.A ⟶ u.A)
    (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).left ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (pullPt gA hg.w x) (pullPt gA hg.w y)).left) ∧
    (∀ i, (u'.P i).left ≫ gA =
      Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).left) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol)

end PolarisedAbelianScheme

variable {a b : ℚ}

/-- A quaternion multiplication structure on a polarised abelian scheme:
an action of the order `Λ` by group endomorphisms, with the trace
identity on tangent spaces, a distinguished level point, and a
polarisation that is locally the cube of a canonical polarisation. -/
structure QMStructure (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ)
    (β : Fin (2 * 2) → ↥Λ) {d m : ℕ} {S : Type u} [CommRing S]
    (X : PolarisedAbelianScheme 2 d m S) : Type (u + 1) where
  /-- The action of the order. -/
  act : ↥Λ → (X.A ⟶ X.A)
  /-- The action is over the base. -/
  act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f
  /-- The action acts by group homomorphisms on points. -/
  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t X.f),
    pushPt (act x) (act_over x) (X.L.mul t P Q) =
      X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)
  /-- The element `1` acts as the identity. -/
  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A
  /-- The action is multiplicative in the order. -/
  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x
  /-- The action is additive on points. -/
  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t X.f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)
  /-- The trace of the action on tangent spaces is the quaternion trace. -/
  act_trace : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) X.f),
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) X.f,
      P ∈ Set.range τ ↔ IsTangentVector X.L k sk P) →
    (∀ v w : V, τ (v + w) = X.L.mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).left = tangentScale k c ≫ (τ v).left) →
    ∀ (x : ↥Λ) (Φ : V →ₗ[k] V),
    (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
    ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) =
      ((n : ℚ) : ℍ[ℚ, a, b]) → LinearMap.trace k V Φ = (n : k)
  /-- A distinguished level point. -/
  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f
  /-- The distinguished point matches the level points under the action. -/
  level_match : ∀ j : Fin (2 * 2),
    pushPt (act (β j)) (act_over (β j)) P = X.P j
  /-- The polarisation is locally isomorphic over the base to the cube
  `polE ⊗ polE ⊗ polE` of a canonical polarisation `polE` for the
  action. -/
  pol_canonical : ∃ polE : X.A.Modules,
    IsCanonicalPolData X.f X.L act act_over star polE ∧
    LocIsoOnBase X.f X.pol (moduleTensor X.A polE (moduleTensor X.A polE polE))

namespace QMStructure

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
  {d m : ℕ}

/-- Pullback of a quaternion multiplication structure along a ring
homomorphism. -/
def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X') : Prop :=
  ∃ (gA : X'.A ⟶ X.A)
    (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (x y : SchemeHomOver t' X'.f),
      (X'.L.mul t' x y).left ≫ gA =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (pullPt gA hg.w x) (pullPt gA hg.w y)).left) ∧
    (∀ i, (X'.P i).left ≫ gA =
      Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).left) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
    (∀ x : ↥Λ, s'.act x ≫ gA = gA ≫ s.act x) ∧
    s'.P.left ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ s.P.left

private theorem specMap_ofHom_comp {S S' S'' : Type u} [CommRing S]
    [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- Pullback of quaternion multiplication structures is transitive. -/
theorem IsPullback.trans {S S' S'' : Type u} [CommRing S] [CommRing S']
    [CommRing S''] (φ : S →+* S') (χ : S' →+* S'')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    {X'' : PolarisedAbelianScheme 2 d m S''}
    {t : QMStructure Λ star β X} {t' : QMStructure Λ star β X'}
    {t'' : QMStructure Λ star β X''}
    (h : IsPullback φ t t') (h' : IsPullback χ t' t'') :
    IsPullback (χ.comp φ) t t'' := by
  obtain ⟨g₁, hg₁, hmul₁, hP₁, ⟨φ₁⟩, hact₁, hQ₁⟩ := h
  obtain ⟨g₂, hg₂, hmul₂, hP₂, ⟨φ₂⟩, hact₂, hQ₂⟩ := h'
  have e : Spec.map (CommRingCat.ofHom (χ.comp φ)) =
      Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom φ) :=
    specMap_ofHom_comp φ χ
  have hg : CategoryTheory.IsPullback (g₂ ≫ g₁) X''.f X.f
      (Spec.map (CommRingCat.ofHom (χ.comp φ))) := by
    rw [e]; exact hg₂.paste_horiz hg₁
  refine ⟨g₂ ≫ g₁, hg, ?_, ?_, ⟨?_⟩, ?_, ?_⟩
  · intro T t' x y
    have h1 := hmul₂ t' x y
    have h2 := hmul₁ (t' ≫ Spec.map (CommRingCat.ofHom χ))
      (pullPt g₂ hg₂.w x) (pullPt g₂ hg₂.w y)
    calc (X''.L.mul t' x y).left ≫ (g₂ ≫ g₁)
        = ((X''.L.mul t' x y).left ≫ g₂) ≫ g₁ := (Category.assoc _ _ _).symm
      _ = (X'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom χ))
            (pullPt g₂ hg₂.w x) (pullPt g₂ hg₂.w y)).left ≫ g₁ := by rw [h1]
      _ = (X.L.mul ((t' ≫ Spec.map (CommRingCat.ofHom χ)) ≫
              Spec.map (CommRingCat.ofHom φ))
            (pullPt g₁ hg₁.w (pullPt g₂ hg₂.w x))
            (pullPt g₁ hg₁.w (pullPt g₂ hg₂.w y))).left := h2
      _ = (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (χ.comp φ)))
            (pullPt (g₂ ≫ g₁) hg.w x) (pullPt (g₂ ≫ g₁) hg.w y)).left :=
        X.L.mul_left_congr (by rw [e, Category.assoc])
          (by simp only [pullPt_left, Category.assoc])
          (by simp only [pullPt_left, Category.assoc])
  · intro i
    rw [← Category.assoc, hP₂, Category.assoc, hP₁, ← Category.assoc, ← e]
  · exact ((Scheme.Modules.pullbackComp (f := g₂) (g := g₁)).app X.pol).symm ≪≫
      Functor.mapIso (Scheme.Modules.pullback (f := g₂)) φ₁ ≪≫ φ₂
  · intro x
    rw [← Category.assoc, hact₂, Category.assoc, hact₁, Category.assoc]
  · rw [← Category.assoc, hQ₂, Category.assoc, hQ₁, ← Category.assoc, ← e]

end QMStructure

end AlgebraicGeometry

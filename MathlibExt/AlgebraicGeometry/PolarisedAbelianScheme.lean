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
`Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean`,
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
public import MathlibExt.AlgebraicGeometry.CanonicalPolarizationData
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.ProjSpace.Basic
public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurve
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree
public import MathlibExt.AlgebraicGeometry.SchemeHomOver
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor


/-!
# Polarised abelian schemes with quaternion multiplication

A polarised abelian scheme is an abelian scheme equipped with a very
ample polarisation line bundle and a full level structure. A quaternion
multiplication structure is an action of a `ℤ`-submodule of a quaternion
algebra (no order condition is imposed) by group endomorphisms, compatible
with the level points, whose polarisation is locally the cube of a canonical
polarisation for the action. Pullback of such a structure along a ring
homomorphism is transitive.

## Implementation notes

Very ampleness is `Scheme.Modules.ClosedImmersionBySections`: some
presentation of the sheaf by global sections maps the scheme to
projective space over the base by a closed immersion.

Invertibility is `CoherentCurveLinearSeries.IsLineBundle`. Canonical
polarisations, local isomorphism over the base and the rank of global
sections on geometric fibres are those of `QMCanonicalPol`
(`CanonicalPolarizationData`, `LocIsoOnBase`, `geomFibreH0Finrank`), and
the tensor cube is built with `SchemeModulesTensor.moduleTensor`. Points
are pushed forward and reindexed with `CerednikDrinfeld.QM.mapPt`,
`pushPt` and `compPt`, and pulled back along a commutative square with
`CerednikDrinfeld.QM.pullPt`; tangent vectors are those of
`CerednikDrinfeld.QM.IsTangentVector`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle)
open MathlibExt.AlgebraicGeometry.QMCanonicalPol
  (CanonicalPolarizationData LocIsoOnBase geomFibreH0Finrank)
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor (moduleTensor)

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

variable {R : Type u} [CommRing R]

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
    change (P.left ≫ g) ≫ f = t' ≫ ψ
    rw [Category.assoc, hg, ← Category.assoc, hw])

@[simp]
theorem pullPt_left {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {S' : Type u} [CommRing S'] {f' : A' ⟶ Spec (CommRingCat.of S')}
    {ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)}
    (g : A' ⟶ A) (hg : g ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' f') : (pullPt g hg P).left = P.left ≫ g := rfl

end CerednikDrinfeld.QM

open CerednikDrinfeld.QM
  (compPt IsTangentVector mapPt pullPt pullPt_left pushPt tangentBase tangentScale)

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

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

namespace RelativeGroupLaw

/-- Finite linear combinations of points with natural coefficients. -/
def finComb {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) : SchemeHomOver t f :=
  letI := L.pointGroup t
  (List.ofFn fun i => x i ^ c i).prod

end RelativeGroupLaw

/-- Smoothness and properness of `f : A ⟶ Spec R`, connectedness of every
fibre of `f`, and the existence of a relative group law on `A` over
`Spec R`. The group law need not be commutative. -/
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
        (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
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

/-- A polarised abelian scheme over `S` with fibres of dimension `g` and a
full level-`n` structure: `2 * g` sections of order dividing `n` that write
every `n`-torsion point over an algebraically closed field in exactly one
way as a combination with coefficients in `Fin n`. Its polarisation `pol`
is an invertible, very ample sheaf whose global sections have dimension `d`
on every geometric fibre. -/
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
  pol_isInvertible : IsLineBundle pol
  /-- The polarisation sheaf is very ample relative to the base: some
  presentation of it by global sections maps `A` to projective space over
  `S` by a closed immersion. -/
  pol_veryAmple : Scheme.Modules.ClosedImmersionBySections pol f
  /-- The polarisation has geometric fibre rank `d`. -/
  pol_finrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    geomFibreH0Finrank f pol k sk = d

namespace PolarisedAbelianScheme

variable {g d n : ℕ}

/-- `u` and `u'` are isomorphic: some isomorphism `e : u.A ≅ u'.A` over
`Spec S` carries the group law of `u` to that of `u'` and the level points
of `u` to those of `u'`, and pulls `u'.pol` back to a sheaf that is locally
isomorphic over the base to `u.pol`. -/
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

/-- `u'` is a pullback of `u` along `φ : S →+* S'`: some `gA : u'.A ⟶ u.A`
forms a pullback square with the structure morphisms and `Spec φ`, carries
products for the group law of `u'` to products for that of `u`, carries
each level point of `u'` to the base change of the corresponding level
point of `u`, and pulls `u.pol` back to a sheaf isomorphic to `u'.pol`. -/
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
an action of a `ℤ`-submodule `Λ` of `ℍ[ℚ, a, b]` by group endomorphisms
(no order condition is imposed on `Λ`; `act_one` and `act_mul` apply
only when `1` and the product lie in `Λ`), with the trace identity on
tangent spaces, a distinguished level point, and a polarisation that is
locally the cube of a canonical polarisation. -/
structure QMStructure (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ)
    (β : Fin (2 * 2) → ↥Λ) {d m : ℕ} {S : Type u} [CommRing S]
    (X : PolarisedAbelianScheme 2 d m S) : Type (u + 1) where
  /-- The action of `Λ`. -/
  act : ↥Λ → (X.A ⟶ X.A)
  /-- The action is over the base. -/
  act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f
  /-- The action acts by group homomorphisms on points. -/
  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t X.f),
    pushPt (act x) (act_over x) (X.L.mul t P Q) =
      X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)
  /-- If `1` lies in `Λ`, it acts as the identity. -/
  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A
  /-- The action is multiplicative wherever the product lies in `Λ`. -/
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
    CanonicalPolarizationData X.L act act_over star polE ∧
    LocIsoOnBase X.f X.pol (moduleTensor X.A polE (moduleTensor X.A polE polE))

namespace QMStructure

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
  {d m : ℕ}

/-- `s'` is a pullback of `s` along `φ : S →+* S'`: some `gA : X'.A ⟶ X.A`
satisfies the four conditions of `PolarisedAbelianScheme.IsPullback` for `X`
and `X'`, intertwines the actions of `Λ`, and carries the distinguished
point of `s'` to the base change of that of `s`. -/
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

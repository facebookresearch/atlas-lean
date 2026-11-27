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
built from a sheaf `L` and its dual `L^∨ = 𝓗om(L, 𝒪)`, and its kernel
conditions are defined directly from the group law on points.  Rosati
compatibility takes a family `act : I → (A ⟶ A)` of endomorphisms of `A`
over the base and a map `star : I → I` (`act` need not be an action, nor
`star` an involution), and compares the pullbacks of the Mumford bundle along
`(x, y) ↦ (x, act b y)` and `(x, y) ↦ (act (star b) x, y)`.  Canonical
polarization data packages an invertible sheaf that is symmetric, whose
Mumford kernel is exactly the `2`-torsion, that after a faithfully flat
extension of the base ring is, locally over the new base, a tensor product
of a kernel-trivial sheaf with its negation pullback for every group law on
the base change compatible with the given one (the base change of the law
is one, so the form holds for it), whose global sections on every geometric
fibre are finite-dimensional and nonzero, and that is Rosati compatible
with the given `act` and `star`.

Line bundles, the structure sheaf and the tensor product are those of
`CoherentCurveLinearSeries` and `SchemeModulesTensor`; the dual is the sheaf
Hom `BundleTrace.homSheaf` into the structure sheaf; the base change of a
group law and of its points is that of `RelativeGroupLaw`.
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

/-- The slice at a `T`-point `x` of `A` over `t : T ⟶ Spec S`: the map
`A ×_S T ⟶ A ×_S A`, `(a, s) ↦ (a, x s)`, along which the kernel conditions
pull back the Mumford bundle. -/
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
killed by `2`.  For an abelian scheme, this is the kernel of a sheaf of the
canonical form `L₀ ⊗ (-1)^* L₀` with `L₀` principal: there
`φ_L = φ_{L₀} + φ_{(-1)^* L₀} = 2 φ_{L₀}` with `φ_{L₀}` an isomorphism, so
`ker φ_L = A[2]`.  The definition itself takes any relative group law. -/
def KernelIsTwoTorsion (L : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶
      Spec (CommRingCat.of S)) (x : Over.mk t ⟶ Over.mk f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt x)).obj (mumfordBundle G L))
        (structureModule _) ↔
      G.mul t x x = G.one t

/-- The first Rosati lift: for a family `act : I → (A ⟶ A)` of endomorphisms
of `A` over the base and an index `b : I`, the map `A ×_S A ⟶ A ×_S A`,
`(x, y) ↦ (x, act b y)`. -/
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

/-- The second Rosati lift: for a family `act : I → (A ⟶ A)` of
endomorphisms of `A` over the base, a map `star : I → I` and an index
`b : I`, the map `A ×_S A ⟶ A ×_S A`, `(x, y) ↦ (act (star b) x, y)`. -/
def rosatiLiftRight {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (star : I → I) (b : I) :
    pullback f f ⟶ pullback f f :=
  pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
    (by
      calc pullback.fst f f ≫ act (star b) ≫ f
          = pullback.fst f f ≫ f := by
            rw [act_over]
        _ = pullback.snd f f ≫ f := pullback.condition)

/-- Rosati compatibility of `L` with a family `act : I → (A ⟶ A)` of
endomorphisms of `A` over the base (`act_over`) and a map `star : I → I`:
for every `b : I`, the pullback of the Mumford bundle along
`rosatiLiftLeft`, `(x, y) ↦ (x, act b y)`, and its pullback along
`rosatiLiftRight`, `(x, y) ↦ (act (star b) x, y)`, are locally isomorphic
over the base `Spec S`.  Nothing else is asked of the inputs: `I` carries no
structure, the maps `act b` need not form an action or respect the group
law, and `star` need not be an involution (a constant map on a two-element
type is allowed).  The name refers to the use with `act` an action of a ring
on `A` and `star` an involution of that ring. -/
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

/-- The base change `G.baseChange i` of a relative group law along
`i : Spec S' ⟶ Spec S` is compatible with `G`: the first projection to `A`
carries the product of two points of the base change to the product, under
`G`, of their images. -/
theorem baseChange_mul_left_fst {S' : Type u} [CommRing S']
    (i : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of S'))
    (P Q : Over.mk t' ⟶ Over.mk (pullback.snd f i)) :
    ((G.baseChange i).mul t' P Q).left ≫ pullback.fst f i =
      (G.mul (t' ≫ i) (RelativeGroupLaw.baseChangePointToBase i P)
        (RelativeGroupLaw.baseChangePointToBase i Q)).left :=
  pullback.lift_fst _ _ _

/-- The dimension over `k` of the global sections of `L` on the fibre of `f`
over `sk : S →+* k`, that is, of the pullback of `L` to `A ×_S Spec k`.  The
definition takes any field `k`; geometric fibres are the case `k`
algebraically closed, which is how `CanonicalPolarizationData.positiveRank`
uses it.  It is `Module.finrank`, so it is `0` when the sections are
infinite-dimensional: a positive value says that they are finite-dimensional
and nonzero. -/
def geomFibreH0Finrank (f : A ⟶ Spec (CommRingCat.of S)) (L : A.Modules) (k : Type u) [Field k]
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
symmetric, its Mumford kernel is exactly the `2`-torsion, after some
faithfully flat extension `S → S'` of the base ring every group law on the
base change that is compatible with `G` (the base change of `G` is one)
makes `L` locally isomorphic over `Spec S'` to `L₀ ⊗ (-1)^* L₀` for an
invertible kernel-trivial `L₀`, its global sections on every geometric
fibre are finite-dimensional and nonzero, and it is Rosati compatible with
the family `act` of endomorphisms over the base and the map `star : I → I`
(`act` need not be an action, nor `star` an involution). -/
structure CanonicalPolarizationData {I : Type v} (act : I → (A ⟶ A))
    (act_over : ∀ b, act b ≫ f = f) (star : I → I)
    (L : A.Modules) : Prop where
  /-- The sheaf is invertible. -/
  isLineBundle : IsLineBundle L
  /-- The sheaf is symmetric. -/
  isSymmetric : IsSymmetric G L
  /-- The Mumford kernel is exactly the `2`-torsion. -/
  kernelIsTwoTorsion : KernelIsTwoTorsion G L
  /-- There is a faithfully flat extension `S → S'` of the base ring (an
  fpqc cover: finite presentation is not required) such that every group law
  `G'` on the base change that is compatible with `G` (the first projection
  carries products under `G'` to products under `G`) gives the canonical
  tensor form: an invertible `L₀`, kernel-trivial for `G'`, with `L`
  locally isomorphic over `Spec S'` to `L₀ ⊗ (-1)^* L₀`.  The field supplies
  no such law itself; the base change `G.baseChange` is one
  (`baseChange_mul_left_fst`), and
  `CanonicalPolarizationData.exists_baseChange_canonicalForm` gives the form
  for it. -/
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
                (RelativeGroupLaw.baseChangePointToBase
                  (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P)
                (RelativeGroupLaw.baseChangePointToBase
                  (Spec.map (CommRingCat.ofHom (algebraMap S S'))) Q)).left) →
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
  /-- On every geometric fibre (`k` algebraically closed) the global sections
  of `L` are finite-dimensional and nonzero: their `Module.finrank` over `k`
  is positive, which rules out both zero and infinite-dimensional sections. -/
  positiveRank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    0 < geomFibreH0Finrank f L k sk
  /-- The sheaf is Rosati compatible (`RosatiCompatible`) with the family
  `act` and the map `star`; `act` need not be an action, nor `star` an
  involution. -/
  rosatiCompatible : RosatiCompatible G L act act_over star

variable {G} in
/-- The canonical form after base change, with the compatible law supplied:
the faithfully flat extension `S → S'` of canonical polarization data and
the base change of `G` to `S'`, which is compatible with `G` by
`baseChange_mul_left_fst`, give an invertible `L₀`, kernel-trivial for that
base change, with `L` locally isomorphic over `Spec S'` to
`L₀ ⊗ (-1)^* L₀`. -/
theorem CanonicalPolarizationData.exists_baseChange_canonicalForm
    {I : Type v} {act : I → (A ⟶ A)} {act_over : ∀ b, act b ≫ f = f}
    {star : I → I} {L : A.Modules}
    (h : CanonicalPolarizationData G act act_over star L) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∃ L₀ :
          (pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
        IsLineBundle L₀ ∧
        KernelTrivial
          (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₀ ∧
        LocIsoOnBase
          (pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
          ((Scheme.Modules.pullback
            (pullback.fst f
              (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj L)
          (moduleTensor _ L₀
            ((Scheme.Modules.pullback (negMor
              (G.baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap S S')))))).obj L₀)) := by
  obtain ⟨S', _, _, hS', hform⟩ := h.locallyCanonicalForm
  exact ⟨S', _, _, hS', hform _ fun t' P Q ↦ baseChange_mul_left_fst G _ t' P Q⟩

end MathlibExt.AlgebraicGeometry.QMCanonicalPol

end

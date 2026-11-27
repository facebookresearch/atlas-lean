/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Homology/TwoTermComplex/DeterminantFunctor.lean`
* `StacksFrontier/Homology/TwoTermComplex/DeterminantLine/SurjectiveQuasiIso.lean`
* `StacksFrontier/Homology/TwoTermComplex/DeterminantLine/Composition.lean`
* `StacksFrontier/Homology/TwoTermComplex/DeterminantLine/Homotopy.lean`
* `StacksFrontier/AlgebraicGeometry/DeterminantTwoTermGlobal/Local.lean`

Modifications: native cochain and derived categories, the source's finite-projective
presentation criterion and exterior-annihilator determinant modules are used, with the whole
kernel, quasi-isomorphism, homotopy and surjective-span normalization.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveDeterminantModules
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Source-normalized two-term determinant presentations and transports

The actual complex lives in degrees `-1,0`. Its determinant module is
`Hom(det K[-1],det K[0])`, hence `det K[0] tensor det K[-1]^-1`.
Maps are pinned by the ordered determinant diagrams of the actual kernel
and by every degreewise-surjective quasi-isomorphism span. Homotopic maps
have the same transport. No line unrelated to the presenting modules can
satisfy the object normalization below.

This scope is Tor amplitude `[-1,0]`. For usual curve cohomology in `[0,1]`,
the usual determinant is the inverse after shift `[1]`. A general bounded
perfect determinant requires a separate source integration.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TwoTermDeterminantModels

open CategoryTheory CategoryTheory.Limits
open ProjectiveDeterminantModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- The source's actual finite-projective two-term presentation criterion. -/
structure Presentation (K : DerivedCategory (ModuleCat.{u} R)) where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  finite : ∀ i : ℤ, Module.Finite R (complex.X i)
  projective : ∀ i : ℤ, Module.Projective R (complex.X i)
  strictlyGE : complex.IsStrictlyGE (-1)
  strictlyLE : complex.IsStrictlyLE 0
  comparison : K ≅ DerivedCategory.Q.obj complex

attribute [instance] Presentation.finite Presentation.projective

/-- An object $K$ of the derived category of $R$-modules is two-term perfect if it is isomorphic to
a complex of finitely generated projective $R$-modules concentrated in degrees $-1$ and $0$. -/
def IsTwoTermPerfect (K : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  Nonempty (Presentation K)

/-- The actual full derived category with the two-term-perfect property. -/
abbrev PerfectTwoTerm (R : Type u) [CommRing R] :=
  (show ObjectProperty (DerivedCategory (ModuleCat.{u} R)) from IsTwoTermPerfect).FullSubcategory

/-- The actual determinant of the two finite-projective presenting modules. -/
abbrev presentationDeterminant {K : DerivedCategory (ModuleCat.{u} R)} (P : Presentation K) :=
  determinantModule R (P.complex.X (-1)) →ₗ[R] determinantModule R (P.complex.X 0)

/-- The actual differential of the kernel of a cochain map. -/
def kernelDifferential {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (f : P.complex ⟶ Q.complex) :
    LinearMap.ker (f.f (-1)).hom →ₗ[R] LinearMap.ker (f.f 0).hom :=
  ((P.complex.d (-1) 0).hom.domRestrict (LinearMap.ker (f.f (-1)).hom)).codRestrict
    (LinearMap.ker (f.f 0).hom) (by
      intro x
      rw [LinearMap.mem_ker]
      have h := (ConcreteCategory.congr_hom (f.comm (-1) 0) x.val).symm
      change (f.f 0).hom ((P.complex.d (-1) 0).hom x.val) =
        (Q.complex.d (-1) 0).hom ((f.f (-1)).hom x.val) at h
      exact h.trans (by rw [x.property]; exact map_zero _))

/-- The genuine source comparison, normalized by the actual acyclic
kernel and both ordered short exact sequence determinant diagrams. -/
structure SurjectiveComparison {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (f : P.complex ⟶ Q.complex)
    (hs : Function.Surjective (f.f (-1)).hom ∧ Function.Surjective (f.f 0).hom)
    (hq : QuasiIso f) where
  negative : ShortExactDeterminant (f.f (-1)).hom hs.1
  zero : ShortExactDeterminant (f.f 0).hom hs.2
  kernelAcyclic : Function.Bijective (kernelDifferential P Q f)
  comparison : presentationDeterminant P ≃ₗ[R] presentationDeterminant Q
  normalization : ∀ (φ : presentationDeterminant P)
    (x : determinantModule R (LinearMap.ker (f.f (-1)).hom))
    (y : determinantModule R (Q.complex.X (-1))),
    zero.comparison
      (determinantEquiv (LinearEquiv.ofBijective (kernelDifferential P Q f) kernelAcyclic) x
        ⊗ₜ[R] comparison φ y) = φ (negative.comparison (x ⊗ₜ[R] y))

/-- An actual degreewise-surjective quasi-isomorphism span representing
the given derived isomorphism, with its native derived commuting equation. -/
structure SurjectiveSpan {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (a : K ≅ L) where
  middle : Presentation K
  left : middle.complex ⟶ P.complex
  right : middle.complex ⟶ Q.complex
  left_surjective : Function.Surjective (left.f (-1)).hom ∧ Function.Surjective (left.f 0).hom
  right_surjective : Function.Surjective (right.f (-1)).hom ∧ Function.Surjective (right.f 0).hom
  left_quasiIso : QuasiIso left
  right_quasiIso : QuasiIso right
  commutes : DerivedCategory.Q.map left ≫ P.comparison.inv ≫ a.hom ≫ Q.comparison.hom =
    DerivedCategory.Q.map right

/-- Transport of determinant modules of two-term presentations over a commutative ring $R$. A
presentation $P$ of an object $K$ of the derived category is a complex of finitely generated
projective $R$-modules in degrees $-1$ and $0$ with an isomorphism to $K$, and its determinant
module is $\operatorname{Hom}_R(\det P^{-1}, \det P^0)$. The data are: for every
degreewise-surjective quasi-isomorphism $f : P \to Q$ of presentations, an isomorphism of
determinant modules normalized by the determinant diagrams of the short exact sequences of $f$ in
degrees $-1$ and $0$ and of its acyclic kernel (`SurjectiveComparison`); and for all presentations
$P$ of $K$ and $Q$ of $L$ and every isomorphism $a : K \cong L$, an isomorphism
$\det P \cong \det Q$, the transport along $a$. They are subject to: every such $a$ is represented
by a span of degreewise-surjective quasi-isomorphisms of presentations; every determinant module is
invertible; for every such span, the transport along $a$ is the inverse of the comparison of its
left leg followed by the comparison of its right leg; homotopic maps have the same comparison; and
transport preserves identities and composition. -/
structure TransportSystem (R : Type u) [CommRing R] where
  spans : ∀ {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (a : K ≅ L), Nonempty (SurjectiveSpan P Q a)
  presentationInvertible : ∀ (K : DerivedCategory (ModuleCat.{u} R)) (P : Presentation K),
    Module.Invertible R (presentationDeterminant P)
  surjective : ∀ (K L : DerivedCategory (ModuleCat.{u} R))
    (P : Presentation K) (Q : Presentation L) (f : P.complex ⟶ Q.complex)
    (hs : Function.Surjective (f.f (-1)).hom ∧ Function.Surjective (f.f 0).hom)
    (hq : QuasiIso f), SurjectiveComparison P Q f hs hq
  transport : ∀ {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (_a : K ≅ L),
    presentationDeterminant P ≃ₗ[R] presentationDeterminant Q
  span_normalization : ∀ {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (a : K ≅ L) (s : SurjectiveSpan P Q a),
    transport P Q a =
      ((surjective K K s.middle P s.left s.left_surjective s.left_quasiIso).comparison).symm.trans
        (surjective K L s.middle Q s.right s.right_surjective s.right_quasiIso).comparison
  homotopy_normalization : ∀ {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (f g : P.complex ⟶ Q.complex)
    (hsf : Function.Surjective (f.f (-1)).hom ∧ Function.Surjective (f.f 0).hom)
    (hsg : Function.Surjective (g.f (-1)).hom ∧ Function.Surjective (g.f 0).hom)
    (hqf : QuasiIso f) (hqg : QuasiIso g) (_h : Homotopy f g),
    (surjective K L P Q f hsf hqf).comparison = (surjective K L P Q g hsg hqg).comparison
  identity : ∀ {K : DerivedCategory (ModuleCat.{u} R)} (P : Presentation K),
    transport P P (Iso.refl K) = LinearEquiv.refl R (presentationDeterminant P)
  composition : ∀ {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : Presentation K) (Q : Presentation L) (V : Presentation M) (a : K ≅ L) (b : L ≅ M),
    transport P V (a ≪≫ b) = (transport P Q a).trans (transport Q V b)

end MathlibExt.AlgebraicGeometry.TwoTermDeterminantModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionBaseChange
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension
public import MathlibExt.KTheory.Ring.K0.Projective

/-!
# The same actual associative and commutative RingK0 actions

The same-universe source/target shrink is naturally isomorphic to identity
through its actual linear equivalences. Combining this with the genuine
balanced/baseChange isomorphism identifies the EXISTING ringScalarExtension
functor with baseChange. Generator naturality and the original K0 dictionary
then identify the full underlying additive homomorphisms.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace FGProjectiveCat

/-- Same-universe shrinking retains every original module and linear map up to its actual Iso. -/
def sameUniverseShrinkIso (S : Type u) [Ring S] :
    (universeEquivalence.{u, u} S).functor ≅ 𝟭 (FGProjectiveCat.{u} S) :=
  NatIso.ofComponents
    (fun M => (ModuleCat.isFGProjective.{u} S).isoMk
      (UniverseEquivalence.shrinkLinearEquiv.{u, u} S M).toModuleIso)
    (by
      intro M N g
      apply FGProjectiveCat.hom_ext
      apply LinearMap.ext
      intro x
      change UniverseEquivalence.shrinkLinearEquiv.{u, u} S N
        (((universeEquivalence.{u, u} S).functor.map g).hom.hom x) =
          g.hom.hom (UniverseEquivalence.shrinkLinearEquiv.{u, u} S M x)
      have h := UniverseEquivalence.shrinkFunctor_map_apply S g x
      exact (congrArg (UniverseEquivalence.shrinkLinearEquiv.{u, u} S N) h).trans
        ((UniverseEquivalence.shrinkLinearEquiv.{u, u} S N).apply_symm_apply _))

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual existing ring-universe scalar functor is naturally isomorphic to existing baseChange. -/
def ringScalarExtensionBaseChangeIso (f : R →+* S) :
    ringScalarExtension.{u, u} f ≅ baseChange.{u, u, u} f :=
  Functor.isoWhiskerLeft (scalarExtension.{u, u, u} f) (sameUniverseShrinkIso S) ≪≫
    Functor.rightUnitor (scalarExtension.{u, u, u} f) ≪≫ scalarExtensionBaseChangeIso f

/-- The full underlying additive RingK0 actions agree in the same-universe commutative specialization. -/
theorem scalarExtensionK0_eq_mapRingHom (f : R →+* S) :
    scalarExtensionK0.{u, u} f = (AlgebraicKTheory.RingK0.mapRingHom f).toAddMonoidHom := by
  apply AlgebraicKTheory.K0.hom_ext
  intro P
  change scalarExtensionK0 f (AlgebraicKTheory.K0.mk P) =
    AlgebraicKTheory.RingK0.mapRingHom f (AlgebraicKTheory.K0.mk P)
  rw [scalarExtensionK0_mk, AlgebraicKTheory.RingK0.mapRingHom_mk]
  exact AlgebraicKTheory.K0.mk_congr_of_iso ((ringScalarExtensionBaseChangeIso f).app P)

/-- Every existing K0 value follows the same canonical public ring-map action. -/
theorem scalarExtensionK0_eq_mapRingHom_apply (f : R →+* S) (a : AlgebraicKTheory.RingK0 R) :
    scalarExtensionK0 f a = AlgebraicKTheory.RingK0.mapRingHom f a :=
  DFunLike.congr_fun (scalarExtensionK0_eq_mapRingHom f) a

end FGProjectiveCat

end

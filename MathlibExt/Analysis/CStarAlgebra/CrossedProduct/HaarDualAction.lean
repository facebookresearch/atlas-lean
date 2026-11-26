/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterContinuity
public import MathlibExt.Topology.Algebra.PontryaginDual.Pairing

/-!
# Dual character actions on full Haar crossed products

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α, the separated completion of the twisted convolution
core in the maximal L¹-dominated C-star seminorm, with dense core map ι. For a continuous
unitary character χ of G put Mχf(s)=χ(s)•f(s). The compact-open character group acts on X by
star automorphisms Dχ with Dχ(ι(f))=ι(Mχf), and χ↦Dχ(x) is norm-continuous for every x∈X. Let
μDual be a regular left Haar measure on the continuous unitary character group
Ĝ=PontryaginDual G, equipped with the compact-open topology and its Borel measurable
structure. The second full crossed product is Y=X⋊Ĝ for this action. Pulling its dual
character action back along evaluation g↦(χ↦χ(g)) gives a point-norm action of G on Y.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

attribute [local instance] fullCovariantCompletionCStarAlgebra

/-- **Point-norm dual character action.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α, the separated completion of the twisted convolution
core in the maximal L¹-dominated C-star seminorm, with dense core map ι. For a continuous
unitary character χ of G put Mχf(s)=χ(s)•f(s). The action fullHaarDualAction μ α of
Ĝ=PontryaginDual G on X satisfies Dχ(ι(f))=ι(Mχf), Dχη=Dχ∘Dη and D1=id. Every orbit χ↦Dχ(x) is
continuous from the compact-open topology to the norm topology of X.
-/
def fullHaarDualAction :
    PointNormCStarAction (PontryaginDual G) (FullCovariantCompletion mu alpha) where
  toMonoidHom :=
    { toFun := completedCharacterEquiv mu alpha
      map_one' := by
        apply StarAlgEquiv.ext
        intro x
        exact DFunLike.congr_fun (completedCharacterHom_one mu alpha) x
      map_mul' := fun chi eta => by
        apply StarAlgEquiv.ext
        intro x
        exact DFunLike.congr_fun (completedCharacterHom_mul mu alpha chi eta) x }
  continuous_orbit := continuous_completedCharacterEquiv_orbit mu alpha

omit [mu.Regular] in
/-- **Dual action on completed core coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action. For X=FullCovariantCompletion μ α and its
dense core map ι, the action D=fullHaarDualAction μ α satisfies Dχ(ι(f))=ι(Mχf) for
χ∈PontryaginDual G, where Mχf(s)=χ(s)•f(s).
-/
@[simp]
theorem fullHaarDualAction_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    fullHaarDualAction mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) :=
  completedCharacterEquiv_apply mu alpha chi f

section Double

variable [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
variable (muDual : Measure (PontryaginDual G)) [muDual.IsHaarMeasure] [muDual.Regular]

/-- **The second full Haar crossed product.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α and let ĥαχ be the point-norm action on X determined by
ĥαχ(ι(f))=ι(s↦χ(s)•f(s)). Let μDual be a regular left Haar measure on the continuous unitary
character group Ĝ=PontryaginDual G, equipped with the compact-open topology and its Borel
measurable structure. DoubleFullHaarCrossedProduct μ α μDual is the separated maximal C-star
completion of the compactly supported twisted convolution core of Ĝ with values in X and
action ĥα.
-/
abbrev DoubleFullHaarCrossedProduct : Type (max uG uA) :=
  FullCovariantCompletion muDual (fullHaarDualAction mu alpha)

/-- **C-star algebra of the second full crossed product.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α and let ĥαχ be the point-norm action on X determined by
ĥαχ(ι(f))=ι(s↦χ(s)•f(s)). Let μDual be a regular left Haar measure on the continuous unitary
character group Ĝ=PontryaginDual G, equipped with the compact-open topology and its Borel
measurable structure. The second crossed product Y=DoubleFullHaarCrossedProduct μ α μDual is a
nonunital complex C-star algebra. Its norm is induced by the maximal L¹(μDual)-dominated
C-star seminorm on the X-valued twisted convolution core; ‖star(y)*y‖=‖y‖².
-/
@[instance_reducible]
def doubleFullHaarCrossedProductCStarAlgebra :
    NonUnitalCStarAlgebra (DoubleFullHaarCrossedProduct mu alpha muDual) :=
  fullCovariantCompletionCStarAlgebra muDual (fullHaarDualAction mu alpha)

attribute [local instance] doubleFullHaarCrossedProductCStarAlgebra

/-- **Dense coefficient map into the second crossed product.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α and let ĥαχ be the point-norm action on X determined by
ĥαχ(ι(f))=ι(s↦χ(s)•f(s)). Let μDual be a regular left Haar measure on the continuous unitary
character group Ĝ=PontryaginDual G, equipped with the compact-open topology and its Borel
measurable structure. The nonunital complex star homomorphism toDoubleFullHaarCrossedProduct
sends each compactly supported continuous coefficient F:Ĝ→X to its class ι₂(F) in the maximal
C-star completion Y=DoubleFullHaarCrossedProduct μ α μDual.
-/
def toDoubleFullHaarCrossedProduct :
    Carrier muDual (fullHaarDualAction mu alpha) →⋆ₙₐ[ℂ] DoubleFullHaarCrossedProduct mu alpha muDual :=
  toFullCovariantCompletion muDual (fullHaarDualAction mu alpha)

/-- **Double dual action pulled back by group evaluation.**

Let G be a locally compact topological group with its Borel measurable structure and regular
left Haar measure μ, A a nonunital complex C-star algebra, and α a point-norm action of G on
A. Write X=FullCovariantCompletion μ α and let ĥαχ be the point-norm action on X determined by
ĥαχ(ι(f))=ι(s↦χ(s)•f(s)). Let μDual be a regular left Haar measure on the continuous unitary
character group Ĝ=PontryaginDual G, equipped with the compact-open topology and its Borel
measurable structure. On Y=DoubleFullHaarCrossedProduct μ α μDual, doubleDualHaarAction μ α
μDual is the point-norm action of G obtained from the character action of the second crossed
product using the character ev_g(χ)=χ(g). Thus β_g(ι₂(F))=ι₂(χ↦χ(g)•F(χ)) for every core
coefficient F:Ĝ→X.
-/
def doubleDualHaarAction :
    PointNormCStarAction G (DoubleFullHaarCrossedProduct mu alpha muDual) :=
  (fullHaarDualAction muDual (fullHaarDualAction mu alpha)).restrict (PontryaginDual.evaluation G)

omit [mu.Regular] [muDual.Regular] in
/-- **Double dual action on the second dense core.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action. Set X=FullCovariantCompletion μ α and let
μDual be a left Haar measure on the compact-open character group Ĝ with its Borel structure.
For the second completion Y=DoubleFullHaarCrossedProduct μ α μDual, its dense coefficient map
ι₂ and β=doubleDualHaarAction μ α μDual, β_g(ι₂(F))=ι₂(χ↦χ(g)•F(χ)); the scalar χ(g) is the
evaluation character of Ĝ.
-/
@[simp]
theorem doubleDualHaarAction_apply (g : G) (f : Carrier muDual (fullHaarDualAction mu alpha)) :
    doubleDualHaarAction mu alpha muDual g (toDoubleFullHaarCrossedProduct mu alpha muDual f) =
      toDoubleFullHaarCrossedProduct mu alpha muDual
        (characterModulation muDual (fullHaarDualAction mu alpha) (PontryaginDual.evaluation G g) f) := by
  simpa only [doubleDualHaarAction, PointNormCStarAction.restrict_apply,
    toDoubleFullHaarCrossedProduct] using
    fullHaarDualAction_apply muDual (fullHaarDualAction mu alpha) (PontryaginDual.evaluation G g) f

end Double
end HaarTwistedCore

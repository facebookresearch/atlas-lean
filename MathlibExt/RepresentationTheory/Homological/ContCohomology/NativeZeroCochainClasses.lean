/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldCoinductionCochainNaturality

public import MathlibExt.AlgebraicGeometry.Sites.AlternatingCofaceCoefficientComparison

/-!
# Degree-zero cohomology and invariant coaugmentation

For a separable closure Ω/k and a discrete continuous Galois module M,
taking invariants commutes with the alternating-coface complex of its
coinduction coresolution. The comparison has identity degree components
and is natural in M. The invariant coaugmentation gives closed
degree-zero cochains, whose continuous homogeneous values are constant.

More generally, a closed degree-zero morphism transports through a cochain
map in any abelian category. For a topological representation of a profinite
group, invariant coefficients define constant zero-cycles and their classes
are the inverse of the canonical H⁰-to-invariants isomorphism.
For topological ℤ-coefficients, forgetting to abelian groups preserves
the degree-zero cycle projection through the canonical homology comparison.
-/

/-!
# Alternating cofaces and invariant coefficients

For discrete continuous Galois modules, the additive invariant functor
can be applied before or after forming the alternating-coface complex.
-/
/-!
Let Ω/k be a separable closure, G its Galois group and M a discrete
continuous abelian G-module in c=max(u,w).
Alt(F(Cores_T(M))) ≅ F(Alt(Cores_T(M))) identifies the same degree
objects and alternating coface maps, with F=Inv_G.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The canonical cochain isomorphism
Alt(F(Cores_T(M))) ≅ F(Alt(Cores_T(M)))
commutes taking invariants with the alternating coface construction.
Its degree terms are identified without changing their maps. -/
def fieldCoindInvariantCanonicalIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldCoindInvariantComplexFunctor.{u, w} k Ω).obj M ≅
      (((DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (fieldCoindCanonicalComplex.{u, w} k Ω M)) := by
  unfold fieldCoindInvariantComplexFunctor fieldCoindCanonicalComplex
  change AlternatingCofaceMapComplex.obj
      (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M ⋙
        DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))) ≅ _
  exact actualAlternatingCoefficientIso
    (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k)))
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) M)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
In every degree n, the forward component of the invariant/alternating
cochain comparison is the identity of the common degree object. -/
theorem fieldCoindInvariantCanonicalIso_hom_f
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (n : ℕ) :
    (fieldCoindInvariantCanonicalIso.{u, w} k Ω M).hom.f n = 𝟙 _ := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The coefficient functor M ↦ F(Alt(Cores_T(M))) takes values in
nonnegative cochain complexes of abelian groups in c.
It applies coinduction, the alternating complex and then invariants
degreewise. -/
abbrev fieldCoindInvariantMappedFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  fieldCoindCanonicalComplexFunctor.{u, w} k Ω ⋙
    (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))).mapHomologicalComplex
      (ComplexShape.up ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The invariant/alternating comparisons form a natural isomorphism
between M ↦ Alt(F(Cores_T(M))) and M ↦ F(Alt(Cores_T(M))). -/
def fieldCoindInvariantCanonicalNatIso :
    fieldCoindInvariantComplexFunctor.{u, w} k Ω ≅ fieldCoindInvariantMappedFunctor.{u, w} k Ω := by
  unfold fieldCoindInvariantComplexFunctor fieldCoindInvariantMappedFunctor fieldCoindCanonicalComplexFunctor
  exact Functor.isoWhiskerLeft
    (Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)))
    (actualAlternatingCoefficientNatIso
      (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))))

/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
Every forward degree n map of the natural invariant/alternating
complex comparison is the identity. -/
theorem fieldCoindInvariantCanonicalNatIso_hom_f
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (n : ℕ) :
    ((fieldCoindInvariantCanonicalNatIso.{u, w} k Ω).hom.app M).f n = 𝟙 _ := rfl

end AlgebraicGeometry.Scheme.DerivedSections
end

/-!
# Invariant coaugmentation cycles

The coaugmentation of a Galois coefficient's coinduction coresolution
restricts to its invariant coefficients and gives a degree-zero cycle.
-/
/-!
For Ω/k a separable closure and M a discrete continuous Galois module,
the constant coaugmentation M → T(M), followed by invariants, gives
M^G → Z⁰(Alt(Inv_G(Cores_T(M)))).
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The invariant part of the constant coaugmentation defines
M^G → Z⁰(Alt(F(Cores_T(M)))).
It is the cycle lift of the invariant coaugmentation, transported
through the canonical invariant/alternating complex comparison. -/
def fieldCoindInvariantCoaugmentationCycle
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantFunctor.{u, w} k Ω).obj M ⟶
      ((fieldCoindInvariantComplexFunctor.{u, w} k Ω).obj M).cycles 0 :=
  let F := fieldInvariantFunctor.{u, w} k Ω
  let L := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (fieldCoindCanonicalComplex.{u, w} k Ω M))
  L.liftCycles (F.map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0))
    1 (by simp) (by
      change F.map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
        F.map ((fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1) = 0
      exact (F.map_comp _ _).symm.trans
        ((congrArg F.map ((congrArg
          (fun q => q ≫ (fieldCoindCanonicalComplex.{u, w} k Ω M).d 0 1)
          (fieldCoindCanonicalCoaugmentation_f_zero.{u, w} k Ω M)).trans
            (fieldCoindCanonicalCoaugmentation_closed.{u, w} k Ω M))).trans (F.map_zero _ _))) ≫
    HomologicalComplex.cyclesMap ((fieldCoindInvariantCanonicalNatIso.{u, w} k Ω).inv.app M) 0

end AlgebraicGeometry.Scheme.DerivedSections
end

/-!
# Degree-zero cycles under a cochain map

A cochain morphism sends a closed degree-zero morphism to a closed
degree-zero morphism, retaining its underlying composite.
-/
/-!
Let C be an abelian category, a:L→K a map of nonnegative cochain
complexes and x:A→L⁰ satisfy d_L⁰∘x=0.
The cycle induced in K has underlying morphism a₀∘x.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let C be an abelian category, K,L nonnegative cochain complexes,
a:L→K, and x:A→L⁰ with d_L⁰∘x=0.
Lifting x to cycles and applying Z⁰(a), then including into K⁰,
equals a₀∘x. Object and morphism universes may be independent. -/
theorem transport_liftCycles_i
    {K L : CochainComplex C ℕ} (a : L ⟶ K) {A : C} (x : A ⟶ L.X 0)
    (hx : x ≫ L.d 0 1 = 0) :
    (L.liftCycles x 1 (by simp) hx ≫ HomologicalComplex.cyclesMap a 0) ≫ K.iCycles 0 =
      x ≫ a.f 0 := by
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i_assoc]

end HomologicalComplex
end

/-!
# Constant cochains in the continuous Galois model

The coinduction coaugmentation and the continuous homogeneous comparison
send an invariant coefficient to the same constant cochain.
-/
@[expose] public section
section
/-!
For a discrete continuous Galois module M, the invariant
coaugmentation followed by the homogeneous cochain comparison has
value g↦x on an invariant coefficient x∈M^G.
-/
public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The degree-zero coaugmentation map M^G → C⁰_cts(G,M) is the
invariant image of M→T(M) followed by the canonical coinduction/
homogeneous cochain comparison. -/
def fieldCoindNativeCoaugmentationVectorCurrent
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantFunctor.{u, w} k Ω).obj M ⟶
      ((ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M).X 0 :=
  (fieldInvariantFunctor.{u, w} k Ω).map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
    (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f 0

/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
The invariant degree-zero coaugmentation is precisely the composite
M^G → Inv_G(T(M)) → C⁰_cts(G,M) given by invariant coaugmentation
and the degree-zero cochain comparison. -/
theorem fieldCoindNativeCoaugmentationVectorCurrent_eq
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldCoindNativeCoaugmentationVectorCurrent.{u, w} k Ω M =
      (fieldInvariantFunctor.{u, w} k Ω).map ((fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0) ≫
        (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f 0 := by
  unfold fieldCoindNativeCoaugmentationVectorCurrent
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let Ω/k be a separable closure of fields in universe u,
G=Gal(Ω/k), c=max(u,w), and M a discrete continuous G-module with
abelian coefficients in c. Let T be continuous coinduction and
F=Inv_G the additive invariant functor.
For x∈M^G and g∈G, the continuous degree-zero coaugmentation
has value c_x(g)=x. -/
theorem fieldCoindNativeCoaugmentationVectorCurrent_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (x : (fieldInvariantFunctor.{u, w} k Ω).obj M) (g : Gal(Ω/k)) :
    (fieldCoindNativeCoaugmentationVectorCurrent.{u, w} k Ω M x).val g = x.val := by
  unfold fieldCoindNativeCoaugmentationVectorCurrent
  rw [fieldCoindInvariantCochainIso_hom_f, fieldCoindCanonicalCoaugmentation_f_zero]
  exact DiscreteAbelianAction.coindCoresolution_coaugmentation_apply.{u, w} Gal(Ω/k) M x.val g

end AlgebraicGeometry.Scheme.DerivedSections
end

/-!
# Invariant coefficients as homogeneous zero-cycles

For a topological representation of a profinite group, an invariant
coefficient gives a closed constant homogeneous degree-zero cochain.
-/
/-!
Let R be a ring with a topology, G a profinite group and X a
topological R-representation. The map X^G→Z⁰(C_hom(G,X)) takes an
invariant x to the constant function g↦x; its class gives H⁰_cts(G,X).
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe r v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable {R : Type r} [Ring R] [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let R be a ring with a topology, G a profinite group and X a
topological R-representation. The map X^G → Z⁰(C_hom(G,X)) sends
x to the constant homogeneous zero-cycle g↦x.
The scalar, group and carrier universes are independent. -/
def zeroCycleInclusion (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G) :
    (TopRep.invariantsFunctor R G).obj X ⟶ (TopRep.homogeneousCochains X).cycles 0 :=
  (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).inv ≫
    (ContinuousCohomology.cocycles₀Iso X).inv

/-- For a ring R with a topology, a profinite G and a topological
R-representation X, let z:X^G→Z⁰(C_hom(G,X)) be the constant-cycle
inclusion. Its projection to cohomology is
π∘z=zeroIso_X⁻¹ : X^G→H⁰_cts(G,X). -/
theorem zeroCycleInclusion_projection
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G) :
    zeroCycleInclusion G X ≫ ContinuousCohomology.π X 0 = (ContinuousCohomology.zeroIso X).inv := by
  exact (ContinuousCohomology.homogeneousZeroIso_inverse_projection.{r, v, w} X).symm

end ContinuousCohomology
end

/-!
# Degree-zero homology after forgetting topology

The exact functor from topological ℤ-modules to abelian groups identifies
cycle and homology objects through their canonical comparisons.
-/
/-!
For the homogeneous complex K of a topological ℤ-representation,
the cycle and homology comparisons for the underlying-group functor U
commute with the degree-zero projection Z⁰(K)→H⁰(K).
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a profinite group, X a topological ℤ-representation with
carrier max(v,w), K its homogeneous complex and U the underlying-group
functor. For any abelian-group map c:A→U(Z⁰K), transport to Z⁰(UK),
project to H⁰(UK), then compare with U(H⁰K).
This composite equals U(π_K)∘c. Thus the canonical cycle/homology
comparisons preserve every represented degree-zero class. -/
theorem discreteForgetZeroCycle_class
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (A : AddCommGrpCat.{max v w}) (c : A ⟶
      (discreteCoefficientForget.{max v w}).obj ((TopRep.homogeneousCochains X).sc 0).cycles) :
    c ≫ (((TopRep.homogeneousCochains X).sc 0).mapCyclesIso
        discreteCoefficientForget.{max v w}).inv ≫
      (((discreteCoefficientForget.{max v w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (TopRep.homogeneousCochains X)).homologyπ 0 ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso
        discreteCoefficientForget.{max v w}).hom =
    c ≫ discreteCoefficientForget.{max v w}.map (ContinuousCohomology.π X 0) := by
  let U := discreteCoefficientForget.{max v w}
  let K := TopRep.homogeneousCochains X
  let S := K.sc 0
  let eC := S.mapCyclesIso U
  let eH := S.mapHomologyIso U
  have h := CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom S U
  change c ≫ eC.inv ≫ (S.map U).homologyπ ≫ eH.hom = c ≫ U.map S.homologyπ
  exact (congrArg (fun q => c ≫ eC.inv ≫ q) h).trans
    ((congrArg (fun q => c ≫ q)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ U.map S.homologyπ) eC.inv_hom_id).trans (Category.id_comp _)))))

end ContinuousCohomology
end
